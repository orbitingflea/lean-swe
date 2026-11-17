#!/usr/bin/env python3
"""Verify PR labels for edits to frozen spec files (`spec-add` vs `spec-change`).

Locked spec files (`Core/*.lean` and `LeanSwe/**/{Types,Model,SpecTests,Interface}.lean`,
except brand-new `LeanSwe/<Pkg>` packages absent at the base commit) always require a PR label.
Every top-level unit in a Lean file is split at unindented column-0 boundaries outside nested
block comments (`/- ... -/`), doc comments (`/-- ... -/`), string literals (including
interpolated `s!"..."` expressions), char literals, and `mutual ... end` blocks; leading
`--` comments, `/- ... -/` / `/-- ... -/` comments, and `@[...]` attributes stay attached to the
following declaration, while `where`/`|`/`deriving`/`termination_by`/`decreasing_by`
continuations stay attached to the preceding declaration. A unit is unchanged iff its text (doc
comment included) is byte-identical. Pure declaration additions (`def`, `theorem`, `lemma`,
`abbrev`, `structure`, `inductive`, `class`, `instance`, `example`, `mutual`, `opaque`)
appended after all non-`end` base units (before any unchanged trailing `end` lines) or added as a
new locked spec file require `spec-add` (also satisfied by `spec-change`). Any alteration
(including adding fields to an existing `EmpiricalAssumptions` structure, editing doc comments, or
adding `assume`), removal, rename/copy, middle insertion, embedded/indented/same-line extra
commands, or non-declaration directive requires `spec-change`.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import subprocess
import sys

SPEC_BASENAMES = frozenset({"Types.lean", "Model.lean", "SpecTests.lean", "Interface.lean"})
LABEL_ADD = "spec-add"
LABEL_CHANGE = "spec-change"
ALLOW_NEW_PACKAGES = True

PURE_DECL_MODIFIERS = frozenset({"private", "protected", "noncomputable", "partial"})
PURE_DECL_HEADS = frozenset({
    "def",
    "theorem",
    "lemma",
    "abbrev",
    "structure",
    "inductive",
    "class",
    "instance",
    "example",
    "mutual",
    "opaque",
})
CONTINUATION_TOKENS = frozenset({"where", "deriving", "termination_by", "decreasing_by"})
NON_DECL_COMMANDS = frozenset({
    "axiom",
    "open",
    "set_option",
    "universe",
    "universes",
    "variable",
    "variables",
    "import",
    "export",
    "namespace",
    "section",
    "attribute",
    "local",
    "scoped",
    "macro",
    "macro_rules",
    "syntax",
    "elab",
    "elab_rules",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "notation",
    "declare_syntax_cat",
    "initialize",
    "builtin_initialize",
    "register_simp_attr",
    "register_tactic_extension",
    "seal",
    "unseal",
    "run_cmd",
    "run_elab",
    "prelude",
    "module",
    "unsafe",
    "/-!",
})


@dataclass(frozen=True)
class LockedDiffAssessment:
    """Classification of one touched locked spec file against its base commit."""

    hit: str
    required_label: str
    reason: str


def resolve_repo_root() -> Path:
    """Return the Git repository top-level directory."""
    top = subprocess.check_output(
        ["git", "rev-parse", "--show-toplevel"],
        text=True,
    ).strip()
    return Path(top)


def resolve_effective_base(repo_root: Path, base_ref: str, head_ref: str) -> str:
    """Resolve merge-base(base_ref, head_ref), falling back to verified base_ref on shallow clones."""
    base_commit = subprocess.check_output(
        ["git", "rev-parse", "--verify", f"{base_ref}^{{commit}}"],
        cwd=repo_root,
        text=True,
    ).strip()
    head_commit = subprocess.check_output(
        ["git", "rev-parse", "--verify", f"{head_ref}^{{commit}}"],
        cwd=repo_root,
        text=True,
    ).strip()
    mb = subprocess.run(
        ["git", "merge-base", base_commit, head_commit],
        cwd=repo_root,
        capture_output=True,
        text=True,
    )
    if mb.returncode == 0 and mb.stdout.strip():
        return mb.stdout.strip()
    return base_commit


def is_spec_file(rel_path: str) -> bool:
    """Return True when rel_path is a frozen spec file under Core/ or LeanSwe/."""
    parts = Path(rel_path).parts
    if not parts:
        return False
    if parts[0] == "Core" and rel_path.endswith(".lean"):
        return True
    if parts[0] == "LeanSwe" and len(parts) >= 2 and parts[-1] in SPEC_BASENAMES:
        return True
    return False


def top_package_dir(rel_path: str) -> str | None:
    """Return 'LeanSwe/<Pkg>' for paths under LeanSwe/<Pkg>/..., else None."""
    parts = Path(rel_path).parts
    if len(parts) >= 3 and parts[0] == "LeanSwe":
        return f"LeanSwe/{parts[1]}"
    return None


def existing_top_packages_at_base(repo_root: Path, base_ref: str) -> set[str]:
    """Return the set of 'LeanSwe/<Pkg>' directories present in base_ref."""
    proc = subprocess.run(
        ["git", "ls-tree", "-d", "--name-only", base_ref, "LeanSwe/"],
        cwd=repo_root,
        capture_output=True,
        text=True,
        check=True,
    )
    return {line.strip().rstrip("/") for line in proc.stdout.splitlines() if line.strip().startswith("LeanSwe/")}


def read_pr_labels(event_path: Path | None, cli_labels: list[str], legacy_mark: bool) -> set[str]:
    """Collect active spec labels from CLI flags and the GitHub PR event JSON payload."""
    labels = {lbl for lbl in cli_labels if lbl in (LABEL_ADD, LABEL_CHANGE)}
    if legacy_mark:
        labels.add(LABEL_CHANGE)
    if event_path is not None and event_path.exists():
        payload = json.loads(event_path.read_text(encoding="utf-8"))
        pr_obj = payload.get("pull_request") or {}
        for item in pr_obj.get("labels") or []:
            if isinstance(item, dict):
                name = item.get("name")
                if name in (LABEL_ADD, LABEL_CHANGE):
                    labels.add(name)
    return labels


def diff_entries(repo_root: Path, base_ref: str, head_ref: str) -> list[tuple[str, list[str]]]:
    """Return (status_code, [paths...]) from NUL-delimited git diff --name-status --find-renames -z."""
    raw = subprocess.check_output(
        ["git", "diff", "--name-status", "--find-renames", "-z", base_ref, head_ref],
        cwd=repo_root,
    ).decode("utf-8", errors="surrogateescape")
    tokens = raw.split("\0")
    entries: list[tuple[str, list[str]]] = []
    idx = 0
    while idx < len(tokens):
        status = tokens[idx]
        if not status:
            idx += 1
            continue
        if status[0] in ("R", "C"):
            entries.append((status, [tokens[idx + 1], tokens[idx + 2]]))
            idx += 3
        else:
            entries.append((status, [tokens[idx + 1]]))
            idx += 2
    return entries


def git_show_text(repo_root: Path, commit_ref: str, rel_path: str) -> str:
    """Return UTF-8 text of rel_path at commit_ref."""
    return subprocess.check_output(
        ["git", "show", f"{commit_ref}:{rel_path}"],
        cwd=repo_root,
    ).decode("utf-8", errors="surrogateescape")


@dataclass(frozen=True)
class LeanToken:
    """One non-comment code/command token emitted by the Lean scanner."""

    text: str
    bdepth: int
    interp_depth: int
    after_dot: bool
    in_attr: bool


@dataclass(frozen=True)
class LeanLexState:
    """Persistent Lean 4 lexer state tracked across lines or full units."""

    block_depth: int = 0
    frames: tuple[tuple[str, bool | int], ...] = (("code", 0),)
    bdepth: int = 0
    in_attr: bool = False
    attr_base_depth: int = 0

    @property
    def is_top_level(self) -> bool:
        """Return True when not inside any block comment, string, or interpolated `{...}`."""
        return self.block_depth == 0 and len(self.frames) == 1


def scan_lean(source: str, state: LeanLexState | None = None) -> tuple[list[LeanToken], LeanLexState]:
    """Scan Lean source from `state`, returning non-comment tokens and the updated lexer state."""
    st = state or LeanLexState()
    block_depth = st.block_depth
    frames: list[tuple[str, bool | int]] = list(st.frames)
    bdepth = st.bdepth
    in_attr = st.in_attr
    attr_base_depth = st.attr_base_depth

    tokens: list[LeanToken] = []
    i = 0
    n = len(source)
    while i < n:
        ch = source[i]
        if block_depth > 0:
            if source.startswith("/-", i):
                block_depth += 1
                i += 2
            elif source.startswith("-/", i):
                block_depth -= 1
                i += 2
            else:
                i += 1
            continue

        frame_kind, frame_val = frames[-1]
        if frame_kind == "str":
            if ch == "\\":
                i = min(n, i + 2)
            elif ch == '"':
                frames.pop()
                i += 1
            elif frame_val and ch == "{":
                frames.append(("code", 1))
                bdepth += 1
                i += 1
            else:
                i += 1
            continue

        # Code frame
        interp_depth = sum(1 for k, _ in frames if k == "str")
        if source.startswith("--", i):
            nl = source.find("\n", i)
            if nl == -1:
                break
            i = nl + 1
        elif source.startswith("/-", i):
            if source.startswith("/-!", i):
                tokens.append(LeanToken("/-!", bdepth, interp_depth, after_dot=False, in_attr=in_attr))
            block_depth = 1
            i += 2
        elif ch == '"':
            is_interp = i >= 2 and source[i - 1] == "!" and (source[i - 2].isalnum() or source[i - 2] in "_'»")
            frames.append(("str", is_interp))
            i += 1
        elif ch == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'»")):
            if i + 2 < n and source[i + 1] == "\\":
                close_pos = next((k for k in range(i + 3, min(n, i + 10)) if source[k] == "'"), -1)
                if close_pos != -1 and "\n" not in source[i:close_pos]:
                    i = close_pos + 1
                    continue
            elif i + 2 < n and source[i + 1] not in "'\\\n" and source[i + 2] == "'":
                i += 3
                continue
            i += 1
        elif ch == "«":
            end = source.find("»", i + 1)
            if end == -1:
                tokens.append(LeanToken(source[i:], bdepth, interp_depth, after_dot=False, in_attr=in_attr))
                break
            after_dot = i > 0 and source[i - 1] == "."
            tokens.append(LeanToken(source[i : end + 1], bdepth, interp_depth, after_dot=after_dot, in_attr=in_attr))
            i = end + 1
        elif source.startswith("@[", i) and not in_attr and bdepth == 0 and interp_depth == 0:
            in_attr = True
            attr_base_depth = bdepth
            bdepth += 1
            i += 2
        elif ch in "([{⟨":
            if isinstance(frame_val, int) and frame_val > 0 and ch == "{":
                frames[-1] = ("code", frame_val + 1)
            bdepth += 1
            i += 1
        elif ch in ")]}⟩":
            if isinstance(frame_val, int) and frame_val > 0 and ch == "}":
                bdepth = max(0, bdepth - 1)
                if frame_val == 1:
                    frames.pop()
                else:
                    frames[-1] = ("code", frame_val - 1)
                i += 1
                continue
            bdepth = max(0, bdepth - 1)
            if in_attr and ch == "]" and bdepth <= attr_base_depth:
                in_attr = False
            i += 1
        elif ch == "#" and i + 1 < n and source[i + 1].isalpha() and (
            i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'»")
        ):
            j = i + 1
            while j < n and (source[j].isalnum() or source[j] in "_'"):
                j += 1
            tokens.append(LeanToken(source[i:j], bdepth, interp_depth, after_dot=False, in_attr=in_attr))
            i = j
        elif ch.isalpha() or ch == "_":
            after_dot = i > 0 and source[i - 1] == "."
            j = i
            while j < n and (source[j].isalnum() or source[j] in "_'"):
                j += 1
            tokens.append(LeanToken(source[i:j], bdepth, interp_depth, after_dot=after_dot, in_attr=in_attr))
            i = j
        else:
            i += 1

    next_state = LeanLexState(
        block_depth=block_depth,
        frames=tuple(frames),
        bdepth=bdepth,
        in_attr=in_attr,
        attr_base_depth=attr_base_depth,
    )
    return tokens, next_state


def _extract_head_from_tokens(tokens: list[LeanToken]) -> tuple[str | None, int]:
    """Return `(head_keyword, token_index)` after skipping `@[...]` attrs and pure modifiers."""
    idx = 0
    while idx < len(tokens):
        tok = tokens[idx]
        if tok.in_attr:
            idx += 1
            continue
        if (
            not tok.after_dot
            and tok.bdepth == 0
            and tok.interp_depth == 0
            and tok.text in PURE_DECL_MODIFIERS
        ):
            idx += 1
            continue
        return (None if tok.after_dot else tok.text), idx
    return None, idx


def extract_unit_head(unit_text: str) -> str | None:
    """Return the declaration/command keyword of a unit after stripping comments, `@[...]`, and modifiers."""
    tokens, end_state = scan_lean(unit_text)
    if end_state.in_attr or end_state.block_depth > 0 or len(end_state.frames) != 1:
        return None
    head, _ = _extract_head_from_tokens(tokens)
    return head


def split_lean_units(source: str) -> tuple[list[str], bool]:
    """Split Lean source into top-level units plus whether lexer state ended cleanly."""
    units: list[str] = []
    cur_lines: list[str] = []
    lex_state = LeanLexState()
    in_mutual = False

    def flush() -> None:
        while cur_lines and not cur_lines[-1].strip():
            cur_lines.pop()
        if cur_lines:
            units.append("\n".join(cur_lines))
            cur_lines.clear()

    for ln in source.splitlines():
        at_col0_clear = lex_state.is_top_level and len(ln) > 0 and not ln[0].isspace()
        line_tokens, next_state = scan_lean(ln + "\n", lex_state)
        first_tok = line_tokens[0].text if line_tokens else None
        if at_col0_clear:
            if in_mutual:
                cur_lines.append(ln)
                if first_tok == "end":
                    in_mutual = False
            elif cur_lines and (first_tok in CONTINUATION_TOKENS or ln.startswith("|")):
                cur_lines.append(ln)
            elif cur_lines and extract_unit_head("\n".join(cur_lines)) is None:
                if first_tok == "end" or first_tok == "/-!" or ln.startswith("/-!"):
                    flush()
                    cur_lines.append(ln)
                else:
                    cur_lines.append(ln)
                    if extract_unit_head("\n".join(cur_lines)) == "mutual":
                        in_mutual = True
            else:
                flush()
                cur_lines.append(ln)
                if extract_unit_head("\n".join(cur_lines)) == "mutual":
                    in_mutual = True
        else:
            if cur_lines or ln.strip():
                cur_lines.append(ln)
        lex_state = next_state
    flush()
    clean_eof = lex_state.is_top_level and not lex_state.in_attr and lex_state.bdepth == 0 and not in_mutual
    return units, clean_eof


def validate_pure_added_unit(unit_text: str) -> str | None:
    """Return None if `unit_text` is a single pure declaration addition, else an error reason."""
    tokens, end_state = scan_lean(unit_text)
    if not (end_state.is_top_level and not end_state.in_attr and end_state.bdepth == 0):
        return f"unclosed syntax in added unit: {unit_preview(unit_text)}"

    head_tok, head_idx = _extract_head_from_tokens(tokens)
    if head_tok not in PURE_DECL_HEADS:
        return f"appended non-declaration item ({head_tok or 'comment'}): {unit_preview(unit_text)}"

    if head_tok == "mutual":
        if head_idx > 0:
            return f"disallowed prefix on mutual block: {unit_preview(unit_text)}"
        mutual_depth = 1
        for tok in tokens[head_idx + 1 :]:
            if tok.after_dot or tok.interp_depth > 0:
                continue
            if mutual_depth == 0:
                return f"trailing token '{tok.text}' after mutual 'end': {unit_preview(unit_text)}"
            if tok.text in NON_DECL_COMMANDS or tok.text.startswith("#"):
                return f"disallowed command '{tok.text}' inside mutual block: {unit_preview(unit_text)}"
            if tok.text == "mutual":
                mutual_depth += 1
            elif tok.text == "end":
                mutual_depth -= 1
        if mutual_depth != 0:
            return f"unclosed mutual block: {unit_preview(unit_text)}"
        return None

    disallowed_inner = NON_DECL_COMMANDS | PURE_DECL_HEADS | {"end"}
    for tok in tokens[head_idx + 1 :]:
        if tok.after_dot or tok.interp_depth > 0:
            continue
        if tok.text in disallowed_inner or tok.text.startswith("#"):
            return (
                f"additional or non-declaration command '{tok.text}' in unit: "
                f"{unit_preview(unit_text)}"
            )
    return None


def unit_preview(unit_text: str) -> str:
    """Return a short one-line signature preview of a Lean unit for diagnostics."""
    for ln in unit_text.splitlines():
        s = ln.strip()
        if not s or s.startswith("--") or s.startswith("/--") or s.startswith("@["):
            continue
        return s[:80] + ("..." if len(s) > 80 else "")
    first = unit_text.splitlines()[0].strip() if unit_text else "<empty>"
    return first[:80] + ("..." if len(first) > 80 else "")


def classify_locked_spec_diff(
    repo_root: Path,
    base_ref: str,
    head_ref: str,
    status: str,
    paths: list[str],
) -> LockedDiffAssessment:
    """Determine whether one touched locked spec file requires `spec-add` or `spec-change`."""
    hit = f"{status}\t{' -> '.join(paths)}"
    if status[0] in ("D", "R", "C"):
        return LockedDiffAssessment(hit, LABEL_CHANGE, f"spec file status '{status}' alters or removes existing spec")
    if status == "A" and len(paths) == 1:
        head_text = git_show_text(repo_root, head_ref, paths[0])
        head_units, head_clean = split_lean_units(head_text)
        if not head_clean or not head_units:
            return LockedDiffAssessment(hit, LABEL_CHANGE, "new locked spec file is empty or has unclosed syntax")
        return LockedDiffAssessment(
            hit,
            LABEL_ADD,
            f"new locked spec file adding {len(head_units)} unit(s) with no base declarations touched",
        )
    if status != "M" or len(paths) != 1:
        return LockedDiffAssessment(hit, LABEL_CHANGE, f"unsupported spec diff status '{status}'")

    rel_path = paths[0]
    base_text = git_show_text(repo_root, base_ref, rel_path)
    head_text = git_show_text(repo_root, head_ref, rel_path)
    base_units, base_clean = split_lean_units(base_text)
    head_units, head_clean = split_lean_units(head_text)
    if not base_clean or not head_clean:
        return LockedDiffAssessment(hit, LABEL_CHANGE, "unclosed Lean comment, string, or mutual block")

    trailing_ends = 0
    while trailing_ends < len(base_units) and extract_unit_head(base_units[-1 - trailing_ends]) == "end":
        trailing_ends += 1
    base_prefix_len = len(base_units) - trailing_ends
    base_prefix = base_units[:base_prefix_len]
    base_ends = base_units[base_prefix_len:]

    for idx, base_u in enumerate(base_prefix):
        if idx >= len(head_units):
            return LockedDiffAssessment(hit, LABEL_CHANGE, f"removed declaration: {unit_preview(base_u)}")
        if head_units[idx] != base_u:
            if base_u in head_units[idx + 1 :]:
                return LockedDiffAssessment(
                    hit,
                    LABEL_CHANGE,
                    f"inserted or reordered item before existing declaration: {unit_preview(base_u)}",
                )
            if head_units[idx] in base_prefix[idx + 1 :] or (
                base_ends and head_units[idx] == base_ends[0] and base_u not in head_units[idx:]
            ):
                return LockedDiffAssessment(hit, LABEL_CHANGE, f"removed declaration: {unit_preview(base_u)}")
            return LockedDiffAssessment(hit, LABEL_CHANGE, f"modified declaration: {unit_preview(base_u)}")

    if len(head_units) < len(base_units):
        return LockedDiffAssessment(hit, LABEL_CHANGE, "removed trailing 'end' block")
    if base_ends and head_units[len(head_units) - trailing_ends :] != base_ends:
        return LockedDiffAssessment(hit, LABEL_CHANGE, "modified or removed trailing 'end' block")

    added_units = head_units[base_prefix_len : len(head_units) - trailing_ends]
    if not added_units:
        return LockedDiffAssessment(hit, LABEL_CHANGE, "no new top-level declarations appended (whitespace-only edit)")

    for added_u in added_units:
        err = validate_pure_added_unit(added_u)
        if err is not None:
            return LockedDiffAssessment(hit, LABEL_CHANGE, err)

    return LockedDiffAssessment(hit, LABEL_ADD, f"pure addition of {len(added_units)} declaration(s)")


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint checking PR spec-change and spec-add labels."""
    parser = argparse.ArgumentParser(description="Verify spec-add / spec-change PR labels on locked spec files.")
    parser.add_argument("--base", required=True, help="Base commit or ref to diff against.")
    parser.add_argument("--head", default="HEAD", help="Head commit or ref (default: HEAD).")
    parser.add_argument(
        "--event-path",
        default=os.environ.get("GITHUB_EVENT_PATH"),
        help="Path to GitHub Actions event JSON payload.",
    )
    parser.add_argument(
        "--label",
        action="append",
        default=[],
        choices=[LABEL_ADD, LABEL_CHANGE],
        help="Treat the given PR label as present for local testing (repeatable).",
    )
    parser.add_argument(
        "--has-mark",
        action="store_true",
        help="Alias for --label spec-change.",
    )
    args = parser.parse_args(argv)

    repo_root = resolve_repo_root()
    effective_base = resolve_effective_base(repo_root, args.base, args.head)
    base_pkgs = existing_top_packages_at_base(repo_root, effective_base)
    entries = diff_entries(repo_root, effective_base, args.head)

    locked_assessments: list[LockedDiffAssessment] = []
    new_pkg_spec_hits: list[str] = []

    for status, paths in entries:
        spec_paths = [p for p in paths if is_spec_file(p)]
        if not spec_paths:
            continue
        if ALLOW_NEW_PACKAGES and status == "A" and len(paths) == 1:
            pkg = top_package_dir(paths[0])
            if pkg is not None and pkg not in base_pkgs:
                new_pkg_spec_hits.append(f"{status}\t{paths[0]}")
                continue
        locked_assessments.append(classify_locked_spec_diff(repo_root, effective_base, args.head, status, paths))

    event_file = Path(args.event_path) if args.event_path else None
    labels_present = read_pr_labels(event_file, args.label, args.has_mark)

    if not locked_assessments:
        if new_pkg_spec_hits:
            print(
                f"SPEC_CHECK: ok (new-package spec files={len(new_pkg_spec_hits)}, "
                "locked spec files touched=0)"
            )
        else:
            print("SPEC_CHECK: ok (spec files touched=0)")
        return 0

    requires_change = any(a.required_label == LABEL_CHANGE for a in locked_assessments)
    required_label = LABEL_CHANGE if requires_change else LABEL_ADD

    if LABEL_CHANGE in labels_present:
        print(
            f"SPEC_CHECK: ok (label='{LABEL_CHANGE}' present, "
            f"locked spec files touched={len(locked_assessments)})"
        )
        for a in locked_assessments:
            print(f"  MARKED_SPEC_EDIT: {a.hit} ({a.reason})")
        return 0

    if LABEL_ADD in labels_present and not requires_change:
        print(
            f"SPEC_CHECK: ok (label='{LABEL_ADD}' present, "
            f"pure additions verified across {len(locked_assessments)} locked spec file(s))"
        )
        for a in locked_assessments:
            print(f"  MARKED_SPEC_ADD: {a.hit} ({a.reason})")
        return 0

    if LABEL_ADD in labels_present and requires_change:
        print(
            f"SPEC_CHECK: failed (label '{LABEL_ADD}' allows pure appended declarations only, "
            f"but existing spec content was modified or removed; apply label '{LABEL_CHANGE}')",
            file=sys.stderr,
        )
        for a in locked_assessments:
            tag = "SPEC_CHANGE_REQUIRED" if a.required_label == LABEL_CHANGE else "SPEC_ADD_ONLY"
            hint = f"apply label '{LABEL_CHANGE}'" if a.required_label == LABEL_CHANGE else "covered if upgraded"
            print(f"{tag}: {a.hit} ({a.reason}; {hint})", file=sys.stderr)
        return 1

    print(
        f"SPEC_CHECK: failed (missing '{required_label}' label for "
        f"{len(locked_assessments)} locked spec file(s))",
        file=sys.stderr,
    )
    for a in locked_assessments:
        if a.required_label == LABEL_ADD:
            print(
                f"UNMARKED_SPEC_ADD: {a.hit} ({a.reason}; apply label '{LABEL_ADD}' or '{LABEL_CHANGE}')",
                file=sys.stderr,
            )
        else:
            print(
                f"UNMARKED_SPEC_CHANGE: {a.hit} ({a.reason}; apply label '{LABEL_CHANGE}')",
                file=sys.stderr,
            )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
