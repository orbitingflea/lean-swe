#!/usr/bin/env python3
"""Verify PR labels for locked specs (`spec-add`/`spec-change`) and foreign budget (`add-foreign-lang`).

Locked spec files (`Core/*.lean`, `LeanSwe/**/{Types,Model,Interface,Properties,ModelChecks}.lean`,
`LeanSwe/**/{Types,Model,Interface,Properties,ModelChecks}/**/*.lean`, and locked spec metadata
files `scripts/package_manifest.json`, `scripts/external_assumptions.json`, and
`scripts/coverage_overrides.json`, except brand-new `LeanSwe/<Pkg>` packages absent at the base
commit) always require a PR label. `SpecTests.lean` and `SpecTests/**/*.lean` are intentionally
unlocked (`#153`).
Every top-level unit in a Lean file is split at unindented column-0 boundaries outside nested
block comments (`/- ... -/`), doc comments (`/-- ... -/`), string literals (including
interpolated `s!"..."` expressions), char literals, and `mutual ... end` blocks; leading
`--` comments, `/- ... -/` / `/-- ... -/` comments, and `@[...]` attributes stay attached to the
following declaration, while `where`/`|`/`deriving`/`termination_by`/`decreasing_by`
continuations stay attached to the preceding declaration. A unit is unchanged iff its text (doc
comment included) is byte-identical. Pure declaration additions (`def`, `theorem`, `abbrev`,
`structure`, `inductive`, `example`, `mutual`) with at most allowlisted `@[...]` attributes,
appended after all non-`end` base units (before any unchanged trailing `end` lines), added as a
validated new `{Types,Model,Properties,ModelChecks}{.lean,/**/*.lean}` file in an existing
package, or manifest-only additions/strengthenings in `scripts/package_manifest.json` (adding
entries under existing top-level packages, upgrading `"kind": "property" -> "model"`, adding
`fuzz_suite`, adding `deps`, or tightening `external_boundary: false -> true`) require
`spec-add` (also satisfied by `spec-change`). Purely adding `scripts/package_manifest.json`
entries for brand-new top-level `LeanSwe/<Pkg>` packages absent at the base commit (touching zero
existing entries) is exempt alongside brand-new package spec files when `ALLOW_NEW_PACKAGES` is
enabled. Any alteration (including adding fields to an existing `EmpiricalAssumptions` structure,
editing doc comments, or adding `assume`), removal, rename/copy, middle insertion, new
`Core/*.lean` or `Interface{.lean,/**/*.lean}`, `opaque`/`instance`/`class`, unsafe or custom
`@[...]` attributes, embedded/indented/same-line extra commands, non-declaration directive, or
non-strengthening edit to locked spec metadata JSON files (including downgrading a package from
`"kind": "model"` to `"kind": "property"` or `external_boundary: true -> false`, removing a
package/dep/`fuzz_suite`, or editing `scripts/external_assumptions.json` /
`scripts/coverage_overrides.json`) requires `spec-change`.

When `scripts/package_manifest.json` is present in `base` or `head`, manifest integrity is
enforced unconditionally: 100% package coverage under `LeanSwe/`, zero orphan entries, no
`"kind": "property"` for packages with `external_boundary=true` or `@[extern]` declarations, and
every referenced `fuzz_suite` must exist in `harness/Fuzz/suites.json`.

`.foreign-budget.json` is enforced as a strictly orthogonal one-way ratchet: deleting files,
lowering `max_lines`, clearing `legacy_unmigrated`, or tightening `function_overrides` /
`named_thread_helpers` needs no label, whereas adding/loosening any budget entry, changing a
vendored SHA-256, or deleting/renaming `.foreign-budget.json` requires `add-foreign-lang` (`spec-change`
and `spec-add` do not substitute for `add-foreign-lang`, nor vice versa).
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import subprocess
import sys

SPEC_SUBDIRS = frozenset({"Types", "Model", "Interface", "Properties", "ModelChecks"})
SPEC_BASENAMES = frozenset(f"{d}.lean" for d in SPEC_SUBDIRS)
PACKAGE_MANIFEST_PATH = "scripts/package_manifest.json"
EXTERNAL_ASSUMPTIONS_PATH = "scripts/external_assumptions.json"
COVERAGE_OVERRIDES_PATH = "scripts/coverage_overrides.json"
LOCKED_SPEC_JSON_PATHS = frozenset({
    PACKAGE_MANIFEST_PATH,
    EXTERNAL_ASSUMPTIONS_PATH,
    COVERAGE_OVERRIDES_PATH,
})
FUZZ_SUITES_PATH = "harness/Fuzz/suites.json"
NON_PACKAGE_SUBDIRS = frozenset({
    "Proofs",
    "Model",
    "Types",
    "SpecTests",
    "Properties",
    "ModelChecks",
    "SpecMutants",
    "RuntimeTests",
    "Impl",
    "Interface",
    "SysBridge",
    "Host",
    "Init",
    "Aeneas",
})
MANIFEST_ROOT_KEYS = frozenset({"version", "packages"})
MANIFEST_PKG_REQUIRED_KEYS = frozenset({"kind", "purity", "deps", "external_boundary"})
MANIFEST_PKG_OPTIONAL_KEYS = frozenset({"fuzz_suite", "err_msg_opaque", "spec_style"})
MANIFEST_PKG_ALL_KEYS = MANIFEST_PKG_REQUIRED_KEYS | MANIFEST_PKG_OPTIONAL_KEYS
MANIFEST_KINDS = frozenset({"model", "property", "support"})
MANIFEST_PURITIES = frozenset({"pure", "nondet_io", "mixed", "types_only"})
MANIFEST_SPEC_STYLES = frozenset({"pure_eq", "inverse_render", "state_step"})
FOREIGN_BUDGET_PATH = ".foreign-budget.json"
BUDGET_ROOT_KEYS = frozenset({"version", "files", "vendored_files", "function_overrides", "named_thread_helpers"})
BUDGET_FILE_KEYS = frozenset({"max_lines", "legacy_unmigrated"})
BUDGET_VENDORED_KEYS = frozenset({"sha256", "max_lines"})
BUDGET_OVERRIDE_KEYS = frozenset(
    {"max_code_lines", "max_branches", "allow_array_copy_loop", "max_loops", "allow_poll"}
)
LABEL_ADD = "spec-add"
LABEL_CHANGE = "spec-change"
LABEL_FOREIGN = "add-foreign-lang"
ALL_GATE_LABELS = frozenset({LABEL_ADD, LABEL_CHANGE, LABEL_FOREIGN})
ALLOW_NEW_PACKAGES = True

SAFE_DECL_ATTRS = frozenset({
    "inline",
    "reducible",
    "always_inline",
    "noinline",
    "macro_inline",
    "specialize",
    "nospecialize",
})
PURE_DECL_MODIFIERS = frozenset({"private", "protected", "noncomputable", "partial"})
PURE_DECL_HEADS = frozenset({
    "def",
    "theorem",
    "abbrev",
    "structure",
    "inductive",
    "example",
    "mutual",
})
DISALLOWED_DECL_HEADS = frozenset({"opaque", "instance", "class"})
CONTINUATION_TOKENS = frozenset({"where", "deriving", "termination_by", "decreasing_by"})
NON_DECL_COMMANDS = frozenset({
    "axiom",
    "open",
    "set_option",
    "universe",
    "variable",
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
    "add_decl_doc",
    "unif_hint",
    "simproc",
    "dsimproc",
    "simproc_decl",
    "coinductive",
    "seal",
    "unseal",
    "run_cmd",
    "run_elab",
    "unsafe",
    "/-!",
})
NON_RESERVED_HEAD_COMMANDS = frozenset({
    "alias",
    "lemma",
    "prelude",
    "irreducible_def",
    "register_option",
    "register_simp_attr",
    "register_simproc_attr",
    "register_tactic_extension",
})
NON_INTERP_MACROS = frozenset({"panic!", "unreachable!", "assert!", "debug_assert!"})
IDENT_CONT_CHARS = "_'?!"


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
    """Return True when rel_path is a frozen spec file under Core/, LeanSwe/, or locked metadata JSON."""
    if rel_path in LOCKED_SPEC_JSON_PATHS:
        return True
    parts = Path(rel_path).parts
    if not parts:
        return False
    if parts[0] == "Core" and rel_path.endswith(".lean"):
        return True
    if parts[0] == "LeanSwe" and len(parts) >= 2 and rel_path.endswith(".lean"):
        if parts[-1] in SPEC_BASENAMES:
            return True
        if any(seg in SPEC_SUBDIRS for seg in parts[1:-1]):
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


def read_pr_labels(event_path: Path | None, cli_labels: list[str]) -> set[str]:
    """Collect active gate labels from CLI flags and the GitHub PR event JSON payload."""
    labels: set[str] = set()
    for raw in cli_labels:
        for part in raw.split(","):
            lbl = part.strip()
            if lbl in ALL_GATE_LABELS:
                labels.add(lbl)
    if event_path is not None and event_path.exists():
        payload = json.loads(event_path.read_text(encoding="utf-8"))
        pr_obj = payload.get("pull_request") or {}
        for item in pr_obj.get("labels") or []:
            if isinstance(item, dict):
                name = item.get("name")
                if name in ALL_GATE_LABELS:
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


def git_file_exists(repo_root: Path, commit_ref: str, rel_path: str) -> bool:
    """Return True if rel_path exists as a blob at commit_ref."""
    proc = subprocess.run(
        ["git", "cat-file", "-e", f"{commit_ref}:{rel_path}"],
        cwd=repo_root,
        capture_output=True,
    )
    return proc.returncode == 0


def git_list_tree_files(repo_root: Path, commit_ref: str, prefix: str) -> list[str]:
    """Return repo-relative file paths under prefix at commit_ref."""
    proc = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", "-z", commit_ref, "--", prefix],
        cwd=repo_root,
        capture_output=True,
    )
    if proc.returncode != 0:
        return []
    raw = proc.stdout.decode("utf-8", errors="surrogateescape")
    return [tok for tok in raw.split("\0") if tok]


@dataclass(frozen=True)
class LeanToken:
    """One non-comment code/command token emitted by the Lean scanner."""

    text: str
    bdepth: int
    interp_depth: int
    after_dot: bool
    after_backtick: bool
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
        """Return True at top-level code (outside comments, strings, interpolations, attrs, delimiters)."""
        return self.block_depth == 0 and len(self.frames) == 1 and self.bdepth == 0 and not self.in_attr


def scan_lean(source: str, state: LeanLexState | None = None) -> tuple[list[LeanToken], LeanLexState]:
    """Scan Lean source from `state`, returning non-comment tokens and the updated lexer state."""
    st = state or LeanLexState()
    block_depth = st.block_depth
    frames: list[tuple[str, bool | int]] = list(st.frames)
    bdepth = st.bdepth
    in_attr = st.in_attr
    attr_base_depth = st.attr_base_depth

    tokens: list[LeanToken] = []
    last_ident_end = -1
    last_ident_text = ""
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
        if frame_kind == "raw":
            closing = '"' + "#" * int(frame_val)
            if source.startswith(closing, i):
                frames.pop()
                i += len(closing)
            else:
                i += 1
            continue
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
        after_num_or_dot = i > 0 and (source[i - 1].isdigit() or source[i - 1] == ".")
        if ch == "r" and last_ident_end != i and not after_num_or_dot:
            k = i + 1
            while k < n and source[k] == "#":
                k += 1
            if k < n and source[k] == '"':
                if in_attr:
                    tokens.append(
                        LeanToken("<attr_arg>", bdepth, interp_depth, after_dot=False, after_backtick=False, in_attr=True)
                    )
                frames.append(("raw", k - (i + 1)))
                i = k + 1
                continue
        if source.startswith("--", i):
            nl = source.find("\n", i)
            if nl == -1:
                break
            i = nl + 1
        elif source.startswith("/-", i):
            if source.startswith("/-!", i):
                tokens.append(
                    LeanToken("/-!", bdepth, interp_depth, after_dot=False, after_backtick=False, in_attr=in_attr)
                )
            block_depth = 1
            i += 2
        elif ch == '"':
            if in_attr:
                tokens.append(
                    LeanToken("<attr_arg>", bdepth, interp_depth, after_dot=False, after_backtick=False, in_attr=True)
                )
            is_interp = (
                last_ident_end == i
                and last_ident_text.endswith("!")
                and last_ident_text not in NON_INTERP_MACROS
            )
            frames.append(("str", is_interp))
            i += 1
        elif ch == "'" and last_ident_end != i and not after_num_or_dot:
            if i + 2 < n and source[i + 1] == "\\":
                close_pos = next((k for k in range(i + 3, min(n, i + 10)) if source[k] == "'"), -1)
                if close_pos != -1 and "\n" not in source[i:close_pos]:
                    if in_attr:
                        tokens.append(
                            LeanToken(
                                "<attr_arg>", bdepth, interp_depth, after_dot=False, after_backtick=False, in_attr=True
                            )
                        )
                    i = close_pos + 1
                    continue
            elif i + 2 < n and source[i + 1] not in "'\\\n" and source[i + 2] == "'":
                if in_attr:
                    tokens.append(
                        LeanToken(
                            "<attr_arg>", bdepth, interp_depth, after_dot=False, after_backtick=False, in_attr=True
                        )
                    )
                i += 3
                continue
            if in_attr:
                tokens.append(
                    LeanToken("<attr_arg>", bdepth, interp_depth, after_dot=False, after_backtick=False, in_attr=True)
                )
            i += 1
        elif ch == "«":
            end = source.find("»", i + 1)
            after_dot = i > 0 and source[i - 1] == "."
            after_backtick = i > 0 and source[i - 1] == "`"
            if end == -1:
                tokens.append(
                    LeanToken(
                        source[i:],
                        bdepth,
                        interp_depth,
                        after_dot=after_dot,
                        after_backtick=after_backtick,
                        in_attr=in_attr,
                    )
                )
                break
            tok_text = source[i : end + 1]
            tokens.append(
                LeanToken(
                    tok_text,
                    bdepth,
                    interp_depth,
                    after_dot=after_dot,
                    after_backtick=after_backtick,
                    in_attr=in_attr,
                )
            )
            last_ident_end = end + 1
            last_ident_text = tok_text
            i = end + 1
        elif source.startswith("@[", i) and not in_attr and bdepth == 0 and interp_depth == 0:
            in_attr = True
            attr_base_depth = bdepth
            bdepth += 1
            i += 2
        elif ch in "([{⟨":
            if in_attr:
                tokens.append(
                    LeanToken("<attr_arg>", bdepth, interp_depth, after_dot=False, after_backtick=False, in_attr=True)
                )
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
            elif in_attr:
                tokens.append(
                    LeanToken("<attr_arg>", bdepth, interp_depth, after_dot=False, after_backtick=False, in_attr=True)
                )
            i += 1
        elif ch == "#" and i + 1 < n and source[i + 1].isalpha():
            j = i + 1
            while j < n and (source[j].isalnum() or source[j] in IDENT_CONT_CHARS):
                j += 1
            tokens.append(
                LeanToken(source[i:j], bdepth, interp_depth, after_dot=False, after_backtick=False, in_attr=in_attr)
            )
            i = j
        elif ch.isalpha() or ch == "_":
            after_dot = i > 0 and source[i - 1] == "."
            after_backtick = i > 0 and source[i - 1] == "`"
            j = i
            while j < n and (source[j].isalnum() or source[j] in IDENT_CONT_CHARS):
                j += 1
            tok_text = source[i:j]
            tokens.append(
                LeanToken(
                    tok_text,
                    bdepth,
                    interp_depth,
                    after_dot=after_dot,
                    after_backtick=after_backtick,
                    in_attr=in_attr,
                )
            )
            last_ident_end = j
            last_ident_text = tok_text
            i = j
        else:
            if in_attr and ch not in " \t\r\n,":
                tokens.append(
                    LeanToken("<attr_arg>", bdepth, interp_depth, after_dot=False, after_backtick=False, in_attr=True)
                )
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
            and not tok.after_backtick
            and tok.bdepth == 0
            and tok.interp_depth == 0
            and tok.text in PURE_DECL_MODIFIERS
        ):
            idx += 1
            continue
        return (None if (tok.after_dot or tok.after_backtick) else tok.text), idx
    return None, idx


def extract_unit_head(unit_text: str) -> str | None:
    """Return the declaration/command keyword of a unit after stripping comments, `@[...]`, and modifiers."""
    tokens, end_state = scan_lean(unit_text)
    if not end_state.is_top_level:
        return None
    head, _ = _extract_head_from_tokens(tokens)
    return head


def _update_mutual_depth(tokens: list[LeanToken], mutual_depth: int) -> int:
    """Update `mutual` nesting depth across top-level tokens on one line."""
    for tok in tokens:
        if tok.after_dot or tok.after_backtick or tok.bdepth > 0 or tok.interp_depth > 0:
            continue
        if tok.text == "mutual":
            mutual_depth += 1
        elif tok.text == "end" and mutual_depth > 0:
            mutual_depth -= 1
    return mutual_depth


def split_lean_units(source: str) -> tuple[list[str], bool]:
    """Split Lean source into top-level units plus whether lexer state ended cleanly."""
    units: list[str] = []
    cur_lines: list[str] = []
    lex_state = LeanLexState()
    mutual_depth = 0

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
            if mutual_depth > 0:
                cur_lines.append(ln)
                mutual_depth = _update_mutual_depth(line_tokens, mutual_depth)
            elif cur_lines and (first_tok in CONTINUATION_TOKENS or ln.startswith("|")):
                cur_lines.append(ln)
            elif cur_lines and extract_unit_head("\n".join(cur_lines)) is None:
                if first_tok in ("end", "/-!") or ln.startswith("/-!"):
                    flush()
                    cur_lines.append(ln)
                else:
                    cur_lines.append(ln)
                    if extract_unit_head("\n".join(cur_lines)) == "mutual":
                        mutual_depth = _update_mutual_depth(line_tokens, 0)
            else:
                flush()
                cur_lines.append(ln)
                if extract_unit_head("\n".join(cur_lines)) == "mutual":
                    mutual_depth = _update_mutual_depth(line_tokens, 0)
        else:
            if cur_lines or ln.strip():
                cur_lines.append(ln)
            if mutual_depth > 0:
                mutual_depth = _update_mutual_depth(line_tokens, mutual_depth)
        lex_state = next_state
    flush()
    clean_eof = lex_state.is_top_level and mutual_depth == 0
    return units, clean_eof


def _validate_unit_attrs(tokens: list[LeanToken], unit_text: str) -> str | None:
    """Validate that every `@[...]` attribute token in a unit belongs to `SAFE_DECL_ATTRS`."""
    for tok in tokens:
        if tok.in_attr:
            if tok.after_dot or tok.after_backtick or tok.bdepth != 1 or tok.text not in SAFE_DECL_ATTRS:
                return f"disallowed attribute '@[{tok.text}]' in unit: {unit_preview(unit_text)}"
    return None


def validate_pure_added_unit(unit_text: str) -> str | None:
    """Return None if `unit_text` is a single pure declaration addition, else an error reason."""
    tokens, end_state = scan_lean(unit_text)
    if not end_state.is_top_level:
        return f"unclosed syntax in added unit: {unit_preview(unit_text)}"

    attr_err = _validate_unit_attrs(tokens, unit_text)
    if attr_err is not None:
        return attr_err

    head_tok, head_idx = _extract_head_from_tokens(tokens)
    if head_tok not in PURE_DECL_HEADS:
        return f"appended non-declaration item ({head_tok or 'comment'}): {unit_preview(unit_text)}"

    if head_tok == "mutual":
        if head_idx > 0:
            return f"disallowed prefix on mutual block: {unit_preview(unit_text)}"
        mutual_disallowed = NON_DECL_COMMANDS | DISALLOWED_DECL_HEADS
        mutual_depth = 1
        for tok in tokens[head_idx + 1 :]:
            if tok.in_attr or tok.interp_depth > 0 or tok.after_dot or tok.after_backtick:
                continue
            if mutual_depth == 0:
                return f"trailing token '{tok.text}' after mutual 'end': {unit_preview(unit_text)}"
            if tok.text in mutual_disallowed or tok.text.startswith("#"):
                return f"disallowed command '{tok.text}' inside mutual block: {unit_preview(unit_text)}"
            if tok.bdepth == 0:
                if tok.text == "mutual":
                    mutual_depth += 1
                elif tok.text == "end":
                    mutual_depth -= 1
            elif tok.text in ("mutual", "end"):
                return f"disallowed keyword '{tok.text}' inside mutual block: {unit_preview(unit_text)}"
        if mutual_depth != 0:
            return f"unclosed mutual block: {unit_preview(unit_text)}"
        return None

    disallowed_inner = NON_DECL_COMMANDS | DISALLOWED_DECL_HEADS | PURE_DECL_HEADS | {"end"}
    for tok in tokens[head_idx + 1 :]:
        if tok.in_attr or tok.interp_depth > 0 or tok.after_dot or tok.after_backtick:
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


def _is_valid_dotted_name(tokens: list[LeanToken], blocked: frozenset[str]) -> bool:
    """Return True if `tokens` form a single plain dotted identifier chain."""
    if not tokens or tokens[0].after_dot:
        return False
    for idx, tok in enumerate(tokens):
        if tok.in_attr or tok.bdepth > 0 or tok.interp_depth > 0 or tok.after_backtick:
            return False
        if idx > 0 and not tok.after_dot:
            return False
        if tok.text in blocked or tok.text.startswith("#"):
            return False
    return True


def validate_new_spec_file(rel_path: str, head_text: str) -> tuple[bool, str]:
    """Validate a newly added (`status == 'A'`) locked spec file for `spec-add` eligibility."""
    path_obj = Path(rel_path)
    is_interface_file = path_obj.name == "Interface.lean" or (
        path_obj.parts[:1] == ("LeanSwe",)
        and rel_path.endswith(".lean")
        and "Interface" in path_obj.parts[1:-1]
    )
    if (path_obj.parts and path_obj.parts[0] == "Core") or is_interface_file:
        return False, f"new locked spec file '{rel_path}' expands Core or Interface boundary"

    head_units, head_clean = split_lean_units(head_text)
    if not head_clean or not head_units:
        return False, "new locked spec file is empty or has unclosed syntax"

    blocked_framing_words = (
        NON_DECL_COMMANDS | DISALLOWED_DECL_HEADS | PURE_DECL_HEADS | NON_RESERVED_HEAD_COMMANDS | {"end"}
    )
    seen_decl = False
    pure_decl_count = 0
    ns_stack: list[str] = []

    for unit in head_units:
        tokens, end_state = scan_lean(unit)
        if not end_state.is_top_level:
            return False, f"unclosed syntax in new spec unit: {unit_preview(unit)}"
        if not tokens:
            return False, f"standalone comment or empty unit in new spec file: {unit_preview(unit)}"

        first = tokens[0]
        if (
            not first.in_attr
            and first.bdepth == 0
            and first.interp_depth == 0
            and not first.after_dot
            and not first.after_backtick
        ):
            head0 = first.text
            if head0 == "/-!":
                if len(tokens) != 1:
                    return False, f"unexpected code after module docstring: {unit_preview(unit)}"
                continue
            if head0 == "import":
                if seen_decl or ns_stack:
                    return False, f"import must precede declarations and namespaces: {unit_preview(unit)}"
                if not _is_valid_dotted_name(tokens[1:], blocked_framing_words):
                    return False, f"disallowed import framing in new spec file: {unit_preview(unit)}"
                continue
            if head0 == "namespace":
                if not _is_valid_dotted_name(tokens[1:], blocked_framing_words):
                    return False, f"disallowed namespace framing in new spec file: {unit_preview(unit)}"
                ns_stack.extend(tok.text for tok in tokens[1:])
                continue
            if head0 == "open":
                if len(tokens) < 2 or any(
                    tok.in_attr
                    or tok.interp_depth > 0
                    or tok.after_backtick
                    or tok.text.startswith("#")
                    or tok.text in blocked_framing_words
                    or tok.text in ("scoped", "in")
                    for tok in tokens[1:]
                ):
                    return False, f"disallowed 'open' framing in new spec file: {unit_preview(unit)}"
                continue
            if head0 == "end":
                if len(tokens) == 1:
                    if not ns_stack:
                        return False, f"unmatched 'end' in new spec file: {unit_preview(unit)}"
                    ns_stack.pop()
                    continue
                if not _is_valid_dotted_name(tokens[1:], blocked_framing_words):
                    return False, f"disallowed 'end' framing in new spec file: {unit_preview(unit)}"
                segs = [tok.text for tok in tokens[1:]]
                if len(segs) > len(ns_stack) or ns_stack[-len(segs) :] != segs:
                    return False, f"mismatched 'end {'.'.join(segs)}' in new spec file"
                del ns_stack[-len(segs) :]
                continue

        err = validate_pure_added_unit(unit)
        if err is not None:
            return False, err
        seen_decl = True
        pure_decl_count += 1

    if ns_stack:
        return False, f"unclosed namespace '{'.'.join(ns_stack)}' in new spec file"
    if pure_decl_count < 1:
        return False, "new locked spec file contains no pure declarations"
    return True, f"new locked spec file adding {pure_decl_count} pure declaration(s)"


def classify_locked_spec_diff(
    repo_root: Path,
    base_ref: str,
    head_ref: str,
    status: str,
    paths: list[str],
) -> LockedDiffAssessment:
    """Determine whether one touched locked spec file requires `spec-add` or `spec-change`."""
    hit = f"{status}\t{' -> '.join(paths)}"
    if any(p in LOCKED_SPEC_JSON_PATHS for p in paths):
        if status == "M" and paths == [PACKAGE_MANIFEST_PATH]:
            base_text = git_show_text(repo_root, base_ref, PACKAGE_MANIFEST_PATH)
            head_text = git_show_text(repo_root, head_ref, PACKAGE_MANIFEST_PATH)
            req_label, reason = classify_package_manifest_texts(
                base_text, head_text, base_top_pkgs=set(), allow_new_packages=False
            )
            return LockedDiffAssessment(hit, req_label or LABEL_ADD, reason)
        if (
            PACKAGE_MANIFEST_PATH in paths
            and git_file_exists(repo_root, base_ref, PACKAGE_MANIFEST_PATH)
            and git_file_exists(repo_root, head_ref, PACKAGE_MANIFEST_PATH)
        ):
            base_text = git_show_text(repo_root, base_ref, PACKAGE_MANIFEST_PATH)
            head_text = git_show_text(repo_root, head_ref, PACKAGE_MANIFEST_PATH)
            downgraded, _ = find_manifest_kind_downgrades(base_text, head_text)
            if downgraded:
                return LockedDiffAssessment(
                    hit,
                    LABEL_CHANGE,
                    f"downgraded package kind 'model' -> 'property' for {', '.join(downgraded)}",
                )
        target = next(p for p in reversed(paths) if p in LOCKED_SPEC_JSON_PATHS)
        return LockedDiffAssessment(
            hit, LABEL_CHANGE, f"locked spec metadata '{target}' changed (status '{status}')"
        )
    if status[0] in ("D", "R", "C"):
        return LockedDiffAssessment(hit, LABEL_CHANGE, f"spec file status '{status}' alters or removes existing spec")
    if status == "A" and len(paths) == 1:
        head_text = git_show_text(repo_root, head_ref, paths[0])
        ok, reason = validate_new_spec_file(paths[0], head_text)
        return LockedDiffAssessment(hit, LABEL_ADD if ok else LABEL_CHANGE, reason)
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


def _is_nonneg_int(val: object) -> bool:
    """Return True if val is an int (excluding bool) >= 0."""
    return isinstance(val, int) and not isinstance(val, bool) and val >= 0


def _check_budget_files_ratchet(base_files: object, head_files: object) -> str | None:
    """Return a loosen-reason string if 'files' loosened or broke schema, else None."""
    if not isinstance(base_files, dict) or not isinstance(head_files, dict):
        return "invalid 'files' section in .foreign-budget.json"
    for path, head_entry in head_files.items():
        if path not in base_files:
            return f"added foreign budget entry '{path}'"
        base_entry = base_files[path]
        if not isinstance(base_entry, dict) or not isinstance(head_entry, dict):
            return f"invalid entry object for '{path}'"
        if not set(head_entry.keys()).issubset(BUDGET_FILE_KEYS):
            return f"unknown key in entry '{path}'"
        base_max = base_entry.get("max_lines")
        head_max = head_entry.get("max_lines")
        if not _is_nonneg_int(base_max) or not _is_nonneg_int(head_max):
            return f"invalid max_lines in '{path}'"
        if head_max > base_max:
            return f"raised max_lines on '{path}' ({base_max} -> {head_max})"
        base_leg = base_entry.get("legacy_unmigrated")
        head_leg = head_entry.get("legacy_unmigrated")
        if not isinstance(base_leg, bool) or not isinstance(head_leg, bool):
            return f"invalid legacy_unmigrated in '{path}'"
        if not base_leg and head_leg:
            return f"loosened legacy_unmigrated on '{path}' (false -> true)"
    return None


def _check_budget_vendored_ratchet(base_vend: object, head_vend: object) -> str | None:
    """Return a loosen-reason string if 'vendored_files' loosened or changed hash, else None."""
    if not isinstance(base_vend, dict) or not isinstance(head_vend, dict):
        return "invalid 'vendored_files' section in .foreign-budget.json"
    for path, head_entry in head_vend.items():
        if path not in base_vend:
            return f"added vendored file entry '{path}'"
        base_entry = base_vend[path]
        if not isinstance(base_entry, dict) or not isinstance(head_entry, dict):
            return f"invalid vendored entry for '{path}'"
        if not set(head_entry.keys()).issubset(BUDGET_VENDORED_KEYS):
            return f"unknown key in vendored entry '{path}'"
        base_sha = base_entry.get("sha256")
        head_sha = head_entry.get("sha256")
        if not isinstance(base_sha, str) or not isinstance(head_sha, str):
            return f"invalid sha256 in vendored entry '{path}'"
        if head_sha != base_sha:
            return f"changed vendored sha256 on '{path}'"
        if "max_lines" in base_entry and "max_lines" not in head_entry:
            return f"removed vendored max_lines cap on '{path}'"
        if "max_lines" in head_entry:
            head_max = head_entry["max_lines"]
            if not _is_nonneg_int(head_max):
                return f"invalid vendored max_lines on '{path}'"
            if "max_lines" in base_entry:
                base_max = base_entry["max_lines"]
                if not _is_nonneg_int(base_max) or head_max > base_max:
                    return f"raised vendored max_lines on '{path}' ({base_max} -> {head_max})"
    return None


def _effective_override_limits(entry: object, fn_key: str) -> tuple[tuple[int, int, int, int, bool] | None, str | None]:
    """Compute `(max_code_lines, max_branches, max_for_loops, max_other_loops, allow_poll)` for an override."""
    if not isinstance(entry, dict):
        return None, f"invalid function_overrides object for '{fn_key}'"
    if not set(entry.keys()).issubset(BUDGET_OVERRIDE_KEYS):
        return None, f"unknown key in function_overrides '{fn_key}'"
    lines = entry.get("max_code_lines", 35)
    if not _is_nonneg_int(lines):
        return None, f"invalid max_code_lines in function_overrides '{fn_key}'"
    branches = entry.get("max_branches", 8)
    if not _is_nonneg_int(branches):
        return None, f"invalid max_branches in function_overrides '{fn_key}'"
    allow_copy = entry.get("allow_array_copy_loop", False)
    if not isinstance(allow_copy, bool):
        return None, f"invalid allow_array_copy_loop in function_overrides '{fn_key}'"
    allow_poll = entry.get("allow_poll", False)
    if not isinstance(allow_poll, bool):
        return None, f"invalid allow_poll in function_overrides '{fn_key}'"
    if "max_loops" in entry:
        max_loops = entry["max_loops"]
        if not _is_nonneg_int(max_loops):
            return None, f"invalid max_loops in function_overrides '{fn_key}'"
        max_for = max_loops
        max_other = max_loops
    elif allow_copy:
        max_for = 1
        max_other = 0
    else:
        max_for = 0
        max_other = 0
    return (lines, branches, max_for, max_other, allow_poll), None


def _check_budget_overrides_ratchet(base_ov: object, head_ov: object) -> str | None:
    """Return a loosen-reason string if 'function_overrides' added or loosened effective limits, else None."""
    if base_ov is None:
        base_ov = {}
    if head_ov is None:
        head_ov = {}
    if not isinstance(base_ov, dict) or not isinstance(head_ov, dict):
        return "invalid 'function_overrides' section in .foreign-budget.json"
    default_limits = (35, 8, 0, 0, False)
    for fn_key in set(base_ov.keys()) | set(head_ov.keys()):
        if fn_key not in base_ov:
            return f"added function_overrides entry '{fn_key}'"
        base_limits, err = _effective_override_limits(base_ov[fn_key], fn_key)
        if err is not None or base_limits is None:
            return err
        if fn_key not in head_ov:
            head_limits = default_limits
        else:
            head_limits, err = _effective_override_limits(head_ov[fn_key], fn_key)
            if err is not None or head_limits is None:
                return err
        base_lines, base_br, base_for, base_other, base_poll = base_limits
        head_lines, head_br, head_for, head_other, head_poll = head_limits
        if head_lines > base_lines:
            return f"raised max_code_lines on '{fn_key}' ({base_lines} -> {head_lines})"
        if head_br > base_br:
            return f"raised max_branches on '{fn_key}' ({base_br} -> {head_br})"
        if head_for > base_for or head_other > base_other:
            return f"loosened loop allowance on '{fn_key}'"
        if not base_poll and head_poll:
            return f"loosened allow_poll on '{fn_key}'"
    return None


def _check_budget_thread_helpers_ratchet(base_helpers: object, head_helpers: object) -> str | None:
    """Return a loosen-reason string if 'named_thread_helpers' gained entries, else None."""
    if base_helpers is None:
        base_helpers = []
    if head_helpers is None:
        head_helpers = []
    if not isinstance(base_helpers, list) or not isinstance(head_helpers, list):
        return "invalid 'named_thread_helpers' section in .foreign-budget.json"
    if not all(isinstance(x, str) for x in base_helpers) or not all(isinstance(x, str) for x in head_helpers):
        return "non-string item in 'named_thread_helpers'"
    added = sorted(set(head_helpers) - set(base_helpers))
    if added:
        return f"added named_thread_helpers entry '{added[0]}'"
    return None


def _strict_object_pairs_hook(pairs: list[tuple[str, object]]) -> dict[str, object]:
    """Decode JSON object while rejecting duplicate keys."""
    out: dict[str, object] = {}
    for key, value in pairs:
        if key in out:
            raise ValueError(f"duplicate JSON key '{key}'")
        out[key] = value
    return out


def _reject_json_constant(token: str) -> object:
    """Reject non-standard JSON constants such as NaN and Infinity."""
    raise ValueError(f"invalid JSON constant '{token}'")


def _loads_strict_json(text: str) -> object:
    """Parse JSON while forbidding duplicate keys and non-finite numeric constants."""
    return json.loads(
        text,
        object_pairs_hook=_strict_object_pairs_hook,
        parse_constant=_reject_json_constant,
    )


def classify_foreign_budget_texts(base_text: str, head_text: str) -> str | None:
    """Return None when head .foreign-budget.json only tightens or keeps base, else loosen reason."""
    try:
        base_obj = _loads_strict_json(base_text)
        head_obj = _loads_strict_json(head_text)
    except (json.JSONDecodeError, ValueError) as exc:
        return f"invalid JSON in .foreign-budget.json: {exc}"
    if not isinstance(base_obj, dict) or not isinstance(head_obj, dict):
        return ".foreign-budget.json root must be a JSON object"
    if not set(head_obj.keys()).issubset(BUDGET_ROOT_KEYS):
        return "unknown top-level key in .foreign-budget.json"
    base_ver = base_obj.get("version")
    head_ver = head_obj.get("version")
    if not _is_nonneg_int(base_ver) or not _is_nonneg_int(head_ver) or head_ver != base_ver:
        return "changed or invalid version in .foreign-budget.json"
    for checker, key in (
        (_check_budget_files_ratchet, "files"),
        (_check_budget_vendored_ratchet, "vendored_files"),
        (_check_budget_overrides_ratchet, "function_overrides"),
        (_check_budget_thread_helpers_ratchet, "named_thread_helpers"),
    ):
        err = checker(base_obj.get(key), head_obj.get(key))
        if err is not None:
            return err
    return None


def classify_foreign_budget_diff(
    repo_root: Path,
    base_ref: str,
    head_ref: str,
    status: str,
    paths: list[str],
) -> LockedDiffAssessment | None:
    """Return an `add-foreign-lang` assessment if `.foreign-budget.json` loosened, else None."""
    hit = f"{status}\t{' -> '.join(paths)}"
    if status != "M" or paths != [FOREIGN_BUDGET_PATH]:
        return LockedDiffAssessment(
            hit,
            LABEL_FOREIGN,
            f"foreign budget status '{status}' alters or introduces '{FOREIGN_BUDGET_PATH}'",
        )
    base_text = git_show_text(repo_root, base_ref, FOREIGN_BUDGET_PATH)
    head_text = git_show_text(repo_root, head_ref, FOREIGN_BUDGET_PATH)
    reason = classify_foreign_budget_texts(base_text, head_text)
    if reason is not None:
        return LockedDiffAssessment(hit, LABEL_FOREIGN, reason)
    return None


def has_extern_attribute(source: str) -> bool:
    """Return True if Lean source declares an `extern` attribute (`@[...]` or `attribute [...]`)."""
    if "extern" not in source:
        return False
    tokens, _ = scan_lean(source)
    for idx, tok in enumerate(tokens):
        if tok.after_dot or tok.after_backtick or tok.interp_depth > 0:
            continue
        if tok.in_attr and tok.bdepth == 1 and tok.text == "extern":
            return True
        if not tok.in_attr and tok.bdepth == 0 and tok.text == "attribute":
            j = idx + 1
            while j < len(tokens) and tokens[j].bdepth >= 1:
                inner = tokens[j]
                if (
                    inner.bdepth == 1
                    and not inner.after_dot
                    and not inner.after_backtick
                    and inner.interp_depth == 0
                    and inner.text == "extern"
                ):
                    return True
                j += 1
    return False


def _is_valid_manifest_pkg_name(pkg: str) -> bool:
    """Return True if pkg is a valid dotted `LeanSwe.<Pkg>` identifier."""
    if not pkg.startswith("LeanSwe."):
        return False
    segs = pkg.split(".")
    if len(segs) < 2:
        return False
    for seg in segs[1:]:
        if not seg or not seg[0].isalpha() or not all(ch.isalnum() or ch == "_" for ch in seg):
            return False
        if seg in NON_PACKAGE_SUBDIRS:
            return False
    return True


def _discover_packages_from_lean_paths(lean_paths: list[str]) -> tuple[set[str], set[str]]:
    """Return `(discovered_pkgs, all_lean_dirs)` from repo-relative `.lean` paths under `LeanSwe/`."""
    discovered: set[str] = set()
    all_lean_dirs: set[str] = set()
    for rel_path in lean_paths:
        p = Path(rel_path)
        parts = p.parts
        if len(parts) < 3 or parts[0] != "LeanSwe" or not rel_path.endswith(".lean"):
            continue
        parent_parts = parts[:-1]
        all_lean_dirs.add("/".join(parent_parts))
        if parts[-1] in ("Interface.lean", "Types.lean") and not any(
            seg in NON_PACKAGE_SUBDIRS for seg in parent_parts[1:]
        ):
            discovered.add(".".join(parent_parts))
    return discovered, all_lean_dirs


def _owner_package_for_lean_path(rel_path: str, sorted_pkg_prefixes: list[tuple[str, str]]) -> str | None:
    """Return the deepest package owning rel_path by longest directory prefix match."""
    for dir_prefix, pkg in sorted_pkg_prefixes:
        if rel_path.startswith(dir_prefix):
            return pkg
    return None


def find_manifest_kind_downgrades(base_text: str, head_text: str) -> tuple[list[str], str | None]:
    """Return `(downgraded_pkgs, parse_err)` for packages changing kind `'model' -> 'property'`."""
    try:
        base_obj = _loads_strict_json(base_text)
        head_obj = _loads_strict_json(head_text)
    except (json.JSONDecodeError, ValueError) as exc:
        return [], str(exc)
    if not isinstance(base_obj, dict) or not isinstance(head_obj, dict):
        return [], "manifest root must be a JSON object"
    base_pkgs = base_obj.get("packages")
    head_pkgs = head_obj.get("packages")
    if not isinstance(base_pkgs, dict) or not isinstance(head_pkgs, dict):
        return [], "manifest 'packages' must be a JSON object"
    downgraded: list[str] = []
    for pkg in sorted(set(base_pkgs.keys()) & set(head_pkgs.keys())):
        b_entry = base_pkgs[pkg]
        h_entry = head_pkgs[pkg]
        if (
            isinstance(b_entry, dict)
            and isinstance(h_entry, dict)
            and b_entry.get("kind") == "model"
            and h_entry.get("kind") == "property"
        ):
            downgraded.append(pkg)
    return downgraded, None


def _classify_existing_manifest_pkg_edit(pkg: str, base_entry: object, head_entry: object) -> tuple[str | None, str]:
    """Classify an edit to an existing manifest package entry.

    Returns `(None, "")` when unchanged, `(LABEL_ADD, reason)` for pure strengthenings,
    or `(LABEL_CHANGE, reason)` for any downgrade or non-strengthening alteration.
    """
    if base_entry == head_entry:
        return None, ""
    if not isinstance(base_entry, dict) or not isinstance(head_entry, dict):
        return LABEL_CHANGE, f"altered entry shape for '{pkg}'"
    if not set(head_entry.keys()).issubset(MANIFEST_PKG_ALL_KEYS):
        return LABEL_CHANGE, f"unknown key(s) added to '{pkg}'"

    b_kind = base_entry.get("kind")
    h_kind = head_entry.get("kind")
    if b_kind == "model" and h_kind == "property":
        return LABEL_CHANGE, f"downgraded package kind 'model' -> 'property' for {pkg}"
    if b_kind != h_kind and not (b_kind == "property" and h_kind == "model"):
        return LABEL_CHANGE, f"changed kind on '{pkg}' ({b_kind!r} -> {h_kind!r})"

    b_ext = base_entry.get("external_boundary")
    h_ext = head_entry.get("external_boundary")
    if not isinstance(b_ext, bool) or not isinstance(h_ext, bool):
        return LABEL_CHANGE, f"invalid external_boundary on '{pkg}'"
    if b_ext and not h_ext:
        return LABEL_CHANGE, f"loosened external_boundary on '{pkg}' (true -> false)"

    b_has_suite = "fuzz_suite" in base_entry
    h_has_suite = "fuzz_suite" in head_entry
    if b_has_suite and not h_has_suite:
        return LABEL_CHANGE, f"removed fuzz_suite on '{pkg}'"
    if b_has_suite and h_has_suite and base_entry["fuzz_suite"] != head_entry["fuzz_suite"]:
        return (
            LABEL_CHANGE,
            f"changed fuzz_suite on '{pkg}' ({base_entry['fuzz_suite']!r} -> {head_entry['fuzz_suite']!r})",
        )
    if not b_has_suite and h_has_suite:
        h_suite = head_entry["fuzz_suite"]
        if not isinstance(h_suite, str) or not h_suite:
            return LABEL_CHANGE, f"invalid fuzz_suite added on '{pkg}'"

    b_deps = base_entry.get("deps")
    h_deps = head_entry.get("deps")
    if (
        not isinstance(b_deps, list)
        or not isinstance(h_deps, list)
        or not all(isinstance(x, str) for x in b_deps)
        or not all(isinstance(x, str) for x in h_deps)
    ):
        return LABEL_CHANGE, f"invalid deps on '{pkg}'"
    removed_deps = sorted(set(b_deps) - set(h_deps))
    if removed_deps:
        return LABEL_CHANGE, f"removed deps on '{pkg}': {', '.join(removed_deps)}"

    for key in ("purity", "err_msg_opaque", "spec_style"):
        if (key in base_entry) != (key in head_entry) or base_entry.get(key) != head_entry.get(key):
            return LABEL_CHANGE, f"modified '{key}' on '{pkg}'"

    changes: list[str] = []
    if b_kind == "property" and h_kind == "model":
        changes.append("kind 'property' -> 'model'")
    if not b_ext and h_ext:
        changes.append("external_boundary false -> true")
    if not b_has_suite and h_has_suite:
        changes.append(f"added fuzz_suite '{head_entry['fuzz_suite']}'")
    added_deps = sorted(set(h_deps) - set(b_deps))
    if added_deps:
        changes.append(f"added deps {', '.join(added_deps)}")
    if not changes:
        return LABEL_CHANGE, f"reordered or reformatted entry '{pkg}'"
    return LABEL_ADD, f"strengthened '{pkg}' ({'; '.join(changes)})"


def classify_package_manifest_texts(
    base_text: str,
    head_text: str,
    base_top_pkgs: set[str],
    allow_new_packages: bool = ALLOW_NEW_PACKAGES,
) -> tuple[str | None, str]:
    """Classify a `scripts/package_manifest.json` modification into `(required_label, reason)`.

    Returns `(None, reason)` when `allow_new_packages` is True and only brand-new top-level
    packages absent from `base_top_pkgs` are added; `(LABEL_ADD, reason)` for pure additions
    or strengthenings (`property -> model`, adding `fuzz_suite`/`deps`, tightening
    `external_boundary`); or `(LABEL_CHANGE, reason)` for any downgrade, removal, or other edit.
    """
    try:
        base_obj = _loads_strict_json(base_text)
        head_obj = _loads_strict_json(head_text)
    except (json.JSONDecodeError, ValueError) as exc:
        return LABEL_CHANGE, f"invalid JSON in '{PACKAGE_MANIFEST_PATH}': {exc}"
    if not isinstance(base_obj, dict) or not isinstance(head_obj, dict):
        return LABEL_CHANGE, f"'{PACKAGE_MANIFEST_PATH}' root must be a JSON object"
    if set(base_obj.keys()) != MANIFEST_ROOT_KEYS or set(head_obj.keys()) != MANIFEST_ROOT_KEYS:
        return LABEL_CHANGE, f"changed top-level keys in '{PACKAGE_MANIFEST_PATH}'"
    base_ver = base_obj.get("version")
    head_ver = head_obj.get("version")
    if isinstance(base_ver, bool) or isinstance(head_ver, bool) or base_ver != 1 or head_ver != 1:
        return LABEL_CHANGE, f"changed or invalid version in '{PACKAGE_MANIFEST_PATH}'"
    base_pkgs = base_obj.get("packages")
    head_pkgs = head_obj.get("packages")
    if not isinstance(base_pkgs, dict) or not isinstance(head_pkgs, dict):
        return LABEL_CHANGE, f"'{PACKAGE_MANIFEST_PATH}' 'packages' must be a JSON object"

    downgraded = [
        pkg
        for pkg in sorted(set(base_pkgs.keys()) & set(head_pkgs.keys()))
        if isinstance(base_pkgs[pkg], dict)
        and isinstance(head_pkgs[pkg], dict)
        and base_pkgs[pkg].get("kind") == "model"
        and head_pkgs[pkg].get("kind") == "property"
    ]
    if downgraded:
        return LABEL_CHANGE, f"downgraded package kind 'model' -> 'property' for {', '.join(downgraded)}"

    removed = sorted(set(base_pkgs.keys()) - set(head_pkgs.keys()))
    if removed:
        return LABEL_CHANGE, f"removed manifest package(s): {', '.join(removed)}"

    strengthened: list[str] = []
    for pkg in sorted(base_pkgs.keys()):
        req, reason = _classify_existing_manifest_pkg_edit(pkg, base_pkgs[pkg], head_pkgs[pkg])
        if req == LABEL_CHANGE:
            return LABEL_CHANGE, reason
        if req == LABEL_ADD:
            strengthened.append(reason)

    added = sorted(set(head_pkgs.keys()) - set(base_pkgs.keys()))
    for pkg in added:
        if not isinstance(pkg, str) or not _is_valid_manifest_pkg_name(pkg):
            return LABEL_CHANGE, f"invalid added package name '{pkg}' in '{PACKAGE_MANIFEST_PATH}'"
        if not isinstance(head_pkgs[pkg], dict):
            return LABEL_CHANGE, f"invalid added package entry '{pkg}' in '{PACKAGE_MANIFEST_PATH}'"

    if not added and not strengthened:
        return LABEL_CHANGE, f"no semantic package addition or strengthening in '{PACKAGE_MANIFEST_PATH}'"

    if added and not strengthened and allow_new_packages:
        if all(f"LeanSwe/{pkg.split('.')[1]}" not in base_top_pkgs for pkg in added):
            return None, f"added manifest entries for brand-new package(s): {', '.join(added)}"

    parts: list[str] = []
    if added:
        parts.append(f"added manifest package(s): {', '.join(added)}")
    if strengthened:
        parts.append("; ".join(strengthened))
    return LABEL_ADD, "; ".join(parts)


def _validate_manifest_data(
    manifest_text: str,
    suites_text: str | None,
    lean_paths: list[str],
    read_lean_text,
) -> list[str]:
    """Validate package manifest schema, 100% coverage, external-boundary rules, and fuzz suites."""
    errors: list[str] = []
    try:
        manifest_obj = _loads_strict_json(manifest_text)
    except (json.JSONDecodeError, ValueError) as exc:
        return [f"invalid JSON in '{PACKAGE_MANIFEST_PATH}': {exc}"]

    if not isinstance(manifest_obj, dict):
        return [f"'{PACKAGE_MANIFEST_PATH}' root must be a JSON object"]
    unknown_root = sorted(set(manifest_obj.keys()) - MANIFEST_ROOT_KEYS)
    missing_root = sorted(MANIFEST_ROOT_KEYS - set(manifest_obj.keys()))
    if missing_root:
        errors.append(f"missing top-level key(s) in '{PACKAGE_MANIFEST_PATH}': {', '.join(missing_root)}")
    if unknown_root:
        errors.append(f"unknown top-level key(s) in '{PACKAGE_MANIFEST_PATH}': {', '.join(unknown_root)}")

    version = manifest_obj.get("version")
    if isinstance(version, bool) or version != 1:
        errors.append(f"'{PACKAGE_MANIFEST_PATH}' version must be integer 1")

    packages = manifest_obj.get("packages")
    if not isinstance(packages, dict):
        errors.append(f"'{PACKAGE_MANIFEST_PATH}' 'packages' must be a JSON object")
        return errors

    valid_suites: set[str] | None = None
    if suites_text is not None:
        try:
            suites_obj = _loads_strict_json(suites_text)
        except (json.JSONDecodeError, ValueError) as exc:
            errors.append(f"invalid JSON in '{FUZZ_SUITES_PATH}': {exc}")
        else:
            if not isinstance(suites_obj, dict) or not isinstance(suites_obj.get("suites"), dict):
                errors.append(f"'{FUZZ_SUITES_PATH}' must contain a 'suites' object")
            else:
                valid_suites = set(suites_obj["suites"].keys())

    discovered_pkgs, all_lean_dirs = _discover_packages_from_lean_paths(lean_paths)

    for pkg, entry in packages.items():
        if not isinstance(pkg, str) or not _is_valid_manifest_pkg_name(pkg):
            errors.append(f"invalid package name '{pkg}' in '{PACKAGE_MANIFEST_PATH}'")
            continue
        if not isinstance(entry, dict):
            errors.append(f"package '{pkg}' entry must be a JSON object")
            continue

        missing_keys = sorted(MANIFEST_PKG_REQUIRED_KEYS - set(entry.keys()))
        unknown_keys = sorted(set(entry.keys()) - MANIFEST_PKG_ALL_KEYS)
        if missing_keys:
            errors.append(f"package '{pkg}' missing required key(s): {', '.join(missing_keys)}")
        if unknown_keys:
            errors.append(f"package '{pkg}' has unknown key(s): {', '.join(unknown_keys)}")

        kind = entry.get("kind")
        if kind not in MANIFEST_KINDS:
            errors.append(f"package '{pkg}' has invalid kind '{kind}' (expected one of {sorted(MANIFEST_KINDS)})")

        purity = entry.get("purity")
        if purity not in MANIFEST_PURITIES:
            errors.append(
                f"package '{pkg}' has invalid purity '{purity}' (expected one of {sorted(MANIFEST_PURITIES)})"
            )

        deps = entry.get("deps")
        if not isinstance(deps, list) or not all(isinstance(d, str) for d in deps):
            errors.append(f"package '{pkg}' field 'deps' must be a list of package names")
        else:
            if len(set(deps)) != len(deps):
                errors.append(f"package '{pkg}' has duplicate entries in 'deps'")
            if deps != sorted(deps):
                errors.append(f"package '{pkg}' field 'deps' must be sorted")
            for dep in deps:
                if dep == pkg:
                    errors.append(f"package '{pkg}' cannot list itself in 'deps'")
                elif dep not in packages:
                    errors.append(f"package '{pkg}' depends on unknown manifest package '{dep}'")

        ext_boundary = entry.get("external_boundary")
        if not isinstance(ext_boundary, bool):
            errors.append(f"package '{pkg}' field 'external_boundary' must be a boolean")
        elif kind == "property" and ext_boundary:
            errors.append(f"package '{pkg}' has external_boundary=true and cannot use kind='property'")

        if "err_msg_opaque" in entry and not isinstance(entry["err_msg_opaque"], bool):
            errors.append(f"package '{pkg}' field 'err_msg_opaque' must be a boolean")

        if "spec_style" in entry and entry["spec_style"] not in MANIFEST_SPEC_STYLES:
            errors.append(
                f"package '{pkg}' has invalid spec_style '{entry['spec_style']}' "
                f"(expected one of {sorted(MANIFEST_SPEC_STYLES)})"
            )

        if "fuzz_suite" in entry:
            suite = entry["fuzz_suite"]
            if not isinstance(suite, str) or not suite:
                errors.append(f"package '{pkg}' field 'fuzz_suite' must be a non-empty string")
            elif valid_suites is None:
                errors.append(
                    f"package '{pkg}' references fuzz_suite '{suite}' but '{FUZZ_SUITES_PATH}' is missing or invalid"
                )
            elif suite not in valid_suites:
                errors.append(
                    f"package '{pkg}' references unknown fuzz_suite '{suite}' (not in '{FUZZ_SUITES_PATH}')"
                )

        pkg_dir = pkg.replace(".", "/")
        if pkg_dir not in all_lean_dirs:
            errors.append(f"orphan manifest entry '{pkg}': directory '{pkg_dir}' has no Lean files on disk")
        elif kind != "support" and pkg not in discovered_pkgs:
            errors.append(
                f"orphan manifest entry '{pkg}': directory '{pkg_dir}' lacks Interface.lean and Types.lean"
            )

    for pkg in sorted(discovered_pkgs):
        if pkg not in packages:
            errors.append(f"missing package '{pkg}' in '{PACKAGE_MANIFEST_PATH}'")

    owner_candidates = {p for p in packages if isinstance(p, str) and _is_valid_manifest_pkg_name(p)} | discovered_pkgs
    sorted_pkg_prefixes = sorted(
        ((p.replace(".", "/") + "/", p) for p in owner_candidates),
        key=lambda item: (-len(item[0]), item[0]),
    )
    pkgs_with_extern: set[str] = set()
    for rel_path in lean_paths:
        if not rel_path.endswith(".lean"):
            continue
        owner = _owner_package_for_lean_path(rel_path, sorted_pkg_prefixes)
        if owner is None or owner not in packages or owner in pkgs_with_extern:
            continue
        if has_extern_attribute(read_lean_text(rel_path)):
            pkgs_with_extern.add(owner)

    for pkg in sorted(pkgs_with_extern):
        entry = packages.get(pkg)
        if not isinstance(entry, dict):
            continue
        if entry.get("kind") == "property":
            errors.append(f"package '{pkg}' contains @[extern] declarations and cannot use kind='property'")
        if entry.get("external_boundary") is False:
            errors.append(
                f"package '{pkg}' contains @[extern] declarations but manifest declares external_boundary=false"
            )

    return errors


def validate_package_manifest(
    repo_root: Path,
    manifest_rel_path: str = PACKAGE_MANIFEST_PATH,
    suites_rel_path: str = FUZZ_SUITES_PATH,
) -> list[str]:
    """Validate `scripts/package_manifest.json` against the working tree under `repo_root`."""
    manifest_path = repo_root / manifest_rel_path
    if not manifest_path.is_file():
        return [f"missing package manifest '{manifest_rel_path}'"]
    manifest_text = manifest_path.read_text(encoding="utf-8")

    suites_path = repo_root / suites_rel_path
    suites_text = suites_path.read_text(encoding="utf-8") if suites_path.is_file() else None

    lean_root = repo_root / "LeanSwe"
    lean_paths = (
        sorted(p.relative_to(repo_root).as_posix() for p in lean_root.rglob("*.lean"))
        if lean_root.is_dir()
        else []
    )
    return _validate_manifest_data(
        manifest_text,
        suites_text,
        lean_paths,
        lambda rel: (repo_root / rel).read_text(encoding="utf-8"),
    )


def git_grep_word_files(repo_root: Path, commit_ref: str, word: str, prefix: str) -> set[str]:
    """Return repo-relative paths under prefix at commit_ref matching whole word."""
    proc = subprocess.run(
        ["git", "grep", "-l", "-z", "-w", "--", word, commit_ref, "--", prefix],
        cwd=repo_root,
        capture_output=True,
    )
    if proc.returncode == 1:
        return set()
    if proc.returncode != 0:
        raise subprocess.CalledProcessError(proc.returncode, proc.args, proc.stdout, proc.stderr)
    raw = proc.stdout.decode("utf-8", errors="surrogateescape")
    ref_prefix = f"{commit_ref}:"
    out: set[str] = set()
    for tok in raw.split("\0"):
        if not tok:
            continue
        if tok.startswith(ref_prefix):
            out.add(tok[len(ref_prefix) :])
        else:
            out.add(tok)
    return out


def validate_package_manifest_at_ref(
    repo_root: Path,
    commit_ref: str,
    manifest_rel_path: str = PACKAGE_MANIFEST_PATH,
    suites_rel_path: str = FUZZ_SUITES_PATH,
) -> list[str]:
    """Validate `scripts/package_manifest.json` against the git tree at `commit_ref`."""
    if not git_file_exists(repo_root, commit_ref, manifest_rel_path):
        return [f"missing package manifest '{manifest_rel_path}' at '{commit_ref}'"]
    manifest_text = git_show_text(repo_root, commit_ref, manifest_rel_path)
    suites_text = (
        git_show_text(repo_root, commit_ref, suites_rel_path)
        if git_file_exists(repo_root, commit_ref, suites_rel_path)
        else None
    )
    lean_paths = [p for p in git_list_tree_files(repo_root, commit_ref, "LeanSwe") if p.endswith(".lean")]
    extern_candidates = git_grep_word_files(repo_root, commit_ref, "extern", "LeanSwe") if lean_paths else set()
    return _validate_manifest_data(
        manifest_text,
        suites_text,
        lean_paths,
        lambda rel: git_show_text(repo_root, commit_ref, rel) if rel in extern_candidates else "",
    )


def _parse_cli_label(value: str) -> str:
    """Validate comma-separated CLI `--label` values against known gate labels."""
    parts = [p.strip() for p in value.split(",") if p.strip()]
    if not parts or any(p not in ALL_GATE_LABELS for p in parts):
        raise argparse.ArgumentTypeError(
            f"invalid label '{value}' (choose from {sorted(ALL_GATE_LABELS)})"
        )
    return value


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint checking PR labels and `.foreign-budget.json` ratchet."""
    parser = argparse.ArgumentParser(
        description="Verify spec-add / spec-change / add-foreign-lang PR labels."
    )
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
        type=_parse_cli_label,
        help="Treat the given PR label(s) as present for local testing (repeatable or comma-separated).",
    )
    args = parser.parse_args(argv)

    repo_root = resolve_repo_root()
    effective_base = resolve_effective_base(repo_root, args.base, args.head)
    base_pkgs = existing_top_packages_at_base(repo_root, effective_base)
    entries = diff_entries(repo_root, effective_base, args.head)

    locked_assessments: list[LockedDiffAssessment] = []
    foreign_assessments: list[LockedDiffAssessment] = []
    new_pkg_spec_hits: list[str] = []
    budget_tightened = False

    for status, paths in entries:
        if FOREIGN_BUDGET_PATH in paths:
            budget_err = classify_foreign_budget_diff(repo_root, effective_base, args.head, status, paths)
            if budget_err is not None:
                foreign_assessments.append(budget_err)
            else:
                budget_tightened = True
        spec_paths = [p for p in paths if is_spec_file(p)]
        if not spec_paths:
            continue
        if ALLOW_NEW_PACKAGES and status == "A" and len(paths) == 1:
            pkg = top_package_dir(paths[0])
            if pkg is not None and pkg not in base_pkgs:
                new_pkg_spec_hits.append(f"{status}\t{paths[0]}")
                continue
        if status == "M" and paths == [PACKAGE_MANIFEST_PATH]:
            req_label, reason = classify_package_manifest_texts(
                git_show_text(repo_root, effective_base, PACKAGE_MANIFEST_PATH),
                git_show_text(repo_root, args.head, PACKAGE_MANIFEST_PATH),
                base_pkgs,
                ALLOW_NEW_PACKAGES,
            )
            if req_label is None:
                new_pkg_spec_hits.append(f"{status}\t{PACKAGE_MANIFEST_PATH}")
                continue
            locked_assessments.append(LockedDiffAssessment(f"{status}\t{PACKAGE_MANIFEST_PATH}", req_label, reason))
            continue
        locked_assessments.append(classify_locked_spec_diff(repo_root, effective_base, args.head, status, paths))

    event_file = Path(args.event_path) if args.event_path else None
    labels_present = read_pr_labels(event_file, args.label)

    has_manifest_base = git_file_exists(repo_root, effective_base, PACKAGE_MANIFEST_PATH)
    has_manifest_head = git_file_exists(repo_root, args.head, PACKAGE_MANIFEST_PATH)
    manifest_validated = has_manifest_base or has_manifest_head
    manifest_errors = (
        validate_package_manifest_at_ref(repo_root, args.head) if manifest_validated else []
    )

    failed = False
    if manifest_errors:
        failed = True
        print(
            f"MANIFEST_CHECK: failed ({len(manifest_errors)} error(s) in '{PACKAGE_MANIFEST_PATH}')",
            file=sys.stderr,
        )
        for err in manifest_errors:
            print(f"MANIFEST_ERROR: {err}", file=sys.stderr)

    if foreign_assessments and LABEL_FOREIGN not in labels_present:
        failed = True
        print(
            f"FOREIGN_BUDGET_CHECK: failed (missing '{LABEL_FOREIGN}' label for "
            f"loosening/adding '{FOREIGN_BUDGET_PATH}')",
            file=sys.stderr,
        )
        for a in foreign_assessments:
            print(
                f"UNMARKED_FOREIGN_BUDGET: {a.hit} ({a.reason}; apply label '{LABEL_FOREIGN}')",
                file=sys.stderr,
            )

    if locked_assessments:
        requires_change = any(a.required_label == LABEL_CHANGE for a in locked_assessments)
        required_label = LABEL_CHANGE if requires_change else LABEL_ADD
        if LABEL_CHANGE in labels_present:
            pass
        elif LABEL_ADD in labels_present and not requires_change:
            pass
        elif LABEL_ADD in labels_present and requires_change:
            failed = True
            print(
                f"SPEC_CHECK: failed (label '{LABEL_ADD}' allows pure appended declarations only, "
                f"but existing spec content was modified or removed; apply label '{LABEL_CHANGE}')",
                file=sys.stderr,
            )
            for a in locked_assessments:
                tag = "SPEC_CHANGE_REQUIRED" if a.required_label == LABEL_CHANGE else "SPEC_ADD_ONLY"
                hint = f"apply label '{LABEL_CHANGE}'" if a.required_label == LABEL_CHANGE else "covered if upgraded"
                print(f"{tag}: {a.hit} ({a.reason}; {hint})", file=sys.stderr)
        else:
            failed = True
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

    if failed:
        return 1

    if manifest_validated:
        print(f"MANIFEST_CHECK: ok ('{PACKAGE_MANIFEST_PATH}' verified)")

    if foreign_assessments:
        print(f"FOREIGN_BUDGET_CHECK: ok (label='{LABEL_FOREIGN}' present)")
        for a in foreign_assessments:
            print(f"  MARKED_FOREIGN_BUDGET: {a.hit} ({a.reason})")
    elif budget_tightened:
        print("FOREIGN_BUDGET_CHECK: ok (foreign-budget tightened; no label required)")

    if not locked_assessments:
        suffix = "; foreign-budget tightened" if budget_tightened else ""
        if new_pkg_spec_hits:
            print(
                f"SPEC_CHECK: ok (new-package spec files={len(new_pkg_spec_hits)}, "
                f"locked spec files touched=0{suffix})"
            )
        else:
            print(f"SPEC_CHECK: ok (spec files touched=0{suffix})")
        return 0

    requires_change = any(a.required_label == LABEL_CHANGE for a in locked_assessments)
    if LABEL_CHANGE in labels_present:
        print(
            f"SPEC_CHECK: ok (label='{LABEL_CHANGE}' present, "
            f"locked spec files touched={len(locked_assessments)})"
        )
        for a in locked_assessments:
            print(f"  MARKED_SPEC_EDIT: {a.hit} ({a.reason})")
        return 0

    print(
        f"SPEC_CHECK: ok (label='{LABEL_ADD}' present, "
        f"pure additions verified across {len(locked_assessments)} locked spec file(s))"
    )
    for a in locked_assessments:
        print(f"  MARKED_SPEC_ADD: {a.hit} ({a.reason})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
