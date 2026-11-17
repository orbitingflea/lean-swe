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
comment included) is byte-identical. Pure declaration additions (`def`, `theorem`, `abbrev`,
`structure`, `inductive`, `example`, `mutual`) with at most allowlisted `@[...]` attributes,
appended after all non-`end` base units (before any unchanged trailing `end` lines) or added as a
validated new `{Types,Model,SpecTests}.lean` file in an existing package, require `spec-add` (also
satisfied by `spec-change`). Any alteration (including adding fields to an existing
`EmpiricalAssumptions` structure, editing doc comments, or adding `assume`), removal, rename/copy,
middle insertion, new `Core/*.lean` or `Interface.lean`, `opaque`/`instance`/`class`, unsafe or
custom `@[...]` attributes, embedded/indented/same-line extra commands, or non-declaration
directive requires `spec-change`.
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


def read_pr_labels(event_path: Path | None, cli_labels: list[str]) -> set[str]:
    """Collect active spec labels from CLI flags and the GitHub PR event JSON payload."""
    labels = {lbl for lbl in cli_labels if lbl in (LABEL_ADD, LABEL_CHANGE)}
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
    if (path_obj.parts and path_obj.parts[0] == "Core") or path_obj.name == "Interface.lean":
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
    labels_present = read_pr_labels(event_file, args.label)

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
