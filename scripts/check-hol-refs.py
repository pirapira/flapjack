#!/usr/bin/env python3
"""Verify `@[hol "<path>" "<name>"]` cross-references and emit the HOL-to-Lean map.

Every Lean declaration that ports a HOL4 declaration carries
`@[hol "cakeml/.../fooScript.sml" "theorem_name"]` (see `Flapjack/HolRef.lean`
and `AGENTS.md`).  This script checks, without running Lean, that

* the cited file exists in the `cakeml` submodule, and
* a HOL declaration with exactly that name is declared in that file; when
  the name is duplicated, the tag must cite a matching source line
  (`Theorem`, `Triviality`, `Definition`, `Datatype`, `Inductive`,
  `CoInductive`, `Overload`, `Type`, or an SML-level `val name = ...`), and
* the Lean module carrying the tag is transitively imported from the library
  root `Flapjack.lean`, so `lake build Flapjack` actually elaborates it.  A
  tagged theorem in an orphaned module would otherwise count as ported while
  never being checked.

Usage:
  scripts/check-hol-refs.py            # check; exit 1 on any bad reference
  scripts/check-hol-refs.py --mapping  # also print a TSV mapping to stdout:
                                       #   lean_file:line  lean_decl  hol_path  hol_name[:line]
  scripts/check-hol-refs.py --orphans  # also list every non-test module that is
                                       # not reachable from Flapjack.lean (warning only)

Uses only the standard library.
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIRS = [ROOT / "Flapjack", ROOT / "Flapjack.lean"]

ATTR_RE = re.compile(r'\bhol\s+"([^"]+)"\s+"([^"]+)"(?:\s+(\d+))?')
QUALIFIER_RE = re.compile(r'\(\s*list_as_array\s*:=\s*\[([^]]*)\]\s*\)')
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|inductive|structure|class|opaque|axiom)\s+"
    r"([^\s:({\[]+)"
)
HOL_HEADER_KEYWORDS = (
    "Theorem",
    "Triviality",
    "Definition",
    "Datatype",
    "Inductive",
    "CoInductive",
    "Overload",
    "Type",
)
IMPORT_RE = re.compile(r"^import\s+(Flapjack(?:\.[A-Za-z0-9_]+)*)", re.M)


def module_name(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def reachable_modules(root: str = "Flapjack") -> set[str]:
    """Modules transitively imported from the library root."""
    seen: set[str] = set()
    stack = [root]
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        path = module_path(module)
        if not path.is_file():
            continue
        for imported in IMPORT_RE.findall(path.read_text(encoding="utf-8")):
            if imported not in seen:
                stack.append(imported)
    return seen


def lean_files() -> list[Path]:
    files: list[Path] = []
    for entry in LEAN_DIRS:
        if entry.is_file():
            files.append(entry)
        elif entry.is_dir():
            files.extend(sorted(entry.rglob("*.lean")))
    return files


def find_lean_decl(lines: list[str], start: int) -> str:
    """Name of the declaration that the attribute at `lines[start]` decorates."""
    for offset in range(0, 8):
        index = start + offset
        if index >= len(lines):
            break
        match = DECL_RE.match(lines[index])
        if match:
            return match.group(1)
    return "?"


def hol_attribute_sites(lines: list[str]):
    """Yield HOL attributes, including attributes split across Lean lines."""
    comment_depth = 0
    start: int | None = None
    chunks: list[str] = []
    for number, line in enumerate(lines, start=1):
        # Ignore documentation/examples in nestable Lean block comments.
        in_comment = comment_depth > 0
        comment_depth += line.count("/-") - line.count("-/")
        if in_comment or comment_depth > 0:
            continue
        stripped = line.lstrip()
        if stripped.startswith("--"):
            continue
        if start is None:
            if not stripped.startswith("@["):
                continue
            start = number
        chunks.append(stripped)
        if "]" not in stripped:
            continue
        attribute = " ".join(chunks)
        if "hol " in attribute:
            for hol_path, hol_name, hol_line in ATTR_RE.findall(attribute):
                qualifier = QUALIFIER_RE.search(attribute)
                fields = tuple(
                    field.strip()
                    for field in qualifier.group(1).split(",")
                ) if qualifier else ()
                yield start, hol_path, hol_name, int(hol_line) if hol_line else None, fields
        start = None
        chunks = []


def strip_lean_comments(text: str) -> str:
    """Remove nested Lean comments while preserving strings and line breaks."""
    result: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    line_comment = False
    while index < len(text):
        if line_comment:
            if text[index] == "\n":
                line_comment = False
                result.append("\n")
            else:
                result.append(" ")
            index += 1
        elif depth:
            if text.startswith("/-", index):
                depth += 1
                result.extend((" ", " "))
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                result.extend((" ", " "))
                index += 2
            else:
                result.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif in_string:
            char = text[index]
            result.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
        elif text.startswith("/-", index):
            depth = 1
            result.extend((" ", " "))
            index += 2
        elif text.startswith("--", index):
            line_comment = True
            result.extend((" ", " "))
            index += 2
        else:
            char = text[index]
            result.append(char)
            if char == '"':
                in_string = True
            index += 1
    return "".join(result)


def structure_fields(lines: list[str]) -> set[str]:
    """Collect field names declared by structures in one Lean module."""
    fields: set[str] = set()
    structure_indent: int | None = None
    for line in strip_lean_comments("\n".join(lines)).splitlines():
        structure = re.match(r"^(\s*)structure\s+[A-Za-z0-9_'.]+.*\bwhere\s*$", line)
        if structure:
            structure_indent = len(structure.group(1))
            continue
        if structure_indent is None:
            continue
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        if indent <= structure_indent:
            structure_indent = None
            continue
        field = re.match(r"^\s+([A-Za-z_][A-Za-z0-9_']*)\s*:", line)
        if field:
            fields.add(field.group(1))
    return fields


def has_list_array_witness(lines: list[str], field: str) -> bool:
    """Require a same-module, kernel-checked representation theorem for a field.

    The witness convention is `holListArrayWitness_<field>` and its theorem
    type must mention both `RepresentsHOLNodeList` and the qualified state field.
    Lake checks the theorem when it builds the tagged module.
    """
    source = strip_lean_comments("\n".join(lines))
    pattern = re.compile(
        rf"^\s*(?:@[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?"
        rf"(?:theorem|lemma)\s+holListArrayWitness_{re.escape(field)}\b"
        rf"(?P<type>[\s\S]*?):=",
        re.M,
    )
    for match in pattern.finditer(source):
        statement = match.group("type")
        if "RepresentsHOLNodeList" in statement and re.search(
            rf"\.\s*{re.escape(field)}\b", statement
        ):
            return True
    return False


def list_as_array_errors(lines: list[str], fields: tuple[str, ...], module: str) -> list[str]:
    """Validate qualified fields against local state declarations and witnesses."""
    errors: list[str] = []
    declared_fields = structure_fields(lines)
    for field in fields:
        if field not in declared_fields:
            errors.append(
                f"list_as_array field `{field}` is not a field of a Lean structure "
                f"declared in {module}"
            )
        if not has_list_array_witness(lines, field):
            errors.append(
                f"list_as_array field `{field}` has no same-module checked witness "
                f"`holListArrayWitness_{field}`"
            )
    return errors


def hol_declaration_lines(
    path: Path, cache: dict[Path, dict[str, list[int]]]
) -> dict[str, list[int]]:
    if path not in cache:
        names: dict[str, list[int]] = {}
        header = re.compile(
            r"^(?:%s)\s+([A-Za-z0-9_']+)" % "|".join(HOL_HEADER_KEYWORDS)
        )
        sml_val = re.compile(r"^val\s+([A-Za-z0-9_']+)\s*=")
        with path.open(encoding="utf-8", errors="replace") as handle:
            for number, line in enumerate(handle, start=1):
                match = header.match(line) or sml_val.match(line)
                if match:
                    names.setdefault(match.group(1), []).append(number)
        cache[path] = names
    return cache[path]


def hol_ref_error(
    path: Path, name: str, line: int | None,
    cache: dict[Path, dict[str, list[int]]]
) -> str | None:
    declared = hol_declaration_lines(path, cache).get(name, [])
    if not declared:
        return f"declares no `{name}`"
    if line is None and len(declared) > 1:
        return (
            f"declares `{name}` at multiple lines {declared}; "
            "add the source line to @[hol]"
        )
    if line is not None and line not in declared:
        return f"declares `{name}` at {declared}, not at line {line}"
    return None


def main(argv: list[str]) -> int:
    want_mapping = "--mapping" in argv
    want_orphans = "--orphans" in argv
    errors: list[str] = []
    mapping: list[tuple[str, str, str, str]] = []
    cache: dict[Path, dict[str, list[int]]] = {}
    reachable = reachable_modules()

    if not (ROOT / "cakeml" / "pancake").is_dir():
        print(
            "error: the cakeml submodule is not checked out; run "
            "`git submodule update --init --depth 1 -- cakeml`",
            file=sys.stderr,
        )
        return 1

    for lean_path in lean_files():
        rel = lean_path.relative_to(ROOT).as_posix()
        lines = lean_path.read_text(encoding="utf-8").splitlines()
        module = module_name(lean_path)
        module_reported = False
        for number, hol_path, hol_name, hol_line, fields in hol_attribute_sites(lines):
            where = f"{rel}:{number}"
            lean_decl = find_lean_decl(lines, number - 1)
            if module not in reachable and not module_reported:
                module_reported = True
                errors.append(
                    f"{rel}: module {module} carries @[hol] but is not imported "
                    f"(transitively) from Flapjack.lean, so `lake build Flapjack` "
                    f"never checks it; add the import to Flapjack.lean"
                )
            if fields:
                errors.extend(
                    f"{where}: {error}"
                    for error in list_as_array_errors(lines, fields, rel)
                )
            target = ROOT / hol_path
            if not hol_path.startswith("cakeml/") or not hol_path.endswith(".sml"):
                errors.append(f"{where}: path is not a cakeml/...sml file: {hol_path}")
                continue
            if not target.is_file():
                errors.append(f"{where}: HOL file does not exist: {hol_path}")
                continue
            ref_error = hol_ref_error(target, hol_name, hol_line, cache)
            if ref_error is not None:
                errors.append(
                    f"{where}: {hol_path} {ref_error} "
                    f"(cited by {lean_decl})"
                )
                continue
            mapped_name = f"{hol_name}:{hol_line}" if hol_line is not None else hol_name
            mapping.append((where, lean_decl, hol_path, mapped_name))

    if want_mapping:
        for row in mapping:
            print("\t".join(row))

    if want_orphans:
        orphans = sorted(
            module_name(path)
            for path in lean_files()
            if path.is_relative_to(ROOT / "Flapjack")
            and not path.is_relative_to(ROOT / "Flapjack" / "Test")
            and module_name(path) not in reachable
        )
        for module in orphans:
            print(f"warning: {module} is not reachable from Flapjack.lean", file=sys.stderr)

    if errors:
        for error in errors:
            print(f"error: {error}", file=sys.stderr)
        print(f"{len(errors)} bad @[hol] reference(s)", file=sys.stderr)
        return 1
    print(f"{len(mapping)} @[hol] reference(s) checked", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
