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
from collections.abc import Iterable
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIRS = [ROOT / "Flapjack", ROOT / "Flapjack.lean"]

ATTR_RE = re.compile(r'\bhol\s+"([^"]+)"\s+"([^"]+)"(?:\s+(\d+))?')
QUALIFIER_RE = re.compile(r'\(\s*list_as_array\s*:=\s*\[([^]]*)\]\s*\)')
NAMES_AS_STRING_RE = re.compile(r'\(\s*names_as_string\s*:=\s*\[([^]]*)\]\s*\)')
NAMES_AS_STRING_BOUNDARY_RE = re.compile(
    r'\(\s*names_as_string_boundary\s*:=\s*\[([^]]*)\]\s*\)'
)
FMAP_AS_FINITE_SUPPORT_RE = re.compile(
    r'\(\s*fmap_as_finite_support\s*:=\s*\[([^]]*)\]\s*\)'
)
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
    attribute_bracket_depth = 0
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
            attribute_bracket_depth = 0
        chunks.append(stripped)
        attribute_bracket_depth += stripped.count("[") - stripped.count("]")
        if attribute_bracket_depth > 0:
            continue
        attribute = " ".join(chunks)
        if "hol " in attribute:
            for hol_path, hol_name, hol_line in ATTR_RE.findall(attribute):
                def fields_for(pattern: re.Pattern[str]) -> tuple[str, ...]:
                    qualifier = pattern.search(attribute)
                    return tuple(
                        field.strip() for field in qualifier.group(1).split(",")
                    ) if qualifier else ()

                yield (
                    start,
                    hol_path,
                    hol_name,
                    int(hol_line) if hol_line else None,
                    fields_for(QUALIFIER_RE),
                    fields_for(NAMES_AS_STRING_RE),
                    fields_for(NAMES_AS_STRING_BOUNDARY_RE),
                    fields_for(FMAP_AS_FINITE_SUPPORT_RE),
                )
        start = None
        chunks = []
        attribute_bracket_depth = 0


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


def structure_field_types(lines: list[str]) -> dict[str, str]:
    """Text of each structure field declaration's type, per module.

    The type is the remainder of the declaration line; qualified finite-map
    fields name their `HolFiniteMapExact` carrier on that line, which is enough
    for the representation gate to reject raw `α → Option β` maps.
    """
    field_types: dict[str, str] = {}
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
        field = re.match(r"^\s+([A-Za-z_][A-Za-z0-9_']*)\s*:\s*(?P<type>.+)$", line)
        if field:
            field_types.setdefault(field.group(1), field.group("type").strip())
    return field_types


def structure_field_map(lines: list[str]) -> dict[str, set[str]]:
    """Field names of every structure declared in this module."""
    members: dict[str, set[str]] = {}
    structure_indent: int | None = None
    current: str | None = None
    for line in strip_lean_comments("\n".join(lines)).splitlines():
        structure = re.match(
            r"^(\s*)structure\s+([A-Za-z0-9_'.]+).*\bwhere\s*$", line
        )
        if structure:
            structure_indent = len(structure.group(1))
            current = structure.group(2)
            members.setdefault(current, set())
            continue
        if structure_indent is None:
            continue
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        if indent <= structure_indent:
            structure_indent = None
            current = None
            continue
        field = re.match(r"^\s+([A-Za-z_][A-Za-z0-9_']*)\s*:", line)
        if field and current is not None:
            members[current].add(field.group(1))
    return members


def owning_structure_for_fields(
    members: dict[str, set[str]], fields: Iterable[str]
) -> str | None:
    """The single structure declaring every qualified field, if unique.

    The qualifier stays narrow: all named fields must live in one carrier
    structure, so fields split across several structures are rejected.
    """
    wanted = set(fields)
    owners = [name for name, names in members.items() if wanted <= names]
    if len(owners) == 1:
        return owners[0]
    return None


ROUNDTRIP_RE = re.compile(r"\b(?:to|of)[A-Z][A-Za-z0-9_']*")


def has_fmap_witness(
    lines: list[str],
    owning: str | None,
    counterpart_names: Iterable[str],
) -> bool:
    """Require the canonical finite-map translation witness in this module.

    The witness is named `holFmapAsFiniteSupportWitness`; its statement must
    name the unique structure that owns every qualified field together with its
    broad counterpart (another structure declared in the same module) or the
    canonical `toX`/`ofX` roundtrip.  Lake checks the proof; this gate checks
    presence and shape without hard-coding any one carrier module.
    """
    if not owning:
        return False
    counterparts = {name for name in counterpart_names if name and name != owning}
    source = strip_lean_comments("\n".join(lines))
    pattern = re.compile(
        rf"^\s*(?:@\[[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?"
        rf"(?:theorem|lemma)\s+holFmapAsFiniteSupportWitness\b"
        rf"(?P<statement>[\s\S]*?):=",
        re.M,
    )
    for match in pattern.finditer(source):
        statement = match.group("statement")
        if owning not in statement:
            continue
        if any(name in statement for name in counterparts):
            return True
        if ROUNDTRIP_RE.search(statement):
            return True
    return False


def fmap_as_finite_support_errors(
    lines: list[str], fields: tuple[str, ...], module: str
) -> list[str]:
    """Validate the reviewed canonical HOL finite-map translation.

    Each named field must be a same-module structure field whose declared type
    uses `HolFiniteMapExact`; a raw `α → Option β` lookup map is ineligible.
    All named fields must belong to ONE owning carrier structure, and the module
    must provide a canonical witness `holFmapAsFiniteSupportWitness` naming that
    structure together with its broad counterpart or `toX`/`ofX` roundtrip.
    """
    errors: list[str] = []
    if len(set(fields)) != len(fields):
        errors.append("fmap_as_finite_support fields must be distinct")
    declared_fields = structure_fields(lines)
    field_types = structure_field_types(lines)
    for field in fields:
        if field not in declared_fields:
            errors.append(
                f"fmap_as_finite_support field `{field}` is not a field of a Lean "
                f"structure declared in {module}"
            )
            continue
        field_type = field_types.get(field, "")
        if "HolFiniteMapExact" not in field_type:
            errors.append(
                f"fmap_as_finite_support field `{field}` does not use the approved "
                "HolFiniteMapExact carrier; a raw function-backed map is ineligible"
            )
    members = structure_field_map(lines)
    owning = owning_structure_for_fields(members, fields) if fields else None
    if fields and owning is None:
        errors.append(
            "fmap_as_finite_support fields must all be declared by one owning "
            f"carrier structure in {module}"
        )
    elif fields and not has_fmap_witness(lines, owning, members.keys()):
        errors.append(
            "fmap_as_finite_support has no same-module checked canonical witness "
            "`holFmapAsFiniteSupportWitness` naming the owning structure and its "
            "broad counterpart or `toX`/`ofX` roundtrip"
        )
    return errors


def has_list_array_witness(lines: list[str], field: str) -> bool:
    """Require a same-module, kernel-checked representation theorem for a field.

    The witness convention is `holListArrayWitness_<field>` and its theorem
    type must mention both `RepresentsHOLNodeList` and the qualified state field.
    The relation must occur in the result type, exactly once, and not in any
    premise: a theorem assuming the relation it claims to establish is not a
    representation witness. Lake checks the witness proof when it builds the
    tagged module; this syntactic gate does not itself prove semantic
    correspondence.
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
        depth = 0
        result_start: int | None = None
        for index, char in enumerate(statement):
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth -= 1
            elif char == ":" and depth == 0:
                result_start = index + 1
        if result_start is None:
            continue
        premises, result_type = statement[:result_start], statement[result_start:]
        if (
            "RepresentsHOLNodeList" not in premises
            and result_type.count("RepresentsHOLNodeList") == 1
            and re.search(rf"\.\s*{re.escape(field)}\b", result_type)
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


def has_mlstring_witness(lines: list[str], declaration: str) -> bool:
    """Require a same-module byte-range theorem for a byte-observable tag.

    The theorem is named for the tagged declaration and its result must
    establish `NameRanged`. Input range premises are allowed. This syntax check
    does not establish that the result is the right output or that a premise is
    discharged on the executed path; Lean checks the proof and source review
    records those obligations.
    """
    source = strip_lean_comments("\n".join(lines))
    pattern = re.compile(
        rf"^\s*(?:@\[[\s\S]*?\]\s*)?(?:private\s+|protected\s+)?"
        rf"(?:theorem|lemma)\s+holMlStringWitness_{re.escape(declaration)}\b"
        rf"(?P<type>[\s\S]*?):=",
        re.M,
    )
    for match in pattern.finditer(source):
        statement = match.group("type")
        depth = 0
        result_start: int | None = None
        for index, char in enumerate(statement):
            if char in "([{":
                depth += 1
            elif char in ")]}":
                depth -= 1
            elif char == ":" and depth == 0:
                result_start = index + 1
        if result_start is None:
            continue
        result_type = statement[result_start:]
        result = result_type.strip()
        if re.match(r"^(?:[A-Za-z0-9_]+\.)*NameRanged\b", result):
            return True
    return False


def names_as_string_errors(
    lines: list[str],
    identifiers: tuple[str, ...],
    boundary_identifiers: tuple[str, ...],
    module: str,
    declaration: str,
) -> list[str]:
    """Validate reviewed HOL `mlstring` identifiers and byte boundaries."""
    errors: list[str] = []
    if len(set(identifiers)) != len(identifiers):
        errors.append("names_as_string identifiers must be distinct")
    if len(set(boundary_identifiers)) != len(boundary_identifiers):
        errors.append("names_as_string_boundary identifiers must be distinct")
    for identifier in boundary_identifiers:
        if identifier not in identifiers:
            errors.append(
                f"names_as_string_boundary identifier `{identifier}` is not listed by "
                "names_as_string"
            )
        if not has_mlstring_witness(lines, declaration):
            errors.append(
                f"names_as_string_boundary identifier `{identifier}` in {module}:{declaration} "
                f"has no same-module checked witness `holMlStringWitness_{declaration}` "
                "with a NameRanged result"
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
        # HOL ``Datatype:`` blocks put the declared type name on the next
        # line(s) (``name = ...``) and terminate with a top-level ``End``.
        datatype_header = re.compile(r"^Datatype\s*:?\s*$")
        datatype_name = re.compile(r"^\s*([A-Za-z0-9_']+)\s*=")
        datatype_end = re.compile(r"^End\b")
        in_datatype = False
        with path.open(encoding="utf-8", errors="replace") as handle:
            for number, line in enumerate(handle, start=1):
                if in_datatype:
                    if datatype_end.match(line):
                        in_datatype = False
                    else:
                        match = datatype_name.match(line)
                        if match:
                            names.setdefault(match.group(1), []).append(number)
                    continue
                if datatype_header.match(line):
                    in_datatype = True
                    continue
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
        for (number, hol_path, hol_name, hol_line, list_fields,
             names_fields, boundary_fields, fmap_fields) in hol_attribute_sites(lines):
            where = f"{rel}:{number}"
            lean_decl = find_lean_decl(lines, number - 1)
            if module not in reachable and not module_reported:
                module_reported = True
                errors.append(
                    f"{rel}: module {module} carries @[hol] but is not imported "
                    f"(transitively) from Flapjack.lean, so `lake build Flapjack` "
                    f"never checks it; add the import to Flapjack.lean"
                )
            if list_fields:
                errors.extend(
                    f"{where}: {error}"
                    for error in list_as_array_errors(lines, list_fields, rel)
                )
            if fmap_fields:
                errors.extend(
                    f"{where}: {error}"
                    for error in fmap_as_finite_support_errors(lines, fmap_fields, rel)
                )
            if names_fields or boundary_fields:
                errors.extend(
                    f"{where}: {error}"
                    for error in names_as_string_errors(
                        lines, names_fields, boundary_fields, rel, lean_decl
                    )
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
