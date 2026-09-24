#!/usr/bin/env python3
"""Build a small, deterministic index for CakeML/HOL source files.

The index is deliberately a generated developer aid rather than part of the
Lean build.  It understands the HOL script declarations that are useful while
porting Pancake and has a best-effort fallback for older ``val ...`` scripts.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path


IDENT = r"[A-Za-z_][A-Za-z0-9_'$]*"
TOP_LEVEL = re.compile(
    r"^\s*(?:Theory\b|Ancestors\b|Libs\b|Type\b|Datatype:\b|"
    r"Definition\b|Theorem\b|Triviality\b|Termination\b|"
    r"val\s+_\s*=\s*new_theory\b|val\s+" + IDENT + r"\s*=)"
)
DECL_RE = re.compile(
    r"^\s*(Theorem|Triviality|Definition)\s+(\S+?)\s*(?::|=)"
)
OLD_DECL_RE = re.compile(
    r"^\s*val\s+(" + IDENT + r")\s*=\s*(Q\.prove|prove|store_thm|Define)\b"
)
THEORY_RE = re.compile(r"^\s*Theory\s+(\S+)")
OLD_THEORY_RE = re.compile(r'^\s*val\s+_\s*=\s*new_theory\s+"([^"]+)"')
ANCESTORS_RE = re.compile(r"^\s*Ancestors\b(.*)$")
# A line beginning a new header section or the theory body; it terminates an
# ``Ancestors`` list.  Used instead of "collect until the next known keyword"
# so that unrelated body lines cannot leak into the dependency graph.
SECTION_RE = re.compile(
    r"^\s*(?:Libs\b|Type\b|Datatype:|Definition\b|Theorem\b|Triviality\b|"
    r"val\b|Overload\b|open\b|local\b|structure\b|signature\b|functor\b|"
    r"fun\b|end\b|Infrastructure\b|Tests?\b|Proof\b)"
)
IDENT_ONLY = re.compile(r"^" + IDENT + r"$")


@dataclass(frozen=True)
class Entry:
    kind: str
    name: str
    path: str
    start: int
    end: int
    theory: str

    def key(self) -> tuple[str, str, str, int, int, str]:
        return (self.kind, self.name, self.path, self.start, self.end, self.theory)


def clean_name(name: str) -> str:
    """Remove HOL declaration attributes, including attributes with spaces."""
    name = name.strip()
    return re.sub(r"\s*\[[^\]]*\]\s*$", "", name)


def mask_comments(lines: list[str]) -> list[str]:
    """Mask nested SML comments while preserving line lengths and newlines."""
    masked: list[str] = []
    depth = 0
    in_string = False
    for line in lines:
        out: list[str] = []
        i = 0
        while i < len(line):
            two = line[i : i + 2]
            if depth:
                if two == "(*":
                    depth += 1
                    out.extend("  ")
                    i += 2
                elif two == "*)":
                    depth -= 1
                    out.extend("  ")
                    i += 2
                else:
                    out.append("\n" if line[i] == "\n" else " ")
                    i += 1
                continue
            if line[i] == '"' and not in_string:
                in_string = True
                out.append(line[i])
                i += 1
                continue
            if line[i] == '"' and in_string:
                # HOL strings use doubled quotes only rarely; keeping the
                # simple state machine is sufficient for declaration headers.
                in_string = False
                out.append(line[i])
                i += 1
                continue
            if two == "(*" and not in_string:
                depth = 1
                out.extend("  ")
                i += 2
                continue
            out.append(line[i])
            i += 1
        masked.append("".join(out))
    return masked


def declaration_end(masked: list[str], start: int, kind: str) -> int:
    """Find the end line for a modern HOL declaration (1-based inclusive)."""
    if kind in {"Theorem", "Triviality"}:
        for i in range(start, len(masked)):
            if re.match(r"^\s*QED\b", masked[i]):
                return i + 1
            # Equality-style theorem declarations have no QED.  Stop before
            # the next declaration if one is encountered.
            if i > start and TOP_LEVEL.match(masked[i]):
                return i
        return len(masked)
    if kind == "Definition":
        for i in range(start, len(masked)):
            if re.match(r"^\s*End\b", masked[i]):
                return i + 1
            if i > start and TOP_LEVEL.match(masked[i]):
                return i
        return len(masked)
    if kind == "Datatype":
        for i in range(start, len(masked)):
            if re.match(r"^\s*End\b", masked[i]):
                return i + 1
        return len(masked)
    raise ValueError(f"unknown declaration kind: {kind}")


def old_declaration_end(masked: list[str], start: int) -> int:
    """Best-effort end finder for ``val x = Define/Q.prove/store_thm``."""
    # Most old declarations are terminated by ``);`` or a semicolon.  Track
    # delimiters so a semicolon inside a quoted HOL term does not end it.
    parens = brackets = braces = 0
    in_string = False
    for i in range(start, len(masked)):
        line = masked[i]
        escaped = False
        for ch in line:
            if ch == '"' and not escaped:
                in_string = not in_string
            if not in_string:
                if ch == "(":
                    parens += 1
                elif ch == ")":
                    parens = max(0, parens - 1)
                elif ch == "[":
                    brackets += 1
                elif ch == "]":
                    brackets = max(0, brackets - 1)
                elif ch == "{":
                    braces += 1
                elif ch == "}":
                    braces = max(0, braces - 1)
            escaped = ch == "\\" and not escaped
            if ch != "\\":
                escaped = False
        if i > start and parens == brackets == braces == 0:
            if ";" in line or re.match(r"^\s*End\b", line):
                return i + 1
            if TOP_LEVEL.match(line):
                return i
    return min(len(masked), start + 1)


def parse_file(root: Path, path: Path) -> tuple[list[Entry], list[tuple[str, str]], bool]:
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines(keepends=True)
    masked = mask_comments(lines)
    relative = path.relative_to(root).as_posix()
    entries: list[Entry] = []

    theory = ""
    theory_match = next((m for line in masked if (m := THEORY_RE.match(line))), None)
    if theory_match:
        theory = clean_name(theory_match.group(1))
    else:
        old_theory_match = next(
            (m for line in masked if (m := OLD_THEORY_RE.match(line))), None
        )
        if old_theory_match:
            theory = old_theory_match.group(1)

    dependencies: list[tuple[str, str]] = []
    for i, line in enumerate(masked):
        match = ANCESTORS_RE.match(line)
        if not match:
            continue
        rest = [
            ancestor
            for tok in match.group(1).split()
            if (ancestor := clean_name(tok)) and IDENT_ONLY.match(ancestor)
        ]
        j = i + 1
        while j < len(masked):
            line_j = masked[j]
            if not line_j.strip():
                # Blank lines are tolerated only when an indented,
                # non-section continuation line follows.
                k = j + 1
                while k < len(masked) and not masked[k].strip():
                    k += 1
                if (
                    k < len(masked)
                    and masked[k][0].isspace()
                    and not SECTION_RE.match(masked[k])
                ):
                    j = k
                    continue
                break
            if not line_j[0].isspace():
                break
            if SECTION_RE.match(line_j):
                break
            rest.extend(
                ancestor
                for tok in line_j.split()
                if (ancestor := clean_name(tok)) and IDENT_ONLY.match(ancestor)
            )
            j += 1
        for ancestor in dict.fromkeys(rest):
            if ancestor and ancestor != theory:
                dependencies.append((theory, ancestor))
        break

    recognized_style = bool(theory or any(TOP_LEVEL.match(line) for line in masked))

    i = 0
    while i < len(masked):
        line = masked[i]
        match = DECL_RE.match(line)
        if match:
            kind, raw_name = match.groups()
            name = clean_name(raw_name)
            end = declaration_end(masked, i, kind)
            entries.append(Entry(kind, name, relative, i + 1, end, theory))
            i = max(i + 1, end)
            continue

        if re.match(r"^\s*Datatype\s*:", line):
            end = declaration_end(masked, i, "Datatype")
            for j in range(i + 1, end - 1):
                type_match = re.match(r"^\s*(" + IDENT + r")\s*=", masked[j])
                if type_match:
                    entries.append(
                        Entry("Datatype", type_match.group(1), relative, i + 1, end, theory)
                    )
            i = max(i + 1, end)
            continue

        old = OLD_DECL_RE.match(line)
        if old:
            name, constructor = old.groups()
            kind = "Definition" if constructor == "Define" else "Theorem"
            end = old_declaration_end(masked, i)
            entries.append(Entry(kind, name, relative, i + 1, end, theory))
            recognized_style = True
            i = max(i + 1, end)
            continue
        i += 1

    return entries, dependencies, recognized_style


def cakeml_revision(root: Path) -> str:
    try:
        return subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "HEAD"], text=True
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cakeml", type=Path, default=Path("cakeml"))
    parser.add_argument("--out", type=Path, default=Path(".hol-index"))
    args = parser.parse_args()
    root = args.cakeml.resolve()
    out = args.out
    files = sorted(root.rglob("*.sml"))
    entries: list[Entry] = []
    dependencies: set[tuple[str, str]] = set()
    unparsed: list[str] = []
    for path in files:
        file_entries, file_dependencies, recognized = parse_file(root, path)
        entries.extend(file_entries)
        dependencies.update(file_dependencies)
        if not recognized:
            unparsed.append(path.relative_to(root).as_posix())

    out.mkdir(parents=True, exist_ok=True)
    revision = cakeml_revision(root)
    header = f"# cakeml_commit\t{revision}\n"
    index_lines = [header]
    index_lines.extend(
        "\t".join(
            [entry.kind, entry.name, f"{entry.path}:{entry.start}-{entry.end}", entry.theory]
        )
        + "\n"
        for entry in sorted(set(entries), key=Entry.key)
    )
    (out / "hol-index.tsv").write_text("".join(index_lines), encoding="utf-8")

    graph_lines = [header]
    graph_lines.extend(f"{theory} -> {ancestor}\n" for theory, ancestor in sorted(dependencies))
    (out / "theory-deps.txt").write_text("".join(graph_lines), encoding="utf-8")

    (out / ".unparsed").write_text(
        "\n".join(unparsed) + ("\n" if unparsed else ""), encoding="utf-8"
    )
    (out / "source.sha").write_text(revision + "\n", encoding="utf-8")
    print(
        f"indexed {len(files)} SML files, {len(set(entries))} declarations, "
        f"{len(dependencies)} dependency edges; {len(unparsed)} unparsed files"
    )
    print(f"outputs: {out / 'hol-index.tsv'} and {out / 'theory-deps.txt'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
