#!/usr/bin/env python3
"""Inventory the HOL dependency closure of the Pancake-to-RISC-V semantics theorem.

The goal is a *reproducible* count of what the Pancake-to-RISC-V correctness
statement actually depends on, including the external CakeML backend, so that
porting work can be planned against evidence instead of against every theorem in
every transitively imported script.

Method (first slice; deliberately coarse, see limitations below):

1. Reuse the generated HOL index (``scripts/index-hol.py`` -> ``.hol-index/``)
   for declaration names and source spans, and for the ``Ancestors`` theory
   graph.
2. Theory closure: transitive ``Ancestors`` closure from the root theory.  This
   is the *source pool*: every script the HOL development needs to build the
   root theorem.
3. Required closure: a lexical citation fixed point over that pool, starting at
   the root theorem.  A declaration is "required" when its name occurs in the
   source span of a required declaration.  This is an *upper bound* on the
   genuinely needed HOL results.
4. Lean coverage: which required declarations already carry a ``@[hol ...]``
   tag (matched by ``(theory, name)`` and by name alone).

Limitations (explicit, do not overclaim):

* Citation is lexical, not semantic: a name mentioned in a comment or shadowed
  by a local identifier counts as a citation, and theory qualifiers are dropped,
  so same-named declarations in different theories collapse into one node.
* The required set is therefore an upper bound and the missing-port count a
  lower bound.
* Definitions and datatypes are included; a Lean port may legitimately exist
  without a ``@[hol]`` tag, so "untagged" is not the same as "unported".
* ``.hol-index/`` is a generated, git-ignored artifact.  Regenerate it with
  ``python3 scripts/index-hol.py`` before trusting the numbers.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
CAKEML = ROOT / "cakeml"
INDEX_DIR = ROOT / ".hol-index"
INDEX = INDEX_DIR / "hol-index.tsv"
DEPS = INDEX_DIR / "theory-deps.txt"

DEFAULT_ROOT_THEOREM = "pan_to_target_compile_semantics"
DEFAULT_ROOT_THEORY = "pan_to_targetProof"

TAG_RE = re.compile(r'@\[hol\s+"([^"]+)"\s+"([^"]+)"')
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'$]*")

AREA_ORDER = [
    "pancake",
    "cakeml_backend",
    "cakeml_semantics",
    "cakeml_other",
    "basis",
    "other",
]


@dataclass(frozen=True)
class Declaration:
    kind: str
    name: str
    path: str
    start: int
    end: int
    theory: str


def theory_of_script(path: str) -> str:
    name = Path(path).name
    if name.endswith("Script.sml"):
        return name[: -len("Script.sml")]
    return name[: -len(".sml")] if name.endswith(".sml") else Path(name).stem


def area_of_path(path: str) -> str:
    parts = Path(path).parts
    if not parts:
        return "other"
    if parts[0] == "pancake":
        return "pancake"
    if len(parts) >= 2 and parts[0] == "compiler" and parts[1] == "backend":
        return "cakeml_backend"
    if parts[0] == "semantics":
        return "cakeml_semantics"
    if parts[0] == "basis":
        return "basis"
    if parts[0] == "compiler":
        return "cakeml_other"
    return "other"


def load_index(path: Path) -> list[Declaration]:
    declarations: list[Declaration] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) < 4:
            continue
        kind, name, location, theory = fields[:4]
        source, span = location.rsplit(":", 1)
        start, end = span.split("-", 1)
        declarations.append(
            Declaration(kind, name, source, int(start), int(end), theory)
        )
    return declarations


def load_theory_graph(path: Path) -> dict[str, set[str]]:
    graph: dict[str, set[str]] = defaultdict(set)
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line or line.startswith("#") or "->" not in line:
            continue
        theory, ancestor = line.split(" -> ", 1)
        graph[theory.strip()].add(ancestor.strip())
    return graph


def theory_closure(graph: dict[str, set[str]], roots: list[str]) -> set[str]:
    seen: set[str] = set()
    queue = deque(roots)
    while queue:
        theory = queue.popleft()
        if theory in seen:
            continue
        seen.add(theory)
        queue.extend(graph.get(theory, ()))
    return seen


class SourceCache:
    def __init__(self, base: Path) -> None:
        self.base = base
        self._files: dict[str, list[str]] = {}

    def span(self, path: str, start: int, end: int) -> str:
        lines = self._files.get(path)
        if lines is None:
            target = self.base / path
            try:
                lines = target.read_text(encoding="utf-8", errors="replace").splitlines()
            except OSError:
                lines = []
            self._files[path] = lines
        return "\n".join(lines[max(start - 1, 0) : end])


def citation_edges(
    declarations: list[Declaration],
    cache: SourceCache,
) -> tuple[dict[str, set[str]], set[str]]:
    names = {declaration.name for declaration in declarations}
    edges: dict[str, set[str]] = defaultdict(set)
    for declaration in declarations:
        tokens = set(IDENT.findall(cache.span(declaration.path, declaration.start, declaration.end)))
        edges[declaration.name].update((tokens & names) - {declaration.name})
    return edges, names


def required_closure(edges: dict[str, set[str]], root: str) -> set[str]:
    required: set[str] = set()
    queue = deque([root])
    while queue:
        name = queue.popleft()
        if name in required:
            continue
        required.add(name)
        queue.extend(edges.get(name, ()))
    return required


def load_lean_tags(base: Path) -> set[tuple[str, str]]:
    tags: set[tuple[str, str]] = set()
    for lean in base.rglob("*.lean"):
        for match in TAG_RE.finditer(lean.read_text(encoding="utf-8", errors="replace")):
            tags.add((theory_of_script(match.group(1)), match.group(2)))
    return tags


def format_counts(counts: dict[str, int], order: list[str]) -> str:
    keys = [key for key in order if counts.get(key)]
    keys += sorted(key for key in counts if key not in order and counts[key])
    return ", ".join(f"{key}: {counts[key]}" for key in keys) if keys else "none"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root-theorem", default=DEFAULT_ROOT_THEOREM)
    parser.add_argument("--root-theory", default=DEFAULT_ROOT_THEORY)
    parser.add_argument(
        "--out",
        type=Path,
        default=ROOT / "docs" / "HOL-DEPENDENCY-INVENTORY.md",
    )
    parser.add_argument(
        "--json", type=Path, default=None,
        help="optionally also write the full required list as JSON",
    )
    parser.add_argument(
        "--list", action="store_true",
        help="print the full required declaration list to stdout",
    )
    parser.add_argument(
        "--check", action="store_true",
        help="fail if --out does not match the freshly generated report",
    )
    args = parser.parse_args()

    if not INDEX.exists() or not DEPS.exists():
        parser.error(
            f"{INDEX_DIR} is missing; run: python3 scripts/index-hol.py"
        )

    declarations = load_index(INDEX)
    graph = load_theory_graph(DEPS)
    closure = theory_closure(graph, [args.root_theory])
    in_closure = [d for d in declarations if d.theory in closure]

    cache = SourceCache(CAKEML)
    edges, _names = citation_edges(in_closure, cache)
    required = required_closure(edges, args.root_theorem)

    root_decls = [d for d in in_closure if d.name == args.root_theorem]
    root_theory = root_decls[0].theory if root_decls else args.root_theory

    pool_kinds: dict[str, int] = defaultdict(int)
    for d in in_closure:
        pool_kinds[d.kind] += 1
    required_kinds: dict[str, int] = defaultdict(int)
    required_by_theory: dict[str, int] = defaultdict(int)
    name_theory: dict[str, str] = {}
    for d in in_closure:
        if d.name in required:
            required_kinds[d.kind] += 1
            required_by_theory[d.theory] += 1
            name_theory.setdefault(d.name, d.theory)

    pool_areas: dict[str, int] = defaultdict(int)
    for d in in_closure:
        pool_areas[area_of_path(d.path)] += 1
    required_areas: dict[str, int] = defaultdict(int)
    for d in in_closure:
        if d.name in required:
            required_areas[area_of_path(d.path)] += 1

    tags = load_lean_tags(ROOT / "Flapjack")
    tagged_names = {name for _theory, name in tags}
    tagged_here = sorted(
        name for name in required if (name_theory.get(name), name) in tags
    )
    untagged_here = sorted(
        name for name in required if (name_theory.get(name), name) not in tags
    )
    untagged_anywhere = [name for name in untagged_here if name not in tagged_names]

    if root_decls:
        root_decl = root_decls[0]
        root_tokens = set(IDENT.findall(cache.span(root_decl.path, root_decl.start, root_decl.end)))
        direct = sorted(root_tokens & set(name_theory))
    else:
        direct = []

    lines: list[str] = []
    source_sha = ""
    sha_file = INDEX_DIR / "source.sha"
    if sha_file.exists():
        source_sha = sha_file.read_text(encoding="utf-8").strip()

    lines.append("# HOL dependency inventory: Pancake-to-RISC-V correctness")
    lines.append("")
    lines.append(
        "Generated by `python3 scripts/hol-dependency-inventory.py` (first "
        "slice: direct citations and source-pool counts). Regenerate the "
        "underlying index first with `python3 scripts/index-hol.py`."
    )
    lines.append("")
    if source_sha:
        lines.append(f"- CakeML revision indexed: `{source_sha}`")
    lines.append(f"- Root theorem: `{args.root_theorem}` (theory `{root_theory}`)")
    lines.append(f"- Root theory for the ancestor closure: `{args.root_theory}`")
    lines.append("")
    lines.append("## Counts")
    lines.append("")
    lines.append(f"- Scripts/theories in the transitive ancestor closure: `{len(closure)}`")
    lines.append(f"- Declarations in those theories (source pool): `{len(in_closure)}`")
    lines.append(f"  - by kind: {format_counts(pool_kinds, [])}")
    lines.append(
        f"  - by area: {format_counts(pool_areas, AREA_ORDER)}"
    )
    lines.append(
        f"- Required declarations (lexical citation closure of the root, "
        f"upper bound): `{len(required)}`"
    )
    lines.append(f"  - by kind: {format_counts(required_kinds, [])}")
    lines.append(
        f"  - by area: {format_counts(required_areas, AREA_ORDER)}"
    )
    lines.append("")
    lines.append("## Lean coverage of the required set")
    lines.append("")
    lines.append(f"- `@[hol]` tags found under `Flapjack/`: `{len(tags)}`")
    lines.append(
        f"- Required declarations tagged by `(theory, name)`: "
        f"`{len(tagged_here)}`"
    )
    lines.append(
        f"- Required declarations with no matching `(theory, name)` tag: "
        f"`{len(untagged_here)}`"
    )
    lines.append(
        f"- ... of which also have no same-name tag anywhere: "
        f"`{len(untagged_anywhere)}` (lower bound on genuinely missing ports)"
    )
    lines.append("")
    lines.append("## Direct citations of the root theorem")
    lines.append("")
    lines.append(
        f"`{len(direct)}` distinct indexed declaration names occur in the root "
        "theorem span."
    )
    lines.append("")
    for name in direct[:80]:
        lines.append(f"- `{name}` ({name_theory.get(name, 'unknown')})")
    if len(direct) > 80:
        lines.append(f"- ... and {len(direct) - 80} more (see `--list`)")
    lines.append("")
    lines.append("## Required declarations per theory (top 30)")
    lines.append("")
    for theory, count in sorted(required_by_theory.items(), key=lambda kv: (-kv[1], kv[0]))[:30]:
        lines.append(f"- `{theory}`: {count}")
    lines.append("")
    lines.append("## Transitive ancestor closure (all theories)")
    lines.append("")
    root_direct_ancestors = sorted(graph.get(args.root_theory, ()))
    lines.append(
        f"Direct `Ancestors` of `{args.root_theory}`: "
        + ", ".join(f"`{a}`" for a in root_direct_ancestors)
    )
    lines.append("")
    lines.append(f"All {len(closure)} theories in the closure:")
    lines.append("")
    theory_area: dict[str, str] = {}
    for declaration in in_closure:
        theory_area.setdefault(declaration.theory, area_of_path(declaration.path))
    for theory in sorted(closure):
        area = theory_area.get(theory, "unknown")
        lines.append(f"- `{theory}` ({area})")
    lines.append("")
    lines.append("## Reproduction")
    lines.append("")
    lines.append("```sh")
    lines.append("python3 scripts/index-hol.py          # writes .hol-index/ (git-ignored)")
    lines.append("python3 scripts/hol-dependency-inventory.py")
    lines.append("python3 scripts/hol-dependency-inventory.py --list   # full required list")
    lines.append("```")
    lines.append("")
    lines.append("## Known limitations")
    lines.append("")
    lines.append(
        "- Citation is lexical over identifier tokens in declaration spans, not "
        "semantic; theory qualifiers are dropped, so same-named declarations "
        "collapse into one node."
    )
    lines.append(
        "- The required count is therefore an upper bound; the missing-port "
        "count is a lower bound."
    )
    lines.append(
        "- Definitions and datatypes are included, and an untagged declaration "
        "may still have a correct untagged Lean analogue."
    )
    lines.append(
        "- This first slice does not yet resolve `Theory$name` / `nameTheory.name` "
        "qualified citations, nor distinguish HOL helper lemmas that Lean proof "
        "restructuring makes unnecessary."
    )
    lines.append("- `.hol-index/` is generated and git-ignored; numbers move with the CakeML revision.")
    lines.append("")

    report = "\n".join(lines)
    if args.check:
        if not args.out.exists():
            print(f"missing {args.out}", file=sys.stderr)
            return 1
        if args.out.read_text(encoding="utf-8") != report:
            print(
                f"{args.out} is stale; rerun python3 scripts/hol-dependency-inventory.py",
                file=sys.stderr,
            )
            return 1
        print(f"{args.out} is up to date")
        return 0

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(report, encoding="utf-8")

    if args.json is not None:
        payload = {
            "root_theorem": args.root_theorem,
            "root_theory": args.root_theory,
            "cake_revision": source_sha,
            "counts": {
                "closure_theories": len(closure),
                "pool_declarations": len(in_closure),
                "required_declarations": len(required),
                "tagged_required": len(tagged_here),
                "untagged_required": len(untagged_here),
                "missing_ports_lower_bound": len(untagged_anywhere),
            },
            "required": [
                {"theory": name_theory[name], "name": name}
                for name in sorted(required)
            ],
        }
        args.json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")

    if args.list:
        for name in sorted(required):
            print(f"{name_theory.get(name, 'unknown')}\t{name}")

    print(
        f"closure theories={len(closure)} pool={len(in_closure)} "
        f"required={len(required)} tagged={len(tagged_here)} "
        f"untagged={len(untagged_here)} missing_lower_bound={len(untagged_anywhere)}"
    )
    print(f"wrote {args.out.relative_to(ROOT) if args.out.is_absolute() else args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
