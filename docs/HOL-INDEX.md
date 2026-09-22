# CakeML/HOL source index

The port frequently needs to answer questions such as “where is the original
definition of this Pancake function?” or “which HOL theories does this proof
depend on?”.  `scripts/index-hol.py` builds a lightweight index for that
purpose.  It uses only the Python standard library and scans the checked-out
`cakeml` submodule; it does not participate in the Lean build.

From the repository root, regenerate it with:

```sh
python3 scripts/index-hol.py
```

The generated, gitignored `.hol-index/` directory contains:

- `hol-index.tsv`: sorted `kind`, `name`, `path:line-start-line-end`, and
  owning HOL theory records for theorem, triviality, definition, and datatype
  declarations;
- `theory-deps.txt`: one sorted `Theory -> ancestor` edge per line;
- `.unparsed`: SML files without a recognizable HOL theory/declaration header;
  this is a review list, not an assertion that those files are invalid; and
- `source.sha`: the CakeML submodule commit used to generate the index.

Queries are deliberately plain text, for example:

```sh
rg -w 'pc_compile_correct' .hol-index/hol-index.tsv
rg '^pan_to_crep -> ' .hol-index/theory-deps.txt
```

The index is a local build artifact and is absent from a fresh checkout.  If
the recorded commit does not match `git -C cakeml rev-parse HEAD`, regenerate
before relying on line ranges or dependency results.

To find candidates in any Pancake HOL script, run
`python3 scripts/next-hol-port.py --file cakeml/pancake/FILE.sml`, replacing
`FILE.sml` with its path below `cakeml/pancake/`. Add `--goal HOL_NAME` to
show only earlier declarations or `--kind Theorem` for theorem candidates.
The command refreshes a stale index and excludes declarations with `@[hol]`
tags. Source order and tag presence are navigation aids, not a dependency
proof or an equivalence claim; inspect HOL, Lean, and GitHub issues before
starting work.
