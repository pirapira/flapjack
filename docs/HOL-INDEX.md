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

To identify small candidates on the path to a particular HOL theorem, use:

```sh
python3 scripts/next-hol-port.py \
  --file cakeml/pancake/proofs/pan_globalsProofScript.sml \
  --goal compile_top_shape_wf
```

This regenerates a missing or stale index, combines it with the current
`@[hol]` mapping, and lists untagged definitions earlier in that script.
`--kind Theorem` selects supporting theorems instead; repeat `--kind` to show
multiple kinds. Source order is only a starting point for bottom-up porting,
not a complete dependency graph. Check the actual HOL dependencies, existing
Lean declarations, and GitHub issue claims before starting a port. An absent
tag does not prove a missing implementation; a present tag does not prove
equivalence.
