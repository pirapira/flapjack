# Original Pancake HOL probes

The repository-wide parity workflow is documented in
[`docs/PARITY-TESTING.md`](../../docs/PARITY-TESTING.md).

The files in this directory execute definitions from the CakeML Pancake HOL
development. They are test-data generators, not independent Lean reference
implementations. A parity fixture may be used to close a porting bead only
when it records the original source definition, the probe source, and the
command used to regenerate its output.

The probes currently cover the small `loop_to_word` slice used by
`Flapjack.Test.LoopToWord` and the `panSem$mem_load` boundary used by
`Flapjack.Test.PanMemoryParity`. Their source references are respectively
`cakeml/pancake/loop_to_wordScript.sml` and
`cakeml/pancake/semantics/panSemScript.sml`.

From the repository root, with HOL4 and the CakeML checkout available,
regenerate both checked-in outputs with:

```sh
scripts/hol-probes/regenerate.sh
```

Normal Lean CI consumes the checked-in output and does not require HOL4. A
reviewer with HOL4 can rerun the command and inspect the diff. Each probe's
declaration and source path make its reference boundary explicit.
