# Original Pancake HOL probes

The repository-wide parity workflow is documented in
[`docs/PARITY-TESTING.md`](../../docs/PARITY-TESTING.md).

The files in this directory execute definitions from the CakeML Pancake HOL
development. They are test-data generators, not independent Lean reference
implementations. A parity fixture may be used to close a porting bead only
when it records the original source definition, the probe source, and the
command used to regenerate its output.

The probe currently covers the small `loop_to_word` slice used by
`Flapjack.Test.LoopToWord`. From the repository root, with HOL4 and the CakeML
checkout available, regenerate it with:

```sh
scripts/hol-probes/regenerate.sh
```

Normal Lean CI consumes the checked-in output and does not require HOL4. A
reviewer with HOL4 can rerun the command and inspect the diff. The probe's
`Ancestors loop_to_word` declaration and the source path below make the
reference boundary explicit:

`cakeml/pancake/loop_to_wordScript.sml`
