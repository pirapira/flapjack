# Pan-to-Crep parity fixture coverage

This matrix is generated from the direct CakeML/HOL EVAL probes and the
Lean checks that consume the corresponding intermediate results. The
captured `.out` files are committed, so CI checks do not rebuild HOL.
Run `python3 scripts/pan-to-crep-coverage-report.py --check` to validate
the inventory and this report.

| Pancake boundary | Direct HOL EVAL artifact | Lean check | Covered cases |
| --- | --- | --- | --- |
| `compile_exp` | [`compile_exp_probe.out`](../scripts/hol-probes/compile_exp_probe.out) | [`CompileExpParity.lean`](../Flapjack/Test/CompileExpParity.lean) | original expression cases plus duplicate-key FUPDATE lookup through the finite-map context |
| `compile_prog` | [`compile_prog_probe.out`](../scripts/hol-probes/compile_prog_probe.out) | [`CompileProgParity.lean`](../Flapjack/Test/CompileProgParity.lean) | empty input; direct compile_prog triples for inline calls including first duplicate binding and nested expansion; valid Global return destination; handled call with missing destination and a two-word payload |
| `compile_to_crep` | [`compile_to_crep_probe.out`](../scripts/hol-probes/compile_to_crep_probe.out) | [`CompileToCrepeParity.lean`](../Flapjack/Test/CompileToCrepeParity.lean) | empty input; one-word and two-word exception raises, including a two-word payload lowered after earlier declarations so its later Temp slots stay word-strided; handled two-word exception; flattened parameters |
| `exp_hdl` | [`exp_hdl_probe.out`](../scripts/hol-probes/exp_hdl_probe.out) | [`ExpHdlParity.lean`](../Flapjack/Test/ExpHdlParity.lean) | missing and known handler variables; duplicate finite-map updates in both FUPDATE and FUPDATE_LIST form, where the last binding wins; the executed adapter on a duplicate-bearing association-list context |
| `ret_hdl` | [`ret_hdl_probe.out`](../scripts/hol-probes/ret_hdl_probe.out) | [`RetHdlParity.lean`](../Flapjack/Test/RetHdlParity.lean) | One, empty/single/two-word Comb, and Named shapes |
| `ret_var` | [`ret_var_probe.out`](../scripts/hol-probes/ret_var_probe.out) | [`RetVarParity.lean`](../Flapjack/Test/RetVarParity.lean) | empty and populated One, single and multiword Comb, and Named shapes |
| `wrap_rt` | [`wrap_rt_probe.out`](../scripts/hol-probes/wrap_rt_probe.out) | [`WrapRtParity.lean`](../Flapjack/Test/WrapRtParity.lean) | absent, empty/single One, empty Comb, and Named destinations |
| `compile` | [`compile_def_probe.out`](../scripts/hol-probes/compile_def_probe.out) | [`CompileDefParity.lean`](../Flapjack/Test/CompileDefParity.lean) | finite-map duplicate updates; empty-shape Return; fixed-stride structured Load/Store; 64-bit RISC-V specialization against HOL word64 stride; missing/empty/malformed Global and Local destination lists; valid Local pair destination |

## Scope

The matrix covers intermediate Pan-to-Crep behavior; it does not claim
complete Pancake language coverage. End-to-end RISC-V exact-output
coverage remains checked separately by `scripts/parity-small-corpus.py`
and the pinned goldens in CI. The multiword raise and handled-call rows
exercise word-indexed global slots with `bytesInWord = 8` in Lean.
