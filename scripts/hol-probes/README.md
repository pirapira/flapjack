# Original Pancake HOL probes

The repository-wide parity workflow is documented in
[`docs/PARITY-TESTING.md`](../../docs/PARITY-TESTING.md).

The files in this directory execute definitions from the CakeML Pancake HOL
development. They are test-data generators, not independent Lean reference
implementations. A parity fixture may be used to close a porting bead only
when it records the original source definition, the probe source, and the
command used to regenerate its output.

The probes currently cover the small `loop_to_word` slice used by
`Flapjack.Test.LoopToWord`, the `panSem$mem_load` boundary used by
`Flapjack.Test.PanMemoryParity`, the fixed-width load boundary used by
`Flapjack.Test.PanFixedLoadParity`, and the `panSem$shape_of` boundary used by
`Flapjack.Test.PanShapeParity`, plus the `panSem` word/value helpers used by
`Flapjack.Test.PanWordParity`. The fixed-width store boundary is covered by
`Flapjack.Test.PanFixedStoreParity`, and the word-store boundary by
`Flapjack.Test.PanFlatStoreParity`. Value flattening is covered by
`Flapjack.Test.PanFlattenParity`; scoped local restoration (`res_var_def`) is
covered by `Flapjack.Test.PanResVarParity`. Their source references are
respectively
`cakeml/pancake/loop_to_wordScript.sml` and
`cakeml/pancake/semantics/panSemScript.sml`; `Flapjack.Test.PanOpParity`
additionally probes `pan_op_def` at lines 191--193.
`Flapjack.Test.LoopSetVarParity` probes `set_var_def` at
`cakeml/pancake/semantics/loopSemScript.sml:108-110`.
`Flapjack.Test.LoopDecClockParity` probes `dec_clock_def` at lines 42--43 of
the same source.
`Flapjack.Test.LoopFixClockParity` probes `fix_clock_def` at lines 46--49.
`Flapjack.Test.PanEvaluateDeclsParity` probes `evaluate_decls_def` at
`cakeml/pancake/semantics/panSemScript.sml:814-835`, including each declaration
constructor, ordered global updates, local clearing during initializer
evaluation, an in-domain word load, function-code replacement, and
shape/duplicate failure cases.
`pan_sem_state_eval_probe.out` records direct HOL EVAL of `eval_def` at
`cakeml/pancake/semantics/panSemScript.sml:209-297` for in-domain and
out-of-domain word loads, little- and big-endian byte loads, 32-bit loads, and
list-valued `word_op_def` operators with accepted and rejected operand counts.
The source-shaped generic definition is `Flapjack.Pancake.wordOpHOL`; its
all-width equation to the production RISC-V target is in
`Flapjack.Pancake.Semantics.CrepRuntimeTarget`. The state-derived Lean
boundary and its matching cases live in
`Flapjack.Pancake.Semantics.PanSemStateEval` and
`Flapjack.Test.PanSemStateEvalParity`.
`compile_def_probe.out` also records direct HOL evaluations of assigned Global
call destinations through `pan_to_crep$compile`: absent lookups, the
`One`/empty-list fallback, and inconsistent shape/name-list lengths. The
matching Lean cases live in `Flapjack.Test.CompileDefParity`.
`excp_rel_probe.out` and `ctxt_fc_probe.out` are direct EVALs from
`pan_to_crepProofTheory`, paired with `Flapjack.Test.PanToCrepRelationsParity`.
The `functions_projection` row in `ctxt_fc_probe.out` directly checks the
HOL `ctxt_fc_funcs_eq` theorem at `pan_to_crepProofScript.sml:2295` against
the kernel-checked Lean fixture in that module. The `vmax_nonempty_list` and
`vmax_empty_list` rows directly check `ctxt_fc_vmax` at line 2307 and are
paired with `ctxtFcVmax` Lean fixtures.
The `excp_rel` cases deliberately use a word-valued compiler-code map and a
shape-valued source map, matching the definition's independent HOL value types.
The `ctxt_fc` cases record `with_shape` slot slicing, ZIP truncation, and
`MAX_LIST` on an empty name list.
`code_rel_probe.out` records the HOL-inferred source/target code-map types,
compiled parameter return, localisation outcomes, function-signature lookup,
and target entry. The probe also proves matching and deliberately mismatching
`code_rel` instances against `code_rel_def`; the corresponding Lean relation
analogue tests live in `Flapjack.Test.PanToCrepCodeRelParity`. The Lean
relation remains untagged until its list-backed compiler body is replaced by
the exact HOL `compile` port tracked by bead `flapjack-pxn.18.3.1.4`.
`globals_lookup_probe.out` records direct HOL EVAL of
`pan_to_crepProof$globals_lookup_def` for a present singleton word and a
missing global; the matching Lean guards live in
`Flapjack.Test.PanToCrepGlobalsLookupParity`.
`crep_arith_dest_const_probe.out` records direct HOL EVAL of
`crep_arith$dest_const_def` at
`cakeml/pancake/crep_arithScript.sml:10-12` for a constant, variable, load,
and multiplication expression. Its Lean constructor checks live in
`Flapjack.Test.CrepeDestConstParity`.
`crep_dest_2exp_probe.out` records direct HOL EVAL of
`crep_arith$dest_2exp_def` at `cakeml/pancake/crep_arithScript.sml:15`, including
the corresponding `word_lsl 1w` results for successful exponents. Its Lean
destination, shift, and width checks live in `Flapjack.Test.CrepeDest2ExpParity`.
`crep_arith_eval_mul_const_probe.out` records direct HOL EVAL of
`crepSem$eval` after `crep_arith$mul_const` for zero, one, power-of-two, and
general multipliers, with a word-valued local. Its matching production runtime
cases live in `Flapjack.Test.CrepeMulConstParity`.
`crep_simp_exp_probe.out` records direct HOL EVAL of
`crep_arith$simp_exp_def` (`crep_arithScript.sml:59`) for constant folding,
left/right constant multiplication, nested multiplication, and recursive
load/word-operation children. Its Lean syntax checks live in
`Flapjack.Test.CrepeSimpExpParity`; these cases do not establish the
polymorphic evaluator-preservation theorem `simp_exp_correct1`.
`crep_eval_probe.out` records direct HOL EVAL of the `Const`, `Var`, `Load`,
`LoadGlob`, `BaseAddr`, and `TopAddr` constructor cases from
`cakeml/pancake/semantics/crepSemScript.sml:90-166`. The width-8 production
checks live in `Flapjack.Test.CrepEvalConstructorParity`; generic word-result
projection equations live beside `evalCrepRuntimeExp` in
`Flapjack/Pancake/Semantics/CrepSem.lean`. These equations cover a constructor
scope slice only: the target-extended runtime state and the remaining
word-operation and byte-load cases still need an evaluator correspondence.
`pan_globals_compile_top_probe.out` records original Pancake HOL evaluation
of `pan_globals$compile_top` for an absent start function (the total empty-list
result), a present `main` entry, and a global initializer in a nonempty
declaration list. Its Lean checks live in
`Flapjack.Test.PanGlobalsCompileTopForStartParity`.
`pan_structs_afindi_map_probe.out` records direct HOL EVAL for the hit and
miss cases of `afindi_MAP_eq` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:356`; its matching Lean
checks live in `Flapjack.Test.PanStructsAfindiParity`.
`pan_structs_afindi_length_probe.out` records direct HOL EVAL of first and
last successful key indices against `afindi_less_length` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:345`; Lean checks the same
rows in `Flapjack.Test.PanStructsAfindiParity`.
`pan_structs_afindi_el_probe.out` records direct HOL EVAL of the first
component at first, middle and last successful `afindi` indices for
`afindi_EL` at `cakeml/pancake/proofs/pan_structsProofScript.sml:430`; Lean
checks the equivalent `getElem?`-based API in
`Flapjack.Test.PanStructsAfindiParity`.
`pan_structs_alookup_afindi_probe.out` records direct HOL EVAL of present,
missing and duplicate-key cases for `ALOOKUP_eq_afindi` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:405`; matching `List.lookup`
regressions live in `Flapjack.Test.PanStructsAfindiParity`.
`pan_structs_compile_correct_probe.out` records direct HOL EVAL of
`convert_v_def` on a named record, source/converted `Skip` evaluator equations,
and zero-clock timeout / positive-clock decrement `Tick` evaluator equations,
plus HOL simplifier reduction of `convert_s_def` over nonempty local, global,
exception-shape, and function-code finite maps using the finite-map lookup
rules. These are used in `compile_correct` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:1034`. These rows cover
evaluator support only; the full theorem's finite-map premises and invariant,
shape-map, and result-value postconditions remain open in
`flapjack-pxn.18.5.3.29` and `.30`. Lean regressions live in
`Flapjack.Test.PanStructsCompileCorrect`.
`pan_structs_compile_exp_correct_probe.out` records HOL simplifier evaluations
of Local and Global variable-constructor instances and a Const-constructor
instance of `compile_exp_correct`; each tuple contains old shape, semantic
value shape, field validity, source evaluation, and converted target
evaluation. The production `structCompileExp`/`evalPanValueExp` cases are
proved in `panStructCompileExpCorrectVarCase` and
`panStructCompileExpCorrectConstCase` and exercised by finite-map regressions
in `Flapjack.Test.PanStructsCompileCorrect`. The other expression constructors
remain open.
`pan_structs_value_validity_probe.out` records direct HOL EVAL of the word,
matching/mismatching named-record, missing-context, and duplicate-key first
match rows for
`v_flds_ok_def` and `is_wf_shape_v_def`; the matching Bool-valued Lean
definitions and regressions live in
`Flapjack.Pancake.Proofs.PanStructs.CompileCorrect` and
`Flapjack.Test.PanStructsValueValidityParity`.
`pan_structs_afindi_append_probe.out` records direct HOL EVAL of prefix-hit,
shifted suffix-hit and missing-key rows for `afindi_append` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:417`; matching Lean cases
live in `Flapjack.Test.PanStructsAfindiParity`.
`pan_structs_dropwhile_afindi_probe.out` records direct HOL EVAL of first-hit,
later-hit and absent-key cases for `dropWhile_afindi` at
`cakeml/pancake/proofs/pan_structsProofScript.sml:334`; matching Lean rows
live in `Flapjack.Test.PanStructsAfindiParity`.
The `longdiv_code_probe.out` fixture probes the original software LongDiv
helper at `cakeml/compiler/backend/data_to_wordScript.sml:829-867` and the
RISC-V target's deliberate LongDiv encoding rejection.
The `prog_if_probe.out` fixture probes the comparison-materialization helper
`prog_if_def` at `cakeml/pancake/crep_to_loopScript.sml:34`, including its
canonical live-set insertion order.
The `compile_crepop_probe.out` fixture probes the RISC-V `Mul` case of
`compile_crepop_def` at line 42 of the same source.
The original Pancake source-level support boundary is also explicit in
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:2285-2291`: `LLongDiv` is
accepted by `loop_inst_ok` only for `x86_64`. Consequently, RISC-V parity must
port the `data_to_word` helper path rather than add a direct RISC-V lowering
for source `LLongDiv`.

From the repository root, with HOL4 and the CakeML checkout available,
regenerate both checked-in outputs with:

```sh
scripts/hol-probes/regenerate.sh
```

Normal Lean CI consumes the checked-in output and does not require HOL4. A
reviewer with HOL4 can rerun the command and inspect the diff. Each probe's
declaration and source path make its reference boundary explicit. The script
is incremental: a fixture is rerun only when its probe, the Pancake theory it
observes, or the script itself is newer than that fixture. Delete a fixture
when a forced regeneration is desired. To refresh one fixture while developing,
set `HOL_PROBE_ONLY` to its probe filename, for example:

```sh
HOL_PROBE_ONLY=pan_globals_compile_top_probeScript.sml scripts/hol-probes/regenerate.sh
```

The checked-in source-facing compiler corpus at
`scripts/parity-small-corpus.json` complements these semantic probes. Run
`scripts/parity-small-corpus.py` after building `flapjack-compile` to invoke
the original `cake --pancake --target=riscv` compiler and Flapjack on the same
five supported programs. The manifest records each original Cake stdout hash,
the CakeML semantic definition exercised by the fixture, and the P1 beads that
own any current generated/user-code differences. The runner compares the
complete runtime, generated-entry, and user-function sections; it does not
normalize instruction bytes.

The focused Pan-to-Crep fixtures are summarized in
[`docs/PAN-TO-CREP-PARITY-COVERAGE.md`](../../docs/PAN-TO-CREP-PARITY-COVERAGE.md).
CI validates that each listed direct-HOL case remains present in its committed
probe output and in the corresponding Lean test with
`scripts/pan-to-crep-coverage-report.py --check`.
