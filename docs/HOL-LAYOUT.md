# HOL source layout

The primary Pancake modules now use the paths and names of the corresponding
scripts under `cakeml/pancake`. This is a location guide, not a claim that
every definition or theorem in a script has been ported. Declaration-level
provenance is recorded by `@[hol ...]` and checked by
`scripts/check-hol-refs.py --mapping`. Correctness claims are described in
[`SOUNDNESS.md`](SOUNDNESS.md).

| HOL script | Lean counterpart |
| --- | --- |
| `panLangScript.sml` | `Flapjack/Pancake/PanLang.lean` |
| `panStaticScript.sml` | `Flapjack/Pancake/PanStatic.lean` |
| `pan_simpScript.sml` | `Flapjack/Pancake/PanSimp.lean` |
| `pan_structsScript.sml` | `Flapjack/Pancake/PanStructs.lean` |
| `proofs/pan_structsProofScript.sml` | `Flapjack/Pancake/Proofs/PanStructs.lean` |
| `pan_globalsScript.sml` | `Flapjack/Pancake/PanGlobals.lean` |
| `proofs/pan_globalsProofScript.sml` | `Flapjack/Pancake/Proofs/PanGlobals.lean`, `PanGlobals/ShapeInfrastructure.lean` |
| `proofs/pan_to_crepProofScript.sml` | `Flapjack/Pancake/Proofs/PanToCrep.lean` |
| `pan_to_crepScript.sml` | `Flapjack/Pancake/PanToCrep.lean`, `PanToCrep/Compile.lean` |
| `crepLangScript.sml` | `Flapjack/Pancake/CrepLang.lean` |
| `crep_arithScript.sml` | `Flapjack/Pancake/CrepArith.lean` |
| `crep_inlineScript.sml` | `Flapjack/Pancake/CrepInline.lean`, `CrepInline/Pass.lean` |
| `crep_to_loopScript.sml` | `Flapjack/Pancake/CrepToLoop.lean`, `CrepToLoop/Optimise.lean` |
| `loopLangScript.sml` | `Flapjack/Pancake/LoopLang.lean` |
| `loop_callScript.sml` | `Flapjack/Pancake/LoopCall.lean` |
| `loop_liveScript.sml` | `Flapjack/Pancake/LoopLive.lean` |
| `loop_to_wordScript.sml` | `Flapjack/Pancake/LoopToWord.lean` |
| `semantics/panSemScript.sml` | `Flapjack/Pancake/Semantics/PanSem.lean` |
| `semantics/crepSemScript.sml` | `Flapjack/Pancake/Semantics/CrepSem.lean`, `CrepSem/Eval.lean` |
| `semantics/crepPropsScript.sml` | `Flapjack/Pancake/Semantics/CrepProps.lean` |
| `semantics/loopSemScript.sml` | `Flapjack/Pancake/Semantics/LoopSem.lean` |
| `proofs/pan_simpProofScript.sml` | `Flapjack/Pancake/Proofs/PanSimp.lean`, `PanSimp/Evaluate.lean` |

`compile_top_shape_wf` from `proofs/pan_globalsProofScript.sml` is ported in
`Flapjack/Pancake/Proofs/PanGlobals.lean`. It assumes successful faithful
`evaluateDecls` and HOL's admissible-declaration condition, then proves the
function-shape property of the total `globalCompileTopForStart` result. Its
statement contract is checked by
`Flapjack/Test/PanGlobalsCompileTopShapeWfParity.lean`. The related
`compile_top_shape_wf_nil` corollary remains open under bead
`flapjack-pxn.18.3.2.2`.

`evaluate_decls_def` from `semantics/panSemScript.sml` is ported in
`Flapjack/Pancake/Semantics/PanSem.lean` as `evaluateDecls`. Its dedicated
state retains full function entries and exception shapes, while runtime
expression evaluation uses the source empty-local environment for each value
declaration. Direct HOL-EVAL branch results and Lean parity fixtures are kept
in `scripts/hol-probes/pan_evaluate_decls_probe.out` and
`Flapjack/Test/PanEvaluateDeclsParity.lean`.

The total `compile_top_def` result and the HOL-shaped
`compile_top_only_functions_or_exns` theorem are now present. Reusable
Flapjack-specific shape predicates and pass lemmas live in
`PanGlobals/ShapeInfrastructure.lean`; they use Flapjack's value evaluator
and are infrastructure, not ports of the two open HOL shape theorems.

Additional helper, semantic, and proof modules still live at the old top
level while their exact HOL counterparts and statement shapes are reviewed.
`Flapjack/PanStructsAfindi.lean` retains residual shape-context helpers; the
`afindi` implementation and its matched proof declarations now live in the
listed Pancake modules.

Placement under `Proofs` does not imply that a whole pass correctness theorem
has been established. The remaining moves and review gate are tracked by beads
`flapjack-pxn.18.3.1`–`flapjack-pxn.18.3.3`.
