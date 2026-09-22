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
| `pan_globalsScript.sml` | `Flapjack/Pancake/PanGlobals.lean` |
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
| `proofs/pan_globalsProofScript.sml` | `Flapjack/Pancake/Proofs/PanGlobals.lean` (shape well-formedness theorems) |

Flapjack-specific helper lemmas supporting the shape proofs remain in
`Flapjack/PanGlobalsSemantics.lean`; they are not themselves attributed to HOL.
Their whole-list predicates and start-function interfaces are Flapjack-specific.
Placement under `Proofs` does not imply that a whole pass correctness theorem
has been established. The remaining moves and review gate are tracked by beads
`flapjack-pxn.18.3.1`–`flapjack-pxn.18.3.3`.
