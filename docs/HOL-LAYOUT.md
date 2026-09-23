# HOL source layout

The primary Pancake modules now use the paths and names of the corresponding
scripts under `cakeml/pancake`. This is a location guide, not a claim that
every definition or theorem in a script has been ported. Declaration-level
provenance is recorded by `@[hol ...]` and checked by
`scripts/check-hol-refs.py --mapping`. The declaration inventory is in
[`HOL-THEOREM-MAP.json`](HOL-THEOREM-MAP.json); CI checks that every tagged
declaration and every theorem or lemma under `Flapjack/Pancake/Proofs` has an
entry, its HOL tag matches the entry, and reviewer and statement-status fields
are present. `pending_statement_review` and
`no_hol_reference_pending_classification` entries are open review work, not
claims of HOL correspondence. `documented_mismatch` records a known source
candidate whose Lean analogue remains untagged because its statement differs;
the mismatch must be explained beside the Lean declaration. The inventory
recognizes `theorem` and `lemma` declarations only; `#check` commands and
comments do not count as theorem entries or tests. Correctness claims are described in
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
| `proofs/pan_to_crepProofScript.sml` | `Flapjack/Pancake/Proofs/PanToCrep.lean`, `PanToCrep/CompileExpVmax.lean` |
| `pan_to_crepScript.sml` | `Flapjack/Pancake/PanToCrep.lean`, `PanToCrep/Compile.lean` |
| `crepLangScript.sml` | `Flapjack/Pancake/CrepLang.lean` |
| `crep_arithScript.sml` | `Flapjack/Pancake/CrepArith.lean` |
| `crep_inlineScript.sml` | `Flapjack/Pancake/CrepInline.lean`, `CrepInline/Pass.lean` |
| `crep_to_loopScript.sml` | `Flapjack/Pancake/CrepToLoop.lean`, `CrepToLoop/Optimise.lean` |
| `loopLangScript.sml` | `Flapjack/Pancake/LoopLang.lean` |
| `loop_callScript.sml` | `Flapjack/Pancake/LoopCall.lean` |
| `loop_liveScript.sml` | `Flapjack/Pancake/LoopLive.lean` |
| `loop_to_wordScript.sml` | `Flapjack/Pancake/LoopToWord.lean` |
| `semantics/panSemScript.sml` | `Flapjack/PanBst.lean`, `Flapjack/Pancake/Semantics/PanSem.lean`, `PanSemStateEval.lean` |
| `semantics/pan_commonPropsScript.sml` | `Flapjack/Pancake/Semantics/PanCommonProps.lean` |
| `semantics/crepSemScript.sml` | `Flapjack/Pancake/Semantics/CrepSem.lean`, `CrepSem/Eval.lean` |
| `semantics/crepPropsScript.sml` | `Flapjack/Pancake/Semantics/CrepProps.lean` |
| `semantics/loopSemScript.sml` | `Flapjack/Pancake/Semantics/LoopSem.lean` |
| `proofs/pan_simpProofScript.sml` | `Flapjack/Pancake/Proofs/PanSimp.lean`, `PanSimp/Evaluate.lean` |

Placement under `Proofs` does not imply that a whole pass correctness theorem
has been established. For declaration-level provenance, use
`scripts/check-hol-refs.py --mapping`; CI validates the review inventory with
`scripts/check_hol_theorem_map.py`. For untagged port candidates, use
`scripts/next-hol-port.py`. Track individual gaps and progress in
[GitHub issues](https://github.com/pirapira/flapjack/issues), not in this
layout guide.
