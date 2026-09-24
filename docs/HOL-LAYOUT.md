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
uses `reviewed_list_as_array` when the HOL list fields are represented by Lean
arrays. For each qualified field, the reference checker requires a same-module
structure field and a `holListArrayWitness_<field>` theorem relating that field
to its HOL list with `RepresentsHOLNodeList`, without assuming that relation in
the witness premises. This checks witness shape and Lean kernel acceptance; it
does not establish cross-language equivalence by itself. Ordinary exact tags retain
`reviewed_exact`. The inventory
recognizes `theorem` and `lemma` declarations only; `#check` commands and
comments do not count as theorem entries or tests. Correctness claims are described in
[`SOUNDNESS.md`](SOUNDNESS.md).

The qualifier covers only the named representation fields; evaluator,
state-transition, error, hypothesis, and conclusion details must still match
HOL. See [`AGENTS.md`](../AGENTS.md#qualify-only-named-list-to-array-state-fields)
for the review rule.

| HOL script | Lean counterpart |
| --- | --- |
| `panLangScript.sml` | `Flapjack/Pancake/PanLang.lean` |
| `compiler/backend/wordLangScript.sml` | `Flapjack/Pancake/WordLang.lean` |
| `compiler/backend/semantics/wordConvsScript.sml` | `Flapjack/Pancake/WordConvs.lean` |
| `compiler/backend/stackLangScript.sml` | `Flapjack/Compiler/Backend/StackLang.lean` (generic HOL `store_name` and `prog` syntax) |
| `compiler/backend/semantics/stackPropsScript.sml` | `Flapjack/Compiler/Backend/StackProps.lean` (recursive `stack_asm_ok` clauses; asm-config bridge pending) |
| `compiler/backend/labLangScript.sml` | `Flapjack/Compiler/Backend/LabLang.lean` (generic HOL `lab`, `line`, and `sec` syntax) |
| `panStaticScript.sml` | `Flapjack/Pancake/PanStatic.lean` |
| `pan_simpScript.sml` | `Flapjack/Pancake/PanSimp.lean` |
| `pan_structsScript.sml` | `Flapjack/Pancake/PanStructs.lean` |
| `proofs/pan_structsProofScript.sml` | `Flapjack/Pancake/Proofs/PanStructs.lean` |
| `pan_globalsScript.sml` | `Flapjack/Pancake/PanGlobals.lean` |
| `proofs/pan_globalsProofScript.sml` | `Flapjack/Pancake/Proofs/PanGlobals.lean`, `PanGlobals/ShapeInfrastructure.lean` |
| `proofs/pan_to_crepProofScript.sml` | `Flapjack/Pancake/Proofs/PanToCrep.lean`, `PanToCrep/CompileExpVmax.lean`, `PanToCrep/CompileProgParams.lean`, `PanToCrep/Primop.lean` |
| `pan_to_crepScript.sml` | `Flapjack/Pancake/PanToCrep.lean`, `PanToCrep/Compile.lean`, `PanToCrep/CompileProg.lean` |
| `crepLangScript.sml` | `Flapjack/Pancake/CrepLang.lean` |
| `crep_arithScript.sml` | `Flapjack/Pancake/CrepArith.lean` |
| `crep_inlineScript.sml` | `Flapjack/Pancake/CrepInline.lean`, `CrepInline/Pass.lean` |
| `crep_to_loopScript.sml` | `Flapjack/Pancake/CrepToLoop.lean`, `CrepToLoop/Optimise.lean` |
| `loopLangScript.sml` | `Flapjack/Pancake/LoopLang.lean` |
| `loop_callScript.sml` | `Flapjack/Pancake/LoopCall.lean` |
| `loop_liveScript.sml` | `Flapjack/Pancake/LoopLive.lean` |
| `loop_to_wordScript.sml` | `Flapjack/Pancake/LoopToWord.lean` |
| `semantics/panSemScript.sml` | `Flapjack/PanBst.lean`, `Flapjack/PanValueFfiClockSemantics.lean`, `Flapjack/Pancake/Semantics/PanSem.lean`, `PanSem/Primop.lean`, `PanSemStateEval.lean` |
| `semantics/pan_commonPropsScript.sml` | `Flapjack/Pancake/Semantics/PanCommonProps.lean` |
| `semantics/panPropsScript.sml` | `Flapjack/Pancake/Semantics/PanProps.lean` |
| `semantics/crepSemScript.sml` | `Flapjack/Pancake/Semantics/CrepSem.lean`, `CrepSem/Eval.lean`, `CrepSem/Primop.lean` |
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
