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

## ML bindings versus declarations

`scripts/check-hol-refs.py` recognizes a HOL declaration in two forms: a
definition/theorem header (`Theorem`, `Triviality`, `Definition`, `Datatype`,
`Inductive`, `CoInductive`, `Overload`, `Type`) or an ML `val NAME = ...`
binding. A theorem-valued binding such as
`val llist_shorter_lnth = Q.prove (...)` is a proved result, so a Lean
counterpart may cite it from `@[hol]`. The scanner accepts every
`val NAME =` line and cannot distinguish a proved binding from an arbitrary ML
value, so it does not enforce theorem status: source review is responsible for
never tagging a non-theorem value, and the reference checker only verifies that
the cited name occurs in one of the two syntactic forms.

| HOL script | Lean counterpart |
| --- | --- |
| `pancake/pan_to_targetScript.sml` | `Flapjack/Pancake/PanToTarget.lean` |
| `pancake/proofs/pan_to_targetProofScript.sml` | `Flapjack/Pancake/Proofs/PanToTarget.lean` and its `PanToTarget/` submodules |
| `panLangScript.sml` | `Flapjack/Pancake/PanLang.lean` (exact `mlstring`-named syntax over the faithful carriers in `Flapjack/Pancake/PanLang/Shape.lean`, `Flapjack/Pancake/PanLang/Exp.lean` and `Flapjack/Pancake/PanLang/Prog.lean` and `Flapjack/Pancake/PanLang/Decl.lean` (`fun_decl`, `decl`, `struct_info`, byte-ranged production roundtrips and the MlString-keyed struct-context pass-boundary bridge), and follow-ups) |
| `compiler/backend/word_simpScript.sml` | `Flapjack/Compiler/Backend/WordSimp.lean` |
| `compiler/backend/proofs/word_simpProofScript.sml` | `Flapjack/Compiler/Backend/WordSimp/Proofs/` (`GcWordConst.lean` `is_gc_word_const`) |
| `compiler/backend/proofs/wordConvsProofScript.sml` | `Flapjack/Pancake/Proofs/WordConvs/` |
| `compiler/backend/wordLangScript.sml` | `Flapjack/Pancake/WordLang.lean` |
| `compiler/backend/backendScript.sml` | `Flapjack/Compiler/Backend/Backend.lean` |
| `compiler/backend/backend_commonScript.sml` | `Flapjack/Compiler/Backend/BackendCommon.lean` and its `BackendCommon/BvlStubs.lean` submodule |
| `compiler/backend/bvl_to_bviScript.sml` | `Flapjack/Compiler/Backend/BvlToBvi.lean` and its `BvlToBvi/Config.lean` submodule |
| `compiler/backend/semantics/wordConvsScript.sml` | `Flapjack/Pancake/WordConvs.lean` |
| `compiler/backend/stackLangScript.sml` | `Flapjack/Compiler/Backend/StackLang.lean`, `Flapjack/Compiler/Encoders/Asm.lean`, `Flapjack/Compiler/Backend/StackLang/Prog.lean`, `Flapjack/Compiler/Backend/StackLang/Overloads.lean` (`While`/`move`/arithmetic overloads, `list_Seq`, `gc_stub_location`), `Flapjack/Compiler/Backend/StackCarrier.lean`, `Flapjack/Compiler/Backend/MlStringBridge.lean` |
| `basis/pure/mlstringScript.sml` | `Flapjack/Basis/Pure/MlString.lean` (`mlstring = implode string`, `string = char list`; HOL `char` modeled by `HolChar = BitVec 8`, the canonical 256-element carrier); kernel-checked `String`<->`mlstring` bridge and stack-program embedding in `Flapjack/Compiler/Backend/MlStringBridge.lean` |
| `basis/pure/mllistScript.sml` (`sort`) | `Flapjack/Basis/Pure/MlList.lean` (tagged `sort_def`, with an untagged clause-for-clause rendering of HOL `mergesort_tail`) |
| `compiler/backend/word_allocScript.sml` | `Flapjack/Compiler/Backend/WordAlloc/` (`Expressions.lean` exact expression renaming and live sets) |
| `compiler/backend/word_removeScript.sml` | `Flapjack/Compiler/Backend/WordRemove.lean` |
| `compiler/backend/word_unreachScript.sml` | `Flapjack/Compiler/Backend/WordUnreach.lean` |
| `compiler/backend/word_copyScript.sml` | `Flapjack/Compiler/Backend/WordCopy.lean` |
| `compiler/backend/word_to_wordScript.sml` | `Flapjack/Compiler/Backend/WordToWord/` (`Config.lean` config and `next_n_oracle`; `Compile.lean` `compile_single`, `full_compile_single` and `compile`) |
| `compiler/backend/proofs/word_to_wordProofScript.sml` | `Flapjack/Compiler/Backend/WordToWord/Proofs/` (`CodeRel.lean` `code_rel` and its helpers; `CompileSingle.lean` `FST_compile_single` and `compile_single_lem`; `CompileSingleCorrect/` the `compile_single_correct` case pieces and assembly; `CompileWordToWord.lean` `compile_word_to_word_thm`) |
| `misc/miscScript.sml` (`anub`) | `Flapjack/Misc/Anub.lean` |
| `compiler/backend/data_to_wordScript.sml` | `Flapjack/Compiler/Backend/DataToWord/` (`Config.lean` gc_kind/config and pointer-layout helpers) |
| `compiler/backend/proofs/word_gcFunctionsScript.sml` | `Flapjack/Compiler/Backend/WordGcFunctions.lean` (copying, generational and partial GC definitions and `word_gc_fun`); `WordGcFunctions/Roots.lean` (root `EVERY2`/`LENGTH` theorems) |
| `compiler/backend/proofs/word_allocProofScript.sml` | `Flapjack/Compiler/Backend/WordAlloc/Proofs/` (`StrongLocalsRel.lean` live-scoped lookup transport) |
| `compiler/backend/proofs/word_unreachProofScript.sml` | `Flapjack/Compiler/Backend/WordUnreach/Proofs.lean` |
| `compiler/backend/proofs/word_instProofScript.sml` | `Flapjack/Compiler/Backend/WordInst/Proofs/` (`PullExp.lean` pull_exp/optimize_consts/flatten_exp group, `InstSelect.lean` inst_select_exp_thm/inst_select_thm/inst_select_Loop_helper, `ThreeToTwo.lean` three_to_two_reg family) |
| `compiler/backend/proofs/word_removeProofScript.sml` | `Flapjack/Compiler/Backend/WordRemove/Proofs/` (`CompileState.lean` compile_state group, `Correct.lean` word_remove_correct) |
| `compiler/backend/proofs/word_copyProofScript.sml` | `Flapjack/Compiler/Backend/WordCopy/Proofs/` (`Invariant.lean` CPstate_inv group, `Models.lean` CPstate_models group, `Move.lean` copy_prop_move and invariant preservation, `Store.lean` move/store models and expression congruences, `Inst.lean` copy_prop_inst semantics, `Correct.lean` copy_prop_correct and evaluate_copy_prop) |
| `compiler/backend/word_cseScript.sml` | `Flapjack/Compiler/Backend/WordCse/` (`Knowledge.lean`, `RegisterData.lean`, `InstructionKeys.lean`, `RegisterUses.lean`, `Canonical*.lean`, `FactProducers.lean`, `Join.lean` and `Production*.lean` definitions and clause bodies; `Transform.lean` `word_cseInst`, `word_cse`, `word_common_subexp_elim` and `Seqs`) |
| `compiler/backend/proofs/word_cseProofScript.sml` | `Flapjack/Compiler/Backend/WordCse/Proofs/` (`ListOrder.lean` listCmp laws, `IntersectionInvariant.lean` `invariant_bm_inter_eq`, `IntersectionAccumulator.lean` `bm_inter_eq_acc_thm` and `lookup_bm_inter_eq`, `KnowledgeLemmas.lean` the listCmp-map and `register_read(s)` lemmas, `WfDataPreservation.lean` the `wf_data` preservation section, `DataInvTransport.lean` the `data_inv` transport lemmas, `DataInvUpdates.lean` the `data_inv` knowledge-update lemmas, `FactInsert.lean` the fact-producer correctness group, `MoveLemmas.lean` the move and clock lemmas, `CompCorrect.lean` with `CompCorrect/` cases `comp_correct` and `word_common_subexp_elim_correct`, `Conventions.lean` the syntactic-convention section) |
| `compiler/backend/semantics/wordSemScript.sml` | `Flapjack/Compiler/Backend/Semantics/WordSem/` (`State.lean` carriers, `Accessors.lean` state accessors and `word_exp`, `Env.lean` env/stack/cut helpers, `CallHelpers.lean` call/loop helpers, `Alloc.lean` find_code/gc/alloc/assign, `ShMem.lean` sh_mem_*/share_inst, `Inst.lean` inst_def, `Evaluate.lean` evaluate_def, `EvaluateClock.lean` clock lemmas, `EvaluateInd.lean` rebound evaluate_ind/evaluate_def, `Semantics.lean` semantics_def); the older call-aware executable analogue `Flapjack/WordSemantics.lean` is not a port |
| `compiler/backend/semantics/wordPropsScript.sml` | `Flapjack/Compiler/Backend/Semantics/WordSem/EnvListSupport.lean` (`env_to_list_lookup_equiv`, over the exact `wordSemEnvToList` result and Spt lookup carriers); `Flapjack/Compiler/Backend/Semantics/WordSem/Props/` (`EvaluateAddClock.lean` clock-constancy lemmas and `evaluate_add_clock`, `EvaluateDecClock.lean` `evaluate_dec_clock`, `LocalsRel.lean` locals_rel family through `locals_rel_evaluate_thm`, `StateConst.lean` the `*_const`/`*_with_const` state-constancy group) |
| `compiler/backend/semantics/stackPropsScript.sml` | `Flapjack/Compiler/Backend/StackProps.lean` (recursive `stack_asm_ok` clauses and `addr_ok`, linked to the `asm_config` predicates; `StackProps/EvaluateAddClock.lean` and `StackProps/EvaluateConsts.lean` prove `evaluate_add_clock` and `evaluate_consts` over the exact StackSem evaluator; `StackProps/CallArgs.lean` `call_args_def`) |
| `compiler/backend/semantics/backendPropsScript.sml` | `Flapjack/Compiler/Backend/BackendProps.lean` (nonzero-entry label restriction and set support) |
| `compiler/backend/semantics/stackSemScript.sml` | `Flapjack/Compiler/Backend/Semantics/StackSem/State.lean` (exact state/result carriers and canonical finite-support state roundtrip), `StackSem/StateOps.lean` (memory/register/clock primitives), `StackSem/Control.lean` (code lookup and clock clamp/bound), `StackSem/Bitmap.lean` (polymorphic bitmap filter/map and length theorems), `StackSem/WordBitmap.lean` (word bit length and bitmap decoding), `StackSem/StackCodec.lean` (descriptor and recursive stack codecs), `StackSem/Evaluate.lean` (assembled total evaluator), `StackSem/EvaluateDef.lean` (`evaluate` and the 34-clause `evaluate_def`), `StackSem/Semantics.lean` (observational `semantics_def`) |
| `compiler/encoders/asm/asmScript.sml` | `Flapjack/Compiler/Encoders/Asm.lean` (asm_config validity predicates: `reg_ok`, `fp_reg_ok`, `reg_imm_ok`, `offset_ok`, `arith_ok`, `fp_ok`, `cmp_ok`, `inst_ok`; exact carriers `reg_imm`, `addr`, `inst`, `arith`, `fp`, `binop`, `cmp`, `memop`, `asm`) |
| `compiler/encoders/asm/asmSemScript.sml` | `Flapjack/Compiler/Encoders/AsmSem/` (`State.lean` asm_state, `Arithmetic.lean` register/arith updates, `FpUpdates.lean` fp_upd, `Memory.lean` addr/read_mem_word/write_mem_word, `MemOps.lean` mem_load/mem_store/mem_op, `Step.lean` inst/jump_to_offset/asm/asm_step) |
| `compiler/encoders/asm/asmPropsScript.sml` | `Flapjack/Compiler/Encoders/AsmProps/` (`Target.lean` target carrier and target_state_rel, `Encoding.lean` enc_ok/target_ok, `Interference.lean`, `Assertions.lean` asserts/asserts2, `PcCoverage.lean` all_pcs, `Memory.lean` memory-word invariants, `EncoderCorrect.lean` encoder_correct) |
| `compiler/backend/labLangScript.sml` | `Flapjack/Compiler/Backend/LabLang.lean` (generic HOL `lab`, `line`, and `sec` syntax) |
| `compiler/backend/lab_to_targetScript.sml` | `Flapjack/Compiler/Backend/LabProps.lean` (`cbw_to_asm` carrier boundary only; target encoding remains open), `Flapjack/Compiler/Backend/LabToTarget/` (exact encoding/labels/positions/second-pass/padding/remove-labels/shmem-info and the `config`/`compile_lab`/`compile` entry) |
| `compiler/backend/lab_filterScript.sml` | `Flapjack/Compiler/Backend/LabFilter.lean` |
| `misc/miscScript.sml` (`list_subset`) | `Flapjack/Misc/ListSubset.lean` |
| `compiler/backend/proofs/lab_filterProofScript.sml` | `Flapjack/Compiler/Backend/LabFilter/Proofs.lean` (submodules in `LabFilter/Proofs/`) |
| `compiler/backend/proofs/lab_to_targetProofScript.sml` | `Flapjack/Compiler/Backend/LabToTarget/` (code similarity and structural preservation; `ShareMemDomain.lean` share_mem_domain_code_rel, `ShareMemState.lean` share_mem_state_rel) |
| `compiler/backend/semantics/labPropsScript.sml` | `Flapjack/Compiler/Backend/LabProps.lean` (`line_ok_pre`, `sec_ok_pre`, and `all_enc_ok_pre`; asm/config carrier bridge remains explicit) |
| `compiler/backend/semantics/labPropsScript.sml` | `Flapjack/Compiler/Backend/LabProps.lean` (`line_ok_pre`, `sec_ok_pre`, and `all_enc_ok_pre`; asm/config carrier bridge remains explicit) |
| `compiler/backend/semantics/labSemScript.sml` | `Flapjack/Compiler/Backend/LabSem.lean` (`is_Label`) |
| `semantics/astScript.sml` | `Flapjack/AstHOL.lean` (exact `ast$shift` carrier; the remaining `ast` declarations are an open inventory item) |
| `compiler/backend/stack_namesScript.sml` | `Flapjack/Compiler/Backend/StackNames.lean` |
| `compiler/backend/proofs/stack_namesProofScript.sml` | `Flapjack/Compiler/Backend/StackNames/` (`NamesOk.lean` names_ok lemmas, `AsmAdmissibility/` stack_asm_ok, `Proofs/RenameState.lean` rename_state group over the MAP_KEYS rendering in `Flapjack/FiniteMap/MapKeys.lean`, `Proofs/CompCorrect.lean` comp_correct, `Proofs/CompileSemantics.lean` compile_semantics(_alt), `Proofs/MakeInit.lean` make_init_def/make_init_semantics, `Proofs/LabelsCallArgs.lean` stack_names_lab_pres/stack_names_call_args) |
| `compiler/backend/riscv/riscv_configScript.sml` | `Flapjack/Compiler/Backend/RiscVConfig/Names.lean` |
| `compiler/backend/stackLangScript.sml` (shared-word `prog`) | `Flapjack/Compiler/Backend/StackCarrier.lean` |
| `compiler/backend/stack_removeScript.sml` | `Flapjack/Compiler/Backend/StackRemove.lean` (`max_stack_alloc`, `word_offset`, `store_list`, `store_length`, `stack_err_lab`, `halt_inst`; also the tagged stackLang instruction overloads `left_shift_inst`/`right_shift_inst`/`const_inst`/`load_inst`/`store_inst` over the exact `HolProg` carrier) |
| `compiler/backend/proofs/stack_removeProofScript.sml` | `Flapjack/Compiler/Backend/StackRemove.lean` (`is_SOME_Word`, `read_mem`/`LENGTH_read_mem`, `addresses`/`IN_addresses`; `names_ok` Prop-shaped tag); full native code relation in `Flapjack/Compiler/Backend/StackRemove/Proofs/CodeRelation.lean` |
| `HOL/examples/machine-code/hoare-triple/set_sepScript.sml` | `Flapjack/Misc/SetSep.lean` (generic paired function graph and heap predicates) |
| `compiler/backend/proofs/stack_allocProofScript.sml` | `Flapjack/Compiler/Backend/StackAlloc/Proofs/` (`WordLemmas.lean` word/bit-length lemmas, `Bitmap.lean` bitmap list lemmas and `enc_dec_stack`, `GcBitmaps.lean` proof-side GC definitions, `Unroll.lean` bitmap-collector unrolling theorems, `Submap.lean` SUBMAP lemmas, `CodeThm/` GC code simulation theorems) |
| `compiler/backend/stack_allocScript.sml` | `Flapjack/Compiler/Backend/StackAlloc.lean` (generic `next_lab`; executable pass counterpart remains `Flapjack/StackAlloc.lean`); `StackAlloc/GcCode.lean` (GC stub code); `StackAlloc/Compile.lean` (`next_lab`, `comp`, `prog_comp`, `stubs`, `compile` over `HolProg`) |
| `compiler/backend/stack_to_labScript.sml` | `Flapjack/Compiler/Backend/StackToLab.lean`, `Flapjack/Compiler/Backend/StackToLab/Native.lean` (`flatten`, `prog_to_section`), `Flapjack/Compiler/Backend/StackToLab/Compile.lean` (`is_gen_gc`, `config`, `compile`, `compile_no_stubs`) |
| `compiler/backend/reg_alloc/parmoveScript.sml` | `Flapjack/Compiler/Backend/Parmove.lean` |
| `compiler/backend/word_to_stackScript.sml` | `Flapjack/Compiler/Backend/WordToStack.lean`, `Flapjack/Compiler/Backend/WordToStackRegFormat.lean` |
| `compiler/backend/proofs/word_to_stackProofScript.sml` | `Flapjack/Compiler/Backend/WordToStack/Proofs/` (theorem groups, including `StackSize.lean`) |
| `panStaticScript.sml` | `Flapjack/Pancake/PanStatic.lean` |
| `pan_simpScript.sml` | `Flapjack/Pancake/PanSimp.lean` |
| `pan_structsScript.sml` | `Flapjack/Pancake/PanStructs.lean` |
| `proofs/pan_structsProofScript.sml` | `Flapjack/Pancake/Proofs/PanStructs.lean` |
| `pan_globalsScript.sml` | `Flapjack/Pancake/PanGlobals.lean` |
| `proofs/pan_globalsProofScript.sml` | `Flapjack/Pancake/Proofs/PanGlobals.lean`, `PanGlobals/ShapeInfrastructure.lean` |
| `proofs/pan_to_crepProofScript.sml` | `Flapjack/Pancake/Proofs/PanToCrep.lean`, `PanToCrep/CompileExpVmax.lean`, `PanToCrep/CompileProgParams.lean`, `PanToCrep/Primop.lean` |
| `pan_to_crepScript.sml` | `Flapjack/Pancake/PanToCrep.lean`, `PanToCrep/Compile.lean`, `PanToCrep/CompileProg.lean` |
| `pan_to_wordScript.sml` | `Flapjack/Pancake/PanToWord.lean` |
| `crepLangScript.sml` | `Flapjack/Pancake/CrepLang.lean`, `Flapjack/Pancake/CrepLang/Exp.lean` (exact width-indexed `CrepExpHOL`), `Flapjack/Pancake/CrepLang/Prog.lean` (exact width-indexed `CrepProgHOL`) |
| `crep_arithScript.sml` | `Flapjack/Pancake/CrepArith.lean` |
| `crep_inlineScript.sml` | `Flapjack/Pancake/CrepInline.lean`, `CrepInline/Pass.lean` |
| `crep_to_loopScript.sml` | `Flapjack/Pancake/CrepToLoop.lean`, `CrepToLoop/Optimise.lean` |
| `proofs/crep_to_loopProofScript.sml` | `Flapjack/Pancake/CrepToLoop/StateRel.lean` (proof relations and exact `mem_lookup_fromalist_some` port) |
| `misc/miscScript.sml` (`spt`/`num_set`) | `Flapjack/Misc/Sptree.lean` (exact `spt` inductive carrier + tagged `num_set` abbrev; `Spt` itself untagged because HOL/src is outside cakeml) |
| `loopLangScript.sml` | `Flapjack/Pancake/LoopLang.lean` (exact exp/loop_arith/prog carriers, now over the exact `unit spt`-backed `NumSet`; executable `LoopProg` bridge tracked by .18.5.17.1.1) |
| `loop_callScript.sml` | `Flapjack/Pancake/LoopCall.lean`, `LoopCall/IsLoad.lean` |
| `proofs/loop_callProofScript.sml` | `Flapjack/Pancake/Proofs/LoopCall/CompileCorrect.lean` (`labels_in_def`, `compile_correct`) |
| `loop_liveScript.sml` | `Flapjack/Pancake/LoopLive.lean`, `LoopLive/Fixedpoint.lean` |
| `proofs/loop_liveProofScript.sml` | `Flapjack/Pancake/Proofs/LoopLive/CompileCorrect.lean` (`compile_correct` and its case pieces), `LoopLive/Optimise.lean` (`mark_correct`, `comp_correct`, `optimise_correct`) |
| `loop_to_wordScript.sml` | `Flapjack/Pancake/LoopToWord.lean` |
| `semantics/panSemScript.sml` | `Flapjack/PanBst.lean`, `Flapjack/PanValueFfiClockSemantics.lean`, `Flapjack/Pancake/Semantics/PanSem.lean`, `PanSem/Primop.lean`, `PanSem/ValueHOL.lean`, `PanSem/MemLoadHOL.lean`, `PanSemStateEval.lean`, `PanSem/Semantics.lean` (exact `semantics_def` over `evaluateHOLFiniteState`) |
| `semantics/pan_commonPropsScript.sml` | `Flapjack/Pancake/Semantics/PanCommonProps.lean` |
| `pan_commonScript.sml` | `Flapjack/Pancake/PanCommon.lean` |
| `misc/miscScript.sml` (`app_list`/`append`) | `Flapjack/Misc/AppList.lean` |
| `misc/miscScript.sml` (`good_dimindex`) | `Flapjack/Misc/GoodDimindex.lean` (exact `good_dimindex` predicate) |
| `semantics/panPropsScript.sml` | `Flapjack/Pancake/Semantics/PanProps.lean`, `PanProps/EvalInvariant.lean`, `PanProps/MemByteArray.lean` (exact `write_bytearray_update_byte` / `read_write_bytearray_lemma`), `PanProps/LocalisedExpSimps.lean`, `PanProps/NamelessExpSimps.lean`, `PanProps/EvaluateAddClockIoEventsMono.lean` |
| `semantics/crepSemScript.sml` | `Flapjack/Pancake/Semantics/CrepSem.lean`, `CrepSem/Eval.lean`, `CrepSem/TotalEval.lean`, `CrepSem/Primop.lean`, `CrepSem/LookupCode.lean` |
| `semantics/crepPropsScript.sml` | `Flapjack/Pancake/Semantics/CrepProps.lean` |
| `semantics/loopSemScript.sml` | `Flapjack/Pancake/Semantics/LoopSem.lean`; exact width-indexed `state` carrier + production bridge in `Flapjack/Pancake/Semantics/LoopSemState.lean` (untagged pending exact sub-carriers) |
| `semantics/ffi/ffiScript.sml` | `Flapjack/Ffi.lean` (production FFI state/events), `Flapjack/FfiHOL.lean` (exact ffi_outcome/oracle_result/shmem_op/ffiname/oracle/oracle_function/io_event/final_event/ffi_state/ffi_result carriers + call_FFI) |
| `semantics/fpSemScript.sml` | `Flapjack/FpSemHOL.lean` (tagged `fpfma_def`, over the HOL `binary_ieee`/`machine_ieee` renderings in `Flapjack/Misc/BinaryIeee*.lean` and `Flapjack/Misc/MachineIeee*.lean`) |
| `semantics/proofs/evaluatePropsScript.sml` | `Flapjack/EvaluateProps.lean` |
| `semantics/proofs/semanticsPropsScript.sml` | `Flapjack/SemanticsProps.lean` (structural behavior and `implements'` analogue; HOL `llist` representation bridge remains open) |
| `proofs/pan_simpProofScript.sml` | `Flapjack/Pancake/Proofs/PanSimp.lean`, `PanSimp/Evaluate.lean` |
| `proofs/pan_to_wordProofScript.sml` | `Flapjack/Pancake/Proofs/PanToWord.lean` |

Placement under `Proofs` does not imply that a whole pass correctness theorem
has been established. For declaration-level provenance, use
`scripts/check-hol-refs.py --mapping`; CI validates the review inventory with
`scripts/check_hol_theorem_map.py`. For untagged port candidates, use
`scripts/next-hol-port.py`. Track individual gaps and progress in
[GitHub issues](https://github.com/pirapira/flapjack/issues), not in this
layout guide.
| compiler/backend/reg_alloc/reg_allocScript.sml | Flapjack/Compiler/Backend/RegAlloc.lean |
| compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml | Flapjack/Compiler/Backend/RegAlloc/Proofs.lean |
| compiler/backend/reg_alloc/linear_scanScript.sml | Flapjack/Compiler/Backend/LinearScan.lean |
| compiler/backend/reg_alloc/proofs/linear_scanProofScript.sml | Flapjack/Compiler/Backend/LinearScan/Proofs.lean |
| translator/monadic/monad_base/ml_monadBaseScript.sml | Flapjack/Translator/Monadic/MonadBase.lean (fixed arrays in `MonadBase/Arrays.lean`) |
| `misc/miscScript.sml` (`the`) | `Flapjack/Misc/MiscThe.lean` |
| `misc/miscScript.sml` (`LLOOKUP` optional indexing and list-update laws) | `Flapjack/Misc/ListLookup.lean` |

The pinned external `hol4/src/coretypes/optionScript.sml` counterpart is
`Flapjack/Misc/Option.lean`.

The pinned external `hol4/src/coalgebras/llistScript.sml` counterpart is
`Flapjack/Misc/LList.lean`; `lprefix_lubScript.sml` chain and least-upper-bound
declarations remain in `Flapjack/Misc/LprefixLub.lean`.

The pinned external `HOL/src/n-bit/byteScript.sml` counterpart is
`Flapjack/Byte.lean` (byte extraction and arbitrary-count word serialization).

The pinned external `HOL/src/n-bit/alignmentScript.sml` counterpart is
`Flapjack/Misc/Alignment.lean` (`align`, `aligned`, `byte_align`, `byte_aligned`, and
`wordsScript.sml`'s `word_slice`), with production bridges in `Flapjack/Misc/Alignment/Production.lean`.

The pinned external `HOL/examples/l3-machine-code/riscv/model/riscvScript.sml` (the L3-generated
RISC-V model) counterpart is `Flapjack/RiscV/L3/` (`Types.lean`: every `Construct`/`Record`
datatype and the `riscv_state` record; `Defs.lean`: the selected complete
FP/state equations and their source dependency closure; `Support.lean`:
library-rendering infrastructure sharing the canonical `Flapjack.holArb`).
The full original dependency export is reproduced by
`scripts/l3/regenerate-export.sh` from the pinned HOL. Generator self-consistency
checks are distinct from source review and the finite original HOL probes.

The pinned external `HOL/src/pred_set/src/pred_setScript.sml` counterpart is
`Flapjack/Misc/PredSet.lean` (the left inverse `LINV_OPT`/`LINV`, sets as predicates).

The pinned external `HOL/src/num/extra_theories/logrootScript.sml` counterpart is
`Flapjack/Misc/Logroot.lean` (the specified `LOG`, rendered by Hilbert choice like HOL's
`new_specification`), and `HOL/src/num/extra_theories/bitScript.sml`'s is `Flapjack/Misc/Bit.lean`
(`LOG2`).

The pinned external `hol4/src/finite_maps/sptreeScript.sml` counterpart is
`Flapjack/Misc/Sptree.lean` with submodules under `Flapjack/Misc/Sptree/` (for example
`Map.lean` for `map_def`/`lookup_map` and `InterEq.lean` for `inter_eq_def`).

The pinned external `HOL/src/sort/mergesortScript.sml` counterpart is
`Flapjack/Misc/Mergesort.lean` (the non-tail `sort2`/`sort3`/`merge`/`mergesortN`, their
sortedness, and the tail-recursive correctness lemmas over the untagged tail rendering in
`Flapjack/Basis/Pure/MlList.lean`).

The pinned external `HOL/src/floating-point/binary_ieeeScript.sml` counterpart is
`Flapjack/Misc/BinaryIeee.lean` with its rendering family `BinaryIeeeRound.lean`,
`BinaryIeeeArith.lean`, `BinaryIeeeConvert.lean` and `BinaryIeeeSqrt.lean`; the
arbitrary-real (Mathlib `ℝ`) ports of its real-argument declarations are in
`Flapjack/Misc/BinaryIeeeSqrt/RealCarrier.lean`. `HOL/src/floating-point/machine_ieeeScript.sml`,
including the declarations `machine_ieeeLib` generates at its fp32/fp64 encoding calls,
maps to `Flapjack/Misc/MachineIeee.lean` with submodules `Arith.lean`, `Convert.lean`,
`ConvertInt.lean`, `ConvertReal.lean` and `SqrtReal.lean` under `Flapjack/Misc/MachineIeee/`.


### Computed finite-map result observations

`(fmap_as_finite_support_result_observations := [Producer, ...])` records
only the canonical finite-support representation of explicitly named imported
map producers used in a tagged declaration's type. Each producer must return
`HolFiniteMapExact`, carry the standalone result qualifier, have its checked
same-module lookup witness, and have a source-reviewed result manifest record.
The observer has its own `reviewed_fmap_as_finite_support_result_observations`
record with exactly the same producer list and a complete source comparison.
Producer acceptance does not establish observer acceptance. The checker rejects
unused, ambiguous, shadowed, unqualified, unreviewed, non-map, and unwitnessed
producers. This narrow qualifier cannot combine with other representations and
permits no changed quantifiers, hypotheses, evaluator, or conclusion. The
syntactic checks and kernel witnesses do not prove cross-language equivalence;
the complete observer still requires manual HOL source comparison.

The pinned `HOL/src/monad/more_monads/state_transformerScript.sml` iteration counterpart is `Flapjack/Misc/StateTransformer.lean` (`FOR_def`).

`Flapjack/Misc/Words/Replicate.lean` is the `word_replicate_def` group counterpart of pinned `HOL/src/n-bit/wordsScript.sml`.

Pinned `HOL/src/list/src/numposrepScript.sml` digit conversion maps to `Flapjack/Misc/Numposrep.lean`; `HOL/src/string/ASCIInumbersScript.sml` character conversion maps to `Flapjack/Misc/ASCIInumbers.lean`; wordsScript `w2s_def`/`word_to_hex_string_def` map to `Flapjack/Misc/Words/Formatting.lean`.

The riscvScript MMU exception group counterpart is `Flapjack/RiscV/L3/Defs/MMU/Exception.lean`; `Nonempty` records HOL type variables intrinsic nonempty kind, as in the reviewed HD/EL/THE/LINV counterparts.

The primary counterpart of `cakeml/compiler/encoders/riscv/riscv_targetScript.sml`
is `Flapjack/Compiler/Encoders/RiscV/Target.lean`. Its native RISC-V instruction
carrier and Encode body are in the original L3 model counterpart under
`Flapjack/RiscV/L3/`; the exact assembly carrier is in
`Flapjack/Compiler/Encoders/Asm.lean`.
