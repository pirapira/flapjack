import Flapjack.Compiler.Backend.StackToLab.Proofs.MakeInit
import Flapjack.Compiler.Backend.StackToLab.Compile
import Flapjack.Compiler.Backend.StackAlloc.Proofs.MakeInit
import Flapjack.Compiler.Backend.StackNames.Proofs.MakeInit
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitAny
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitFfi
import Flapjack.Compiler.Backend.StackProps.EvaluateConsts

/-! `full_make_init_def` and `full_make_init_buffer`/`_ffi`/`_compile`
(`stack_to_labProofScript.sml:3056`): the StackSem initial state of the
whole stack-to-lab pipeline, built from the LabSem state by the four
`make_init` stages in reverse pass order, and its buffer, FFI and compile
fields. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- Genuine canonical roundtrip for the imported actual state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness

/-- HOL `full_make_init_def`. The local overloads `stack_alloc_compile`,
`stack_remove_compile` and `stack_names_compile` are the tagged pass
compilers; `I ## f ## I` is `Prod.map id (Prod.map f id)`; the four
`make_init`s are, in order of application, stack_to_lab's, stack_names',
stack_remove's `make_init_any`/`make_init_opt` and stack_alloc's. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
noncomputable def fullMakeInit {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (s4 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) :
    StackSemStateFiniteExact width C F × Option (StackSemStateFiniteExact width C F) :=
  let ggc := StackToLab.isGenGc dataConf.gcKind
  let jump := stackConf.jump
  let code1 := StackAlloc.compile dataConf (StackRawCall.compile code)
  let code2 := StackRemove.compileHOL jump offset ggc maxHeap sp BvlToBvi.initGlobalsLocation
    code1
  let code3 := sptFromAList (StackNames.compileHOL stackConf.regNames code2)
  let coracle1 := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ coracle
  let coracle2 := Prod.map id (Prod.map (List.map (StackRemove.progComp jump offset sp)) id) ∘
    coracle1
  let coracle3 := Prod.map id (Prod.map (StackNames.compileHOL stackConf.regNames) id) ∘
    coracle2
  let s3 := MakeInit.makeInit code3 coracle3
    ([2, 3, 4].map (StackNames.findNameSpt stackConf.regNames)) saveRegs s4
  let s2 := StackNames.makeInit stackConf.regNames (sptFromAList code2) coracle2 s3
  let s1 := StackRemove.Proofs.InitMake.makeInitAny ggc maxHeap bitmaps dataSp coracle1 jump
    offset sp (sptFromAList code1) s2
  (StackAlloc.makeInit dataConf (sptFromAList code) coracle s1,
   StackRemove.Proofs.InitMake.makeInitOpt ggc maxHeap bitmaps dataSp coracle1 jump offset sp
     (sptFromAList code1) s2)

/-- Buffers, FFI and compile callback of stack_remove's total initialized
state (Flapjack infrastructure for the three field theorems below; HOL
unfolds `make_init_any_def`/`make_init_opt_def` in each proof). -/
theorem makeInitAnyFields {width : Nat} [NeZero width] {C F : Type}
    (ggc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    let t := StackRemove.Proofs.InitMake.makeInitAny ggc maxHeap bitmaps dataSpace oracle jump
      bounds pointer code s
    t.codeBuffer.buffer = [] ∧ t.dataBuffer.buffer = [] ∧
      t.compile = fun config program =>
        s.compile config (program.map (StackRemove.progComp jump bounds pointer)) := by
  intro t
  unfold t StackRemove.Proofs.InitMake.makeInitAny
  cases h : StackRemove.Proofs.InitMake.makeInitOpt ggc maxHeap bitmaps dataSpace oracle jump
    bounds pointer code s with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some t' =>
    simp only
    obtain ⟨post, rfl, hp⟩ := StackRemove.Proofs.InitAny.makeInitOpt_eq_some h
    rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc, hd, -⟩
    refine ⟨hc, hd, ?_⟩
    unfold StackRemove.Proofs.InitMake.makeInitOpt at h
    rcases run : StackSemEvaluate.evaluate
      (StackRemove.initCode ggc maxHeap pointer, s) with ⟨r, post'⟩
    rw [run] at h
    rcases r with _ | r
    · simp only at h
      split at h
      · simp only [Option.some.injEq] at h
        rw [← h]
        have := (StackProps.evaluateConsts _ _ _ _ run).2.2.2.2.2.2.2
        simp [StackRemove.Proofs.InitReduce.initReduce, this]
      · cases h
    · cases h

/-- HOL `full_make_init_buffer`: both buffers of the initial state are
empty. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_buffer"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem fullMakeInitBuffer {width : Nat} [NeZero width] {C F : Type}
    (a : StackToLab.Config) (b : DataToWord.Config) (c d : Nat)
    (e : BitVec width × BitVec width) (f : List (BitVec width))
    (g : List (Nat × HolProg width)) (h : Flapjack.Compiler.Backend.LabSem.State width C F)
    (i : Nat → Bool) (j : Nat)
    (k : Nat → C × List (Nat × HolProg width) × List (BitVec width)) :
    ((fullMakeInit a b c d e f g h i j k).1 : StackSemStateFiniteExact width C F).codeBuffer.buffer =
        [] ∧
      (fullMakeInit a b c d e f g h i j k).1.dataBuffer.buffer = [] := by
  have := makeInitAnyFields (C := C) (F := F) (StackToLab.isGenGc b.gcKind) c f j
    (Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ k) a.jump e d
    (sptFromAList (StackAlloc.compile b (StackRawCall.compile g)))
    (StackNames.makeInit a.regNames
      (sptFromAList (StackRemove.compileHOL a.jump e (StackToLab.isGenGc b.gcKind) c d
        BvlToBvi.initGlobalsLocation (StackAlloc.compile b (StackRawCall.compile g))))
      (Prod.map id (Prod.map (List.map (StackRemove.progComp a.jump e d)) id) ∘
        (Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ k))
      (MakeInit.makeInit
        (sptFromAList (StackNames.compileHOL a.regNames
          (StackRemove.compileHOL a.jump e (StackToLab.isGenGc b.gcKind) c d
            BvlToBvi.initGlobalsLocation (StackAlloc.compile b (StackRawCall.compile g)))))
        (Prod.map id (Prod.map (StackNames.compileHOL a.regNames) id) ∘
          (Prod.map id (Prod.map (List.map (StackRemove.progComp a.jump e d)) id) ∘
            (Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ k)))
        ([2, 3, 4].map (StackNames.findNameSpt a.regNames)) i h))
  exact ⟨this.1, this.2.1⟩

/-- HOL `full_make_init_ffi`: the initial state keeps the LabSem FFI state. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_ffi"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem fullMakeInitFfi {width : Nat} [NeZero width] {C F : Type}
    (a : StackToLab.Config) (b : DataToWord.Config) (c d : Nat)
    (e : BitVec width × BitVec width) (f : List (BitVec width))
    (g : List (Nat × HolProg width)) (h : Flapjack.Compiler.Backend.LabSem.State width C F)
    (i : Nat → Bool) (j : Nat)
    (k : Nat → C × List (Nat × HolProg width) × List (BitVec width)) :
    ((fullMakeInit a b c d e f g h i j k).1 : StackSemStateFiniteExact width C F).ffi = h.ffi := by
  simp only [fullMakeInit, StackAlloc.makeInit, StackRemove.Proofs.InitFfi.makeInitAnyFfi,
    StackNames.makeInit, MakeInit.makeInit]

/-- HOL `full_make_init_compile`: the compile callback of the initial state
runs the stack_alloc, stack_remove and stack_names program transformations and
`prog_to_section` before the LabSem compiler. -/
@[hol "cakeml/compiler/backend/proofs/stack_to_labProofScript.sml" "full_make_init_compile"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem fullMakeInitCompile {width : Nat} [NeZero width] {C F : Type}
    (a : StackToLab.Config) (b : DataToWord.Config) (c d : Nat)
    (e : BitVec width × BitVec width) (f : List (BitVec width))
    (g : List (Nat × HolProg width)) (h : Flapjack.Compiler.Backend.LabSem.State width C F)
    (i : Nat → Bool) (j : Nat)
    (k : Nat → C × List (Nat × HolProg width) × List (BitVec width)) :
    ((fullMakeInit a b c d e f g h i j k).1 : StackSemStateFiniteExact width C F).compile =
      fun cfg => (fun p => h.compile cfg ((((p.map (StackRemove.progComp a.jump e d)).map
        (StackNames.progCompEntryHOL a.regNames)).map progToSectionHOL))) ∘
        List.map StackAlloc.progComp := by
  simp only [fullMakeInit, StackAlloc.makeInit, (makeInitAnyFields ..).2.2,
    StackNames.makeInit, MakeInit.makeInit, StackNames.compileHOL]
  rfl

end Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
