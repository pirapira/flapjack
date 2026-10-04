import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Alloc
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Call
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Clock
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CodeBufferWrite
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Control
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.DataBufferWrite
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.FFI
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Flat
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Get
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.If
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Install
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.LocValue
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Loop
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.MoveFull
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.OpCurrHeap
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Raise
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Return
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Set
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.ShareInst
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.StoreConsts

import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Inst

namespace Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

namespace AssemblyCodec

/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

end AssemblyCodec

/-- Full original comp_correct5756, with the entire induction motive5719-5751.
All original source execution, nonerror, relation, allocation/flatness, actual
compilation, bitmap bounds/prefix, label-subset and max-variable guards are
retained. Every one of the 26 rebound evaluate_ind clauses is discharged by
its actual complete constructor theorem. The Inst clause uses the whole
proved primitive simulation; no case callback, induction hypothesis, desired
postrelation or target execution is supplied to this theorem.
The result factoring compCorrectResult is the transparent entire original
extra-clock/result-dependent relation/resource conclusion, including mismatch
Halt2/trace-prefix/overflow, normal returns, exception restoration and residual
FFI/clock branches. Canonical finite maps and the common positive machine
word dimension are qualified. The evaluator closure inherits
reals_as_rational_cuts (SOUNDNESS item8); this structural assembly does not
establish a new numerical FP agreement or whole compiler refinement. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "comp_correct" 5756
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrect {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) :
    ∀ (program : WordLangProgHOL (BitVec width))
      (source : WordSemStateFiniteExact width (Nat × C) F),
  ∀ (k f frame : Nat)
    (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat),
    (WordSemStateFiniteExact.evaluate program source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      compNative ac false program (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k) →
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  change ∀ program source, Seq.Simulation ac program source
  apply WordSemStateFiniteExact.evaluate_ind (fun p s => Seq.Simulation ac p s)
  refine ⟨?skip, ?alloc, ?storeConsts, ?move, ?inst, ?assign, ?get, ?set, ?opCurrHeap, ?store,
    ?tick, ?mustTerminate, ?seq, ?ret, ?raise, ?brk, ?cont, ?ite, ?loop, ?locValue, ?install,
    ?codeBufferWrite, ?dataBufferWrite, ?ffi, ?shareInst, ?call⟩
  case skip => exact fun s k f frame _ _ _ _ _ _ _ _ _ h => compCorrectSkip ac k f frame s _ _ _ _ _ _ _ _ _ h
  case alloc => exact fun n names s k f frame _ _ _ _ _ _ _ _ _ h =>
    Alloc.compCorrectAlloc ac n names k f frame s _ _ _ _ _ _ _ _ _ h
  case storeConsts => exact fun t1 t2 a o w s => StoreConsts.compCorrectStoreConsts ac t1 t2 a o w s
  case move => exact fun pri moves s => MoveFull.compCorrectMove ac pri moves s
  case inst => exact fun i s => Inst.compCorrectInst ac i s
  case assign => exact fun v e s k f frame _ _ _ _ _ _ _ _ _ h =>
    Flat.compCorrectAssign ac v e k f frame s _ _ _ _ _ _ _ _ _ h
  case get => exact fun v name s => Get.compCorrectGet ac v name s
  case set => exact fun v e s => Set.compCorrectSet ac v e s
  case opCurrHeap => exact fun b d src s => OpCurrHeap.compCorrectOpCurrHeap ac b d src s
  case store => exact fun e v s k f frame _ _ _ _ _ _ _ _ _ h =>
    Flat.compCorrectStore ac e v k f frame s _ _ _ _ _ _ _ _ _ h
  case tick => exact fun s k f frame _ _ _ _ _ _ _ _ _ h => Clock.compCorrectTick ac k f frame s _ _ _ _ _ _ _ _ _ h
  case mustTerminate => exact fun p s _ k f frame _ _ _ _ _ _ _ _ _ h =>
    Clock.compCorrectMustTerminate ac p k f frame s _ _ _ _ _ _ _ _ _ h
  case seq => exact fun c1 c2 s ih => Seq.compCorrectSeq ac c1 c2 s ih
  case ret => exact fun n ms s => Return.compCorrectReturn ac n ms s
  case raise => exact fun n s => Raise.compCorrectRaise ac n s
  case brk => exact fun l s k f frame _ _ _ _ _ _ _ _ _ h => compCorrectBreak ac l k f frame s _ _ _ _ _ _ _ _ _ h
  case cont => exact fun l s k f frame _ _ _ _ _ _ _ _ _ h => compCorrectContinue ac l k f frame s _ _ _ _ _ _ _ _ _ h
  case ite => exact fun cmp r ri c1 c2 s ih => If.compCorrectIf ac cmp r ri c1 c2 s ih
  case loop => exact fun names c exitNames s ih => Loop.compCorrectLoop ac names exitNames c s ih
  case locValue => exact fun r l s => LocValue.compCorrectLocValue ac r l s
  case install => exact fun p l dp dl names s => Install.compCorrectInstall ac p l dp dl names s
  case codeBufferWrite => exact fun r1 r2 s => CodeBufferWrite.compCorrectCodeBufferWrite ac r1 r2 s
  case dataBufferWrite => exact fun r1 r2 s => DataBufferWrite.compCorrectDataBufferWrite ac r1 r2 s
  case ffi => exact fun i p1 l1 p2 l2 names s k f frame _ _ _ _ _ _ _ _ _ h =>
    FFI.compCorrectFFI ac i p1 l1 p2 l2 names k f frame s _ _ _ _ _ _ _ _ _ h
  case shareInst => exact fun op v e s => ShareInst.compCorrectShareInst ac op v e s
  case call => exact fun ret dest args handler s ih => Call.compCorrectCall ac ret dest args handler s ih


end Flapjack.WordToStackProofs.CompCorrect
