import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Call
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Install

/-!
# `word_to_wordProof` `compile_single_correct`: the induction

HOL proves `compile_single_correct` (`word_to_wordProofScript.sml:235-850`) by
`completeInduct_on` the state's `termdep`, then its `clock`, then `prog_size`,
dispatching each statement to its `Resume` case. `compileSingleCorrectAt_of_install`
performs that induction over every case piece, taking the `Install` case
(ported separately) as its only argument; the size measure is Lean's
structural `sizeOf`, used only for immediate sub-programs.
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm

/-- HOL's complete induction for `compile_single_correct`, given the `Install`
    case (Flapjack infrastructure; the assembled tagged theorem instantiates it). -/
theorem compileSingleCorrectAt_of_install {width : Nat} [NeZero width] {C F : Type}
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width)
    (hInstall : ∀ (ptr len dptr dlen : Nat) (cutsets : WordLangCutsetsHOL)
      (st : WordSemStateFiniteExact width C F),
      CompileSingleCorrectAt tt kk aa co (.install ptr len dptr dlen cutsets) st) :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F),
      CompileSingleCorrectAt tt kk aa co prog st := by
  suffices key : ∀ (d c n : Nat) (prog : WordLangProgHOL (BitVec width))
      (st : WordSemStateFiniteExact width C F),
      st.termdep = d → st.clock = c → sizeOf prog = n → CompileSingleCorrectAt tt kk aa co prog st from
    fun prog st => key _ _ _ prog st rfl rfl rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro prog st hd hc hn
  have lower : CompileSingleCorrectLowerIH tt kk aa co st := by
    intro p' st' h
    rcases h with h | ⟨h1, h2⟩
    · exact ihd _ (hd ▸ h) _ _ p' st' rfl rfl rfl
    · exact ihc _ (hc ▸ h2) _ p' st' (h1.trans hd) rfl rfl
  have sub : ∀ p' : WordLangProgHOL (BitVec width), sizeOf p' < sizeOf prog →
      CompileSingleCorrectSubIH tt kk aa co p' st := by
    intro p' hp st' h1 h2
    exact ihn _ (hn ▸ hp) p' st' (h1.trans hd) (h2.trans hc) rfl
  cases prog with
  | skip => exact compile_single_correct_Skip tt kk aa co st
  | move pri moves => exact compile_single_correct_Move tt kk aa co pri moves st
  | inst i => exact compile_single_correct_Inst tt kk aa co i st
  | assign v e => exact compile_single_correct_Assign tt kk aa co v e st
  | get v name => exact compile_single_correct_Get tt kk aa co v name st
  | set name e => exact compile_single_correct_Set tt kk aa co name e st
  | store e v => exact compile_single_correct_Store tt kk aa co e v st
  | mustTerminate p => exact compile_single_correct_MustTerminate tt kk aa co p st lower
  | call ret dest args handler => exact compile_single_correct_Call tt kk aa co ret dest args handler st lower
  | seq c1 c2 =>
    exact compile_single_correct_Seq tt kk aa co c1 c2 st lower (sub c1 (by simp; omega))
      (sub c2 (by simp; omega))
  | ite cmp r ri c1 c2 =>
    exact compile_single_correct_If tt kk aa co cmp r ri c1 c2 st (sub c1 (by simp; omega))
      (sub c2 (by simp; omega))
  | loop names body exitNames =>
    exact compile_single_correct_Loop tt kk aa co names body exitNames st lower (sub body (by simp; omega))
  | alloc v names => exact compile_single_correct_Alloc tt kk aa co v names st
  | storeConsts a b c d ws => exact compile_single_correct_StoreConsts tt kk aa co a b c d ws st
  | raise v => exact compile_single_correct_Raise tt kk aa co v st
  | «return» v vs => exact compile_single_correct_Return tt kk aa co v vs st
  | «break» v => exact compile_single_correct_Break tt kk aa co v st
  | «continue» v => exact compile_single_correct_Continue tt kk aa co v st
  | tick => exact compile_single_correct_Tick tt kk aa co st
  | opCurrHeap b dst src => exact compile_single_correct_OpCurrHeap tt kk aa co b dst src st
  | locValue r l => exact compile_single_correct_LocValue tt kk aa co r l st
  | install ptr len dptr dlen cutsets => exact hInstall ptr len dptr dlen cutsets st
  | codeBufferWrite a b => exact compile_single_correct_CodeBufferWrite tt kk aa co a b st
  | dataBufferWrite a b => exact compile_single_correct_DataBufferWrite tt kk aa co a b st
  | ffi f a b c d live => exact compile_single_correct_FFI tt kk aa co f a b c d live st
  | shareInst op v e => exact compile_single_correct_ShareInst tt kk aa co op v e st

namespace CompileSingleCorrectAssemblyCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorem of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompileSingleCorrectAssemblyCarrier

open Classical in
/-- HOL `compile_single_correct` (`word_to_wordProofScript.sml:235-850`): running a
    program on the code table compiled entry-wise by `compile_single`, with the
    compiled oracle and `compile`, reproduces every non-error source run from some
    permutation oracle, with related code tables and otherwise the same state.
    HOL's free `tt kk aa co` are the leading binders; `(I ## MAP f) o oracle` is
    `Prod.map id (List.map f) ∘ oracle`; `if res = SOME Error` is decided
    classically. Assembled by HOL's complete induction from the case pieces. -/
@[hol "cakeml/compiler/backend/proofs/word_to_wordProofScript.sml" "compile_single_correct"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compile_single_correct {width : Nat} [NeZero width] {C F : Type}
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width) :
    ∀ (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
      (l : Spt (Nat × WordLangProgHOL (BitVec width)))
      (coracle : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
      (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
        Option (List (BitVec 8) × List (BitVec width) × C)),
      codeRel st.code l ∧ sptDomain st.code = sptDomain l ∧
        st.compile = (fun conf progs => cc conf (progs.map (fun p => compileSingle tt kk aa co (p, none)))) ∧
        coracle = Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ st.compileOracle ∧
        Compiler.Backend.WordSimp.gcFunConstOk st.gcFun →
      ∃ perm' : Nat → Nat → Nat,
        let (res, rst) := evaluate prog { st with permute := perm' }
        if res = some .error then True
        else
          let (res1, rst1) := evaluate prog { st with code := l, compileOracle := coracle, compile := cc }
          res1 = res ∧ codeRel rst.code rst1.code ∧ sptDomain rst.code = sptDomain rst1.code ∧
            rst1 = { rst with
              code := rst1.code
              compileOracle :=
                Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ rst.compileOracle
              compile := cc } :=
  fun prog st => compileSingleCorrectAt_of_install tt kk aa co
    (compile_single_correct_Install tt kk aa co) prog st

end Flapjack.Compiler.Backend.WordToWord
