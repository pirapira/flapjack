import Flapjack.Compiler.Backend.WordToWord.Proofs.CodeRel
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateConst
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateConsts
import Flapjack.Compiler.Backend.WordSimp.Proofs.ConstFpLemmas

/-!
# `word_to_wordProof` `compile_single_correct`: the replaced-code frame

Flapjack infrastructure for `compile_single_correct`
(`word_to_wordProofScript.sml:235-850`): its statement runs a program on the
source state and on the state with the compiled code table, compile oracle and
`compile` function. Every leaf statement (no sub-program, no `Install`) reads
the code table only through its domain, so the two runs agree up to these three
fields, which HOL discharges by rewriting with `state_component_equality`.
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm

section Frame

variable {width : Nat} [NeZero width] {C F : Type}

/-- The state with the code table, compile oracle and `compile` replaced, as in
    the second run of HOL `compile_single_correct` (Flapjack infrastructure). -/
def tgtState (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (o : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C))
    (s : WordSemStateFiniteExact width C F) : WordSemStateFiniteExact width C F :=
  { s with code := l, compileOracle := o, compile := cc }

/-- The leaf statements of `compile_single_correct`: no sub-program and no
    `Install` (Flapjack infrastructure). -/
def cscLeaf {α : Type} : WordLangProgHOL α → Bool
  | .mustTerminate _ | .call _ _ _ _ | .seq _ _ | .ite _ _ _ _ _ | .loop _ _ _
  | .install _ _ _ _ _ => false
  | _ => true

theorem jumpExc_tgt (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (o : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C))
    (s : WordSemStateFiniteExact width C F) :
    jumpExc (tgtState l o cc s) = (jumpExc s).map (Prod.map (tgtState l o cc) id) := by
  unfold jumpExc
  have hh : (tgtState l o cc s).handler = s.handler := rfl
  have hs : (tgtState l o cc s).stack = s.stack := rfl
  by_cases h : s.handler < s.stack.length
  · simp only [hh, hs, h, if_true]
    split <;> rfl
  · simp only [hh, hs, h, if_false, Option.map_none]

set_option linter.unusedSimpArgs false in
/-- A leaf statement runs the same on the replaced-code state, provided the two
    code tables have the same domain. -/
theorem evaluate_tgt_frame (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (o : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C))
    (s : WordSemStateFiniteExact width C F) (hdom : ∀ n, sptMem n l = sptMem n s.code)
    (p : WordLangProgHOL (BitVec width)) (hp : cscLeaf p = true) :
    evaluate p (tgtState l o cc s) = ((evaluate p s).1, tgtState l o cc (evaluate p s).2) := by
  have hI : InstFrame (tgtState l o cc : WordSemStateFiniteExact width C F → _) := by
    constructor <;> intros <;> simp only [tgtState] <;> constConj_tac
  have hA : AllocFrame (tgtState l o cc : WordSemStateFiniteExact width C F → _) := by
    constructor <;> intros <;> simp only [tgtState] <;> constConj_tac
  have hS : ShMemFrame (tgtState l o cc : WordSemStateFiniteExact width C F → _) := by
    constructor <;> intros <;> simp only [tgtState] <;> constConj_tac
  have gv : ∀ x (t : WordSemStateFiniteExact width C F), getVar x (tgtState l o cc t) = getVar x t :=
    fun _ _ => rfl
  have gvs : ∀ xs (t : WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.getVars xs (tgtState l o cc t) = WordSemStateFiniteExact.getVars xs t :=
    fun xs t => (getVars_congr (tgtState l o cc t) t rfl xs).symm
  have wE : ∀ e (t : WordSemStateFiniteExact width C F), wordExp (tgtState l o cc t) e = wordExp t e :=
    fun e t => (wordExp_congr (tgtState l o cc t) t rfl rfl rfl rfl e).symm
  have hi := fun i (t : WordSemStateFiniteExact width C F) => (inst_frame hI i t).symm
  have ha := fun w n (t : WordSemStateFiniteExact width C F) => (alloc_frame hA w n t).symm
  have hsh := fun op v ad (t : WordSemStateFiniteExact width C F) =>
    (shareInst_frame (rw := width) hS op v ad t).symm
  cases p <;> simp only [cscLeaf, Bool.false_eq_true] at hp <;>
    rw [evaluate, evaluate] <;>
    (try simp only [gv, gvs, wE, hi, ha, hsh, hdom, hI.memStore, jumpExc_tgt]) <;>
    (repeat' split) <;>
    first
      | rfl
      | simp_all [tgtState, flushState, setVar, setVars, setStore, unsetVar, getStore,
          decClock, getFpVar, Option.map_eq_none_iff, Option.map_eq_some_iff]

end Frame

end Flapjack.Compiler.Backend.WordToWord
