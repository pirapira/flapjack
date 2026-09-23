import Flapjack.HolRef
import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Semantics.CrepRuntimeTarget

/-! Exact theorem counterpart for CakeML's `crep_arithProofScript.sml`.
    The statement specializes the source's `'a word crepLang$exp` to a
    width-parametric RISC-V word, and uses the production `crepDestConst`. -/

namespace Flapjack

/-- CakeML's `dest_const_thm`: a successful destination test identifies the
    expression as exactly that constant. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "dest_const_thm"]
theorem crepDestConst_eq_const {n : Nat} (expression : CrepExp (RiscV.Word n))
    (value : RiscV.Word n)
    (h : crepDestConst expression = some value) :
    expression = .const value := by
  cases expression <;> simp_all [crepDestConst]

/-! The following private BitVec arithmetic lemmas support the RISC-V
    specialization of HOL's destination facts. They are generic Lean helpers
    and have no declaration in the CakeML HOL development. -/

private theorem bitVec_even_shift_double {n : Nat} (word : BitVec n)
    (heven : word.toNat % 2 = 0) :
    word.toNat = 2 * (BitVec.ushiftRight word 1).toNat := by
  change word.toNat = 2 * (word.toNat >>> 1)
  rw [Nat.shiftRight_eq_div_pow]
  have h := Nat.mod_add_div word.toNat 2
  omega

private theorem one_lt_pow_two {n : Nat} [NeZero n] : 1 < 2 ^ n := by
  cases n with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ n => simp

private theorem bitVec_one_toNat {n : Nat} [NeZero n] :
    (1 : BitVec n).toNat = 1 := by
  change (BitVec.ofNat n 1).toNat = 1
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt one_lt_pow_two

private theorem bitVec_lowBit_zero_even {n : Nat} [NeZero n]
    (word : RiscV.Word n) (h : AndOp.and word 1 = 0) :
    word.toNat % 2 = 0 := by
  have ht := congrArg BitVec.toNat h
  change (word &&& (1 : BitVec n)).toNat = 0 at ht
  rw [BitVec.toNat_and] at ht
  rw [bitVec_one_toNat, Nat.and_one_is_mod] at ht
  exact ht

private theorem bitVec_even_shiftRight_one_double {n : Nat} [NeZero n]
    (word : RiscV.Word n) (heven : word.toNat % 2 = 0) :
    word.toNat = 2 * (ShiftRight.shiftRight word 1).toNat := by
  have hnat := bitVec_even_shift_double word heven
  have hshift : ShiftRight.shiftRight word (1 : RiscV.Word n) =
      BitVec.ushiftRight word 1 := by
    change BitVec.ushiftRight word (1 : RiscV.Word n).toNat =
      BitVec.ushiftRight word 1
    rw [bitVec_one_toNat]
  rw [hshift]
  exact hnat

private theorem crepDest2ExpFuel_sound {n : Nat} [NeZero n]
    (fuel start : Nat) (word : RiscV.Word n) (result : Nat)
    (h : crepDest2ExpFuel fuel start word = some result) :
    start ≤ result ∧ result - start < n ∧
      word.toNat = 2 ^ (result - start) % 2 ^ n := by
  induction fuel generalizing start word result with
  | zero => simp [crepDest2ExpFuel] at h
  | succ fuel ih =>
      simp only [crepDest2ExpFuel] at h
      split at h
      · contradiction
      · split at h
        · have heval : some start = some result := h
          have hr : result = start := by cases heval; rfl
          subst result
          have hw : word = 1 := by simpa using ‹(word == 1) = true›
          have hword : word.toNat = 1 := by
            rw [hw, bitVec_one_toNat]
          have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
          refine ⟨by omega, by omega, ?_⟩
          simp [hword, Nat.mod_eq_of_lt one_lt_pow_two]
        · split at h
          · contradiction
          · have hrec :
              crepDest2ExpFuel fuel (start + 1) (ShiftRight.shiftRight word 1) =
                  some result := h
            have hand : AndOp.and word 1 = 0 := by
              have hbit : (AndOp.and word 1 != 0) = false := by
                cases hb : (AndOp.and word 1 != 0) <;> simp_all
              simpa using hbit
            have ihResult := ih (start + 1) (ShiftRight.shiftRight word 1)
              result hrec
            obtain ⟨hstart, hwidth, hword⟩ := ihResult
            have hdouble := bitVec_even_shiftRight_one_double word
              (bitVec_lowBit_zero_even word hand)
            have hd : result - (start + 1) < n := hwidth
            have hdiff : result - start = result - (start + 1) + 1 := by omega
            have hmod : 2 ^ (result - (start + 1)) % 2 ^ n =
                2 ^ (result - (start + 1)) :=
              Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hd)
            have hlt : word.toNat < 2 ^ n := word.isLt
            rw [hdouble, hword, hmod] at hlt
            have hpowlt : 2 ^ (result - (start + 1) + 1) < 2 ^ n := by
              rw [Nat.pow_succ, Nat.mul_comm]
              exact hlt
            have hdlt : result - (start + 1) + 1 < n :=
              (Nat.pow_lt_pow_iff_right (by decide)).mp hpowlt
            refine ⟨by omega, by omega, ?_⟩
            calc
              word.toNat = 2 * (ShiftRight.shiftRight word 1).toNat := hdouble
              _ = 2 ^ (result - (start + 1) + 1) := by
                rw [hword, hmod, Nat.pow_succ]
                omega
              _ = 2 ^ (result - start) % 2 ^ n := by
                rw [hdiff, Nat.mod_eq_of_lt hpowlt]

/- CakeML's `dest_2exp_thm`: every successful exponent destination is the
   corresponding logical left shift of one. -/
@[hol "cakeml/pancake/crep_arithScript.sml" "dest_2exp_thm"]
theorem crepDest2Exp_eq_shift {n : Nat} [NeZero n] (word : RiscV.Word n)
    (exponent : Nat) (h : crepDest2Exp 0 word = some exponent) :
    word = BitVec.shiftLeft (1 : RiscV.Word n) exponent := by
  change crepDest2ExpFuel (n + 1) 0 word = some exponent at h
  have hs := crepDest2ExpFuel_sound (n + 1) 0 word exponent h
  obtain ⟨_, hbound, hword⟩ := hs
  have hbound : exponent < n := by simpa using hbound
  apply BitVec.eq_of_toNat_eq
  change word.toNat = (BitVec.shiftLeft (1 : RiscV.Word n) exponent).toNat
  rw [BitVec.shiftLeft_eq]
  rw [BitVec.toNat_shiftLeft]
  rw [bitVec_one_toNat]
  rw [Nat.mod_eq_of_lt (by
    have : 2 ^ exponent < 2 ^ n := Nat.pow_lt_pow_right (by decide) hbound
    simpa [Nat.shiftLeft_eq, Nat.one_mul] using this)]
  have hword' : word.toNat = 2 ^ exponent % 2 ^ n := by simpa using hword
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hbound)] at hword'
  simpa [Nat.shiftLeft_eq, Nat.one_mul] using hword'

/- CakeML's `dest_2exp_bound'`: a successful exponent destination is below
   the word width. -/
@[hol "cakeml/pancake/proofs/crep_arithProofScript.sml" "dest_2exp_bound'"]
theorem crepDest2Exp_lt_width {n : Nat} [NeZero n] (word : RiscV.Word n)
    (exponent : Nat) (h : crepDest2Exp 0 word = some exponent) :
    exponent < n := by
  change crepDest2ExpFuel (n + 1) 0 word = some exponent at h
  have hs := crepDest2ExpFuel_sound (n + 1) 0 word exponent h
  exact (by simpa using hs.2.1)

/-- Flapjack support lemma for HOL `eval_mul_const`, deliberately untagged.
    It proves preservation for production `evalCrepRuntimeExp` only after
    specializing values to `RiscV.Word n` and replacing the state's target
    operations with `riscvCrepWordTarget`. The HOL theorem instead quantifies
    over its polymorphic word type and arbitrary `crepSem` state; its evaluator
    is defined through HOL `eval_def` and `crep_op_def`/`word_sh`. No theorem
    currently relates those operations and every HOL state to this canonical
    production target. Width generality alone therefore does not establish the
    required evaluator correspondence or justify an `@[hol]` tag. -/
theorem crepEvalMulConst {n : Nat} [NeZero n] {σ : Type}
    (state : CrepRuntimeState (RiscV.Word n) σ)
    (expression : CrepExp (RiscV.Word n)) (constant value : RiscV.Word n)
    (h : (evalCrepRuntimeExp (riscvCrepWordTarget state) expression).map
        PanWordLab.word = some (.word value)) :
    (evalCrepRuntimeExp (riscvCrepWordTarget state)
        (crepMulConst (BitVec.ofNat n) expression constant)).map
      PanWordLab.word = some (.word (value * constant)) := by
  have hInjective : Function.Injective (PanWordLab.word : RiscV.Word n →
      PanWordLab (RiscV.Word n)) := by
    intro left right hEq
    cases hEq
    rfl
  have hRaw : evalCrepRuntimeExp (riscvCrepWordTarget state) expression =
      some value := by
    apply Option.map_injective hInjective
    simpa using h
  change Option.map PanWordLab.word
      (evalCrepRuntimeExp (riscvCrepWordTarget state)
        (crepMulConst (BitVec.ofNat n) expression constant)) =
    Option.map PanWordLab.word (some (value * constant))
  apply congrArg (Option.map PanWordLab.word)
  by_cases hzero : constant = (0 : RiscV.Word n)
  · simp [crepMulConst, hzero, evalCrepRuntimeExp]
  · by_cases hone : constant = (1 : RiscV.Word n)
    · simp [crepMulConst, hone, hRaw, NeZero.ne n]
    · have hzeroWord : constant ≠ (0 : RiscV.Word n) := by
        intro hz
        exact hzero hz
      have honeWord : constant ≠ (1 : RiscV.Word n) := by
        intro ho
        exact hone ho
      have hzeroCond : ¬((constant == 0) = true) := by
        intro hb
        have heq : constant = 0 := by simpa using hb
        exact hzeroWord heq
      have honeCond : ¬((constant == 1) = true) := by
        intro hb
        have heq : constant = 1 := by simpa using hb
        exact honeWord heq
      cases hdest : crepDest2Exp 0 constant with
      | none =>
          have hmul : crepMulConst (BitVec.ofNat n) expression constant =
              .crepOp .mul [expression, .const constant] := by
            unfold crepMulConst
            simp only [if_neg hzeroCond, if_neg honeCond, hdest]
          rw [hmul]
          simp [evalCrepRuntimeExp, hRaw]
      | some exponent =>
          have hbound : exponent < n :=
            crepDest2Exp_lt_width constant exponent hdest
          have hpower : constant = BitVec.twoPow n exponent := by
            simpa [BitVec.twoPow, BitVec.shiftLeft_eq] using
              crepDest2Exp_eq_shift constant exponent hdest
          have hfromNat : (BitVec.ofNat n exponent).toNat = exponent := by
            rw [BitVec.toNat_ofNat]
            apply Nat.mod_eq_of_lt
            exact Nat.lt_trans (Nat.lt_two_pow_self (n := exponent))
              (Nat.pow_lt_pow_right (by decide) hbound)
          have hmulShift : value <<< exponent = value * constant := by
            calc
              value <<< exponent = value * BitVec.twoPow n exponent :=
                BitVec.shiftLeft_eq_mul_twoPow value exponent
              _ = value * constant := by rw [← hpower]
          have hshift :
              RiscV.panRiscVShift .lsl value (BitVec.ofNat n exponent) =
                some (value * constant) := by
            unfold RiscV.panRiscVShift
            rw [hfromNat]
            simp only [if_pos hbound]
            simp [hmulShift]
          have hmul : crepMulConst (BitVec.ofNat n) expression constant =
              .shift .lsl expression (.const (BitVec.ofNat n exponent)) := by
            unfold crepMulConst
            simp only [if_neg hzeroCond, if_neg honeCond, hdest]
          rw [hmul]
          simp only [evalCrepRuntimeExp]
          rw [hRaw]
          simp [riscvCrepWordTarget, RiscV.panRiscVMemoryModel, hshift]

/-- Flapjack representation of HOL's local `mapc f` state update: apply `f`
    to each present code-map entry and leave every other runtime field alone. -/
def crepArithMapCode {n : Nat} (f : (List Nat × CrepProg (RiscV.Word n)) →
    (List Nat × CrepProg (RiscV.Word n))) (state : CrepRuntimeState (RiscV.Word n) σ) :
    CrepRuntimeState (RiscV.Word n) σ :=
  { state with code := fun name => (state.code name).map f }

/-! Internal evaluator lemma: `evalCrepRuntimeExp` reads locals, globals,
    memory, and target operations but never the code map. This supports the
    HOL-local `mapc f` step and is infrastructure rather than a HOL theorem. -/
private theorem crepEvalCodeMapIrrel {n : Nat} [NeZero n] {σ : Type}
    (f : (List Nat × CrepProg (RiscV.Word n)) → (List Nat × CrepProg (RiscV.Word n)))
    (state : CrepRuntimeState (RiscV.Word n) σ) (expression : CrepExp (RiscV.Word n)) :
    evalCrepRuntimeExp (riscvCrepWordTarget (crepArithMapCode f state)) expression =
      evalCrepRuntimeExp (riscvCrepWordTarget state) expression := by
  have evalExpsMapM (targetState : CrepRuntimeState (RiscV.Word n) σ) :
      ∀ expressions,
        evalCrepRuntimeExps (riscvCrepWordTarget targetState) expressions =
          expressions.mapM (evalCrepRuntimeExp (riscvCrepWordTarget targetState)) := by
    intro expressions
    induction expressions with
    | nil => simp [evalCrepRuntimeExps]
    | cons head tail ih => simp [evalCrepRuntimeExps, ih]
  induction expression using
      (CrepExp.rec (motive_2 := fun expressions =>
        ∀ (state : CrepRuntimeState (RiscV.Word n) σ)
          (f : List Nat × CrepProg (RiscV.Word n) → List Nat × CrepProg (RiscV.Word n)),
          (∀ e, e ∈ expressions →
            evalCrepRuntimeExp (riscvCrepWordTarget (crepArithMapCode f state)) e =
              evalCrepRuntimeExp (riscvCrepWordTarget state) e) ∧
          evalCrepRuntimeExps (riscvCrepWordTarget (crepArithMapCode f state)) expressions =
            evalCrepRuntimeExps (riscvCrepWordTarget state) expressions))
      generalizing state f <;>
    all_goals try simp_all [crepArithMapCode, riscvCrepWordTarget, evalCrepRuntimeExp,
      evalCrepRuntimeExps, crepRuntimeLoad, crepRuntimeLoad32, crepRuntimeLoadByte]
  case op operator expressions ih =>
    have hArgs := ih state f |>.2
    have hArgs' :
        List.mapM (evalCrepRuntimeExp
          (riscvCrepWordTarget (crepArithMapCode f state))) expressions =
        List.mapM (evalCrepRuntimeExp (riscvCrepWordTarget state)) expressions := by
      calc
        _ = evalCrepRuntimeExps (riscvCrepWordTarget (crepArithMapCode f state)) expressions :=
          (evalExpsMapM (crepArithMapCode f state) expressions).symm
        _ = _ := hArgs
    simpa [riscvCrepWordTarget, crepArithMapCode] using
      congrArg (fun values => values.bind
        (fun words => RiscV.panRiscVMemoryModel.wordOp operator words)) hArgs'
  case crepOp operator expressions ih =>
    cases operator
    cases expressions with
    | nil => simp [evalCrepRuntimeExp]
    | cons left rest =>
      cases rest with
      | nil => simp [evalCrepRuntimeExp]
      | cons right rest =>
        cases rest with
        | nil =>
          simp only [evalCrepRuntimeExp]
          rw [ih state f |>.1 left (by simp)]
          rw [ih state f |>.1 right (by simp)]
        | cons _ _ => simp [evalCrepRuntimeExp]


end Flapjack
