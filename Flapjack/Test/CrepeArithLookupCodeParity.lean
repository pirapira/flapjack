import Flapjack.Pancake.Proofs.CrepArith

/-! Direct original-HOL boundary for the `lookup_code` helper used by
`crep_arithProofScript.sml:simp_prog_correct`. The HOL fixture simplifies an
8-bit multiplication in the stored function body before looking it up; the
Lean theorem below states that exact commute law over `lookupCrepHolCode`. -/

namespace Flapjack.Test.CrepeArithLookupCodeParity

open Flapjack

private abbrev Word8 := RiscV.Word 8

private def code : FunName → Option (List Nat × CrepProg Word8) :=
  FUPDATE FEMPTY ("f", ([1], .assign 2 (.crepOp .mul [.const 2, .const 4])))

private def arguments : List (PanWordLab Word8) := [.word 9]

private def simpCode := crepArithSimpCodeMap (BitVec.ofNat 8) code

example :
    lookupCrepHolCode simpCode "f" arguments 1 =
      (lookupCrepHolCode code "f" arguments 1).map
        (fun (body, locals) => (crepSimpProg (BitVec.ofNat 8) body, locals)) :=
  crepArithLookupCodeSimpProg (fromNat := BitVec.ofNat 8)
    code "f" arguments 1

/-- The HOL definition accepts `len` but does not inspect it. The exact lemma
    retains that quantified input, including values different from the
    parameter count. -/
example :
    lookupCrepHolCode simpCode "f" arguments 0 =
      (lookupCrepHolCode code "f" arguments 0).map
        (fun (body, locals) => (crepSimpProg (BitVec.ofNat 8) body, locals)) :=
  crepArithLookupCodeSimpProg (fromNat := BitVec.ofNat 8)
    code "f" arguments 0

/- HOL `simp_prog_after_lookup` in `crep_arith_lookup_code_probe.out` is
   `SOME (Assign 2 (Const 8w), FEMPTY⟨1 ↦ Word 9w⟩)`. -/
#guard match lookupCrepHolCode simpCode "f" arguments 1 with
  | some (body, locals) =>
      (match body with
       | .assign 2 (.const value) => value == BitVec.ofNat 8 8
       | _ => false) &&
      FLOOKUP locals 1 == some (.word (BitVec.ofNat 8 9))
  | none => false

#guard (lookupCrepHolCode simpCode "missing" [] 0).isNone

end Flapjack.Test.CrepeArithLookupCodeParity
