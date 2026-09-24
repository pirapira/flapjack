import Flapjack.Pancake.Proofs.CrepArith

/-! Direct original-HOL boundary for the local `lookup_code` theorem used by
`crep_arithProofScript.sml:simp_prog_correct`. The HOL fixture simplifies an
8-bit multiplication in the stored function body before looking it up. The
width-indexed Lean theorem states the source `FMAP_MAP2`/`OPTION_MAP` commute
law over `lookupCrepHolCodeW`; the generic helper remains untagged support. -/

namespace Flapjack.Test.CrepeArithLookupCodeParity

open Flapjack

private abbrev Word8 := RiscV.Word 8

private def code : FunName → Option (List Nat × CrepProg Word8) :=
  FUPDATE FEMPTY ("f", ([1], .assign 2 (.crepOp .mul [.const 2, .const 4])))

private def arguments : List (PanWordLab Word8) := [.word 9]

private def simpCode := crepArithSimpCodeMap (BitVec.ofNat 8) code

private def wrongArityCode : FunName → Option (List Nat × CrepProg Word8) :=
  FUPDATE FEMPTY ("f", ([1, 2], .skip))

private def duplicateParameterCode : FunName → Option (List Nat × CrepProg Word8) :=
  FUPDATE FEMPTY ("f", ([1, 1], .skip))

example :
    lookupCrepHolCode simpCode "f" arguments 1 =
      (lookupCrepHolCode code "f" arguments 1).map
        (fun (body, locals) => (crepSimpProg (BitVec.ofNat 8) body, locals)) :=
  crepArithLookupCodeSimpProg (fromNat := BitVec.ofNat 8)
    code "f" arguments 1

example :
    lookupCrepHolCodeW simpCode "f" arguments 1 =
      (lookupCrepHolCodeW code "f" arguments 1).map
        (fun (body, locals) => (crepSimpProg (BitVec.ofNat 8) body, locals)) :=
  crepArithLookupCodeSimpProgW code "f" arguments 1

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

#guard match lookupCrepHolCodeW simpCode "f" arguments 1 with
  | some (body, locals) =>
      (match body with
       | .assign 2 (.const value) => value == BitVec.ofNat 8 8
       | _ => false) &&
      FLOOKUP locals 1 == some (.word (BitVec.ofNat 8 9))
  | none => false

/- The production call lookup is definitionally routed through the same
   HOL-shaped lookup helper; the checked oracle row above is the direct HOL
   successful lookup observation. -/
#guard match lookupCrepRuntimeCode "f" [BitVec.ofNat 8 9] simpCode with
  | some (body, locals) =>
      (match body with
       | .assign 2 (.const value) => value == BitVec.ofNat 8 8
       | _ => false) &&
      FLOOKUP locals 1 == some (.word (BitVec.ofNat 8 9))
  | none => false

#guard (lookupCrepRuntimeCode "f" [BitVec.ofNat 8 9] wrongArityCode).isNone
#guard (lookupCrepRuntimeCode "f"
  [BitVec.ofNat 8 9, BitVec.ofNat 8 10] duplicateParameterCode).isNone
#guard (lookupCrepRuntimeCode "missing" [] code).isNone

#guard (lookupCrepHolCode simpCode "missing" [] 0).isNone

end Flapjack.Test.CrepeArithLookupCodeParity
