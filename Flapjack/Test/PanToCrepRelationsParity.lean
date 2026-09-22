import Flapjack.Pancake.Proofs.PanToCrep

/-! Direct original Pancake HOL EVAL coverage for
`pan_to_crepProof$excp_rel` and `ctxt_fc`; outputs are committed in
`scripts/hol-probes/excp_rel_probe.out` and `ctxt_fc_probe.out`. -/

namespace Flapjack.Test.PanToCrepRelationsParity

open Flapjack

theorem emptyExceptionMapsRelated :
    excpRel (FEMPTY : FiniteMap String Nat)
      (FEMPTY : FiniteMap String Shape) := by
  constructor
  · funext exception
    simp [FDOM, FEMPTY]
  · intro exception exception' code code' hlookup
    simp [FLOOKUP, FEMPTY] at hlookup

theorem sameDomainSingletonMapsRelated :
    excpRel
      (FUPDATE FEMPTY ("E", 0) : FiniteMap String Nat)
      (FUPDATE FEMPTY ("E", Shape.one) : FiniteMap String Shape) := by
  constructor
  · funext exception
    simp [FDOM, FUPDATE, FEMPTY]
  · intro exception exception' code code' hlookup hlookup' _hcode
    simp [FLOOKUP, FUPDATE, FEMPTY] at hlookup hlookup'
    have hname : exception = "E" := hlookup.1.symm
    have hname' : exception' = "E" := hlookup'.1.symm
    exact hname.trans hname'.symm

theorem mismatchedExceptionDomainsNotRelated :
    ¬ excpRel
      (FUPDATE FEMPTY ("E", 0) : FiniteMap String Nat)
      (FUPDATE FEMPTY ("F", Shape.one) : FiniteMap String Shape) := by
  intro hrel
  have hdomain := congrFun hrel.1 "E"
  simp [FDOM, FUPDATE, FEMPTY] at hdomain

theorem nonInjectiveCompilerCodesNotRelated :
    ¬ excpRel
      (FUPDATE_LIST FEMPTY [("E", 0), ("F", 0)] : FiniteMap String Nat)
      (FUPDATE_LIST FEMPTY [("E", Shape.one), ("F", Shape.comb [])]
        : FiniteMap String Shape) := by
  intro hrel
  have hE : FLOOKUP
      (FUPDATE_LIST FEMPTY [("E", 0), ("F", 0)] : FiniteMap String Nat)
      "E" = some 0 := by simp [FLOOKUP, FUPDATE_LIST, FUPDATE]
  have hF : FLOOKUP
      (FUPDATE_LIST FEMPTY [("E", 0), ("F", 0)] : FiniteMap String Nat)
      "F" = some 0 := by simp [FLOOKUP, FUPDATE_LIST, FUPDATE]
  have hEq := hrel.2 "E" "F" 0 0 hE hF rfl
  have hne : "E" ≠ "F" := by decide
  exact hne hEq

def compilerFunctions : FiniteMap String (List (String × Shape) × Shape) :=
  FUPDATE FEMPTY ("f", ([], .one))

def exceptionCodes : FiniteMap String Nat := FUPDATE FEMPTY ("E", 3)

def shapedSlotsContext : PanToCrepProofContext Nat :=
  ctxtFc compilerFunctions exceptionCodes ["x", "pair"]
    [.one, .comb [.one, .one]] [0, 1, 2]

def shapedSlotsGuard : Bool :=
  (match FLOOKUP shapedSlotsContext.vars "x" with
    | some (.one, [0]) => true | _ => false) &&
  (match FLOOKUP shapedSlotsContext.vars "pair" with
    | some (.comb [.one, .one], [1, 2]) => true | _ => false) &&
  (match FLOOKUP shapedSlotsContext.funcs "f" with
    | some ([], .one) => true | _ => false) &&
  (match FLOOKUP shapedSlotsContext.eids "E" with
    | some 3 => true | _ => false) &&
  (shapedSlotsContext.vmax == 2)

def truncatedContext : PanToCrepProofContext Nat :=
  ctxtFc FEMPTY FEMPTY ["x", "ignored"] [.one] []

def zipTruncationGuard : Bool :=
  (match FLOOKUP truncatedContext.vars "x" with
    | some (.one, []) => true | _ => false) &&
  (match FLOOKUP truncatedContext.vars "ignored" with
    | none => true | _ => false) &&
  (truncatedContext.vmax == 0)

def emptyMaximumGuard : Bool :=
  (ctxtFc FEMPTY FEMPTY [] [] [] : PanToCrepProofContext Nat).vmax == 0

#guard shapedSlotsGuard
#guard zipTruncationGuard
#guard emptyMaximumGuard

def runChecks : IO Bool := do
  let checks := [
    ("excp_rel empty maps", true),
    ("excp_rel equal domains and injected codes", true),
    ("excp_rel rejects a domain mismatch", true),
    ("excp_rel rejects duplicate compiler codes", true),
    ("ctxt_fc slices shaped slots and preserves maps", shapedSlotsGuard),
    ("ctxt_fc preserves ZIP truncation", zipTruncationGuard),
    ("ctxt_fc empty MAX_LIST", emptyMaximumGuard)]
  for (name, passed) in checks do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
  pure (checks.all Prod.snd)

end Flapjack.Test.PanToCrepRelationsParity
