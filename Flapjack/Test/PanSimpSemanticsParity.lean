import Flapjack.PanSimpSemantics

/-!
Focused regressions for the evaluator-level `pan_simp` sequence lemmas:
they are instantiated on concrete `Prog Nat` programs so that the statements
and hypotheses stay exercised.
-/

namespace Flapjack

/-- `Skip` itself evaluates to its input state with no returned values. -/
example :
    evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.skip : Prog Nat)
      = some ((fun _ => none), (fun _ => none), (fun _ => none),
          ([] : List (PanValue Nat))) := by
  simp [evalPanValueProgWithPrimitive]

/-- Appending `Skip` to a concrete program preserves its evaluation. -/
example :
    evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.seq (.tick : Prog Nat) (.skip : Prog Nat))
      = evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.tick : Prog Nat) :=
  evalPanValueProgWithPrimitive_seq_skip ([] : StructContext) (0 : Nat) 0 1
    (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
    (.tick : Prog Nat) none

/-- Prefixing `Skip` to a concrete program preserves its evaluation. -/
example :
    evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.seq (.skip : Prog Nat) (.tick : Prog Nat))
      = evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.tick : Prog Nat) :=
  evalPanValueProgWithPrimitive_skip_seq ([] : StructContext) (0 : Nat) 0 1
    (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
    (.tick : Prog Nat) none

/-- `smartSeq` evaluates like the explicit sequence it abbreviates. -/
example :
    evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (smartSeq (.skip : Prog Nat) (.tick : Prog Nat))
      = evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.seq (.skip : Prog Nat) (.tick : Prog Nat)) :=
  evalPanValueProgWithPrimitive_smartSeq ([] : StructContext) (0 : Nat) 0 1
    (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
    (.skip : Prog Nat) (.tick : Prog Nat) none

/-- Sequence associativity on concrete programs. -/
example :
    evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.seq (.seq (.tick : Prog Nat) (.skip : Prog Nat)) (.tick : Prog Nat))
      = evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.seq (.tick : Prog Nat) (.seq (.skip : Prog Nat) (.tick : Prog Nat))) :=
  evalPanValueProgWithPrimitive_seq_assoc ([] : StructContext) (0 : Nat) 0 1
    (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
    (.tick : Prog Nat) (.skip : Prog Nat) (.tick : Prog Nat) none

/-- Full `seqAssoc` correctness (CakeML `evaluate_seq_assoc`) on a concrete
    program, exercising the recursive `while` wrapper path. -/
example :
    evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (seqAssoc (.tick : Prog Nat) (.while (.const 1) (.tick : Prog Nat)))
      = evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.seq (.tick : Prog Nat) (.while (.const 1) (.tick : Prog Nat))) :=
  evalPanValueProgWithPrimitive_seqAssoc ([] : StructContext) (0 : Nat) 0 1
    (fun _ _ => none) none
    (.while (.const 1) (.tick : Prog Nat)) (.tick : Prog Nat)
    (fun _ => none) (fun _ => none) (fun _ => none)

end Flapjack