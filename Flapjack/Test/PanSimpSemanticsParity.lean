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

/-- CakeML `eval_seq_assoc_eq_evaluate`: `seqAssoc Skip` preserves evaluation
    on a concrete program. -/
example :
    evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (seqAssoc (.skip : Prog Nat) (.tick : Prog Nat))
      = evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.tick : Prog Nat) :=
  evalPanValueProgWithPrimitive_seqAssoc_skip ([] : StructContext) (0 : Nat) 0 1
    (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
    (.tick : Prog Nat) none

/-- CakeML `evaluate_seq_no_error_fst`: a successful sequence evaluation
    exposes a successful first-component evaluation. -/
example
    (h : evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.seq (.tick : Prog Nat) (.tick : Prog Nat))
      = some ((fun _ => none), (fun _ => none), (fun _ => none),
          ([] : List (PanValue Nat)))) :
    ∃ firstResult, evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.tick : Prog Nat) = some firstResult :=
  evalPanValueProgWithPrimitive_seq_some_fst ([] : StructContext) (0 : Nat) 0 1
    (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
    (.tick : Prog Nat) (.tick : Prog Nat) none _ h

/-- CakeML `ret_to_tail_correct` (structured fragment): the tail-call rewrite
    preserves evaluation on a concrete program. -/
example :
    evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (retToTail (.tick : Prog Nat))
      = evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.tick : Prog Nat) :=
  evalPanValueProgWithPrimitive_retToTail ([] : StructContext) (0 : Nat) 0 1
    (fun _ _ => none) none (.tick : Prog Nat)
    (fun _ => none) (fun _ => none) (fun _ => none)

/-- CakeML `evaluate_seq_call_ret_eq` (structured fragment): the tail-call
    recognition rewrite preserves evaluation. -/
example :
    evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (seqCallRet (.tick : Prog Nat))
      = evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.tick : Prog Nat) :=
  evalPanValueProgWithPrimitive_seqCallRet ([] : StructContext) (0 : Nat) 0 1
    (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
    (.tick : Prog Nat) none

/-- CakeML `evaluate_seq_simp` (structured fragment): the full `pan_simp`
    program transformation preserves evaluation on a concrete program. -/
example :
    evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (panSimpProg (.seq (.tick : Prog Nat) (.tick : Prog Nat)))
      = evalPanValueProgWithPrimitive ([] : StructContext) (0 : Nat) 0 1
        (fun _ => none) (fun _ => none) (fun _ => none) (fun _ _ => none)
        (.seq (.tick : Prog Nat) (.tick : Prog Nat)) :=
  evalPanValueProgWithPrimitive_panSimpProg ([] : StructContext) (0 : Nat) 0 1
    (fun _ _ => none) none (.seq (.tick : Prog Nat) (.tick : Prog Nat))
    (fun _ => none) (fun _ => none) (fun _ => none)

/-- The `seqAssoc` syntactic size bound instantiates on a small program. -/
example :
    progSize (seqAssoc (.skip : Prog Nat) (.seq (.tick : Prog Nat) (.tick : Prog Nat))) ≤
      progSize (.skip : Prog Nat) + 4 * progSize (.seq (.tick : Prog Nat) (.tick : Prog Nat)) :=
  progSize_seqAssoc_le _ _

/-- Every program has a positive structural size, which supplies the missing
    lower bound for budget composition (`progSize_pos`). -/
example : 1 ≤ progSize (.while (.const 1) (.seq (.tick : Prog Nat) (.tick : Prog Nat))) :=
  progSize_pos _

/-- The call-aware budget reserves a uniform callee allowance at a `Call`. -/
example :
    progCallFuel 5 (.call none "f" ([] : List (Exp Nat)) : Prog Nat) = 1 + 5 := by
  simp [progCallFuel]

/-- The call-aware budget dominates the plain structural size on a calling program. -/
example :
    progSize (.decCall "x" .one "f" [] (.tick : Prog Nat) : Prog Nat) ≤
      progCallFuel 5 (.decCall "x" .one "f" [] (.tick : Prog Nat) : Prog Nat) :=
  progSize_le_progCallFuel 5 _

/-- The declaration-table pass preserves the exception identifiers reachable
    from function bodies (source-side companion of Cake's `get_eids`). -/
private def demoSimpDecls : List (Decl Nat) :=
  [Decl.function { name := "f", inline := false, exported := false, params := [], body := .raise "E" (.const 0), returnShape := .one },
   Decl.exnDecl "E" .one]

example :
    declarationExceptionIds (panSimpDecls demoSimpDecls) =
      declarationExceptionIds demoSimpDecls :=
  declarationExceptionIds_panSimpDecls demoSimpDecls

#check @declarationExceptionIds_panSimpDecls

/-- The function projection of the declaration table is the flat map of
    `expIds` over the function bodies (the list Cake's `get_eids` numbers). -/
private def demoFunDecl : FunDecl Nat :=
  { name := "f", inline := false, exported := false, params := [], body := .raise "E" (.const 0), returnShape := .one }

example :
    declarationExceptionIds ([demoFunDecl].map (fun function => Decl.function function)) =
      [demoFunDecl].flatMap (fun function => expIds function.body) :=
  declarationExceptionIds_map_function _

#check @declarationExceptionIds_map_function

end Flapjack
