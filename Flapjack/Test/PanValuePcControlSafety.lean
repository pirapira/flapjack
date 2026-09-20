import Flapjack.PanToCrepCorrectnessBoundary

namespace Flapjack.Test.PanValuePcControlSafety

open Flapjack

def controlContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

/-! The primitive control leaves satisfy the exact top-level Cake label rule. -/
example : PanValueCrepProgramStateControlSafe (.break : Prog Nat) :=
  panValueCrepProgramStateControlSafe_break

example : PanValueCrepProgramStateControlSafe (.continue : Prog Nat) :=
  panValueCrepProgramStateControlSafe_continue

/-! Cake's `pc_compile_correct[Return]` has no loop-control label to transport;
the source-word return bridge makes that case explicit. -/
example
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect
        (.return (SourceWordExp.const (7 : Nat)).toExp) ∧
      PanValueCrepProgramStateControlSafe
        (.return (SourceWordExp.const (7 : Nat)).toExp) := by
  exact panValueCrepProgramStateCorrect_and_controlSafe_return_source_word
    (SourceWordExp.const 7) hbytesInWord hlookup

example :
    PanValueCrepProgramStateControlSafe
      (.seq (.break : Prog Nat) (.continue : Prog Nat)) := by
  exact panValueCrepProgramStateControlSafe_seq
    (.break : Prog Nat) (.continue : Prog Nat)
    panValueCrepProgramStateCorrect_break
    panValueCrepProgramStateControlSafe_break
    panValueCrepProgramStateControlSafe_continue

example (condition : SourceWordExp Nat) (thenBranch elseBranch : Prog Nat)
    (hthenSafe : PanValueCrepProgramStateControlSafe thenBranch)
    (helseSafe : PanValueCrepProgramStateControlSafe elseBranch)
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateControlSafe
      (.ite condition.toExp thenBranch elseBranch) :=
  panValueCrepProgramStateControlSafe_ite_source_word condition thenBranch
    elseBranch hthenSafe helseSafe hbytesInWord hlookup

/-! The conditional bridge carries evaluator correctness and the boundary
    control-label obligation together. -/
example (condition : SourceWordExp Nat)
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect
        (.ite condition.toExp (.break : Prog Nat) (.continue : Prog Nat)) ∧
      PanValueCrepProgramStateControlSafe
        (.ite condition.toExp (.break : Prog Nat) (.continue : Prog Nat)) := by
  exact panValueCrepProgramStateCorrect_and_controlSafe_ite_source_word
    condition (.break : Prog Nat) (.continue : Prog Nat)
    panValueCrepProgramStateCorrect_break
    panValueCrepProgramStateCorrect_continue
    panValueCrepProgramStateControlSafe_break
    panValueCrepProgramStateControlSafe_continue
    hbytesInWord hlookup

example (condition : SourceWordExp Nat) (body : Prog Nat)
    (hloopSafe : PanValueCrepProgramLoopStateControlSafe
      (.while condition.toExp body)) :
    PanValueCrepProgramStateControlSafe
      (.while condition.toExp body) :=
  panValueCrepProgramStateControlSafe_while_of_loop_safe condition body hloopSafe

example (body : Prog Nat) :
    PanValueCrepProgramLoopStateControlSafe
      (.while (SourceWordExp.const (0 : Nat)).toExp body) :=
  panValueCrepProgramLoopStateControlSafe_while_zero body

example (condition : SourceWordExp Nat) (body : Prog Nat)
    (hbody : PanValueCrepProgramStateCorrect body)
    (hbodySafe : PanValueCrepProgramLoopStateControlSafe body)
    (hloopSafe : PanValueCrepProgramLoopStateControlSafe
      (.while condition.toExp body))
    (hbytesInWord : ∀ (context : CompileContext Nat) (bytesInWord : Nat),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext Nat)
      (sourceLocals : VarName → Option (PanValue Nat))
      (name : VarName) (value : PanValue Nat),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramStateCorrect (.while condition.toExp body) ∧
      PanValueCrepProgramStateControlSafe (.while condition.toExp body) := by
  exact panValueCrepProgramStateCorrect_and_controlSafe_while_source_word
    condition body hbody hbodySafe hloopSafe hbytesInWord hlookup

/-! Nonzero labels remain rejected at the `pc_compile_correct` boundary. -/
example :
    ¬ panValuePcResultRel [] controlContext (fun _ _ _ => True) (fun _ => some 0)
        (fun _ _ => none)
        (.broke (fun _ => none) (fun _ => none) (fun _ => none))
        (.broke { locals := fun _ => none, memory := fun _ => none } 1) := by
  apply panValuePcResultRel_broke_rejects_nonzero_label
  decide

end Flapjack.Test.PanValuePcControlSafety
