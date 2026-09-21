import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.CrepeProgramWordInduction

/-!
Regression coverage for the assembled stateful source-to-Crep induction.
The example has nested sequencing and a return boundary, so it exercises both
the recursive proof and the explicit source/compiled state relation.
-/

namespace Flapjack.Test.CrepeProgramInduction

open Flapjack

/-! The word-program induction now admits ordinary calls through the same
relation-premised state-correctness constructor used by the Pancake call
case. -/
#check @StatefulWordProg.callWord
#check @StatefulWordProg.decWord
#check @panValueCrepProgramStateCorrect_statefulWord

def compactExample : Prog Nat :=
  .seq (.return (.const 7))
    (.seq .tick (.annot "regression" "stateful"))

def arbitraryRaise : Prog Nat :=
  .raise "E" (.rStruct [.const 3, .const 5, .const 8])

example : StatefulCompactProg Nat compactExample := by
  exact .seq (.returnConst 7) (.seq .tick (.annot "regression" "stateful"))

example : PanValueCrepProgramStateCorrect compactExample := by
  exact panValueCrepProgramStateCorrect_statefulCompact compactExample
    (.seq (.returnConst 7) (.seq .tick (.annot "regression" "stateful")))

example : PanValueCrepProgramCorrect compactExample := by
  exact panValueCrepProgramCorrect_statefulCompact compactExample
    (.seq (.returnConst 7) (.seq .tick (.annot "regression" "stateful")))

example (hraiseState : PanValueCrepProgramStateCorrect arbitraryRaise)
    (hraisePlain : PanValueCrepProgramCorrect arbitraryRaise) :
    StatefulCompactProg Nat arbitraryRaise := by
  exact .raiseWithEvidence "E" (.rStruct [.const 3, .const 5, .const 8])
    hraiseState hraisePlain

example (hraiseState : PanValueCrepProgramStateCorrect arbitraryRaise)
    (hraisePlain : PanValueCrepProgramCorrect arbitraryRaise) :
    PanValueCrepProgramStateCorrect arbitraryRaise := by
  exact panValueCrepProgramStateCorrect_statefulCompact arbitraryRaise
    (.raiseWithEvidence "E" (.rStruct [.const 3, .const 5, .const 8])
      hraiseState hraisePlain)

example (hraiseState : PanValueCrepProgramStateCorrect arbitraryRaise)
    (hraisePlain : PanValueCrepProgramCorrect arbitraryRaise) :
    PanValueCrepProgramCorrect arbitraryRaise := by
  exact panValueCrepProgramCorrect_statefulCompact arbitraryRaise
    (.raiseWithEvidence "E" (.rStruct [.const 3, .const 5, .const 8])
      hraiseState hraisePlain)

example : PanValueCrepProgramStateControlSafe compactExample := by
  exact panValueCrepProgramStateControlSafe_statefulCompact compactExample
    (.seq (.returnConst 7) (.seq .tick (.annot "regression" "stateful")))

example : PanValueCrepProgramStateCorrect compactExample ∧
    PanValueCrepProgramStateControlSafe compactExample := by
  exact panValueCrepProgramStateCorrect_and_controlSafe_statefulCompact
    compactExample
    (.seq (.returnConst 7) (.seq .tick (.annot "regression" "stateful")))

/-! The composed return theorem is exercised independently of the inductive
fragment, with a continuation that would change control if it were run. -/
example : PanValueCrepProgramStateCorrect
    (.seq (.return (.const (11 : Nat))) (.tick : Prog Nat)) := by
  exact panValueCrepProgramStateCorrect_seq_return_const 11 .tick
    panValueCrepProgramStateCorrect_tick

example (locals : Nat → Option Nat) (names : List Nat) (values : List Nat)
    (hread : readCrepLocals locals names = some values) :
    values.length = names.length := by
  exact readCrepLocals_length locals names values hread

example (structs : StructContext) (context : CompileContext Nat)
    (sourceLocals : VarName → Option (PanValue Nat))
    (crepLocals : Nat → Option Nat) (name : VarName)
    (value : PanValue Nat) (shape : Shape) (slots : List Nat)
    (hrel : panValueCrepLocalsRel structs context sourceLocals crepLocals)
    (hsource : sourceLocals name = some value)
    (hlookup : lookupInfo name context.vars = some (shape, slots)) :
    panShapeMatches (panValueShape structs value) shape = true ∧
      slots.length = (panValueFlatWords value).length ∧
      readCrepLocals crepLocals slots = some (panValueFlatWords value) := by
  exact panValueCrepLocalsRel_lookup_evidence structs context sourceLocals
    crepLocals name value shape slots hrel hsource hlookup

example (structs : StructContext) (context : CompileContext Nat)
    (sourceLocals sourceGlobals : VarName → Option (PanValue Nat))
    (sourceMemory : Nat → Option (PanValue Nat)) (crepState : CrepState Nat)
    (address value : Nat)
    (hrel : panValueCrepStateRel structs context sourceLocals sourceGlobals
      sourceMemory crepState)
    (hmemory : sourceMemory address = some (.word value)) :
    crepState.memory address = some value := by
  exact panValueCrepStateRel_memory_lookup structs context sourceLocals
    sourceGlobals sourceMemory crepState address value hrel hmemory

end Flapjack.Test.CrepeProgramInduction
