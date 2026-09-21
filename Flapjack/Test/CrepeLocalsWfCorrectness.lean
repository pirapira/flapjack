import Flapjack.CrepeStateRelation

namespace Flapjack.Test.CrepeLocalsWfCorrectness

open Flapjack

def context : CompileContext Nat :=
  { vars := [("x", (.one, [0]))], functions := [], exceptions := [],
    maxVar := 1, bytesInWord := 8 }

def sourceLocals : VarName → Option (PanValue Nat) :=
  fun name => if name == "x" then some (.word 3) else none

def crepLocals : Nat → Option Nat :=
  fun slot => if slot = 0 then some 3 else none

theorem related_locals_are_well_formed :
    panValueIsWf ([] : StructContext) (.word 3) = true := by
  apply panValueCrepLocalsRel_wf_shape_nil context sourceLocals crepLocals
    (fun name shape slots hlookup => by
      simp [context, lookupInfo] at hlookup
      rcases hlookup with ⟨rfl, rfl, rfl⟩
      simp [isWfShape])
    (by
      intro name value shape slots hsource hlookup
      simp [sourceLocals, context, lookupInfo] at hsource hlookup
      rcases hlookup with ⟨rfl, rfl, rfl⟩
      rcases hsource with ⟨_, rfl⟩
      simp [crepLocals, readCrepLocals, panValueShape, panShapeMatches,
        panValueFlatWords, panValueFlatWordsFuel])
    "x" (.word 3) (by simp [sourceLocals])
    (by
      refine ⟨.one, [0], ?_⟩
      simp [context, lookupInfo])

end Flapjack.Test.CrepeLocalsWfCorrectness
