import Flapjack.CrepeExpressionRelation

namespace Flapjack

/-! Regression for the locality domain used by the source-to-Crep proof. -/

theorem localise_dec_return_is_localised :
    localisedProg
      (Parser.localiseProg []
        (.dec "x" .one (.const (7 : Nat))
          (.return (.var .global "x"))) : Prog Nat) := by
  simp [Parser.localiseProg, Parser.localiseExp, Parser.localiseKind,
    localisedProg, localisedExp, expGlobalVars]

theorem global_assignment_is_outside_correctness_domain :
    ¬ localisedProg (.assign .global "x" (.const (7 : Nat)) : Prog Nat) := by
  simp [localisedProg]

/-! Cake's `localised_exp_shape_val` (`pan_globalsProofScript.sml:3207`). -/

theorem localisedExp_shapeVal_fixture :
    localisedExp (shapeVal (α := Nat) (.comb [.one, .named "n"])) :=
  localisedExp_shapeVal _

theorem localisedExp_shapeVals_fixture :
    ∀ expression ∈ shapeVals (α := Nat) [.one, .comb [.one]],
      localisedExp expression := by
  intro expression hmem
  exact localisedExp_shapeVals _ expression hmem

def shapeValLocalisedGuard : Bool :=
  (shapeVals (α := Nat) [.one, .comb [.one]]).all
    (fun expression => expGlobalVars expression == [])

#eval shapeValLocalisedGuard
#guard shapeValLocalisedGuard

/-! Cake's `compile_exp_localised` (`pan_globalsProofScript.sml:3196`). -/

def compileContext : GlobalPassContext Nat :=
  { globals := [("g", (Shape.one, 4))]
    globalsSize := 4
    maxGlobalsSize := 8
    bytesInWord := 8
    fromNat := fun n => n }

theorem globalCompileExp_localised_fixture :
    localisedExp (globalCompileExp compileContext (.var .global "g")) :=
  globalCompileExp_localised compileContext (.var .global "g")

theorem globalCompileExps_expGlobalVars_fixture :
    expGlobalVars.expGlobalVarsList
      (globalCompileExp.globalCompileExps compileContext
        [.var .global "g", .topAddr]) = [] :=
  globalCompileExps_expGlobalVars compileContext [.var .global "g", .topAddr]

def globalCompileExpLocalisedGuard : Bool :=
  (expGlobalVars (globalCompileExp compileContext (.var .global "g")) == []) &&
    (expGlobalVars (globalCompileExp compileContext .topAddr) == [])

#eval globalCompileExpLocalisedGuard
#guard globalCompileExpLocalisedGuard

theorem globalShapeVal_localised_fixture :
    localisedExp (globalShapeVal compileContext (.comb [.one, .named "n"])) :=
  globalShapeVal_localised compileContext (.comb [.one, .named "n"])

theorem nestedSeq_localised_fixture :
    localisedProg
      (nestedSeq ([.skip, .annot "t" "x"] : List (Prog Nat))) :=
  (nestedSeq_localised ([.skip, .annot "t" "x"] : List (Prog Nat))).mpr
    (by intro statement hmem; simp at hmem; rcases hmem with rfl | rfl <;>
      simp [localisedProg])

def nestedSeqLocalisedGuard : Bool :=
  (expGlobalVars (globalShapeVal compileContext (.comb [.one])) == [])

#eval nestedSeqLocalisedGuard
#guard nestedSeqLocalisedGuard


theorem globalCompileProg_localised_fixture :
    localisedProg
      (globalCompileProg compileContext
        (.seq .skip (.dec "x" .one (.const 1) .skip))) :=
  globalCompileProg_localised compileContext _

def globalCompileProgLocalisedGuard : Bool :=
  expGlobalVars (globalCompileExp compileContext (.var .global "g")) == []

#eval globalCompileProgLocalisedGuard
#guard globalCompileProgLocalisedGuard


end Flapjack
