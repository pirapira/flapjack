import Flapjack.PanToCrepExceptionRelation

namespace Flapjack.Test.PanToCrepExceptionRelation

open Flapjack

def declarations : List (Decl Nat) :=
  [.exnDecl "E" .one,
   .decl .one "x" (.const 0),
   .exnDecl "F" (.comb [.one, .one])]

def actualCodes : InfoMap Nat :=
  [("E", 17), ("F", 23)]

/-! A concrete fixture for Cake's `get_eids_imp_excp_rel`: the target values
are deliberately different from the source numbering; only the domain is
shared, while the source table's values are injective. -/
example : panValuePcExceptionCodeRel
    (crepGetEidsFromDecls id declarations) actualCodes := by
  apply getEidsImpExcpRel id declarations actualCodes
  · intro left right hleft hright hcode
    simpa using hcode
  · simp [exceptionEntries, declarations]
  · intro exception
    by_cases hE : "E" = exception <;>
      by_cases hF : "F" = exception <;>
        simp [crepGetEidsFromDecls, pipelineExceptionCodes, lookupInfo,
          actualCodes, declarations, hE, hF]

def relationGuard : Bool :=
  let expected := crepGetEidsFromDecls id declarations
  (lookupInfo "E" expected).isSome &&
    (lookupInfo "F" expected).isSome &&
    (lookupInfo "G" expected).isSome == false

#eval relationGuard
#guard relationGuard

end Flapjack.Test.PanToCrepExceptionRelation
