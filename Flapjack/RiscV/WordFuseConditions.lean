import Flapjack.RiscV.Allocator

/-!
`Flapjack.CrepToLoop` lowers a control-flow condition by materializing the
relation into a fresh temporary (`ite operator condition right (assign t 1)
(assign t 0)`) and then testing that temporary (`ite notEqual u (imm 0) ...`).
The original CakeML pipeline collapses this round trip before emission.  This
module performs the collapse at the Word boundary: it tracks which variables
provably hold the 0/1 result of a comparison and, when such a variable is
tested against zero and is dead afterwards, replaces the test with the
original comparison.  The rewrite is semantics preserving because the tracked
variable is dead; it is intended to run before `wordProgDCE`, which then
removes the now unused copy and definition.
-/

namespace Flapjack.RiscV

open Flapjack

/-- A variable known to hold the 0/1 result of a comparison. -/
structure WordConditionFact (α : Type u) where
  name : Nat
  operator : Cmp
  condition : Nat
  right : WordRegImm α
  deriving Repr

def wordConditionFactLookup [BEq α] (facts : List (WordConditionFact α))
    (name : Nat) : Option (WordConditionFact α) :=
  facts.find? (fun fact => fact.name == name)

def wordConditionFactSet (facts : List (WordConditionFact α)) (name : Nat)
    (value : Option (WordConditionFact α)) : List (WordConditionFact α) :=
  let cleared := facts.filter (fun fact => fact.name != name)
  match value with
  | some fact => { fact with name := name } :: cleared
  | none => cleared

/-- Split a program into its top-level statements. -/
def wordProgToList : WordProg α → List (WordProg α)
  | .seq first second => wordProgToList first ++ wordProgToList second
  | other => [other]

/-- Rebuild a right-nested sequence from a statement list. -/
def wordListToProg : List (WordProg α) → WordProg α
  | [] => .skip
  | [single] => single
  | first :: rest => .seq first (wordListToProg rest)

/-- A size measure for the shapes the fusion pass recurses through. -/
def wordProgFuel : WordProg α → Nat
  | .seq first second => 1 + wordProgFuel first + wordProgFuel second
  | .ite _ _ _ thenBranch elseBranch =>
      1 + wordProgFuel thenBranch + wordProgFuel elseBranch
  | _ => 1

/-- Recognise `ite _ _ _ (assign t 1) (assign t 0)`, which defines the 0/1
result of a comparison in `t`. -/
def wordBooleanDefinition? [BEq α] [OfNat α 0] [OfNat α 1] :
    WordProg α → Option Nat
  | .ite _ _ _ (.assign thenName (.const thenValue))
      (.assign elseName (.const elseValue)) =>
      if thenName == elseName && thenValue == (1 : α) && elseValue == (0 : α) then
        some thenName
      else none
  | _ => none

def wordFuseConditionsAux [BEq α] [OfNat α 0] [OfNat α 1]
      (fuel : Nat) (facts : List (WordConditionFact α))
      (statements : List (WordProg α)) : List (WordProg α) :=
    match fuel with
    | 0 => statements
    | fuel + 1 =>
      match statements with
      | [] => []
      | statement :: rest =>
          match statement with
          | .ite .notEqual name (.imm _) thenBranch elseBranch =>
              let then' := wordListToProg
                (wordFuseConditionsAux fuel facts (wordProgToList thenBranch))
              let else' := wordListToProg
                (wordFuseConditionsAux fuel facts (wordProgToList elseBranch))
              match wordConditionFactLookup facts name with
              | some fact =>
                  let dead :=
                    !(wordProgVariables then').contains name &&
                      !(wordProgVariables else').contains name &&
                      !(wordProgVariables (wordListToProg rest)).contains name
                  let rest' := wordFuseConditionsAux fuel
                    (wordConditionFactSet facts name none) rest
                  if dead then
                    .ite fact.operator fact.condition fact.right then' else' :: rest'
                  else
                    .ite .notEqual name (.imm 0) then' else' :: rest'
              | none =>
                  .ite .notEqual name (.imm 0) then' else' ::
                    wordFuseConditionsAux fuel
                      (wordConditionFactSet facts name none) rest
          | .assign name (.var source) =>
              .assign name (.var source) ::
                wordFuseConditionsAux fuel
                  (wordConditionFactSet facts name (wordConditionFactLookup facts source))
                  rest
          | .ite operator condition right thenBranch elseBranch =>
              let then' := wordListToProg
                (wordFuseConditionsAux fuel facts (wordProgToList thenBranch))
              let else' := wordListToProg
                (wordFuseConditionsAux fuel facts (wordProgToList elseBranch))
              let facts' := match wordBooleanDefinition? statement with
                | some name =>
                    wordConditionFactSet facts name
                      (some { name := name, operator := operator,
                              condition := condition, right := right })
                | none =>
                    (wordProgWriteVars statement).foldl
                      (fun facts name => wordConditionFactSet facts name none) facts
              .ite operator condition right then' else' ::
                wordFuseConditionsAux fuel facts' rest
          | other =>
              let facts' := (wordProgWriteVars other).foldl
                (fun facts name => wordConditionFactSet facts name none) facts
              other :: wordFuseConditionsAux fuel facts' rest

/-- Fuse materialized comparison round trips in a Word program.  The fuel
bounds the number of recursive visits through the sequence spine and the
conditional branches; if the bound is exhausted the program is returned
unchanged, so the pass is always sound. -/
def wordFuseConditions [BEq α] [OfNat α 0] [OfNat α 1]
    (program : WordProg α) : WordProg α :=
  wordListToProg
    (wordFuseConditionsAux (wordProgFuel program + 1) [] (wordProgToList program))

end Flapjack.RiscV
