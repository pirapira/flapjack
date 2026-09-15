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

/-- Drop every fact whose variable or whose comparison operands are written by
the given statement.  A fact records that a variable holds the truth of
`condition = right`, so it survives only while both the variable and the
operands keep their values. -/
def wordConditionFactInvalidate (facts : List (WordConditionFact α))
    (written : List Nat) : List (WordConditionFact α) :=
  facts.filter (fun fact =>
    !(written.contains fact.name) &&
      !(written.contains fact.condition) &&
      (match fact.right with
       | .imm _ => true
       | .reg register => !(written.contains register)))

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

/-! The source `word_simp$simp_duplicate_if` hoists a second conditional over
    the short sequence between it and a preceding boolean definition.  The
    `crep_to_loop` shape is particularly regular: a comparison writes 1/0 to
    its left operand, a copy carries that result to a temporary, and a
    `!= 0` conditional consumes it.  Rebuild that as one conditional and put
    the two constant-result writes in the corresponding branches. -/
def wordSimpleStatement : WordProg α → Bool
  | .skip | .tick | .move _ _ | .assign _ _ => true
  | _ => false

def wordFindBooleanTest [BEq α] [OfNat α 0] [OfNat α 1] :
    Nat → Nat → List (WordProg α) →
      Option (List (WordProg α) × Nat × WordProg α × WordProg α ×
        List (WordProg α))
  | 0, _, _ => none
  | fuel + 1, condition, statements =>
      match statements with
      | .assign temporary (.var source) :: statement :: rest =>
          if source == condition then
            match statement with
            | .ite .notEqual tested (.imm _) thenBranch elseBranch =>
                if tested == temporary then
                  some ([], temporary, thenBranch, elseBranch, rest)
                else none
            | _ =>
                if wordSimpleStatement statement then
                  match wordFindBooleanTest fuel condition (statement :: rest) with
                  | some (intermediate, temporary, thenBranch, elseBranch, rest) =>
                      some (.assign temporary (.var source) :: intermediate,
                        temporary, thenBranch, elseBranch, rest)
                  | none => none
                else none
          else none
      | statement :: rest =>
          if wordSimpleStatement statement then
            match wordFindBooleanTest fuel condition rest with
            | some (intermediate, temporary, thenBranch, elseBranch, rest) =>
                some (statement :: intermediate, temporary, thenBranch, elseBranch, rest)
            | none => none
          else none
      | [] => none
def wordMergeBooleanIfs [BEq α] [OfNat α 0] [OfNat α 1] :
    Nat → List (WordProg α) → List (WordProg α)
  | 0, statements => statements
  | _fuel + 1, [] => []
  | fuel + 1, statement :: rest =>
      let recurse := wordMergeBooleanIfs fuel
      match statement with
      | .loop liveIn body liveOut =>
          .loop liveIn
              (wordListToProg (recurse (wordProgToList body))) liveOut ::
            recurse rest
      | .ite operator condition right thenBranch elseBranch =>
          let then' := wordListToProg (recurse (wordProgToList thenBranch))
          let else' := wordListToProg (recurse (wordProgToList elseBranch))
          match wordBooleanDefinition? statement with
          | some defined =>
              if defined == condition then
                match wordFindBooleanTest fuel condition rest with
                | some (intermediate, temporary, testThen, testElse, remaining) =>
                    let thenTest := wordListToProg
                      (recurse (wordProgToList testThen))
                    let elseTest := wordListToProg
                      (recurse (wordProgToList testElse))
                    let mergedThen := wordListToProg
                      ([then'] ++ intermediate ++
                        [.assign temporary (.const (1 : α)), thenTest])
                    let mergedElse := wordListToProg
                      ([else'] ++ intermediate ++
                        [.assign temporary (.const (0 : α)), elseTest])
                    .ite operator condition right mergedThen mergedElse ::
                      recurse remaining
                | none => statement :: recurse rest
              else statement :: recurse rest
          | none => statement :: recurse rest
      | other => other :: recurse rest
  termination_by fuel => fuel

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
          | .loop liveIn body liveOut =>
              let body' := wordListToProg
                (wordFuseConditionsAux fuel [] (wordProgToList body))
              .loop liveIn body' liveOut ::
                wordFuseConditionsAux fuel facts rest
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
              let facts' := wordConditionFactInvalidate facts
                (wordProgWriteVars statement)
              let facts'' :=
                match wordConditionFactLookup facts' source with
                | some fact => wordConditionFactSet facts' name (some fact)
                | none => facts'
              .assign name (.var source) ::
                wordFuseConditionsAux fuel facts'' rest
          | .ite operator condition right thenBranch elseBranch =>
              let then' := wordListToProg
                (wordFuseConditionsAux fuel facts (wordProgToList thenBranch))
              let else' := wordListToProg
                (wordFuseConditionsAux fuel facts (wordProgToList elseBranch))
              let written := wordProgWriteVars statement
              let facts' := wordConditionFactInvalidate facts written
              let facts'' :=
                match wordBooleanDefinition? statement with
                | some name =>
                  let operandsSafe :=
                      match right with
                      | .imm _ => true
                      | .reg register => !(written.contains register)
                    if operandsSafe then
                      wordConditionFactSet facts' name
                        (some { name := name, operator := operator,
                                condition := condition, right := right })
                    else facts'
                | none => facts'
              .ite operator condition right then' else' ::
                wordFuseConditionsAux fuel facts'' rest
          | other =>
              let facts' := wordConditionFactInvalidate facts
                (wordProgWriteVars other)
              other :: wordFuseConditionsAux fuel facts' rest

/-- Fuse materialized comparison round trips in a Word program.  The fuel
bounds the number of recursive visits through the sequence spine and the
conditional branches; if the bound is exhausted the program is returned
unchanged, so the pass is always sound. -/
def wordFuseConditions [BEq α] [OfNat α 0] [OfNat α 1]
    (program : WordProg α) : WordProg α :=
  let merged := wordListToProg
    (wordMergeBooleanIfs (wordProgFuel program + 1) (wordProgToList program))
  wordListToProg
    (wordFuseConditionsAux (wordProgFuel merged + 1) [] (wordProgToList merged))

end Flapjack.RiscV
