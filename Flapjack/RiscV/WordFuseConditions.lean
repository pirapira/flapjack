import Flapjack.RiscV.Allocator
import Flapjack.RiscV.WordSimp

/-!
`Flapjack.CrepToLoop` lowers a control-flow condition by materializing the
relation into a fresh temporary (`ite operator condition right (assign t 1)
(assign t 0)`) and then testing that temporary (`ite notEqual u (imm 0) ...`).
The original CakeML pipeline collapses this round trip before emission.  This
module performs the collapse at the Word boundary: it tracks which variables
provably hold the 0/1 result of a comparison and, when such a variable is
tested against zero and is dead afterwards, replaces the test with the
original comparison.  The rewrite is semantics preserving because the tracked
  variable is dead; the later Cake-style dead-code cleanup removes the now
  unused copy and definition after full SSA has assigned names consistently.
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

/-- Transfer comparison facts across Cake's parallel `Move` carrier.  All
destinations are invalidated before looking up sources, while the lookups use
the pre-move fact set; this preserves the source semantics for a parallel
move whose source is also a destination. -/
def wordConditionFactMove [BEq α] (facts : List (WordConditionFact α))
    (moves : List (Nat × Nat)) : List (WordConditionFact α) :=
  let destinations := moves.map Prod.fst
  let remaining := wordConditionFactInvalidate facts destinations
  moves.foldl
    (fun current (destination, source) =>
      match wordConditionFactLookup remaining source with
      | some fact => wordConditionFactSet current destination (some fact)
      | none => wordConditionFactSet current destination none)
    remaining

/-- Split a program into its top-level statements. -/
def wordProgToList : WordProg α → List (WordProg α)
  | .seq first second => wordProgToList first ++ wordProgToList second
  | other => [other]

/-! `word_simp` starts with Cake's `Seq_assoc`, which removes `Skip` at
    sequence boundaries before inspecting a materialized condition.  The
    source lowering can retain the same harmless wrappers inside an `Ite`
    branch, so normalize the sequence spine when recognizing such branches.
    This intentionally does not rewrite any other instruction. -/
def wordProgStripSeqSkips : WordProg α → WordProg α
  | .seq first second =>
      let first := wordProgStripSeqSkips first
      let second := wordProgStripSeqSkips second
      match first, second with
      | .skip, second => second
      | first, .skip => first
      | first, second => .seq first second
  | program => program

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
  | .ite _ _ _ thenBranch elseBranch =>
      let thenBranch := wordProgStripSeqSkips thenBranch
      let elseBranch := wordProgStripSeqSkips elseBranch
      match thenBranch, elseBranch with
      | .assign thenName (.const thenValue),
          .assign elseName (.const elseValue) =>
          if thenName == elseName && thenValue == (1 : α) && elseValue == (0 : α) then
            some thenName
          else none
      | _, _ => none
  | _ => none

/-! Cake's `word_simp$simp_duplicate_if` duplicates a short straight-line
    continuation after a 0/1 comparison materialisation.  This is the shape
    emitted by `crep_to_loop` for `while`: the comparison writes its left
    temporary to 1/0, a short sequence copies that result, and a following
    `NotEqual ... 0` selects the loop body or break.  Duplicating only the
    source's simple statements is safe and exposes the direct branch that
    `word_to_stack` consumes. -/
def wordConditionDefinition? [BEq α] [OfNat α 0] [OfNat α 1] :
    WordProg α → Option (Cmp × Nat × WordRegImm α × WordProg α × WordProg α)
  | .ite operator condition right thenBranch elseBranch =>
      let thenBranch := wordProgStripSeqSkips thenBranch
      let elseBranch := wordProgStripSeqSkips elseBranch
      match wordBooleanDefinition? (.ite operator condition right thenBranch elseBranch) with
      | some _ => some (operator, condition, right, thenBranch, elseBranch)
      | none => none
  | _ => none

def wordConditionPrefixSafe : WordProg α → Bool
  | .skip | .tick | .move _ _ | .assign _ _ => true
  | _ => false

def wordConditionHasAlias (condition test : Nat) : List (WordProg α) → Bool
  | [] => condition == test
  | statement :: statements =>
      match statement with
      | .assign name (.var source) =>
          (name == test && source == condition) ||
            wordConditionHasAlias condition test statements
      | .move _ moves =>
          moves.any (fun move => move.1 == test && move.2 == condition) ||
            wordConditionHasAlias condition test statements
      | _ => wordConditionHasAlias condition test statements

def wordConditionTest? (condition : Nat) (before : List (WordProg α)) :
    List (WordProg α) → Option (List (WordProg α) × WordProg α × WordProg α ×
      List (WordProg α))
  | [] => none
  | statement :: statements =>
      match statement with
      | .ite .notEqual test (.imm _) thenBranch elseBranch =>
          if wordConditionHasAlias condition test before then
            some (before, thenBranch, elseBranch, statements)
          else none
      | _ =>
          if wordConditionPrefixSafe statement &&
              !((wordProgWriteVars statement).contains condition) then
            wordConditionTest? condition (before ++ [statement]) statements
          else none

def wordDuplicateConditionsAux [BEq α] [OfNat α 0] [OfNat α 1]
    (fuel : Nat) (normalize : WordProg α → WordProg α)
    (statements : List (WordProg α)) : List (WordProg α) :=
  match fuel with
  | 0 => statements
  | fuel + 1 =>
      match statements with
      | [] => []
      | statement :: rest =>
          match wordConditionDefinition? statement with
          | some (operator, condition, right, thenDefinition, elseDefinition) =>
              match wordConditionTest? condition [] rest with
              | some (before, thenBranch, elseBranch, remaining) =>
                  let thenBody := normalize (wordListToProg
                    (wordDuplicateConditionsAux fuel normalize
                      (wordProgToList thenDefinition ++ before ++
                        wordProgToList thenBranch)))
                  let elseBody := normalize (wordListToProg
                    (wordDuplicateConditionsAux fuel normalize
                      (wordProgToList elseDefinition ++ before ++
                        wordProgToList elseBranch)))
                  .ite operator condition right thenBody elseBody ::
                    wordDuplicateConditionsAux fuel normalize remaining
              | none =>
                  statement :: wordDuplicateConditionsAux fuel normalize rest
          | none =>
              match statement with
              | .loop liveIn body liveOut =>
                  let body' := wordListToProg
                    (wordDuplicateConditionsAux fuel normalize (wordProgToList body))
                  .loop liveIn body' liveOut ::
                    wordDuplicateConditionsAux fuel normalize rest
              | _ => statement :: wordDuplicateConditionsAux fuel normalize rest

def wordDuplicateConditions [BEq α] [OfNat α 0] [OfNat α 1]
    (program : WordProg α) : WordProg α :=
  wordListToProg
    (wordDuplicateConditionsAux (wordProgFuel program + 1) id (wordProgToList program))

def wordDuplicateConditionsWithFold [Add α] [Sub α] [AndOp α] [OrOp α]
    [HXor α α α] [Complement α] [DecidableEq α] [WordSimpShift α]
    [BEq α] [OfNat α 0] [OfNat α 1]
    (program : WordProg α) : WordProg α :=
  wordListToProg
    (wordDuplicateConditionsAux (wordProgFuel program + 1) wordConstFp
      (wordProgToList program))

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
              let facts' := wordConditionFactInvalidate facts
                (wordProgWriteVars statement)
              let facts'' :=
                match wordConditionFactLookup facts' source with
                | some fact => wordConditionFactSet facts' name (some fact)
                | none => facts'
              .assign name (.var source) ::
                wordFuseConditionsAux fuel facts'' rest
          | .move priority moves =>
              let facts' := wordConditionFactMove facts moves
              .move priority moves ::
                wordFuseConditionsAux fuel facts' rest
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
                      !(written.contains condition) &&
                        (match right with
                         | .imm _ => true
                         | .reg register => !(written.contains register))
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
  let duplicated := wordDuplicateConditions program
  wordListToProg
    (wordFuseConditionsAux (wordProgFuel duplicated + 1) []
      (wordProgToList duplicated))

def wordFuseConditionsWithFold [Add α] [Sub α] [AndOp α] [OrOp α]
    [HXor α α α] [Complement α] [DecidableEq α] [WordSimpShift α]
    [BEq α] [OfNat α 0] [OfNat α 1]
    (program : WordProg α) : WordProg α :=
  let duplicated := wordDuplicateConditionsWithFold program
  wordListToProg
    (wordFuseConditionsAux (wordProgFuel duplicated + 1) []
      (wordProgToList duplicated))

/-! Cake's `word_simp$push_out_if` moves a terminating branch out of an
    `If`.  This is observable in the backend because the conditional then has
    one empty branch, changing the branch layout and avoiding an unnecessary
    jump over the terminating code.  The Boolean result records whether the
    transformed program is known to terminate normally at this point. -/
def wordPushOutIfAux : WordProg α → WordProg α × Bool
  | .mustTerminate body =>
      let (body', terminates) := wordPushOutIfAux body
      (.mustTerminate body', terminates)
  | .return label values =>
      (.return label values, true)
  | .raise exception =>
      (.raise exception, true)
  | .call none target arguments handler =>
      (.call none target arguments handler, true)
  | .ite operator condition right thenBranch elseBranch =>
      let (thenBranch', thenTerminates) := wordPushOutIfAux thenBranch
      let (elseBranch', elseTerminates) := wordPushOutIfAux elseBranch
      match thenTerminates, elseTerminates with
      | true, true =>
          (.ite operator condition right thenBranch' elseBranch', true)
      | false, true =>
          (.seq (.ite operator condition right .skip elseBranch') thenBranch', false)
      | true, false =>
          (.seq (.ite operator condition right thenBranch' .skip) elseBranch', false)
      | false, false =>
          (.ite operator condition right thenBranch' elseBranch', false)
  | .seq first second =>
      let (first', firstTerminates) := wordPushOutIfAux first
      if firstTerminates then
        (.seq first' second, true)
      else
        let (second', secondTerminates) := wordPushOutIfAux second
        (.seq first' second', secondTerminates)
  | .loop liveIn body liveOut =>
      let (body', _) := wordPushOutIfAux body
      (.loop liveIn body' liveOut, false)
  | program =>
      (program, false)
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def wordPushOutIf (program : WordProg α) : WordProg α :=
  (wordPushOutIfAux program).1

/-! The caller has already run Cake's program-level `const_fp`.  The remaining
    `simp_duplicate_if`/condition-fusion step is local to the duplicated
    branches, followed by Cake's terminating-branch hoisting.  Applying
    `const_fp` to the whole result again changes temporary numbering and the
    eventual RISC-V byte order.  Keep this wrapper as the source pipeline's
    post-`const_fp` composition before instruction selection. -/
def wordFuseConditionsAndFold [Add α] [Sub α] [AndOp α] [OrOp α]
    [HXor α α α] [Complement α] [OfNat α 1] [OfNat α 0] [DecidableEq α]
    [WordSimpShift α]
    (program : WordProg α) : WordProg α :=
  wordPushOutIf (wordFuseConditionsWithFold program)

end Flapjack.RiscV
