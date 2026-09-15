import Flapjack.RiscV.WordExpressionFlatten

/-!
# Word instruction selection for shared-memory addresses

Cake's `word_inst$inst_select` receives one fixed fresh temporary per
function.  For `ShareInst` it materializes the address into that temporary
and leaves a small `base + immediate` form when the offset fits.  The old
Flapjack boundary passed the expression tree directly to Word-to-Stack,
which is semantically usable but emits a different register sequence.
-/

namespace Flapjack.RiscV

open Flapjack

def wordInstSelectMaximum : List Nat → Nat
  | [] => 0
  | value :: values => max value (wordInstSelectMaximum values)
termination_by values => sizeOf values
decreasing_by all_goals decreasing_trivial

/- A local sequence join keeps the pass in the same right-associated shape as
`wordFlattenProgram`, without depending on the dead-code pass. -/
def wordDeadSelectSeq (first second : WordProg α) : WordProg α :=
  match first, second with
  | .skip, program => program
  | program, .skip => program
  | _, _ => .seq first second

/-! Cake's `pull_exp` and `flatten_exp` are observable before the allocator.
    `pull_ops` accumulates operands on the left, and `flatten_exp` rebuilds an
    n-ary operation as a right-associated binary tree.  Subtraction is the
    important exception: Cake handles it with `convert_sub` and never feeds
    it through the associative operand collector.  In particular, applying
    `pull_ops` to `Sub [x, y]` would incorrectly turn the expression into
    `Sub [y, x]`.  Keeping these cases explicit preserves the source operand
    order that feeds Cake's move preferences and clash graph. -/

def wordInstPullOps (operator : BinOp) :
    List (WordExp α) → List (WordExp α) → List (WordExp α)
  | [], accumulated => accumulated
  | expression :: expressions, accumulated =>
      match expression with
      | .op nested args =>
          if nested = operator then
            wordInstPullOps operator expressions (args ++ accumulated)
          else
            wordInstPullOps operator expressions (expression :: accumulated)
      | _ => wordInstPullOps operator expressions (expression :: accumulated)
termination_by expressions _ => sizeOf expressions
decreasing_by all_goals decreasing_trivial

def wordInstConvertSub [Sub α] [OfNat α 0] : List (WordExp α) → WordExp α
  | [.const left, .const right] => .const (left - right)
  | [expression, .const value] => .op .add [.const (0 - value), expression]
  | expressions => .op .sub expressions

def wordInstPullExp [Sub α] [OfNat α 0] : WordExp α → WordExp α
  | .op operator [] => .op operator []
  | .op _ [expression] => wordInstPullExp expression
  | .op .sub expressions =>
      wordInstConvertSub (expressions.map wordInstPullExp)
  | .op operator expressions =>
      let expressions := expressions.map wordInstPullExp
      .op operator (wordInstPullOps operator expressions [])
  | .load address => .load (wordInstPullExp address)
  | .shift operator left right =>
      .shift operator (wordInstPullExp left) (wordInstPullExp right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordInstFlattenExp : WordExp α → WordExp α
  | .op operator [] => .op operator []
  | .op _ [expression] => wordInstFlattenExp expression
  | .op operator (expression :: expressions) =>
      .op operator
        [ wordInstFlattenExp expression
        , wordInstFlattenExp (.op operator expressions) ]
  | .load address => .load (wordInstFlattenExp address)
  | .shift operator left right =>
      .shift operator (wordInstFlattenExp left) (wordInstFlattenExp right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordInstNormalizeExp [Sub α] [OfNat α 0] (expression : WordExp α) : WordExp α :=
  wordInstFlattenExp (wordInstPullExp expression)

def wordInstSelectAtom [Sub α] [OfNat α 0] [OfNat α 1] [DecidableEq α]
    (temp : Nat) : WordExp α → WordProg α × WordExp α
  | .const value => (.assign temp (.const value), .var temp)
  | .var name => (.assign temp (.var name), .var temp)
  | .lookup store => (.assign temp (.lookup store), .var temp)
  | .load address =>
      let (prelude, address) := wordInstSelectAtom temp address
      (wordDeadSelectSeq prelude (.assign temp (.load address)), .var temp)
  | .op .add [left, .const value] =>
      let (prelude, left) := wordInstSelectAtom temp left
      (prelude, .op .add [left, .const value])
  | .op operator [left, right] =>
      let (leftPrelude, _) := wordInstSelectAtom temp left
      let (rightPrelude, _) := wordInstSelectAtom (temp + 1) right
      let code := wordDeadSelectSeq leftPrelude rightPrelude
      let generic :=
        (wordDeadSelectSeq code
          (.assign temp (.op operator [.var temp, .var (temp + 1)])), .var temp)
      match operator, left, right with
      | .add, .lookup .currHeap,
          .shift .lsl (.lookup .heapLength) (.const value) =>
          if value = (1 : α) then
            (.seq (.get temp .heapLength)
              (.seq (.assign temp (.shift .lsl (.var temp) (.const (1 : α))))
                (.opCurrHeap .add temp temp)), .var temp)
          else generic
      | .add, .shift .lsl (.lookup .heapLength) (.const value),
          .lookup .currHeap =>
          if value = (1 : α) then
            (.seq (.get temp .heapLength)
              (.seq (.assign temp (.shift .lsl (.var temp) (.const (1 : α))))
                (.opCurrHeap .add temp temp)), .var temp)
          else generic
      | _, _, _ => generic
  | .shift operator left right =>
      let (leftPrelude, _) := wordInstSelectAtom temp left
      let (rightPrelude, _) := wordInstSelectAtom (temp + 1) right
      let code := wordDeadSelectSeq leftPrelude rightPrelude
      (wordDeadSelectSeq code
        (.assign temp (.shift operator (.var temp) (.var (temp + 1)))), .var temp)
  | expression => (.assign temp expression, .var temp)
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordInstSelectProgram [Sub α] [OfNat α 0] [OfNat α 1] [DecidableEq α]
    (temp : Nat) : WordProg α → WordProg α
  | .seq first second =>
      wordDeadSelectSeq (wordInstSelectProgram temp first)
        (wordInstSelectProgram temp second)
  | .shareInst operator name address =>
      let (prelude, address) :=
        wordInstSelectAtom temp (wordInstNormalizeExp address)
      wordDeadSelectSeq prelude (.shareInst operator name address)
  | .assign destination value =>
      let value := wordInstNormalizeExp value
      match value with
      | .load address =>
          if wordExpIsAtom address then
            .assign destination value
          else
            let (prelude, address) := wordInstSelectAtom temp address
            wordDeadSelectSeq prelude (.assign destination (.load address))
      | .op operator [left, .const value] =>
          let (prelude, left) := wordInstSelectAtom temp left
          wordDeadSelectSeq prelude
            (.assign destination (.op operator [left, .const value]))
      | .op operator [left, right] =>
          let (leftPrelude, left) := wordInstSelectAtom temp left
          let (rightPrelude, right) := wordInstSelectAtom (temp + 1) right
          wordDeadSelectSeq leftPrelude
            (wordDeadSelectSeq rightPrelude
              (.assign destination (.op operator [left, right])))
      | value => .assign destination value
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right
        (wordInstSelectProgram temp thenBranch)
        (wordInstSelectProgram temp elseBranch)
  | .loop liveIn body liveOut =>
      .loop liveIn (wordInstSelectProgram temp body) liveOut
  | .mustTerminate body => .mustTerminate (wordInstSelectProgram temp body)
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments none =>
      .call (some (destinations, cutsets,
        wordInstSelectProgram temp returnCode, returnLabel, entryLabel))
        target arguments none
  | .call (some (destinations, cutsets, returnCode, returnLabel, entryLabel))
      target arguments (some (exception, body, handlerLabel, handlerEntryLabel)) =>
      .call (some (destinations, cutsets,
        wordInstSelectProgram temp returnCode, returnLabel, entryLabel))
        target arguments
        (some (exception, wordInstSelectProgram temp body,
          handlerLabel, handlerEntryLabel))
  | .call none target arguments none =>
      .call none target arguments none
  | .call none target arguments (some (exception, body, handlerLabel, handlerEntryLabel)) =>
      .call none target arguments
        (some (exception, wordInstSelectProgram temp body,
          handlerLabel, handlerEntryLabel))
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordInstSelectProgramFrom [Sub α] [OfNat α 0] [OfNat α 1] [DecidableEq α]
    (program : WordProg α) : WordProg α :=
  wordInstSelectProgram (wordInstSelectMaximum (wordProgVariables program) + 1) program

end Flapjack.RiscV
