import Flapjack.RiscV.WordExpressionFlatten

/-!
# Word instruction selection

Port of CakeML `word_inst$inst_select` (see
`cakeml/compiler/backend/word_instScript.sml`).

The pass rewrites `WordLang` assignments into three-address instruction
forms that match the RISC-V addressing modes:

* `Load (Op Add [exp; Const w])` with a small offset becomes a
  base-plus-offset load (`Mem .. (Addr r w)`).
* binary operations with a constant operand become immediate forms
  (`Arith (Binop .. (Imm w))`), using the `Add → Sub (-w)` fallback that
  Cake applies when the direct immediate is out of range.
* shifts with constant amounts become immediate shifts, degenerate
  amounts (zero, or at least the word width) become moves or zero.
* other constants are materialised into registers.

`pull_exp`/`flatten_exp` re-associate expressions so that constants end
up in the right operand position, exactly like the original.
-/

namespace Flapjack.RiscV

open Flapjack

/-! ## RISC-V immediate and offset bounds

Cake's RISC-V configuration: `valid_imm (INL op) w` accepts `w` when the
signed value fits in twelve bits, except that `Sub` is emitted as `addi`
with a negated immediate, so `-2048` is excluded for it.
`addr_offset_ok`, `hw_offset_ok` and `byte_offset_ok` all accept the
signed twelve-bit range `(-2048, 2047]`. -/

def wordInstSelectValidImm {width : Nat} (operator : BinOp) (value : Word width) :
    Bool :=
  let signed := value.toInt
  (if operator == .sub then -2048 < signed else -2048 ≤ signed) &&
    signed ≤ 2047

def wordInstSelectOffsetOk {width : Nat} (value : Word width) : Bool :=
  -2048 < value.toInt && value.toInt ≤ 2047

/-! ## Constant folding helpers (Cake `word_inst` prelude) -/

/-- Cake `word_op`: right-fold evaluation of a constant list. -/
def wordInstSelectWordOp {width : Nat} [NeZero width] (operator : BinOp)
    (values : List (Word width)) : Option (Word width) :=
  match operator, values with
  | .and, values =>
      some (values.foldr (fun (left right : Word width) => left &&& right)
        (~~~ (0 : Word width)))
  | .add, values =>
      some (values.foldr (fun (left right : Word width) => left + right)
        (0 : Word width))
  | .or, values =>
      some (values.foldr (fun (left right : Word width) => left ||| right)
        (0 : Word width))
  | .xor, values =>
      some (values.foldr (fun (left right : Word width) => left ^^^ right)
        (0 : Word width))
  | .sub, [left, right] => some (left - right)
  | _, _ => none

/-- Cake `pull_ops`: pull the operands of nested identical operators to
the front of the list, accumulating in reverse. -/
def wordInstSelectPullOps (operator : BinOp) :
    List (WordExp (Word width)) → List (WordExp (Word width)) →
      List (WordExp (Word width))
  | [], accumulator => accumulator
  | .op nested arguments :: rest, accumulator =>
      if operator == nested then
        wordInstSelectPullOps operator rest (arguments ++ accumulator)
      else
        wordInstSelectPullOps operator rest
          (.op nested arguments :: accumulator)
  | expression :: rest, accumulator =>
      wordInstSelectPullOps operator rest (expression :: accumulator)
termination_by expressions _ => sizeOf expressions
decreasing_by all_goals decreasing_tactic

/-- Cake `op_consts`: the constant produced by an operator with no
operands. -/
def wordInstSelectOpConsts [NeZero width] (operator : BinOp) : WordExp (Word width) :=
  match operator with
  | .and => .const (~~~0)
  | _ => .const 0

/-- Cake `reduce_const`. -/
def wordInstSelectReduceConst [NeZero width] (operator : BinOp) (value : Word width)
    (rest : List (WordExp (Word width))) : WordExp (Word width) :=
  if value == 0 then
    if operator == .add || operator == .or || operator == .xor then
      match rest with
      | [] => .const value
      | [expression] => expression
      | _ => .op operator rest
    else if operator == .and then
      .const 0
    else
      .op operator (.const value :: rest)
  else
    .op operator (.const value :: rest)

/-- Cake `optimize_consts`. -/
def wordInstSelectOptimizeConsts [NeZero width] (operator : BinOp)
    (expressions : List (WordExp (Word width))) : WordExp (Word width) :=
  let constants := expressions.filter (fun expression =>
    match expression with
    | .const _ => true
    | _ => false)
  let others := expressions.filter (fun expression =>
    match expression with
    | .const _ => false
    | _ => true)
  match constants with
  | [] => .op operator others
  | _ =>
      match wordInstSelectWordOp operator
          (constants.map (fun expression =>
            match expression with
            | .const value => value
            | _ => 0)) with
      | some value => wordInstSelectReduceConst operator value others
      | none => .op operator expressions

/-- Cake `convert_sub`. -/
def wordInstSelectConvertSub :
    List (WordExp (Word width)) → WordExp (Word width)
  | [.const left, .const right] => .const (left - right)
  | [expression, .const right] =>
      .op .add [.const (0 - right), expression]
  | expressions => .op .sub expressions

/-- Cake `pull_exp`: re-associate so that a constant, if any, is the
head of the operand list. -/
def wordInstSelectPullExp [NeZero width] : WordExp (Word width) → WordExp (Word width)
  | .op .sub arguments =>
      wordInstSelectConvertSub (arguments.map wordInstSelectPullExp)
  | .op operator [] => wordInstSelectOpConsts operator
  | .op operator [expression] => wordInstSelectPullExp expression
  | .op operator arguments =>
      wordInstSelectOptimizeConsts operator
        (wordInstSelectPullOps operator
          (arguments.map wordInstSelectPullExp) [])
  | .load address => .load (wordInstSelectPullExp address)
  | .shift operator left right =>
      .shift operator (wordInstSelectPullExp left)
        (wordInstSelectPullExp right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_tactic

/-- Cake `flatten_exp`: fold a flat operand list into a right-leaning
binary tree whose right-most leaf is the head of the list, so constants
end up in the right operand position. -/
def wordInstSelectFlattenExp [NeZero width] : WordExp (Word width) → WordExp (Word width)
  | .op .sub arguments => .op .sub (arguments.map wordInstSelectFlattenExp)
  | .op operator [] => wordInstSelectOpConsts operator
  | .op operator [expression] => wordInstSelectFlattenExp expression
  | .op operator (expression :: rest) =>
      .op operator
        [wordInstSelectFlattenExp (.op operator rest),
         wordInstSelectFlattenExp expression]
  | .load address => .load (wordInstSelectFlattenExp address)
  | .shift operator left right =>
      .shift operator (wordInstSelectFlattenExp left)
        (wordInstSelectFlattenExp right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_tactic

/-! ## Maximal-munch instruction selection (Cake `inst_select_exp`) -/

/-- Cake `inst_select_exp`: select instructions for one binary
expression.  `target` receives the value of the whole expression and
`temporary` is the scratch register used for sub-expressions. -/
def wordInstSelectExp [NeZero width] (target temporary : Nat) :
    WordExp (Word width) → WordProg (Word width)
  | .load (.op .add [address, .const offset]) =>
      if wordInstSelectOffsetOk offset then
        .seq (wordInstSelectExp temporary temporary address)
          (.inst (.memOffset .load target temporary offset))
      else
        .seq (wordInstSelectExp temporary temporary
            (.op .add [address, .const offset]))
          (.inst (.memOffset .load target temporary 0))
  | .load address =>
      .seq (wordInstSelectExp temporary temporary address)
        (.inst (.memOffset .load target temporary 0))
  | .const value => .inst (.const target value)
  | .var name => .move 0 [(target, name)]
  | .lookup store => .get target store
  | .op operator [left, .const value] =>
      let prelude := wordInstSelectExp temporary temporary left
      if wordInstSelectValidImm operator value then
        .seq prelude (.inst (.binop operator target temporary (.imm value)))
      else if operator == .add &&
          wordInstSelectValidImm .sub (0 - value) then
        .seq prelude
          (.inst (.binop .sub target temporary (.imm (0 - value))))
      else
        .seq prelude
          (.seq (.inst (.const (temporary + 1) value))
            (.inst (.binop operator target temporary
              (.reg (temporary + 1)))))
  | .op operator [left, right] =>
      .seq (wordInstSelectExp temporary temporary left)
        (.seq (wordInstSelectExp (temporary + 1) (temporary + 1) right)
          (.inst (.binop operator target temporary
            (.reg (temporary + 1)))))
  | .shift operator expression (.const amount) =>
      let n := amount.toNat
      if n < width then
        let prelude := wordInstSelectExp temporary temporary expression
        if n == 0 then
          .seq prelude (.move 0 [(target, temporary)])
        else
          .seq prelude
            (.inst (.shiftInst operator target temporary
              (.imm (BitVec.ofNat width n))))
      else
        .inst (.const target 0)
  | .shift operator expression amount =>
      .seq (wordInstSelectExp temporary temporary expression)
        (.seq (wordInstSelectExp (temporary + 1) (temporary + 1) amount)
          (.inst (.shiftInst operator target temporary
            (.reg (temporary + 1)))))
  | _ => .skip
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_tactic

/-! ## Program-level selection (Cake `inst_select`) -/

def wordInstSelectMaximum : List Nat → Nat
  | [] => 0
  | value :: values => max value (wordInstSelectMaximum values)
termination_by values => sizeOf values
decreasing_by all_goals decreasing_trivial

def wordInstSelectProgram [NeZero width] (temporary : Nat) :
    WordProg (Word width) → WordProg (Word width)
  | .assign name value =>
      wordInstSelectExp name temporary
        (wordInstSelectFlattenExp (wordInstSelectPullExp value))
  | .set store value =>
      .seq (wordInstSelectExp temporary temporary
          (wordInstSelectFlattenExp (wordInstSelectPullExp value)))
        (.set store (.var temporary))
  | .store address name =>
      match wordInstSelectFlattenExp (wordInstSelectPullExp address) with
      | .op .add [base, .const offset] =>
          if wordInstSelectOffsetOk offset then
            .seq (wordInstSelectExp temporary temporary base)
              (.inst (.memOffset .store name temporary offset))
          else
            .seq (wordInstSelectExp temporary temporary
                (.op .add [base, .const offset]))
              (.inst (.memOffset .store name temporary 0))
      | address =>
          .seq (wordInstSelectExp temporary temporary address)
            (.inst (.memOffset .store name temporary 0))
  | .seq first second =>
      .seq (wordInstSelectProgram temporary first)
        (wordInstSelectProgram temporary second)
  | .mustTerminate body =>
      .mustTerminate (wordInstSelectProgram temporary body)
  | .shareInst operator name address =>
      match wordInstSelectFlattenExp (wordInstSelectPullExp address) with
      | .op .add [base, .const offset] =>
          if wordInstSelectOffsetOk offset then
            .seq (wordInstSelectExp temporary temporary base)
              (.shareInst operator name
                (.op .add [.var temporary, .const offset]))
          else
            .seq (wordInstSelectExp temporary temporary
                (.op .add [base, .const offset]))
              (.shareInst operator name (.var temporary))
      | address =>
          .seq (wordInstSelectExp temporary temporary address)
            (.shareInst operator name (.var temporary))
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right
        (wordInstSelectProgram temporary thenBranch)
        (wordInstSelectProgram temporary elseBranch)
  | .call returns target arguments handler =>
      let returns := match returns with
        | none => none
        | some (values, cutsets, returnCode, first, second) =>
            some (values, cutsets, wordInstSelectProgram temporary
              returnCode, first, second)
      let handler := match handler with
        | none => none
        | some (label, body, first, second) =>
            some (label, wordInstSelectProgram temporary body, first, second)
      .call returns target arguments handler
  | .loop liveIn body liveOut =>
      .loop liveIn (wordInstSelectProgram temporary body) liveOut
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_tactic

def wordInstSelectProgramFrom [NeZero width] :
    WordProg (Word width) → WordProg (Word width) :=
  fun program =>
    wordInstSelectProgram (wordInstSelectMaximum (wordProgVariables program) + 1)
      program

end Flapjack.RiscV
