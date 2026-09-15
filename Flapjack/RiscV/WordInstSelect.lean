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

/-! Cake's `pull_exp` and `flatten_exp` are observable before the allocator:
    `pull_ops` accumulates operands on the left, and `flatten_exp` rebuilds an
    n-ary operation as a right-associated binary tree.  In particular,
    `Add [x, y]` becomes `Add [y, x]`.  Keeping these two small normalizers at
    the instruction-selection boundary preserves the source operand order
    that feeds Cake's move preferences and clash graph. -/

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

def wordInstPullExp : WordExp α → WordExp α
  | .op operator [] => .op operator []
  | .op _operator [expression] => wordInstPullExp expression
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
  | .op _operator [expression] => wordInstFlattenExp expression
  | .op operator (expression :: expressions) =>
      .op operator
        [ wordInstFlattenExp (.op operator expressions)
        , wordInstFlattenExp expression ]
  | .load address => .load (wordInstFlattenExp address)
  | .shift operator left right =>
      .shift operator (wordInstFlattenExp left) (wordInstFlattenExp right)
  | expression => expression
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordInstNormalizeExp (expression : WordExp α) : WordExp α :=
  wordInstFlattenExp (wordInstPullExp expression)

def wordInstSelectAtom (temp : Nat) : WordExp α → WordProg α × WordExp α
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
      (wordDeadSelectSeq code
        (.assign temp (.op operator [.var temp, .var (temp + 1)])), .var temp)
  | .shift operator left right =>
      let (leftPrelude, _) := wordInstSelectAtom temp left
      let (rightPrelude, _) := wordInstSelectAtom (temp + 1) right
      let code := wordDeadSelectSeq leftPrelude rightPrelude
      (wordDeadSelectSeq code
        (.assign temp (.shift operator (.var temp) (.var (temp + 1)))), .var temp)
  | expression => (.assign temp expression, .var temp)
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordInstSelectProgram (temp : Nat) : WordProg α → WordProg α
  | .seq first second =>
      wordDeadSelectSeq (wordInstSelectProgram temp first)
        (wordInstSelectProgram temp second)
  | .shareInst operator name address =>
      let (prelude, address) :=
        wordInstSelectAtom temp (wordInstNormalizeExp address)
      wordDeadSelectSeq prelude (.shareInst operator name address)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right
        (wordInstSelectProgram temp thenBranch)
        (wordInstSelectProgram temp elseBranch)
  | .loop liveIn body liveOut =>
      .loop liveIn (wordInstSelectProgram temp body) liveOut
  | .mustTerminate body => .mustTerminate (wordInstSelectProgram temp body)
  | .call returns target arguments handler =>
      /- The source-facing hello path has no nested call address.  Keep call
         metadata opaque here; the dedicated call lowering owns its handler
         recursion and remains unchanged. -/
      .call returns target arguments handler
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordInstSelectProgramFrom (program : WordProg α) : WordProg α :=
  wordInstSelectProgram (wordInstSelectMaximum (wordProgVariables program) + 1) program

end Flapjack.RiscV
