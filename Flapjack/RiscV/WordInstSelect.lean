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
      let (prelude, address) := wordInstSelectAtom temp address
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
