import Flapjack.CrepeInline

namespace Flapjack

/-! Executable regressions for Crepe inline return rewriting. -/

def crepInlineEocResult : CrepProg Nat :=
  crepTransformEoc [8, 9]
    (.return [.const 1, .const 2] : CrepProg Nat)

def crepInlineEocCheck : Bool :=
  match crepInlineEocResult with
  | .seq (.assign 8 (.const 1))
      (.seq (.assign 9 (.const 2)) .skip) => true
  | _ => false

#guard crepInlineEocCheck

def crepInlineBranchResult : CrepProg Nat :=
  crepTransformBranch 2 [8]
    (.return [.const 4] : CrepProg Nat)

def crepInlineBranchCheck : Bool :=
  match crepInlineBranchResult with
  | .seq (.seq (.assign 8 (.const 4)) .skip) (.break 2) => true
  | _ => false

#guard crepInlineBranchCheck

def crepInlineArgsResult : CrepProg Nat :=
  crepArgLoad [20, 21] [.const 3, .const 4] [10, 11]
    (.return [.var 10, .var 11] : CrepProg Nat)

def crepInlineArgsCheck : Bool :=
  match crepInlineArgsResult with
  | .dec 20 (.const 3) (.dec 21 (.const 4)
      (.dec 10 (.var 20) (.dec 11 (.var 21) (.return [.var 10, .var 11])))) => true
  | _ => false

#guard crepInlineArgsCheck

end Flapjack
