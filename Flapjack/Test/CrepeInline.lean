import Flapjack.CrepeInline

namespace Flapjack

/-! Executable regressions for the Crepe inlining support slice. -/

def crepInlineVariables : List Nat :=
  crepVarProg
    (.seq (.assign 4 (.var 3))
      (.call (some ([7], some (11, .assign 12 (.var 11))))
        "callee" [.var 5]) : CrepProg Nat)

#guard crepInlineVariables = [4, 3, 5, 7, 12, 11]
#guard crepVmaxProg
    (.seq (.assign 4 (.var 3)) (.return [.var 9]) : CrepProg Nat) = 9
#guard crepHasReturn (.return [.const 0] : CrepProg Nat)
#guard crepNotBranchRet (.seq (.assign 1 (.const 0)) (.assign 2 (.const 0))
    : CrepProg Nat)

def crepInlineUnreachable : CrepProg Nat × Option CrepEarlyExit :=
  crepUnreachElim
    (.seq (.return [.const 1]) (.assign 4 (.const 99)) : CrepProg Nat)

#guard match crepInlineUnreachable with
  | (.return [.const 1], some .return) => true
  | _ => false

end Flapjack
