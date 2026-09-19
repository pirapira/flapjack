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

def branchReturn : CrepProg Nat :=
  .ite (.const 1) (.return [.const 1]) (.assign 2 (.const 0))

def loopReturn : CrepProg Nat :=
  .while (.const 1) (.return [.const 1])

def handledCallReturn : CrepProg Nat :=
  .call (some ([7], some (11, .return [.const 1]))) "callee" []

/-! These cases mirror `crep_inlineScript.sml:68-78`: branching and handler
    returns make `not_branch_ret` false, while calls without handlers remain
    true. -/
#guard !crepNotBranchRet branchReturn
#guard !crepNotBranchRet loopReturn
#guard !crepNotBranchRet handledCallReturn
#guard crepNotBranchRet (.call none "callee" [] : CrepProg Nat)
#guard crepNotBranchRet
    (.call (some ([7], none)) "callee" [] : CrepProg Nat)

def crepInlineUnreachable : CrepProg Nat × Option CrepEarlyExit :=
  crepUnreachElim
    (.seq (.return [.const 1]) (.assign 4 (.const 99)) : CrepProg Nat)

#guard match crepInlineUnreachable with
  | (.return [.const 1], some .return) => true
  | _ => false

def crepInlineUnreachableExits : Bool :=
  (match crepUnreachElim
      (.seq (.raise 3) (.return [.const 1]) : CrepProg Nat) with
    | (.raise 3, some .exception) => true
    | _ => false) &&
  (match crepUnreachElim
      (.ite (.const 1) (.return [.const 1]) (.raise 2) : CrepProg Nat) with
    | (.ite _ (.return [_]) (.raise _), some .exception) => true
    | _ => false) &&
  (match crepUnreachElim
      (.while (.const 1) (.return [.const 1]) : CrepProg Nat) with
    | (.while _ (.return [_]), none) => true
    | _ => false) &&
  (match crepUnreachElim
      (.call none "callee" [] : CrepProg Nat) with
    | (.call none "callee" [], some .return) => true
    | _ => false)

#guard crepInlineUnreachableExits

end Flapjack
