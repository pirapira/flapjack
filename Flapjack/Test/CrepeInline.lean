import Flapjack.CrepeInline

namespace Flapjack

/-! Executable regressions for the Crepe inlining support slice. -/

def crepInlineVariables : List Nat :=
  crepVarProg
    (.seq (.assign 4 (.var 3))
      (.call (some ([7], some (11, .assign 12 (.var 11))))
        "callee" [.var 5]) : CrepProg Nat)

#guard crepInlineVariables = [4, 3, 5, 7, 12, 11]

/-! Direct coverage for Cake `var_prog_def`
    (`cakeml/pancake/crep_inlineScript.sml:11-32`).  This keeps the
    statement-level cases observable, including call handlers and all memory
    variants, rather than checking only the original sequence fixture. -/
def crepVarProgCakeParity : Bool :=
  crepVarProg (.dec 9 (.var 1) (.return [.var 2]) : CrepProg Nat) = [9, 1, 2] &&
  crepVarProg (.assign 3 (.var 4) : CrepProg Nat) = [3, 4] &&
  crepVarProg (.store (.var 5) (.const 0) : CrepProg Nat) = [5] &&
  crepVarProg (.store32 (.var 5) (.var 6) : CrepProg Nat) = [5, 6] &&
  crepVarProg (.storeByte (.var 5) (.var 6) : CrepProg Nat) = [5, 6] &&
  crepVarProg (.storeGlob 7 (.var 8) : CrepProg Nat) = [8] &&
  crepVarProg (.seq (.assign 3 (.var 4)) (.return [.var 5]) : CrepProg Nat) =
    [3, 4, 5] &&
  crepVarProg
      (.ite (.var 8) (.assign 9 (.var 10)) .skip : CrepProg Nat) = [8, 9, 10] &&
  crepVarProg (.while (.var 11) (.assign 12 (.var 13)) : CrepProg Nat) =
    [11, 12, 13] &&
  crepVarProg (.call none "f" [.var 14, .const 0] : CrepProg Nat) = [14] &&
  crepVarProg
      (.call (some ([15], none)) "f" [.var 16] : CrepProg Nat) = [16, 15] &&
  crepVarProg
      (.call (some ([17], some (18, .assign 19 (.var 20)))) "f" [.var 21]
        : CrepProg Nat) = [21, 17, 19, 20] &&
  crepVarProg (.extCall "ffi" 22 23 24 25 : CrepProg Nat) = [22, 23, 24, 25] &&
  crepVarProg (.return [.var 26, .const 0] : CrepProg Nat) = [26] &&
  crepVarProg (.shMem .store 27 (.var 28) : CrepProg Nat) = [27, 28] &&
  crepVarProg (.primitive [29, 30] .addCarry [31, 32] : CrepProg Nat) =
    [29, 30, 31, 32] &&
  crepVarProg (.skip : CrepProg Nat) = []

#guard crepVarProgCakeParity

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
