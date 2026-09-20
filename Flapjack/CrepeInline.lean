import Flapjack.Crepe

/-!
Executable support for the Crepe inlining pass.

This file ports the analysis and control-flow-normalization pieces of
CakeML's `crep_inline` theory.  The actual call substitution is intentionally
kept as a later layer; these helpers are useful independently when checking
that an inline candidate has no unreachable tail.
-/

namespace Flapjack

def crepVarProg : CrepProg α → List Nat
  | .dec name value body => [name] ++ crepExpVars value ++ crepVarProg body
  | .assign name value => [name] ++ crepExpVars value
  | .primitive names _ arguments => names ++ arguments
  | .store address value | .store32 address value | .storeByte address value =>
      crepExpVars address ++ crepExpVars value
  | .storeGlob _ value => crepExpVars value
  | .seq first second => crepVarProg first ++ crepVarProg second
  | .ite condition thenBranch elseBranch =>
      crepExpVars condition ++ crepVarProg thenBranch ++ crepVarProg elseBranch
  | .while condition body => crepExpVars condition ++ crepVarProg body
  | .call none _ arguments => arguments.flatMap crepExpVars
  | .call (some (names, none)) _ arguments =>
      arguments.flatMap crepExpVars ++ names
  | .call (some (names, some (_, handler))) _ arguments =>
      arguments.flatMap crepExpVars ++ names ++ crepVarProg handler
  | .extCall _ configuration configurationLength array arrayLength =>
      [configuration, configurationLength, array, arrayLength]
  | .return values => values.flatMap crepExpVars
  | .shMem _ name address => name :: crepExpVars address
  | .skip | .break _ | .continue _ | .raise _ | .tick => []
termination_by program => sizeOf program
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

def crepVmaxProg (program : CrepProg α) : Nat :=
  (crepVarProg program).foldl max 0

def crepHasReturn : CrepProg α → Bool
  | .dec _ _ body => crepHasReturn body
  | .seq first second => crepHasReturn first || crepHasReturn second
  | .ite _ thenBranch elseBranch =>
      crepHasReturn thenBranch || crepHasReturn elseBranch
  | .while _ body => crepHasReturn body
  | .call none _ _ => true
  | .call (some (_, none)) _ _ => false
  | .call (some (_, some (_, handler))) _ _ => crepHasReturn handler
  | .return _ => true
  | _ => false
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def crepNotBranchRet : CrepProg α → Bool
  | .dec _ _ body => crepNotBranchRet body
  /- CakeML recurses `not_branch_ret` into both `Seq` children
     (`crep_inlineScript.sml:70`); the non-recursive `has_return` test is
     only used for `If`/`While`. -/
  | .seq first second => crepNotBranchRet first && crepNotBranchRet second
  | .ite _ thenBranch elseBranch =>
      !crepHasReturn thenBranch && !crepHasReturn elseBranch
  | .while _ body => !crepHasReturn body
  | .call none _ _ | .call (some (_, none)) _ _ => true
  | .call (some (_, some (_, handler))) _ _ => !crepHasReturn handler
  | _ => true
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! Kernel-checked port of CakeML's
    `not_has_return_imp_not_branch_ret` (`crep_inlineProofScript.sml:1758`):
    a program with no return cannot acquire a return through a branching
    construct.  The handler case is included because handlers are recursive
    Crep programs rather than opaque metadata. -/
private theorem crepHasReturn_false_imp_notBranchRet_aux :
    (program : CrepProg α) →
      crepHasReturn program = false → crepNotBranchRet program = true
  | .skip => fun _ => by simp [crepNotBranchRet]
  | .dec name value body => fun h =>
      by
        simpa [crepNotBranchRet] using
          (crepHasReturn_false_imp_notBranchRet_aux body (by
            simpa [crepHasReturn] using h))
  | .assign name value => fun _ => by simp [crepNotBranchRet]
  | .primitive names operator args =>
      fun _ => by simp [crepNotBranchRet]
  | .store address value => fun _ => by simp [crepNotBranchRet]
  | .store32 address value =>
      fun _ => by simp [crepNotBranchRet]
  | .storeByte address value =>
      fun _ => by simp [crepNotBranchRet]
  | .storeGlob address value =>
      fun _ => by simp [crepNotBranchRet]
  | .seq first second => fun h =>
      by
        have hparts : crepHasReturn first = false ∧
            crepHasReturn second = false := by
          simpa [crepHasReturn] using h
        simp [crepNotBranchRet,
          crepHasReturn_false_imp_notBranchRet_aux first hparts.1,
          crepHasReturn_false_imp_notBranchRet_aux second hparts.2]
  | .ite condition thenBranch elseBranch => fun h =>
      by simpa [crepHasReturn, crepNotBranchRet] using h
  | .while condition body => fun h =>
      by simpa [crepHasReturn, crepNotBranchRet] using h
  | .break label => fun _ => by simp [crepNotBranchRet]
  | .continue label => fun _ => by simp [crepNotBranchRet]
  | .call none name args => fun h =>
      by simp [crepHasReturn] at h
  | .call (some (names, none)) name args =>
      fun _ => by simp [crepNotBranchRet]
  | .call (some (names, some (handlerName, handler))) name args => fun h =>
      by
        have hhandler : crepHasReturn handler = false := by
          simpa [crepHasReturn] using h
        simpa [crepNotBranchRet] using hhandler
  | .extCall function configuration configurationLength array arrayLength =>
      fun _ => by simp [crepNotBranchRet]
  | .raise exception => fun _ => by simp [crepNotBranchRet]
  | .return values => fun _ => by simp [crepNotBranchRet]
  | .shMem operator name address =>
      fun _ => by simp [crepNotBranchRet]
  | .tick => fun _ => by simp [crepNotBranchRet]
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

theorem crepHasReturn_false_imp_notBranchRet (program : CrepProg α)
    (h : crepHasReturn program = false) :
    crepNotBranchRet program = true :=
  crepHasReturn_false_imp_notBranchRet_aux program h

inductive CrepEarlyExit where
  | exception
  | return
  | loopExit
  deriving DecidableEq, Repr

def crepMergeExit : Option CrepEarlyExit → Option CrepEarlyExit → Option CrepEarlyExit
  | some .return, second => second
  | first, some .return => first
  | some .exception, second => second
  | first, some .exception => first
  | some .loopExit, second => second
  | first, some .loopExit => first
  | none, none => none

def crepArgLoad (temporaryNames : List Nat) (arguments : List (CrepExp α))
    (argumentNames : List Nat) (program : CrepProg α) : CrepProg α :=
  nestedDecs temporaryNames arguments
    (nestedDecs argumentNames (temporaryNames.map .var) program)

def crepInlineTail (program : CrepProg α) : CrepProg α :=
  .seq .tick program

def crepTransformEoc (returnNames : List Nat) : CrepProg α → CrepProg α
  | .return values =>
      crepNestedSeq (returnNames.zipWith (fun name value => .assign name value) values)
  | .call none name arguments =>
      .call (some (returnNames, none)) name arguments
  | .call (some (names, none)) name arguments =>
      .call (some (names, none)) name arguments
  | .call (some (names, some (handler, body))) name arguments =>
      .call (some (names, some (handler, crepTransformEoc returnNames body)))
        name arguments
  | .dec name value body => .dec name value (crepTransformEoc returnNames body)
  | .while condition body => .while condition (crepTransformEoc returnNames body)
  | .seq first second =>
      .seq (crepTransformEoc returnNames first) (crepTransformEoc returnNames second)
  | .ite condition thenBranch elseBranch =>
      .ite condition (crepTransformEoc returnNames thenBranch)
        (crepTransformEoc returnNames elseBranch)
  | program => program
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def crepTransformBranch (loopDepth : Nat) (returnNames : List Nat) :
    CrepProg α → CrepProg α
  | .return values =>
      .seq
        (crepNestedSeq
          (returnNames.zipWith (fun name value => .assign name value) values))
        (.break loopDepth)
  | .call none name arguments =>
      .seq (.call (some (returnNames, none)) name arguments) (.break loopDepth)
  | .call (some (names, none)) name arguments =>
      .call (some (names, none)) name arguments
  | .call (some (names, some (handler, body))) name arguments =>
      .call (some (names, some (handler,
        crepTransformBranch loopDepth returnNames body))) name arguments
  | .dec name value body =>
      .dec name value (crepTransformBranch loopDepth returnNames body)
  | .while condition body =>
      .while condition (crepTransformBranch (loopDepth + 1) returnNames body)
  | .seq first second =>
      .seq (crepTransformBranch loopDepth returnNames first)
        (crepTransformBranch loopDepth returnNames second)
  | .ite condition thenBranch elseBranch =>
      .ite condition (crepTransformBranch loopDepth returnNames thenBranch)
        (crepTransformBranch loopDepth returnNames elseBranch)
  | program => program
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def crepInlineNontail [OfNat α 0] (program : CrepProg α) (returnNames temporaryReturns
    temporaryNames : List Nat) (arguments : List (CrepExp α))
    (argumentNames : List Nat) : CrepProg α :=
  nestedDecs temporaryReturns (temporaryReturns.map (fun _ => .const 0))
    (.seq
      (crepArgLoad temporaryNames
        arguments argumentNames program)
      (crepNestedSeq
        (returnNames.zipWith (fun name temporary => .assign name (.var temporary))
          temporaryReturns)))

def crepUnreachElim : CrepProg α → CrepProg α × Option CrepEarlyExit
  | .return values => (.return values, some .return)
  | .raise exception => (.raise exception, some .exception)
  | .break label => (.break label, some .loopExit)
  | .continue label => (.continue label, some .loopExit)
  | .seq first second =>
      let (first', firstExit) := crepUnreachElim first
      if firstExit.isSome then
        (first', firstExit)
      else
        let (second', secondExit) := crepUnreachElim second
        (.seq first' second', secondExit)
  | .dec name value body =>
      let (body', bodyExit) := crepUnreachElim body
      (.dec name value body', bodyExit)
  | .ite condition thenBranch elseBranch =>
      let (then', thenExit) := crepUnreachElim thenBranch
      let (else', elseExit) := crepUnreachElim elseBranch
      (.ite condition then' else', crepMergeExit thenExit elseExit)
  | .while condition body =>
      let (body', _) := crepUnreachElim body
      (.while condition body', none)
  | .call none name arguments =>
      (.call none name arguments, some .return)
  | .call (some (names, none)) name arguments =>
      (.call (some (names, none)) name arguments, none)
  | .call (some (names, some (handler, body))) name arguments =>
      let (body', _) := crepUnreachElim body
      (.call (some (names, some (handler, body'))) name arguments, none)
  | program => (program, none)
termination_by program => sizeOf program
decreasing_by
  all_goals first | decreasing_trivial | simp_wf

/-! Kernel-checked port of CakeML's
    `not_has_return_imp_unreach_elim` (`crep_inlineProofScript.sml:1765`):
    `unreach_elim` cannot report a return for a program whose executable
    return analysis is false.  The private statement is slightly stronger
    than Cake's self-equality formulation and makes the recursive argument
    explicit; the public theorem below recovers the original statement. -/
private theorem crepHasReturn_false_imp_unreachElim_notReturn_aux :
    (program : CrepProg α) →
      crepHasReturn program = false →
      (crepUnreachElim program).2 ≠ some .return
  | .skip => fun _ => by simp [crepUnreachElim]
  | .dec name value body => fun h =>
      by
        simpa [crepUnreachElim] using
          (crepHasReturn_false_imp_unreachElim_notReturn_aux body (by
            simpa [crepHasReturn] using h))
  | .assign name value => fun _ => by simp [crepUnreachElim]
  | .primitive names operator args => fun _ => by simp [crepUnreachElim]
  | .store address value => fun _ => by simp [crepUnreachElim]
  | .store32 address value => fun _ => by simp [crepUnreachElim]
  | .storeByte address value => fun _ => by simp [crepUnreachElim]
  | .storeGlob address value => fun _ => by simp [crepUnreachElim]
  | .seq first second => fun h =>
      by
        have hparts : crepHasReturn first = false ∧
            crepHasReturn second = false := by
          simpa [crepHasReturn] using h
        cases hfirst : crepUnreachElim first with
        | mk first' firstExit =>
            cases hsecond : crepUnreachElim second with
            | mk second' secondExit =>
                have hfirstNot : firstExit ≠ some .return := by
                  simpa [hfirst] using
                    (crepHasReturn_false_imp_unreachElim_notReturn_aux first
                      hparts.1)
                have hsecondNot : secondExit ≠ some .return := by
                  simpa [hsecond] using
                    (crepHasReturn_false_imp_unreachElim_notReturn_aux second
                      hparts.2)
                by_cases hsome : firstExit.isSome
                · simp [crepUnreachElim, hfirst, hsome, hfirstNot]
                · simp [crepUnreachElim, hfirst, hsecond, hsome, hsecondNot]
  | .ite condition thenBranch elseBranch => fun h =>
      by
        have hparts : crepHasReturn thenBranch = false ∧
            crepHasReturn elseBranch = false := by
          simpa [crepHasReturn] using h
        cases hthen : crepUnreachElim thenBranch with
        | mk then' thenExit =>
            cases helse : crepUnreachElim elseBranch with
            | mk else' elseExit =>
                have hthenNot : thenExit ≠ some .return := by
                  simpa [hthen] using
                    (crepHasReturn_false_imp_unreachElim_notReturn_aux thenBranch
                      hparts.1)
                have helseNot : elseExit ≠ some .return := by
                  simpa [ helse] using
                    (crepHasReturn_false_imp_unreachElim_notReturn_aux elseBranch
                      hparts.2)
                cases thenExit with
                | none =>
                    cases elseExit with
                    | none => simp [crepUnreachElim, hthen, helse, crepMergeExit]
                    | some elseExit =>
                        cases elseExit <;>
                          simp [crepUnreachElim, hthen, helse, crepMergeExit]
                | some thenExit =>
                    cases thenExit with
                    | exception =>
                        cases elseExit with
                        | none => simp [crepUnreachElim, hthen, helse, crepMergeExit]
                        | some elseExit =>
                            cases elseExit <;>
                              simp [crepUnreachElim, hthen, helse, crepMergeExit,
                                helseNot]
                    | «return» =>
                        simp at hthenNot
                    | loopExit =>
                        cases elseExit with
                        | none => simp [crepUnreachElim, hthen, helse, crepMergeExit]
                        | some elseExit =>
                            cases elseExit <;>
                              simp [crepUnreachElim, hthen, helse, crepMergeExit,
                                helseNot]
  | .while condition body => fun _ => by simp [crepUnreachElim]
  | .break label => fun _ => by simp [crepUnreachElim]
  | .continue label => fun _ => by simp [crepUnreachElim]
  | .call none name args => fun h => by simp [crepHasReturn] at h
  | .call (some (names, none)) name args => fun _ => by simp [crepUnreachElim]
  | .call (some (names, some (handlerName, handler))) name args =>
      fun _ => by simp [crepUnreachElim]
  | .extCall function configuration configurationLength array arrayLength =>
      fun _ => by simp [crepUnreachElim]
  | .raise exception => fun _ => by simp [crepUnreachElim]
  | .return values => fun h => by simp [crepHasReturn] at h
  | .shMem operator name address => fun _ => by simp [crepUnreachElim]
  | .tick => fun _ => by simp [crepUnreachElim]
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

theorem crepHasReturn_false_imp_unreachElim_notReturn
    (program : CrepProg α) (result : Option CrepEarlyExit)
    (hReturn : crepHasReturn program = false)
    (hElim : crepUnreachElim program = (program, result)) :
    result ≠ some .return := by
  have hNotReturn :=
    crepHasReturn_false_imp_unreachElim_notReturn_aux program hReturn
  rw [hElim] at hNotReturn
  exact hNotReturn

end Flapjack
