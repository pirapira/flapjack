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
  | .seq first second => !crepHasReturn first && !crepHasReturn second
  | .ite _ thenBranch elseBranch =>
      !crepHasReturn thenBranch && !crepHasReturn elseBranch
  | .while _ body => !crepHasReturn body
  | .call none _ _ | .call (some (_, none)) _ _ => true
  | .call (some (_, some (_, handler))) _ _ => !crepHasReturn handler
  | _ => true
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

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

end Flapjack
