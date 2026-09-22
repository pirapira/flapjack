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


theorem crepExpsOf_unreachElim (program : CrepProg α) :
    ∀ {q : CrepProg α} {r : Option CrepEarlyExit} {e : CrepExp α},
      crepUnreachElim program = (q, r) → e ∈ crepExpsOf q → e ∈ crepExpsOf program := by
  apply crepUnreachElim.induct
    (motive := fun program => ∀ {q : CrepProg α} {r : Option CrepEarlyExit} {e : CrepExp α},
      crepUnreachElim program = (q, r) → e ∈ crepExpsOf q → e ∈ crepExpsOf program)
  · intro values q r e h hmem
    rw [crepUnreachElim.eq_def] at h
    cases h
    exact hmem
  · intro exception q r e h hmem
    rw [crepUnreachElim.eq_def] at h
    cases h
    exact hmem
  · intro label q r e h hmem
    rw [crepUnreachElim.eq_def] at h
    cases h
    exact hmem
  · intro label q r e h hmem
    rw [crepUnreachElim.eq_def] at h
    cases h
    exact hmem
  · intro first second second' secondExit hfirst hsome ihFirst q r e h hmem
    have hunf : crepUnreachElim (first.seq second) = (second', secondExit) := by
      rw [crepUnreachElim.eq_def]
      dsimp only
      rw [hfirst]
      simp [hsome]
    rw [hunf] at h
    cases h
    simp only [crepExpsOf]
    exact List.mem_append.mpr (Or.inl (ihFirst hfirst hmem))
  · intro first second second' secondExit hfirst hnotsome second'' secondExit' hsecond ihFirst ihSecond q r e h hmem
    have hunf : crepUnreachElim (first.seq second) = (.seq second' second'', secondExit') := by
      rw [crepUnreachElim.eq_def]
      dsimp only
      rw [hfirst]
      simp [hnotsome, hsecond]
    rw [hunf] at h
    cases h
    simp only [crepExpsOf] at hmem
    simp only [crepExpsOf]
    rcases List.mem_append.mp hmem with hm | hm
    · exact List.mem_append.mpr (Or.inl (ihFirst hfirst hm))
    · exact List.mem_append.mpr (Or.inr (ihSecond hsecond hm))
  · intro name value body body' bodyExit hbody ih q r e h hmem
    have hunf : crepUnreachElim (.dec name value body) = (.dec name value body', bodyExit) := by
      rw [crepUnreachElim.eq_def]
      dsimp only
      rw [hbody]
    rw [hunf] at h
    cases h
    simp only [crepExpsOf, List.mem_cons] at hmem
    simp only [crepExpsOf, List.mem_cons]
    rcases hmem with heq | hmem
    · exact Or.inl heq
    · exact Or.inr (ih hbody hmem)
  · intro condition thenBranch elseBranch then' thenExit hthen then'' elseExit helse ihThen ihElse q r e h hmem
    have hunf : crepUnreachElim (.ite condition thenBranch elseBranch) =
        (.ite condition then' then'', crepMergeExit thenExit elseExit) := by
      rw [crepUnreachElim.eq_def]
      dsimp only
      rw [hthen]
      dsimp only
      rw [helse]
    rw [hunf] at h
    cases h
    simp only [crepExpsOf, List.mem_cons] at hmem
    simp only [crepExpsOf, List.mem_cons]
    rcases hmem with heq | hmem
    · exact Or.inl heq
    · rcases List.mem_append.mp hmem with hm | hm
      · exact Or.inr (List.mem_append.mpr (Or.inl (ihThen hthen hm)))
      · exact Or.inr (List.mem_append.mpr (Or.inr (ihElse helse hm)))
  · intro condition body body' bodyExit hbody ih q r e h hmem
    have hunf : crepUnreachElim (.while condition body) = (.while condition body', none) := by
      rw [crepUnreachElim.eq_def]
      dsimp only
      rw [hbody]
    rw [hunf] at h
    cases h
    simp only [crepExpsOf, List.mem_cons] at hmem
    simp only [crepExpsOf, List.mem_cons]
    rcases hmem with heq | hmem
    · exact Or.inl heq
    · exact Or.inr (ih hbody hmem)
  · intro name arguments q r e h hmem
    rw [crepUnreachElim.eq_def] at h
    cases h
    exact hmem
  · intro names name arguments q r e h hmem
    rw [crepUnreachElim.eq_def] at h
    cases h
    exact hmem
  · intro names handler body name arguments second' secondExit hbody ih q r e h hmem
    have hunf : crepUnreachElim (.call (some (names, some (handler, body))) name arguments) =
        (.call (some (names, some (handler, second'))) name arguments, none) := by
      rw [crepUnreachElim.eq_def]
      dsimp only
      rw [hbody]
    rw [hunf] at h
    cases h
    simp only [crepExpsOf] at hmem ⊢
    rcases List.mem_append.mp hmem with hm | hm
    · exact List.mem_append.mpr (Or.inl hm)
    · exact List.mem_append.mpr (Or.inr (ih hbody hm))
  · intro program hret hraise hbreak hcontinue hseq hdec hite hwhile hcallnone hcallsomenone hcallsomesome
    intro q r e h hmem
    cases program <;> simp_all [crepUnreachElim]

theorem crepExpsOf_nestedSeq_assign_zipWith (names : List Nat) :
    ∀ (values : List (CrepExp α)) {e : CrepExp α},
      e ∈ crepExpsOf
          (crepNestedSeq (names.zipWith (fun name value => .assign name value)
            values)) →
        e ∈ values := by
  induction names with
  | nil =>
      intro values e hmem
      cases values with
      | nil => simp [crepNestedSeq, crepExpsOf] at hmem
      | cons value values => simp [crepNestedSeq, crepExpsOf] at hmem
  | cons name names ih =>
      intro values e hmem
      cases values with
      | nil => simp [List.zipWith, crepNestedSeq, crepExpsOf] at hmem
      | cons value values =>
          simp only [List.zipWith_cons_cons, crepNestedSeq, crepExpsOf,
            List.singleton_append, List.mem_cons] at hmem
          rcases hmem with heq | hmem
          · subst heq; exact by simp
          · exact List.mem_cons.mpr (Or.inr (ih values hmem))

theorem crepExpsOf_transformEoc (returnNames : List Nat) (program : CrepProg α) :
    ∀ {e : CrepExp α},
      e ∈ crepExpsOf (crepTransformEoc returnNames program) →
        e ∈ crepExpsOf program := by
  apply crepTransformEoc.induct
    (motive := fun program => ∀ {e : CrepExp α},
      e ∈ crepExpsOf (crepTransformEoc returnNames program) →
        e ∈ crepExpsOf program)
  · intro values e hmem
    simp only [crepTransformEoc, crepExpsOf] at hmem ⊢
    exact crepExpsOf_nestedSeq_assign_zipWith returnNames values hmem
  · intro name arguments e hmem
    simpa only [crepTransformEoc, crepExpsOf] using hmem
  · intro names name arguments e hmem
    simpa only [crepTransformEoc, crepExpsOf] using hmem
  · intro names handler body name arguments ih e hmem
    simp only [crepTransformEoc, crepExpsOf] at hmem ⊢
    rcases List.mem_append.mp hmem with h | h
    · exact List.mem_append.mpr (Or.inl h)
    · exact List.mem_append.mpr (Or.inr (ih h))
  · intro name value body ih e hmem
    simp only [crepTransformEoc, crepExpsOf, List.mem_cons] at hmem ⊢
    rcases hmem with h | h
    · exact Or.inl h
    · exact Or.inr (ih h)
  · intro condition body ih e hmem
    simp only [crepTransformEoc, crepExpsOf, List.mem_cons] at hmem ⊢
    rcases hmem with h | h
    · exact Or.inl h
    · exact Or.inr (ih h)
  · intro first second ihFirst ihSecond e hmem
    simp only [crepTransformEoc, crepExpsOf] at hmem ⊢
    rcases List.mem_append.mp hmem with h | h
    · exact List.mem_append.mpr (Or.inl (ihFirst h))
    · exact List.mem_append.mpr (Or.inr (ihSecond h))
  · intro condition thenBranch elseBranch ihThen ihElse e hmem
    simp only [crepTransformEoc, crepExpsOf, List.mem_cons] at hmem ⊢
    rcases hmem with h | h
    · exact Or.inl h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr (List.mem_append.mpr (Or.inl (ihThen h)))
      · exact Or.inr (List.mem_append.mpr (Or.inr (ihElse h)))
  · intro program h1 h2 h3 h4 h5 h6 h7 h8 e hmem
    cases program <;> simp_all [crepTransformEoc]

theorem crepExpsOf_transformBranch (loopDepth : Nat) (returnNames : List Nat)
    (program : CrepProg α) :
    ∀ {e : CrepExp α},
      e ∈ crepExpsOf (crepTransformBranch loopDepth returnNames program) →
        e ∈ crepExpsOf program := by
  apply crepTransformBranch.induct (motive := fun loopDepth program =>
    ∀ {e : CrepExp α},
      e ∈ crepExpsOf (crepTransformBranch loopDepth returnNames program) →
        e ∈ crepExpsOf program)
  · intro loopDepth values e hmem
    simp only [crepTransformBranch, crepExpsOf, List.append_nil] at hmem ⊢
    exact crepExpsOf_nestedSeq_assign_zipWith returnNames values hmem
  · intro loopDepth name arguments e hmem
    simp only [crepTransformBranch, crepExpsOf, List.append_nil] at hmem ⊢
    exact hmem
  · intro loopDepth names name arguments e hmem
    simpa only [crepTransformBranch, crepExpsOf] using hmem
  · intro loopDepth names handler body name arguments ih e hmem
    simp only [crepTransformBranch, crepExpsOf] at hmem ⊢
    rcases List.mem_append.mp hmem with h | h
    · exact List.mem_append.mpr (Or.inl h)
    · exact List.mem_append.mpr (Or.inr (ih h))
  · intro loopDepth name value body ih e hmem
    simp only [crepTransformBranch, crepExpsOf, List.mem_cons] at hmem ⊢
    rcases hmem with heq | hmem
    · exact Or.inl heq
    · exact Or.inr (ih hmem)
  · intro loopDepth condition body ih e hmem
    simp only [crepTransformBranch, crepExpsOf, List.mem_cons] at hmem ⊢
    rcases hmem with heq | hmem
    · exact Or.inl heq
    · exact Or.inr (ih hmem)
  · intro loopDepth first second ihFirst ihSecond e hmem
    simp only [crepTransformBranch, crepExpsOf] at hmem ⊢
    rcases List.mem_append.mp hmem with h | h
    · exact List.mem_append.mpr (Or.inl (ihFirst h))
    · exact List.mem_append.mpr (Or.inr (ihSecond h))
  · intro loopDepth condition thenBranch elseBranch ihThen ihElse e hmem
    simp only [crepTransformBranch, crepExpsOf, List.mem_cons] at hmem ⊢
    rcases hmem with heq | hmem
    · exact Or.inl heq
    · rcases List.mem_append.mp hmem with h | h
      · exact Or.inr (List.mem_append.mpr (Or.inl (ihThen h)))
      · exact Or.inr (List.mem_append.mpr (Or.inr (ihElse h)))
  · intro loopDepth program h1 h2 h3 h4 h5 h6 h7 h8 e hmem
    cases program <;> simp_all [crepTransformBranch]

/-- Cake's `mem_var_prog_nested_seq`
    (`cakeml/pancake/proofs/crep_inlineProofScript.sml:2226`): the variables of
    a nested sequence are the concatenation of the statements' variables. -/
theorem crepVarProg_nestedSeq (programs : List (CrepProg α)) :
    ∀ x, x ∈ crepVarProg (crepNestedSeq programs) ↔
      x ∈ (programs.map crepVarProg).flatten := by
  induction programs with
  | nil => intro x; simp [crepNestedSeq, crepVarProg]
  | cons program programs ih =>
      intro x; simp [crepNestedSeq, crepVarProg, ih, List.mem_append]

/-- The `List.zipWith` variant of `crepVarProg` for a nested sequence of
    assignments used by `crepTransformEoc` and `crepTransformBranch`: the
    variables of the generated assignments are among the given names or the
    values' variables. -/
theorem crepVarProg_nestedSeq_assign_zipWith (names : List Nat) :
    ∀ (values : List (CrepExp α)) {x : Nat},
      x ∈ crepVarProg
          (crepNestedSeq (names.zipWith (fun name value => .assign name value) values)) →
        x ∈ names ∨ x ∈ values.flatMap crepExpVars := by
  induction names with
  | nil =>
      intro values x hmem
      cases values with
      | nil => simp [List.zipWith, crepNestedSeq, crepVarProg] at hmem
      | cons value values => simp [List.zipWith, crepNestedSeq, crepVarProg] at hmem
  | cons name names ih =>
      intro values x hmem
      cases values with
      | nil => simp [List.zipWith, crepNestedSeq, crepVarProg] at hmem
      | cons value values =>
          simp only [List.zipWith_cons_cons, crepNestedSeq, crepVarProg,
            List.mem_append] at hmem
          rcases hmem with h | h
          · rcases h with h | h
            · exact Or.inl (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))
            · exact Or.inr (List.mem_flatMap.mpr ⟨value, by simp, h⟩)
          · rcases ih values h with h | h
            · exact Or.inl (List.mem_cons.mpr (Or.inr h))
            · exact Or.inr (List.mem_flatMap.mpr
                (by rcases List.mem_flatMap.mp h with ⟨v, hv, hx⟩
                    exact ⟨v, by simp [hv], hx⟩))

/-- Cake's `mem_var_prog_transform_eoc`
    (`cakeml/pancake/proofs/crep_inlineProofScript.sml:2241`): ending the call
    at end-of-call summaries only introduces the return variables. -/
theorem crepVarProg_transformEoc (returnNames : List Nat) (program : CrepProg α) :
    ∀ {x : Nat}, x ∈ crepVarProg (crepTransformEoc returnNames program) →
      x ∈ crepVarProg program ∨ x ∈ returnNames := by
  have haux : ∀ (program : CrepProg α), ∀ {x : Nat},
      x ∈ crepVarProg (crepTransformEoc returnNames program) →
        x ∈ crepVarProg program ++ returnNames := by
    apply crepTransformEoc.induct (motive := fun program =>
      ∀ {x : Nat}, x ∈ crepVarProg (crepTransformEoc returnNames program) →
        x ∈ crepVarProg program ++ returnNames)
    · intro values x hmem
      simp only [crepTransformEoc] at hmem
      rcases crepVarProg_nestedSeq_assign_zipWith returnNames values hmem with h | h
      · simp only [crepVarProg, List.mem_append]; exact Or.inr h
      · simp only [crepVarProg, List.mem_append]; exact Or.inl h
    · intro name arguments x hmem
      simp only [crepTransformEoc, crepVarProg, List.mem_append] at hmem ⊢
      exact hmem
    · intro names name arguments x hmem
      simp only [crepTransformEoc, crepVarProg, List.mem_append] at hmem ⊢
      exact Or.inl hmem
    · intro names handler body name arguments ih x hmem
      simp only [crepTransformEoc, crepVarProg, List.mem_append] at hmem ⊢
      rcases hmem with h | h
      · exact Or.inl (Or.inl h)
      · rcases List.mem_append.mp (ih h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
    · intro name value body ih x hmem
      simp only [crepTransformEoc, crepVarProg, List.mem_append] at hmem ⊢
      rcases hmem with h | h
      · exact Or.inl (Or.inl h)
      · rcases List.mem_append.mp (ih h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
    · intro condition body ih x hmem
      simp only [crepTransformEoc, crepVarProg, List.mem_append] at hmem ⊢
      rcases hmem with h | h
      · exact Or.inl (Or.inl h)
      · rcases List.mem_append.mp (ih h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
    · intro first second ihFirst ihSecond x hmem
      simp only [crepTransformEoc, crepVarProg, List.mem_append] at hmem ⊢
      rcases hmem with h | h
      · rcases List.mem_append.mp (ihFirst h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases List.mem_append.mp (ihSecond h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
    · intro condition thenBranch elseBranch ihThen ihElse x hmem
      simp only [crepTransformEoc, crepVarProg, List.mem_append] at hmem ⊢
      rcases hmem with h | h
      · rcases h with h | h
        · exact Or.inl (Or.inl (Or.inl h))
        · rcases List.mem_append.mp (ihThen h) with h' | h'
          · exact Or.inl (Or.inl (Or.inr h'))
          · exact Or.inr h'
      · rcases List.mem_append.mp (ihElse h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
    · intro program h1 h2 h3 h4 h5 h6 h7 h8 x hmem
      cases program <;> simp_all [crepTransformEoc, List.mem_append]
  intro x hmem
  exact List.mem_append.mp (haux program hmem)

/-- Cake's `mem_var_prog_transform_branch`
    (`cakeml/pancake/proofs/crep_inlineProofScript.sml:2258`): ending the call
    at branch summaries only introduces the return variables. -/
theorem crepVarProg_transformBranch (loopDepth : Nat) (returnNames : List Nat)
    (program : CrepProg α) :
    ∀ {x : Nat}, x ∈ crepVarProg (crepTransformBranch loopDepth returnNames program) →
      x ∈ crepVarProg program ∨ x ∈ returnNames := by
  have haux : ∀ (loopDepth : Nat) (program : CrepProg α), ∀ {x : Nat},
      x ∈ crepVarProg (crepTransformBranch loopDepth returnNames program) →
        x ∈ crepVarProg program ++ returnNames := by
    apply crepTransformBranch.induct (motive := fun loopDepth program =>
      ∀ {x : Nat}, x ∈ crepVarProg (crepTransformBranch loopDepth returnNames program) →
        x ∈ crepVarProg program ++ returnNames)
    · intro loopDepth values x hmem
      simp only [crepTransformBranch, crepVarProg, List.append_nil] at hmem
      rcases crepVarProg_nestedSeq_assign_zipWith returnNames values hmem with h | h
      · simp only [crepVarProg, List.mem_append]; exact Or.inr h
      · simp only [crepVarProg, List.mem_append]; exact Or.inl h
    · intro loopDepth name arguments x hmem
      simp only [crepTransformBranch, crepVarProg, List.append_nil,
        List.mem_append] at hmem ⊢
      exact hmem
    · intro loopDepth names name arguments x hmem
      simp only [crepTransformBranch, crepVarProg, List.mem_append] at hmem ⊢
      exact Or.inl hmem
    · intro loopDepth names handler body name arguments ih x hmem
      simp only [crepTransformBranch, crepVarProg, List.mem_append] at hmem ⊢
      rcases hmem with h | h
      · exact Or.inl (Or.inl h)
      · rcases List.mem_append.mp (ih h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
    · intro loopDepth name value body ih x hmem
      simp only [crepTransformBranch, crepVarProg, List.mem_append] at hmem ⊢
      rcases hmem with h | h
      · exact Or.inl (Or.inl h)
      · rcases List.mem_append.mp (ih h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
    · intro loopDepth condition body ih x hmem
      simp only [crepTransformBranch, crepVarProg, List.mem_append] at hmem ⊢
      rcases hmem with h | h
      · exact Or.inl (Or.inl h)
      · rcases List.mem_append.mp (ih h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
    · intro loopDepth first second ihFirst ihSecond x hmem
      simp only [crepTransformBranch, crepVarProg, List.mem_append] at hmem ⊢
      rcases hmem with h | h
      · rcases List.mem_append.mp (ihFirst h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases List.mem_append.mp (ihSecond h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
    · intro loopDepth condition thenBranch elseBranch ihThen ihElse x hmem
      simp only [crepTransformBranch, crepVarProg, List.mem_append] at hmem ⊢
      rcases hmem with h | h
      · rcases h with h | h
        · exact Or.inl (Or.inl (Or.inl h))
        · rcases List.mem_append.mp (ihThen h) with h' | h'
          · exact Or.inl (Or.inl (Or.inr h'))
          · exact Or.inr h'
      · rcases List.mem_append.mp (ihElse h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
    · intro loopDepth program h1 h2 h3 h4 h5 h6 h7 h8 x hmem
      cases program <;> simp_all [crepTransformBranch, List.mem_append]
  intro x hmem
  exact List.mem_append.mp (haux loopDepth program hmem)

theorem crepUnreachElim_preserve_hasReturn (program : CrepProg α) :
    crepHasReturn program = false →
      ∀ {q : CrepProg α} {r : Option CrepEarlyExit},
        crepUnreachElim program = (q, r) → crepHasReturn q = false := by
  have h : ∀ (n : Nat) (program : CrepProg α), sizeOf program < n →
      crepHasReturn program = false →
        ∀ {q : CrepProg α} {r : Option CrepEarlyExit},
          crepUnreachElim program = (q, r) → crepHasReturn q = false := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro program hlt hh q r he
      cases program with
      | «skip» =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «dec» name value body =>
        have hbody : crepHasReturn body = false := by
          simpa [crepHasReturn] using hh
        rw [crepUnreachElim.eq_def] at he
        dsimp only at he
        cases hebody : crepUnreachElim body with
        | mk body' bodyExit =>
          rw [hebody] at he
          cases he
          have hsub : sizeOf body < sizeOf (CrepProg.dec name value body : CrepProg α) := by
            decreasing_trivial
          have hres := ih (sizeOf (CrepProg.dec name value body : CrepProg α)) hlt
            body hsub hbody hebody
          simpa [crepHasReturn] using hres
      | «assign» name value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «primitive» names operator args =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «store» address value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «store32» address value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «storeByte» address value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «storeGlob» address value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «seq» first second =>
        have hparts : crepHasReturn first = false ∧ crepHasReturn second = false := by
          simpa [crepHasReturn] using hh
        rw [crepUnreachElim.eq_def] at he
        dsimp only at he
        cases hfirst : crepUnreachElim first with
        | mk first' firstExit =>
          rw [hfirst] at he
          by_cases hsome : firstExit.isSome = true
          · simp only [hsome] at he
            cases he
            have hsub : sizeOf first < sizeOf (CrepProg.seq first second : CrepProg α) := by
              decreasing_trivial
            have hres := ih (sizeOf (CrepProg.seq first second : CrepProg α)) hlt
              first hsub hparts.1 hfirst
            simpa [crepHasReturn] using hres
          · simp only [hsome] at he
            cases hsecond : crepUnreachElim second with
            | mk second' secondExit =>
              rw [hsecond] at he
              cases he
              have hsub1 : sizeOf first < sizeOf (CrepProg.seq first second : CrepProg α) := by
                decreasing_trivial
              have hsub2 : sizeOf second < sizeOf (CrepProg.seq first second : CrepProg α) := by
                decreasing_trivial
              have h1 := ih (sizeOf (CrepProg.seq first second : CrepProg α)) hlt
                first hsub1 hparts.1 hfirst
              have h2 := ih (sizeOf (CrepProg.seq first second : CrepProg α)) hlt
                second hsub2 hparts.2 hsecond
              simp [crepHasReturn, h1, h2]
      | «ite» condition thenBranch elseBranch =>
        have hparts : crepHasReturn thenBranch = false ∧ crepHasReturn elseBranch = false := by
          simpa [crepHasReturn] using hh
        rw [crepUnreachElim.eq_def] at he
        dsimp only at he
        cases hthen : crepUnreachElim thenBranch with
        | mk then' thenExit =>
          rw [hthen] at he
          dsimp only at he
          cases helse : crepUnreachElim elseBranch with
          | mk else' elseExit =>
            rw [helse] at he
            cases he
            have hsub1 : sizeOf thenBranch <
                sizeOf (CrepProg.ite condition thenBranch elseBranch : CrepProg α) := by
              decreasing_trivial
            have hsub2 : sizeOf elseBranch <
                sizeOf (CrepProg.ite condition thenBranch elseBranch : CrepProg α) := by
              decreasing_trivial
            have h1 := ih (sizeOf (CrepProg.ite condition thenBranch elseBranch : CrepProg α))
              hlt thenBranch hsub1 hparts.1 hthen
            have h2 := ih (sizeOf (CrepProg.ite condition thenBranch elseBranch : CrepProg α))
              hlt elseBranch hsub2 hparts.2 helse
            simp [crepHasReturn, h1, h2]
      | «while» condition body =>
        have hbody : crepHasReturn body = false := by
          simpa [crepHasReturn] using hh
        rw [crepUnreachElim.eq_def] at he
        dsimp only at he
        cases hbody' : crepUnreachElim body with
        | mk body' bodyExit =>
          rw [hbody'] at he
          cases he
          have hsub : sizeOf body < sizeOf (CrepProg.while condition body : CrepProg α) := by
            decreasing_trivial
          have hres := ih (sizeOf (CrepProg.while condition body : CrepProg α)) hlt
            body hsub hbody hbody'
          simpa [crepHasReturn] using hres
      | «break» label =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «continue» label =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «call» returnInfo name args =>
        cases returnInfo with
        | none =>
          rw [crepUnreachElim.eq_def] at he
          cases he
          exact hh
        | some pair =>
          obtain ⟨names, rest⟩ := pair
          cases rest with
          | none =>
            rw [crepUnreachElim.eq_def] at he
            cases he
            exact hh
          | some hr =>
            obtain ⟨handler, body⟩ := hr
            have hbody : crepHasReturn body = false := by
              simpa [crepHasReturn] using hh
            rw [crepUnreachElim.eq_def] at he
            dsimp only at he
            cases hbody' : crepUnreachElim body with
            | mk body' bodyExit =>
              rw [hbody'] at he
              cases he
              have hsub : sizeOf body <
                  sizeOf (CrepProg.call (some (names, some (handler, body)))
                    name args : CrepProg α) := by
                decreasing_trivial
              have hres := ih (sizeOf (CrepProg.call (some (names, some (handler, body)))
                name args : CrepProg α)) hlt body hsub hbody hbody'
              simpa [crepHasReturn] using hres
      | «extCall» function configuration configurationLength array arrayLength =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «raise» exception =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «return» values =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «shMem» operator name address =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «tick» =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
  intro hh q r he
  exact h (sizeOf program + 1) program (Nat.lt_succ_self _) hh he

theorem crepUnreachElim_preserve_notBranchRet (program : CrepProg α) :
    crepNotBranchRet program = true →
      ∀ {q : CrepProg α} {r : Option CrepEarlyExit},
        crepUnreachElim program = (q, r) → crepNotBranchRet q = true := by
  have h : ∀ (n : Nat) (program : CrepProg α), sizeOf program < n →
      crepNotBranchRet program = true →
        ∀ {q : CrepProg α} {r : Option CrepEarlyExit},
          crepUnreachElim program = (q, r) → crepNotBranchRet q = true := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro program hlt hh q r he
      cases program with
      | «skip» =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «dec» name value body =>
        have hbody : crepNotBranchRet body = true := by
          simpa [crepNotBranchRet] using hh
        rw [crepUnreachElim.eq_def] at he
        dsimp only at he
        cases hebody : crepUnreachElim body with
        | mk body' bodyExit =>
          rw [hebody] at he
          cases he
          have hsub : sizeOf body < sizeOf (CrepProg.dec name value body : CrepProg α) := by
            decreasing_trivial
          have hres := ih (sizeOf (CrepProg.dec name value body : CrepProg α)) hlt
            body hsub hbody hebody
          simpa [crepNotBranchRet] using hres
      | «assign» name value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «primitive» names operator args =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «store» address value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «store32» address value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «storeByte» address value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «storeGlob» address value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «seq» first second =>
        have hparts : crepNotBranchRet first = true ∧ crepNotBranchRet second = true := by
          simpa [crepNotBranchRet] using hh
        rw [crepUnreachElim.eq_def] at he
        dsimp only at he
        cases hfirst : crepUnreachElim first with
        | mk first' firstExit =>
          rw [hfirst] at he
          by_cases hsome : firstExit.isSome = true
          · simp only [hsome] at he
            cases he
            have hsub : sizeOf first < sizeOf (CrepProg.seq first second : CrepProg α) := by
              decreasing_trivial
            have hres := ih (sizeOf (CrepProg.seq first second : CrepProg α)) hlt
              first hsub hparts.1 hfirst
            simpa [crepNotBranchRet] using hres
          · simp only [hsome] at he
            cases hsecond : crepUnreachElim second with
            | mk second' secondExit =>
              rw [hsecond] at he
              cases he
              have hsub1 : sizeOf first < sizeOf (CrepProg.seq first second : CrepProg α) := by
                decreasing_trivial
              have hsub2 : sizeOf second < sizeOf (CrepProg.seq first second : CrepProg α) := by
                decreasing_trivial
              have h1 := ih (sizeOf (CrepProg.seq first second : CrepProg α)) hlt
                first hsub1 hparts.1 hfirst
              have h2 := ih (sizeOf (CrepProg.seq first second : CrepProg α)) hlt
                second hsub2 hparts.2 hsecond
              simp [crepNotBranchRet, h1, h2]
      | «ite» condition thenBranch elseBranch =>
        have hparts : (!crepHasReturn thenBranch) = true ∧ (!crepHasReturn elseBranch) = true := by
          simpa [crepNotBranchRet] using hh
        rw [crepUnreachElim.eq_def] at he
        dsimp only at he
        cases hthen : crepUnreachElim thenBranch with
        | mk then' thenExit =>
          rw [hthen] at he
          dsimp only at he
          cases helse : crepUnreachElim elseBranch with
          | mk else' elseExit =>
            rw [helse] at he
            cases he
            have hthenFalse : crepHasReturn thenBranch = false := by simpa using hparts.1
            have helseFalse : crepHasReturn elseBranch = false := by simpa using hparts.2
            have hthen' := crepUnreachElim_preserve_hasReturn thenBranch hthenFalse hthen
            have helse' := crepUnreachElim_preserve_hasReturn elseBranch helseFalse helse
            simp [crepNotBranchRet, hthen', helse']
      | «while» condition body =>
        have hparts : (!crepHasReturn body) = true := by
          simpa [crepNotBranchRet] using hh
        rw [crepUnreachElim.eq_def] at he
        dsimp only at he
        cases hbody' : crepUnreachElim body with
        | mk body' bodyExit =>
          rw [hbody'] at he
          cases he
          have hbodyFalse : crepHasReturn body = false := by simpa using hparts
          have hres := crepUnreachElim_preserve_hasReturn body hbodyFalse hbody'
          simp [crepNotBranchRet, hres]
      | «break» label =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «continue» label =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «call» returnInfo name args =>
        cases returnInfo with
        | none =>
          rw [crepUnreachElim.eq_def] at he
          cases he
          exact hh
        | some pair =>
          obtain ⟨names, rest⟩ := pair
          cases rest with
          | none =>
            rw [crepUnreachElim.eq_def] at he
            cases he
            exact hh
          | some hr =>
            obtain ⟨handler, body⟩ := hr
            have hparts : (!crepHasReturn body) = true := by
              simpa [crepNotBranchRet] using hh
            rw [crepUnreachElim.eq_def] at he
            dsimp only at he
            cases hbody' : crepUnreachElim body with
            | mk body' bodyExit =>
              rw [hbody'] at he
              cases he
              have hbodyFalse : crepHasReturn body = false := by simpa using hparts
              have hres := crepUnreachElim_preserve_hasReturn body hbodyFalse hbody'
              simp [crepNotBranchRet, hres]
      | «extCall» function configuration configurationLength array arrayLength =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «raise» exception =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «return» values =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «shMem» operator name address =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
      | «tick» =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        exact hh
  intro hh q r he
  exact h (sizeOf program + 1) program (Nat.lt_succ_self _) hh he

/-! CakeML's `crep_inlineProofScript.sml` `unreach_elim_nested_decs` (:1697),
    `unreach_elim_arg_load` (:1709) and `unreach_elim_arg_load_perm` (:1720):
    wrapping an `unreach_elim` fixpoint in nested declarations preserves the
    fixpoint and its reported early exit. -/

theorem crepUnreachElim_dec_fixpoint (name : Nat) (value : CrepExp α) (program : CrepProg α)
    (r : Option CrepEarlyExit)
    (hfix : crepUnreachElim program = (program, r)) :
    crepUnreachElim (.dec name value program) = (.dec name value program, r) := by
  rw [crepUnreachElim.eq_def]
  dsimp only
  rw [hfix]

theorem crepUnreachElim_nestedDecs (names : List Nat) (values : List (CrepExp α))
    (program : CrepProg α) (r : Option CrepEarlyExit)
    (hlen : names.length = values.length)
    (hfix : crepUnreachElim program = (program, r)) :
    crepUnreachElim (nestedDecs names values program) =
      (nestedDecs names values program, r) := by
  induction names generalizing values program r with
  | nil =>
      cases values with
      | nil => simpa [nestedDecs] using hfix
      | cons value values => simp at hlen
  | cons name names ih =>
      cases values with
      | nil => simp at hlen
      | cons value values =>
          simp only [nestedDecs]
          exact crepUnreachElim_dec_fixpoint name value
            (nestedDecs names values program) r
            (ih values program r (by simpa using hlen) hfix)

theorem crepUnreachElim_argLoad (program : CrepProg α) (tmpVars : List Nat)
    (args : List (CrepExp α)) (argsVName : List Nat) (r : Option CrepEarlyExit)
    (hlen1 : tmpVars.length = args.length)
    (hlen2 : args.length = argsVName.length)
    (hfix : crepUnreachElim program = (program, r)) :
    crepUnreachElim (argLoad tmpVars args argsVName program) =
      (argLoad tmpVars args argsVName program, r) := by
  unfold argLoad
  have hinner : crepUnreachElim
      (nestedDecs argsVName (tmpVars.map CrepExp.var) program) =
      (nestedDecs argsVName (tmpVars.map CrepExp.var) program, r) :=
    crepUnreachElim_nestedDecs argsVName (tmpVars.map CrepExp.var) program r
      (by rw [List.length_map]; omega) hfix
  exact crepUnreachElim_nestedDecs tmpVars args
    (nestedDecs argsVName (tmpVars.map CrepExp.var) program) r hlen1 hinner

theorem crepUnreachElim_argLoad_perm (program : CrepProg α) (tmpVars : List Nat)
    (args : List (CrepExp α)) (argsVName : List Nat) (r : Option CrepEarlyExit)
    (hlen1 : tmpVars.length = argsVName.length)
    (hlen2 : args.length = argsVName.length)
    (hfix : crepUnreachElim program = (program, r)) :
    crepUnreachElim (argLoad tmpVars args argsVName program) =
      (argLoad tmpVars args argsVName program, r) :=
  crepUnreachElim_argLoad program tmpVars args argsVName r
    (by omega) hlen2 hfix


 /-! Kernel-checked port of CakeML's `unreach_elim_converge`
    (`crep_inlineProofScript.sml:1663`): re-running unreachable-code elimination
    on its own output is a no-op, so the pair returned by `crepUnreachElim` is a
    fixed point.  Cake proves this by `recInduct unreach_elim_ind`; here the
    measure is `sizeOf`, matching the well-founded definition. -/

theorem crepUnreachElim_converge (program : CrepProg α) :
    ∀ {q : CrepProg α} {r : Option CrepEarlyExit},
      crepUnreachElim program = (q, r) → crepUnreachElim q = (q, r) := by
  have h : ∀ (n : Nat) (program : CrepProg α), sizeOf program < n →
      ∀ {q : CrepProg α} {r : Option CrepEarlyExit},
        crepUnreachElim program = (q, r) → crepUnreachElim q = (q, r) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro program hlt q r he
      cases program with
      | «skip» =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «dec» name value body =>
        rw [crepUnreachElim.eq_def] at he
        dsimp only at he
        cases hbody : crepUnreachElim body with
        | mk body' bodyExit =>
          rw [hbody] at he
          cases he
          have hsub : sizeOf body < sizeOf (CrepProg.dec name value body : CrepProg α) := by
            decreasing_trivial
          have hres := ih (sizeOf (CrepProg.dec name value body : CrepProg α)) hlt
            body hsub hbody
          rw [crepUnreachElim.eq_def]
          dsimp only
          rw [hres]
      | «assign» name value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «primitive» names operator args =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «store» address value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «store32» address value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «storeByte» address value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «storeGlob» address value =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «seq» first second =>
        rw [crepUnreachElim.eq_def] at he
        dsimp only at he
        cases hfirst : crepUnreachElim first with
        | mk first' firstExit =>
          rw [hfirst] at he
          cases firstExit with
          | some firstExitValue =>
            simp only [Option.isSome_some, if_true] at he
            cases he
            have hsub : sizeOf first < sizeOf (CrepProg.seq first second : CrepProg α) := by
              decreasing_trivial
            exact ih (sizeOf (CrepProg.seq first second : CrepProg α)) hlt first hsub hfirst
          | none =>
            simp only [Option.isSome_none, Bool.false_eq_true, if_false] at he
            cases hsecond : crepUnreachElim second with
            | mk second' secondExit =>
              rw [hsecond] at he
              cases he
              have hsub1 : sizeOf first < sizeOf (CrepProg.seq first second : CrepProg α) := by
                decreasing_trivial
              have hsub2 : sizeOf second < sizeOf (CrepProg.seq first second : CrepProg α) := by
                decreasing_trivial
              have h1 := ih (sizeOf (CrepProg.seq first second : CrepProg α)) hlt first hsub1 hfirst
              have h2 := ih (sizeOf (CrepProg.seq first second : CrepProg α)) hlt second hsub2 hsecond
              rw [crepUnreachElim.eq_def]
              dsimp only
              rw [h1]
              simp only [Option.isSome_none, Bool.false_eq_true, if_false]
              rw [h2]
      | «ite» condition thenBranch elseBranch =>
        rw [crepUnreachElim.eq_def] at he
        dsimp only at he
        cases hthen : crepUnreachElim thenBranch with
        | mk then' thenExit =>
          rw [hthen] at he
          dsimp only at he
          cases helse : crepUnreachElim elseBranch with
          | mk else' elseExit =>
            rw [helse] at he
            cases he
            have hsub1 : sizeOf thenBranch <
                sizeOf (CrepProg.ite condition thenBranch elseBranch : CrepProg α) := by
              decreasing_trivial
            have hsub2 : sizeOf elseBranch <
                sizeOf (CrepProg.ite condition thenBranch elseBranch : CrepProg α) := by
              decreasing_trivial
            have h1 := ih (sizeOf (CrepProg.ite condition thenBranch elseBranch : CrepProg α))
              hlt thenBranch hsub1 hthen
            have h2 := ih (sizeOf (CrepProg.ite condition thenBranch elseBranch : CrepProg α))
              hlt elseBranch hsub2 helse
            rw [crepUnreachElim.eq_def]
            dsimp only
            rw [h1]
            dsimp only
            rw [h2]
      | «while» condition body =>
        rw [crepUnreachElim.eq_def] at he
        dsimp only at he
        cases hbody : crepUnreachElim body with
        | mk body' bodyExit =>
          rw [hbody] at he
          dsimp only at he
          cases he
          have hsub : sizeOf body < sizeOf (CrepProg.while condition body : CrepProg α) := by
            decreasing_trivial
          have hres := ih (sizeOf (CrepProg.while condition body : CrepProg α)) hlt
            body hsub hbody
          rw [crepUnreachElim.eq_def]
          dsimp only
          rw [hres]
      | «break» label =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «continue» label =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «call» returnInfo name args =>
        cases returnInfo with
        | none =>
          rw [crepUnreachElim.eq_def] at he
          cases he
          simp [crepUnreachElim]
        | some pair =>
          obtain ⟨names, rest⟩ := pair
          cases rest with
          | none =>
            rw [crepUnreachElim.eq_def] at he
            cases he
            simp [crepUnreachElim]
          | some hr =>
            obtain ⟨handler, body⟩ := hr
            rw [crepUnreachElim.eq_def] at he
            dsimp only at he
            cases hbody : crepUnreachElim body with
            | mk body' bodyExit =>
              rw [hbody] at he
              dsimp only at he
              cases he
              have hsub : sizeOf body <
                  sizeOf (CrepProg.call (some (names, some (handler, body)))
                    name args : CrepProg α) := by
                decreasing_trivial
              have hres := ih (sizeOf (CrepProg.call (some (names, some (handler, body)))
                name args : CrepProg α)) hlt body hsub hbody
              rw [crepUnreachElim.eq_def]
              dsimp only
              rw [hres]
      | «extCall» function configuration configurationLength array arrayLength =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «raise» exception =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «return» values =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «shMem» operator name address =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
      | «tick» =>
        rw [crepUnreachElim.eq_def] at he
        cases he
        simp [crepUnreachElim]
  intro q r he
  exact h (sizeOf program + 1) program (Nat.lt_succ_self _) he

 /-! Kernel-checked port of CakeML's `unreach_elim_fix_point`
    (`crep_inlineProofScript.sml:1686`): the range of `crepUnreachElim` is
    exactly its fixed-point set. -/

theorem crepUnreachElim_fixPoint (q : CrepProg α) (r : Option CrepEarlyExit) :
    (∃ p : CrepProg α, crepUnreachElim p = (q, r)) ↔
      crepUnreachElim q = (q, r) := by
  constructor
  · rintro ⟨p, hp⟩
    exact crepUnreachElim_converge p hp
  · intro hq
    exact ⟨q, hq⟩

end Flapjack
