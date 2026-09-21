import Flapjack.PanSimp
import Flapjack.CrepeExpressionRelation
import Flapjack.PanToCrepCorrectnessBoundary
import Flapjack.PanProgramSimp

/-!
`pan_simp` only inserts `Skip`, `Seq`, and `Annot` nodes and rewrites the
`AssignCall`/`Return` shape into a destination-free tail call.  None of these
introduce global-variable reads, so the localisation invariant `localisedProg`
used by the Pancake-to-Crep boundary is preserved by the whole pass.  This is
the source-side ingredient of Cake's `mk_ctxt_code_imp_code_rel`
(`pan_to_crepProofScript.sml`), which requires the compiled code to consist of
localised programs.
-/

namespace Flapjack

theorem localisedProg_skip : localisedProg (.skip : Prog α) := by
  simp [localisedProg]

theorem localisedProg_annot (tag text : String) :
    localisedProg (.annot tag text : Prog α) := by
  simp [localisedProg]

theorem localisedProg_smartSeq (pre program : Prog α)
    (hpre : localisedProg pre) (hprogram : localisedProg program) :
    localisedProg (smartSeq pre program) := by
  unfold smartSeq
  split
  · exact hprogram
  · exact ⟨hpre, hprogram⟩

theorem localisedProg_seqCallRet (program : Prog α) (h : localisedProg program) :
    localisedProg (seqCallRet program) := by
  unfold seqCallRet
  split
  · split
    · simp only [localisedProg] at h ⊢
      exact ⟨h.1.1, trivial⟩
    · exact h
  · exact h

theorem localisedProg_seqAssoc (pre program : Prog α)
    (hpre : localisedProg pre) (hprogram : localisedProg program) :
    localisedProg (seqAssoc pre program) := by
  let rec go (pre : Prog α) (hpre : localisedProg pre) : (program : Prog α) →
      localisedProg program → localisedProg (seqAssoc pre program)
    | .skip => by
        intro _
        simp only [seqAssoc]
        exact hpre
    | .dec name shape value body => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.dec name shape value (seqAssoc .skip body))
          hpre (by
            simp only [localisedProg] at hprogram ⊢
            exact ⟨hprogram.1, go .skip localisedProg_skip body hprogram.2⟩)
    | .seq first second => by
        intro hprogram
        simp only [seqAssoc]
        simp only [localisedProg] at hprogram
        exact go (seqAssoc pre first) (go pre hpre first hprogram.1) second hprogram.2
    | .ite condition thenBranch elseBranch => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre
          (.ite condition (seqAssoc .skip thenBranch) (seqAssoc .skip elseBranch))
          hpre (by
            simp only [localisedProg] at hprogram ⊢
            exact ⟨hprogram.1, go .skip localisedProg_skip thenBranch hprogram.2.1,
              go .skip localisedProg_skip elseBranch hprogram.2.2⟩)
    | .while condition body => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.while condition (seqAssoc .skip body))
          hpre (by
            simp only [localisedProg] at hprogram ⊢
            exact ⟨hprogram.1, go .skip localisedProg_skip body hprogram.2⟩)
    | .call info function arguments => by
        intro hprogram
        cases info with
        | none =>
            simp only [seqAssoc]
            exact localisedProg_smartSeq pre (.call none function arguments) hpre hprogram
        | some info =>
            cases info with
            | mk returns handlerInfo =>
                cases returns with
                | none =>
                    cases handlerInfo with
                    | none =>
                        simp only [seqAssoc]
                        exact localisedProg_smartSeq pre
                          (.call (some (none, none)) function arguments) hpre hprogram
                    | some handler =>
                        cases handler with
                        | mk exception handlerInfo =>
                            cases handlerInfo with
                            | mk handlerVar handlerProgram =>
                                simp only [seqAssoc]
                                refine localisedProg_smartSeq pre _ hpre ?_
                                simp only [localisedProg] at hprogram ⊢
                                exact ⟨hprogram.1,
                                  go .skip localisedProg_skip handlerProgram hprogram.2⟩
                | some ret =>
                    cases ret with
                    | mk kind name =>
                        cases kind with
                        | «local» =>
                            cases handlerInfo with
                            | none =>
                                simp only [seqAssoc]
                                exact localisedProg_smartSeq pre
                                  (.call (some (some (.local, name), none)) function arguments)
                                  hpre hprogram
                            | some handler =>
                                cases handler with
                                | mk exception handlerInfo =>
                                    cases handlerInfo with
                                    | mk handlerVar handlerProgram =>
                                        simp only [seqAssoc]
                                        refine localisedProg_smartSeq pre _ hpre ?_
                                        simp only [localisedProg] at hprogram ⊢
                                        exact ⟨hprogram.1,
                                          go .skip localisedProg_skip handlerProgram
                                            hprogram.2⟩
                        | «global» =>
                            simp only [localisedProg] at hprogram
                            exact hprogram.2.elim
    | .decCall name shape function arguments body => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre
          (.decCall name shape function arguments (seqAssoc .skip body))
          hpre (by
            simp only [localisedProg] at hprogram ⊢
            exact ⟨hprogram.1, go .skip localisedProg_skip body hprogram.2⟩)
    | .annot tag text => by
        intro _
        simp only [seqAssoc]
        exact hpre
    | .assign kind name value => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.assign kind name value) hpre hprogram
    | .primitive name operator args => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.primitive name operator args) hpre hprogram
    | .store address value => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.store address value) hpre hprogram
    | .store32 address value => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.store32 address value) hpre hprogram
    | .storeByte address value => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.storeByte address value) hpre hprogram
    | .break => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.break : Prog α) hpre hprogram
    | .continue => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.continue : Prog α) hpre hprogram
    | .extCall function configuration configurationLength array arrayLength => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre
          (.extCall function configuration configurationLength array arrayLength)
          hpre hprogram
    | .raise exception value => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.raise exception value) hpre hprogram
    | .return value => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.return value) hpre hprogram
    | .shMemLoad size kind name address => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.shMemLoad size kind name address) hpre hprogram
    | .shMemStore size address value => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.shMemStore size address value) hpre hprogram
    | .tick => by
        intro hprogram
        simp only [seqAssoc]
        exact localisedProg_smartSeq pre (.tick : Prog α) hpre hprogram
  exact go pre hpre program hprogram

theorem localisedProg_retToTail (program : Prog α) (h : localisedProg program) :
    localisedProg (retToTail program) := by
  let rec go : (program : Prog α) → localisedProg program →
      localisedProg (retToTail program)
    | .skip => by
        intro _
        simp only [retToTail]
        exact localisedProg_skip
    | .dec name shape value body => by
        intro hprogram
        simp only [retToTail]
        simp only [localisedProg] at hprogram ⊢
        exact ⟨hprogram.1, go body hprogram.2⟩
    | .seq first second => by
        intro hprogram
        simp only [retToTail]
        simp only [localisedProg] at hprogram
        exact localisedProg_seqCallRet _
          ⟨go first hprogram.1, go second hprogram.2⟩
    | .ite condition thenBranch elseBranch => by
        intro hprogram
        simp only [retToTail]
        simp only [localisedProg] at hprogram ⊢
        exact ⟨hprogram.1, go thenBranch hprogram.2.1, go elseBranch hprogram.2.2⟩
    | .while condition body => by
        intro hprogram
        simp only [retToTail]
        simp only [localisedProg] at hprogram ⊢
        exact ⟨hprogram.1, go body hprogram.2⟩
    | .call info function arguments => by
        intro hprogram
        cases info with
        | none =>
            simp only [retToTail]
            exact hprogram
        | some info =>
            cases info with
            | mk returns handlerInfo =>
                cases returns with
                | none =>
                    cases handlerInfo with
                    | none =>
                        simp only [retToTail]
                        exact hprogram
                    | some handler =>
                        cases handler with
                        | mk exception handlerInfo =>
                            cases handlerInfo with
                            | mk handlerVar handlerProgram =>
                                simp only [retToTail]
                                simp only [localisedProg] at hprogram ⊢
                                exact ⟨hprogram.1, go handlerProgram hprogram.2⟩
                | some ret =>
                    cases ret with
                    | mk kind name =>
                        cases kind with
                        | «local» =>
                            cases handlerInfo with
                            | none =>
                                simp only [retToTail]
                                exact hprogram
                            | some handler =>
                                cases handler with
                                | mk exception handlerInfo =>
                                    cases handlerInfo with
                                    | mk handlerVar handlerProgram =>
                                        simp only [retToTail]
                                        simp only [localisedProg] at hprogram ⊢
                                        exact ⟨hprogram.1, go handlerProgram hprogram.2⟩
                        | «global» =>
                            simp only [localisedProg] at hprogram
                            exact hprogram.2.elim
    | .decCall name shape function arguments body => by
        intro hprogram
        simp only [retToTail]
        simp only [localisedProg] at hprogram ⊢
        exact ⟨hprogram.1, go body hprogram.2⟩
    | .annot tag text => by
        intro _
        simp only [retToTail]
        exact localisedProg_annot tag text
    | .assign kind name value => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
    | .primitive name operator args => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
    | .store address value => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
    | .store32 address value => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
    | .storeByte address value => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
    | .break => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
    | .continue => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
    | .extCall function configuration configurationLength array arrayLength => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
    | .raise exception value => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
    | .return value => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
    | .shMemLoad size kind name address => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
    | .shMemStore size address value => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
    | .tick => by
        intro hprogram
        simp only [retToTail]
        exact hprogram
  exact go program h

theorem localisedProg_panSimpProg (program : Prog α) (h : localisedProg program) :
    localisedProg (panSimpProg program) := by
  unfold panSimpProg
  exact localisedProg_retToTail _ (localisedProg_seqAssoc .skip program
    localisedProg_skip h)

/-! The code-level invariant used by the Pancake-to-Crep boundary
(`panValuePcLocalisedCode`, `Flapjack/PanToCrepCorrectnessBoundary.lean`) is
preserved by the `pan_simp` function-table transform. -/

theorem panValuePcLocalisedCode_panValueFunctionsSimp
    (code : PanValuePcSourceCode α)
    (h : panValuePcLocalisedCode code) :
    panValuePcLocalisedCode (panValueFunctionsSimp code) := by
  induction code with
  | nil =>
      intro entry hentry
      simp [panValueFunctionsSimp] at hentry
  | cons head rest ih =>
      intro entry hentry
      obtain ⟨name, parameters, body⟩ := head
      simp only [panValueFunctionsSimp, List.mem_cons] at hentry
      rcases hentry with rfl | hrest
      · exact localisedProg_panSimpProg body (h (name, parameters, body) (by simp))
      · exact ih (fun e he => h e (by simp [he])) entry hrest

end Flapjack
