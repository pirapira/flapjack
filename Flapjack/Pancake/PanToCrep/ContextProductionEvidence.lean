import Flapjack.FiniteMap
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.ContextBridge

/-!
Finite support and byte-range evidence for Pan-to-Crep contexts constructed by
the production list-update helpers.  The range premise is the parser/compiler
invariant `DeclByteRanged`; it is not assumed for arbitrary production syntax.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

private theorem updateList_lookup_has_entry [BEq α] [LawfulBEq α]
    (entries : List (α × β)) (key : α) (value : β)
    (h : FLOOKUP (FUPDATE_LIST FEMPTY entries) key = some value) :
    ∃ entry, entry ∈ entries ∧ entry.1 = key ∧ entry.2 = value := by
  rcases flookupFupdateList_mem_or_base FEMPTY entries key value h with hm | hb
  · exact hm
  · simp [FLOOKUP, FEMPTY] at hb

private theorem compileParamVars_byteRanged
    (params : List (VarName × Shape)) (offset : Nat)
    (hranged : ∀ p ∈ params, ParamByteRanged p) :
    ∀ entry ∈ (compileParamVars params offset).1,
      NameRanged entry.1 ∧ ShapeByteRanged entry.2.1 := by
  induction params generalizing offset with
  | nil => simp [compileParamVars]
  | cons parameter params ih =>
      obtain ⟨name, shape⟩ := parameter
      have hp := hranged (name, shape) (by simp)
      have htail : ∀ p ∈ params, ParamByteRanged p := by
        intro p hp
        exact hranged p (by simp [hp])
      simp only [compileParamVars]
      intro entry hentry
      simp only [List.mem_cons] at hentry
      rcases hentry with hhead | htailMem
      · cases hhead
        exact ⟨hp.1, hp.2⟩
      · exact ih (offset + Shape.shapeSize shape) htail entry htailMem

private theorem functionEntries_byteRanged {width : Nat}
    (declarations : List (Decl (BitVec width)))
    (hranged : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ entry ∈ functionEntries declarations,
      NameRanged entry.1 ∧
        (∀ parameter ∈ entry.2.1,
          NameRanged parameter.1 ∧ ShapeByteRanged parameter.2) ∧
        ShapeByteRanged entry.2.2.2 := by
  induction declarations with
  | nil => simp [functionEntries]
  | cons declaration declarations ih =>
      have htail : ∀ d ∈ declarations, DeclByteRanged d := by
        intro d hd
        exact hranged d (by simp [hd])
      cases declaration with
      | function fd =>
          have hfd := hranged (.function fd) (by simp)
          simp only [DeclByteRanged, FunDeclByteRanged] at hfd
          simp only [functionEntries]
          intro entry hentry
          simp only [List.mem_cons] at hentry
          rcases hentry with hhead | htailMem
          · cases hhead
            exact ⟨hfd.1, hfd.2.1, hfd.2.2.2⟩
          · exact ih htail entry htailMem
      | decl shape name value =>
          simp only [functionEntries]
          exact ih htail
      | exnDecl name shape =>
          simp only [functionEntries]
          exact ih htail
      | name struct fields =>
          simp only [functionEntries]
          exact ih htail

private theorem exceptionEntries_byteRanged {width : Nat}
    (declarations : List (Decl (BitVec width)))
    (hranged : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ entry ∈ exceptionEntries declarations, NameRanged entry.1 := by
  induction declarations with
  | nil => simp [exceptionEntries]
  | cons declaration declarations ih =>
      have htail : ∀ d ∈ declarations, DeclByteRanged d := by
        intro d hd
        exact hranged d (by simp [hd])
      cases declaration with
      | function fd => simpa [exceptionEntries] using ih htail
      | decl shape name value => simpa [exceptionEntries] using ih htail
      | exnDecl name shape =>
          have hd := hranged (.exnDecl name shape) (by simp)
          simp only [DeclByteRanged] at hd
          simp only [exceptionEntries, List.mem_cons]
          intro entry hmem
          rcases hmem with heq | htailMem
          · cases heq
            exact hd.1
          · exact ih htail entry htailMem
      | name struct fields => simpa [exceptionEntries] using ih htail

private theorem panToCrepMakeFuncs_entries_byteRanged {width : Nat}
    (declarations : List (Decl (BitVec width)))
    (hranged : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ entry ∈ (panToCrepMakeFuncs declarations).reverse,
      NameRanged entry.1 ∧
        (∀ parameter ∈ entry.2.1,
          NameRanged parameter.1 ∧ ShapeByteRanged parameter.2) ∧
        ShapeByteRanged entry.2.2 := by
  have hentries : ∀ entry ∈ panToCrepMakeFuncs declarations,
      NameRanged entry.1 ∧
        (∀ parameter ∈ entry.2.1,
          NameRanged parameter.1 ∧ ShapeByteRanged parameter.2) ∧
        ShapeByteRanged entry.2.2 := by
    intro entry hmem
    have hproject := functionEntries_byteRanged declarations hranged
    rw [panToCrepMakeFuncs_eq_map] at hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    rcases hproject source hsource with ⟨hn, hp, hs⟩
    exact ⟨hn, hp, hs⟩
  simpa only [List.mem_reverse] using hentries

private theorem exceptionNames_byteRanged {width : Nat}
    (declarations : List (Decl (BitVec width)))
    (hranged : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ name ∈ (exceptionEntries declarations).map Prod.fst, NameRanged name := by
  intro name hmem
  rcases List.mem_map.mp hmem with ⟨entry, hentry, rfl⟩
  exact exceptionEntries_byteRanged declarations hranged entry hentry

/-- Contexts built by the compiler's `make_vmap`/`make_funcs`/
`get_eids_from_decls` list updates have finite support.  Byte-range evidence
comes from the same `DeclByteRanged` premise supplied by the parser-backed
source path; no claim is made for arbitrary String-backed declarations. -/
theorem panToCrepCompilerContextProductionEvidence {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (params : List (VarName × Shape)) (vmax : Nat)
    (hdecls : ∀ d ∈ declarations, DeclByteRanged d)
    (hparams : ∀ p ∈ params, ParamByteRanged p) :
    PanToCrepContextProductionEvidence
      (panToCrepMkCtxtHOL (panToCrepMakeVmapHOL params)
        (functionInfosHOL declarations) vmax
        (panToCrepGetEidsFromDeclsHOL declarations)) := by
  let context := panToCrepMkCtxtHOL (panToCrepMakeVmapHOL params)
    (functionInfosHOL declarations) vmax (panToCrepGetEidsFromDeclsHOL declarations)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨((compileParamVars params 0).1.map Prod.fst), ?_⟩
    intro key hkey
    change FLOOKUP (FUPDATE_LIST FEMPTY (compileParamVars params 0).1) key ≠ none at hkey
    cases hlookup : FLOOKUP (FUPDATE_LIST FEMPTY (compileParamVars params 0).1) key with
    | none => contradiction
    | some value =>
        obtain ⟨entry, hentry, hname, _⟩ := updateList_lookup_has_entry
          (compileParamVars params 0).1 key value hlookup
        exact List.mem_map.mpr ⟨entry, hentry, hname⟩
  · refine ⟨(panToCrepMakeFuncs declarations).reverse.map Prod.fst, ?_⟩
    intro key hkey
    change FLOOKUP (FUPDATE_LIST FEMPTY (panToCrepMakeFuncs declarations).reverse) key ≠ none at hkey
    cases hlookup : FLOOKUP (FUPDATE_LIST FEMPTY (panToCrepMakeFuncs declarations).reverse) key with
    | none => contradiction
    | some value =>
        obtain ⟨entry, hentry, hname, _⟩ := updateList_lookup_has_entry
          (panToCrepMakeFuncs declarations).reverse key value hlookup
        exact List.mem_map.mpr ⟨entry, hentry, hname⟩
  · let names := (exceptionEntries declarations).map Prod.fst
    refine ⟨(names.zip ((List.range names.length).map (BitVec.ofNat width))).reverse.map Prod.fst, ?_⟩
    intro key hkey
    change FLOOKUP (FUPDATE_LIST FEMPTY
      (names.zip ((List.range names.length).map (BitVec.ofNat width))).reverse) key ≠ none at hkey
    cases hlookup : FLOOKUP (FUPDATE_LIST FEMPTY
      (names.zip ((List.range names.length).map (BitVec.ofNat width))).reverse) key with
    | none => contradiction
    | some value =>
        obtain ⟨entry, hentry, hname, _⟩ := updateList_lookup_has_entry
          (names.zip ((List.range names.length).map (BitVec.ofNat width))).reverse key value hlookup
        exact List.mem_map.mpr ⟨entry, hentry, hname⟩
  · intro key value hlookup
    change FLOOKUP (FUPDATE_LIST FEMPTY (compileParamVars params 0).1) key = some value at hlookup
    obtain ⟨entry, hentry, hname, hvalue⟩ := updateList_lookup_has_entry
      (compileParamVars params 0).1 key value hlookup
    have hr := compileParamVars_byteRanged params 0 hparams entry hentry
    exact ⟨hname ▸ hr.1, hvalue ▸ hr.2⟩
  · intro key value hlookup
    change FLOOKUP (FUPDATE_LIST FEMPTY (panToCrepMakeFuncs declarations).reverse) key = some value at hlookup
    obtain ⟨entry, hentry, hname, hvalue⟩ := updateList_lookup_has_entry
      (panToCrepMakeFuncs declarations).reverse key value hlookup
    have hr := panToCrepMakeFuncs_entries_byteRanged declarations hdecls entry hentry
    cases entry with
    | mk name info =>
      obtain ⟨params, result⟩ := info
      have hinfo : (params, result) = value := hvalue
      cases hinfo
      exact ⟨hname ▸ hr.1, hr.2.1, hr.2.2⟩
  · let names := (exceptionEntries declarations).map Prod.fst
    intro key value hlookup
    change FLOOKUP (FUPDATE_LIST FEMPTY
      (names.zip ((List.range names.length).map (BitVec.ofNat width))).reverse) key = some value at hlookup
    obtain ⟨entry, hentry, hname, _⟩ := updateList_lookup_has_entry
      (names.zip ((List.range names.length).map (BitVec.ofNat width))).reverse key value hlookup
    have hnameMem : entry.1 ∈ names := by
      have hzip : entry ∈ names.zip ((List.range names.length).map (BitVec.ofNat width)) := by
        simpa only [List.mem_reverse] using hentry
      exact (List.of_mem_zip hzip).1
    have hr := exceptionNames_byteRanged declarations hdecls entry.1 hnameMem
    exact hname ▸ hr

/-- The context passed to panToCrepCompFuncRiscV for any function extracted
    from a byte-ranged declaration list satisfies the exact bridge premises.
    This is the producer-shaped theorem for the executed compiler path:
    functionEntries supplies the parameters, while the full declaration
    list supplies function and exception tables. -/
theorem panToCrepFunctionContextProductionEvidence {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (entry : FunName × List (VarName × Shape) × Prog (BitVec width) × Shape)
    (hdecls : ∀ d ∈ declarations, DeclByteRanged d)
    (hentry : entry ∈ functionEntries declarations) :
    PanToCrepContextProductionEvidence
      (panToCrepMkCtxtHOL (panToCrepMakeVmapHOL entry.2.1)
        (functionInfosHOL declarations)
        (Shape.shapeSize (.comb (entry.2.1.map Prod.snd)) - 1)
        (panToCrepGetEidsFromDeclsHOL declarations)) := by
  have hr := functionEntries_byteRanged declarations hdecls entry hentry
  exact panToCrepCompilerContextProductionEvidence declarations entry.2.1
    (Shape.shapeSize (.comb (entry.2.1.map Prod.snd)) - 1) hdecls hr.2.1

end Flapjack
