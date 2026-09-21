import Flapjack.PanProgramSemantics
import Flapjack.PanSimp

/-!
Counterpart of Cake's `decs_stcnames_compile_prog`
(`cakeml/pancake/proofs/pan_simpProofScript.sml:1334-1341`):

    !ctxt pan_code. decs_stcnames ctxt (compile_prog pan_code) =
                    decs_stcnames ctxt pan_code

Flapjack's `collectPanValueStructs` is the executable counterpart of Cake's
`decs_stcnames` (`cakeml/pancake/semantics/panSemScript.sml:839-859`), and
`panSimpDecls` is the counterpart of `pan_simp$compile_prog`.  Because
`pan_simp` rewrites only function bodies and leaves every other declaration
constructor untouched, it cannot change the struct-name context that
`collectPanValueStructs` accumulates. -/

namespace Flapjack

/-- Cons equation for `collectPanValueStructs`, mirroring Cake's
    `decs_stcnames_def`. -/
theorem collectPanValueStructs_cons (declaration : Decl α) (declarations : List (Decl α))
    (context : StructContext) :
    collectPanValueStructs (declaration :: declarations) context =
      (match declaration with
       | .name name fields =>
           if (lookupInfo name context).isSome then none
           else if !(fields.map (fun field => field.1)).Nodup then none
           else if !fields.all (fun field => isWfShape context field.2) then none
           else collectPanValueStructs declarations
                  ((name, panValueDeclStructInfo context fields) :: context)
       | _ => collectPanValueStructs declarations context) := by
  cases declaration <;> rw [collectPanValueStructs.eq_def]

/-- Cake's `decs_stcnames_compile_prog`: `pan_simp` preserves the
    struct-name context collected from a declaration list. -/
theorem collectPanValueStructs_panSimpDecls (declarations : List (Decl α))
    (context : StructContext) :
    collectPanValueStructs (panSimpDecls declarations) context =
      collectPanValueStructs declarations context := by
  rw [panSimpDecls_eq_map]
  induction declarations generalizing context with
  | nil => rfl
  | cons declaration declarations ih =>
      simp only [List.map_cons]
      cases declaration <;>
        simp [panSimpDecl, collectPanValueStructs_cons, ih]

/-! Cake's `OPT_MMAP` is `List.mapM` for `Option`, so the list-mapping helper
lemmas used by `compile_correct` (`cakeml/pancake/proofs/pan_simpProofScript.sml`)
have the following `List.mapM` counterparts.  These are the pieces needed to
transfer an `OPT_MMAP (eval s) es = SOME vs` hypothesis to a related state `t`
(`opt_mmap_eq_some_helper`, `OPT_MMAP_NONE`, `OPT_MMAP_NONE'`). -/

/-- Cake's `opt_mmap_eq_some_helper` (`pan_simpProofScript.sml:394`): if two
    functions agree on every element that the first maps successfully, then
    mapping the second succeeds with the same result. -/
theorem list_mapM_eq_some_of_eq_some {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α) (zs : List β), xs.mapM f = some zs →
      (∀ x ∈ xs, ∀ y, f x = some y → g x = some y) → xs.mapM g = some zs
  | [], zs, h, _ => h
  | x :: xs, zs, h, hfg => by
      rw [List.mapM_cons] at h ⊢
      cases hx : f x with
      | none => simp [hx] at h
      | some a =>
          have hga : g x = some a := hfg x (by simp) a hx
          rw [hga]
          simp at h ⊢
          cases hys : List.mapM f xs with
          | none => simp [hys] at h
          | some ys =>
              have hz : zs = a :: ys := by simpa [hys, hx] using h.symm
              subst hz
              rw [list_mapM_eq_some_of_eq_some f g xs ys hys
                    (fun z hz' b hb => hfg z (by simp [hz']) b hb)]
              rfl

/-- Cake's `OPT_MMAP_NONE` (`pan_simpProofScript.sml:500`): a failing map has
    a failing element. -/
theorem list_mapM_eq_none_exists {α β : Type} (f : α → Option β) (xs : List α)
    (h : xs.mapM f = none) : ∃ x ∈ xs, f x = none := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      rw [List.mapM_cons] at h
      cases hx : f x with
      | none => exact ⟨x, by simp, hx⟩
      | some y =>
          cases hys : List.mapM f xs with
          | none =>
              obtain ⟨z, hz, hfz⟩ := ih hys
              exact ⟨z, by simp [hz], hfz⟩
          | some ys =>
              simp [hys] at h
              exact absurd hx (h y)

/-- Cake's `OPT_MMAP_NONE'` (`pan_simpProofScript.sml:509`): a failing element
    makes the whole map fail. -/
theorem list_mapM_eq_none_of_mem {α β : Type} (f : α → Option β) {x : α} {xs : List α}
    (hx : x ∈ xs) (hf : f x = none) : xs.mapM f = none := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.mapM_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · simp [hf]
      · cases hy : f y with
        | none => simp
        | some b => simp [ih hx']
/-! Cake's `state_rel_imp_evaluate_decls`
(`cakeml/pancake/proofs/pan_simpProofScript.sml:1303-1331`) says that evaluating a
declaration list and evaluating the `pan_simp`-simplified declaration list agree
up to a state relation that only changes function bodies.  The Flapjack analogue
below states that relation explicitly (`panValueProgramStateRel`) and proves the
same preservation for `evalPanValueDeclarationsWithStructs` and for the
struct-name-collecting entry point `evalPanValueDeclarations`. -/

def panValueFunctionsSimp :
    List (FunName × List VarName × Prog α) →
      List (FunName × List VarName × Prog α)
  | [] => []
  | (name, parameters, body) :: rest =>
      (name, parameters, panSimpProg body) :: panValueFunctionsSimp rest

def panValueProgramStateRel (s t : PanValueProgramState α) : Prop :=
  s.structs = t.structs ∧
  s.globals = t.globals ∧
  s.memory = t.memory ∧
  s.returnShapes = t.returnShapes ∧
  s.parameterShapes = t.parameterShapes ∧
  s.exceptions = t.exceptions ∧
  s.baseAddress = t.baseAddress ∧
  s.topAddress = t.topAddress ∧
  s.bytesInWord = t.bytesInWord ∧
  t.functions = panValueFunctionsSimp s.functions

theorem panSimpDecls_nil : panSimpDecls ([] : List (Decl α)) = [] := by
  simp [panSimpDecls]

theorem panSimpDecls_function (declaration : FunDecl α) (declarations : List (Decl α)) :
    panSimpDecls (.function declaration :: declarations) =
      .function { declaration with body := panSimpProg declaration.body } ::
        panSimpDecls declarations := by
  simp [panSimpDecls]

theorem panSimpDecls_name (name : StructName) (fields : List (FieldName × Shape))
    (declarations : List (Decl α)) :
    panSimpDecls (.name name fields :: declarations) = .name name fields :: panSimpDecls declarations := by
  simp [panSimpDecls]

end Flapjack

namespace Flapjack

theorem panValueProgramStateRel_evalPanValueDeclarationsWithStructs
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (s t : PanValueProgramState α)
    (hrel : panValueProgramStateRel s t)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (s' : PanValueProgramState α)
    (hs : evalPanValueDeclarationsWithStructs structs s declarations memoryAccess = some s') :
    ∃ t', evalPanValueDeclarationsWithStructs structs t (panSimpDecls declarations)
        memoryAccess = some t' ∧ panValueProgramStateRel s' t' := by
  induction declarations generalizing s t s' with
  | nil =>
      simp only [evalPanValueDeclarationsWithStructs] at hs
      refine ⟨t, ?_, ?_⟩
      · simp [panSimpDecls_nil, evalPanValueDeclarationsWithStructs]
      · rw [show s' = s from ?_]
        · exact hrel
        · simp only [Option.some.injEq] at hs; exact hs.symm
  | cons declaration declarations ih =>
      cases declaration with
      | name struct fields =>
          simp only [panSimpDecls_name, evalPanValueDeclarationsWithStructs] at hs ⊢
          exact ih s t hrel s' hs
      | decl shape name expression =>
          simp only [panSimpDecls, evalPanValueDeclarationsWithStructs] at hs ⊢
          obtain ⟨hstructs, hglobals, hmemory, hret, hparam, hexn, hbase, htop, hbiw, hfuncs⟩ := hrel
          rw [hglobals, hmemory, hbase, htop, hbiw] at hs
          cases hval : evalPanValueExp structs (fun _ => none) t.globals t.memory
              t.baseAddress t.topAddress t.bytesInWord expression
              (memoryAccess := memoryAccess) with
          | none => simp [hval] at hs
          | some value =>
              by_cases hmatch : panShapeMatches (panValueShape structs value) shape = true
              · simp [hval, hmatch] at hs ⊢
                refine ih _ _ ?_ s' hs
                exact ⟨rfl, rfl, rfl, hret, hparam, hexn, rfl, rfl, rfl, hfuncs⟩
              · simp [hval, hmatch] at hs
      | function declaration =>
          simp only [panSimpDecls_function, evalPanValueDeclarationsWithStructs] at hs ⊢
          obtain ⟨hstructs, hglobals, hmemory, hret, hparam, hexn, hbase, htop, hbiw, hfuncs⟩ := hrel
          by_cases hwf : (declaration.params.all (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true
          · simp only [hwf] at hs ⊢
            refine ih _ _ ?_ s' hs
            exact ⟨rfl, hglobals, hmemory, by rw [hret], by rw [hparam],
              hexn, hbase, htop, hbiw, by simp [hfuncs, panValueFunctionsSimp]⟩
          · simp [hwf] at hs
      | exnDecl exception shape =>
          simp only [panSimpDecls, evalPanValueDeclarationsWithStructs] at hs ⊢
          obtain ⟨hstructs, hglobals, hmemory, hret, hparam, hexn, hbase, htop, hbiw, hfuncs⟩ := hrel
          rw [hexn] at hs
          by_cases hexists : (lookupInfo exception t.exceptions).isSome = true
          · simp [hexists] at hs
          · by_cases hwf : isWfShape structs shape = true
            · simp only [hexists, hwf] at hs ⊢
              refine ih _ _ ?_ s' hs
              exact ⟨rfl, hglobals, hmemory, hret, hparam, rfl, hbase, htop, hbiw, hfuncs⟩
            · simp [hexists, hwf] at hs

theorem panValueProgramStateRel_evalPanValueDeclarations
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (declarations : List (Decl α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (s' : PanValueProgramState α)
    (hs : evalPanValueDeclarations s declarations memoryAccess = some s') :
    ∃ t', evalPanValueDeclarations t (panSimpDecls declarations) memoryAccess = some t' ∧
      panValueProgramStateRel s' t' := by
  obtain ⟨hstructs, hglobals, hmemory, hret, hparam, hexn, hbase, htop, hbiw, hfuncs⟩ := hrel
  simp only [evalPanValueDeclarations] at hs ⊢
  cases hcollect : collectPanValueStructs declarations s.structs with
  | none => simp [hcollect] at hs
  | some structs =>
      have htcollect : collectPanValueStructs (panSimpDecls declarations) t.structs =
          some structs := by
        rw [collectPanValueStructs_panSimpDecls, ← hstructs]
        exact hcollect
      simp only [hcollect, htcollect] at hs ⊢
      refine panValueProgramStateRel_evalPanValueDeclarationsWithStructs structs
        { s with structs := structs } { t with structs := structs } ?_ declarations
        memoryAccess s' hs
      exact ⟨rfl, hglobals, hmemory, hret, hparam, hexn, hbase, htop, hbiw, hfuncs⟩

/-! Cake's `map_snd_f_eq` (`pan_simpProofScript.sml:43`): rewriting only the
    body component of a declaration triple commutes with projecting that body
    and applying a further function.  Stated for `List (α × β × γ)`, whose
    nested `Prod.snd` projections are Cake's `SND ∘ SND`. -/

/-- Cake's `map_snd_f_eq` (`pan_simpProofScript.sml:43`). -/
theorem list_map_third_map_eq {α β γ δ ε : Type} (f : γ → δ) (g : δ → ε)
    (p : List (α × β × γ)) :
    (p.map (fun t => (t.1, t.2.1, f t.2.2))).map (fun t => g t.2.2) =
      p.map (fun t => g (f t.2.2)) := by
  induction p with
  | nil => rfl
  | cons t ts ih => simp [ih]

/-! Cake's `compile_eval_correct` (`pan_simpProofScript.sml:489-...`): an
    expression that evaluates successfully before `pan_simp` evaluates to the
    same value in any state related by `state_rel`.  `pan_simp` rewrites only
    function bodies, which expression evaluation never observes, so the
    Flapjack counterpart follows from the component equalities recorded in
    `panValueProgramStateRel`. -/

/-- Expression-level counterpart of Cake's `compile_eval_correct`: evaluation
    is invariant under `panValueProgramStateRel` (locals are passed
    explicitly because `PanValueProgramState` does not store them). -/
theorem evalPanValueExp_panValueProgramStateRel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals : VarName → Option (PanValue α))
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (expression : Exp α) (memoryAccess : Option (PanValueMemoryAccess α))
    (value : PanValue α)
    (hs : evalPanValueExp structs locals s.globals s.memory s.baseAddress
        s.topAddress s.bytesInWord expression (memoryAccess := memoryAccess) =
      some value) :
    evalPanValueExp structs locals t.globals t.memory t.baseAddress
      t.topAddress t.bytesInWord expression (memoryAccess := memoryAccess) =
      some value := by
  obtain ⟨_hstructs, hglobals, hmemory, _hret, _hparam, _hexn, hbase, htop,
    hbiw, _hfuncs⟩ := hrel
  simpa only [hglobals, hmemory, hbase, htop, hbiw] using hs

end Flapjack
