import Flapjack.PanGlobals
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

/-- Cake's `decs_stcnames_only_functions`
    (`cakeml/pancake/semantics/panPropsScript.sml:1592`): a declaration list
    without struct declarations leaves the struct-name context unchanged. -/
theorem collectPanValueStructs_of_no_names (context : StructContext)
    (declarations : List (Decl α))
    (hall : declarations.all (fun declaration => !isName declaration) = true) :
    collectPanValueStructs declarations context = some context := by
  induction declarations generalizing context with
  | nil => simp [collectPanValueStructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      have hnotname : isName declaration = false := by simpa using hhead
      cases declaration with
      | function declaration =>
          simpa [collectPanValueStructs_cons] using ih context htail
      | decl shape name value =>
          simpa [collectPanValueStructs_cons] using ih context htail
      | exnDecl exception shape =>
          simpa [collectPanValueStructs_cons] using ih context htail
      | name name fields => simp [isName] at hnotname

/-- Cake's `decs_stcnames_only_functions2`
    (`cakeml/pancake/semantics/panPropsScript.sml:1600`): a list of function
    declarations only leaves the struct-name context unchanged. -/
theorem collectPanValueStructs_of_functions (context : StructContext)
    (declarations : List (Decl α))
    (hall : declarations.all globalDeclIsFunction = true) :
    collectPanValueStructs declarations context = some context := by
  refine collectPanValueStructs_of_no_names context declarations ?_
  refine List.all_eq_true.mpr (fun declaration hmem => ?_)
  have hfunction := List.all_eq_true.mp hall declaration hmem
  cases declaration <;> simp_all [globalDeclIsFunction, isName]

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

/-- Cake's `opt_mmap_eq_some_el` (`pan_structsProofScript.sml:19`): a successful
    `OPT_MMAP` is exactly a length match together with a pointwise success
    condition, adapted from total `EL` to `getElem?`. -/
theorem list_mapM_eq_some_iff {α β : Type} (f : α → Option β) (xs : List α) (ys : List β) :
    xs.mapM f = some ys ↔
      xs.length = ys.length ∧ ∀ n, n < ys.length → (xs[n]?).bind f = ys[n]? := by
  induction xs generalizing ys with
  | nil =>
      constructor
      · intro h
        cases h
        simp
      · intro h
        obtain ⟨hlen, _⟩ := h
        have : ys = [] := by simpa using hlen.symm
        subst this
        rfl
  | cons x xs ih =>
      rw [List.mapM_cons]
      constructor
      · intro h
        cases hx : f x with
        | none => simp [hx] at h
        | some b =>
            simp only [hx] at h
            cases hxs : xs.mapM f with
            | none => simp [hxs] at h
            | some ys' =>
                simp only [hxs] at h
                have hb : b :: ys' = ys := by simpa using h
                subst hb
                obtain ⟨hlen, hpt⟩ := (ih ys').mp hxs
                refine ⟨by simp [hlen], ?_⟩
                intro n hn
                cases n with
                | zero => simp [hx]
                | succ m =>
                    simp only [List.getElem?_cons_succ, List.length_cons] at hn ⊢
                    have hm : m < ys'.length := by omega
                    simpa using hpt m hm
      · intro h
        obtain ⟨hlen, hpt⟩ := h
        cases ys with
        | nil => simp at hlen
        | cons b ys' =>
            have hfx : f x = some b := by
              have := hpt 0 (by simp)
              simpa using this
            have htail : xs.length = ys'.length ∧
                ∀ n, n < ys'.length → (xs[n]?).bind f = ys'[n]? := by
              refine ⟨by simpa using hlen, ?_⟩
              intro n hn
              have := hpt (n + 1) (by simp; omega)
              simpa [List.getElem?_cons_succ] using this
            have hxs : xs.mapM f = some ys' := (ih ys').mpr htail
            simp [hfx, hxs]

/-- Cake's `opt_mmap_eq_every`
(`cakeml/pancake/proofs/pan_structsProofScript.sml:255-265`): if `mapM f` succeeds
on `xs` producing `ys`, then any predicate that holds for every successful image
`f x = some y` with `x ∈ xs` holds for every element of `ys`. -/
theorem list_mapM_all_of_mem {α β : Type} (f : α → Option β) (P : β → Bool)
    (xs : List α) (ys : List β) (h : xs.mapM f = some ys)
    (hf : ∀ x y, x ∈ xs → f x = some y → P y = true) :
    ys.all P = true := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.mapM_nil] at h
      cases h
      simp
  | cons a as ih =>
      rw [List.mapM_cons] at h
      cases hx : f a with
      | none => simp [hx] at h
      | some b =>
          simp only [hx] at h
          cases hxs : as.mapM f with
          | none => simp [hxs] at h
          | some ys' =>
              simp only [hxs] at h
              have hb : b :: ys' = ys := by simpa using h
              subst hb
              simp only [List.all_cons, Bool.and_eq_true]
              exact ⟨hf a b (by simp) hx,
                ih ys' hxs (fun x y hx' hfy => hf x y (by simp [hx']) hfy)⟩

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

/-! The evaluator uses the source-shaped `lookupPanFunction` table rather than
    Cake's richer declaration projection.  This is the direct function-table
    lookup bridge needed when lifting `state_rel_imp_semantics`: a successful
    source lookup remains successful after `pan_simp`, with only the body
    transformed. -/
theorem lookupPanFunction_panValueFunctionsSimp
    (functions : List (FunName × List VarName × Prog α)) (name : FunName)
    {parameters : List VarName} {body : Prog α}
    (hlookup : lookupPanFunction name functions = some (parameters, body)) :
    lookupPanFunction name (panValueFunctionsSimp functions) =
      some (parameters, panSimpProg body) := by
  induction functions with
  | nil =>
      simp [lookupPanFunction] at hlookup
  | cons entry functions ih =>
      obtain ⟨candidate, parameters', body'⟩ := entry
      by_cases hname : name == candidate
      · simp [lookupPanFunction, panValueFunctionsSimp, hname] at hlookup ⊢
        rcases hlookup with ⟨rfl, rfl⟩
        simp
      · have htail : lookupPanFunction name functions = some (parameters, body) := by
          simpa [lookupPanFunction, hname] using hlookup
        have htail' := ih htail
        simpa [lookupPanFunction, panValueFunctionsSimp, hname] using htail'

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

/-! State-relation form of the lookup bridge.  This is the call-site fact used
    by the Cake `state_rel_imp_semantics` induction: related states differ in
    function bodies only, so a source callee lookup lifts to its `pan_simp`
    body in the target state. -/
theorem panValueProgramStateRel_lookupPanFunction
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (name : FunName) {parameters : List VarName} {body : Prog α}
    (hlookup : lookupPanFunction name s.functions = some (parameters, body)) :
    lookupPanFunction name t.functions = some (parameters, panSimpProg body) := by
  obtain ⟨_hstructs, _hglobals, _hmemory, _hreturnShapes, _hparameterShapes,
    _hexceptions, _hbaseAddress, _htopAddress, _hbytesInWord, hfunctions⟩ := hrel
  rw [hfunctions]
  exact lookupPanFunction_panValueFunctionsSimp s.functions name hlookup

/-- Cake's `state_rel_upd_inv` (`pan_simpProofScript.sml:387`): the source
    state can be recovered from the target state by resetting the simplified
    function table. -/
theorem panValueProgramStateRel_functions_recover
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t) :
    ∃ functions, s = { t with functions := functions } := by
  refine ⟨s.functions, ?_⟩
  cases s
  cases t
  simp_all [panValueProgramStateRel]

/-- Cake's `state_rel_intro` (`pan_simpProofScript.sml:377`): the target state is
    the source state with its function table replaced by the simplified one. -/
theorem panValueProgramStateRel_intro
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t) :
    t = { s with functions := panValueFunctionsSimp s.functions } := by
  cases s
  cases t
  simp_all [panValueProgramStateRel]

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

/-! Cake's `OPT_MMAP_eval_some_eq` (`pan_simpProofScript.sml:518`): a whole
    list of expressions that evaluates successfully evaluates to the same
    values under `state_rel`.  This is Cake's `OPT_MMAP_eval_some_eq`, whose
    `OPT_MMAP` is `List.mapM` for `Option`, and it is the list-level consumer
    of the `compile_eval_correct` bridge above. -/

/-- List-level counterpart of Cake's `OPT_MMAP_eval_some_eq`: if a list of
    expressions maps successfully under `state_rel`-related states, the
    mapped values agree. -/
theorem list_mapM_eval_panValueProgramStateRel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals : VarName → Option (PanValue α))
    (s t : PanValueProgramState α) (hrel : panValueProgramStateRel s t)
    (expressions : List (Exp α)) (values : List (PanValue α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hs : expressions.mapM (fun expression =>
        evalPanValueExp structs locals s.globals s.memory s.baseAddress
          s.topAddress s.bytesInWord expression (memoryAccess := memoryAccess)) =
      some values) :
    expressions.mapM (fun expression =>
      evalPanValueExp structs locals t.globals t.memory t.baseAddress
        t.topAddress t.bytesInWord expression (memoryAccess := memoryAccess)) =
      some values :=
  list_mapM_eq_some_of_eq_some
    (fun expression => evalPanValueExp structs locals s.globals s.memory
      s.baseAddress s.topAddress s.bytesInWord expression
      (memoryAccess := memoryAccess))
    (fun expression => evalPanValueExp structs locals t.globals t.memory
      t.baseAddress t.topAddress t.bytesInWord expression
      (memoryAccess := memoryAccess))
    expressions values hs
    (fun expression _ value heval =>
      evalPanValueExp_panValueProgramStateRel structs locals s t hrel expression
        memoryAccess value heval)

/-! Cake's `evaluate_decls_functions`
    (`cakeml/pancake/semantics/panPropsScript.sml:1518`):

        !s pan_code s'. evaluate_decls s pan_code = SOME s' ==>
                     s'.code = s.code |++ functions pan_code

    Evaluating a declaration list installs exactly the function declarations it
    contains, in source order, leaving every other declaration constructor
    untouched.  Cake's `|++` folds map updates in source order, so a later
    function wins; Flapjack's function table is a lookup list that prepends each
    installed function, so the accumulated table is the reversed source-order
    projection of `functions`. -/

/-- Source-order projection of a declaration list's function entries into the
    `(name, parameter names, body)` shape stored by `PanValueProgramState`. -/
def panFunctionEntries (declarations : List (Decl α)) :
    List (FunName × List VarName × Prog α) :=
  (functions declarations).reverse.map
    (fun entry : FunName × List (VarName × Shape) × Prog α × Shape =>
      (entry.1, entry.2.1.map Prod.fst, entry.2.2.1))

/-- Source-order projection of a declaration list's function entries into the
    `(name, return shape)` pairs stored in `returnShapes`. -/
def panReturnShapeEntries (declarations : List (Decl α)) : InfoMap Shape :=
  (functions declarations).reverse.map
    (fun entry : FunName × List (VarName × Shape) × Prog α × Shape =>
      (entry.1, entry.2.2.2))

/-- Source-order projection of a declaration list's function entries into the
    `(name, parameters)` pairs stored in `parameterShapes`. -/
def panParameterShapeEntries (declarations : List (Decl α)) :
    InfoMap (List (VarName × Shape)) :=
  (functions declarations).reverse.map
    (fun entry : FunName × List (VarName × Shape) × Prog α × Shape =>
      (entry.1, entry.2.1))

/-- Cake's `evaluate_decls_functions` (`panPropsScript.sml:1518`): a successful
    declaration evaluation only prepends the list's function entries to the
    function table. -/
theorem evalPanValueDeclarationsWithStructs_functions
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state') :
    state'.functions = panFunctionEntries declarations ++ state.functions := by
  induction declarations generalizing state with
  | nil =>
      simp only [evalPanValueDeclarationsWithStructs] at heval
      have hstate : state = state' := (Option.some.injEq _ _).mp heval
      subst hstate
      simp [panFunctionEntries, functions]
  | cons declaration declarations ih =>
      cases declaration with
      | name struct fields =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          rw [ih state heval]
          simp [panFunctionEntries, functions]
      | decl shape name expression =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          cases hval : evalPanValueExp structs (fun _ => none) state.globals
              state.memory state.baseAddress state.topAddress state.bytesInWord
              expression (memoryAccess := memoryAccess) with
          | none => simp [hval] at heval
          | some value =>
              by_cases hmatch :
                  panShapeMatches (panValueShape structs value) shape = true
              · simp [hval, hmatch] at heval
                rw [ih _ heval]
                simp [panFunctionEntries, functions]
              · simp [hval, hmatch] at heval
      | function declaration =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hwf : (declaration.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true
          · simp only [hwf] at heval
            rw [ih _ heval]
            simp [panFunctionEntries, functions, List.reverse_cons, List.map_append]
          · simp [hwf] at heval
      | exnDecl exception shape =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
          · simp [hexists] at heval
          · by_cases hwf : isWfShape structs shape = true
            · simp only [hexists, hwf] at heval
              rw [ih _ heval]
              simp [panFunctionEntries, functions]
            · simp [hexists, hwf] at heval

/-! Cake's `evaluate_decls_eshapes`
    (`cakeml/pancake/semantics/panPropsScript.sml:1409`):

        !s ds s'. evaluate_decls s ds = SOME s' ==>
                     s'.eshapes = s.eshapes |++ exceptions ds

    The exception-table counterpart of `evaluate_decls_functions`: a successful
    declaration evaluation only prepends the list's exception declarations, in
    source order, to the exception-shape table.  Flapjack prepends each
    installed exception, so the accumulated table is the reversed source-order
    projection of `exceptionEntries`. -/

/-- Source-order projection of a declaration list's exception entries into the
    `(exception, shape)` pairs stored by `PanValueProgramState`. -/
def panExceptionEntries (declarations : List (Decl α)) : List (ExceptionId × Shape) :=
  (exceptionEntries declarations).reverse

theorem panExceptionEntries_nil : panExceptionEntries ([] : List (Decl α)) = [] := by
  simp [panExceptionEntries, exceptionEntries]

theorem panExceptionEntries_cons (declaration : Decl α) (declarations : List (Decl α)) :
    panExceptionEntries (declaration :: declarations) =
      (match declaration with
       | .exnDecl exception shape =>
           panExceptionEntries declarations ++ [(exception, shape)]
       | _ => panExceptionEntries declarations) := by
  cases declaration <;>
    simp [panExceptionEntries, exceptionEntries_cons, List.reverse_cons]

/-- Cake's `evaluate_decls_eshapes` (`panPropsScript.sml:1409`): a successful
    declaration evaluation only prepends the list's exception entries to the
    exception-shape table. -/
theorem evalPanValueDeclarationsWithStructs_exceptions
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state') :
    state'.exceptions = panExceptionEntries declarations ++ state.exceptions := by
  induction declarations generalizing state with
  | nil =>
      simp only [evalPanValueDeclarationsWithStructs] at heval
      have hstate : state = state' := (Option.some.injEq _ _).mp heval
      subst hstate
      simp [panExceptionEntries_nil]
  | cons declaration declarations ih =>
      cases declaration with
      | name struct fields =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          rw [ih state heval]
          simp [panExceptionEntries_cons]
      | decl shape name expression =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          cases hval : evalPanValueExp structs (fun _ => none) state.globals
              state.memory state.baseAddress state.topAddress state.bytesInWord
              expression (memoryAccess := memoryAccess) with
          | none => simp [hval] at heval
          | some value =>
              by_cases hmatch :
                  panShapeMatches (panValueShape structs value) shape = true
              · simp [hval, hmatch] at heval
                rw [ih _ heval]
                simp [panExceptionEntries_cons]
              · simp [hval, hmatch] at heval
      | function declaration =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hwf : (declaration.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true
          · simp only [hwf] at heval
            rw [ih _ heval]
            simp [panExceptionEntries_cons]
          · simp [hwf] at heval
      | exnDecl exception shape =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
          · simp [hexists] at heval
          · by_cases hwf : isWfShape structs shape = true
            · simp only [hexists, hwf] at heval
              rw [ih _ heval]
              simp [panExceptionEntries_cons, List.append_assoc]
            · simp [hexists, hwf] at heval

/-! The same Cake `evaluate_decls_eshapes` equation at the public declaration
    evaluator.  This wrapper exposes the exception table after struct
    collection, which is the state needed by a later raised-call lookup. -/
theorem evalPanValueDeclarations_exceptions
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state state' : PanValueProgramState α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (heval : evalPanValueDeclarations state declarations memoryAccess = some state') :
    state'.exceptions = panExceptionEntries declarations ++ state.exceptions := by
  simp only [evalPanValueDeclarations] at heval
  cases hcollect : collectPanValueStructs declarations state.structs with
  | none => simp [hcollect] at heval
  | some structs =>
      simp only [hcollect] at heval
      exact evalPanValueDeclarationsWithStructs_exceptions structs
        { state with structs := structs } state' declarations memoryAccess heval

/-! Compose the public declaration-state equation with Cake's top-level raised
    call boundary.  The result keeps both the raised payload and the exception
    table available to the caller instead of hiding lookup in a premise. -/
theorem evalPanValueProgram_of_declarations_and_raised_call_with_exception_state
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (initial : PanValueProgramState α)
    (primitive : PanPrimitiveHandler α) (ffi : PanValueFfiHandler α)
    (fuel : Nat) (declarations : List (Decl α)) (entry : FunName)
    (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (memoryHandler : Option (PanValueAcceleratorFfiHandler α))
    (state : PanValueProgramState α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (exception : ExceptionId)
    (value : PanValue α)
    (hdeclarations : evalPanValueDeclarations initial declarations
      (memoryAccess := memoryAccess) = some state)
    (hcall : evalPanValueCallWithPrimitiveCallsAndFfi primitive ffi
      state.structs state.functions state.baseAddress state.topAddress
      state.bytesInWord fuel (fun _ => none) state.globals state.memory none
      entry arguments (memoryAccess := memoryAccess)
      (contracts := some (PanValueCallContracts.mk state.returnShapes
        state.exceptions state.parameterShapes))
      (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value)) :
    evalPanValueProgram initial primitive ffi fuel declarations entry arguments
      (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
      some (.raised locals globals memory exception value) ∧
    state.exceptions = panExceptionEntries declarations ++ initial.exceptions := by
  constructor
  · exact evalPanValueProgram_of_declarations_and_raised_call initial primitive ffi
      fuel declarations entry arguments memoryAccess memoryHandler state locals globals
      memory exception value hdeclarations hcall
  · exact evalPanValueDeclarations_exceptions initial state declarations memoryAccess
      hdeclarations

/-! Package the public declaration facts needed by the raised evaluator: the
    collected struct context makes the exception payload shape well formed, and
    the resulting state carries Cake's exact exception table equation. -/
theorem evalPanValueDeclarations_exception_state_evidence
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state state' : PanValueProgramState α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    {exception : ExceptionId} {shape : Shape}
    (hmem : (.exnDecl exception shape : Decl α) ∈ declarations)
    (heval : evalPanValueDeclarations state declarations memoryAccess = some state') :
    ∃ structs : StructContext,
      collectPanValueStructs declarations state.structs = some structs ∧
        state'.exceptions = panExceptionEntries declarations ++ state.exceptions ∧
        isWfShape structs shape = true := by
  obtain ⟨structs, hcollect, hwf⟩ :=
    evalPanValueDeclarations_exceptions_wf state state' declarations memoryAccess
      heval hmem
  exact ⟨structs, hcollect,
    evalPanValueDeclarations_exceptions state state' declarations memoryAccess heval,
    hwf⟩

/-! Cake's `evaluate_decls_only_exn_decls`
    (`cakeml/pancake/semantics/panPropsScript.sml:1436`): when every
    declaration is an exception declaration, successful evaluation changes
    only the exception-shape table.  This stronger state equation is useful
    when composing the exception environment with later function/global
    declarations. -/
theorem evalPanValueDeclarationsWithStructs_only_exn_decls
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hstructs : state.structs = structs)
    (hall : declarations.all isExnDecl = true)
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state') :
    state' = { state with
      structs := structs
      exceptions := panExceptionEntries declarations ++ state.exceptions } := by
  induction declarations generalizing state with
  | nil =>
      simp only [evalPanValueDeclarationsWithStructs] at heval
      have hstate : state = state' := (Option.some.injEq _ _).mp heval
      subst hstate
      rw [panExceptionEntries_nil, List.nil_append, ← hstructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      have hexndecl : isExnDecl declaration = true := hhead
      cases declaration with
      | exnDecl exception shape =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
          · simp [hexists] at heval
          · by_cases hwf : isWfShape structs shape = true
            · simp only [hexists, hwf] at heval
              rw [ih _ (by rfl) htail heval]
              simp [panExceptionEntries_cons, List.append_assoc]
            · simp [hexists, hwf] at heval
      | function _ => simp [isExnDecl] at hexndecl
      | decl _ _ _ => simp [isExnDecl] at hexndecl
      | name _ _ => simp [isExnDecl] at hexndecl

/-- Cake's `evaluate_decls_only_exn_decls` (`panPropsScript.sml:1436`) at the
    `evalPanValueDeclarations` level: struct-name collection is a no-op for an
    exception-only declaration list, so the state's struct context is kept. -/
theorem evalPanValueDeclarations_only_exn_decls
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hall : declarations.all isExnDecl = true)
    (heval : evalPanValueDeclarations state declarations memoryAccess = some state') :
    state' = { state with
      exceptions := panExceptionEntries declarations ++ state.exceptions } := by
  simp only [evalPanValueDeclarations] at heval
  cases hcollect : collectPanValueStructs declarations state.structs with
  | none => simp [hcollect] at heval
  | some structs =>
      simp only [hcollect] at heval
      have hnames : declarations.all (fun declaration => !isName declaration) = true := by
        refine List.all_eq_true.mpr (fun declaration hmem => ?_)
        have h := List.all_eq_true.mp hall declaration hmem
        cases declaration <;> simp_all [isExnDecl, isName]
      have hstructs : structs = state.structs := by
        have hno := collectPanValueStructs_of_no_names state.structs declarations hnames
        rw [hcollect] at hno
        exact Option.some.inj hno
      subst hstructs
      have hmain := evalPanValueDeclarationsWithStructs_only_exn_decls state.structs
        { state with structs := state.structs } state' declarations memoryAccess
        (by rfl) hall heval
      simpa using hmain

/-! Cake's `evaluate_decls_names`
    (`cakeml/pancake/semantics/panPropsScript.sml:1552`): a declaration list
    consisting only of structure names is skipped by declaration evaluation. -/
theorem evalPanValueDeclarationsWithStructs_names
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hall : declarations.all isName = true) :
    evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state := by
  induction declarations with
  | nil =>
      simp [evalPanValueDeclarationsWithStructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      have hname : isName declaration = true := hhead
      cases declaration with
      | name name fields =>
          simp only [evalPanValueDeclarationsWithStructs]
          exact ih htail
      | decl shape name expression =>
          simp [isName] at hname
      | function declaration =>
          simp [isName] at hname
      | exnDecl exception shape =>
          simp [isName] at hname

/-- Cake's `evaluate_decls_only_funs_and_exn_decls`
    (`cakeml/pancake/semantics/panPropsScript.sml:1561`): when every declaration
    is a function or an exception declaration, a successful evaluation changes
    only the function and exception tables, together with Flapjack's separate
    return-shape and parameter-shape maps. -/
theorem evalPanValueDeclarationsWithStructs_only_funs_and_exn_decls
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hstructs : state.structs = structs)
    (hall : declarations.all
      (fun declaration =>
        globalDeclIsFunction declaration || isExnDecl declaration) = true)
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state') :
    state' = { state with
      structs := structs
      functions := panFunctionEntries declarations ++ state.functions
      returnShapes := panReturnShapeEntries declarations ++ state.returnShapes
      parameterShapes :=
        panParameterShapeEntries declarations ++ state.parameterShapes
      exceptions := panExceptionEntries declarations ++ state.exceptions } := by
  induction declarations generalizing state with
  | nil =>
      simp only [evalPanValueDeclarationsWithStructs] at heval
      have hstate : state = state' := (Option.some.injEq _ _).mp heval
      subst hstate
      simp [panFunctionEntries, panReturnShapeEntries, panParameterShapeEntries,
        panExceptionEntries, functions, exceptionEntries, ← hstructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      cases declaration with
      | function declaration =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hwf : (declaration.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true
          · simp only [hwf] at heval
            rw [ih _ (by rfl) htail heval]
            simp [panFunctionEntries, panReturnShapeEntries,
              panParameterShapeEntries, panExceptionEntries, functions,
              exceptionEntries, List.reverse_cons, List.map_append,
              List.append_assoc]
          · simp [hwf] at heval
      | exnDecl exception shape =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
          · simp [hexists] at heval
          · by_cases hwf : isWfShape structs shape = true
            · simp only [hexists, hwf] at heval
              rw [ih _ (by rfl) htail heval]
              simp [panFunctionEntries, panReturnShapeEntries,
                panParameterShapeEntries, panExceptionEntries_cons, functions,
                List.append_assoc]
            · simp [hexists, hwf] at heval
      | decl shape name expression =>
          simp [globalDeclIsFunction, isExnDecl] at hhead
      | name name fields =>
          simp [globalDeclIsFunction, isExnDecl] at hhead

/-- Cake's `evaluate_decls_only_functions`
    (`cakeml/pancake/semantics/panPropsScript.sml:1529`): when every declaration
    is a function declaration, a successful evaluation changes only the function
    table, together with Flapjack's separate return-shape and parameter-shape
    maps. -/
theorem evalPanValueDeclarationsWithStructs_only_functions
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hstructs : state.structs = structs)
    (hall : declarations.all globalDeclIsFunction = true)
    (heval : evalPanValueDeclarationsWithStructs structs state declarations
      memoryAccess = some state') :
    state' = { state with
      structs := structs
      functions := panFunctionEntries declarations ++ state.functions
      returnShapes := panReturnShapeEntries declarations ++ state.returnShapes
      parameterShapes :=
        panParameterShapeEntries declarations ++ state.parameterShapes } := by
  induction declarations generalizing state with
  | nil =>
      simp only [evalPanValueDeclarationsWithStructs] at heval
      have hstate : state = state' := (Option.some.injEq _ _).mp heval
      subst hstate
      simp [panFunctionEntries, panReturnShapeEntries, panParameterShapeEntries,
        functions, ← hstructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      cases declaration with
      | function declaration =>
          simp only [evalPanValueDeclarationsWithStructs] at heval
          by_cases hwf : (declaration.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true
          · simp only [hwf] at heval
            rw [ih _ (by rfl) htail heval]
            simp [panFunctionEntries, panReturnShapeEntries,
              panParameterShapeEntries, functions, List.reverse_cons,
              List.map_append, List.append_assoc]
          · simp [hwf] at heval
      | decl shape name expression =>
          simp [globalDeclIsFunction] at hhead
      | exnDecl exception shape =>
          simp [globalDeclIsFunction] at hhead
      | name name fields =>
          simp [globalDeclIsFunction] at hhead

/-- Cake's `evaluate_decls_only_functions` (`panPropsScript.sml:1529`) at the
    `evalPanValueDeclarations` level: struct-name collection is a no-op for a
    function-only declaration list, so the state's struct context is kept. -/
theorem evalPanValueDeclarations_only_functions
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hall : declarations.all globalDeclIsFunction = true)
    (heval : evalPanValueDeclarations state declarations memoryAccess = some state') :
    state' = { state with
      functions := panFunctionEntries declarations ++ state.functions
      returnShapes := panReturnShapeEntries declarations ++ state.returnShapes
      parameterShapes :=
        panParameterShapeEntries declarations ++ state.parameterShapes } := by
  simp only [evalPanValueDeclarations] at heval
  cases hcollect : collectPanValueStructs declarations state.structs with
  | none => simp [hcollect] at heval
  | some structs =>
      simp only [hcollect] at heval
      have hstructs : structs = state.structs := by
        have hno := collectPanValueStructs_of_functions state.structs declarations hall
        rw [hcollect] at hno
        exact Option.some.inj hno
      subst hstructs
      have hmain := evalPanValueDeclarationsWithStructs_only_functions state.structs
        { state with structs := state.structs } state' declarations memoryAccess
        (by rfl) hall heval
      simpa using hmain

/-- Cake's `evaluate_decls_only_functions_SOME`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2390`): when every
    declaration is a function declaration whose parameter and return shapes are
    well formed, evaluation succeeds and installs exactly the function table
    together with Flapjack's separate return-shape and parameter-shape maps.
    This is the converse direction of
    `evalPanValueDeclarationsWithStructs_only_functions`. -/
theorem evalPanValueDeclarationsWithStructs_only_functions_sufficiency
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hstructs : state.structs = structs)
    (hall : declarations.all globalDeclIsFunction = true)
    (hwf : ∀ declaration, declaration ∈ declarations →
      (match declaration with
        | .function function =>
            function.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs function.returnShape
        | _ => true) = true) :
    evalPanValueDeclarationsWithStructs structs state declarations memoryAccess =
      some { state with
        structs := structs
        functions := panFunctionEntries declarations ++ state.functions
        returnShapes := panReturnShapeEntries declarations ++ state.returnShapes
        parameterShapes :=
          panParameterShapeEntries declarations ++ state.parameterShapes } := by
  induction declarations generalizing state with
  | nil =>
      simp [evalPanValueDeclarationsWithStructs, panFunctionEntries,
        panReturnShapeEntries, panParameterShapeEntries, functions, ← hstructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      cases declaration with
      | function declaration =>
          simp only [evalPanValueDeclarationsWithStructs]
          have hdeclWf : (declaration.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs declaration.returnShape) = true :=
            hwf (.function declaration) (by simp)
          rw [if_pos hdeclWf]
          rw [ih _ (by rfl) htail
            (fun other hmem => hwf other (by simp [hmem]))]
          simp [panFunctionEntries, panReturnShapeEntries,
            panParameterShapeEntries, functions, List.reverse_cons,
            List.map_append, List.append_assoc]
      | decl shape name expression =>
          simp [globalDeclIsFunction] at hhead
      | exnDecl exception shape =>
          simp [globalDeclIsFunction] at hhead
      | name name fields =>
          simp [globalDeclIsFunction] at hhead

/-! Cake's `exns_wf_evaluate_decls` (`cakeml/pancake/semantics/panPropsScript.sml:1448`):
    for an exception-only declaration list the exception-table well-formedness
    conditions (distinct ids, ids absent from the incoming table, well-formed
    shapes) are sufficient for the evaluator to succeed and install exactly
    that table.  This is the converse direction of
    `evalPanValueDeclarationsWithStructs_exceptions_wf`. -/

theorem lookupInfo_of_ne [BEq String] {name candidate : String} {value : α}
    {entries : InfoMap α} (hne : (candidate == name) = false) :
    lookupInfo name ((candidate, value) :: entries) =
      lookupInfo name entries := by
  simp [lookupInfo, hne]

theorem evalPanValueDeclarationsWithStructs_exns_wf_sufficiency
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (structs : StructContext) (state : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hstructs : state.structs = structs)
    (hall : declarations.all isExnDecl = true)
    (hnodup :
      ((panExceptionEntries declarations).map (fun entry => entry.1)).Nodup)
    (hnone : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries declarations →
        lookupInfo exception state.exceptions = none)
    (hwf : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries declarations →
        isWfShape structs shape = true) :
    evalPanValueDeclarationsWithStructs structs state declarations memoryAccess =
      some { state with
        structs := structs
        exceptions := panExceptionEntries declarations ++ state.exceptions } := by
  induction declarations generalizing state with
  | nil =>
      simp [evalPanValueDeclarationsWithStructs, panExceptionEntries_nil,
        List.nil_append, ← hstructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      cases declaration with
      | function function => simp [isExnDecl] at hhead
      | decl shape name expression => simp [isExnDecl] at hhead
      | exnDecl exception shape =>
          simp only [panExceptionEntries_cons]
          simp only [evalPanValueDeclarationsWithStructs]
          have hheadNone : lookupInfo exception state.exceptions = none :=
            hnone exception shape (by simp [panExceptionEntries_cons])
          have hheadWf : isWfShape structs shape = true :=
            hwf exception shape (by simp [panExceptionEntries_cons])
          rw [hheadNone]
          simp only [Option.isSome_none, Bool.false_eq_true, if_false,
            hheadWf, if_true]
          simp only [panExceptionEntries_cons, List.map_append, List.map_cons,
            List.map_nil] at hnodup
          obtain ⟨hnodupTail, _, hdisjoint⟩ := List.nodup_append.mp hnodup
          let next : PanValueProgramState α :=
            { state with
              structs := structs
              exceptions := (exception, shape) :: state.exceptions }
          have htailNone : ∀ eid shape',
              (eid, shape') ∈ panExceptionEntries declarations →
                lookupInfo eid next.exceptions = none := by
            intro eid shape' hmem
            have heid : eid ∈ (panExceptionEntries declarations).map
                (fun entry => entry.1) :=
              List.mem_map.mpr ⟨(eid, shape'), hmem, rfl⟩
            have hne : (exception == eid) = false := by
              rw [Bool.eq_false_iff]
              intro h
              exact (hdisjoint eid heid exception (by simp))
                (beq_iff_eq.mp h).symm
            show lookupInfo eid ((exception, shape) :: state.exceptions) = none
            rw [lookupInfo_of_ne (name := eid) (candidate := exception)
              (value := shape) (entries := state.exceptions) hne]
            exact hnone eid shape' (by
              simp only [panExceptionEntries_cons]
              exact List.mem_append_left _ hmem)
          have htailWf : ∀ eid shape',
              (eid, shape') ∈ panExceptionEntries declarations →
                isWfShape structs shape' = true :=
            fun eid shape' hmem =>
              hwf eid shape' (by
                simp only [panExceptionEntries_cons]
                exact List.mem_append_left _ hmem)
          have hrec := ih next (by rfl) htail hnodupTail htailNone htailWf
          exact hrec.trans (by simp [next, List.append_assoc])
      | name struct fields => simp [isExnDecl] at hhead

/-- Cake's `exns_wf_evaluate_decls` at the `evalPanValueDeclarations` level:
    the exception-only list collects no struct names, so the incoming struct
    context is preserved. -/
theorem evalPanValueDeclarations_exns_wf_sufficiency
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (state : PanValueProgramState α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hall : declarations.all isExnDecl = true)
    (hnodup :
      ((panExceptionEntries declarations).map (fun entry => entry.1)).Nodup)
    (hnone : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries declarations →
        lookupInfo exception state.exceptions = none)
    (hwf : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries declarations →
        isWfShape state.structs shape = true) :
    evalPanValueDeclarations state declarations memoryAccess =
      some { state with
        exceptions := panExceptionEntries declarations ++ state.exceptions } := by
  simp only [evalPanValueDeclarations]
  have hnames :
      declarations.all (fun declaration => !isName declaration) = true := by
    refine List.all_eq_true.mpr (fun declaration hmem => ?_)
    have h := List.all_eq_true.mp hall declaration hmem
    cases declaration <;> simp_all [isExnDecl, isName]
  rw [collectPanValueStructs_of_no_names state.structs declarations hnames]
  have hmain := evalPanValueDeclarationsWithStructs_exns_wf_sufficiency
    state.structs { state with structs := state.structs } declarations
    memoryAccess (by rfl) hall hnodup hnone hwf
  simpa using hmain

/-- Cake's `evaluate_decls_only_functions_and_exns_SOME`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2404`): for a list of
    function and exception declarations, the per-function parameter/return
    well-formedness conditions together with exception distinctness, freshness
    and shape well-formedness are sufficient for the evaluator to succeed and
    install exactly the function and exception tables.  This combines
    `evalPanValueDeclarationsWithStructs_only_functions_sufficiency` and
    `evalPanValueDeclarationsWithStructs_exns_wf_sufficiency`. -/
theorem evalPanValueDeclarationsWithStructs_only_functions_and_exns_sufficiency
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [LawfulBEq String]
    (structs : StructContext) (state : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hstructs : state.structs = structs)
    (hall : declarations.all
      (fun declaration =>
        globalDeclIsFunction declaration || isExnDecl declaration) = true)
    (hfunctions : ∀ declaration, declaration ∈ declarations →
      (match declaration with
        | .function function =>
            function.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs function.returnShape
        | _ => true) = true)
    (hnodup :
      ((panExceptionEntries declarations).map (fun entry => entry.1)).Nodup)
    (hnone : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries declarations →
        lookupInfo exception state.exceptions = none)
    (hexns : ∀ exception shape,
      (exception, shape) ∈ panExceptionEntries declarations →
        isWfShape structs shape = true) :
    evalPanValueDeclarationsWithStructs structs state declarations memoryAccess =
      some { state with
        structs := structs
        functions := panFunctionEntries declarations ++ state.functions
        returnShapes := panReturnShapeEntries declarations ++ state.returnShapes
        parameterShapes :=
          panParameterShapeEntries declarations ++ state.parameterShapes
        exceptions := panExceptionEntries declarations ++ state.exceptions } := by
  induction declarations generalizing state with
  | nil =>
      simp [evalPanValueDeclarationsWithStructs, panFunctionEntries,
        panReturnShapeEntries, panParameterShapeEntries, panExceptionEntries_nil,
        functions, List.nil_append, ← hstructs]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      cases declaration with
      | function function =>
          simp only [evalPanValueDeclarationsWithStructs]
          have hdeclWf : (function.params.all
                (fun parameter => isWfShape structs parameter.2) &&
              isWfShape structs function.returnShape) = true :=
            hfunctions (.function function) (by simp)
          rw [if_pos hdeclWf]
          have hnodupTail :
              ((panExceptionEntries declarations).map
                (fun entry => entry.1)).Nodup := by
            simpa [panExceptionEntries_cons] using hnodup
          have hnoneTail : ∀ exception shape,
              (exception, shape) ∈ panExceptionEntries declarations →
                lookupInfo exception state.exceptions = none := by
            intro exception shape hmem
            exact hnone exception shape (by
              simpa [panExceptionEntries_cons] using hmem)
          have hexnsTail : ∀ exception shape,
              (exception, shape) ∈ panExceptionEntries declarations →
                isWfShape structs shape = true := by
            intro exception shape hmem
            exact hexns exception shape (by
              simpa [panExceptionEntries_cons] using hmem)
          let next : PanValueProgramState α :=
            { state with
              structs := structs
              functions :=
                (function.name, function.params.map Prod.fst, function.body) ::
                  state.functions
              returnShapes :=
                (function.name, function.returnShape) :: state.returnShapes
              parameterShapes :=
                (function.name, function.params) :: state.parameterShapes }
          exact (ih next (by rfl) htail
            (fun other hmem => hfunctions other (by simp [hmem]))
            hnodupTail hnoneTail hexnsTail).trans (by
              simp [next, panFunctionEntries, panReturnShapeEntries,
                panParameterShapeEntries, panExceptionEntries_cons, functions,
                List.reverse_cons, List.map_append,
                List.append_assoc])
      | exnDecl exception shape =>
          simp only [panExceptionEntries_cons]
          simp only [evalPanValueDeclarationsWithStructs]
          have hheadNone : lookupInfo exception state.exceptions = none :=
            hnone exception shape (by simp [panExceptionEntries_cons])
          have hheadWf : isWfShape structs shape = true :=
            hexns exception shape (by simp [panExceptionEntries_cons])
          rw [hheadNone]
          simp only [Option.isSome_none, Bool.false_eq_true, if_false,
            hheadWf, if_true]
          simp only [panExceptionEntries_cons, List.map_append, List.map_cons,
            List.map_nil] at hnodup
          obtain ⟨hnodupTail, _, hdisjoint⟩ := List.nodup_append.mp hnodup
          let next : PanValueProgramState α :=
            { state with
              structs := structs
              exceptions := (exception, shape) :: state.exceptions }
          have hnoneTail : ∀ eid shape',
              (eid, shape') ∈ panExceptionEntries declarations →
                lookupInfo eid next.exceptions = none := by
            intro eid shape' hmem
            have heid : eid ∈ (panExceptionEntries declarations).map
                (fun entry => entry.1) :=
              List.mem_map.mpr ⟨(eid, shape'), hmem, rfl⟩
            have hne : (exception == eid) = false := by
              rw [Bool.eq_false_iff]
              intro h
              exact (hdisjoint eid heid exception (by simp))
                (beq_iff_eq.mp h).symm
            show lookupInfo eid ((exception, shape) :: state.exceptions) = none
            rw [lookupInfo_of_ne (name := eid) (candidate := exception)
              (value := shape) (entries := state.exceptions) hne]
            exact hnone eid shape' (by
              simp only [panExceptionEntries_cons]
              exact List.mem_append_left _ hmem)
          have hexnsTail : ∀ eid shape',
              (eid, shape') ∈ panExceptionEntries declarations →
                isWfShape structs shape' = true :=
            fun eid shape' hmem =>
              hexns eid shape' (by
                simp only [panExceptionEntries_cons]
                exact List.mem_append_left _ hmem)
          have hrec := ih next (by rfl) htail
            (fun other hmem => hfunctions other (by simp [hmem]))
            hnodupTail hnoneTail hexnsTail
          exact hrec.trans (by
            simp [next, panFunctionEntries,
              panReturnShapeEntries, panParameterShapeEntries, functions,
              List.append_assoc])
      | decl shape name expression =>
          simp [globalDeclIsFunction, isExnDecl] at hhead
      | name name fields =>
          simp [globalDeclIsFunction, isExnDecl] at hhead

theorem evalPanValueDeclarationsWithStructs_function_exnDecl_commute
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (declaration : FunDecl α) (exception : ExceptionId) (shape : Shape)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    evalPanValueDeclarationsWithStructs structs state
        (.function declaration :: .exnDecl exception shape :: declarations)
        memoryAccess =
      evalPanValueDeclarationsWithStructs structs state
        (.exnDecl exception shape :: .function declaration :: declarations)
        memoryAccess := by
  simp only [evalPanValueDeclarationsWithStructs]
  by_cases hwf : (declaration.params.all
        (fun parameter => isWfShape structs parameter.2) &&
      isWfShape structs declaration.returnShape) = true
  · by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
    · simp [hwf, hexists]
    · by_cases hshape : isWfShape structs shape = true
      · simp [hwf, hexists, hshape]
      · simp [hwf, hexists, hshape]
  · by_cases hexists : (lookupInfo exception state.exceptions).isSome = true
    · simp [hwf, hexists]
    · by_cases hshape : isWfShape structs shape = true
      · simp [hwf, hexists, hshape]
      · simp [hwf, hexists, hshape]

/-- Cake's `evaluate_decls_one_fun_last`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1854`): a function
    declaration may be moved to the front past a list of global and exception
    declarations. -/
theorem evalPanValueDeclarationsWithStructs_one_fun_last
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (declaration : FunDecl α) (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hrest : declarations.all (fun declaration =>
      isDecl declaration || isExnDecl declaration) = true) :
    evalPanValueDeclarationsWithStructs structs state
        (declarations ++ [.function declaration]) memoryAccess =
      evalPanValueDeclarationsWithStructs structs state
        (.function declaration :: declarations) memoryAccess := by
  induction declarations generalizing state with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hrest
      obtain ⟨hhead, htail⟩ := hrest
      rw [List.cons_append]
      cases head with
      | function function => simp [isDecl, isExnDecl] at hhead
      | name name fields => simp [isDecl, isExnDecl] at hhead
      | decl shape name expression =>
          rw [evalPanValueDeclarationsWithStructs_function_decl_commute]
          simp only [evalPanValueDeclarationsWithStructs]
          cases hval : evalPanValueExp structs (fun _ => none) state.globals
              state.memory state.baseAddress state.topAddress state.bytesInWord
              expression (memoryAccess := memoryAccess) with
          | none => rfl
          | some value =>
              by_cases hmatch :
                  panShapeMatches (panValueShape structs value) shape = true
              · simp [hmatch]
                rw [ih _ htail]
                simp only [evalPanValueDeclarationsWithStructs]
              · simp [hmatch]
      | exnDecl exception shape =>
          rw [evalPanValueDeclarationsWithStructs_function_exnDecl_commute]
          simp only [evalPanValueDeclarationsWithStructs]
          rw [ih _ htail]
          simp only [evalPanValueDeclarationsWithStructs]

/-- The well-founded declaration filter agrees with `List.filter`, which makes
    the core list-filter API available for the resort argument. -/
theorem globalDeclsFilter_eq_filter (predicate : Decl α → Bool)
    (declarations : List (Decl α)) :
    globalDeclsFilter predicate declarations =
      List.filter predicate declarations := by
  induction declarations with
  | nil => simp [globalDeclsFilter]
  | cons declaration declarations ih =>
      cases h : predicate declaration <;> simp [globalDeclsFilter, h, ih]

theorem globalDeclsFilter_append (predicate : Decl α → Bool)
    (left right : List (Decl α)) :
    globalDeclsFilter predicate (left ++ right) =
      globalDeclsFilter predicate left ++ globalDeclsFilter predicate right := by
  simp only [globalDeclsFilter_eq_filter, List.filter_append]

/-- Exception declarations commute past global declarations. -/
theorem evalPanValueDeclarationsWithStructs_exnDecl_decl_commute
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (exception : ExceptionId) (shape : Shape)
    (declShape : Shape) (name : DeclarationName) (expression : Exp α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α)) :
    evalPanValueDeclarationsWithStructs structs state
        (.exnDecl exception shape :: .decl declShape name expression :: declarations)
        memoryAccess =
      evalPanValueDeclarationsWithStructs structs state
        (.decl declShape name expression :: .exnDecl exception shape :: declarations)
        memoryAccess := by
  simp only [evalPanValueDeclarationsWithStructs]
  cases hval : evalPanValueExp structs (fun _ => none) state.globals
      state.memory state.baseAddress state.topAddress state.bytesInWord
      expression (memoryAccess := memoryAccess) with
  | none =>
      by_cases hexists : (lookupInfo exception state.exceptions).isSome = true <;>
        by_cases hshape : isWfShape structs shape = true <;>
        simp [hexists, hshape]
  | some value =>
      by_cases hmatch : panShapeMatches (panValueShape structs value) declShape = true <;>
        by_cases hexists : (lookupInfo exception state.exceptions).isSome = true <;>
        by_cases hshape : isWfShape structs shape = true <;>
        simp [hmatch, hexists, hshape]

/-- Bubbling a declaration that commutes with every element of `rest` to the
    end of that list. -/
theorem evalPanValueDeclarationsWithStructs_bubble_last
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (memoryAccess : Option (PanValueMemoryAccess α))
    (declaration : Decl α) (rest : List (Decl α))
    (hcomm : ∀ other ∈ rest, ∀ state tail,
      evalPanValueDeclarationsWithStructs structs state
          (declaration :: other :: tail) memoryAccess =
        evalPanValueDeclarationsWithStructs structs state
          (other :: declaration :: tail) memoryAccess) :
    ∀ state,
      evalPanValueDeclarationsWithStructs structs state
          (declaration :: rest) memoryAccess =
        evalPanValueDeclarationsWithStructs structs state
          (rest ++ [declaration]) memoryAccess := by
  induction rest with
  | nil => intro state; rw [List.nil_append]
  | cons other rest ih =>
      intro state
      have hcomm' : ∀ x ∈ rest, ∀ state tail,
          evalPanValueDeclarationsWithStructs structs state
              (declaration :: x :: tail) memoryAccess =
            evalPanValueDeclarationsWithStructs structs state
              (x :: declaration :: tail) memoryAccess :=
        fun x hx => hcomm x (List.mem_cons_of_mem other hx)
      rw [hcomm other (List.mem_cons_self ..) state rest]
      rw [List.cons_append]
      rw [show other :: declaration :: rest = [other] ++ (declaration :: rest) from rfl]
      rw [show other :: (rest ++ [declaration]) =
        [other] ++ (rest ++ [declaration]) from rfl]
      rw [evalPanValueDeclarationsWithStructs_append]
      rw [evalPanValueDeclarationsWithStructs_append]
      cases hstep : evalPanValueDeclarationsWithStructs structs state [other]
          memoryAccess with
      | none => rfl
      | some state' => exact ih hcomm' state'

/-- Moving a declaration out of a middle block and past a tail block it commutes
    with. -/
theorem evalPanValueDeclarationsWithStructs_insert_last
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (memoryAccess : Option (PanValueMemoryAccess α))
    (declaration : Decl α) (middle tail : List (Decl α))
    (hcomm : ∀ other ∈ tail, ∀ state rest,
      evalPanValueDeclarationsWithStructs structs state
          (declaration :: other :: rest) memoryAccess =
        evalPanValueDeclarationsWithStructs structs state
          (other :: declaration :: rest) memoryAccess) :
    ∀ state,
      evalPanValueDeclarationsWithStructs structs state
          ((middle ++ [declaration]) ++ tail) memoryAccess =
        evalPanValueDeclarationsWithStructs structs state
          ((middle ++ tail) ++ [declaration]) memoryAccess := by
  intro state
  rw [show (middle ++ [declaration]) ++ tail =
      middle ++ ([declaration] ++ tail) from by simp [List.append_assoc]]
  rw [show (middle ++ tail) ++ [declaration] =
      middle ++ (tail ++ [declaration]) from by simp [List.append_assoc]]
  rw [evalPanValueDeclarationsWithStructs_append]
  rw [evalPanValueDeclarationsWithStructs_append]
  cases h : evalPanValueDeclarationsWithStructs structs state middle memoryAccess with
  | none => rfl
  | some state' =>
      simpa using evalPanValueDeclarationsWithStructs_bubble_last structs memoryAccess
        declaration tail hcomm state'

/-- Cake's `resort_decls_evaluate`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1874`): the global pass's
    declaration resort preserves declaration evaluation. -/
theorem evalPanValueDeclarationsWithStructs_resortDecls
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hall : declarations.all (fun declaration =>
      isDecl declaration || isExnDecl declaration ||
        globalDeclIsFunction declaration) = true) :
    evalPanValueDeclarationsWithStructs structs state
        (globalResortDecls declarations) memoryAccess =
      evalPanValueDeclarationsWithStructs structs state declarations memoryAccess := by
  have h : ∀ reversed : List (Decl α),
      (reversed.reverse.all (fun declaration =>
        isDecl declaration || isExnDecl declaration ||
          globalDeclIsFunction declaration) = true) →
      evalPanValueDeclarationsWithStructs structs state
          (globalResortDecls reversed.reverse) memoryAccess =
        evalPanValueDeclarationsWithStructs structs state reversed.reverse
          memoryAccess := by
    intro reversed
    induction reversed with
    | nil => intro _; simp [globalResortDecls, globalDeclsFilter]
    | cons declaration rest ih =>
        intro hall
        rw [List.reverse_cons]
        rw [List.reverse_cons] at hall
        have hdecl : (isDecl declaration || isExnDecl declaration ||
            globalDeclIsFunction declaration) = true :=
          List.all_eq_true.mp hall declaration
            (List.mem_append_right rest.reverse (List.mem_singleton_self declaration))
        have hallRest : rest.reverse.all (fun entry =>
            isDecl entry || isExnDecl entry ||
              globalDeclIsFunction entry) = true :=
          List.all_eq_true.mpr (fun entry hmem =>
            List.all_eq_true.mp hall entry
              (List.mem_append_left [declaration] hmem))
        have hbase := ih hallRest
        cases declaration with
        | function function =>
            have hresort : globalResortDecls (rest.reverse ++ [.function function]) =
                globalResortDecls rest.reverse ++ [.function function] := by
              simp only [globalResortDecls, globalDeclsFilter_append]
              simp [globalDeclsFilter, globalDeclIsName, globalDeclIsException,
                globalDeclIsGlobal, globalDeclIsFunction]
            rw [hresort]
            rw [evalPanValueDeclarationsWithStructs_append]
            rw [hbase]
            rw [evalPanValueDeclarationsWithStructs_append]
        | decl shape name expression =>
            have hresort : globalResortDecls
                (rest.reverse ++ [.decl shape name expression]) =
                (globalDeclsFilter globalDeclIsName rest.reverse ++
                  globalDeclsFilter globalDeclIsException rest.reverse ++
                  globalDeclsFilter globalDeclIsGlobal rest.reverse ++
                  [.decl shape name expression]) ++
                globalDeclsFilter globalDeclIsFunction rest.reverse := by
              simp only [globalResortDecls, globalDeclsFilter_append]
              simp [globalDeclsFilter, globalDeclIsName, globalDeclIsException,
                globalDeclIsGlobal, globalDeclIsFunction, List.append_assoc]
            have hcomm : ∀ other ∈
                  globalDeclsFilter globalDeclIsFunction rest.reverse,
                ∀ state' tail,
                  evalPanValueDeclarationsWithStructs structs state'
                      (.decl shape name expression :: other :: tail) memoryAccess =
                    evalPanValueDeclarationsWithStructs structs state'
                      (other :: .decl shape name expression :: tail) memoryAccess := by
              intro other hmem state' tail
              have hfun : globalDeclIsFunction other = true :=
                List.all_eq_true.mp
                  (globalDeclsFilter_all globalDeclIsFunction rest.reverse) other hmem
              cases other with
              | function function =>
                  exact (evalPanValueDeclarationsWithStructs_function_decl_commute
                    structs state' function shape name expression tail
                    memoryAccess).symm
              | decl _ _ _ => simp [globalDeclIsFunction] at hfun
              | exnDecl _ _ => simp [globalDeclIsFunction] at hfun
              | name _ _ => simp [globalDeclIsFunction] at hfun
            rw [hresort]
            rw [evalPanValueDeclarationsWithStructs_insert_last structs memoryAccess
              (.decl shape name expression)
              (globalDeclsFilter globalDeclIsName rest.reverse ++
                globalDeclsFilter globalDeclIsException rest.reverse ++
                globalDeclsFilter globalDeclIsGlobal rest.reverse)
              (globalDeclsFilter globalDeclIsFunction rest.reverse) hcomm]
            rw [show
              (globalDeclsFilter globalDeclIsName rest.reverse ++
                  globalDeclsFilter globalDeclIsException rest.reverse ++
                  globalDeclsFilter globalDeclIsGlobal rest.reverse) ++
                globalDeclsFilter globalDeclIsFunction rest.reverse =
              globalResortDecls rest.reverse from rfl]
            rw [evalPanValueDeclarationsWithStructs_append]
            rw [hbase]
            rw [evalPanValueDeclarationsWithStructs_append]
        | exnDecl exception shape =>
            have hresort : globalResortDecls (rest.reverse ++ [.exnDecl exception shape]) =
                (globalDeclsFilter globalDeclIsName rest.reverse ++
                  globalDeclsFilter globalDeclIsException rest.reverse ++
                  [.exnDecl exception shape]) ++
                (globalDeclsFilter globalDeclIsGlobal rest.reverse ++
                  globalDeclsFilter globalDeclIsFunction rest.reverse) := by
              simp only [globalResortDecls, globalDeclsFilter_append]
              simp [globalDeclsFilter, globalDeclIsName, globalDeclIsException,
                globalDeclIsGlobal, globalDeclIsFunction, List.append_assoc]
            have hcomm : ∀ other ∈
                  globalDeclsFilter globalDeclIsGlobal rest.reverse ++
                    globalDeclsFilter globalDeclIsFunction rest.reverse,
                ∀ state' tail,
                  evalPanValueDeclarationsWithStructs structs state'
                      (.exnDecl exception shape :: other :: tail) memoryAccess =
                    evalPanValueDeclarationsWithStructs structs state'
                      (other :: .exnDecl exception shape :: tail) memoryAccess := by
              intro other hmem state' tail
              rcases List.mem_append.mp hmem with hmem | hmem
              · have hglobal : globalDeclIsGlobal other = true :=
                  List.all_eq_true.mp
                    (globalDeclsFilter_all globalDeclIsGlobal rest.reverse) other hmem
                cases other with
                | decl declShape declName declExpr =>
                    exact evalPanValueDeclarationsWithStructs_exnDecl_decl_commute
                      structs state' exception shape declShape declName declExpr
                      tail memoryAccess
                | function _ => simp [globalDeclIsGlobal] at hglobal
                | exnDecl _ _ => simp [globalDeclIsGlobal] at hglobal
                | name _ _ => simp [globalDeclIsGlobal] at hglobal
              · have hfun : globalDeclIsFunction other = true :=
                  List.all_eq_true.mp
                    (globalDeclsFilter_all globalDeclIsFunction rest.reverse) other hmem
                cases other with
                | function function =>
                    exact (evalPanValueDeclarationsWithStructs_function_exnDecl_commute
                      structs state' function exception shape tail memoryAccess).symm
                | decl _ _ _ => simp [globalDeclIsFunction] at hfun
                | exnDecl _ _ => simp [globalDeclIsFunction] at hfun
                | name _ _ => simp [globalDeclIsFunction] at hfun
            rw [hresort]
            rw [evalPanValueDeclarationsWithStructs_insert_last structs memoryAccess
              (.exnDecl exception shape)
              (globalDeclsFilter globalDeclIsName rest.reverse ++
                globalDeclsFilter globalDeclIsException rest.reverse)
              (globalDeclsFilter globalDeclIsGlobal rest.reverse ++
                globalDeclsFilter globalDeclIsFunction rest.reverse) hcomm]
            rw [show
              (globalDeclsFilter globalDeclIsName rest.reverse ++
                  globalDeclsFilter globalDeclIsException rest.reverse) ++
                (globalDeclsFilter globalDeclIsGlobal rest.reverse ++
                  globalDeclsFilter globalDeclIsFunction rest.reverse) =
              globalResortDecls rest.reverse from by
              rw [globalResortDecls]
              exact (List.append_assoc
                (globalDeclsFilter globalDeclIsName rest.reverse ++
                  globalDeclsFilter globalDeclIsException rest.reverse)
                (globalDeclsFilter globalDeclIsGlobal rest.reverse)
                (globalDeclsFilter globalDeclIsFunction rest.reverse)).symm]
            rw [evalPanValueDeclarationsWithStructs_append]
            rw [hbase]
            rw [evalPanValueDeclarationsWithStructs_append]
        | name name fields =>
            simp [isDecl, isExnDecl, globalDeclIsFunction] at hdecl
  simpa using h declarations.reverse (by simpa using hall)

/-- Cake's `resort_decls_evaluate_IMP`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1943`). -/
theorem evalPanValueDeclarationsWithStructs_resortDecls_imp
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (state state' : PanValueProgramState α)
    (declarations : List (Decl α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (hall : declarations.all (fun declaration =>
      isDecl declaration || isExnDecl declaration ||
        globalDeclIsFunction declaration) = true)
    (heval : evalPanValueDeclarationsWithStructs structs state
        (globalResortDecls declarations) memoryAccess = some state') :
    evalPanValueDeclarationsWithStructs structs state declarations memoryAccess =
      some state' := by
  rw [evalPanValueDeclarationsWithStructs_resortDecls structs state declarations
    memoryAccess hall] at heval
  exact heval

/-! Counterpart of Cake's `filter_not_mem_self`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1407`):

    FILTER (\x. ~MEM x l) l = []

Filtering a list by its own complement of membership removes every element. -/
theorem filter_not_mem_self {α : Type} [DecidableEq α] (l : List α) :
    l.filter (fun x => decide (x ∉ l)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp [hx]

/-! Counterpart of Cake's `MAP_SOME_MEM_lemma`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4060`):

    MAP f (FLAT xs) = MAP SOME (FLAT ys) /\ MEM zs xs /\ MEM z zs
      ==> ?y. f z = SOME y /\ MEM y (FLAT ys)

The unused existential of the original is dropped. -/
theorem map_flatten_eq_map_some_flatten {α β : Type} (f : α → Option β)
    (xs : List (List α)) (ys : List (List β)) (zs : List α) (z : α)
    (h : xs.flatten.map f = ys.flatten.map some)
    (hzs : zs ∈ xs) (hz : z ∈ zs) :
    ∃ y, f z = some y ∧ y ∈ ys.flatten := by
  have hzflat : z ∈ xs.flatten := List.mem_flatten.mpr ⟨zs, hzs, hz⟩
  have hzmap : f z ∈ xs.flatten.map f := List.mem_map.mpr ⟨z, hzflat, rfl⟩
  rw [h] at hzmap
  obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hzmap
  exact ⟨y, hfy.symm, hy⟩

/-! Counterpart of Cake's `mod_eq_lt_eq`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4621`):

    !n x m. n < x /\ m < x /\ n MOD x = m MOD x ==> n = m

Below the modulus, reduction is the identity. -/
theorem mod_eq_of_lt_eq {n x m : Nat} (hn : n < x) (hm : m < x)
    (h : n % x = m % x) : n = m := by
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at h
  exact h

/-! Counterpart of Cake's `pair_map_I`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:4630`):

    (λ(x,y). (x,y)) = I

The anonymous pair constructor is the identity on pairs. -/
theorem prod_mk_pair_eq_id {α β : Type} :
    (fun p : α × β => (p.1, p.2)) = id := by
  funext p
  cases p
  rfl

/-! Counterpart of Cake's `not_none_then_some`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:3593`):

    x <> NONE <=> ?a. x = SOME a -/
theorem option_ne_none_iff_exists {α : Type} (x : Option α) :
    x ≠ none ↔ ∃ a, x = some a := by
  constructor
  · intro h
    cases x with
    | none => exact absurd rfl h
    | some a => exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact Option.some_ne_none a

end Flapjack
