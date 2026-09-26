import Flapjack.Pancake.PanStructs
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.PanLang.Prog

/-!
Byte-rangedness preservation for the named-structure elimination pass
(`structCompileTop`). The pass rewrites every shape in a declaration through
`structCompileShape`, so proving `DeclByteRanged` survives it needs
byte-rangedness of the struct shapes, the compiled expressions, and the
compiled programs, carried by the struct context invariant `CtxBR`.

Nothing here is a HOL port; the definitions already live in `PanStructs.lean`,
and these lemmas are Flapjack-specific infrastructure for the executed
parser-to-Crep boundary.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Byte-rangedness of the production struct context used by the struct pass. -/
def CtxBR (c : StructContext) : Prop :=
  ∀ p ∈ c, NameRanged p.1 ∧ ListParamByteRanged p.2.fields

theorem lookupInfoWithRest_exists_mem [BEq String] {name : String} {context : StructContext}
    {info : StructInfo} {suffix : StructContext}
    (h : lookupInfoWithRest name context = some (info, suffix)) :
    ∃ k, (k, info) ∈ context := by
  induction context with
  | nil => simp only [lookupInfoWithRest] at h; cases h
  | cons entry rest ih =>
      by_cases hc : entry.1 == name
      · simp only [lookupInfoWithRest, hc] at h
        injection h with hp
        injection hp with h1 _
        exact ⟨entry.1, by simp only [List.mem_cons]; left; cases entry; simp_all⟩
      · simp only [lookupInfoWithRest, hc] at h
        obtain ⟨k, hk⟩ := ih h
        exact ⟨k, by simp [hk]⟩

theorem lookupInfoWithRest_ctxBR [BEq String] {name : String} {context : StructContext}
    {info : StructInfo} {suffix : StructContext}
    (h : lookupInfoWithRest name context = some (info, suffix)) (hc : CtxBR context) :
    CtxBR suffix := by
  induction context with
  | nil => simp only [lookupInfoWithRest] at h; cases h
  | cons entry rest ih =>
      by_cases hmatch : entry.1 == name
      · simp only [lookupInfoWithRest, hmatch] at h
        injection h with hp
        injection hp with _ h2
        subst h2
        exact fun p hp => hc p (by simp [hp])
      · simp only [lookupInfoWithRest, hmatch] at h
        exact ih h (fun p hp => hc p (by simp [hp]))

theorem structCompileShapeWF_byteRanged (context : StructContext) (shape : Shape)
    (hc : CtxBR context) (hs : ShapeByteRanged shape) :
    ShapeByteRanged (structCompileShapeWF context shape) := by
  refine (structCompileShapeWF.induct
    (motive1 := fun context shapes => CtxBR context → (∀ s ∈ shapes, ShapeByteRanged s) →
        ∀ s ∈ structCompileShapeWF.structCompileShapesWF context shapes, ShapeByteRanged s)
    (motive2 := fun context shape => CtxBR context → ShapeByteRanged shape →
        ShapeByteRanged (structCompileShapeWF context shape)) ?_ ?_ ?_ ?_ ?_ ?_) context shape hc hs
  · intro _context _ _ s hs
    simp [structCompileShapeWF.structCompileShapesWF] at hs
  · intro context shape shapes ihshape ihshapes hctx hcons s hmem
    simp only [structCompileShapeWF.structCompileShapesWF] at hmem
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact ihshape hctx (hcons shape (by simp))
    · exact ihshapes hctx (fun t ht => hcons t (by simp [ht])) s hmem'
  · intro _context _ _
    simp [structCompileShapeWF, ShapeByteRanged]
  · intro context shapes ihshapes hctx hcomb
    rw [structCompileShapeWF]
    simp only [ShapeByteRanged] at hcomb ⊢
    exact ihshapes hctx hcomb
  · intro context name info suffix hlookup ihfields hctx _hnamed
    rw [structCompileShapeWF]
    split
    · rename_i info' suffix' heq
      rw [hlookup] at heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [ShapeByteRanged]
      refine ihfields (lookupInfoWithRest_ctxBR hlookup hctx) ?_
      intro s hsinfo
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hsinfo
      obtain ⟨k, hk⟩ := lookupInfoWithRest_exists_mem hlookup
      exact ((hctx (k, info) hk).2 p hp).2
    · rename_i heq
      rw [hlookup] at heq
      simp at heq
  · intro context name hlookup _hctx _hnamed
    rw [structCompileShapeWF]
    split
    · rename_i info' suffix' heq
      rw [hlookup] at heq
      simp at heq
    · simp [ShapeByteRanged]

theorem structCompileShape_byteRanged (context : StructContext) (shape : Shape)
    (hc : CtxBR context) (hs : ShapeByteRanged shape) :
    ShapeByteRanged (structCompileShape context shape) :=
  structCompileShapeWF_byteRanged context shape hc hs

theorem structCompileShapesWF_byteRanged (context : StructContext) (hc : CtxBR context)
    (shapes : List Shape) (hs : ∀ s ∈ shapes, ShapeByteRanged s) :
    ∀ s ∈ structCompileShapeWF.structCompileShapesWF context shapes, ShapeByteRanged s := by
  induction shapes with
  | nil => intro s hmem; simp [structCompileShapeWF.structCompileShapesWF] at hmem
  | cons shape shapes ih =>
      intro s hmem
      simp only [structCompileShapeWF.structCompileShapesWF] at hmem
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact structCompileShapeWF_byteRanged context shape hc (hs shape (by simp))
      · exact ih (fun t ht => hs t (by simp [ht])) s hmem'

private theorem listExpByteRanged_iff {width : Nat} (l : List (Exp (BitVec width))) :
    ListExpByteRanged l ↔ ∀ e ∈ l, ExpByteRanged e := by
  induction l with
  | nil => simp [ListExpByteRanged]
  | cons e es ih =>
    constructor
    · intro h e' he'
      rw [List.mem_cons] at he'
      rcases he' with rfl | he'
      · exact h.1
      · exact ih.mp h.2 e' he'
    · intro h
      exact ⟨h e (by simp), ih.mpr (fun x hx => h x (by simp [hx]))⟩

private theorem listFieldByteRanged_iff {width : Nat} (l : List (String × Exp (BitVec width))) :
    ListFieldByteRanged l ↔
      ∀ p ∈ l, (∀ c ∈ p.1.toList, c.toNat < 256) ∧ ExpByteRanged p.2 := by
  induction l with
  | nil => simp [ListFieldByteRanged]
  | cons p ps ih =>
    constructor
    · intro h q hq
      rw [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨h.1, h.2.1⟩
      · exact ih.mp h.2.2 q hq
    · intro h
      exact ⟨(h p (by simp)).1, (h p (by simp)).2, ih.mpr (fun q hq => h q (by simp [hq]))⟩

private theorem lookupInfo_value_byteRanged [BEq String] {key : String}
    {entries : List (String × Exp (BitVec width))} {value : Exp (BitVec width)}
    (h : lookupInfo key entries = some value)
    (hall : ∀ p ∈ entries, ExpByteRanged p.2) : ExpByteRanged value := by
  induction entries with
  | nil => simp [lookupInfo] at h
  | cons entry rest ih =>
    obtain ⟨candidate, v⟩ := entry
    by_cases hc : candidate == key
    · simp only [lookupInfo, hc] at h
      injection h with h
      subst h
      exact hall (candidate, v) (by simp)
    · simp only [lookupInfo, hc] at h
      exact ih h (fun p hp => hall p (by simp [hp]))

theorem structSelectFields_byteRanged [BEq String]
    (fields : List (FieldName × Shape)) (compiled : List (String × Exp (BitVec width)))
    (h : ∀ p ∈ compiled, ExpByteRanged p.2) :
    ∀ e ∈ structSelectFields fields compiled, ExpByteRanged e := by
  induction fields with
  | nil => intro e he; simp [structSelectFields] at he
  | cons f fs ih =>
    obtain ⟨field, shape⟩ := f
    intro e he
    simp only [structSelectFields] at he
    split at he
    · rename_i expression hlookup
      rw [List.mem_cons] at he
      rcases he with rfl | he'
      · exact lookupInfo_value_byteRanged hlookup h
      · exact ih e he'
    · exact ih e he

theorem structCompileExp_byteRanged {width : Nat} [BEq String] (context : StructPassContext)
    (hc : CtxBR context.structs) :
    ∀ e : Exp (BitVec width), ExpByteRanged e → ExpByteRanged (structCompileExp context e) := by
  refine (structCompileExp.induct (α := BitVec width) context
    (motive1 := fun l => (∀ e ∈ l, ExpByteRanged e) →
        ∀ e ∈ structCompileExp.structCompileExps context l, ExpByteRanged e)
    (motive2 := fun e => ExpByteRanged e → ExpByteRanged (structCompileExp context e))
    (motive3 := fun l => (∀ p ∈ l, ExpByteRanged p.2) →
        ∀ p ∈ structCompileExp.structCompileFields context l, ExpByteRanged p.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · intro _ e he
    simp [structCompileExp.structCompileExps] at he
  · intro e es ihe ihes hall x hx
    simp only [structCompileExp.structCompileExps] at hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ihe (hall e (by simp))
    · exact ihes (fun y hy => hall y (by simp [hy])) x hx'
  · intro fields ih hv
    rw [structCompileExp]
    exact (listExpByteRanged_iff _).mpr (ih ((listExpByteRanged_iff _).mp hv))
  · intro index value ih hv
    rw [structCompileExp]
    simp only [ExpByteRanged] at hv ⊢
    exact ih hv
  · intro name fields info hlookup ihfields hv
    rw [structCompileExp]
    simp only [hlookup]
    exact (listExpByteRanged_iff _).mpr
      (structSelectFields_byteRanged info.fields _
        (ihfields (fun p hp => ((listFieldByteRanged_iff fields).mp hv.2 p hp).2)))
  · intro name fields hlookup _hv
    rw [structCompileExp]
    simp only [hlookup]
    simp [ExpByteRanged, ListExpByteRanged]
  · intro field value ih hv
    rw [structCompileExp]
    simp only [ExpByteRanged] at hv ⊢
    exact ih hv.2
  · intro shape address ih hv
    rw [structCompileExp]
    exact ⟨structCompileShape_byteRanged context.structs shape hc hv.1, ih hv.2⟩
  · intro address ih hv
    rw [structCompileExp]
    exact ih hv
  · intro address ih hv
    rw [structCompileExp]
    exact ih hv
  · intro operator arguments ih hv
    rw [structCompileExp]
    exact (listExpByteRanged_iff _).mpr (ih ((listExpByteRanged_iff _).mp hv))
  · intro operator arguments ih hv
    rw [structCompileExp]
    exact (listExpByteRanged_iff _).mpr (ih ((listExpByteRanged_iff _).mp hv))
  · intro operator left right ihl ihr hv
    rw [structCompileExp]
    exact ⟨ihl hv.1, ihr hv.2⟩
  · intro operator left right ihl ihr hv
    rw [structCompileExp]
    exact ⟨ihl hv.1, ihr hv.2⟩
  · intro expression h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hv
    cases expression with
    | const v => simp [ExpByteRanged]
    | var k name => simpa [structCompileExp] using hv
    | baseAddr => simp [structCompileExp, ExpByteRanged]
    | topAddr => simp [structCompileExp, ExpByteRanged]
    | bytesInWord => simp [structCompileExp, ExpByteRanged]
    | rStruct fs => exact (h1 fs rfl).elim
    | rField i v => exact (h2 i v rfl).elim
    | nStruct nm fs => exact (h3 nm fs rfl).elim
    | nField f v => exact (h4 f v rfl).elim
    | load sh a => exact (h5 sh a rfl).elim
    | load32 a => exact (h6 a rfl).elim
    | loadByte a => exact (h7 a rfl).elim
    | op o args => exact (h8 o args rfl).elim
    | panOp o args => exact (h9 o args rfl).elim
    | cmp o l r => exact (h10 o l r rfl).elim
    | shift o l r => exact (h11 o l r rfl).elim
  · intro _ p hp
    simp [structCompileExp.structCompileFields] at hp
  · intro field expression fields ihe ih hall p hp
    simp only [structCompileExp.structCompileFields] at hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | hp'
    · exact ihe (hall (field, expression) (by simp))
    · exact ih (fun q hq => hall q (by simp [hq])) p hp'

private theorem structCompileExps_byteRanged {width : Nat} [BEq String]
    (context : StructPassContext) (hc : CtxBR context.structs) :
    ∀ expressions : List (Exp (BitVec width)),
      (∀ expression ∈ expressions, ExpByteRanged expression) →
        ∀ expression ∈ structCompileExp.structCompileExps context expressions,
          ExpByteRanged expression := by
  intro expressions
  induction expressions with
  | nil => simp [structCompileExp.structCompileExps]
  | cons expression rest ih =>
      intro hall compiled hmem
      simp only [structCompileExp.structCompileExps] at hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        exact structCompileExp_byteRanged context hc expression (hall expression (by simp))
      · exact ih (fun e he => hall e (by simp [he])) compiled htail

private theorem structCompileProgExps_byteRanged {width : Nat} [BEq String]
    (context : StructPassContext) (hc : CtxBR context.structs) :
    ∀ expressions : List (Exp (BitVec width)),
      (∀ expression ∈ expressions, ExpByteRanged expression) →
        ∀ expression ∈ structCompileProg.structCompileExps context expressions,
          ExpByteRanged expression := by
  intro expressions
  induction expressions with
  | nil => simp [structCompileProg.structCompileExps]
  | cons expression rest ih =>
      intro hall compiled hmem
      simp only [structCompileProg.structCompileExps] at hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        exact structCompileExp_byteRanged context hc expression (hall expression (by simp))
      · exact ih (fun e he => hall e (by simp [he])) compiled htail

theorem structCompileProg_byteRanged {width : Nat} [BEq String]
    (context : StructPassContext) (hc : CtxBR context.structs) :
    ∀ program : Prog (BitVec width), ProgByteRanged program →
      ProgByteRanged (structCompileProg context program)
  | .skip, _ => by simp [ProgByteRanged, structCompileProg]
  | .dec name shape value body, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hn, hs, hv, hb⟩
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨hn, structCompileShape_byteRanged context.structs shape hc hs,
        structCompileExp_byteRanged context hc value hv,
        structCompileProg_byteRanged { context with locals := (name, shape) :: context.locals } hc body hb⟩
  | .assign kind name value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨h.1, structCompileExp_byteRanged context hc value h.2⟩
  | .primitive name operator arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨h.1, structCompileProgExps_byteRanged context hc arguments h.2⟩
  | .store address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileExp_byteRanged context hc address h.1,
        structCompileExp_byteRanged context hc value h.2⟩
  | .store32 address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileExp_byteRanged context hc address h.1,
        structCompileExp_byteRanged context hc value h.2⟩
  | .storeByte address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileExp_byteRanged context hc address h.1,
        structCompileExp_byteRanged context hc value h.2⟩
  | .seq first second, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileProg_byteRanged context hc first h.1,
        structCompileProg_byteRanged context hc second h.2⟩
  | .ite condition thenBranch elseBranch, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileExp_byteRanged context hc condition h.1,
        structCompileProg_byteRanged context hc thenBranch h.2.1,
        structCompileProg_byteRanged context hc elseBranch h.2.2⟩
  | .while condition body, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileExp_byteRanged context hc condition h.1,
        structCompileProg_byteRanged context hc body h.2⟩
  | .break, _ => by simp [ProgByteRanged, structCompileProg]
  | .continue, _ => by simp [ProgByteRanged, structCompileProg]
  | .call none function arguments, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hn, hargs, _⟩
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨hn, ⟨structCompileProgExps_byteRanged context hc arguments hargs, trivial⟩⟩
  | .call (some (kindOpt, none)) function arguments, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hn, hargs, hkind, _⟩
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨hn, structCompileProgExps_byteRanged context hc arguments hargs,
        hkind, trivial⟩
  | .call (some (kindOpt, some (exception, handlerVar, body))) function arguments, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hn, hargs, hkind, hexception, hhandlerVar, hbody⟩
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨hn, structCompileProgExps_byteRanged context hc arguments hargs,
        hkind, hexception, hhandlerVar,
        structCompileProg_byteRanged context hc body hbody⟩
  | .decCall name shape function arguments body, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hn, hs, hf, hargs, hbody⟩
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨hn, structCompileShape_byteRanged context.structs shape hc hs, hf,
        structCompileProgExps_byteRanged context hc arguments hargs,
        structCompileProg_byteRanged { context with locals := (name, shape) :: context.locals }
          hc body hbody⟩
  | .extCall function configuration configurationLength array arrayLength, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨h.1, structCompileExp_byteRanged context hc configuration h.2.1,
        structCompileExp_byteRanged context hc configurationLength h.2.2.1,
        structCompileExp_byteRanged context hc array h.2.2.2.1,
        structCompileExp_byteRanged context hc arrayLength h.2.2.2.2⟩
  | .raise exception value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨h.1, structCompileExp_byteRanged context hc value h.2⟩
  | .return value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact structCompileExp_byteRanged context hc value h
  | .shMemLoad size kind name address, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨h.1, structCompileExp_byteRanged context hc address h.2⟩
  | .shMemStore size address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProg, ProgByteRanged]
      exact ⟨structCompileExp_byteRanged context hc address h.1,
        structCompileExp_byteRanged context hc value h.2⟩
  | .tick, _ => by simp [ProgByteRanged, structCompileProg]
  | .annot tag text, h => by simpa [ProgByteRanged, structCompileProg] using h
termination_by program _ => sizeOf program
decreasing_by
  all_goals
    first
    | decreasing_trivial
    | (simp_wf; omega)
    | omega

private theorem structCompileParams_byteRanged [BEq String] (context : StructContext)
    (hc : CtxBR context) (parameters : List (String × Shape))
    (h : ListParamByteRanged parameters) :
    ListParamByteRanged (parameters.map fun (name, shape) =>
      (name, structCompileShape context shape)) := by
  intro parameter hmem
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hmem
  rcases h source hsource with ⟨hname, hshape⟩
  exact ⟨hname, structCompileShape_byteRanged context source.2 hc hshape⟩

private theorem structGetNamesStep_ctxBR {width : Nat} (context : StructPassContext)
    (declaration : Decl (BitVec width)) (hc : CtxBR context.structs)
    (hd : DeclByteRanged declaration) :
    CtxBR ((match declaration with
      | .name name fields =>
          { context with structs := (name, { fields := fields, size := 0 }) :: context.structs }
      | _ => context).structs) := by
  cases declaration with
  | name name fields =>
      simp only [DeclByteRanged] at hd
      intro pair hp
      simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · cases hp
        exact ⟨hd.1, hd.2⟩
      · exact hc pair hp
  | decl shape name value => exact hc
  | function declaration => exact hc
  | exnDecl exception shape => exact hc

private theorem structGetNames_ctxBR {width : Nat} (context : StructPassContext)
    (declarations : List (Decl (BitVec width))) (hc : CtxBR context.structs)
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    CtxBR (structGetNames context declarations).structs := by
  induction declarations generalizing context with
  | nil => simpa [structGetNames] using hc
  | cons declaration rest ih =>
      have hd := hdecls declaration (by simp)
      have hrest : ∀ item ∈ rest, DeclByteRanged item := by
        intro item hitem
        exact hdecls item (by simp [hitem])
      cases declaration with
      | name name fields =>
          have hnext := structGetNamesStep_ctxBR context (.name name fields) hc hd
          change CtxBR (structGetNames
            { context with structs := (name, { fields := fields, size := 0 }) :: context.structs }
            rest).structs
          exact ih _ hnext hrest
      | decl shape name value =>
          change CtxBR (structGetNames context rest).structs
          exact ih context hc hrest
      | function declaration =>
          change CtxBR (structGetNames context rest).structs
          exact ih context hc hrest
      | exnDecl exception shape =>
          change CtxBR (structGetNames context rest).structs
          exact ih context hc hrest

private theorem structCompileDecls_structs {width : Nat} [BEq String]
    (declarations : List (Decl (BitVec width))) :
    ∀ context : StructPassContext,
      (structCompileDecls declarations context).2.structs = context.structs := by
  induction declarations with
  | nil => intro context; rfl
  | cons declaration rest ih =>
      intro context
      cases declaration <;> simp [structCompileDecls, ih]

private theorem structCompileDecls_byteRanged {width : Nat} [BEq String]
    (declarations : List (Decl (BitVec width))) :
    ∀ context : StructPassContext, CtxBR context.structs →
      (∀ declaration ∈ declarations, DeclByteRanged declaration) →
      ∀ declaration ∈ (structCompileDecls declarations context).1,
        DeclByteRanged declaration := by
  induction declarations with
  | nil => simp [structCompileDecls]
  | cons declaration rest ih =>
      intro context hc hdecls result hresult
      have hd := hdecls declaration (by simp)
      have hrest : ∀ item ∈ rest, DeclByteRanged item := by
        intro item hitem
        exact hdecls item (by simp [hitem])
      cases declaration with
      | decl shape name value =>
          simp only [structCompileDecls] at hresult
          simp only [List.mem_cons] at hresult
          rcases hresult with heq | htail
          · cases heq
            simp only [DeclByteRanged] at hd ⊢
            rcases hd with ⟨hshape, hname, hvalue⟩
            exact ⟨structCompileShape_byteRanged context.structs shape hc hshape,
              hname, structCompileExp_byteRanged context hc value hvalue⟩
          · exact ih { context with globals := (name, shape) :: context.globals }
              hc hrest result htail
      | function declaration =>
          simp only [structCompileDecls] at hresult
          simp only [List.mem_cons] at hresult
          rcases hresult with heq | htail
          · cases heq
            simp only [DeclByteRanged, FunDeclByteRanged] at hd ⊢
            rcases hd with ⟨hname, hparams, hbody, hreturn⟩
            have hstructs := structCompileDecls_structs rest context
            have hctx : CtxBR (structCompileDecls rest context).2.structs := by
              simpa [hstructs] using hc
            have hbodyOut := structCompileProg_byteRanged
              { (structCompileDecls rest context).2 with locals := declaration.params }
              hctx declaration.body hbody
            refine ⟨hname, structCompileParams_byteRanged context.structs hc
              declaration.params hparams, ?_,
              structCompileShape_byteRanged context.structs declaration.returnShape hc hreturn⟩
            simpa [structCompileDecls, hstructs] using hbodyOut
          · exact ih context hc hrest result htail
      | exnDecl exception shape =>
          simp only [structCompileDecls] at hresult
          simp only [List.mem_cons] at hresult
          rcases hresult with heq | htail
          · cases heq
            simp only [DeclByteRanged] at hd ⊢
            rcases hd with ⟨hname, hshape⟩
            exact ⟨hname, structCompileShape_byteRanged context.structs shape hc hshape⟩
          · exact ih context hc hrest result htail
      | name name fields =>
          simp only [structCompileDecls] at hresult
          exact ih context hc hrest result hresult

theorem structCompileTop_byteRanged {width : Nat} [BEq String]
    (declarations : List (Decl (BitVec width)))
    (hdecls : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    ∀ declaration ∈ structCompileTop declarations, DeclByteRanged declaration := by
  let initial : StructPassContext := { structs := [], locals := [], globals := [] }
  have hcontext : CtxBR (structGetNames initial declarations).structs :=
    structGetNames_ctxBR initial declarations (by simp [initial, CtxBR]) hdecls
  intro declaration hmem
  letI : BEq String := instBEqOfDecidableEq
  simpa [structCompileTop, initial] using
    structCompileDecls_byteRanged declarations (structGetNames initial declarations)
      hcontext hdecls declaration hmem

end Flapjack
