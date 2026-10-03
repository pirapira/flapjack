import Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectNilName
import Flapjack.Pancake.Proofs.PanStructs.CompileExpCorrectExact
import Flapjack.Pancake.Proofs.PanStructs.ValueShapeConversion
import Flapjack.Pancake.Proofs.PanStructs.CompileDeclsStructs
namespace Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectDecl
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact
/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness


/-- Flapjack infrastructure for the Decl minor; no independent HOL declaration. -/
private theorem converterGlobalsCode {width : Nat} {σ : Type} [NeZero width]
    (context : ContextExact) (source : PanSemStateFiniteExact width σ)
    (globals : List (MlS × ShapeHOL)) :
    convertStateExact { context with globals := globals } source =
      { convertStateExact context source with
        code := convertCodeExact { context with globals := globals } source.code } := rfl
/-- Flapjack infrastructure for the Decl minor; no independent HOL declaration. -/
private theorem evalConverterGlobals {width : Nat} {σ : Type} [NeZero width]
    (context : ContextExact) (source : PanSemStateFiniteExact width σ)
    (globals : List (MlS × ShapeHOL)) (expression : ExpHOL width) :
    @PanSemStateFiniteExact.evalHOLFinite width σ _
        (convertStateExact { context with globals := globals } source)
        (fun address => Classical.propDecidable (source.memaddrs address)) expression =
      @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
        (fun address => Classical.propDecidable (source.memaddrs address)) expression := by
  change @PanSemStateFiniteExact.evalHOLFinite width σ _
    { convertStateExact context source with
      code := convertCodeExact { context with globals := globals } source.code }
    (fun address => Classical.propDecidable (source.memaddrs address)) expression = _
  exact @PanPropsEvalStateFiniteExact.evalHOL_upd_code_eq width σ _
    (convertStateExact context source)
    (fun address => Classical.propDecidable (source.memaddrs address)) expression
    (convertCodeExact { context with globals := globals } source.code)
/-- Flapjack infrastructure for the Decl minor; no independent HOL declaration. -/
private theorem mapExt {α β : Type} (a b : HolFiniteMapExact α β)
    (h : ∀ key, a.lookup key = b.lookup key) : a = b :=
  HolFiniteMapExact.ext (funext h)
/-- Flapjack infrastructure for the Decl minor; no independent HOL declaration. -/
private theorem everyUpdate {β : Type} (P : MlS × β → Bool)
    (map : HolFiniteMapExact MlS β) (name : MlS) (value : β)
    (h : feveryHOL P map) (hv : P (name, value) = true) :
    feveryHOL P (map.update (name, value)) := by
  intro key bound hlookup
  simp only [HolFiniteMapExact.update, FUPDATE] at hlookup
  split at hlookup
  · rename_i heq
    have hk : name = key := by simpa using heq
    subst key
    cases hlookup
    exact hv
  · exact h key bound hlookup
/-- Flapjack infrastructure for the Decl minor; no independent HOL declaration. -/
private theorem shapeUpdate {width : Nat} [NeZero width] (map : HolFiniteMapExact MlS (ValueHOL width))
    (name : MlS) (value : ValueHOL width) :
    (map.update (name, value)).map2 (fun entry => shapeOfHOLExact entry.2) =
      (map.map2 (fun entry => shapeOfHOLExact entry.2)).update (name, shapeOfHOLExact value) := by
  apply mapExt
  intro key
  simp only [HolFiniteMapExact.map2, HolFiniteMapExact.update, FUPDATE]
  split <;> rfl
/-- Flapjack infrastructure for the Decl minor; no independent HOL declaration. -/
private theorem initEmptyFields {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) :
    feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2)
      source.emptyLocalsHOLFinite.locals := by
  intro key bound h
  cases h
/-- Flapjack infrastructure for the Decl minor; no independent HOL declaration. -/
private theorem initializerFacts {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (expression : ExpHOL width) (value : ValueHOL width)
    (heval : @PanSemStateFiniteExact.evalHOLFinite width σ _ source.emptyLocalsHOLFinite
      (fun address => Classical.propDecidable (source.memaddrs address)) expression = some value)
    (hstruct : context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)))
    (hlocals : context.locals = []) (hinfo : structInfosOkHOLExact source.structs)
    (hfields : feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals)
    (hglobalMap : shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2))
    (hwf : feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals) :
    valueFldsOkHOLExact source.structs value = true ∧
    isWfShapeValueHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source.emptyLocalsHOLFinite)
      (fun address => Classical.propDecidable (source.memaddrs address))
      (compileExpExact context expression) = some (convertV value) := by
  have hlocalMap : shapeMap context.locals =
      source.emptyLocalsHOLFinite.locals.map2 (fun entry => shapeOfHOLExact entry.2) := by
    rw [hlocals]
    apply mapExt
    intro key
    rfl
  have hexpr := CompileExpCorrectExact.compileExpCorrectExact source.emptyLocalsHOLFinite
    context expression value ⟨heval, hlocalMap, hglobalMap, hstruct, initEmptyFields source, hfields, hinfo⟩
  have hvalueWf : isWfShapeValueHOLExact source.structs value = true := by
    exact @evalHOLExact_isWfShapeValueHOLExact width σ _ source.emptyLocalsHOLFinite.toExact
      (fun address => Classical.propDecidable (source.memaddrs address))
      (by intro key bound h; cases h) hwf expression value heval
  exact ⟨hexpr.2.1, hvalueWf, hexpr.2.2⟩
/-- Flapjack infrastructure for the Decl minor; no independent HOL declaration. -/
private theorem convertedEmpty {width : Nat} {σ : Type} [NeZero width]
    (context : ContextExact) (source : PanSemStateFiniteExact width σ) :
    convertStateExact context source.emptyLocalsHOLFinite =
      (convertStateExact context source).emptyLocalsHOLFinite := rfl
/-- Flapjack infrastructure for the Decl minor; no independent HOL declaration. -/
private theorem convertedGlobal {width : Nat} {σ : Type} [NeZero width]
    (context : ContextExact) (source : PanSemStateFiniteExact width σ)
    (name : MlS) (value : ValueHOL width) :
    convertStateExact context (PanSemStateFiniteExact.setGlobalHOLFinite name value source) =
      PanSemStateFiniteExact.setGlobalHOLFinite name (convertV value) (convertStateExact context source) := by
  have hmap : (source.globals.update (name, value)).map2 (fun entry => convertV entry.2) =
      (source.globals.map2 (fun entry => convertV entry.2)).update (name, convertV value) := by
    apply mapExt
    intro key
    simp only [HolFiniteMapExact.map2, HolFiniteMapExact.update, FUPDATE]
    split <;> rfl
  exact congrArg (fun globals => { convertStateExact context source with globals := globals }) hmap
/-- Original Decl initializer minor with precisely the successful empty-locals
initializer and declared-shape guarded tail IH. All eight original hypotheses
and the full target run/existential context and state conclusions are retained.
Initializer transport across final globals changes only code, using the original
code-invariance theorem; no target execution or post-map premise is added. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_decls_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileDeclsCorrectDecl {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (shape : ShapeHOL) (name : MlS)
    (expression : ExpHOL width) (declarations : List (DeclHOL width))
    (ih : ∀ value : ValueHOL width,
      @PanSemStateFiniteExact.evalHOLFinite width σ _ source.emptyLocalsHOLFinite
        (fun address => Classical.propDecidable (source.memaddrs address)) expression = some value ∧
        shape = shapeOfHOLExact value →
      CompileDeclsCorrectNilName.DeclsProperty
        (PanSemStateFiniteExact.setGlobalHOLFinite name value source) declarations) :
  ∀ (post : PanSemStateFiniteExact width σ) (context finalContext : ContextExact)
    (compiled : List (DeclHOL width)),
    (@PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) (.decl shape name expression :: declarations) = some post ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      context.locals = [] ∧
      structInfosOkHOLExact source.structs ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      compileDeclsExact context (.decl shape name expression :: declarations) = (compiled, finalContext)) →
    @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ (convertStateExact finalContext source)
      (fun address => Classical.propDecidable ((convertStateExact finalContext source).memaddrs address))
      compiled = some (convertStateExact finalContext post) ∧
    (∃ globals, finalContext = { context with globals := globals } ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) post.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) post.globals ∧
      post.structs = source.structs ∧ post.locals = source.locals ∧
      shapeMap globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2)) := by
  intro post context finalContext compiled h
  rcases h with ⟨heval, hstruct, hlocals, hinfo, hfields, hwf, hmap, hcompile⟩
  simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at heval
  cases hinit : @PanSemStateFiniteExact.evalHOLFinite width σ _ source.emptyLocalsHOLFinite
      (fun address => Classical.propDecidable (source.memaddrs address)) expression with
  | none => simp only [hinit] at heval; cases heval
  | some value =>
    simp only [hinit] at heval
    split at heval
    · rename_i hshapeBool
      have hshape : shape = shapeOfHOLExact value := (shapeEqHOL_eq_true _ _).mp hshapeBool
      have hf := initializerFacts source context expression value hinit hstruct hlocals hinfo hfields hmap hwf
      have hnewFields := everyUpdate
        (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals name value hfields hf.1
      have hnewWf := everyUpdate
        (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals name value hwf hf.2.1
      have hnewMap : shapeMap ((name, shape) :: context.globals) =
          (source.globals.update (name, value)).map2 (fun entry => shapeOfHOLExact entry.2) := by
        rw [shapeUpdate]
        change (shapeMap context.globals).update (name, shape) = _
        rw [hmap, hshape]
      simp only [compileDeclsExact] at hcompile
      cases hcompTail : compileDeclsExact
          { context with globals := (name, shape) :: context.globals } declarations with
      | mk tail final =>
        rw [hcompTail] at hcompile
        dsimp only at hcompile
        rcases Prod.mk.inj hcompile with ⟨rfl, rfl⟩
        have htail := ih value ⟨hinit, hshape⟩ post
          { context with globals := (name, shape) :: context.globals } final tail
          ⟨heval, hstruct, hlocals, hinfo, hnewFields, hnewWf, hnewMap, hcompTail⟩
        rcases htail with ⟨htargetTail, globals, hfinal, hpostFields, hpostWf, hpostStruct, hpostLocals, hpostMap⟩
        have hfinalOrig : final = { context with globals := globals } := hfinal
        have htargetInit : @PanSemStateFiniteExact.evalHOLFinite width σ _
            (convertStateExact final source.emptyLocalsHOLFinite)
            (fun address => Classical.propDecidable (source.memaddrs address))
            (compileExpExact context expression) = some (convertV value) := by
          subst final
          exact (evalConverterGlobals context source.emptyLocalsHOLFinite globals
            (compileExpExact context expression)).trans hf.2.2
        have hvalueShape : shapeOfHOLExact (convertV value) = compileShapeExact context.structs shape := by
          have hs := ValueShapeConversion.shapeOfConvertVRev source.structs value ⟨hf.1, hf.2.1, hinfo⟩
          simpa only [← hstruct, ← hshape] using hs
        have htargetGuard : shapeEqHOL (compileShapeExact context.structs shape)
            (shapeOfHOLExact (convertV value)) = true :=
          (shapeEqHOL_eq_true _ _).mpr hvalueShape.symm
        refine ⟨?_, globals, hfinalOrig, hpostFields, hpostWf, hpostStruct, hpostLocals, hpostMap⟩
        simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite]
        change @PanSemStateFiniteExact.evalHOLFinite width σ _
          (convertStateExact final source).emptyLocalsHOLFinite
          (fun address => Classical.propDecidable (source.memaddrs address))
          (compileExpExact context expression) = some (convertV value) at htargetInit
        change (match @PanSemStateFiniteExact.evalHOLFinite width σ _
          (convertStateExact final source).emptyLocalsHOLFinite
          (fun address => Classical.propDecidable (source.memaddrs address))
          (compileExpExact context expression) with
          | some targetValue =>
            if shapeEqHOL (compileShapeExact context.structs shape) (shapeOfHOLExact targetValue) then
              @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
                (PanSemStateFiniteExact.setGlobalHOLFinite name targetValue (convertStateExact final source))
                (fun address => Classical.propDecidable (source.memaddrs address)) tail
            else none
          | none => none) = some (convertStateExact final post)
        rw [htargetInit]
        simp only [htargetGuard, ite_true]
        have htransport := congrArg (fun state =>
          @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ state
            (fun address => Classical.propDecidable (state.memaddrs address)) tail)
          (convertedGlobal final source name value)
        exact htransport.symm.trans htargetTail
    · cases heval
end Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectDecl
