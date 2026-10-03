import Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectNilName
import Flapjack.Pancake.Proofs.PanStructs.CompiledShapesWf
import Flapjack.Pancake.Proofs.PanStructs.CompileDeclsStructs
namespace Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectFunctionExn
open Flapjack Flapjack.Pancake.PanLang
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


/-- Flapjack infrastructure for the declaration state-update minors; no separate HOL declaration. -/
private theorem mappedUpdate {β γ : Type} (map : HolFiniteMapExact MlS β)
    (f : MlS × β → γ) (name : MlS) (value : β) :
    (map.update (name, value)).map2 f = (map.map2 f).update (name, f (name, value)) := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.map2, HolFiniteMapExact.update, FUPDATE]
  split
  · rename_i h
    have hk : name = key := by simpa using h
    subst key
    rfl
  · rfl
/-- Flapjack infrastructure for the declaration state-update minors; no separate HOL declaration. -/
private theorem convertedExn {width : Nat} {σ : Type} [NeZero width]
    (context : ContextExact) (source : PanSemStateFiniteExact width σ)
    (name : MlS) (shape : ShapeHOL) :
    convertStateExact context { source with eshapes := source.eshapes.update (name, shape) } =
      { convertStateExact context source with eshapes :=
        (convertStateExact context source).eshapes.update (name, compileShapeExact context.structs shape) } := by
  exact congrArg (fun eshapes => { convertStateExact context source with eshapes := eshapes })
    (mappedUpdate source.eshapes (fun entry => compileShapeExact context.structs entry.2) name shape)
/-- Flapjack infrastructure for the declaration state-update minors; no separate HOL declaration. -/
private theorem convertedFunction {width : Nat} {σ : Type} [NeZero width]
    (context : ContextExact) (source : PanSemStateFiniteExact width σ)
    (declaration : FunDeclHOL width) :
    convertStateExact context { source with code := source.code.update (declaration.name, (declaration.params, declaration.body, declaration.returnShape)) } =
      { convertStateExact context source with code :=
        (convertStateExact context source).code.update (declaration.name,
          (declaration.params.map (fun p => (p.1, compileShapeExact context.structs p.2)),
           compileProgExact { context with locals := declaration.params } declaration.body,
           compileShapeExact context.structs declaration.returnShape)) } := by
  exact congrArg (fun code => { convertStateExact context source with code := code })
    (mappedUpdate source.code (fun entry =>
      (entry.2.1.map (fun p => (p.1, compileShapeExact context.structs p.2)),
       compileProgExact { context with locals := entry.2.1 } entry.2.2.1,
       compileShapeExact context.structs entry.2.2.2)) declaration.name
      (declaration.params, declaration.body, declaration.returnShape))
/-- Original ExnDecl minor: exactly the source absent-exception and shape-WF guarded tail IH. The target absence and WF guard, plus conversion of the exception update, are derived internally.
All eight original hypotheses and full target/existential conclusions remain. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_decls_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileDeclsCorrectExn {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (name : MlS) (shape : ShapeHOL)
    (declarations : List (DeclHOL width))
    (ih : source.eshapes.lookup name = none ∧ isWfShapeExactHOL source.structs shape = true →
      CompileDeclsCorrectNilName.DeclsProperty
        { source with eshapes := source.eshapes.update (name, shape) } declarations) :
  ∀ (post : PanSemStateFiniteExact width σ) (context finalContext : ContextExact)
    (compiled : List (DeclHOL width)),
    (@PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) (.exnDecl name shape :: declarations) = some post ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      context.locals = [] ∧
      structInfosOkHOLExact source.structs ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      compileDeclsExact context (.exnDecl name shape :: declarations) = (compiled, finalContext)) →
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
  split at heval
  · rename_i hguard
    have hg : source.eshapes.lookup name = none ∧ isWfShapeExactHOL source.structs shape = true := by
      simpa only [Bool.and_eq_true, Option.isNone_iff_eq_none] using hguard
    simp only [compileDeclsExact] at hcompile
    cases hcompTail : compileDeclsExact context declarations with
    | mk tail final =>
      rw [hcompTail] at hcompile
      dsimp only at hcompile
      rcases Prod.mk.inj hcompile with ⟨rfl, rfl⟩
      have hs := compileDeclsStructs context declarations tail final hcompTail
      have htail := ih hg post context final tail
        ⟨heval, hstruct, hlocals, hinfo, hfields, hwf, hmap, hcompTail⟩
      rcases htail with ⟨htarget, globals, hfinal, hpostFields, hpostWf, hpostStruct, hpostLocals, hpostMap⟩
      have htargetGuard : (((convertStateExact final source).eshapes.lookup name).isNone &&
          isWfShapeExactHOL (convertStateExact final source).structs
            (compileShapeExact context.structs shape)) = true := by
        have hw := CompiledShapesWf.isWfShapeCompileShape ([] : List (MlS × StructInfoHOLExact))
        simp only [convertStateExact, convertEshapesExact, HolFiniteMapExact.map2, hg.1,
          Option.map_none, Option.isNone_none, Bool.true_and]
        exact hw.1 context.structs shape
      refine ⟨?_, globals, hfinal, hpostFields, hpostWf, hpostStruct, hpostLocals, hpostMap⟩
      simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite]
      change (if ((convertStateExact final source).eshapes.lookup name).isNone &&
          isWfShapeExactHOL (convertStateExact final source).structs
            (compileShapeExact context.structs shape) then
        @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
          { convertStateExact final source with eshapes :=
            (convertStateExact final source).eshapes.update (name, compileShapeExact context.structs shape) }
          (fun address => Classical.propDecidable (source.memaddrs address)) tail
        else none) = some (convertStateExact final post)
      rw [htargetGuard]
      simp only [ite_true]
      have hc := convertedExn final source name shape
      rw [hs] at hc
      have ht := congrArg (fun state => @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) tail) hc
      exact ht.symm.trans htarget
  · cases heval
/-- Original Function minor: exactly the source parameter-EVERY and return-shape WF guarded tail IH. The target parameter/return WF guards and code-update conversion are derived internally, retaining the final globals and original parameter scope for body compilation.
All eight original hypotheses and full target/existential conclusions remain. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_decls_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileDeclsCorrectFunction {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (declaration : FunDeclHOL width)
    (declarations : List (DeclHOL width))
    (ih : (∀ parameter ∈ declaration.params,
        isWfShapeExactHOL source.structs parameter.2 = true) ∧
        isWfShapeExactHOL source.structs declaration.returnShape = true →
      CompileDeclsCorrectNilName.DeclsProperty
        { source with code := source.code.update (declaration.name, (declaration.params, declaration.body, declaration.returnShape)) } declarations) :
  ∀ (post : PanSemStateFiniteExact width σ) (context finalContext : ContextExact)
    (compiled : List (DeclHOL width)),
    (@PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) (.function declaration :: declarations) = some post ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      context.locals = [] ∧
      structInfosOkHOLExact source.structs ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      compileDeclsExact context (.function declaration :: declarations) = (compiled, finalContext)) →
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
  split at heval
  · rename_i hguard
    have hg : (∀ parameter ∈ declaration.params,
        isWfShapeExactHOL source.structs parameter.2 = true) ∧
        isWfShapeExactHOL source.structs declaration.returnShape = true := by
      simpa only [Bool.and_eq_true, List.all_eq_true] using hguard
    simp only [compileDeclsExact] at hcompile
    cases hcompTail : compileDeclsExact context declarations with
    | mk tail final =>
      rw [hcompTail] at hcompile
      dsimp only at hcompile
      rcases Prod.mk.inj hcompile with ⟨rfl, rfl⟩
      have hs := compileDeclsStructs context declarations tail final hcompTail
      have htail := ih hg post context final tail
        ⟨heval, hstruct, hlocals, hinfo, hfields, hwf, hmap, hcompTail⟩
      rcases htail with ⟨htarget, globals, hfinal, hpostFields, hpostWf, hpostStruct, hpostLocals, hpostMap⟩
      have htargetGuard : ((declaration.params.map
          (fun p => (p.1, compileShapeExact context.structs p.2))).all
            (fun p => isWfShapeExactHOL (convertStateExact final source).structs p.2) &&
          isWfShapeExactHOL (convertStateExact final source).structs
            (compileShapeExact context.structs declaration.returnShape)) = true := by
        have hw := CompiledShapesWf.isWfShapeCompileShape ([] : List (MlS × StructInfoHOLExact))
        rw [Bool.and_eq_true]
        constructor
        · apply List.all_eq_true.mpr
          intro parameter hmem
          rcases List.mem_map.mp hmem with ⟨original, _, rfl⟩
          exact hw.1 context.structs original.2
        · exact hw.1 context.structs declaration.returnShape
      refine ⟨?_, globals, hfinal, hpostFields, hpostWf, hpostStruct, hpostLocals, hpostMap⟩
      simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite]
      change (if ((declaration.params.map
          (fun p => (p.1, compileShapeExact context.structs p.2))).all
            (fun p => isWfShapeExactHOL (convertStateExact final source).structs p.2) &&
          isWfShapeExactHOL (convertStateExact final source).structs
            (compileShapeExact context.structs declaration.returnShape)) then
        @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
          { convertStateExact final source with code :=
            (convertStateExact final source).code.update (declaration.name,
              (declaration.params.map (fun p => (p.1, compileShapeExact context.structs p.2)),
               compileProgExact { final with locals := declaration.params } declaration.body,
               compileShapeExact context.structs declaration.returnShape)) }
          (fun address => Classical.propDecidable (source.memaddrs address)) tail
        else none) = some (convertStateExact final post)
      rw [htargetGuard]
      simp only [ite_true]
      have hc := convertedFunction final source declaration
      rw [← hs]
      have ht := congrArg (fun state => @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ state
          (fun address => Classical.propDecidable (state.memaddrs address)) tail) hc
      exact ht.symm.trans htarget
  · cases heval
end Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectFunctionExn
