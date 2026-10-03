import Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectDecl
import Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectFunctionExn
namespace Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectExact
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


/-- Full original declaration correctness theorem, assembled over every
source constructor. All eight original hypotheses and the actual target run
plus full existential state/context result remain; there is no public IH or
extra target/post-state premise. Generalized list induction supplies exactly
the guarded source-state recursive hypotheses to the reviewed minors. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_decls_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileDeclsCorrectExact {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (declarations : List (DeclHOL width)) :
  ∀ (post : PanSemStateFiniteExact width σ) (context finalContext : ContextExact)
    (compiled : List (DeclHOL width)),
    (@PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) declarations = some post ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      context.locals = [] ∧
      structInfosOkHOLExact source.structs ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) source.globals ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      compileDeclsExact context declarations = (compiled, finalContext)) →
    @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ (convertStateExact finalContext source)
      (fun address => Classical.propDecidable ((convertStateExact finalContext source).memaddrs address))
      compiled = some (convertStateExact finalContext post) ∧
    (∃ globals, finalContext = { context with globals := globals } ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) post.globals ∧
      feveryHOL (fun entry => isWfShapeValueHOLExact source.structs entry.2) post.globals ∧
      post.structs = source.structs ∧ post.locals = source.locals ∧
      shapeMap globals = post.globals.map2 (fun entry => shapeOfHOLExact entry.2)) := by
  have all : ∀ (declarations : List (DeclHOL width)) (source : PanSemStateFiniteExact width σ),
      CompileDeclsCorrectNilName.DeclsProperty source declarations := by
    intro declarations
    induction declarations with
    | nil => exact CompileDeclsCorrectNilName.compileDeclsCorrectNil
    | cons declaration declarations ih =>
      intro source
      cases declaration with
      | name name fields =>
        exact CompileDeclsCorrectNilName.compileDeclsCorrectName
          source name fields declarations (ih source)
      | decl shape name expression =>
        apply CompileDeclsCorrectDecl.compileDeclsCorrectDecl source shape name expression declarations
        intro value _
        exact ih (PanSemStateFiniteExact.setGlobalHOLFinite name value source)
      | function declaration =>
        apply CompileDeclsCorrectFunctionExn.compileDeclsCorrectFunction source declaration declarations
        intro _
        exact ih _
      | exnDecl name shape =>
        apply CompileDeclsCorrectFunctionExn.compileDeclsCorrectExn source name shape declarations
        intro _
        exact ih _
  exact all declarations source
end Flapjack.Pancake.Proofs.PanStructs.CompileDeclsCorrectExact
