import Flapjack.Compiler.Backend.Semantics.WordSem.State
import Flapjack.Pancake.Proofs.PanToWord
import Flapjack.Pancake.Proofs.PanSimp.StateRelImpSemantics
import Flapjack.Pancake.Proofs.PanStructs.CompileTopSemanticsDeclsExact
set_option autoImplicit false
namespace Flapjack.Pancake.Proofs.PanToWord.InitialComposition
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack assembly infrastructure for the first two passes in the original
`pan_to_wordProofScript.sml:529-595` proof. This has no independent HOL
declaration: it derives the two equalities from the original initial-state
assumptions and the reviewed pass theorems. -/
private theorem initialPassSemantics {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateFiniteExact width σ) (code : List (DeclHOL width)) (start : MlS)
    (hfail : PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail)
    (hdist : ((functionsHOL code).map Prod.fst).Nodup)
    (hcode : source.code = HolFiniteMapExact.empty)
    (hlocals : source.locals = HolFiniteMapExact.empty)
    (hglobals : source.globals = HolFiniteMapExact.empty)
    (heshapes : source.eshapes = HolFiniteMapExact.empty) :
    (PanSemStateFiniteExact.semanticsDecls source start code =
      PanSemStateFiniteExact.semanticsDecls source start (panSimpDeclsHOL code)) ∧
    (PanSemStateFiniteExact.semanticsDecls source start code =
      PanSemStateFiniteExact.semanticsDecls source start
        (Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code))) := by
  classical
  have hrel : PanSimp.stateRel source source source.code := by
    refine ⟨?_, (fun _ h => h), ?_⟩
    · cases source; rfl
    · intro f vs p sh he
      simp [hcode, HolFiniteMapExact.empty] at he
  have hsimp := PanSimp.stateRelImpSemanticsDeclsHOL source source code start
    ⟨hrel, hdist, hcode, hcode, hfail⟩
  have hsimpfail : PanSemStateFiniteExact.semanticsDecls source start (panSimpDeclsHOL code) ≠ .fail := by
    rw [← hsimp]
    exact hfail
  have hstruct := Pancake.Proofs.PanStructs.CompileTopSemanticsDeclsExact.compileTopSemanticsDeclsExact
    source start (panSimpDeclsHOL code) ⟨hsimpfail, hlocals, hcode, hglobals⟩
  have hmapempty : ∀ {α β γ : Type} (f : α × β → γ),
      HolFiniteMapExact.map2 f (HolFiniteMapExact.empty : HolFiniteMapExact α β) = HolFiniteMapExact.empty := by
    intro α β γ f
    apply HolFiniteMapExact.ext
    rfl
  have hboot : { source with eshapes := source.eshapes.map2 (fun entry =>
      Pancake.PanStructs.CompileShapeExact.compileShapeExact
        (Pancake.PanStructs.CompileShapeExact.getNamesExact
          { structs := [], locals := [], globals := [] } (panSimpDeclsHOL code)).structs entry.2) } = source := by
    have hm : source.eshapes.map2 (fun entry =>
      Pancake.PanStructs.CompileShapeExact.compileShapeExact
        (Pancake.PanStructs.CompileShapeExact.getNamesExact
          { structs := [], locals := [], globals := [] } (panSimpDeclsHOL code)).structs entry.2) = source.eshapes := by
      rw [heshapes, hmapempty]
    rw [hm]
  rw [hboot] at hstruct
  exact ⟨hsimp, hsimp.trans hstruct⟩

/-- Flapjack assembly infrastructure for the initial three passes of the original
PanToWord proof (source lines 529-595), with the literal globals-state update.
The size, allocation guards, and memory agreement come from the original
source assumptions. There is no independent HOL declaration to tag; the full
24-hypothesis `state_rel_imp_semantics` remains separate pending work. -/
theorem initialToGlobalsSemantics {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (code : List (DeclHOL width)) (start : MlS) (globalsSize : Nat)
    (hfail : PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail)
    (hdist : ((functionsHOL code).map Prod.fst).Nodup)
    (hcode : source.code = HolFiniteMapExact.empty)
    (hlocals : source.locals = HolFiniteMapExact.empty)
    (hglobals : source.globals = HolFiniteMapExact.empty)
    (heshapes : source.eshapes = HolFiniteMapExact.empty)
    (hsize : globalsSize = ((decShapesHOL code).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] code)))).sum)
    (halloc : globalsAllocatableHOL source code)
    (halign : panGlobalsByteAlignedHOL source.topAddr) (hdim : goodDimindex width)
    (hmem : ∀ address, source.memaddrs address →
      target.memory address = wlabWlocExact (source.memory address)) :
    PanSemStateFiniteExact.semanticsDecls source start code =
      PanSemStateFiniteExact.semanticsDecls
        { source with
          topAddr := source.topAddr + panBytesInWord width * BitVec.ofNat width globalsSize
          memaddrs := fun address => source.memaddrs address ∨
            Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address
          memory := wlocWlabHOL ∘ target.memory
          locals := source.locals }
        start (compileTopExactHOL
          (Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code)) start) := by
  classical
  obtain ⟨hsimp, hstruct⟩ := initialPassSemantics source code start hfail hdist hcode hlocals hglobals heshapes
  have hsimpnf : PanSemStateFiniteExact.semanticsDecls source start (panSimpDeclsHOL code) ≠ .fail := by
    rw [← hsimp]; exact hfail
  have hstructnf : PanSemStateFiniteExact.semanticsDecls source start
      (Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code)) ≠ .fail := by
    rw [← hstruct]; exact hfail
  let structCode := Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code)
  have hdiststruct : ((functionsHOL structCode).map Prod.fst).Nodup := by
    dsimp only [structCode]
    rw [functionNamesStructsCompileTopHOL, functionNamesCompileProgHOL]
    exact hdist
  have hsizelist := semanticsSizeDecsStcnamesCompileStructsHOL source start (panSimpDeclsHOL code)
    ⟨hsimpnf, hglobals⟩
  have hsizecompiled : ((decShapesHOL structCode).map sizeOfShapeHOL).sum = globalsSize := by
    dsimp only [structCode]
    rw [hsizelist, decShapesCompileProgHOL, decsStcnamesHOLExact_panSimpDeclsHOL_eq]
    exact hsize.symm
  have halloc' := halloc
  dsimp only [globalsAllocatableHOL] at halloc'
  rw [← hsize] at halloc'
  obtain ⟨_, hdisjoint, htopnot, hbound⟩ := halloc'
  have hmemory : ∀ address, source.memaddrs address →
      source.memory address = (wlocWlabHOL ∘ target.memory) address := by
    intro address ha
    simp only [Function.comp_apply, hmem address ha, wlocWlabWlabWlocHOL]
  let globalState : PanSemStateFiniteExact width σ :=
    { source with
      topAddr := source.topAddr + panBytesInWord width * BitVec.ofNat width globalsSize
      memaddrs := fun address => source.memaddrs address ∨
        Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address
      memory := wlocWlabHOL ∘ target.memory
      locals := source.locals }
  have hglobal := PanGlobalsCompileTopSemanticsDecls.compileTopSemanticsDeclsHOL
    source globalState structCode start (panBytesInWord width * BitVec.ofNat width globalsSize)
    (Compiler.Backend.StackRemove.addresses source.topAddr globalsSize)
    (wlocWlabHOL ∘ target.memory) source.locals
    ⟨hdiststruct, rfl, hcode, hglobals, halign, hdim,
      (by rw [hsizecompiled]), (by rw [hsizecompiled]),
      (fun address hs hf => hdisjoint address ⟨hs, hf⟩), hmemory,
      htopnot, (by simpa [hsizecompiled, panBytesInWord,
        Compiler.Backend.StackRemove.bytesInWord, Nat.mul_comm] using hbound),
      Pancake.PanStructs.CompileShapeExact.compileTopNoNames _, hstructnf⟩
  exact hstruct.trans hglobal

end Flapjack.Pancake.Proofs.PanToWord.InitialComposition
