import Flapjack.HolRef
import Flapjack.Pancake.CrepInline.Pass
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanLang.Decl

/-!
HOL-shaped top-level Pancake-to-Crep compiler boundary. The compilation
produces HOL's function-triple shape and passes it through Flapjack's
source-shaped inline traversal; the exact `compile_inl_top` carrier port is
tracked by `flapjack-e7w.1`. Its executed selection filter calls the reviewed
`inlinableHOL` through the total `inlinableThroughHOL` declaration adapter.
Metadata is attached only in a downstream adapter for Flapjack's existing
pipeline representation.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of Cake's
    `pan_to_crep$compile_prog`
    (`cakeml/pancake/pan_to_crepScript.sml:393-397`). It compiles declarations
    to a triple list, selects inline names using `functions (FILTER inlinable
    declarations)` with the filter evaluated by exact `inlinableHOL` on the
    exact one-bit projection adapter, and applies the source-shaped triple-list `compileInlTopHOL`
    pass; the `let` structure and operand order match HOL clause-for-clause.
    The tag is WITHDRAWN as a documented carrier mismatch; see the note below. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port), source-reviewed mismatch. HOL
-- `compile_prog` (`pan_to_crepScript.sml:393-397`) is
-- `compile_inl_top (MAP FST (functions (FILTER inlinable prog)))
--    (compile_to_crep prog)` over a word-indexed `'a prog`; its result is
-- `(mlstring # num list # 'a crepLang$prog) list`, with no additional
-- hypotheses or side conditions. This definition differs on carriers, not
-- just names: (1) declarations and inline names use
-- `FunName` = `String` vs HOL `funname` = `mlstring`; (2) the source is a
-- production `Decl (BitVec width)` with production `Shape` vs HOL's
-- word-indexed `decl` carrying `mlstring`/`shape`; (3) the target is
-- production `CrepProg (BitVec width)` (whose `Call`/`ExtCall` funnames are
-- `String`) via untagged `compileToCrepHOL` vs HOL `'a crepLang$prog` via
-- `compile_to_crep`; (4) `compileInlTopHOL` is the source-shaped pass over
-- generic `CrepProg α` vs HOL `compile_inl_top`. The `[BEq FunName]
-- [LawfulBEq FunName] [LawfulHashable FunName] [OfNat (BitVec width) 0/1]`
-- arguments are executable artifacts HOL does not have. `names_as_string`
-- cannot authorize the `Decl`/`Shape`/`CrepProg` carriers and no `NameRanged`
-- witness exists (the output is a triple list, not a name). Direct HOL-EVAL
-- rows `empty`, `duplicate_first`, `nested_inline` in
-- `scripts/hol-probes/compile_prog_probe.out` are reproduced by
-- `Flapjack/Test/CompileProgParity.lean`; the `params_two_words` row is
-- reproduced by `Flapjack/Test/CompileProgParamsParity.lean`. Faithful-port
-- dependency `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`; exact
-- `compile` by `.18.3.5.8.13`, exact `compile_inl_top` carrier by
-- `flapjack-e7w.1`; the full exact `compile_inl_top` and production inliner
-- are tracked by open epic `flapjack-e7w.2`). In `compileFlapjackEntryCake`
-- (Pipeline.lean), the
-- parser-proved branch invokes `compileProgTopHOLWithMetadataOfExact`, which
-- crosses the `DeclHOL` input boundary and then calls this source-shaped
-- implementation; it does not make the emitted Crep bodies exact
-- `CrepProgHOL` values. This is a carrier gap, not a measured performance
-- exception. Keep the `compile_prog_def` inventory bead open until the exact
-- `compile_to_crep` and `compile_inl_top` dependencies are routed through the
-- executed path.
def compileProgTopHOL [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width))) :
    List (FunName × List Nat × CrepProg (BitVec width)) :=
  let inlineNames :=
    (functionEntries (declarations.filter inlinableThroughHOL)).map
      fun (name, _, _, _) => name
  compileInlTopHOL inlineNames (compileToCrepHOL declarations)

/-! Metadata adapter following the exact `compile_prog` triple boundary.
The Cake passes following `compile_prog` consume triples; the production
Flapjack pipeline keeps the source return shape in `CompiledFunction`. -/
def compileProgTopHOLWithMetadata [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width))) :
    List (CompiledFunction (BitVec width)) :=
  (compileToCrepHOLWithMetadata declarations).zipWith
    (fun original (_, _, body) => { original with body })
    (compileProgTopHOL declarations)

/-! Exact-carrier interface for the `compile_prog` boundary (bead
    flapjack-pxn.18.3.5.8.6). It consumes the MLString-keyed declaration
carrier `DeclHOL` and converts byte-ranged names at the boundary via
`declOfHOL`, so the exact HOL carriers are the interface type of the
declaration-level compiler boundary. The parser-backed source entrypoints pass
their proved byte-range invariant into `compileProgTopHOLWithMetadataOfExact`,
which routes the compiler body through this interface. Its result still uses
Flapjack's source-shaped Crep carrier; the explicit carrier mismatch and
unported HOL `compile`/`compile_inl_top` dependencies remain documented above. -/
def compileProgTopHOLOfExact {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (DeclHOL width)) :
    List (FunName × List Nat × CrepProg (BitVec width)) :=
  compileProgTopHOL (declarations.map declOfHOL)

/-- Metadata adapter whose compiler input crosses the exact `DeclHOL` carrier
    boundary.  Its side condition is the byte-range premise used by the
    production-to-HOL declaration codec; it is preserved by the executed
    entry transforms before this adapter is called. -/
def compileProgTopHOLWithMetadataOfExact {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width)))
    (_h : ∀ d ∈ declarations, DeclByteRanged d) :
    List (CompiledFunction (BitVec width)) :=
  (compileToCrepHOLWithMetadata declarations).zipWith
    (fun original (_, _, body) => { original with body })
    (compileProgTopHOLOfExact (declarations.map declToHOL))

/-- Byte-ranged production declarations round-trip through the exact carrier. -/
theorem map_declOfHOL_declToHOL {width : Nat} [NeZero width]
    (declarations : List (Flapjack.Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    (declarations.map declToHOL).map declOfHOL = declarations := by
  induction declarations with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons]
      rw [declOfHOL_declToHOL d (h d (by simp)),
        ih (fun e he => h e (by simp [he]))]

/-- The exact-carrier `compile_prog` boundary agrees with the production
    compiler on every byte-ranged declaration list. -/
theorem compileProgTopHOLOfExact_declToHOL {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Flapjack.Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    compileProgTopHOLOfExact (declarations.map declToHOL) =
      compileProgTopHOL declarations := by
  unfold compileProgTopHOLOfExact
  rw [map_declOfHOL_declToHOL declarations h]

/-- The exact-carrier metadata adapter preserves the current pipeline result
    for every declaration list satisfying the codec's byte-range premise. -/
theorem compileProgTopHOLWithMetadataOfExact_eq {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName]
    [LawfulHashable FunName] [OfNat (BitVec width) 0]
    [OfNat (BitVec width) 1]
    (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    compileProgTopHOLWithMetadataOfExact declarations h =
      compileProgTopHOLWithMetadata declarations := by
  unfold compileProgTopHOLWithMetadataOfExact compileProgTopHOLWithMetadata
  rw [compileProgTopHOLOfExact_declToHOL declarations h]

end Flapjack
