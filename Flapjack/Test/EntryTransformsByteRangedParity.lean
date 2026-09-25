import Flapjack.Pancake.EntryTransformsByteRanged

/-!
Parity fixture for the first two executed entry transforms preserving
`DeclByteRanged` (bead `flapjack-pxn.18.3.5.8.7.1.3`).

These are Flapjack-only preservation theorems (no HOL-tagged declaration), so
the fixture only witnesses the kernel-checked statements at the production
declaration/program types. -/

namespace Flapjack.Test.EntryTransformsByteRangedParity

open Flapjack
open Flapjack.Pancake.PanLang

example {width : Nat} (program : Prog (BitVec width))
    (h : ProgByteRanged program) :
    ProgByteRanged (panSimpProg program) :=
  panSimpProg_byteRanged program h

example {width : Nat} (declaration : Decl (BitVec width))
    (h : DeclByteRanged declaration) :
    DeclByteRanged (panSimpDecl declaration) :=
  panSimpDecl_byteRanged declaration h

example {width : Nat} (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ d ∈ panSimpDecls declarations, DeclByteRanged d :=
  panSimpDecls_byteRanged declarations h

example {width : Nat} [BEq String] (start : FunName)
    (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ d ∈ panTargetMoveStartToFront start declarations, DeclByteRanged d :=
  panTargetMoveStartToFront_byteRanged start declarations h

example {width : Nat} [BEq String] (start : FunName)
    (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ d ∈ panSimpDecls (panTargetMoveStartToFront start declarations),
      DeclByteRanged d :=
  entryFirstTwoTransforms_byteRanged start declarations h

end Flapjack.Test.EntryTransformsByteRangedParity
