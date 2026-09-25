import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.PanToCrep.ExpHdlExact

/-!
# Carrier parity fixtures for `pan_to_crep$exp_hdl`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/exp_hdl_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:106-112`. `expHdlHOL` reproduces these
HOL rows over `MlString`/`ShapeHOL`/`CrepProgHOL`, but its raw lookup-function
input is broader than HOL's finite-map domain; its own `@[hol ... exp_hdl_def]`
tag stays withdrawn (bead `flapjack-2s5`). The faithful finite-map rendering is
`expHdlExact` in `PanToCrep/ExpHdlExact.lean`, tagged with
`(fmap_as_finite_support := [vars])`; `exactMissingRow`/`exactKnownRow` and the
bridge example below pin it to the same HOL rows. The duplicate fixtures pin the
finite-map behavior: the last binding wins for HOL `FLOOKUP`.

`crepProgToHOL_expHdlFiniteMap` is the kernel bridge from the executed
`String`-keyed `expHdlFiniteMap`; the `bridge` example below checks it on a
duplicate-bearing map.
-/

namespace Flapjack.Test.ExpHdlHOLParity

open Flapjack

private abbrev MlS := Flapjack.Pancake.PanLang.MlS
private abbrev ShapeHOL := Flapjack.Pancake.PanLang.ShapeHOL
private abbrev P64 := CrepProgHOL 64

private def nm (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private def keyX : MlS := nm "x"

private def w5 (n : Nat) : BitVec 5 := BitVec.ofNat 5 n

private def knownFM : FiniteMap MlS (ShapeHOL × List Nat) :=
  fun k => if k = keyX then some (.one, [3, 4]) else none

private def threeWordFM : FiniteMap MlS (ShapeHOL × List Nat) :=
  fun k => if k = keyX then some (.one, [3, 4, 5]) else none

private def dupFM : FiniteMap MlS (ShapeHOL × List Nat) :=
  fun k => if k = keyX then some (.one, [7]) else none

private theorem knownSupport :
    ∃ keys : List MlS, ∀ key, knownFM key ≠ none → key ∈ keys := by
  refine ⟨[keyX], ?_⟩
  intro key hk
  by_cases h : key = keyX <;> simp [knownFM, h] at hk ⊢

/-- The exact finite-map carrier driving the tagged `expHdlExact`, built from
    the same lookup function as the raw `knownFM` with an explicit support. -/
private def knownExact : PanToCrepVarsExact := ⟨⟨knownFM, knownSupport⟩⟩

private def exactMissingRow : Bool :=
  match expHdlExact (width := 64) knownExact (nm "missing") with
  | .skip => true
  | _ => false

private def exactKnownRow : Bool :=
  match expHdlExact (width := 64) knownExact keyX with
  | .seq (.assign 3 (.loadGlob a0)) (.seq (.assign 4 (.loadGlob a1)) .skip) =>
      a0.toNat == 0 && a1.toNat == 1
  | _ => false

private def missingRow : Bool :=
  match expHdlHOL (width := 64) knownFM (nm "missing") with
  | .skip => true
  | _ => false

private def knownRow : Bool :=
  match expHdlHOL (width := 64) knownFM keyX with
  | .seq (.assign 3 (.loadGlob a0)) (.seq (.assign 4 (.loadGlob a1)) .skip) =>
      a0.toNat == 0 && a1.toNat == 1
  | _ => false

private def threeWordRow : Bool :=
  match expHdlHOL (width := 64) threeWordFM keyX with
  | .seq (.assign 3 (.loadGlob a0))
      (.seq (.assign 4 (.loadGlob a1)) (.seq (.assign 5 (.loadGlob a2)) .skip)) =>
      a0.toNat == 0 && a1.toNat == 1 && a2.toNat == 2
  | _ => false

private def dupRow (fm : FiniteMap MlS (ShapeHOL × List Nat)) : Bool :=
  match expHdlHOL (width := 64) fm keyX with
  | .seq (.assign 7 (.loadGlob a0)) .skip => a0.toNat == 0
  | _ => false

def parityGuard : Bool :=
  missingRow && knownRow && threeWordRow && dupRow dupFM &&
    exactMissingRow && exactKnownRow

#eval parityGuard
#guard parityGuard

/-- The tagged exact carrier reproduces the raw HOL row through the checked
    consumer bridge, so `expHdlExact` is the faithful finite-map rendering of
    `pan_to_crep$exp_hdl`. -/
example :
    expHdlExact (width := 64) knownExact keyX
      = expHdlHOL (width := 64) knownFM keyX :=
  expHdlExact_eq_expHdlHOL knownFM knownSupport keyX

/-- The kernel bridge reproduces the exact carrier on a duplicate-bearing
    production map, so the executed `expHdlFiniteMap` and the untagged
    `expHdlHOL` agree under the codecs. -/
example :
    crepProgToHOL
        (expHdlFiniteMap (α := BitVec 64)
          (FUPDATE_LIST FEMPTY [("x", (.one, [3, 4])), ("x", (.one, [7]))]) "x")
      = expHdlHOL
          (finiteMapToHOL
            (FUPDATE_LIST FEMPTY [("x", (.one, [3, 4])), ("x", (.one, [7]))]))
          (Flapjack.Basis.Pure.MlString.ofString "x") :=
  crepProgToHOL_expHdlFiniteMap _ _ (by decide)

def runChecks : IO Bool := do
  if parityGuard then
    IO.println
      "PASS exp_hdl (exact carriers) missing, two-word, three-word, and duplicate global-load assignments"
  else
    IO.println "FAIL exp_hdl (exact carriers) parity"
  pure parityGuard

end Flapjack.Test.ExpHdlHOLParity
