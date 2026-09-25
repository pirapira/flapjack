import Flapjack.Pancake.PanToCrep

/-!
# Carrier parity fixtures for `pan_to_crep$exp_hdl`

The expected values come from the direct HOL-EVAL fixture
`scripts/hol-probes/exp_hdl_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:106-112`.  `expHdlHOL` reproduces those
HOL rows over the `MlString`-keyed / `ShapeHOL` / width-indexed `CrepProgHOL`
carriers, but its input is the production raw function
`MlString → Option (ShapeHOL × List Nat)`, which is broader than HOL's finite
map, so the `@[hol ... exp_hdl_def]` tag is WITHDRAWN (bead `flapjack-2s5`;
faithful finite-map port tracked by `flapjack-pxn.18.3.5.8.13.2`).  The
duplicate fixtures pin the finite-map semantics: the last binding wins for the
HOL `FLOOKUP` map.

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
  missingRow && knownRow && threeWordRow && dupRow dupFM

#eval parityGuard
#guard parityGuard

/-- The kernel bridge reproduces the exact carrier on a duplicate-bearing
    production map, so the executed `expHdlFiniteMap` and the (untagged)
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
