import Flapjack.Pancake.PanToCrep

/-!
# Original-domain parity for `pan_to_crep$wrap_rt`

The expected cases come from the direct HOL-EVAL fixture
`scripts/hol-probes/wrap_rt_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:131-136`.
-/

namespace Flapjack.Test.WrapRtParity

open Flapjack
open Flapjack.Pancake.PanLang

def isNone : Option (Shape × List Nat) → Bool
  | none => true
  | _ => false

def isOneWord : Option (Shape × List Nat) → Bool
  | some (.one, [1]) => true
  | _ => false

def isEmptyComb : Option (Shape × List Nat) → Bool
  | some (.comb [], []) => true
  | _ => false

def isNamed : Option (Shape × List Nat) → Bool
  | some (.named "S", []) => true
  | _ => false

def parityGuard : Bool :=
  isNone (wrapRt none) &&
  isNone (wrapRt (some (.one, []))) &&
  isOneWord (wrapRt (some (.one, [1]))) &&
  isEmptyComb (wrapRt (some (.comb [], []))) &&
  isNamed (wrapRt (some (.named "S", [])))

#eval parityGuard
#guard parityGuard

def isNoneHOL (value : Option (ShapeHOL × List Nat)) : Bool :=
  match value with
  | none => true
  | _ => false

def isOneWordHOL (value : Option (ShapeHOL × List Nat)) : Bool :=
  match value with
  | some (.one, [1]) => true
  | _ => false

def isEmptyCombHOL (value : Option (ShapeHOL × List Nat)) : Bool :=
  match value with
  | some (.comb [], []) => true
  | _ => false

def isNamedHOL (value : Option (ShapeHOL × List Nat)) : Bool :=
  match value with
  | some (.named name, []) => decide (name = Flapjack.Basis.Pure.MlString.ofString "S")
  | _ => false

/-- Replays the same five direct HOL `wrap_rt_probe.out` rows on the exact
    `mlstring`-backed `ShapeHOL` port `wrapRtHOL`. -/
def exactPortGuard : Bool :=
  isNoneHOL (wrapRtHOL none) &&
  isNoneHOL (wrapRtHOL (some (.one, []))) &&
  isOneWordHOL (wrapRtHOL (some (.one, [1]))) &&
  isEmptyCombHOL (wrapRtHOL (some (.comb [], []))) &&
  isNamedHOL (wrapRtHOL (some (.named (Flapjack.Basis.Pure.MlString.ofString "S"), [])))

/-- The narrow codec bridge relates the exact port to production `wrapRt`. -/
example : wrapRtHOL
      (((some (.named "S", []) : Option (Shape × List Nat))).map
        (fun pair => (Flapjack.Pancake.PanLang.shapeToHOL pair.1, pair.2))) =
    (wrapRt (some (.named "S", []))).map
      (fun pair => (Flapjack.Pancake.PanLang.shapeToHOL pair.1, pair.2)) :=
  wrapRtHOL_map_shapeToHOL _

#eval exactPortGuard
#guard exactPortGuard

def runChecks : IO Bool := do
  if parityGuard && exactPortGuard then
    IO.println "PASS wrap_rt none/empty-one/preserved parity + exact-ShapeHOL port"
  else
    IO.println "FAIL wrap_rt parity"
  pure (parityGuard && exactPortGuard)

end Flapjack.Test.WrapRtParity
