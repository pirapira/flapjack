import Flapjack.Pancake.PanGlobalsByteRanged

/-!
Generated-name byte-rangedness parity (bead `flapjack-0up.3`).

Reproduces the direct HOL-EVAL fixtures
`scripts/hol-probes/pan_globals_fresh_name_probe.out` and
`scripts/hol-probes/pan_globals_new_main_name_probe.out` and checks that the
resulting names stay byte-ranged (`< 256` per character), which is the
precondition for reading them as HOL `mlstring` bytes.
-/

namespace Flapjack.Test.PanGlobalsNameByteRangedParity

open Flapjack
open Flapjack.Parser

/-- Boolean form of `StringByteRanged`, for `#guard` checks. -/
def byteRangedBool (s : String) : Bool :=
  s.toList.all (fun c => decide (c.toNat < 256))

def functionDecl (name : FunName) : Decl Nat :=
  .function
    { name := name
      inline := false
      exported := false
      params := []
      body := .skip
      returnShape := .one }

/-- Rows from `pan_globals_fresh_name_probe.out`. -/
def freshNameGuard : Bool :=
  freshNameHOL "x" [] == "x" &&
  freshNameHOL "x" ["x"] == "x'" &&
  freshNameHOL "x" ["x", "x'", "x''"] == "x'''" &&
  freshNameHOL "x'" ["x'", "x''"] == "x'''" &&
  freshNameHOL "main" ["worker", "helper"] == "main" &&
  globalFreshName "x" [] == "x" &&
  globalFreshName "x" ["x"] == "x'" &&
  globalFreshName "x" ["x", "x'", "x''"] == "x'''" &&
  globalFreshName "x'" ["x'", "x''"] == "x'''" &&
  globalFreshName "main" ["worker", "helper"] == "main"

/-- Rows from `pan_globals_new_main_name_probe.out`. -/
def newMainNameGuard : Bool :=
  globalNewMainName ([] : List (Decl Nat)) == "main" &&
  globalNewMainName [functionDecl "main", functionDecl "main'"] == "main''" &&
  globalNewMainName
    [.decl .one "g" (.const 7), .name "S" [], .exnDecl "E" .one,
     functionDecl "main"] == "main'" &&
  globalNewMainName [functionDecl "worker"] == "main"

/-- The generated names are all byte-ranged. -/
def byteRangedGuard : Bool :=
  byteRangedBool (freshNameHOL "x" ["x", "x'", "x''"]) &&
  byteRangedBool (freshNameHOL "x'" ["x'", "x''"]) &&
  byteRangedBool (globalFreshName "x" ["x", "x'", "x''"]) &&
  byteRangedBool (globalNewMainName [functionDecl "main", functionDecl "main'"]) &&
  byteRangedBool (globalNewMainName [functionDecl "worker"])

def parityGuard : Bool :=
  freshNameGuard && newMainNameGuard && byteRangedGuard

#eval parityGuard
#guard parityGuard

/-- Kernel-checked witnesses (not just `#guard`). -/
example : StringByteRanged (freshNameHOL "x" ["x", "x'", "x''"]) :=
  freshNameHOL_byteRanged "x" ["x", "x'", "x''"] (by
    unfold StringByteRanged CharsByteRanged; decide)

example : StringByteRanged (globalFreshName "x" ["x", "x'", "x''"]) :=
  globalFreshName_byteRanged "x" (by
    unfold StringByteRanged CharsByteRanged; decide) ["x", "x'", "x''"]

example : StringByteRanged
    (globalNewMainName [functionDecl "main", functionDecl "main'"]) :=
  globalNewMainName_byteRanged _

end Flapjack.Test.PanGlobalsNameByteRangedParity
