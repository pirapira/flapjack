import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanLang.Decl

/-!
Generated-name byte-rangedness parity (bead `flapjack-0up.3`).

Reproduces the direct HOL-EVAL fixtures
`scripts/hol-probes/pan_globals_fresh_name_probe.out` and
`scripts/hol-probes/pan_globals_new_main_name_probe.out` and checks that the
resulting names stay byte-ranged (`< 256` per character), which is the
precondition for reading them as HOL `mlstring` bytes.

The kernel-checked witnesses live in the same module as the executable
declarations (`Flapjack/Pancake/PanGlobals.lean`): `holMlStringWitness_*`.
-/

namespace Flapjack.Test.PanGlobalsNameByteRangedParity

open Flapjack

/-- Boolean form of `NameRanged`, for `#guard` checks. -/
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

/-- Same-module kernel-checked witnesses (not just `#guard`). -/
example : Flapjack.Pancake.PanLang.NameRanged
    (freshNameHOL "x" ["x", "x'", "x''"]) :=
  holMlStringWitness_freshNameHOL "x" ["x", "x'", "x''"] (by
    unfold Flapjack.Pancake.PanLang.NameRanged; decide)

example : Flapjack.Pancake.PanLang.NameRanged
    (globalFreshName "x" ["x", "x'", "x''"]) :=
  holMlStringWitness_globalFreshName "x" (by
    unfold Flapjack.Pancake.PanLang.NameRanged; decide) ["x", "x'", "x''"]

example : Flapjack.Pancake.PanLang.NameRanged
    (globalNewMainName [functionDecl "main", functionDecl "main'"]) :=
  holMlStringWitness_globalNewMainName _

/-- Production extraction lemmas (natural counterpart modules). -/
example {width : Nat} {function : String}
    {configuration configurationLength array arrayLength : Flapjack.Exp (BitVec width)}
    (h : Flapjack.Pancake.PanLang.ProgByteRanged
      (Flapjack.Prog.extCall function configuration configurationLength array arrayLength :
        Flapjack.Prog (BitVec width))) :
    Flapjack.Pancake.PanLang.NameRanged function :=
  Flapjack.Pancake.PanLang.progByteRanged_extCall_name h

example {width : Nat} {fd : Flapjack.FunDecl (BitVec width)}
    (h : Flapjack.Pancake.PanLang.DeclByteRanged (Flapjack.Decl.function fd)) :
    Flapjack.Pancake.PanLang.NameRanged fd.name :=
  Flapjack.Pancake.PanLang.declByteRanged_function_name h

end Flapjack.Test.PanGlobalsNameByteRangedParity
