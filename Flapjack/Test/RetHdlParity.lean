import Flapjack.Pancake.PanToCrep

/-!
# Original-domain parity for `pan_to_crep$ret_hdl`

The expected cases come from the direct HOL-EVAL fixture
`scripts/hol-probes/ret_hdl_probe.out`, sourced from
`cakeml/pancake/pan_to_crepScript.sml:122-127`.
-/

namespace Flapjack.Test.RetHdlParity

open Flapjack

def isSkip (program : CrepProg Nat) : Bool :=
  match program with
  | .skip => true
  | _ => false

def isTwoWordAssign (program : CrepProg Nat) : Bool :=
  match program with
  | .seq (.assign 1 (.loadGlob 0))
      (.seq (.assign 2 (.loadGlob 1)) .skip) => true
  | _ => false

def parityGuard : Bool :=
  isSkip (retHdl (α := Nat) .one []) &&
  isSkip (retHdl (α := Nat) (.comb []) []) &&
  isSkip (retHdl (α := Nat) (.comb [.one]) [1]) &&
  isTwoWordAssign (retHdl (α := Nat) (.comb [.one, .one]) [1, 2]) &&
  isSkip (retHdl (α := Nat) (.named "S") [1])

#eval parityGuard
#guard parityGuard

/-! ## Return-path bridge checks (Flapjack-only)

Kernel-checked reductions, not HOL fixtures: they compare the production
String-backed `retHdl` / `expHdlFiniteMap` helpers with the production
`assignRet` output. Only the separate width-indexed `assignRetW` carries the
exact `assign_ret_def` tag. -/

example : retHdl (α := Nat) (.comb [.one, .one]) [1, 2] = assignRet (α := Nat) [1, 2] :=
  retHdl_comb_eq_assignRet _ _ (by simp [Shape.shapeSize])

example : retHdl (α := Nat) (.comb [.one]) [1] = .skip :=
  retHdl_one_word_eq_skip _ _ (by simp [Shape.shapeSize])

example : expHdlFiniteMap
    (FUPDATE (FEMPTY : FiniteMap String (Shape × List Nat))
      ("x", (.comb [.one, .one], [1, 2]))) "x"
    = assignRet (α := Nat) [1, 2] :=
  expHdlFiniteMap_eq_assignRet (shape := .comb [.one, .one])
    (by simp [FLOOKUP, FUPDATE])

example : expHdl [("x", (.comb [.one, .one], [1, 2]))] "x"
    = assignRet (α := Nat) [1, 2] :=
  expHdl_eq_assignRet_of_lookupInfo (shape := .comb [.one, .one])
    (by simp [lookupInfo])

/-! ## Exact-carrier HOL-parity checks

The tagged exact `retHdlHOL` over `ShapeHOL` reproduces the same HOL-EVAL rows
`one`/`comb_empty`/`comb_one`/`comb_two`/`named`, and the kernel bridge
`crepProgToHOL_retHdl` carries the production `retHdl` onto it. -/

def isSkipHOL (program : CrepProgHOL 64) : Bool :=
  match program with
  | .skip => true
  | _ => false

def isTwoWordAssignHOL (program : CrepProgHOL 64) : Bool :=
  match program with
  | .seq (.assign 1 (.loadGlob 0))
      (.seq (.assign 2 (.loadGlob 1)) .skip) => true
  | _ => false

#guard isSkipHOL (retHdlHOL (width := 64) .one [])
#guard isSkipHOL (retHdlHOL (width := 64) (.comb []) [])
#guard isSkipHOL (retHdlHOL (width := 64) (.comb [.one]) [1])
#guard isTwoWordAssignHOL (retHdlHOL (width := 64) (.comb [.one, .one]) [1, 2])
#guard isSkipHOL
  (retHdlHOL (width := 64)
    (.named (Flapjack.Basis.Pure.MlString.ofString "S")) [1])

example (shape : Flapjack.Shape) (names : List Nat) :
    crepProgToHOL (retHdl (α := BitVec 64) shape names) =
      retHdlHOL (Flapjack.Pancake.PanLang.shapeToHOL shape) names :=
  crepProgToHOL_retHdl shape names

example : crepProgToHOL (assignRet (α := BitVec 64) [1, 2]) = assignRetHOL [1, 2] :=
  crepProgToHOL_assignRet [1, 2]

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS ret_hdl One/Comb/Named parity"
  else
    IO.println "FAIL ret_hdl parity"
  pure parityGuard

end Flapjack.Test.RetHdlParity
