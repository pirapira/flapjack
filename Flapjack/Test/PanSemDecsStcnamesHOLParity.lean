import Flapjack.Pancake.Proofs.PanToCrep

/-!
# Parity checks for the exact `decs_stcnames` port

These fixtures mirror the direct HOL EVAL rows in
`scripts/hol-probes/pan_sem_decs_stcnames_probe.out`.  `ShapeHOL`,
`StructInfoHOLExact`, `DeclHOL` and the resulting context have no `DecidableEq`
or `BEq`, so the observations are `Bool`/`Option Nat` projections.
-/

namespace Flapjack.Test.PanSemDecsStcnamesHOLParity

open Flapjack
open Flapjack.Pancake.PanLang


private abbrev ml (s : String) : MlS := Flapjack.Basis.Pure.MlString.ofString s

private def nameAF : List (DeclHOL 8) :=
  [.name (ml "A") [(ml "f", .one)]]

private def nameADup : List (DeclHOL 8) :=
  [.name (ml "A") [], .name (ml "A") []]

private def dupField : List (DeclHOL 8) :=
  [.name (ml "A") [(ml "f", .one), (ml "f", .one)]]

private def wfMiss : List (DeclHOL 8) :=
  [.name (ml "A") [(ml "f", .named (ml "Z"))]]

private def skipDecl : List (DeclHOL 8) :=
  [.decl .one (ml "x") (.const (7 : BitVec 8)), .name (ml "A") []]

private def ctxLen (result : Option StructContextExact) : Option Nat :=
  result.map List.length

private def ctxFirstSize : Option StructContextExact → Option Nat
  | some ((_, info) :: _) => some info.size
  | some [] => none
  | none => none

/-- `decs_stcnames [] [] = SOME []`. -/
example : ctxLen (decsStcnamesHOLExact (width := 8) [] ([] : List (DeclHOL 8))) = some 0 := by
  decide

/-- A well-formed `Name` entry extends the context. -/
example : ctxLen (decsStcnamesHOLExact (width := 8) [] nameAF) = some 1 := by decide

/-- Its `struct_info.size` is `size_of_sh_with_ctxt [] (Comb [One]) = 1`. -/
example : ctxFirstSize (decsStcnamesHOLExact (width := 8) [] nameAF) = some 1 := by decide

/-- A duplicate structure name is rejected. -/
example : (decsStcnamesHOLExact (width := 8) [] nameADup).isNone = true := by decide

/-- Duplicate field names are rejected. -/
example : (decsStcnamesHOLExact (width := 8) [] dupField).isNone = true := by decide

/-- An unknown `Named` field shape is rejected. -/
example : (decsStcnamesHOLExact (width := 8) [] wfMiss).isNone = true := by decide

/-- `Decl`/`Function`/`ExnDecl` entries are skipped and the scan continues. -/
example : ctxLen (decsStcnamesHOLExact (width := 8) [] skipDecl) = some 1 := by decide

/-- `decs_stcnames_lemma`: a code list of only function/exception declarations
leaves the context unchanged (tagged exact port). -/
private def functionAndExn : List (DeclHOL 8) :=
  [.function ⟨ml "f", false, false, [], .skip, .one⟩,
   .exnDecl (ml "e") .one]

example (context : StructContextExact) :
    decsStcnamesHOLExact (width := 8) context functionAndExn = some context := by
  apply decsStcnamesHOLExact_of_functions_or_exnDecls
  native_decide

private def decsGuard : Bool :=
  (ctxLen (decsStcnamesHOLExact (width := 8) [] ([] : List (DeclHOL 8))) == some 0) &&
  (ctxLen (decsStcnamesHOLExact (width := 8) [] nameAF) == some 1) &&
  (ctxFirstSize (decsStcnamesHOLExact (width := 8) [] nameAF) == some 1) &&
  (decsStcnamesHOLExact (width := 8) [] nameADup).isNone &&
  (decsStcnamesHOLExact (width := 8) [] dupField).isNone &&
  (decsStcnamesHOLExact (width := 8) [] wfMiss).isNone &&
  (ctxLen (decsStcnamesHOLExact (width := 8) [] skipDecl) == some 1)

#eval decsGuard
#guard decsGuard

def runChecks : IO Bool := do
  IO.println "PASS panSem decs_stcnames exact carrier matches all 7 oracle rows"
  pure decsGuard

end Flapjack.Test.PanSemDecsStcnamesHOLParity