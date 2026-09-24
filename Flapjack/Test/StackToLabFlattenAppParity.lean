import Flapjack.Compiler.Backend.LabProps
import Flapjack.Compiler.Encoders.Asm

/-! Parity for the `app_list` representation bridge: flattening the HOL-shaped
`flattenApp` output with `misc$append`/`appListFlatten` gives the flat production
`flatten` output, matching the direct HOL rows in
`scripts/hol-probes/stack_to_lab_flatten_app_list_probe.out`. -/

namespace Flapjack.Test.StackToLabFlattenAppParity

open Flapjack
open Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

private abbrev W := BitVec 8

private abbrev P :=
  Flapjack.Compiler.Backend.StackLang.Prog (WordLangInst W) Flapjack.Cmp (WordRegImm W) Flapjack.BinOp
    Flapjack.WordMemOp (WordLangAddr W) String

example :
    appListFlatten (flattenApp (flattenOps (width := 8)) (0 : W) true (.tick : P) 0 0 [] []) =
      ([.asm (.asmi (.inst .skip)) [] 0], false, 0) := by
  simp [flattenApp, appListFlatten, appListAppend, appendAux, flattenOps]

example :
    appListFlatten (flattenApp (flattenOps (width := 8)) (0 : W) true (.halt 0 : P) 0 0 [] []) =
      ([.labAsm .halt (0 : W) [] 0], true, 0) := by
  simp [flattenApp, appListFlatten, appListAppend, appendAux, flattenOps]

example :
    appListFlatten (flattenApp (flattenOps (width := 8)) (0 : W) true
        (.inst (.skip : WordLangInst W) : P) 0 0 [] []) =
      ([.asm (.asmi (.inst .skip)) [] 0], false, 0) := by
  simp [flattenApp, appListFlatten, appListAppend, appendAux, flattenOps]

example :
    appListFlatten (flattenApp (flattenOps (width := 8)) (0 : W) true (.raise 3 : P) 0 0 [] []) =
      ([.asm (.asmi (.jumpReg 3)) [] 0], true, 0) := by
  simp [flattenApp, appListFlatten, appListAppend, appendAux, flattenOps]

/-- The recursive production case matching the HOL `append` row: the flat
`flatten` of `Seq Tick (Halt 0)` at root (`tail = true`). -/
example :
    (flatten (flattenOps (width := 8)) (0 : W) true
        (.seq (.tick : P) (.halt 0) : P) 0 0 [] []).1 =
      [.asm (.asmi (.inst .skip)) [] 0, .label 0 1 0, .labAsm .halt (0 : W) [] 0] := by
  simp [flatten, flattenOps]

example :
    (flatten (flattenOps (width := 8)) (0 : W) true
        (.ite .equal 0 (.reg 1) (.skip : P) (.skip : P) : P) 0 0 [] []).1 = [] := by
  simp [flatten, flattenOps, stackIsSkip]

example :
    (flatten (flattenOps (width := 8)) (0 : W) true
        (.ite .equal 0 (.reg 1) (.skip : P) (.inst (.skip : WordLangInst W)) : P) 0 0 [] []).1 =
      [.labAsm (.jumpCmp .equal 0 (.reg 1) (.lab 0 0)) (0 : W) [] 0,
        .asm (.asmi (.inst .skip)) [] 0, .label 0 0 0] := by
  simp [flatten, flattenOps, stackIsSkip]

example :
    appListFlatten (flattenApp (flattenOps (width := 8)) (0 : W) true
        (.ite .equal 0 (.reg 1) (.skip : P) (.skip : P)) 0 0 [] []) =
      flatten (flattenOps (width := 8)) (0 : W) true
        (.ite .equal 0 (.reg 1) (.skip : P) (.skip : P)) 0 0 [] [] :=
  flattenApp_ite (flattenOps (width := 8)) (0 : W) true .equal 0 (.reg 1) (.skip : P) (.skip : P)
    0 0 [] []
    (fun n => flattenApp_skip (flattenOps (width := 8)) (0 : W) false 0 n [] [])
    (fun n => flattenApp_skip (flattenOps (width := 8)) (0 : W) false 0 n [] [])

example :
    appListFlatten (flattenApp (flattenOps (width := 8)) (0 : W) true
        (.ite .equal 0 (.reg 1) (.skip : P) (.inst (.skip : WordLangInst W))) 0 0 [] []) =
      flatten (flattenOps (width := 8)) (0 : W) true
        (.ite .equal 0 (.reg 1) (.skip : P) (.inst (.skip : WordLangInst W))) 0 0 [] [] :=
  flattenApp_ite (flattenOps (width := 8)) (0 : W) true .equal 0 (.reg 1) (.skip : P)
    (.inst (.skip : WordLangInst W)) 0 0 [] []
    (fun n => flattenApp_skip (flattenOps (width := 8)) (0 : W) false 0 n [] [])
    (fun n => flattenApp_inst (flattenOps (width := 8)) (0 : W) false (.skip : WordLangInst W) 0 n [] [])

example :
    appListFlatten (flattenApp (flattenOps (width := 8)) (0 : W) true (.tick : P) 0 0 [] []) =
      flatten (flattenOps (width := 8)) (0 : W) true (.tick : P) 0 0 [] [] :=
  flattenApp_tick (flattenOps (width := 8)) (0 : W) true 0 0 [] []

example :
    appListFlatten (flattenApp (flattenOps (width := 8)) (0 : W) true
        (.call (some ((.skip : P), 0, 0, 0)) (.inl 1) (some ((.skip : P), 0, 0))) 0 0 [] []) =
      flatten (flattenOps (width := 8)) (0 : W) true
        (.call (some ((.skip : P), 0, 0, 0)) (.inl 1) (some ((.skip : P), 0, 0))) 0 0 [] [] :=
  flattenApp_appListFlatten_eq_flatten (flattenOps (width := 8)) (0 : W) true _ 0 0 [] []

def runChecks : IO Bool := do
  IO.println "PASS stack_to_lab flattenApp app_list bridge matches all 7 oracle rows"
  pure true

end Flapjack.Test.StackToLabFlattenAppParity