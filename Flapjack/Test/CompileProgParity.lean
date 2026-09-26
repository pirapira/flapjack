import Flapjack.Pipeline
import Flapjack.Pancake.PanToCrep.Compile

namespace Flapjack.Test.CompileProgParity

open Flapjack

def compileProgProbeContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 0,
    bytesInWord := 1 }

#check @crepGetEidsFromDecls_lookup_iff_exception
#check @allocatedNames_gt
#check @freshNames_gt
#check @mem_crepExpVars_le_maxCrepExpVar

theorem maxCrepExpVar_mem_fixture :
    7 ≤ maxCrepExpVar ([.var 3, .const 0, .var 7] : List (CrepExp Nat)) := by
  apply mem_crepExpVars_le_maxCrepExpVar
  simp [crepExpVars]

theorem allocatedNames_gt_fixture : (0 : Nat) < (allocatedNames compileProgProbeContext .one).headD 0 := by
  have hmem : (allocatedNames compileProgProbeContext .one).headD 0 ∈ allocatedNames compileProgProbeContext .one := by
    simp [allocatedNames, compileProgProbeContext]
  have := allocatedNames_gt compileProgProbeContext .one hmem
  simpa [compileProgProbeContext] using this

theorem freshNames_gt_fixture : (0 : Nat) < (freshNames compileProgProbeContext 1 1).headD 0 := by
  have hmem : (freshNames compileProgProbeContext 1 1).headD 0 ∈ freshNames compileProgProbeContext 1 1 := by
    simp [freshNames, compileProgProbeContext]
  have := freshNames_gt compileProgProbeContext 1 1 (by decide) hmem
  simpa [compileProgProbeContext] using this

def compileProgProbeDecls : List (Decl Nat) :=
  [.function
     { name := "leaf", inline := true, exported := false, params := [],
       body := .return (.const 7), returnShape := .one },
   .function
     { name := "mid", inline := true, exported := false, params := [],
       body := .call none "leaf" [], returnShape := .one },
   .function
     { name := "main", inline := false, exported := true, params := [],
       body := .call none "mid" [], returnShape := .one }]

/-! Direct `compile_inl_top_def` boundary oracle: the named source pass keeps
    the function table while recursively expanding the selected inline names. -/
def compileInlTopOracle : Bool :=
  match panToCrepCompileInlTop ["first", "second"]
      [CompiledFunction.mk "first" [] (.call none "second" []) .one,
       CompiledFunction.mk "second" [] (.return [.const 9]) .one] with
  | [first, second] =>
      (match first.body with
      | .seq .tick (.return [.const 9]) => true
      | _ => false) &&
      (match second.body with
      | .return [.const 9] => true
      | _ => false)
  | _ => false

#guard compileInlTopOracle

/-! Direct HOL `compile_prog_probe.out` cases for the production triple-list
    `compile_inl_top` boundary. The first duplicate `id` definition wins in
    HOL's `alist_to_fmap`, while nested inline calls expand recursively. -/
def holInlineDuplicateInput : List (FunName × List Nat × CrepProg (BitVec 8)) :=
  [("id", [], .return [.const 7]),
   ("id", [], .return [.const 9]),
   ("main", [], .call none "id" [])]

def holInlineDuplicateParity : Bool :=
  match compileInlTopHOL ["id"] holInlineDuplicateInput with
  | [(first, [], .return [.const firstValue]),
     (second, [], .return [.const secondValue]),
     (main, [], .seq .tick (.return [.const returned]))] =>
      first == "id" && second == "id" && main == "main" &&
        firstValue == 7 && secondValue == 9 && returned == 7
  | _ => false

#guard holInlineDuplicateParity

def holInlineNestedInput : List (FunName × List Nat × CrepProg (BitVec 8)) :=
  [("leaf", [], .return [.const 7]),
   ("mid", [], .call none "leaf" []),
   ("main", [], .call none "mid" [])]

def holInlineNestedParity : Bool :=
  match compileInlTopHOL ["leaf", "mid"] holInlineNestedInput with
  | [(leaf, [], .return [.const leafValue]),
     (mid, [], .seq .tick (.return [.const midValue])),
     (main, [], .seq .tick (.seq .tick (.return [.const mainValue])))] =>
      leaf == "leaf" && mid == "mid" && main == "main" &&
        leafValue == 7 && midValue == 7 && mainValue == 7
  | _ => false

#guard holInlineNestedParity

/-! Direct `compile_prog_probe.out` parity at the new exact
    `compile_prog` triple-list boundary. These declarations are word8 as in
    the HOL EVAL query, and cover the complete empty, duplicate-first, and
    nested-inline outputs rather than testing `compile_inl_top` in isolation. -/
def compileProgTopEmptyParity : Bool :=
  match compileProgTopHOL ([] : List (Decl (BitVec 8))) with
  | [] => true
  | _ => false

def compileProgTopDuplicateParity : Bool :=
  let declarations : List (Decl (BitVec 8)) :=
    [.function
       { name := "id", inline := true, exported := false, params := [],
         body := .return (.const 7), returnShape := .one },
     .function
       { name := "id", inline := true, exported := false, params := [],
         body := .return (.const 9), returnShape := .one },
     .function
       { name := "main", inline := false, exported := true, params := [],
         body := .call none "id" [], returnShape := .one }]
  match compileProgTopHOL declarations with
  | [("id", [], .return [.const 7]),
     ("id", [], .return [.const 9]),
     ("main", [], .seq .tick (.return [.const 7]))] => true
  | _ => false

def compileProgTopNestedParity : Bool :=
  let declarations : List (Decl (BitVec 8)) :=
    [.function
       { name := "leaf", inline := true, exported := false, params := [],
         body := .return (.const 7), returnShape := .one },
     .function
       { name := "mid", inline := true, exported := false, params := [],
         body := .call none "leaf" [], returnShape := .one },
     .function
       { name := "main", inline := false, exported := true, params := [],
         body := .call none "mid" [], returnShape := .one }]
  match compileProgTopHOL declarations with
  | [("leaf", [], .return [.const 7]),
     ("mid", [], .seq .tick (.return [.const 7])),
     ("main", [], .seq .tick (.seq .tick (.return [.const 7])))] => true
  | _ => false

#guard compileProgTopEmptyParity
#guard compileProgTopDuplicateParity
#guard compileProgTopNestedParity

/-! The fixture is the direct HOL evaluation of
    `pan_to_crep$compile_prog` on the same inline callee/caller pair. -/
theorem compile_prog_inline_call_parity :
    compileProgToCrep compileProgProbeContext compileProgProbeDecls =
      [{ name := "leaf", params := [], body := .return [.const 7],
         returnShape := .one },
       { name := "mid", params := [],
         body := .seq .tick (.return [.const 7]), returnShape := .one },
       { name := "main", params := [],
         body := .seq .tick (.seq .tick (.return [.const 7])), returnShape := .one }] := by
  simp [compileProgToCrep, pipelineInlineNames, compileToCrep,
    compileFunctionsSource, compileFunDeclSource, panToCrepCompFunc,
    panToCrepVars_eq, Shape.shapeSize, panToCrepCompileInlTop,
    functionInfos, compileProgProbeContext, compileProgProbeDecls,
    compileProg, compileExp, compileArgs,
    crepInlineTopRecursiveByNames, crepInlineTopRecursive,
    crepInlineFunctionsRecursive, crepInlineActiveNames,
    crepInlineProgRecursive, crepInlineLookup, crepInlineCallBody,
    crepInlineTail, crepArgLoad, crepInlineTmpNames, crepUnreachElim,
    nestedDecs]

/-! Cake's `first_compile_prog_all_distinct` regression: the complete
    source-shaped `compile_prog` boundary keeps every function name distinct
    after the selected inline bodies have been rewritten. -/
theorem compile_prog_first_compile_prog_all_distinct :
    (compileProgToCrep compileProgProbeContext compileProgProbeDecls).map
      CompiledFunction.name |>.Nodup := by
  exact compileProgToCrep_names_nodup _ _ (by
    simp [compileProgProbeDecls, functionDeclarationNames])

/-! Cake's `compile_prog_distinct_params` regression at the same complete
    source-shaped boundary. -/
theorem compile_prog_compile_prog_distinct_params :
    ∀ function ∈ compileProgToCrep compileProgProbeContext compileProgProbeDecls,
      function.params.Nodup := by
  exact compileProgToCrep_params_nodup _ _

def parityGuard : Bool :=
  match compileProgToCrep compileProgProbeContext compileProgProbeDecls with
  | [{ name := "leaf", params := [], body := .return [.const 7],
         returnShape := .one },
     { name := "mid", params := [],
       body := .seq .tick (.return [.const 7]), returnShape := .one },
     { name := "main", params := [],
       body := .seq .tick (.seq .tick (.return [.const 7])), returnShape := .one }] => true
  | _ => false

#eval parityGuard
#guard parityGuard

/-! `pan_to_crep$compile` chooses a shared-store temporary from the largest
    variable in the *address* expression (`pan_to_crepScript.sml:291-299`).
    This small oracle catches the accidental value-based choice that aliases a
    store's address when the value is a lower-numbered local. -/
def shMemStoreAddressTempContext : CompileContext Nat :=
  { vars := [("out", (.one, [2])), ("len", (.one, [1]))], functions := [],
    exceptions := [], maxVar := 2, bytesInWord := 8 }

def shMemStoreAddressTempParity : Bool :=
  match compileProg shMemStoreAddressTempContext
      (.shMemStore .opW (.var .local "out") (.var .local "len")) with
  | .dec 3 (.var 1) (.shMem .store 3 (.var 2)) => true
  | _ => false

#guard shMemStoreAddressTempParity

/-! Cake's `crep_inline` prunes an inline callee at its first terminal
    statement before splicing it into the caller.  The assignment after the
    return is deliberately unreachable and must not survive the inline. -/
def compileProgUnreachableInlineEntries : List (CrepInlineEntry Nat) :=
  [("callee", ([],
    .seq (.return [.const 7]) (.assign 99 (.const 42))))]

def compileProgUnreachableInlineResult : CrepProg Nat :=
  crepInlineProgRecursive compileProgUnreachableInlineEntries
    (crepInlineActiveNames compileProgUnreachableInlineEntries)
    (.call none "callee" [])

def compileProgUnreachableInlineGuard : Bool :=
  match compileProgUnreachableInlineResult with
  | .seq .tick (.return [.const 7]) => true
  | _ => false

#guard compileProgUnreachableInlineGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS compile_prog inline-call source parity"
  else
    IO.println "FAIL compile_prog parity"
  if compileProgUnreachableInlineGuard then
    IO.println "PASS compile_prog unreach-before-inline parity"
  else
    IO.println "FAIL compile_prog unreach-before-inline parity"
  if shMemStoreAddressTempParity then
    IO.println "PASS compile_prog shared-store address temporary parity"
  else
    IO.println "FAIL compile_prog shared-store address temporary parity"
  pure (parityGuard && compileProgUnreachableInlineGuard &&
    shMemStoreAddressTempParity)

end Flapjack.Test.CompileProgParity
