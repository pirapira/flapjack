import Flapjack.Pancake.CrepInline.Pass

namespace Flapjack

/-! Executable regressions for direct Crepe call substitution. -/

def crepInlinePassEntry : CrepInlineEntry Nat :=
  ("identity", ([10], .return [.var 10]))

def crepInlineTailResult : CrepProg Nat :=
  crepInlineProg [crepInlinePassEntry]
    (.call none "identity" [.const 5])

#guard match crepInlineTailResult with
  | .seq .tick
      (.dec 11 (.const 5) (.dec 10 (.var 11) (.return [.var 10]))) => true
  | _ => false

def crepInlineReturnResult : CrepProg Nat :=
  crepInlineProg [crepInlinePassEntry]
    (.call (some ([20], none)) "identity" [.const 5])

#guard match crepInlineReturnResult with
  | .dec 21 (.const 0)
      (.seq
        (.dec 11 (.const 5)
          (.dec 10 (.var 11)
            (.seq .tick
              (.seq (.assign 21 (.var 10)) .skip))))
        (.seq (.assign 20 (.var 21)) .skip)) => true
  | _ => false

def crepInlineTopResult : List (CompiledFunction Nat) :=
  crepInlineTop ["identity"]
    [CompiledFunction.mk "identity" [10] (.return [.var 10]) .one]

#guard match crepInlineTopResult with
  | [function] =>
      function.name == "identity" && function.params == [10] &&
        match function.body with
        | .return [.var 10] => true
        | _ => false
  | _ => false

def crepInlineRecursiveEntries : List (CrepInlineEntry Nat) :=
  [("first", ([], .call none "second" [])),
    ("second", ([], .return [.const 9]))]

def crepInlineRecursiveResult : CrepProg Nat :=
  crepInlineProgRecursive crepInlineRecursiveEntries
    (crepInlineActiveNames crepInlineRecursiveEntries)
    (.call none "first" [])

#guard match crepInlineRecursiveResult with
  | .seq .tick (.seq .tick (.return [.const 9])) => true
  | _ => false

def crepInlineSelfResult : CrepProg Nat :=
  crepInlineProgRecursive
    [("self", ([], .call none "self" []))]
    (crepInlineActiveNames (α := Nat)
      [("self", ([], .call none "self" []))])
    (.call none "self" [])

#guard match crepInlineSelfResult with
  | .seq .tick (.call none "self" []) => true
  | _ => false

def crepInlineByNamesResult : List (CompiledFunction Nat) :=
  crepInlineTopRecursiveByNames ["first", "second"]
    [CompiledFunction.mk "first" [] (.call none "second" []) .one,
      CompiledFunction.mk "second" [] (.return [.const 9]) .one]

#guard match crepInlineByNamesResult with
  | [first, second] =>
      (match first.body with
      | .seq .tick (.return [.const 9]) => true
      | _ => false) &&
      (match second.body with
      | .return [.const 9] => true
      | _ => false)
  | _ => false

/-! Direct `crep_inline$transform_eoc` oracle coverage.  Cake's
    `transform_eoc_def` (crep_inlineScript.sml:138-149) rewrites returns into
    assignments to the caller's temporary return names, turns a returnless
    call into a call carrying those names, and recurses through declarations,
    loops, sequences, conditionals, and handler bodies. -/
def crepTransformEocCakeProbe : CrepProg Nat :=
  .dec 9 (.const 0)
    (.seq
      (.call none "leaf" [.const 1])
      (.while (.const 1)
        (.return [.var 9, .const 2])))

def crepTransformEocCakeResult : CrepProg Nat :=
  crepTransformEoc [20, 21] crepTransformEocCakeProbe

#guard match crepTransformEocCakeResult with
  | .dec 9 (.const 0)
      (.seq
        (.call (some ([20, 21], none)) "leaf" [.const 1])
        (.while (.const 1)
          (.seq
            (.assign 20 (.var 9))
            (.seq (.assign 21 (.const 2)) .skip)))) => true
  | _ => false

def crepTransformEocHandlerProbe : CrepProg Nat :=
  .call (some ([30], some (7, .return [.var 8]))) "callee" []

def crepTransformEocHandlerResult : CrepProg Nat :=
  crepTransformEoc [20, 21] crepTransformEocHandlerProbe

#guard match crepTransformEocHandlerResult with
  | .call (some ([30], some (7,
      (.seq (.assign 20 (.var 8)) (.skip))))) "callee" [] => true
  | _ => false

/-! Direct `crep_inline$transform_branch` coverage.  Cake's
    `transform_branch_def` (crep_inlineScript.sml:156-169) turns returns and
    returnless calls into assignments/calls followed by a break at the current
    loop depth, increments that depth through nested loops, and recursively
    transforms handler bodies. -/
def crepTransformBranchCakeProbe : CrepProg Nat :=
  .while (.const 1) (.return [.const 4])

def crepTransformBranchCakeResult : CrepProg Nat :=
  crepTransformBranch 0 [20] crepTransformBranchCakeProbe

#guard match crepTransformBranchCakeResult with
  | .while (.const 1)
      (.seq
        (.seq (.assign 20 (.const 4)) .skip)
        (.break 1)) => true
  | _ => false

def crepTransformBranchHandlerProbe : CrepProg Nat :=
  .call (some ([30], some (7, .return [.var 8]))) "callee" []

def crepTransformBranchHandlerResult : CrepProg Nat :=
  crepTransformBranch 0 [20, 21] crepTransformBranchHandlerProbe

#guard match crepTransformBranchHandlerResult with
  | .call (some ([30], some (7,
      (.seq
        (.seq (.assign 20 (.var 8)) .skip)
        (.break 0))))) "callee" [] => true
  | _ => false

/-! Direct `crep_inline$inline_nontail` oracle coverage.  Cake's
    `inline_nontail_def` (crep_inlineScript.sml:191-203) nests zero-valued
    return temporaries outside `arg_load`, then copies the temporary results
    back to the caller's destinations in order. -/
def crepInlineNontailCakeResult : CrepProg Nat :=
  crepInlineNontail
    (.return [.const 7, .var 12])
    [20, 21] [30, 31] [40]
    [.const 5] [10]

#guard match crepInlineNontailCakeResult with
  | .dec 30 (.const 0)
      (.dec 31 (.const 0)
        (.seq
          (.dec 40 (.const 5)
            (.dec 10 (.var 40)
              (.return [.const 7, .var 12])))
          (.seq
            (.assign 20 (.var 30))
          (.seq (.assign 21 (.var 31)) .skip)))) => true
  | _ => false

/-! Direct `crep_inline$inline_prog` oracle coverage.  Cake's
    `inline_prog_def` (crep_inlineScript.sml:203-216) keeps a handled outer
    call intact while recursively transforming the handler body. -/
def crepInlineHandlerProgResult : CrepProg Nat :=
  crepInlineProg [crepInlinePassEntry]
    (.call (some ([20], some (7,
      (.call none "identity" [.const 9])))) "outer" [])

#guard match crepInlineHandlerProgResult with
  | .call (some ([20], some (7,
      (.seq .tick
        (.dec 11 (.const 9)
          (.dec 10 (.var 11) (.return [.var 10]))))))) "outer" [] => true
  | _ => false

/-! Direct `crep_inline$compile_inl_prog` oracle coverage.  Cake's
    `compile_inl_prog_def` (crep_inlineScript.sml:259-262) maps each function
    with its own name removed from the inline map: `first` may inline `second`,
    while `second`'s return body remains unchanged. -/
def crepCompileInlProgCakeEntries : List (CrepInlineEntry Nat) :=
  [("first", ([], .call none "second" [])),
   ("second", ([], .return [.const 9]))]

def crepCompileInlProgCakeResult : List (CompiledFunction Nat) :=
  crepInlineFunctionsRecursive crepCompileInlProgCakeEntries
    (crepInlineActiveNames crepCompileInlProgCakeEntries)
    [CompiledFunction.mk "first" [] (.call none "second" []) .one,
     CompiledFunction.mk "second" [] (.return [.const 9]) .one]

#guard match crepCompileInlProgCakeResult with
  | [first, second] =>
      (first.name == "first" &&
        match first.body with
        | .seq .tick (.return [.const 9]) => true
        | _ => false) &&
      (second.name == "second" &&
        match second.body with
        | .return [.const 9] => true
        | _ => false)
  | _ => false

end Flapjack
