import Flapjack.CrepeInlinePass

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

end Flapjack
