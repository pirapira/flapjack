import Flapjack.Compile
import Flapjack.CrepeInline

/-!
The first executable call-substitution layer for Crepe.

The inline map is represented as the finite list used by the CakeML pass.  This
slice performs one direct call substitution; recursive traversal of the
inlined callee is a separate layer so its termination measure stays explicit.
-/

namespace Flapjack

abbrev CrepInlineEntry (α : Type u) := FunName × (List Nat × CrepProg α)

def crepInlineLookup [BEq FunName] (name : FunName) :
    List (CrepInlineEntry α) → Option (List Nat × CrepProg α)
  | [] => none
  | (candidate, definition) :: entries =>
      if name == candidate then some definition else crepInlineLookup name entries

def crepInlineRemove [BEq FunName] (name : FunName) :
    List (CrepInlineEntry α) → List (CrepInlineEntry α)
  | [] => []
  | entry :: entries =>
      if entry.1 == name then crepInlineRemove name entries
      else entry :: crepInlineRemove name entries

def crepInlineTmpNames (arguments argumentNames : List Nat) : List Nat :=
  let maximum := max (arguments.foldl max 0) (argumentNames.foldl max 0)
  (List.range argumentNames.length).map (fun offset => offset + maximum + 1)

def crepAllDistinct : List Nat → Bool
  | [] => true
  | name :: names => !names.contains name && crepAllDistinct names

def crepInlineCall [BEq FunName] [OfNat α 0] [OfNat α 1]
    (inlineable : List (CrepInlineEntry α))
    (returnInfo : Option (List Nat × Option (α × CrepProg α)))
    (name : FunName) (arguments : List (CrepExp α)) : CrepProg α :=
  match crepInlineLookup name inlineable with
  | none => .call returnInfo name arguments
  | some (argumentNames, body) =>
      let temporaryNames := crepInlineTmpNames
        (arguments.flatMap crepExpVars) argumentNames
      match returnInfo with
      | none =>
          crepInlineTail
            (crepArgLoad temporaryNames arguments argumentNames body)
      | some (returnNames, none) =>
          if !crepAllDistinct returnNames then
            .call returnInfo name arguments
          else
            let returnMaximum := returnNames.foldl max 0
            let bodyMaximum := crepVmaxProg body
            let temporaryMaximum := temporaryNames.foldl max 0
            let returnStart := max returnMaximum
              (max bodyMaximum temporaryMaximum) + 1
            let temporaryReturns :=
              (List.range returnNames.length).map
                (fun offset => offset + returnStart)
            let transformed :=
              if crepNotBranchRet body then
                .seq .tick (crepTransformEoc temporaryReturns body)
              else
                .while (.const 1)
                  (crepTransformBranch 0 temporaryReturns body)
            crepInlineNontail transformed returnNames temporaryReturns
              temporaryNames arguments argumentNames
      | some (_, some _) => .call returnInfo name arguments

def crepInlineProg [BEq FunName] [OfNat α 0] [OfNat α 1]
    (inlineable : List (CrepInlineEntry α)) : CrepProg α → CrepProg α
  | .dec name value body =>
      .dec name value (crepInlineProg inlineable body)
  | .seq first second =>
      .seq (crepInlineProg inlineable first) (crepInlineProg inlineable second)
  | .ite condition thenBranch elseBranch =>
      .ite condition (crepInlineProg inlineable thenBranch)
        (crepInlineProg inlineable elseBranch)
  | .while condition body =>
      .while condition (crepInlineProg inlineable body)
  | .call none name arguments =>
      crepInlineCall inlineable none name arguments
  | .call (some (returnNames, none)) name arguments =>
      crepInlineCall inlineable (some (returnNames, none)) name arguments
  | .call (some (returnNames, some (handler, body))) name arguments =>
      .call (some (returnNames, some (handler,
        crepInlineProg inlineable body))) name arguments
  | program => program
termination_by program => sizeOf program
decreasing_by
  all_goals simp_wf; decreasing_trivial

def crepInlineFunctions [BEq FunName] [OfNat α 0] [OfNat α 1]
    (inlineable : List (CrepInlineEntry α)) :
    List (CompiledFunction α) → List (CompiledFunction α)
  | [] => []
  | function :: functions =>
      { function with body :=
          crepInlineProg (crepInlineRemove function.name inlineable) function.body } ::
        crepInlineFunctions inlineable functions

def crepInlineTop [BEq FunName] [OfNat α 0] [OfNat α 1]
    (inlineNames : List FunName) (functions : List (CompiledFunction α)) :
    List (CompiledFunction α) :=
  let inlineable := (functions.filter (fun function =>
      inlineNames.contains function.name)).map (fun function =>
        (function.name, (function.params, function.body)))
  crepInlineFunctions inlineable functions

end Flapjack
