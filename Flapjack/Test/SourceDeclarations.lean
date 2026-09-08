import Flapjack.PanProgramSemantics

namespace Flapjack

def sourceDeclarationInitialState : PanValueProgramState Nat :=
  { structs := []
    globals := fun _ => none
    functions := []
    returnShapes := []
    exceptions := []
    memory := fun _ => none
    baseAddress := 0
    topAddress := 100
    bytesInWord := 1 }

def sourceDeclarationNoFfi : PanValueFfiHandler Nat :=
  fun _ _ _ _ _ _ => none

def sourceDeclarationNoPrimitive : PanPrimitiveHandler Nat :=
  fun _ _ => none

def sourceDeclarationSingleWord : List (PanValue Nat) → Option Nat
  | [.word value] => some value
  | _ => none

example :
    (evalPanValueDeclarations sourceDeclarationInitialState
      [.decl .one "answer" (.const 41),
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .return (.var .global "answer"), returnShape := .one }]).map
      (fun state => (state.globals "answer").bind (fun value =>
        match value with
        | .word value => some value
        | _ => none)) = some (some 41) := by
  decide +kernel

example :
    (panValueProgramResult sourceDeclarationInitialState sourceDeclarationNoPrimitive
      sourceDeclarationNoFfi 20
      [.decl .one "answer" (.const 41),
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .return (.var .global "answer"), returnShape := .one }]
      "main" []).bind sourceDeclarationSingleWord = some 41 := by
  decide +kernel

example :
    (panValueProgramResult sourceDeclarationInitialState sourceDeclarationNoPrimitive
      sourceDeclarationNoFfi 20
      [.name "Pair" [("left", .one), ("right", .one)],
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .return (.nField "right"
             (.nStruct "Pair" [("left", .const 3), ("right", .const 5)])),
           returnShape := .one }]
      "main" []).bind sourceDeclarationSingleWord = some 5 := by
  decide +kernel

def sourceDeclarationFfi : PanValueFfiHandler Nat :=
  fun function configuration _ array _ locals =>
    if function == "inc" then
      some (updatePanValueMap locals "result" (.word (configuration + array + 1)))
    else none

example :
    (panValueProgramResult sourceDeclarationInitialState sourceDeclarationNoPrimitive
      sourceDeclarationFfi 30
      [.function
         { name := "main", inline := false, exported := true, params := [],
           body := .seq
             (.extCall "inc" (.const 20) (.const 0) (.const 21) (.const 0))
             (.return (.var .local "result")), returnShape := .one }]
      "main" []).bind sourceDeclarationSingleWord = some 42 := by
  decide +kernel

example :
    (evalPanValueProgram sourceDeclarationInitialState sourceDeclarationNoPrimitive
      sourceDeclarationNoFfi 20
      [.function
         { name := "main", inline := false, exported := true, params := [],
           body := .return (.const 41), returnShape := .comb [.one, .one] }]
      "main" []).isNone = true := by
  decide +kernel

example :
    (evalPanValueProgram sourceDeclarationInitialState sourceDeclarationNoPrimitive
      sourceDeclarationNoFfi 30
      [.function
         { name := "badReturn", inline := false, exported := false, params := [],
           body := .return (.rStruct [.const 1, .const 2]), returnShape := .one },
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .seq (.call none "badReturn" []) (.return (.const 0)),
           returnShape := .one }]
      "main" []).isNone = true := by
  decide +kernel

example :
    (evalPanValueProgram sourceDeclarationInitialState sourceDeclarationNoPrimitive
      sourceDeclarationNoFfi 30
      [.exnDecl "E" (.comb [.one, .one]),
       .function
         { name := "badRaise", inline := false, exported := false, params := [],
           body := .raise "E" (.const 1), returnShape := .one },
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .seq (.call none "badRaise" []) (.return (.const 0)),
           returnShape := .one }]
      "main" []).isNone = true := by
  decide +kernel

example :
    (evalPanValueProgram sourceDeclarationInitialState sourceDeclarationNoPrimitive
      sourceDeclarationNoFfi 40
      [.exnDecl "E" .one,
       .function
         { name := "raiseGood", inline := false, exported := false, params := [],
           body := .raise "E" (.const 1), returnShape := .one },
       .function
         { name := "main", inline := false, exported := true, params := [],
           body := .seq
             (.dec "caught" .one (.const 0)
               (.call (some (none, some ("E", "missing", .skip)))
                 "raiseGood" []))
             (.return (.const 0)), returnShape := .one }]
      "main" []).isNone = true := by
  decide +kernel

end Flapjack
