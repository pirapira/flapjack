import Flapjack.Pancake.PanGlobals

namespace Flapjack.Test.PanGlobalsDecShapesParity

/-! Direct parity for `pan_globals$dec_shapes_def`
    (`pan_globalsScript.sml:228`). -/
def parityGuard : Bool :=
  let empty := globalDeclShapes ([] : List (Decl Nat))
  let mixed :=
    globalDeclShapes
      [.function
        { name := "f", inline := false, exported := false, params := [],
          body := .skip, returnShape := .one },
       .decl (.comb [.one, .named "S"]) "g" (.const 7),
       .name "S" [], .exnDecl "E" (.named "T"),
       .decl .one "h" (.const 9)]
  (match empty with
  | [] => true
  | _ => false) &&
  (match mixed with
  | [.comb [.one, .named "S"], .one] => true
  | _ => false)

#eval parityGuard
#guard parityGuard

/-! Counterparts of Cake's `dec_shapes` cluster
    (`pan_globalsProofScript.sml:2328-2361`), exercised on the same fixture. -/
def clusterGuard : Bool :=
  let declarations : List (Decl Nat) :=
    [.function
      { name := "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .decl (.comb [.one, .named "S"]) "g" (.const 7),
     .name "S" [], .exnDecl "E" (.named "T"),
     .decl .one "h" (.const 9)]
  let rest : List (Decl Nat) := [.decl .one "k" (.const 11)]
  (match globalDeclShapes (declarations ++ rest) with
   | [.comb [.one, .named "S"], .one, .one] => true
   | _ => false) &&
  (match globalDeclShapes
      (globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration) declarations) with
   | [.comb [.one, .named "S"], .one] => true
   | _ => false) &&
  (match globalDeclShapes (globalDeclsFilter globalDeclIsFunction declarations) with
   | [] => true
   | _ => false) &&
  (match globalDeclShapes (globalDeclsFilter globalDeclIsName declarations) with
   | [] => true
   | _ => false) &&
  (match globalDeclShapes (globalDeclsFilter globalDeclIsException declarations) with
   | [] => true
   | _ => false) &&
  (match globalDeclShapes (globalDeclsFilter globalDeclIsGlobal declarations) with
   | [.comb [.one, .named "S"], .one] => true
   | _ => false) &&
  (match globalDeclShapes (globalResortDecls declarations) with
   | [.comb [.one, .named "S"], .one] => true
   | _ => false)

#eval clusterGuard
#guard clusterGuard

/-! Counterpart of Cake's `exceptions_append`
    (`pan_globalsProofScript.sml:2507`), exercised on a mixed fixture. -/
def exceptionEntriesGuard : Bool :=
  let declarations : List (Decl Nat) :=
    [.function
      { name := "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .name "S" [], .exnDecl "E" (.named "T")]
  let rest : List (Decl Nat) := [.exnDecl "F" .one, .decl .one "k" (.const 11)]
  (match exceptionEntries (declarations ++ rest) with
   | [("E", .named "T"), ("F", .one)] => true
   | _ => false) &&
  (match exceptionEntries declarations ++ exceptionEntries rest with
   | [("E", .named "T"), ("F", .one)] => true
   | _ => false)

#eval exceptionEntriesGuard
#guard exceptionEntriesGuard

/-! Counterpart of Cake's `exceptions_FILTER_is_function`
    (`pan_globalsProofScript.sml:2515`), exercised on a mixed fixture. -/
def exceptionEntriesFilterGuard : Bool :=
  let declarations : List (Decl Nat) :=
    [.function
      { name := "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .name "S" [], .exnDecl "E" (.named "T"),
     .decl .one "h" (.const 9)]
  (match exceptionEntries (globalDeclsFilter globalDeclIsFunction declarations) with
   | [] => true
   | _ => false) &&
  (match exceptionEntries
      (globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
        declarations) with
   | [("E", .named "T")] => true
   | _ => false) &&
  (match exceptionEntries (globalDeclsFilter globalDeclIsException declarations) with
   | [("E", .named "T")] => true
   | _ => false) &&
  (match exceptionEntries (globalDeclsFilter globalDeclIsName declarations) with
   | [] => true
   | _ => false) &&
  (match exceptionEntries (globalDeclsFilter globalDeclIsGlobal declarations) with
   | [] => true
   | _ => false)

#eval exceptionEntriesFilterGuard
#guard exceptionEntriesFilterGuard

/-! Counterpart of Cake's `not_is_function` (`pan_globalsProofScript.sml:2527`). -/
def notIsFunctionGuard : Bool :=
  let declarations : List (Decl Nat) :=
    [.function
      { name := "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .name "S" [], .exnDecl "E" (.named "T"), .decl .one "h" (.const 9)]
  declarations.all (fun declaration =>
    (!isName declaration || !globalDeclIsFunction declaration) &&
    (!isDecl declaration || !globalDeclIsFunction declaration) &&
    (!isExnDecl declaration || !globalDeclIsFunction declaration))

#eval notIsFunctionGuard
#guard notIsFunctionGuard

/-! Counterpart of Cake's `decl_distinct` (`pan_globalsProofScript.sml:2535`). -/
def declDistinctGuard : Bool :=
  let declarations : List (Decl Nat) :=
    [.function
      { name := "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .name "S" [], .exnDecl "E" (.named "T"), .decl .one "h" (.const 9)]
  declarations.all (fun declaration =>
    !(isDecl declaration && isName declaration) &&
    !(isDecl declaration && globalDeclIsFunction declaration) &&
    !(isDecl declaration && isExnDecl declaration))

#eval declDistinctGuard
#guard declDistinctGuard

/-! Counterpart of Cake's `functions_filter_nil` (`pan_globalsProofScript.sml:2967`). -/
def functionsFilterNilGuard : Bool :=
  let declarations : List (Decl Nat) :=
    [.function
      { name := "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .name "S" [], .exnDecl "E" (.named "T"), .decl .one "h" (.const 9)]
  (functions (globalDeclsFilter
    (fun declaration => !globalDeclIsFunction declaration) declarations)).isEmpty &&
  (functions (globalDeclsFilter isExnDecl declarations)).isEmpty &&
  (functions (globalDeclsFilter isName declarations)).isEmpty

#eval functionsFilterNilGuard
#guard functionsFilterNilGuard

/-! Counterpart of Cake's `resort_decls_preserve_functions`
    (`pan_globalsProofScript.sml:2055`): resorting declarations leaves the
    function table unchanged. -/
example : True := by
  let declarations : List (Decl Nat) :=
    [.function
      { name := "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .name "S" [], .exnDecl "E" (.named "T"), .decl .one "h" (.const 9)]
  have h := functions_globalResortDecls declarations
  trivial

/-! Counterpart of Cake's `compile_decs_preserve_functions`
    (`pan_globalsProofScript.sml:2062`): compiling declarations preserves the
    function-name table. -/
example : True := by
  let declarations : List (Decl Nat) :=
    [.function
      { name := "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .name "S" [], .exnDecl "E" (.named "T"), .decl .one "h" (.const 9)]
  let context : GlobalPassContext Nat :=
    { globals := [], globalsSize := 0, maxGlobalsSize := 0,
      bytesInWord := 8, fromNat := fun n => n }
  have h := globalCompileDecs_preserve_functions context declarations
  trivial

/-! Counterparts of Cake's `compile_decs_EVERY_is_function`
    (`pan_globalsProofScript.sml:1977`) and `compile_decs_decls_thm` (`:1967`). -/
example : True := by
  let declarations : List (Decl Nat) :=
    [.function
      { name := "f", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .name "S" [], .exnDecl "E" (.named "T"), .decl .one "h" (.const 9)]
  let context : GlobalPassContext Nat :=
    { globals := [], globalsSize := 0, maxGlobalsSize := 0,
      bytesInWord := 8, fromNat := fun n => n }
  have h := globalCompileDecs_functions_all_isFunction context declarations
  trivial

def noFunctionsDecls : List (Decl Nat) :=
  [.name "S" [], .exnDecl "E" (.named "T"), .decl .one "h" (.const 9)]

def functionsEmptyGuard : Bool :=
  ((globalCompileDecs
    { globals := [], globalsSize := 0, maxGlobalsSize := 0,
      bytesInWord := 8, fromNat := fun n => n } noFunctionsDecls).functions).isEmpty

example : True := by
  have h := globalCompileDecs_functions_eq_nil_of_no_functions
    ({ globals := [], globalsSize := 0, maxGlobalsSize := 0,
       bytesInWord := 8, fromNat := fun n => n } : GlobalPassContext Nat)
    noFunctionsDecls (by decide)
  trivial

#eval functionsEmptyGuard
#guard functionsEmptyGuard

/-! Counterparts of the append structure of Cake's `compile_decls_append`
    (`pan_globalsProofScript.sml:1997`). -/
def declsWithGlobals : List (Decl Nat) :=
  [.decl .one "g" (.const 7), .decl .one "h" (.const 9)]

example : True := by
  have h := globalCompileDecls_append
    ({ globals := [], globalsSize := 0, maxGlobalsSize := 0,
       bytesInWord := 8, fromNat := fun n => n } : GlobalPassContext Nat)
    declsWithGlobals []
  trivial

example : True := by
  have h := globalCompileInitializers_append
    ({ globals := [], globalsSize := 0, maxGlobalsSize := 0,
       bytesInWord := 8, fromNat := fun n => n } : GlobalPassContext Nat)
    declsWithGlobals []
  trivial

/-! Counterparts of Cake's `fperm_decs_append` (`pan_globalsProofScript.sml:1663`)
    and `functions_fperm_decs` (`:1701`). -/
example : True := by
  have h := globalRenameDecls_append "main" "entry" declsWithGlobals []
  trivial

example : True := by
  have h := functions_globalRenameDecls "main" "entry" declsWithGlobals
  trivial

def renameDeclsGuard : Bool :=
  (functions (globalRenameDecls "main" "entry"
      ([.function
        { name := "main", inline := false, exported := false, params := [],
          body := .skip, returnShape := .one }] : List (Decl Nat)))).map
    (fun entry => entry.1) == ["entry"]

#eval renameDeclsGuard
#guard renameDeclsGuard

/-! Counterparts of Cake's `fperm_decs_decls` (`pan_globalsProofScript.sml:2023`)
    and `fperm_decs_FILTER_is_function` (`:2032`). -/
example : True := by
  have h := globalRenameDecls_eq_self_of_no_functions "main" "entry"
    noFunctionsDecls (by decide)
  trivial

example : True := by
  have h := globalRenameDecls_filter_function "main" "entry" declsWithGlobals
  trivial

def renameFilterGuard : Bool :=
  let mixed : List (Decl Nat) :=
    [.function
      { name := "main", inline := false, exported := false, params := [],
        body := .skip, returnShape := .one },
     .decl .one "h" (.const 9)]
  let renamed := globalRenameDecls "main" "entry" mixed
  (globalRenameDecls "main" "entry"
      (globalDeclsFilter globalDeclIsFunction mixed)).length ==
    (globalDeclsFilter globalDeclIsFunction renamed).length &&
  globalFunctionNames
      (globalRenameDecls "main" "entry"
        (globalDeclsFilter globalDeclIsFunction mixed)) ==
    globalFunctionNames (globalDeclsFilter globalDeclIsFunction renamed)

#eval renameFilterGuard
#guard renameFilterGuard

/-! Counterparts of Cake's `fperm_name_cancel`/`fperm_name_cong`
    (`pan_globalsProofScript.sml:1622,1629`). -/
example : True := by
  have h := globalRenameFunctionName_cancel "main" "entry" "main"
  have h2 := globalRenameFunctionName_cong "main" "entry" "foo" "foo"
  trivial

def renameNameGuard : Bool :=
  (globalRenameFunctionName "main" "entry"
      (globalRenameFunctionName "main" "entry" "main") == "main") &&
  (globalRenameFunctionName "main" "entry" "other" == "other") &&
  (globalRenameFunctionName "main" "entry" "entry" == "main")

#eval renameNameGuard
#guard renameNameGuard

/-! Counterpart of Cake's `ALL_DISTINCT_fperm_decs`
    (`pan_globalsProofScript.sml:1711`). -/
def renameNodupDecls : List (Decl Nat) :=
  [.function
    { name := "main", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one },
   .function
    { name := "other", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one }]

example : True := by
  have hnodup :
      ((functions renameNodupDecls).map (fun entry => entry.1)).Nodup := by
    decide
  have h := globalRenameDecls_names_nodup "main" "entry" renameNodupDecls hnodup
  trivial

def renameNodupGuard : Bool :=
  let renamed := globalRenameDecls "main" "entry" renameNodupDecls
  decide (((functions renamed).map (fun entry => entry.1)).Nodup) &&
  (((functions renamed).map (fun entry => entry.1)).length == 2)

#eval renameNodupGuard
#guard renameNodupGuard

/-! Counterpart of Cake's `compile_decs_exns_are_exns`
    (`pan_globalsProofScript.sml:2448`). -/
def exceptionsFilterGuard : Bool :=
  let context : GlobalPassContext Nat :=
    { globals := [], globalsSize := 0, maxGlobalsSize := 0, bytesInWord := 8,
      fromNat := fun n => n }
  (globalCompileDecs context noFunctionsDecls).exceptions.length ==
      (globalDeclsFilter globalDeclIsException noFunctionsDecls).length &&
    (globalCompileDecs context noFunctionsDecls).exceptions.length == 1

example : True := by
  let context : GlobalPassContext Nat :=
    { globals := [], globalsSize := 0, maxGlobalsSize := 0, bytesInWord := 8,
      fromNat := fun n => n }
  have h := globalCompileDecs_exceptions_eq_filter context noFunctionsDecls
  trivial

#eval exceptionsFilterGuard
#guard exceptionsFilterGuard

/-! Counterpart of Cake's `EVERY_fperm_decs`
    (`pan_globalsProofScript.sml:2436`). -/
def renameAllGuard : Bool :=
  (globalRenameDecls "main" "entry" renameNodupDecls).all (fun _ => true)

example : True := by
  have h := globalRenameDecls_all_of_predicate "main" "entry"
    (fun _ : Decl Nat => true) renameNodupDecls (by decide) (by decide)
  trivial

#eval renameAllGuard
#guard renameAllGuard

/-! Counterpart of Cake's `compile_decs_FILTER_decs`
    (`pan_globalsProofScript.sml:2822`). -/
def filterDeclsFixture : List (Decl Nat) :=
  [.function
    { name := "f", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one },
   .decl (.comb [.one, .named "S"]) "g" (.const 7),
   .name "S" [], .exnDecl "E" (.named "T"),
   .decl .one "h" (.const 9)]

def filterDeclsGuard : Bool :=
  let context : GlobalPassContext Nat :=
    { globals := [], globalsSize := 0, maxGlobalsSize := 0, bytesInWord := 8,
      fromNat := fun n => n }
  let onlyDecls := globalDeclsFilter isDecl filterDeclsFixture
  let whole := globalCompileDecs context filterDeclsFixture
  let filtered := globalCompileDecs context onlyDecls
  (filtered.initializers.length == whole.initializers.length) &&
    filtered.functions.isEmpty && filtered.exceptions.isEmpty &&
    (globalCollect context onlyDecls).globals.length ==
      (globalCollect context filterDeclsFixture).globals.length

example : True := by
  let context : GlobalPassContext Nat :=
    { globals := [], globalsSize := 0, maxGlobalsSize := 0, bytesInWord := 8,
      fromNat := fun n => n }
  have h := globalCompileDecs_filter_isDecl context filterDeclsFixture
  trivial

#eval filterDeclsGuard
#guard filterDeclsGuard

/-! Counterpart of Cake's `FILTER_decs_fperm_decs`
    (`pan_globalsProofScript.sml:2832`). -/
def renameFilterNotFunctionGuard : Bool :=
  (globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
      (globalRenameDecls "main" "entry" filterDeclsFixture)).length ==
    (globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
      filterDeclsFixture).length

example : True := by
  have h :=
    globalRenameDecls_filter_not_function "main" "entry" filterDeclsFixture
  trivial

#eval renameFilterNotFunctionGuard
#guard renameFilterNotFunctionGuard

/-! Counterpart of Cake's `compile_decs_EVERY`
    (`pan_globalsProofScript.sml:1986`). -/
example : True := by
  let context : GlobalPassContext Nat :=
    { globals := [], globalsSize := 0, maxGlobalsSize := 0, bytesInWord := 8,
      fromNat := fun n => n }
  have h := globalCompileDecs_functions_all_of_predicate context
    filterDeclsFixture globalDeclIsFunction (by decide)
  trivial

def functionsEveryGuard : Bool :=
  let context : GlobalPassContext Nat :=
    { globals := [], globalsSize := 0, maxGlobalsSize := 0, bytesInWord := 8,
      fromNat := fun n => n }
  (globalCompileDecs context filterDeclsFixture).functions.all
    globalDeclIsFunction

#eval functionsEveryGuard
#guard functionsEveryGuard

/-! Counterpart of Cake's `compile_decs_functions_thm`
    (`pan_globalsProofScript.sml:1967`). -/
def compileDeclF : Decl Nat :=
  .function
    { name := "f", inline := false, exported := false, params := [],
      body := (.skip : Prog Nat), returnShape := .one }

def compileDeclG : Decl Nat :=
  .function
    { name := "g", inline := false, exported := false, params := [],
      body := (.tick : Prog Nat), returnShape := .one }

def functionsOnlyCompileDecls : List (Decl Nat) :=
  [compileDeclF, compileDeclG]

def compileDecsFunctionsGuard : Bool :=
  let context : GlobalPassContext Nat :=
    { globals := [], globalsSize := 0, maxGlobalsSize := 0, bytesInWord := 8,
      fromNat := fun n => n }
  (globalCompileDecs context functionsOnlyCompileDecls).initializers.isEmpty &&
    (globalCompileDecs context functionsOnlyCompileDecls).exceptions.isEmpty &&
    (globalCompileDecs context functionsOnlyCompileDecls).functions.length ==
      functionsOnlyCompileDecls.length

example : True := by
  let context : GlobalPassContext Nat :=
    { globals := [], globalsSize := 0, maxGlobalsSize := 0, bytesInWord := 8,
      fromNat := fun n => n }
  have hall : functionsOnlyCompileDecls.all globalDeclIsFunction = true := by
    simp [functionsOnlyCompileDecls, compileDeclF, compileDeclG,
      globalDeclIsFunction]
  have h :=
    globalCompileDecs_functions_thm context functionsOnlyCompileDecls hall
  trivial

#eval compileDecsFunctionsGuard
#guard compileDecsFunctionsGuard

/-! Cake's `dec_shapes_compile_prog` and `function_names_compile_prog`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:241`, `:248`). -/

theorem globalDeclShapes_panSimpDecls_fixture :
    globalDeclShapes (panSimpDecls filterDeclsFixture) =
      globalDeclShapes filterDeclsFixture :=
  globalDeclShapes_panSimpDecls filterDeclsFixture

theorem functions_names_panSimpDecls_fixture :
    (functions (panSimpDecls filterDeclsFixture)).map Prod.fst =
      (functions filterDeclsFixture).map Prod.fst :=
  functions_names_panSimpDecls filterDeclsFixture

def panSimpShapesGuard : Bool :=
  (globalDeclShapes (panSimpDecls filterDeclsFixture)).length ==
      (globalDeclShapes filterDeclsFixture).length &&
    ((functions (panSimpDecls filterDeclsFixture)).map Prod.fst).length ==
      ((functions filterDeclsFixture).map Prod.fst).length

#eval panSimpShapesGuard
#guard panSimpShapesGuard

/-! Cake's `no_names_compile_prog`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:318`). -/

def noNameDecls : List (Decl Nat) :=
  [compileDeclF, .decl .one "g" (.const 7), .exnDecl "E" .one]

theorem panSimpDecls_all_not_name_fixture :
    (panSimpDecls noNameDecls).all
      (fun declaration => !isName declaration) = true :=
  panSimpDecls_all_not_name noNameDecls
    (by simp [noNameDecls, compileDeclF, isName])

def panSimpNoNamesGuard : Bool :=
  (panSimpDecls noNameDecls).all (fun declaration => !isName declaration) &&
    !(panSimpDecls (noNameDecls ++ [.name "S" []])).all
      (fun declaration => !isName declaration)

#eval panSimpNoNamesGuard
#guard panSimpNoNamesGuard

/-! Cake's `size_of_eids_structs_compile_eq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:305`). -/

def structEidsDecls : List (Decl Nat) :=
  [.exnDecl "E" .one, .decl .one "g" (.const 1), .name "S" []]

theorem sizeOfEids_structCompileTop_fixture :
    sizeOfEids (structCompileTop structEidsDecls) =
      sizeOfEids structEidsDecls :=
  sizeOfEids_structCompileTop structEidsDecls

def structEidsGuard : Bool :=
  sizeOfEids (structCompileTop structEidsDecls) == 1 &&
    sizeOfEids structEidsDecls == 1

#eval structEidsGuard
#guard structEidsGuard

/-! Cake's `size_of_eids_compile_top`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:364`). -/

def eidsTopDecls : List (Decl Nat) := [compileDeclF, .exnDecl "E" .one]

example (compiled : List (Decl Nat))
    (hcompile : globalCompileTopForStartSome 8 id eidsTopDecls "f" = some compiled) :
    sizeOfEids compiled = sizeOfEids eidsTopDecls :=
  globalCompileTopForStart_sizeOfEids 8 id eidsTopDecls "f" compiled hcompile

/-! Cake's `functions_compile_decs_exns`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:519`). -/

example (context : GlobalPassContext Nat) (code : List (Decl Nat)) :
    functions (globalCompileDecs context code).exceptions = [] :=
  globalCompileDecs_exceptions_functions context code

def exceptionsFunctionsGuard : Bool :=
  (functions (globalDeclsFilter globalDeclIsException eidsTopDecls)).length == 0

#eval exceptionsFunctionsGuard
#guard exceptionsFunctionsGuard

end Flapjack.Test.PanGlobalsDecShapesParity
