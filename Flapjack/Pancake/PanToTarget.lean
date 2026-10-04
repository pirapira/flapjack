import Flapjack.Pancake.PanToWord
import Flapjack.Compiler.Backend.Backend
import Flapjack.Compiler.Backend.WordToWord.Compile
import Flapjack.Compiler.Backend.WordToStack.StubNames
import Flapjack.Compiler.Backend.StackAlloc.StubNames
import Flapjack.Compiler.Backend.StackRemove.StubNames
import Flapjack.Basis.Pure.MlList
set_option autoImplicit false
namespace Flapjack.Pancake.PanToTarget
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend

/-- Original exported function names, in source order and with duplicates
retained. Only Function declarations with the export flag set contribute.
The positive word qualifier applies to the reviewed native declaration family;
identifiers remain byte-backed MlStrings, not String replacements. -/
@[hol "cakeml/pancake/pan_to_targetScript.sml" "exports_def"
  (words_as_type_indexed_bitvec)]
def exportsHOL {width : Nat} [NeZero width] : List (DeclHOL width) → List MlS
  | [] => []
  | .function entry :: rest =>
    if entry.exported then entry.name :: exportsHOL rest else exportsHOL rest
  | _ :: rest => exportsHOL rest

/-- Flapjack infrastructure factoring the original compile_prog main-ordering
let binding; it has no independent HOL declaration. Native List.span with the
complement of the main predicate implements rich_list$SPLITP. Keep the literal
([],ys) first branch: an empty input remains empty, while a nonempty list with
no main receives the original zero-returning default main. -/
def mainFirstHOL {width : Nat} [NeZero width] (program : List (DeclHOL width)) : List (DeclHOL width) :=
  let (before, after) := program.span (fun declaration =>
    match declaration with
    | .function entry => decide (entry.name ≠ ofString "main")
    | _ => true)
  match before, after with
  | [], rest => rest
  | before, [] => .function
      { name := ofString "main", inline := false, exported := false, params := [],
        body := .return (.const 0), returnShape := .one } :: before
  | before, main :: rest => main :: before ++ rest

/-- Full original pan_to_target compile_prog: main ordering/default, actual
PanToWord and WordToWord passes, returned colouring-oracle update, native
mllist sort/ZIP symbol table, left-biased stub-name union, original-program
exports, and complete native backend from_word. HOL listTheory.ZIP_def has
both arbitrary-list empty clauses, so native List.zip also preserves unequal
lengths; no extra equal-length hypothesis or arbitrary truncation is added.

This is the reviewed source-shaped definition, separate from the executed
production pipeline. Its delivery does not establish production routing or
the final machine-semantics compiler theorem. -/
@[hol "cakeml/pancake/pan_to_targetScript.sml" "compile_prog_def"
  (words_as_type_indexed_bitvec)]
noncomputable def compileProgHOL {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (config : Backend.Config)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) × Backend.Config) :=
  let prog1 := mainFirstHOL program
  let prog2 := panToWordCompileProgHOL asmConf.isa prog1
  let (col, prog3) := WordToWord.compile config.wordToWordConf asmConf prog2
  let config := { config with wordToWordConf := { config.wordToWordConf with colOracle := col } }
  let names := sptFromAList ((Flapjack.Basis.Pure.MlList.sort
    (fun a b : Nat => decide (a < b)) (prog2.map Prod.fst)).zip
    (ofString "generated_main" :: (functionsHOL prog1).map Prod.fst))
  let names := sptUnion (sptFromAList
    (WordToStack.stubNames () ++ StackAlloc.stubNames () ++ StackRemove.stubNames ())) names
  let config := { config with exported := exportsHOL program }
  Backend.fromWord asmConf config names prog3
end Flapjack.Pancake.PanToTarget
