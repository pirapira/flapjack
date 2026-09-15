import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.RiscV.CakeRegAlloc
import Flapjack.RiscV.Allocator
import Flapjack.CrepToLoopOptimise

namespace Flapjack.ZProbe

open Flapjack.RiscV.CakeRegAlloc
open Flapjack.RiscV
open Flapjack

def source : String :=
  "fun 1 id (x) { return x; }\nfun 1 main() { var 1 t = id(5); return 1; }"

def checked : Option (List (Decl (RiscV.Word 64))) :=
  (Flapjack.Parser.parseTopDecs (fun v => BitVec.ofInt 64 v) source).toOption

def entry : Option (FlapjackPipelineResult (RiscV.Word 64)) :=
  checked.bind (fun declarations =>
    Flapjack.compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
      (fun v => BitVec.ofInt 64 v) "main"
      (panTargetDeclarationsWithDefaultMain declarations))

def src_p1 : String :=
  "fun 1 id (x) { return x; }\nfun 1 main() { var 1 t = id(5); return 1; }\n"
def src_p9 : String :=
  "struct S { 1 f, 1 g }\nfun S mks (1 a, 1 b) { return S <f = a, g = b>; }\nfun 1 id (1 a) { return a; }\nfun 1 main() { var S s = mks(1,2); var 1 t = id(5); return s.f + s.g; }\n"
def src_bc : String :=
  "fun 1 f () {\n    var 1 x = f();\n    var 1 x = f();\n    return 1;\n  }\n\nfun 1 main() { return 0; }\n"
def src_bm_min2 : String :=
  "struct S { 1 f1, 1 f2 }\nfun S mks(1 a, 1 b) { return S <f1 = a, f2 = b>; }\nfun 1 id(1 a) { return a; }\nfun 1 main() {\n  var S s = mks(1, 2);\n  var 1 t = id(5);\n  return s.f1 + s.f2 + t;\n}\n"
def src_live1 : String :=
  "struct S { 1 f1, 1 f2 }\nfun S mks(1 a, 1 b) { return S <f1 = a, f2 = b>; }\nfun 1 id(1 a) { return a; }\nfun 1 main() {\n  var S s1 = mks(1, 2);\n  var 1 t = id(7);\n  return s1.f1 + t;\n}\n"
def src_live3 : String :=
  "struct S { 1 f1, 1 f2 }\nfun S mks(1 a, 1 b) { return S <f1 = a, f2 = b>; }\nfun 1 id(1 a) { return a; }\nfun 1 main() {\n  var S s1 = mks(1, 2);\n  var S s2 = mks(3, 4);\n  var S s3 = mks(5, 6);\n  var 1 t = id(7);\n  return s1.f1 + s2.f2 + s3.f1 + t;\n}\n"
def src_wide : String :=
  "struct S { 1 a, 1 b, 1 c, 1 d, 1 e, 1 f }\nfun S mks(1 x) { return S <a=x,b=x,c=x,d=x,e=x,f=x>; }\nfun 1 id(1 a) { return a; }\nfun 1 main() {\n  var S s = mks(1);\n  var 1 t = id(2);\n  return s.a + s.f + t;\n}\n"
def src_bitmap_calls : String :=
  "fun 1 f () {\n    var 1 x = f();\n    var 1 x = f();\n    return 1;\n  }\n\nfun 1 main() { return 0; }\n"

def pipelineLoopFunctionsOptAux (architecture : RiscV.Architecture)
    (functionInfos : InfoMap (Nat × Nat)) :
    Nat → List (CompiledFunction (RiscV.Word 64)) →
    List (Nat × List Nat × Flapjack.LoopProg (RiscV.Word 64))
  | _, [] => []
  | label, function :: functions =>
      let context : LoopContext (RiscV.Word 64) :=
        { vars := []
          functions := functionInfos
          maxVar := function.params.length
          target := architecture }
      (label, function.params,
        oCompile context function.params function.body) ::
        pipelineLoopFunctionsOptAux architecture functionInfos (label + 1) functions

def optLoopFunctions :
    List (Nat × List Nat × Flapjack.LoopProg (RiscV.Word 64)) :=
  match entry with
  | some pipeline =>
      pipelineLoopFunctionsOptAux .rv64i
        (pipelineFunctionInfos stackFunctionFirstLabel pipeline.crepe)
        stackFunctionFirstLabel pipeline.crepe
  | none => []


def countsFor (src : String) : List Nat :=
  match (Flapjack.Parser.parseTopDecs (fun v => BitVec.ofInt 64 v) src).toOption with
  | none => []
  | some declarations =>
      match Flapjack.compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
          (fun v => BitVec.ofInt 64 v) "main"
          (panTargetDeclarationsWithDefaultMain declarations) with
      | none => []
      | some pipeline =>
          (pipelineLoopFunctionsOptAux .rv64i
            (pipelineFunctionInfos stackFunctionFirstLabel pipeline.crepe)
            stackFunctionFirstLabel pipeline.crepe).map (fun f =>
            let label := f.1
            let params := f.2.1
            let body := f.2.2
            let wordParameters := wordSsaAbiParameters params.length
            let slots := loopAccVars body params
            let context : WordContext :=
              { vars := slots.map (fun name => (name, name + 2)) }
            let wordBody := wordProgDCE (loopToWordProg context body)
            cakeWordStackVarCount label wordParameters
              wordAllocatableRegisters.length wordBody)

#eval countsFor src_p1
#eval countsFor src_p9
#eval countsFor src_bc
#eval countsFor src_bm_min2
#eval countsFor src_live1
#eval countsFor src_live3
#eval countsFor src_wide
#eval countsFor src_bitmap_calls

-- p9 deep dive: dump each function's optimized loop body and SSA
def p9Loop : List (Nat × List Nat × Flapjack.LoopProg (RiscV.Word 64)) :=
  match (Flapjack.Parser.parseTopDecs (fun v => BitVec.ofInt 64 v) src_p9).toOption with
  | none => []
  | some declarations =>
      match Flapjack.compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
          (fun v => BitVec.ofInt 64 v) "main"
          (panTargetDeclarationsWithDefaultMain declarations) with
      | none => []
      | some pipeline =>
          pipelineLoopFunctionsOptAux .rv64i
            (pipelineFunctionInfos stackFunctionFirstLabel pipeline.crepe)
            stackFunctionFirstLabel pipeline.crepe

def p9Word (f : Nat × List Nat × Flapjack.LoopProg (RiscV.Word 64)) :
    Nat × List Nat × WordProg (RiscV.Word 64) :=
  let label := f.1
  let params := f.2.1
  let body := f.2.2
  let wordParameters := wordSsaAbiParameters params.length
  let slots := loopAccVars body params
  let context : WordContext :=
    { vars := slots.map (fun name => (name, name + 2)) }
  (label, params, wordProgDCE (loopToWordProg context body))

#eval p9Loop.map (fun f => (f.1, f.2.1.length, repr (p9Word f).2.2))
#eval p9Loop.map (fun f =>
  let w := p9Word f
  let ssa := (wordFullSsaCcTrans (wordSsaAbiParameters (w.2.1).length).length w.2.2).2.2
  (w.1, repr ssa))
-- wide allocation failure probe
def wideLoop : List (Nat × List Nat × Flapjack.LoopProg (RiscV.Word 64)) :=
  match (Flapjack.Parser.parseTopDecs (fun v => BitVec.ofInt 64 v) src_wide).toOption with
  | none => []
  | some declarations =>
      match Flapjack.compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
          (fun v => BitVec.ofInt 64 v) "main"
          (panTargetDeclarationsWithDefaultMain declarations) with
      | none => []
      | some pipeline =>
          pipelineLoopFunctionsOptAux .rv64i
            (pipelineFunctionInfos stackFunctionFirstLabel pipeline.crepe)
            stackFunctionFirstLabel pipeline.crepe

#eval wideLoop.map (fun f =>
  let label := f.1
  let params := f.2.1
  let body := f.2.2
  let wordParameters := wordSsaAbiParameters params.length
  let slots := loopAccVars body params
  let context : WordContext :=
    { vars := slots.map (fun name => (name, name + 2)) }
  let wordBody := wordProgDCE (loopToWordProg context body)
  let flat := wordProgDCE (wordFlattenProgramFrom
    (LoopToWord.loopToWordCompFunc label params body))
  (label,
   (wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesRiscV
     wordParameters wordBody).isSome,
   (wordAllocateSsaFunctionWithEntryAndClashTreeWithSpillsAndPreferencesRiscV
     wordParameters flat).isSome,
   repr body))

#eval wideLoop.map (fun f =>
  let label := f.1
  let params := f.2.1
  let body := f.2.2
  let wordParameters := wordSsaAbiParameters params.length
  let slots := loopAccVars body params
  let context : WordContext :=
    { vars := slots.map (fun name => (name, name + 2)) }
  let wordBody := wordProgDCE (loopToWordProg context body)
  (label, repr wordBody))

-- wide: which allocation stage fails
#eval wideLoop.map (fun f =>
  let label := f.1
  let params := f.2.1
  let body := f.2.2
  let wordParameters := wordSsaAbiParameters params.length
  let slots := loopAccVars body params
  let context : WordContext :=
    { vars := slots.map (fun name => (name, name + 2)) }
  let wordBody := wordProgDCE (loopToWordProg context body)
  let flat := wordProgDCE (wordFlattenProgramFrom
    (LoopToWord.loopToWordCompFunc label params body))
  let stages (program : Flapjack.WordProg _) : Nat × Nat × Nat :=
    let (state, renamedParameters, program) :=
      wordSsaRenameFunctionWithEntry wordParameters program
    let tree := wordClashTree program []
    let (liveIn, edges) := wordClashTreeAnalyze tree []
    let edges := edges ++ wordProgSpecialConflictEdges program
    let preferences := wordProgPreferenceEdges program
    let slots2 :=
      renamedParameters ++ wordProgVariables program ++ liveIn ++
        edges.flatMap (fun edge => [edge.1, edge.2])
    let alloc :=
      wordAllocateVarsWithFixedLocations slots2 edges preferences
        (wordRiscVFixedSourceLocations
          (wordPhysicalFixedSources wordParameters program))
    match alloc with
    | none => (0, 0, 0)
    | some allocation =>
      (1,
       if wordProgSpecialLocationsSafe allocation.locations program then 1 else 0,
       if wordSpillClashTreeChecked tree allocation.locations then 1 else 0)
  (label, stages wordBody, stages flat))

-- wide: RAW (pre-optimise) bodies allocation stages
def wideRawLoop : List (Nat × List Nat × Flapjack.LoopProg (RiscV.Word 64)) :=
  match (Flapjack.Parser.parseTopDecs (fun v => BitVec.ofInt 64 v) src_wide).toOption with
  | none => []
  | some declarations =>
      match Flapjack.compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
          (fun v => BitVec.ofInt 64 v) "main"
          (panTargetDeclarationsWithDefaultMain declarations) with
      | none => []
      | some pipeline =>
          (Flapjack.pipelineLoopFunctionsAux .rv64i
            (pipelineFunctionInfos stackFunctionFirstLabel pipeline.crepe)
            stackFunctionFirstLabel pipeline.crepe)

#eval wideRawLoop.map (fun f =>
  let label := f.1
  let params := f.2.1
  let body := f.2.2
  let wordParameters := wordSsaAbiParameters params.length
  let slots := loopAccVars body params
  let context : WordContext :=
    { vars := slots.map (fun name => (name, name + 2)) }
  let wordBody := wordProgDCE (loopToWordProg context body)
  let flat := wordProgDCE (wordFlattenProgramFrom
    (LoopToWord.loopToWordCompFunc label params body))
  let stages (program : Flapjack.WordProg _) : Nat × Nat × Nat :=
    let (state, renamedParameters, program) :=
      wordSsaRenameFunctionWithEntry wordParameters program
    let tree := wordClashTree program []
    let (liveIn, edges) := wordClashTreeAnalyze tree []
    let edges := edges ++ wordProgSpecialConflictEdges program
    let preferences := wordProgPreferenceEdges program
    let slots2 :=
      renamedParameters ++ wordProgVariables program ++ liveIn ++
        edges.flatMap (fun edge => [edge.1, edge.2])
    let alloc :=
      wordAllocateVarsWithFixedLocations slots2 edges preferences
        (wordRiscVFixedSourceLocations
          (wordPhysicalFixedSources wordParameters program))
    match alloc with
    | none => (0, 0, 0)
    | some allocation =>
      (1,
       if wordProgSpecialLocationsSafe allocation.locations program then 1 else 0,
       if wordSpillClashTreeChecked tree allocation.locations then 1 else 0)
  (label, stages wordBody, stages flat, repr body))

-- wide: TRUE raw (pre-optimise) loopCompileProg bodies
def wideTrueRawLoop : List (Nat × List Nat × Flapjack.LoopProg (RiscV.Word 64)) :=
  match (Flapjack.Parser.parseTopDecs (fun v => BitVec.ofInt 64 v) src_wide).toOption with
  | none => []
  | some declarations =>
      match Flapjack.compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
          (fun v => BitVec.ofInt 64 v) "main"
          (panTargetDeclarationsWithDefaultMain declarations) with
      | none => []
      | some pipeline =>
          let infos := pipelineFunctionInfos stackFunctionFirstLabel pipeline.crepe
          let rec aux : Nat → List (Flapjack.CompiledFunction (RiscV.Word 64)) →
              List (Nat × List Nat × Flapjack.LoopProg (RiscV.Word 64))
            | _, [] => []
            | label, function :: functions =>
                let context : Flapjack.LoopContext (RiscV.Word 64) :=
                  { vars := []
                    functions := infos
                    maxVar := function.params.length
                    target := .rv64i }
                (label, function.params,
                  Flapjack.loopCompileProg context [] function.body) ::
                  aux (label + 1) functions
          aux stackFunctionFirstLabel pipeline.crepe

#eval wideTrueRawLoop.map (fun f =>
  let label := f.1
  let params := f.2.1
  let body := f.2.2
  let wordParameters := wordSsaAbiParameters params.length
  let flat := wordProgDCE (wordFlattenProgramFrom
    (LoopToWord.loopToWordCompFunc label params body))
  let stages (program : Flapjack.WordProg _) : Nat × Nat × Nat :=
    let (state, renamedParameters, program) :=
      wordSsaRenameFunctionWithEntry wordParameters program
    let tree := wordClashTree program []
    let (liveIn, edges) := wordClashTreeAnalyze tree []
    let edges := edges ++ wordProgSpecialConflictEdges program
    let preferences := wordProgPreferenceEdges program
    let slots2 :=
      renamedParameters ++ wordProgVariables program ++ liveIn ++
        edges.flatMap (fun edge => [edge.1, edge.2])
    let alloc :=
      wordAllocateVarsWithFixedLocations slots2 edges preferences
        (wordRiscVFixedSourceLocations
          (wordPhysicalFixedSources wordParameters program))
    match alloc with
    | none => (0, 0, 0)
    | some allocation =>
      (1,
       if wordProgSpecialLocationsSafe allocation.locations program then 1 else 0,
       if wordSpillClashTreeChecked tree allocation.locations then 1 else 0)
  (label, stages flat, repr (wordProgDCE (loopToWordProg
    { vars := (loopAccVars body params).map (fun name => (name, name + 2)) } body))))


namespace Flapjack.ZProbe.CF
def zCalleeBody : Prog (RiscV.Word 64) :=
  .raise "E" (.const (BitVec.ofNat 64 3))

def zDecls : List (Decl (RiscV.Word 64)) :=
  [.exnDecl "E" .one,
   .function
     { name := "raise", inline := false, exported := false, params := [],
       body := zCalleeBody, returnShape := .one },
   .function
     { name := "main", inline := false, exported := true, params := [],
       body := .dec "exception" .one (.const (BitVec.ofNat 64 0))
         (.call (some (none, some ("E", "exception",
           (.seq
             (.extCall "inc" (.var .local "exception")
               (.const (BitVec.ofNat 64 0)) (.const (BitVec.ofNat 64 0))
               (.const (BitVec.ofNat 64 0)))
             (.return (.var .local "exception")))))) "raise" []),
       returnShape := .one }]
def zPipeline : Option (FlapjackPipelineResult (RiscV.Word 64)) :=
  Flapjack.compileFlapjackEntry .rv64i (BitVec.ofNat 64 8) (fun v => BitVec.ofInt 64 v) "main"
    (Flapjack.panTargetDeclarationsWithDefaultMain zDecls)
def zLoopFns : List (Nat × List Nat × LoopProg (RiscV.Word 64)) :=
  match zPipeline with
  | some p => Flapjack.pipelineLoopFunctions .rv64i stackFunctionFirstLabel p.crepe
  | none => []
def zInfos : InfoMap (Nat × Nat) :=
  match zPipeline with
  | some p => pipelineFunctionInfos stackFunctionFirstLabel p.crepe
  | none => []
def zCtx : LoopContext (RiscV.Word 64) :=
  { vars := [], functions := zInfos, maxVar := 0, target := .rv64i }
def zMainCrepe : Option (CompiledFunction (RiscV.Word 64)) :=
  match zPipeline with
  | some p => p.crepe.find? (fun f => f.name == "main'")
  | none => none
def zStockMain : LoopProg (RiscV.Word 64) :=
  match zMainCrepe with
  | some f => loopCompileProg zCtx [] f.body
  | none => .skip
#eval s!"OLOOP: {repr (zLoopFns.map (fun (l, ps, b) => (l, ps.length, b)))}"
#eval s!"SLOOP: {repr zStockMain}"

-- SSA word dumps: handler function region, oCompile'd vs stock
def zWordFns : List (Nat × List Nat × WordProg (RiscV.Word 64)) :=
  zLoopFns.map (fun (l, ps, b) =>
    (l, ps, wordProgDCE (LoopToWord.loopToWordCompFunc l ps b)))
def zSsaDump : String :=
  String.intercalate "\n" (zWordFns.map (fun (l, ps, b) =>
    s!"FN {l}: {repr ((wordFullSsaCcTrans ps.length b).2.2)}"))
#eval s!"WSSA-OPT: {zSsaDump}"
def zStockWord : WordProg (RiscV.Word 64) :=
  wordProgDCE (LoopToWord.loopToWordCompFunc 4 [] zStockMain)
#eval s!"WSSA-STOCK: {repr ((wordFullSsaCcTrans 0 zStockWord).2.2)}"

end Flapjack.ZProbe.CF



end Flapjack.ZProbe

namespace Flapjack.ZProbe.G25
open Flapjack
open Flapjack.RiscV

def zCase : String := "fun 1 add1(1 a, 1 b) { return a + b; }\nfun 1 sub1(1 a) { return a - 1; }\nfun {1,1} pair(1 a, 1 b) { return <a, b>; }\nstruct S { 1 f1, 1 f2 }\nfun S mks(1 a, 1 b) { return S <f1 = a, f2 = b>; }\nexception E : 1;\nfun 1 main() {\n  var 1 x = 255;\n  var 1 y571 = (ld8 1000 + 24);\n  var 1 y303 = add1((lds 1 (0)), (lds 1 ((1000 + 4))));\n  var S s470 = mks((lds 1 (((1016 + 16) + 16))), (lds 1 (1000)));\n  while (x > 0) {\n    st (((1024 + 1000) + 4)), s470.f1;\n    if (x >= (ld8 1000 + 24)) {\n      y303 = (ld8 1016);\n      x = (1000 #>> 1);\n    } else {\n      try\n        y571 = add1((s470.f1 #>> 7), y303)\n      catch E => y303 {\n          x = s470.f1;\n          y303 = (lds 1 (1024));\n      }\n      x = y303;\n    }\n      continue;\n  }\n  y571 = add1((ld8 (0 + 4)), (lds 1 (1000)));\n  if (y571 > 1000) {\n    if (((lds 1 (1000)) #>> 7) < 3) {\n      y571 = add1(((lds 1 (1000)) << (7 * 0)), 1);\n    } else {\n      !ldw y571, ((1000 + 24 + 4));\n    }\n    y303 = 3;\n  } else {\n    x = 255;\n  }\n  !ldw y303, (1016);\n  y571 = (1000 & y571);\n  st ((((1000 + 24 + 8) + 4) + 8)), 1;\n  return ((3 << 1000) #>> 2);\n}\n"

#eval countsFor zCase

def zBodies : String :=
  match (Flapjack.Parser.parseTopDecs (fun v => BitVec.ofInt 64 v) zCase).toOption with
  | none => "PARSE FAIL"
  | some declarations =>
      match Flapjack.compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
          (fun v => BitVec.ofInt 64 v) "main"
          (panTargetDeclarationsWithDefaultMain declarations) with
      | none => "COMPILE FAIL"
      | some pipeline =>
          String.intercalate "\nFN: "
            ((pipelineLoopFunctionsOptAux .rv64i
              (pipelineFunctionInfos stackFunctionFirstLabel pipeline.crepe)
              stackFunctionFirstLabel pipeline.crepe).map fun f =>
              toString (repr f.2.2))

#eval zBodies

def g25Pipeline : Option (FlapjackPipelineResult (RiscV.Word 64)) :=
  match (Flapjack.Parser.parseTopDecs (fun v => BitVec.ofInt 64 v) zCase).toOption with
  | none => none
  | some declarations =>
      Flapjack.compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
        (fun v => BitVec.ofInt 64 v) "main"
        (panTargetDeclarationsWithDefaultMain declarations)
def g25MainCrepe : Option (CompiledFunction (RiscV.Word 64)) :=
  match g25Pipeline with
  | some p => p.crepe.find? (fun f => f.name == "main'")
  | none => none
def g25Ctx : LoopContext (RiscV.Word 64) :=
  { vars := [],
    functions := match g25Pipeline with
      | some p => pipelineFunctionInfos stackFunctionFirstLabel p.crepe
      | none => [],
    maxVar := 0, target := .rv64i }
def g25StockMain : LoopProg (RiscV.Word 64) :=
  match g25MainCrepe with
  | some f => loopCompileProg g25Ctx [] f.body
  | none => .skip
#eval s!"G25-SLOOP: {repr g25StockMain}"

namespace Flapjack.ZProbe.RB
open Flapjack
open Flapjack.RiscV.CakeRegAlloc
open Flapjack.RiscV
open Flapjack

def findLoop : LoopProg (RiscV.Word 64) -> Option (LoopProg (RiscV.Word 64))
  | .seq (.loop li b lo) _ => some (.loop li b lo)
  | .seq first second => (findLoop first).orElse (fun _ => findLoop second)
  | .loop li b lo => some (.loop li b lo)
  | _ => none
termination_by p => sizeOf p

def g25Loop : Option (LoopProg (RiscV.Word 64)) :=
  match g25StockMain with
  | .loop li b lo => some (.loop li b lo)
  | p => findLoop p

-- shrink JUST the loop node with production-like downward live [2,3]
def shrunk : Option (LoopProg (RiscV.Word 64) × List Nat) :=
  g25Loop.map (fun p => loopShrink [] p [2, 3])

#eval! shrunk.map (fun r => s!"RB-LOOPANN: {r.2}")
#eval! shrunk.map (fun r => s!"RB-RESULT: {repr r.1}")

-- MINIMAL while-shape: guard compute + ite(then=continue, else=break)
def miniBody : LoopProg (RiscV.Word 64) :=
  LoopProg.seq
    (LoopProg.assign 9 (LoopExp.var 7))
    (LoopProg.seq
      (LoopProg.ite (Cmp.notEqual) 9 (RegImm.imm 0)
        (LoopProg.continue 0)
        (LoopProg.break 0)
        [6, 5, 4, 3, 1])
      (LoopProg.skip))

def miniLoop : LoopProg (RiscV.Word 64) :=
  .loop [6, 5, 4, 3, 1] miniBody [6, 5, 4, 3, 1]

def miniShrunk : LoopProg (RiscV.Word 64) × List Nat := loopShrink [] miniLoop [2, 3]
#eval! s!"MINI-ANN: {miniShrunk.2}"
#eval! s!"MINI-RESULT: {repr miniShrunk.1}"


-- MINI2: inner two-assign ite inside then-branch before continue
def mini2Body : LoopProg (RiscV.Word 64) :=
  LoopProg.seq (LoopProg.assign 9 (LoopExp.var 7))
    (LoopProg.seq
      (LoopProg.ite (Cmp.notEqual) 9 (RegImm.imm 0)
        (LoopProg.seq
          (LoopProg.ite (Cmp.notLess) 8 (RegImm.reg 9)
            (LoopProg.assign 10 (LoopExp.const 1))
            (LoopProg.assign 10 (LoopExp.const 0))
            [8, 9])
          (LoopProg.seq (LoopProg.assign 9 (LoopExp.var 10)) (LoopProg.continue 0)))
        (LoopProg.break 0)
        [6, 5, 4, 3, 1])
      LoopProg.skip)

def mini2Loop : LoopProg (RiscV.Word 64) :=
  LoopProg.loop [6, 5, 4, 3, 1] mini2Body [6, 5, 4, 3, 1]

def mini2Shrunk : LoopProg (RiscV.Word 64) × List Nat := loopShrink [] mini2Loop [2, 3]
#eval! s!"MINI2-ANN: {mini2Shrunk.2}"

-- MINI3: try-call with handler inside then-branch
def mini3Body : LoopProg (RiscV.Word 64) :=
  LoopProg.seq (LoopProg.assign 9 (LoopExp.var 7))
    (LoopProg.seq
      (LoopProg.ite (Cmp.notEqual) 9 (RegImm.imm 0)
        (LoopProg.seq
          (LoopProg.assign 7 (LoopExp.shift .ror (LoopExp.var 4) (LoopExp.const 7)))
          (LoopProg.seq
            (LoopProg.assign 8 (LoopExp.var 3))
            (LoopProg.seq
              (LoopProg.call (some ([2], [6, 5, 4, 3, 1])) (some 5) [7, 8]
                (some (7,
                  LoopProg.ite (Cmp.notEqual) 7 (RegImm.imm 1)
                    (LoopProg.raise 7)
                    (LoopProg.seq LoopProg.tick (LoopProg.assign 3 (LoopExp.load (LoopExp.var 1)))) [6, 5, 4, 3, 1],
                  LoopProg.skip,
                  [6, 5, 4, 3, 1])))
              (LoopProg.assign 1 (LoopExp.var 3)))))
        (LoopProg.break 0)
        [6, 5, 4, 3, 1])
      LoopProg.skip)

def mini3Loop : LoopProg (RiscV.Word 64) :=
  LoopProg.loop [6, 5, 4, 3, 1] mini3Body [6, 5, 4, 3, 1]

def mini3Shrunk : LoopProg (RiscV.Word 64) × List Nat := loopShrink [] mini3Loop [2, 3]
#eval! s!"MINI3-ANN: {mini3Shrunk.2}"

-- MINI4: mini3 + trailing continue at then-tail (real shape)
def mini4Body : LoopProg (RiscV.Word 64) :=
  LoopProg.seq (LoopProg.assign 9 (LoopExp.var 7))
    (LoopProg.seq
      (LoopProg.ite (Cmp.notEqual) 9 (RegImm.imm 0)
        (LoopProg.seq
          (LoopProg.assign 7 (LoopExp.shift .ror (LoopExp.var 4) (LoopExp.const 7)))
          (LoopProg.seq
            (LoopProg.assign 8 (LoopExp.var 3))
            (LoopProg.seq
              (LoopProg.call (some ([2], [6, 5, 4, 3, 1])) (some 5) [7, 8]
                (some (7,
                  LoopProg.ite (Cmp.notEqual) 7 (RegImm.imm 1)
                    (LoopProg.raise 7)
                    (LoopProg.seq LoopProg.tick (LoopProg.assign 3 (LoopExp.load (LoopExp.var 1)))) [6, 5, 4, 3, 1],
                  LoopProg.skip,
                  [6, 5, 4, 3, 1])))
              (LoopProg.seq (LoopProg.assign 1 (LoopExp.var 3)) (LoopProg.continue 0)))))
        (LoopProg.break 0)
        [6, 5, 4, 3, 1])
      LoopProg.skip)

def mini4Loop : LoopProg (RiscV.Word 64) :=
  LoopProg.loop [6, 5, 4, 3, 1] mini4Body [6, 5, 4, 3, 1]

def mini4Shrunk : LoopProg (RiscV.Word 64) × List Nat := loopShrink [] mini4Loop [2, 3]
#eval! s!"MINI4-ANN: {mini4Shrunk.2}"

-- MINI5: call wrapped in ELSE of an ite (real user-body shape)
def mini5Else : LoopProg (RiscV.Word 64) :=
  LoopProg.seq (LoopProg.assign 7 (LoopExp.shift .ror (LoopExp.var 4) (LoopExp.const 7)))
    (LoopProg.seq (LoopProg.assign 8 (LoopExp.var 3))
      (LoopProg.seq
        (LoopProg.call (some ([2], [6, 5, 4, 3, 1])) (some 5) [7, 8]
          (some (7,
            LoopProg.ite (Cmp.notEqual) 7 (RegImm.imm 1)
              (LoopProg.raise 7)
              (LoopProg.seq LoopProg.tick (LoopProg.assign 3 (LoopExp.load (LoopExp.var 1)))) [6, 5, 4, 3, 1],
            LoopProg.skip,
            [6, 5, 4, 3, 1])))
        (LoopProg.assign 1 (LoopExp.var 3))))

def mini5Body : LoopProg (RiscV.Word 64) :=
  LoopProg.seq (LoopProg.assign 9 (LoopExp.var 7))
    (LoopProg.seq
      (LoopProg.ite (Cmp.notEqual) 9 (RegImm.imm 0)
        (LoopProg.seq (LoopProg.store (LoopExp.var 6) 9)
          (LoopProg.seq
            (LoopProg.ite (Cmp.notEqual) 10 (RegImm.imm 0)
              (LoopProg.assign 5 (LoopExp.var 2))
              mini5Else
              [10])
            (LoopProg.seq (LoopProg.assign 1 (LoopExp.var 3)) (LoopProg.continue 0))))
        (LoopProg.break 0)
        [6, 5, 4, 3, 1])
      LoopProg.skip)

def mini5Loop : LoopProg (RiscV.Word 64) :=
  LoopProg.loop [6, 5, 4, 3, 1] mini5Body [6, 5, 4, 3, 1]

def mini5Shrunk : LoopProg (RiscV.Word 64) × List Nat := loopShrink [] mini5Loop [2, 3]
#eval! s!"MINI5-ANN: {mini5Shrunk.2}"


-- BIS: bisect the real user body by seq-prefix
def seqPrefix (p : LoopProg (RiscV.Word 64)) (n : Nat) : LoopProg (RiscV.Word 64) :=
  match n, p with
  | 0, _ => LoopProg.skip
  | n + 1, .seq a b => LoopProg.seq a (seqPrefix b n)
  | _, other => other

def guardThen : LoopProg (RiscV.Word 64) -> Option (LoopProg (RiscV.Word 64))
  | .ite (Cmp.notEqual) _ (RegImm.imm _) thenB _ _ => some thenB
  | .seq a b => (guardThen a).orElse (fun _ => guardThen b)
  | .loop _ b _ => guardThen b
  | _ => none

def userBody : Option (LoopProg (RiscV.Word 64)) := g25Loop.bind guardThen

def patchThen (new : LoopProg (RiscV.Word 64)) : Option (LoopProg (RiscV.Word 64)) :=
  g25Loop.map (fun l =>
    match l with
    | .loop li body lo =>
      .loop li
        (match body with
        | .seq a1 r1 =>
          .seq a1
            (match r1 with
            | .seq a2 r2 =>
              .seq a2
                (match r2 with
                | .seq iteLess r3 =>
                  .seq iteLess
                    (match r3 with
                    | .seq a9 guard =>
                      .seq a9
                        (match guard with
                        | .ite op c ri _ els live => .ite op c ri new els live
                        | g => g)
                    | r => r)
                | r => r)
            | r => r)
        | r => r) lo
    | p => p)

def bisAnn (n : Nat) : String :=
  match userBody.map (fun u => seqPrefix u n) with
  | none => "BIS-nouser"
  | some pr =>
    match patchThen (LoopProg.seq pr (LoopProg.continue 0)) with
    | none => "BIS-nopatch"
    | some l => s!"BIS-{n}: {(loopShrink [] l [2, 3]).2}"


#eval! bisAnn 0
#eval! bisAnn 2
#eval! bisAnn 4
#eval! bisAnn 6
#eval! bisAnn 8
#eval! bisAnn 10
#eval! bisAnn 12
#eval! bisAnn 14
#eval! bisAnn 16
#eval! bisAnn 18
#eval! bisAnn 20


-- BIS3: prefix nodes n=0..4 ++ stripped guard (then=continue else=break)
def guardStripped : LoopProg (RiscV.Word 64) :=
  LoopProg.ite (Cmp.notEqual) 9 (RegImm.imm 0) (LoopProg.continue 0) (LoopProg.break 0) [6, 5, 4, 3, 1]

def bis3Body (g25 : Option (LoopProg (RiscV.Word 64))) (n : Nat) : Option (LoopProg (RiscV.Word 64)) :=
  match g25 with
  | none => none
  | some (.loop li body lo) =>
    let tail := (seqPrefix body 20)
    match tail with
    | .seq pre rest => some (.seq (seqPrefix pre n) guardStripped)
    | _ => some guardStripped
  | some _ => none

def bis3Loop (n : Nat) : Option (LoopProg (RiscV.Word 64)) :=
  match g25Loop, bis3Body g25Loop n with
  | some (.loop li _ lo), some body => some (.loop li body lo)
  | _, _ => none

def bis3Ann (n : Nat) : String :=
  match bis3Loop n with
  | some l => s!"BIS3-{n}: {(loopShrink [] l [2, 3]).2}"
  | none => "BIS3-noloop"

#eval! bis3Ann 0
#eval! bis3Ann 1
#eval! bis3Ann 2
#eval! bis3Ann 3
#eval! bis3Ann 4


-- BIS4: correct left-first guard patch; then := seq(seqPrefix userBody n, continue)
def realUserBody : Option (LoopProg (RiscV.Word 64)) :=
  match userBody with
  | some (.seq u _) => some u
  | some other => some other
  | none => none

def prefix4 : LoopProg (RiscV.Word 64) :=
  match g25Loop with
  | some (.loop _ body _) =>
    match (seqPrefix body 20) with
    | .seq pre _ => seqPrefix pre 4
    | other => LoopProg.skip
  | _ => LoopProg.skip

def bis4Body (n : Nat) : LoopProg (RiscV.Word 64) :=
  match realUserBody with
  | some u => LoopProg.seq prefix4
      (LoopProg.ite (Cmp.notEqual) 9 (RegImm.imm 0)
        (LoopProg.seq (seqPrefix u n) (LoopProg.continue 0))
        (LoopProg.break 0) [6, 5, 4, 3, 1])
  | none => LoopProg.skip

def bis4Loop (n : Nat) : Option (LoopProg (RiscV.Word 64)) :=
  match g25Loop with
  | some (.loop li _ lo) => some (.loop li (bis4Body n) lo)
  | _ => none

def bis4Ann (n : Nat) : String :=
  match bis4Loop n with
  | some l => s!"BIS4-{n}: {(loopShrink [] l [2, 3]).2}"
  | none => "BIS4-noloop"

#eval! bis4Ann 0
#eval! bis4Ann 1
#eval! bis4Ann 2
#eval! bis4Ann 3
#eval! bis4Ann 4
#eval! bis4Ann 5
#eval! bis4Ann 6
#eval! bis4Ann 8
#eval! bis4Ann 10
#eval! bis4Ann 12
#eval! bis4Ann 14
#eval! bis4Ann 16
#eval! bis4Ann 18
#eval! bis4Ann 20


def chainDepth (p : LoopProg (RiscV.Word 64)) : Nat :=
  match p with
  | .seq _ b => 1 + chainDepth b
  | _ => 1

#eval! s!"USER-DEPTH: {(realUserBody.map chainDepth).getD 0}"
#eval! s!"THEN-DEPTH: {(userBody.map chainDepth).getD 0}"
#eval! bis4Ann 24
#eval! bis4Ann 28
#eval! bis4Ann 32
#eval! bis4Ann 36
#eval! bis4Ann 40


-- BIS5: full 4-node real prefix + real full user body in guard then
def fullPrefix : LoopProg (RiscV.Word 64) :=
  match g25Loop with
  | some (.loop _ body _) =>
    match body with
    | .seq a r1 => match r1 with
      | .seq b r2 => match r2 with
        | .seq c r3 => match r3 with
          | .seq d _ => LoopProg.seq a (LoopProg.seq b (LoopProg.seq c d))
          | _ => LoopProg.skip
        | _ => LoopProg.skip
      | _ => LoopProg.skip
    | _ => LoopProg.skip
  | _ => LoopProg.skip

def bis5Body : LoopProg (RiscV.Word 64) :=
  match realUserBody with
  | some u => LoopProg.seq fullPrefix
      (LoopProg.ite (Cmp.notEqual) 9 (RegImm.imm 0)
        (LoopProg.seq u (LoopProg.continue 0))
        (LoopProg.break 0) [6, 5, 4, 3, 1])
  | none => LoopProg.skip

def bis5Loop : Option (LoopProg (RiscV.Word 64)) :=
  match g25Loop with
  | some (.loop li _ lo) => some (.loop li bis5Body lo)
  | _ => none

#eval! s!"BIS5: {(bis5Loop.map (fun l => (loopShrink [] l [2, 3]).2)).getD []}"

end Flapjack.ZProbe.RB


namespace Flapjack.ZProbe.TST
open Flapjack
open Flapjack.RiscV

def tst : LoopProg Nat :=
  LoopProg.seq (LoopProg.assign 1 (LoopExp.const 0))
    (LoopProg.loop [3, 2, 1]
      (LoopProg.seq (LoopProg.ite Cmp.notEqual 4 (RegImm.reg 1)
          (LoopProg.break 0)
          (LoopProg.continue 0)
          [3, 2, 1])
        (LoopProg.seq (LoopProg.assign 3 (LoopExp.var 2))
          (LoopProg.seq (LoopProg.call (some ([5], [3, 2, 1])) (some 9) [2, 3]
              (some (9, LoopProg.raise 9, LoopProg.assign 4 (LoopExp.var 3), [3, 2, 1])))
            (LoopProg.continue 0))))
      [3, 2, 1])

def tst2 : LoopProg Nat :=
  LoopProg.seq (LoopProg.assign 1 (LoopExp.const 5))
    (LoopProg.loop [3, 2, 1]
      (LoopProg.seq (LoopProg.assign 4 (LoopExp.var 2))
        (LoopProg.seq
          (LoopProg.ite Cmp.notEqual 4 (RegImm.imm 0)
            (LoopProg.seq LoopProg.skip (LoopProg.continue 0))
            (LoopProg.continue 0)
            [3, 2, 1])
          (LoopProg.seq (LoopProg.call (some ([5], [3, 2, 1])) (some 9) [2, 3]
              (some (9, LoopProg.raise 9, LoopProg.assign 5 (LoopExp.var 4), [3, 2, 1])))
            (LoopProg.break 0))))
      [3, 2, 1])

#eval s!"TST2-SHRUNK: {repr (loopShrink [] tst2 []).1}"

#eval s!"TST-SHRUNK: {repr (loopShrink [] tst []).1}"

end Flapjack.ZProbe.TST

end Flapjack.ZProbe.G25
-- rerun
-- rerun16

namespace Flapjack.ZProbe.TC
open Flapjack
open Flapjack.RiscV

def timeCount : IO Unit := do
  let src <- IO.FS.readFile "/home/zksecurity/stateless-pancaketh/Guest/guest.pp.pnk"
  match (Parser.parseTopDecs (fun v => BitVec.ofInt 64 v) src).toOption with
  | none => IO.println "PARSE FAILED"
  | some decls =>
    match compileFlapjackEntry .rv64i (BitVec.ofNat 64 8) (fun v => BitVec.ofInt 64 v) "main" (panTargetDeclarationsWithDefaultMain decls) with
    | none => IO.println "COMPILE FAILED"
    | some p => do
  let fns := pipelineLoopFunctions .rv64i stackFunctionFirstLabel p.crepe
  let handle <- IO.FS.Handle.mk "/tmp/opencode/fntimes.txt" .write
  let mut total := 0
  let mut nfns := 0
  for (label, params, body) in fns do
    nfns := nfns + 1
    let wordParameters := wordSsaAbiParameters params.length
    let unflattened := wordProgDCE (LoopToWord.loopToWordCompFunc label params body)
    let t0 <- IO.monoMsNow
    let n := CakeRegAlloc.cakeWordStackVarCount label wordParameters wordAllocatableRegisters.length unflattened
    let s := toString n
    let t1 <- IO.monoMsNow
    total := total + (t1 - t0)
    handle.putStrLn s!"FN {label} {s} {t1 - t0}"
    handle.flush
  handle.putStrLn s!"TOTALCOUNT fns={nfns} ms={total}"
  IO.println "PROBE DONE"

-- #eval! timeCount

end Flapjack.ZProbe.TC

namespace Flapjack.ZProbe.PROF

open Flapjack.RiscV.CakeRegAlloc
open Flapjack.RiscV
open Flapjack

def treeSize : Flapjack.WordClashTree -> Nat
  | .delta _ _ => 1
  | .seq a b => 1 + treeSize a + treeSize b
  | .branch _ t e => 1 + treeSize t + treeSize e
  | .set _ => 1

def timeSubSteps (target : Nat) : IO Unit := do
  let handle <- IO.FS.Handle.mk "/tmp/opencode/prof711.txt" .write
  let source <- IO.FS.readFile "/home/zksecurity/stateless-pancaketh/Guest/guest.pp.pnk"
  let some declarations := (Flapjack.Parser.parseTopDecs (fun v => BitVec.ofInt 64 v) source).toOption
    | throw (IO.userError "parse")
  let some pipeline := compileFlapjackEntry .rv64i (BitVec.ofNat 64 8) (fun v => BitVec.ofInt 64 v) "main"
      (panTargetDeclarationsWithDefaultMain declarations)
    | throw (IO.userError "compile")
  let fns := pipelineLoopFunctions .rv64i stackFunctionFirstLabel pipeline.crepe
  match fns.find? (fun e => e.1 == target) with
  | none => handle.putStrLn "LABEL NOT FOUND"
  | some (_, params, body) =>
    let label := target
    let wordParameters := wordSsaAbiParameters params.length
    let k := wordAllocatableRegisters.length
    let unflattenedBody := wordProgDCE (Flapjack.LoopToWord.loopToWordCompFunc label params body)
    handle.putStrLn s!"START label={label} params={params.length} k={k}"
    let t0 <- IO.monoMsNow
    let ssa := (wordFullSsaCcTrans wordParameters.length unflattenedBody).2.2
    let n1 := (wordProgVariables ssa).length
    handle.putStrLn s!"SSA vars={n1}"
    let t1 <- IO.monoMsNow
    let tree := wordClashTree ssa []
    let n2 := treeSize tree
    handle.putStrLn s!"TREE size={n2}"
    let t2 <- IO.monoMsNow
    let fs := cakeGetStackOnly ssa
    let forced := cakeGetForced ssa
    let (wordMoves, spillCosts) := wordGetHeuristics 3 label ssa
    let moves := wordMoves.map (fun m => (m.priority, (m.left, m.right)))
    let n3 := moves.length + ((spillCosts.map List.length).getD 0)
    handle.putStrLn s!"HEUR moves={moves.length} scost={n3 - moves.length}"
    let t3 <- IO.monoMsNow
    let bij := cakeMkBij tree
    let scost := spillCosts.map (fun costs =>
      costs.filterMap (fun entry =>
        (lookupNatInfo entry.1 bij.toAllocator).map
          (fun node => (node, entry.2))))
    let n4 := bij.toAllocator.length + ((scost.map List.length).getD 0)
    handle.putStrLn s!"BIJ nodes={n4}"
    let t4 <- IO.monoMsNow
    let allocation := cakeDoRegAlloc .irc scost k moves tree forced fs
    let n5 := allocation.isSome
    handle.putStrLn s!"ALLOC some={n5}"
    let t5 <- IO.monoMsNow
    let total := cakeWordStackVarCount label wordParameters k unflattenedBody
    handle.putStrLn s!"COUNT total={total}"
    let t6 <- IO.monoMsNow
    handle.putStrLn s!"MS ssa={t1 - t0} tree={t2 - t1} heur={t3 - t2} bij={t4 - t3} alloc={t5 - t4} count={t6 - t5}"
  handle.flush

#eval! timeSubSteps 711

end Flapjack.ZProbe.PROF

-- rerun6
def f00003Source : String :=
  "var 1 g = 41;\nfun 1 main() { return g; }\n"

def f00003Decls : Option (List (Decl (RiscV.Word 64))) :=
  (Flapjack.Parser.parseTopDecs (fun v => BitVec.ofInt 64 v) f00003Source).toOption

def f00003Pipeline : Option (FlapjackPipelineResult (RiscV.Word 64)) :=
  f00003Decls.bind (fun declarations =>
    Flapjack.compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
      (fun v => BitVec.ofInt 64 v) "main"
      (panTargetDeclarationsWithDefaultMain declarations))

def f00003Stack : Option (List (Nat × List Nat × StackProg Nat)) :=
  match f00003Pipeline with
  | none => none
  | some pipeline =>
      match RiscV.pipelineWordFunctionsToStackChecked pipeline.word with
      | .error _ => none
      | .ok functions => some functions

def f00003Probe : String :=
  match f00003Stack with
  | none => "STACK STAGE FAILED"
  | some functions =>
      let config := Flapjack.compileRemoveConfig
      let programs := (RiscV.stackRaiseStubLocation,
          RiscV.stackRaiseStub false config.addressScratch) :: functions.map (fun (label, _, body) => (label, body))
      match RiscV.stackProgramsWithLongDivRuntime config programs with
      | none => "LONGDIV RUNTIME FAILED"
      | some expanded =>
          let sections := (expanded.map (fun (sectionId, program) =>
            RiscV.labProgramToEntrySection sectionId 0 0
              (RiscV.stackRemoveComplete config program))).map RiscV.labSectionNatToWord
          let bad := sections.flatMap (fun section =>
            section.lines.flatMap (fun line =>
              match line with
              | .asm operation _ _ =>
                  if (RiscV.labCompilePlain operation).isNone then
                    [s!"section {section.name}: {repr operation}" ]
                  else []
              | _ => []))
          if bad.isEmpty then "ALL PLAINS OK" else "\n".join bad

#eval f00003Probe
