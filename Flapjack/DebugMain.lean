import Flapjack.RiscV.PipelineDiagnostics

/-!
# Intermediate pipeline dump

This executable is intentionally diagnostic rather than a second compiler
entry point.  It prints the values returned by the source pipeline at the
same boundaries that are named in CakeML's `pan_passes` development.  The
output is designed to be saved beside a differential-fuzz finding and
compared with `scripts/pancake-stage-probe.sml`.
-/

namespace Flapjack.Debug

open Flapjack Flapjack.RiscV

def emit [Repr α] (label : String) (value : α) : IO Unit :=
  IO.println (label ++ "=" ++ repr value)

def dumpPipeline (pipeline : FlapjackPipelineResult (RiscV.Word 64)) : IO Unit := do
  emit "stage=simplified" pipeline.simplified
  emit "stage=structured" pipeline.structured
  emit "stage=global_initializers" pipeline.globals.initializers
  emit "stage=global_declarations" pipeline.globals.declarations
  emit "stage=crepe" pipeline.crepe
  emit "stage=loop" pipeline.loop
  emit "stage=word" pipeline.word
  let selected := pipeline.word.map (fun (label, parameters, body) =>
    (label, parameters, RiscV.wordInstSelectProgramFrom body))
  emit "stage=word_inst_select" selected
  /- The runtime-image CLI follows the source-shaped `pan_to_word` path below,
     rather than the historical `pipeline.word` helper above.  Dump its
     boundaries too so source-to-RISC-V discrepancies can be localized against
     Cake's `loop_to_word` probe. -/
  let sourceLoop := pipelineLoopFunctionsSource .rv64i stackFunctionFirstLabel
    pipeline.crepe
  let sourceWord := panToWordCompileProg sourceLoop
  emit "stage=source_loop" sourceLoop
  emit "stage=source_word" sourceWord
  let sourceSelected := sourceWord.map (fun (label, arity, body) =>
    (label, arity,
      RiscV.wordInstSelectProgramFrom
        (RiscV.wordConstFp (RiscV.wordFlattenProgramFrom body))))
  emit "stage=source_word_inst_select" sourceSelected
  match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked
      (RiscV.wordStackInitialBitmaps false) sourceWord with
  | .error error => emit "stage=source_word_allocated_error" error
  | .ok (functions, _) => emit "stage=source_word_allocated" functions

def dumpSource (source : String) : IO UInt32 := do
  match Parser.parseTopDecs (BitVec.ofInt 64) source with
  | .error errors =>
      emit "stage=parse_error" errors
      return 1
  | .ok declarations =>
      emit "stage=parsed" declarations
      let checked := staticCheck declarations
      emit "stage=static_check" checked
      match compileFlapjackEntry .rv64i (BitVec.ofNat 64 8)
          (fun value => BitVec.ofNat 64 value) "main" declarations with
      | none =>
          IO.println "stage=compile_entry=none"
          return 1
      | some pipeline =>
          dumpPipeline pipeline
          return 0

def usage : String :=
  "Usage: lake exe flapjack-debug [SOURCE.pnk]\n" ++
  "Read Pancake source from SOURCE.pnk or stdin and print intermediate stages."

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [] =>
      let stdin ← IO.getStdin
      dumpSource (← stdin.readToEnd)
  | ["--help"] | ["-h"] =>
      IO.println usage
      return 0
  | [path] =>
      dumpSource (← IO.FS.readFile path)
  | _ =>
      IO.eprintln usage
      return 2

end Flapjack.Debug

def main (arguments : List String) : IO UInt32 := Flapjack.Debug.main arguments
