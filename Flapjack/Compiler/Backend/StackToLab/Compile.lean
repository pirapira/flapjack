import Flapjack.Compiler.Backend.StackToLab.Native
import Flapjack.Compiler.Backend.StackRawCall
import Flapjack.Compiler.Backend.StackAlloc.Compile
import Flapjack.Compiler.Backend.StackRemove.Compile
import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Compiler.Backend.BvlToBvi

/-! `is_gen_gc_def`, the `config` datatype, `compile_def` and
`compile_no_stubs_def` (`stack_to_labScript.sml:138-167`): the stack-to-lab
pass composition rawcall, alloc, remove, names and `prog_to_section`. -/

namespace Flapjack.Compiler.Backend.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang

/-- HOL `is_gen_gc_def`. -/
@[hol "cakeml/compiler/backend/stack_to_labScript.sml" "is_gen_gc_def"]
def isGenGc : DataToWord.GcKind → Bool
  | .generational _ => true
  | _ => false

/-- HOL `stack_to_lab$config`, field for field in HOL order. `reg_names` is a
`num num_map` (`Spt Nat`); `perf_calls` is the original (unverified, x64-only)
performance flag, retained as data. -/
@[hol "cakeml/compiler/backend/stack_to_labScript.sml" "config"]
structure Config where
  regNames : Spt Nat
  jump : Bool
  perfCalls : Bool

/-- HOL `compile_def`. -/
@[hol "cakeml/compiler/backend/stack_to_labScript.sml" "compile_def"
  (words_as_type_indexed_bitvec)]
def compile {width : Nat} [NeZero width] (stackConf : Config) (dataConf : DataToWord.Config)
    (maxHeap sp : Nat) (offset : BitVec width × BitVec width)
    (prog : List (Nat × HolProg width)) : LabSem.LabProgHOL width :=
  let prog := StackRawCall.compile prog
  let prog := StackAlloc.compile dataConf prog
  let prog := StackRemove.compileHOL stackConf.jump offset (isGenGc dataConf.gcKind)
    maxHeap sp BvlToBvi.initGlobalsLocation prog
  let prog := StackNames.compileHOL stackConf.regNames prog
  prog.map progToSectionHOL

/-- HOL `compile_no_stubs_def`. -/
@[hol "cakeml/compiler/backend/stack_to_labScript.sml" "compile_no_stubs_def"
  (words_as_type_indexed_bitvec)]
def compileNoStubs {width : Nat} [NeZero width] (f : Spt Nat) (jump : Bool)
    (offset : BitVec width × BitVec width) (sp : Nat)
    (prog : List (Nat × HolProg width)) : LabSem.LabProgHOL width :=
  (StackNames.compileHOL f
    ((prog.map StackAlloc.progComp).map (StackRemove.progComp jump offset sp))).map
    progToSectionHOL

end Flapjack.Compiler.Backend.StackToLab
