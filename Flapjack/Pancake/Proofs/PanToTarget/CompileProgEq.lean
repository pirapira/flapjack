import Flapjack.Pancake.PanToTarget

namespace Flapjack.Pancake.PanToTarget
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend

/-- Full original compiler equation factoring WordToWord through backend
from_word_0. Main ordering, native symbol construction, and exports are exactly
those of compileProgHOL; only independent let bindings move. No successful
pass, target execution, or output premise is assumed. This equation is source
correspondence, not the final compiler-semantics theorem or production routing. -/
@[hol "cakeml/pancake/pan_to_targetScript.sml" "compile_prog_eq"
  (words_as_type_indexed_bitvec)]
theorem compileProgEqHOL {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (config : Flapjack.Compiler.Backend.Backend.Config)
    (program : List (DeclHOL width)) :
    (compileProgHOL asmConf config program :
      Option (List (BitVec 8) × List (BitVec width) ×
        Flapjack.Compiler.Backend.Backend.Config)) =
      let prog1 := mainFirstHOL program
      let prog2 := panToWordCompileProgHOL asmConf.isa prog1
      let names := sptFromAList ((Flapjack.Basis.Pure.MlList.sort
        (fun a b : Nat => decide (a < b)) (prog2.map Prod.fst)).zip
        (ofString "generated_main" :: (functionsHOL prog1).map Prod.fst))
      let names := sptUnion (sptFromAList
        (WordToStack.stubNames () ++ StackAlloc.stubNames () ++ StackRemove.stubNames ())) names
      let config := { config with exported := exportsHOL program }
      Backend.fromWord0 asmConf config names prog2 := by
  rfl
end Flapjack.Pancake.PanToTarget
