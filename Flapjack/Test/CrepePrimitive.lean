import Flapjack.CrepePrimitiveRelation
import Flapjack.CrepeSemantics

/-! Executable regression for the RISC-V primitive through compilation. -/

namespace Flapjack

def crepePrimitiveContext : CompileContext (RiscV.Word 64) :=
  { vars := [("pair", (.comb [.one, .one], [0, 1]))]
    functions := []
    exceptions := []
    maxVar := 1
    bytesInWord := BitVec.ofNat 64 8 }

def crepePrimitiveProgram : Prog (RiscV.Word 64) :=
  .seq
    (.primitive "pair" .addCarry
      [.const 1, .const 2, .const 0])
    (.return (.var .local "pair"))

def crepePrimitiveState : CrepState (RiscV.Word 64) :=
  { locals := fun _ => none
    memory := fun _ => none }

theorem crepe_primitive_compilation_regression :
    evalCrepFullResult [] RiscV.crepPrimitiveHandler
      (noCrepFfi _) defaultCrepSharedMemHandler
      0 100 20 crepePrimitiveState
      (compileProg crepePrimitiveContext crepePrimitiveProgram) =
      some [BitVec.ofNat 64 3, BitVec.ofNat 64 0] := by
  decide +kernel

end Flapjack
