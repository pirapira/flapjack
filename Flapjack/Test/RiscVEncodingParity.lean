import Flapjack.RiscV.Encoding
import Flapjack.RiscV.WordCse

/-! Encoding parity with the CakeML RISC-V exporter (`export_riscvScript.sml`):
    the Word `Div` operation uses the signed DIV funct3/funct7 encoding. -/

namespace Flapjack.RiscV

example : encodeInstruction (width := 64) (.divU 1 2 3) =
    (0x023140B3 : BitVec 32) := by
  decide

example : encodeInstruction (width := 64) (.remU 1 2 3) =
    (0x023170B3 : BitVec 32) := by
  decide

/-! The reduced Word CSE boundary must preserve Cake's repeated
    HeapLength/Shift/CurrHeap facts as moves.  This is the shape emitted by
    duplicate global initializers before the selected-instruction refactor. -/
def cseDuplicateGlobalPrelude : WordProg (Word 64) :=
  .seq (.get 13 (.heapLength : WordStore (Word 64)))
    (.seq (.assign 17
      (.shift .lsl (.var 13) (.const (1 : Word 64))))
      (.seq (.opCurrHeap .add 21 17)
        (.seq (.get 37 (.heapLength : WordStore (Word 64)))
          (.seq (.assign 41
            (.shift .lsl (.var 37) (.const (1 : Word 64))))
            (.opCurrHeap .add 45 41)))))

#guard (match wordCseProp cseDuplicateGlobalPrelude with
  | .seq (.get 13 .heapLength)
      (.seq (.assign 17 _)
        (.seq (.opCurrHeap .add 21 17)
          (.seq (.move 1 [(37, 13)])
            (.seq (.move 0 [(41, 17)])
              (.move 0 [(45, 21)]))))) => true
  | _ => false)

end Flapjack.RiscV
