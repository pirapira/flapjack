import Flapjack.RiscV.Encoding
import Flapjack.RiscV.ArtifactFormat
import Flapjack.RiscV.WordCse

/-! Encoding and assembly-formatting parity with the CakeML RISC-V exporter
    (`export_riscvScript.sml`): signed DIV carries funct3 4 / funct7 1
    (`riscv_ast` Div), and bitmap data is emitted as split16 — sixteen
    `.quad` words per line, no line at all when empty. -/

namespace Flapjack.RiscV

example : encodeInstruction (width := 64) (.div 1 2 3) =
    (0x023140B3 : BitVec 32) := by
  decide

example : encodeInstruction (width := 64) (.divU 1 2 3) =
    (0x023150B3 : BitVec 32) := by
  decide

example : pancakeBitmapQuadLines [] = [] := by
  rfl

example : pancakeBitmapQuadLines (List.range 16) =
    ["\t.quad 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15"] := by
  decide

example : pancakeBitmapQuadLines (List.range 20) =
    ["\t.quad 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15",
     "\t.quad 16,17,18,19"] := by
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
