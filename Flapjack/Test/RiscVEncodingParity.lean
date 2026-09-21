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
    HeapLength/Shift/CurrHeap facts as moves.  This is the instruction shape
    produced by duplicate global initializers after `inst_select` has turned
    the shift into an `Inst (Arith (Shift ...))`; Cake's `word_cse` shares the
    second shift and heap-base computation through the instruction fact
    table. -/
def cseDuplicateGlobalPrelude : WordProg (Word 64) :=
  .seq (.get 13 (.heapLength : WordStore (Word 64)))
    (.seq (.inst (.arith (.shift .lsl 17 13 (.imm (1 : Word 64)))))
      (.seq (.opCurrHeap .add 21 17)
        (.seq (.get 37 (.heapLength : WordStore (Word 64)))
          (.seq (.inst (.arith (.shift .lsl 41 37 (.imm (1 : Word 64)))))
            (.opCurrHeap .add 45 41)))))

#guard (match wordCseProp cseDuplicateGlobalPrelude with
  | .seq (.get 13 .heapLength)
      (.seq (.inst (.arith (.shift .lsl 17 13 _)))
        (.seq (.opCurrHeap .add 21 17)
          (.seq (.move 1 [(37, 13)])
            (.seq (.move 0 [(41, 17)])
              (.move 0 [(45, 21)]))))) => true
  | _ => false)

/-! `wordCse` must emit the *original* source register of an `OpCurrHeap`
    even when that register has a recorded constant equivalence.  Cake's
    `word_cse_def` uses `canonicalRegs'` only to build the fact key and passes
    the original `OpCurrHeap b r1 r2` to `add_to_data_aux`
    (`cakeml/compiler/backend/word_cseScript.sml:587-594`).  Emitting the
    canonicalised source made the second `Const` look dead, so Flapjack
    dropped an instruction Cake keeps (GH #1127, bead flapjack-1kj): for
    `st (0 + 0), 1; return @base | 1;` Cake emits `li a0,1; ...; li a0,1;
    or a0,a0,@base` while Flapjack emitted only one `li`.  This program is the
    post-SSA shape of that fixture. -/
def cseCurrHeapKeepsOriginalSource : WordProg (Word 64) :=
  .seq (.inst (.const 21 1))
    (.seq (.inst (.const 29 1))
      (.opCurrHeap .or 33 29))

#guard (match wordCseProp cseCurrHeapKeepsOriginalSource with
  | .seq (.inst (.const 21 1))
      (.seq (.inst (.const 29 1))
        (.opCurrHeap .or 33 29)) => true
  | _ => false)

end Flapjack.RiscV
