import Flapjack.RiscV.CorrectnessEncoding

namespace Flapjack.Test.CorrectnessEncoding

open Flapjack Flapjack.RiscV

example :
    (encodeLinkedSections
      [(7, BitVec.ofNat 64 0x1000,
        [.addi (1 : Fin 32) 0 (BitVec.ofNat 64 7), .ecall])]).map
          (fun encodedSection => (encodedSection.label, encodedSection.address)) =
      [(7, BitVec.ofNat 64 0x1000)] := by
  simp [encodeLinkedSections_labels_addresses]

example :
    (encodeLinkedSections
      [(7, BitVec.ofNat 64 0x1000,
        [.addi (1 : Fin 32) 0 (BitVec.ofNat 64 7), .ecall])]).map
          (fun encodedSection => encodedSection.bytes.length) =
      [8] := by
  simp [encodeLinkedSections_byte_lengths]

example :
    (encodeLinkedSections
      [(7, BitVec.ofNat 64 0x1000,
        [.addi (1 : Fin 32) 0 (BitVec.ofNat 64 7), .ecall]),
       (8, BitVec.ofNat 64 0x2000, [])]).foldl
          (fun total encodedSection => total + encodedSection.bytes.length) 0 =
      8 := by
  decide

end Flapjack.Test.CorrectnessEncoding
