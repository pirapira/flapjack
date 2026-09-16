import Flapjack.RiscV.Lab

namespace Flapjack.RiscV

/-! CakeML's `lab_to_target` indexes CallFFI targets from the original
    `ffi_names` order while the exported prefix emits those blocks reversed.
    These two-service guards exercise the position base and prefix ordering;
    the one-service case cannot distinguish the two conventions. -/

example :
    labFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "first" 64 =
      some (0 - BitVec.ofNat 64 112) := by
  decide

example :
    labFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "second" 64 =
      some (0 - BitVec.ofNat 64 128) := by
  decide

example :
    labFfiStubPrefix (width := 64)
      { services := [("first", 7), ("second", 8)] } =
      labFfiServiceStub 8 ++ labFfiServiceStub 7 ++
        List.replicate 8 (.jal 0 0) := by
  rfl

example :
    labCompileAsmWithHalt (width := 64) { services := [] } [] 64 999 .halt =
      some [.jal 0 (0 - BitVec.ofNat 64 80)] := by
  rfl

example :
    labCompileAsmWithHalt (width := 64) { services := [] } [] 64 999 .install =
      some [.jal 0 (0 - BitVec.ofNat 64 96)] := by
  rfl

example :
    labCompileAsmProgramWithFfiBaseAndHalt (width := 64)
      { services := [("first", 7), ("second", 8)] } [] 96 64 999
      (.callFfi "first") =
      /- Cake addresses the exported FFI block from the linked absolute
         position; `ffiBase` is retained only for the legacy API shape. -/
      some [.jal 0 (0 - BitVec.ofNat 64 144)] := by
  decide

end Flapjack.RiscV
