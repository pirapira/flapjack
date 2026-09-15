import Flapjack.RiscV.WordToStack

namespace Flapjack

open RiscV

def reservedSourceMoveConfig : WordStackConfig :=
  { locations := [(24, .register 29)]
    scratch := 31
    stackBase := 0
    addressScratch := 29
    abiBase := 10 }

def riscvAbiParameterMoveConfig : WordStackConfig :=
  { locations := (List.range 12).map (fun name => (name, .register name))
    scratch := 31
    stackBase := 0
    addressScratch := 29
    abiBase := 10
    abiStride := 1 }

/- Cake's RISC-V ABI uses consecutive x10--x21 argument registers.  The
   source-shaped helper keeps stride two, but target lowering must not invent
   x32 for a twelfth parameter. -/
#guard
  wordStackPhysicalMovesFrom riscvAbiParameterMoveConfig
      (List.range 12) 10 =
    some ((List.range 12).map (fun name =>
      (WordLocation.register name, WordLocation.register (10 + name))))

/- CakeML's RISC-V word_to_stack parallel move accepts a physical source in
   x29; only a move destination may not clobber the backend address scratch. -/
#guard
  (wordStackMovesToPhysical (α := Nat) reservedSourceMoveConfig [24] 10).isSome

#guard
  (wordStackParallelLocationMove (α := Nat) reservedSourceMoveConfig
    [(.register 10, .register 29)]).isSome

#guard
  (wordStackParallelLocationMove (α := Nat) reservedSourceMoveConfig
    [(.register 29, .register 10)]).isNone

end Flapjack
