import Flapjack.RiscV.WordToStack

namespace Flapjack

open RiscV

def reservedSourceMoveConfig : WordStackConfig :=
  { locations := [(24, .register 29)]
    scratch := 31
    stackBase := 0
    addressScratch := 29
    abiBase := 10 }

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
