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

/- Cake's `format_var` keeps the first twelve RISC-V ABI slots in x10--x21
   and maps the remaining call arguments into the current `f` frame from its
   highest slot downward.  This is the concrete 25-argument shape that used
   to synthesize x22 and above instead of spilling. -/
def abiOverflowMoveConfig : WordStackConfig :=
  { locations := (List.range 25).map (fun name => (name, .register (2 + name)))
    scratch := 31
    stackBase := 0
    addressScratch := 29
    abiBase := 10
    abiStride := 1
    abiRegisterCount := 12
    abiFrameSlots := 25 }

#guard
  wordStackPhysicalMovesTo abiOverflowMoveConfig (List.range 25) 10 =
    some ((List.range 25).map (fun index =>
      (if index < 12 then .register (10 + index)
       else .stack (25 - (index - 12)), .register (2 + index))))

#guard
  (wordStackMovesToPhysical (α := Nat) abiOverflowMoveConfig
    (List.range 25) 10).isSome

def abiCallOverflow17Config : WordStackConfig :=
  { locations := (List.range 17).map (fun name => (name, .register (2 + name)))
    scratch := 31
    stackBase := 0
    addressScratch := 29
    abiBase := 10
    abiStride := 1
    abiRegisterCount := 12
    abiFrameSlots := 5 }

#guard
  wordStackPhysicalMovesTo abiCallOverflow17Config (List.range 17) 10 =
    some ((List.range 17).map (fun index =>
      (if index < 12 then .register (10 + index)
       else .stack (5 - (index - 12)), .register (2 + index))))

/- Cake's dead-program pass can remove every formal entry move.  Frame sizing
   still uses the complete formal count, but physical entry moves use only the
   surviving destinations; otherwise dead formals can alias and make parmove
   reject the list. -/
def deadEntryMoveProgram : WordProg (Word 64) :=
  .seq (.move 1 [(41, 0), (45, 2)]) .skip

#guard
  wordStackLiveEntryParameters deadEntryMoveProgram = [41, 45]

#guard
  wordStackLiveEntryParameters (.skip : WordProg (Word 64)) = []

end Flapjack
