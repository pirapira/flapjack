import Flapjack.RiscV.Ffi

namespace Flapjack

open RiscV

def ffiAbiState : State 64 :=
  writeRegister
    (writeRegister
      (writeRegister
        (writeRegister (zeroState 64) 2 10) 3 1) 4 20) 5 2

def ffiAbiHost : WordFfiHost 64 :=
  fun service configuration configurationLength array arrayLength state =>
    if service = 7 then
      some (writeRegister state 6
        (configuration + configurationLength + array + arrayLength))
    else none

example :
    ((wordFfiToRiscV { services := [("sum", 7)] } "sum" 2 3 4 5).bind
        (executeInstructionsWithFfi ffiAbiHost ffiAbiState)).map
        (fun state => readRegister state 6) = some 33 := by
  native_decide

example :
    (executeWithFfi ffiAbiHost
        (writeRegister
          (writeRegister
            (writeRegister
              (writeRegister (writeRegister (zeroState 64) 10 10) 11 1)
                12 20) 13 2) 14 7) .ecall).map
        (fun state => readRegister state 6) = some 33 := by
  native_decide

end Flapjack
