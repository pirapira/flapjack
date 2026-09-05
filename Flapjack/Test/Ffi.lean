import Flapjack.RiscV.Link

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

def ffiWordHandler : FunName → Word 64 → Word 64 → Word 64 → Word 64 →
    State 64 → Option (State 64) :=
  fun function configuration configurationLength array arrayLength state =>
    if function == "sum" then
      some (writeRegister state 6
        (configuration + configurationLength + array + arrayLength))
    else none

example :
    ((wordFfiToRiscV { services := [("sum", 7)] } "sum" 2 3 4 5).bind
        (executeInstructionsWithFfi ffiAbiHost ffiAbiState)).map
        (fun state => readRegister state 6) = some 33 := by
  native_decide

example [NeZero width] :
    wordFunctionToRiscVWithCallsAndFfi
      ({ targets := [], services := [("sum", 7)] } : WordCallFfiContext width)
      (.seq (.ffi "sum" 2 3 4 5 []) (.return 0 [6])) =
      some ([.addi 10 2 0, .addi 11 3 0, .addi 12 4 0, .addi 13 5 0,
        .addi 14 0 (BitVec.ofNat width 7), .ecall], [6]) := by
  simp [wordFunctionToRiscVWithCallsAndFfi, wordFfiToRiscV,
    lookupWordFfiService, wordRegisterMoves, wordFunctionToRiscVWithCalls,
    registerOfNat]

example :
    ((wordFunctionToRiscVWithCallsAndFfi
        ({ targets := [], services := [("sum", 7)] } : WordCallFfiContext 64)
        (.seq (.ffi "sum" 2 3 4 5 []) (.return 0 [6]))).bind
      (fun result => executeInstructionsWithFfi ffiAbiHost ffiAbiState result.1)).map
        (fun state => readRegister state 6) = some 33 := by
  native_decide

example :
    (evalWordFunctionWithCallsAndFfi [] ffiWordHandler 10 ffiAbiState
      (.seq (.ffi "sum" 2 3 4 5 []) (.return 0 [6]))).map
        (fun result => result.2) = some [33] := by
  native_decide

example :
    wordFunctionToRiscVWithCallsAndFfiAndLoops
      ({ targets := [], services := [("sum", 7)] } : WordCallFfiContext 64)
      (.loop [] (.seq (.ffi "sum" 2 3 4 5 []) (.break 0)) []) =
      some ([.addi 10 2 0, .addi 11 3 0, .addi 12 4 0, .addi 13 5 0,
        .addi 14 0 7, .ecall, .jal 0 8, .jal 0 (0 - BitVec.ofNat 64 28)], []) := by
  native_decide

example :
    linkWordFunctionsWithFfi (0 : Word 64) [("sum", 7)]
      [(7, [], (.seq (.ffi "sum" 2 3 4 5 []) (.return 0 [6])))] =
      some [(7, 0, [],
        [.addi 10 2 0, .addi 11 3 0, .addi 12 4 0, .addi 13 5 0,
          .addi 14 0 7, .ecall, .jalr 0 1 0], [6])] := by
  simp [linkWordFunctionsWithFfi, wordFunctionTargetSignaturesWithCalls,
    wordFunctionTargetSignaturesAux, wordFunctionReturnNamesWithCalls,
    lookupWordFunctionBody, compileLinkedWordFunctionWithFfi,
    wordFunctionToRiscVWithCallsAndFfiAndLoops,
    wordFunctionToRiscVWithCallsAndFfiAndLoopsAux,
    wordControlInstructions, resolveWordLoopBody, resolveWordLoopBodyAux,
    wordFunctionToRiscVWithCallsAndFfi, wordFfiToRiscV,
    lookupWordFfiService, wordRegisterMoves, wordFunctionToRiscVWithCalls,
    wordFunctionReturnNames, registerOfNat, linkRiscVFunctions,
    linkRiscVFunctionsAt]

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
