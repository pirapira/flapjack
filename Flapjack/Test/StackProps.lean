import Flapjack.Compiler.Backend.StackProps

namespace Flapjack.Test.StackProps

open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps

abbrev ProbeProg := Prog Nat Nat Nat Nat Nat Nat String

def checks : AsmChecks Nat Nat Nat :=
  { regCount := 8
    avoidRegs := [3]
    instOk := fun instruction => instruction == 1
    regOk := fun register => register < 8 && ![3].contains register
    addrOk := fun operator address => operator == 1 && address == 2 }

def valid (program : ProbeProg) : Bool := stackAsmOk checks program

def recursiveClauseGuards : Bool :=
  valid (.inst 1) &&
  !valid (.inst 0) &&
  valid (.shMemOp 1 2 2) &&
  !valid (.shMemOp 1 3 2) &&
  !valid (.shMemOp 0 2 2) &&
  valid (.codeBufferWrite 1 2) &&
  !valid (.codeBufferWrite 1 3) &&
  !valid (.codeBufferWrite 1 8) &&
  valid (.seq (.raise 1) (.ret 2)) &&
  !valid (.seq (.raise 1) (.ret 3)) &&
  valid (.ite 99 99 99 (.raise 1) (.ret 2)) &&
  !valid (.ite 99 99 99 (.raise 1) (.ret 3)) &&
  valid (.loop (.raise 1)) &&
  !valid (.loop (.raise 8)) &&
  valid (.call none (.inl 999) (some (.raise 3, 4, 5))) &&
  valid (.call none (.inr 2) none) &&
  !valid (.call none (.inr 3) none) &&
  valid (.call (some (.raise 1, 2, 3, 4)) (.inl 999)
    (some (.ret 2, 5, 6))) &&
  !valid (.call (some (.raise 1, 2, 3, 4)) (.inl 999)
    (some (.ret 3, 5, 6)))

#guard recursiveClauseGuards

def defaultClauseGuards : Bool :=
  valid .skip &&
  valid (.get 999 .globals) &&
  valid (.set .globals 999) &&
  valid (.opCurrHeap 0 999 999) &&
  valid (.alloc 999) &&
  valid (.storeConsts 999 999 (some 999)) &&
  valid (.break 999) &&
  valid (.continue 999) &&
  valid (.ffi "f" 999 999 999 999 999) &&
  valid .tick &&
  valid (.locValue 999 999 999) &&
  valid (.install 999 999 999 999 999) &&
  valid (.dataBufferWrite 999 999) &&
  valid (.rawCall 999) &&
  valid (.stackAlloc 999) &&
  valid (.stackFree 999) &&
  valid (.stackStore 999 999) &&
  valid (.stackStoreAny 999 999) &&
  valid (.stackLoad 999 999) &&
  valid (.stackLoadAny 999 999) &&
  valid (.stackGetSize 999) &&
  valid (.stackSetSize 999) &&
  valid (.bitmapLoad 999 999) &&
  valid (.halt 999)

#guard defaultClauseGuards

end Flapjack.Test.StackProps
