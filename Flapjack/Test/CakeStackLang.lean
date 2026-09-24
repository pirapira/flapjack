import Flapjack.RiscV.CakeStackLang

namespace Flapjack.Test.CakeStackLang

open Flapjack.RiscV.CakeStackLang

abbrev ProbeProg := Prog Nat Nat Nat Nat Nat Nat Nat String

def progConstructorIndex : ProbeProg → Nat
  | .skip => 0
  | .inst _ => 1
  | .get _ _ => 2
  | .set _ _ => 3
  | .opCurrHeap _ _ _ => 4
  | .call _ _ _ => 5
  | .seq _ _ => 6
  | .ite _ _ _ _ _ => 7
  | .loop _ => 8
  | .jumpLower _ _ _ => 9
  | .alloc _ => 10
  | .storeConsts _ _ _ => 11
  | .raise _ => 12
  | .ret _ => 13
  | .break _ => 14
  | .continue _ => 15
  | .ffi _ _ _ _ _ _ => 16
  | .tick => 17
  | .locValue _ _ _ => 18
  | .install _ _ _ _ _ => 19
  | .shMemOp _ _ _ => 20
  | .codeBufferWrite _ _ => 21
  | .dataBufferWrite _ _ => 22
  | .rawCall _ => 23
  | .stackAlloc _ => 24
  | .stackFree _ => 25
  | .stackStore _ _ => 26
  | .stackStoreAny _ _ => 27
  | .stackLoad _ _ => 28
  | .stackLoadAny _ _ => 29
  | .stackGetSize _ => 30
  | .stackSetSize _ => 31
  | .bitmapLoad _ _ => 32
  | .halt _ => 33

def progConstructorFixtures : List ProbeProg :=
  [ .skip
  , .inst 0
  , .get 1 (.temp 2)
  , .set .globals 1
  , .opCurrHeap 0 1 2
  , .call (some (.skip, 1, 2, 3)) (.inl 4) (some (.tick, 5, 6))
  , .seq .skip .tick
  , .ite 0 1 2 .skip .tick
  , .loop .skip
  , .jumpLower 1 2 3
  , .alloc 4
  , .storeConsts 1 2 (some 3)
  , .raise 1
  , .ret 1
  , .break 1
  , .continue 1
  , .ffi "ffi" 1 2 3 4 5
  , .tick
  , .locValue 1 2 3
  , .install 1 2 3 4 5
  , .shMemOp 0 1 2
  , .codeBufferWrite 1 2
  , .dataBufferWrite 1 2
  , .rawCall 1
  , .stackAlloc 1
  , .stackFree 1
  , .stackStore 1 2
  , .stackStoreAny 1 2
  , .stackLoad 1 2
  , .stackLoadAny 1 2
  , .stackGetSize 1
  , .stackSetSize 1
  , .bitmapLoad 1 2
  , .halt 1 ]

#guard (progConstructorFixtures.map progConstructorIndex) == List.range 34

def storeNameConstructorIndex : StoreName Nat → Nat
  | .nextFree => 0
  | .endOfHeap => 1
  | .triggerGC => 2
  | .heapLength => 3
  | .progStart => 4
  | .bitmapBase => 5
  | .currHeap => 6
  | .otherHeap => 7
  | .allocSize => 8
  | .globals => 9
  | .globReal => 10
  | .handler => 11
  | .genStart => 12
  | .codeBuffer => 13
  | .codeBufferEnd => 14
  | .bitmapBuffer => 15
  | .bitmapBufferEnd => 16
  | .temp _ => 17

def storeNameConstructorFixtures : List (StoreName Nat) :=
  [ .nextFree, .endOfHeap, .triggerGC, .heapLength, .progStart, .bitmapBase
  , .currHeap, .otherHeap, .allocSize, .globals, .globReal, .handler
  , .genStart, .codeBuffer, .codeBufferEnd, .bitmapBuffer, .bitmapBufferEnd
  , .temp 0 ]

#guard (storeNameConstructorFixtures.map storeNameConstructorIndex) == List.range 18

end Flapjack.Test.CakeStackLang
