import Flapjack.StackRemove

namespace Flapjack

def stackRemoveTestConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8 }

example :
    stackRemove stackRemoveTestConfig (.get 4 .heapLength : StackProg Nat) =
      .seq (.seq (.const 29 3) (.arith .add 29 10 29))
        (.inst (.mem .load 4 29)) := by
  change stackRemoveFuel 1024 stackRemoveTestConfig
      (.get 4 .heapLength : StackProg Nat) = _
  simp [stackRemoveFuel, stackRemoveGet, stackRemoveJoin,
    stackRemoveAddress, stackStorePosition, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.set .globals 6 : StackProg Nat) =
      .seq (.seq (.const 29 8) (.arith .add 29 10 29))
        (.inst (.mem .store 6 29)) := by
  change stackRemoveFuel 1024 stackRemoveTestConfig
      (.set .globals 6 : StackProg Nat) = _
  simp [stackRemoveFuel, stackRemoveSet, stackRemoveJoin,
    stackRemoveAddress, stackStorePosition, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackAlloc 2 : StackProg Nat) =
      .seq (.const 31 16) (.arith .sub 20 20 31) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackAlloc,
    stackRemoveStackDelta, stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackFree 2 : StackProg Nat) =
      .seq (.const 31 16) (.arith .add 20 20 31) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackFree,
    stackRemoveStackDelta, stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackAlloc 256 : StackProg Nat) =
      .seq
        (.seq (.const 31 2040) (.arith .sub 20 20 31))
        (.seq (.const 31 8) (.arith .sub 20 20 31)) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackAlloc,
    stackRemoveStackDelta, stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackStore 6 2 : StackProg Nat) =
      .seq (.arith .or 31 6 6)
        (.seq (.seq (.const 29 16) (.arith .add 29 20 29))
          (.inst (.mem .store 31 29))) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackStore,
    stackRemoveStackAddress, stackRemoveMove, stackRemoveJoin,
    stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackLoad 6 2 : StackProg Nat) =
      .seq (.seq (.const 29 16) (.arith .add 29 20 29))
        (.inst (.mem .load 6 29)) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackLoad,
    stackRemoveStackAddress, stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackLoadAny 6 7 : StackProg Nat) =
      .seq (.arith .add 29 20 7) (.inst (.mem .load 6 29)) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackLoadAny,
    stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.stackStoreAny 6 7 : StackProg Nat) =
      .seq (.arith .or 31 6 6)
        (.seq (.arith .add 29 20 7) (.inst (.mem .store 31 29))) := by
  simp [stackRemove, stackRemoveFuel, stackRemoveStackStoreAny,
    stackRemoveMove, stackRemoveJoin, stackRemoveTestConfig]

example :
    stackRemove stackRemoveTestConfig (.get 4 .currHeap : StackProg Nat) =
      .arith .or 4 12 12 := by
  exact stackRemove_get_currHeap _ _

example :
    stackRemove stackRemoveTestConfig
        (.seq (.get 4 .heapLength)
          (.loop (.set .handler 6)) : StackProg Nat) =
      .seq
        (.seq (.seq (.const 29 3) (.arith .add 29 10 29))
          (.inst (.mem .load 4 29)))
        (.loop (.seq (.seq (.const 29 7) (.arith .add 29 10 29))
          (.inst (.mem .store 6 29)))) := by
  change stackRemoveFuel 1024 stackRemoveTestConfig
      (.seq (.get 4 .heapLength)
        (.loop (.set .handler 6)) : StackProg Nat) = _
  simp [stackRemoveFuel, stackRemoveGet, stackRemoveJoin,
    stackRemoveAddress, stackRemoveSet, stackRemoveTestConfig,
    stackRemoveJoin, stackRemoveAddress, stackStorePosition]

end Flapjack
