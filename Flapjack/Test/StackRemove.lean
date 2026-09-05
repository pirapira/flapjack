import Flapjack.StackRemove

namespace Flapjack

def stackRemoveTestConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29 }

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
