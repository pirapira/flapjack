import Flapjack.RiscV.WordToStack

namespace Flapjack

open RiscV

def wordOperationTestConfig : WordStackConfig :=
  { locations := [(0, .register 5), (1, .register 6),
      (2, .register 7), (3, .register 8)]
    scratch := 31
    stackBase := 10 }

example :
    wordStackStoreNameNat (.bitmapBase : WordStore Nat) = some .bitmapBase := by
  rfl

example :
    wordToStackProgNat wordOperationTestConfig
        (.get 0 .heapLength : WordProg Nat) =
      some (.get 5 .heapLength) := by
  simp [wordToStackProgNat, wordStackGet, 
    wordStackStoreName, wordStackLocation, lookupNatInfo,
    wordOperationTestConfig]

example :
    wordToStackProgNat wordOperationTestConfig
        (.opCurrHeap .add 0 1 : WordProg Nat) =
      some (.opCurrHeap .add 5 6) := by
  simp [wordToStackProgNat, wordStackOpCurrHeap, wordStackReadRegister,
    wordStackLocation, lookupNatInfo, wordStackJoin,
    wordOperationTestConfig]

example :
    wordToStackProgNat wordOperationTestConfig
        (.install 0 1 2 3 ([], []) : WordProg Nat) =
      some (.install 5 6 7 8 0) := by
  simp [wordToStackProgNat, wordStackInstall, wordStackLocation,
    lookupNatInfo, wordOperationTestConfig]

/- Alloc and StoreConsts carry allocator/bitmap state which the stateless
   entrypoint cannot preserve.  They must be rejected explicitly rather than
   being replaced by a semantically successful Skip. -/
example :
    wordToStackProgNat wordOperationTestConfig
        (.alloc 0 ([], []) : WordProg Nat) = none := by
  simp [wordToStackProgNat]

example :
    wordToStackProgNat wordOperationTestConfig
        (.storeConsts 0 1 2 3 [] : WordProg Nat) = none := by
  simp [wordToStackProgNat]

example :
    wordToStackProgNat wordOperationTestConfig
        (.codeBufferWrite 0 1 : WordProg Nat) =
      some (.codeBufferWrite 5 6) := by
  simp [wordToStackProgNat, wordStackBufferWrite, wordStackLocation,
    lookupNatInfo, wordOperationTestConfig]

example :
    wordToStackProgNat wordOperationTestConfig
        (.dataBufferWrite 1 2 : WordProg Nat) =
      some (.dataBufferWrite 6 7) := by
  simp [wordToStackProgNat, wordStackBufferWrite, wordStackLocation,
    lookupNatInfo, wordOperationTestConfig]

def wordOperationSpillConfig : WordStackConfig :=
  { locations := [(0, .stack 3), (1, .register 6)]
    scratch := 31
    stackBase := 10 }

example :
    wordToStackProgNat wordOperationSpillConfig
        (.install 1 1 0 1 ([], []) : WordProg Nat) =
      some (.seq (.stackLoad 31 13)
        (.install 6 6 31 6 0)) := by
  simp [wordToStackProgNat, wordStackInstall, wordStackLocation,
    wordStackOffset, wordStackJoin, lookupNatInfo, wordOperationSpillConfig]

example :
    wordToStackProgNat
        { wordOperationSpillConfig with locations :=
            [(0, .register 5), (1, .stack 2)] }
        (.install 0 0 1 1 ([], []) : WordProg Nat) =
      some (.seq (.stackLoad 31 12)
        (.seq (.stackLoad 29 12)
          (.install 5 5 31 29 0))) := by
  simp [wordToStackProgNat, wordStackInstall, wordStackLocation,
    wordStackOffset, wordStackJoin, lookupNatInfo, wordOperationSpillConfig]

example :
    wordToStackProgNat
        { wordOperationSpillConfig with locations :=
            [(0, .register 5), (1, .register 6),
             (2, .stack 3), (3, .stack 2)] }
        (.install 0 1 2 3 ([], []) : WordProg Nat) =
      some (.seq (.stackLoad 31 13)
        (.seq (.stackLoad 29 12)
          (.install 5 6 31 29 0))) := by
  simp [wordToStackProgNat, wordStackInstall, wordStackLocation,
    wordStackOffset, wordStackJoin, lookupNatInfo, wordOperationSpillConfig]

example :
    wordToStackProgNat wordOperationSpillConfig
        (.codeBufferWrite 0 1 : WordProg Nat) =
      some (.seq (.stackLoad 29 13)
        (.codeBufferWrite 29 6)) := by
  simp [wordToStackProgNat, wordStackBufferWrite, wordStackLocation,
    wordStackOffset, wordStackJoin, lookupNatInfo, wordOperationSpillConfig]

example :
    wordToStackProgNat wordOperationSpillConfig
        (.dataBufferWrite 1 0 : WordProg Nat) =
      some (.seq (.stackLoad 31 13)
        (.dataBufferWrite 6 31)) := by
  simp [wordToStackProgNat, wordStackBufferWrite, wordStackLocation,
    wordStackOffset, wordStackJoin, lookupNatInfo, wordOperationSpillConfig]

example :
    wordToStackProgNat
        { wordOperationSpillConfig with locations :=
            [(0, .stack 3), (1, .stack 2)] }
        (.codeBufferWrite 0 1 : WordProg Nat) =
      some (.seq (.stackLoad 29 13)
        (.seq (.stackLoad 31 12)
          (.codeBufferWrite 29 31))) := by
  simp [wordToStackProgNat, wordStackBufferWrite, wordStackLocation,
    wordStackOffset, wordStackJoin, lookupNatInfo, wordOperationSpillConfig]

example :
    wordToStackProgNat wordOperationSpillConfig
        (.get 0 .heapLength : WordProg Nat) =
      some (.seq (.get 31 .heapLength) (.stackStore 31 13)) := by
  simp [wordToStackProgNat, wordStackGet, 
    wordStackStoreName, wordStackLocation, wordStackOffset, lookupNatInfo, wordStackJoin,
    wordOperationSpillConfig]

example :
    wordToStackProgNat wordOperationSpillConfig
        (.opCurrHeap .add 0 1 : WordProg Nat) =
      some (.seq (.opCurrHeap .add 31 6) (.stackStore 31 13)) := by
  simp [wordToStackProgNat, wordStackOpCurrHeap, wordStackReadRegister,
    wordStackLocation, wordStackOffset, lookupNatInfo, wordStackJoin,
    wordOperationSpillConfig]

end Flapjack
