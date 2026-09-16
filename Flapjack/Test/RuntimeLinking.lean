import Flapjack.Pipeline
import Flapjack.RiscV.CorrectnessBackend
import Flapjack.RiscV.ArtifactFormat

namespace Flapjack

open RiscV

#guard RiscV.cakeRuntimeWords.length == 250

#guard RiscV.cakeRuntimeBytes.length == 1000

#guard RiscV.cakeRuntimeBytes.take 4 ==
      [BitVec.ofNat 8 0xB3, BitVec.ofNat 8 0xE0,
       BitVec.ofNat 8 0xD6, BitVec.ofNat 8 0x00]

/- Direct StackLang calls name a callee by section with label zero, matching
   Cake's `INL` call destination.  Keep that alias at the linked section
   entry alongside the public function label. -/
#guard
  (labCollectProgramLabels 0
    [(labSectionNatToWord (width := 64)
      (labProgramToEntrySection 7 3 9 (.skip : StackProg Nat))) ]).head? =
    some (7, 0, 0)

example :
    RiscV.runtimeAssemblySymbolLines [] [] =
      ["    makesym(cml__Init_0, 0, 756)",
       "    makesym(cml__Halt0_1, 756, 8)",
       "    makesym(cml__Halt2_2, 764, 8)",
       "    makesym(cml__GC_3, 772, 40)",
       "    makesym(cml__Raise_4, 812, 36)",
       "    makesym(cml__StoreConsts_5, 848, 152)"] := by
  rfl

def runtimeLinkRemoveConfig : StackRemoveConfig :=
  { storeBase := 10, currHeap := 12, scratch := 31, addressScratch := 29,
    stackPointer := 20, bytesInWord := 8, stackBase := 21, wordShift := 3 }

def runtimeLinkAllocConfig : StackAllocConfig :=
  { gcStubLocation := stackGcStubLocation, returnLabel := 0,
    firstFreshLabel := stackFunctionFirstLabel }

def runtimeLinkGcConfig : StackGcConfig :=
  { shiftLength := 11, smallShiftLength := 9, lenSize := 32, wordShift := 3,
    wordBits := 64, bytesInWord := 8, immediateScratch := 31 }

example :
    (stackAllocCompileWithSimpleGcAndStoreConsts runtimeLinkAllocConfig
      runtimeLinkGcConfig stackStoreConstsStubLocation
      wordAllocatableRegisters.length
      [(3, (.storeConsts 29 30 (some stackStoreConstsStubLocation) : StackProg Nat))]).map
        Prod.fst = [1, 2, 3] := by
  rfl

example :
    (compileStackProgramNatListWithSimpleGcAndStoreConstsToRiscV (width := 64)
      { services := [] } runtimeLinkRemoveConfig runtimeLinkAllocConfig
      runtimeLinkGcConfig stackStoreConstsStubLocation
      wordAllocatableRegisters.length 0 0
      [(3, (.storeConsts 29 30 (some stackStoreConstsStubLocation) : StackProg Nat))]).isSome := by
  decide +kernel

def runtimeLinkDeclarations : List (Decl (RiscV.Word 64)) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := .return (.const (BitVec.ofNat 64 7)), returnShape := .one }]

#guard
  (compileFlapjackRiscVViaAllocatedStackWithFullSsaAndBitmapsAndSimpleGc
    (width := 64) .rv64i (BitVec.ofNat 64 8)
    (fun value => BitVec.ofNat 64 value) [] runtimeLinkRemoveConfig
    runtimeLinkDeclarations).isSome

#guard
  (compileFlapjackRiscVViaAllocatedStackWithFullSsaAndBitmapsAndSimpleGcTarget
    (width := 64) .rv64i (BitVec.ofNat 64 8)
    (fun value => BitVec.ofNat 64 value) [] runtimeLinkRemoveConfig
    runtimeLinkDeclarations).isSome

example :
    RiscV.linkRiscVFunctionsAt (0 : RiscV.Word 64) 12
      [(7, [], some ([.addi 2 0 1, .jalr 0 1 0], [])),
        (8, [2], some ([.addi 10 2 0], [10]))] =
      some [(7, 12, [], [.addi 2 0 1, .jalr 0 1 0], []),
        (8, 20, [2], [.addi 10 2 0], [10])] := by
  rfl

example :
    RiscV.linkRiscVFunctionsAt (0 : RiscV.Word 64) 12
      [(7, [], some ([.addi 2 0 1, .jalr 0 1 0], [])),
       (8, [2], some ([.addi 10 2 0], [10]))] =
      (do
        let left ← RiscV.linkRiscVFunctionsAt (0 : RiscV.Word 64) 12
          [(7, [], some ([.addi 2 0 1, .jalr 0 1 0], []))]
        let right ← RiscV.linkRiscVFunctionsAt (0 : RiscV.Word 64) 20
          [(8, [2], some ([.addi 10 2 0], [10]))]
        pure (left ++ right)) := by
  have h := RiscV.linkRiscVFunctionsAt_append_resolved
    (start := (0 : RiscV.Word 64)) (offset := 12)
    [(7, [], some ([.addi 2 0 1, .jalr 0 1 0], []))]
    [(8, [2], some ([.addi 10 2 0], [10]))] (by
      intro item hitem
      simp only [List.mem_singleton] at hitem
      subst item
      exact ⟨_, _, rfl⟩)
  simpa [RiscV.linkRiscVCodeLength] using h

example :
    RiscV.compileLinkedWordFunction
      ({ targets := [] } : RiscV.WordCallContext 64)
      (7, [], (.return 0 [] : WordProg (RiscV.Word 64))) =
      some (7, [], some ([.jalr 0 1 0], [])) := by
  apply RiscV.compileLinkedWordFunction_shape (code := []) (returns := [])
  simp [RiscV.wordFunctionToRiscVWithCallsAndLoops,
    RiscV.wordFunctionToRiscVWithCallsAndLoopsAux,
    RiscV.wordFunctionToRiscVWithCalls, RiscV.wordControlInstructions]

example :
    RiscV.compileLinkedWordFunctionWithFfi
      ({ targets := [], services := [] } : RiscV.WordCallFfiContext 64)
      (7, [], (.return 0 [] : WordProg (RiscV.Word 64))) =
      some (7, [], some ([.jalr 0 1 0], [])) := by
  apply RiscV.compileLinkedWordFunctionWithFfi_shape (code := []) (returns := [])
  simp [RiscV.wordFunctionToRiscVWithCallsAndFfiAndLoops,
    RiscV.wordFunctionToRiscVWithCallsAndFfiAndLoopsAux,
    RiscV.wordFunctionToRiscVWithCallsAndFfi,
    RiscV.wordFunctionToRiscVWithCalls, RiscV.wordControlInstructions]

example :
    (RiscV.linkRiscVFunctionsAt (0 : RiscV.Word 64) 12
      [(7, [], some ([.addi 2 0 1, .jalr 0 1 0], [])),
       (8, [2], some ([.addi 10 2 0], [10]))]).bind
      (RiscV.lookupLinkedEntry 7) = some 12 := by
  apply RiscV.lookupLinkedEntry_linkRiscVFunctionsAt_head
  rfl

example :
    (RiscV.linkRiscVFunctionsAt (0 : RiscV.Word 64) 12
      [(7, [], some ([.addi 2 0 1, .jalr 0 1 0], [])),
       (8, [2], some ([.addi 10 2 0], [10]))]).bind
        (fun linked =>
          RiscV.wordCallToRiscVLabel linked 7 [2] [10] [6] [4]) =
      some [.addi 2 6 0, .addi 31 0 12, .jalr 1 31 0, .addi 4 10 0] := by
  have h := RiscV.wordCallToRiscVLabel_linkRiscVFunctionsAt_head
    (start := (0 : RiscV.Word 64)) (offset := 12)
    (label := 7) (functionParameters := [])
    (code := [.addi 2 0 1, .jalr 0 1 0]) (functionReturns := [])
    (functions := [(8, [2], some ([.addi 10 2 0], [10]))])
    (linked := [(8, 20, [2], [.addi 10 2 0], [10])])
    (callParameters := [2]) (callReturns := [10])
    (arguments := [6]) (destinations := [4]) (by rfl)
  rw [h]
  exact RiscV.wordCallToRiscV_shape 12

example :
    RiscV.wordFunctionToRiscVWithCalls
      ({ targets := [] } : RiscV.WordCallContext 64)
      ((.move 0 [(2, 1)]) : WordProg (RiscV.Word 64)) =
      some ([.addi 2 1 0], []) := by
  simp [RiscV.wordFunctionToRiscVWithCalls,
    RiscV.wordMoveToInstructions, RiscV.wordMoveToInstructionsAux,
    RiscV.wordMoveRegisterDestinations, RiscV.wordMoveRegisterReady,
    RiscV.wordMoveRegisterRemoveDestination,
    RiscV.wordExpToInstructions, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example :
    RiscV.wordFunctionToRiscVWithCallsAndFfi
      ({ targets := [], services := [] } : RiscV.WordCallFfiContext 64)
      ((.move 0 [(2, 1)]) : WordProg (RiscV.Word 64)) =
      some ([.addi 2 1 0], []) := by
  simp [RiscV.wordFunctionToRiscVWithCallsAndFfi,
    RiscV.wordFunctionToRiscVWithCalls,
    RiscV.wordMoveToInstructions, RiscV.wordMoveToInstructionsAux,
    RiscV.wordMoveRegisterDestinations, RiscV.wordMoveRegisterReady,
    RiscV.wordMoveRegisterRemoveDestination,
    RiscV.wordExpToInstructions, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

example [NeZero width] (context : RiscV.WordCallContext width)
    (state : RiscV.State width) :
    RiscV.evalWordFunction state
        ((.move 0 [(2, 1)]) : WordProg (RiscV.Word width)) =
      some (RiscV.executeInstructions state [.addi 2 1 0], []) := by
  apply RiscV.wordFunctionToRiscVWithCalls_move_sound context state 0 [(2, 1)]
    [.addi 2 1 0]
  simp [RiscV.wordFunctionToRiscVWithCalls,
    RiscV.wordMoveToInstructions, RiscV.wordMoveToInstructionsAux,
    RiscV.wordMoveRegisterDestinations, RiscV.wordMoveRegisterReady,
    RiscV.wordMoveRegisterRemoveDestination,
    RiscV.wordExpToInstructions, RiscV.wordExpToInstruction,
    RiscV.registerOfNat]

end Flapjack
