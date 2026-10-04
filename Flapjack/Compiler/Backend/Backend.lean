import Flapjack.Compiler.Backend.SourceToFlat.Config
import Flapjack.Compiler.Backend.ClosToBvl.Config
import Flapjack.Compiler.Backend.BvlToBvi.Config
import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.WordToWord.Config
import Flapjack.Compiler.Backend.WordToWord.Compile
import Flapjack.Compiler.Backend.WordToStack.NativeConfig
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.DataToWord.MaxHeapLimit
import Flapjack.Compiler.Backend.StackToLab.Compile
import Flapjack.Compiler.Backend.LabToTarget.Compile
import Flapjack.Compiler.Backend.PresLang.Config
import Flapjack.Misc.LookupAny

namespace Flapjack.Compiler.Backend.Backend
open Flapjack Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm

/-- Complete original backend configuration. Every retained frontend/backend
field uses its reviewed concrete carrier; symbols and exported names are native
byte-backed MlStrings and all source lists and sptrees retain their constructors.
This datatype carries no type-indexed word or arbitrary placeholder field. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "config"]
structure Config where
  sourceConf : SourceToFlat.Config
  closConf : ClosToBvl.Config
  bvlConf : BvlToBvi.Config
  dataConf : DataToWord.Config
  wordToWordConf : WordToWord.Config
  wordConf : WordToStack.Native.Config
  stackConf : StackToLab.Config
  labConf : LabToTarget.Config
  symbols : List (MlString × Nat × Nat)
  tapConf : PresLang.TapConfig
  exported : List MlString

/-- The complete source attachment operation. HOL independently quantifies the
byte and bitmap payload types: neither payload is inspected. Only labConf and
symbols are updated, preserving every other configuration field. Missing names
use the original literal NOTFOUND through the reviewed lookup_any operation. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "attach_bitmaps_def"]
def attachBitmaps {Bytes Bitmaps : Type} (names : Spt MlString)
    (config : Config) (bitmaps : Bitmaps) :
    Option (Bytes × LabToTarget.Config) → Option (Bytes × Bitmaps × Config)
  | none => none
  | some (bytes, updatedLab) =>
      some (bytes, bitmaps, { config with
        labConf := updatedLab
        symbols := updatedLab.secPosLen.map fun (name, position, length) =>
          (lookupAny name names (ofString "NOTFOUND"), position, length) })

/-- Original lower laboratory pipeline. The bitmap payload is independently
polymorphic in HOL and remains arbitrary here; compilation errors are retained. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "from_lab_def"
  (words_as_type_indexed_bitvec)]
def fromLab {width : Nat} [NeZero width] {Bitmaps : Type}
    (asmConf : AsmConfigExact width) (config : Flapjack.Compiler.Backend.Backend.Config) (names : Spt MlString)
    (program : LabSem.LabProgHOL width) (bitmaps : Bitmaps) :
    Option (List (BitVec 8) × Bitmaps × Flapjack.Compiler.Backend.Backend.Config) :=
  attachBitmaps names config bitmaps
    (LabToTarget.compile asmConf config.labConf program)

/-- Original stack pipeline, including saturating heap/register subtraction,
both native address offsets, and the independently quantified bitmap payload. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "from_stack_def"
  (words_as_type_indexed_bitvec)]
def fromStack {width : Nat} [NeZero width] {Bitmaps : Type}
    (asmConf : AsmConfigExact width) (config : Flapjack.Compiler.Backend.Backend.Config) (names : Spt MlString)
    (program : List (Nat × StackLang.HolProg width)) (bitmaps : Bitmaps) :
    Option (List (BitVec 8) × Bitmaps × Flapjack.Compiler.Backend.Backend.Config) :=
  let program := StackToLab.compile config.stackConf config.dataConf
    (2 * DataToWord.maxHeapLimit width config.dataConf - 1)
    (asmConf.regCount - (asmConf.avoidRegs.length + 3)) asmConf.addrOffset program
  fromLab asmConf config names program bitmaps

/-- Original word pipeline. The frame-size tuple component is retained as
`_frames`, although HOL does not use it in this definition. Only wordConf is
updated before the complete stack/laboratory pipeline; no success premise is
introduced. The bitmap result here is specifically a list of native words. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "from_word_def"
  (words_as_type_indexed_bitvec)]
def fromWord {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (config : Flapjack.Compiler.Backend.Backend.Config) (names : Spt MlString)
    (program : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config) :=
  let (bitmaps, wordConf, _frames, program) :=
    WordToStack.Native.compileNative asmConf config.stackConf.perfCalls program
  let config := { config with wordConf := wordConf }
  fromStack asmConf config names program bitmaps

/-- Original complete word optimisation and lower-backend composition. Retain
both actual WordToWord outputs, update only its colouring oracle, and pass the
transformed program to fromWord. This source-shaped definition is proof-side;
executed pipeline routing and machine-semantics correctness remain separate. -/
@[hol "cakeml/compiler/backend/backendScript.sml" "from_word_0_def"
  (words_as_type_indexed_bitvec)]
noncomputable def fromWord0 {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (config : Flapjack.Compiler.Backend.Backend.Config)
    (names : Spt MlString) (program : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config) :=
  let (col, program) := WordToWord.compile config.wordToWordConf asmConf program
  let config := { config with wordToWordConf := { config.wordToWordConf with colOracle := col } }
  fromWord asmConf config names program

end Flapjack.Compiler.Backend.Backend
