/-!
# Original Pancake probe facts

The inputs in `Flapjack/Test/OriginalPancake/*.pnk` are run through the
authoritative CakeML Pancake compiler with:

```
scripts/probe-original-pancake.sh INPUT.pnk OUTPUT.cake.S
```

The facts below are copied from those generated RISC-V assembly outputs.  A
`.byte` line contains sixteen bytes except for the final line; therefore the
recorded line count and terminal bytes pin the complete machine-code stream's
size and its ending.  The source references identify the original semantic
equations exercised by each probe.
-/

namespace Flapjack.Test.OriginalPancakeProbes

structure ProbeFact where
  source : String
  sourceReference : String
  cakeByteLines : Nat
  cakeByteCount : Nat
  cakeFinalBytes : List (BitVec 8)
  cakeAssemblySha256 : String
deriving Repr

def setVar : ProbeFact :=
  { source := "fun 1 main() { var 1 x = 7; var 1 x = 11; return x; }"
    sourceReference := "cakeml/pancake/semantics/crepSemScript.sml:55-57 (set_var_def)"
    cakeByteLines := 64
    cakeByteCount := 1012
    cakeFinalBytes :=
      [0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)
    cakeAssemblySha256 :=
      "14ee212eefbbc8ba96af33c6372dcde8bc6b2c4babe72779e3124f2df1cd21b1" }

def setGlobals : ProbeFact :=
  { source := "var 1 g = 7; fun 1 main() { return g; }"
    sourceReference := "cakeml/pancake/semantics/crepSemScript.sml:61-63 (set_globals_def)"
    cakeByteLines := 66
    cakeByteCount := 1048
    cakeFinalBytes :=
      [0x03, 0x35, 0x85, 0xFF, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)
    cakeAssemblySha256 :=
      "1281f0d8cd5e1a22486f15baa4a4526e000645f2abec8fb6893e64603b606ac9" }

def evaluateDecls : ProbeFact :=
  { source := "var 1 g = 41; fun 1 main() { return g; }"
    sourceReference :=
      "cakeml/pancake/semantics/panSemScript.sml:814-837 (evaluate_decls_def)"
    cakeByteLines := 66
    cakeByteCount := 1048
    cakeFinalBytes :=
      [0x03, 0x35, 0x85, 0xFF, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)
    cakeAssemblySha256 :=
      "9b71ab937453e4ded03220a808b551c60bb5ef189387ae0865ba12befccd40fb" }

def decsStcnames : ProbeFact :=
  { source := "struct Pair { 1 left, 1 right } fun 1 main() { return 0; }"
    sourceReference :=
      "cakeml/pancake/semantics/panSemScript.sml:839-859 (decs_stcnames_def)"
    cakeByteLines := 64
    cakeByteCount := 1012
    cakeFinalBytes :=
      [0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)
    cakeAssemblySha256 :=
      "0988fae715209e66b753a42b1b7199b6297cc7389080bea6593d8cb2e8a019fa" }

def semanticsDecls : ProbeFact :=
  { source :=
      "var 1 g = 41; struct Pair { 1 left, 1 right } fun 1 main() { return g; }"
    sourceReference :=
      "cakeml/pancake/semantics/panSemScript.sml:861-871 (semantics_decls_def)"
    cakeByteLines := 66
    cakeByteCount := 1048
    cakeFinalBytes :=
      [0x03, 0x35, 0x85, 0xFF, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)
    cakeAssemblySha256 :=
      "9b71ab937453e4ded03220a808b551c60bb5ef189387ae0865ba12befccd40fb" }

def sourceFactsPinned : Bool :=
  setVar.source == "fun 1 main() { var 1 x = 7; var 1 x = 11; return x; }" &&
    setGlobals.source == "var 1 g = 7; fun 1 main() { return g; }" &&
    evaluateDecls.source == "var 1 g = 41; fun 1 main() { return g; }" &&
    decsStcnames.source == "struct Pair { 1 left, 1 right } fun 1 main() { return 0; }" &&
    semanticsDecls.source ==
      "var 1 g = 41; struct Pair { 1 left, 1 right } fun 1 main() { return g; }"

def outputFactsPinned : Bool :=
  setVar.cakeByteLines == 64 && setVar.cakeByteCount == 1012 &&
    setVar.cakeFinalBytes == [0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8) &&
    setVar.cakeAssemblySha256 ==
      "14ee212eefbbc8ba96af33c6372dcde8bc6b2c4babe72779e3124f2df1cd21b1" &&
    setGlobals.cakeByteLines == 66 && setGlobals.cakeByteCount == 1048 &&
    setGlobals.cakeFinalBytes ==
      [0x03, 0x35, 0x85, 0xFF, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8) &&
    setGlobals.cakeAssemblySha256 ==
      "1281f0d8cd5e1a22486f15baa4a4526e000645f2abec8fb6893e64603b606ac9" &&
    evaluateDecls.cakeByteLines == 66 && evaluateDecls.cakeByteCount == 1048 &&
    evaluateDecls.cakeFinalBytes ==
      [0x03, 0x35, 0x85, 0xFF, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8) &&
    evaluateDecls.cakeAssemblySha256 ==
      "9b71ab937453e4ded03220a808b551c60bb5ef189387ae0865ba12befccd40fb" &&
    decsStcnames.cakeByteLines == 64 && decsStcnames.cakeByteCount == 1012 &&
    decsStcnames.cakeFinalBytes == [0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8) &&
    decsStcnames.cakeAssemblySha256 ==
      "0988fae715209e66b753a42b1b7199b6297cc7389080bea6593d8cb2e8a019fa" &&
    semanticsDecls.cakeByteLines == 66 && semanticsDecls.cakeByteCount == 1048 &&
    semanticsDecls.cakeFinalBytes ==
      [0x03, 0x35, 0x85, 0xFF, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8) &&
    semanticsDecls.cakeAssemblySha256 ==
      "9b71ab937453e4ded03220a808b551c60bb5ef189387ae0865ba12befccd40fb"

#guard sourceFactsPinned
#guard outputFactsPinned

end Flapjack.Test.OriginalPancakeProbes
