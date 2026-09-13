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

def updLocals : ProbeFact :=
  { source := "fun 1 id(1 x) { return x; } fun 1 main() { return id(7); }"
    sourceReference := "cakeml/pancake/semantics/crepSemScript.sml:66-68 (upd_locals_def)"
    cakeByteLines := 64
    cakeByteCount := 1016
    cakeFinalBytes :=
      [0x6F, 0x00, 0x40, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)
    cakeAssemblySha256 :=
      "13977258b5aaec5b4939148e04251e81d8f6e7d17ce6fcec5877b5348ebb3287" }

def emptyLocals : ProbeFact :=
  { source := "fun 1 zero() { return 7; } fun 1 main() { return zero(); }"
    sourceReference := "cakeml/pancake/semantics/crepSemScript.sml:71 (empty_locals_def)"
    cakeByteLines := 64
    cakeByteCount := 1016
    cakeFinalBytes :=
      [0x13, 0x65, 0x70, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)
    cakeAssemblySha256 :=
      "e661960e2ea04f6c804fa9487b600bb0289929ba6c76e0dd10f243263cfdd870" }

def lookupCode : ProbeFact :=
  { source := "fun 1 id(1 x) { return x; } fun 1 main() { return id(7); }"
    sourceReference := "cakeml/pancake/semantics/crepSemScript.sml:76-84 (lookup_code_def)"
    cakeByteLines := 64
    cakeByteCount := 1016
    cakeFinalBytes :=
      [0x6F, 0x00, 0x40, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)
    cakeAssemblySha256 :=
      "13977258b5aaec5b4939148e04251e81d8f6e7d17ce6fcec5877b5348ebb3287" }

def crepOp : ProbeFact :=
  { source := "fun 1 main() { return 6 * 7; }"
    sourceReference := "cakeml/pancake/semantics/crepSemScript.sml:85-88 (crep_op_def)"
    cakeByteLines := 64
    cakeByteCount := 1012
    cakeFinalBytes :=
      [0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8)
    cakeAssemblySha256 :=
      "5e1162c5f80779f9ac072963aac2d3fbbae54d565f05c46a91e4028405dbb57f" }

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
    updLocals.source ==
      "fun 1 id(1 x) { return x; } fun 1 main() { return id(7); }" &&
  emptyLocals.source ==
      "fun 1 zero() { return 7; } fun 1 main() { return zero(); }" &&
  lookupCode.source ==
      "fun 1 id(1 x) { return x; } fun 1 main() { return id(7); }" &&
    crepOp.source == "fun 1 main() { return 6 * 7; }" &&
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
    updLocals.cakeByteLines == 64 && updLocals.cakeByteCount == 1016 &&
    updLocals.cakeFinalBytes ==
      [0x6F, 0x00, 0x40, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8) &&
    updLocals.cakeAssemblySha256 ==
      "13977258b5aaec5b4939148e04251e81d8f6e7d17ce6fcec5877b5348ebb3287" &&
    emptyLocals.cakeByteLines == 64 && emptyLocals.cakeByteCount == 1016 &&
    emptyLocals.cakeFinalBytes ==
      [0x13, 0x65, 0x70, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8) &&
    emptyLocals.cakeAssemblySha256 ==
      "e661960e2ea04f6c804fa9487b600bb0289929ba6c76e0dd10f243263cfdd870" &&
    lookupCode.cakeByteLines == 64 && lookupCode.cakeByteCount == 1016 &&
    lookupCode.cakeFinalBytes ==
      [0x6F, 0x00, 0x40, 0x00, 0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8) &&
    lookupCode.cakeAssemblySha256 ==
      "13977258b5aaec5b4939148e04251e81d8f6e7d17ce6fcec5877b5348ebb3287" &&
    crepOp.cakeByteLines == 64 && crepOp.cakeByteCount == 1012 &&
    crepOp.cakeFinalBytes == [0x67, 0x80, 0x00, 0x00].map (BitVec.ofNat 8) &&
    crepOp.cakeAssemblySha256 ==
      "5e1162c5f80779f9ac072963aac2d3fbbae54d565f05c46a91e4028405dbb57f" &&
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
