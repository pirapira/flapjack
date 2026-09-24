import Flapjack.Compiler.Backend.LabLang

namespace Flapjack.Test.LabLang

open Flapjack.Compiler.Backend.LabLang

abbrev ProbeAsmWithLab := AsmWithLab Nat Nat String
abbrev ProbeAsmOrCbw := AsmOrCbw Nat Nat Nat
abbrev ProbeLine := Line ProbeAsmOrCbw ProbeAsmWithLab Nat Nat

def asmWithLabIndex : ProbeAsmWithLab → Nat
  | .jump _ => 0
  | .jumpCmp _ _ _ _ => 1
  | .call _ => 2
  | .locValue _ _ => 3
  | .callFFI _ => 4
  | .install => 5
  | .halt => 6

def asmWithLabFixtures : List ProbeAsmWithLab :=
  [ .jump (.lab 1 2), .jumpCmp 0 1 2 (.lab 3 4), .call (.lab 1 2)
  , .locValue 1 (.lab 2 3), .callFFI "ffi", .install, .halt ]

#guard (asmWithLabFixtures.map asmWithLabIndex) == List.range 7

def asmOrCbwIndex : ProbeAsmOrCbw → Nat
  | .asmi _ => 0
  | .cbw _ _ => 1
  | .shareMem _ _ _ => 2

def asmOrCbwFixtures : List ProbeAsmOrCbw :=
  [ .asmi 0, .cbw 1 2, .shareMem 0 1 2 ]

#guard (asmOrCbwFixtures.map asmOrCbwIndex) == List.range 3

def lineIndex : ProbeLine → Nat
  | .label _ _ _ => 0
  | .asm _ _ _ => 1
  | .labAsm _ _ _ _ => 2

def lineFixtures : List ProbeLine :=
  [ .label 1 2 3, .asm (.asmi 0) [1, 2] 3
  , .labAsm (.call (.lab 4 5)) 6 [7, 8] 9 ]

#guard (lineFixtures.map lineIndex) == List.range 3

def sectionFixture : Section ProbeLine :=
  { sectionId := 1, lines := lineFixtures }

#guard sectionFixture.sectionId == 1 && sectionFixture.lines.length == 3

example : Lab.lab 4 7 = .lab 4 7 := rfl

end Flapjack.Test.LabLang
