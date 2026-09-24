import Flapjack.Compiler.Backend.LabProps

namespace Flapjack.Test.LabProps

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps

inductive ProbeAsm where
  | skip
  | mem (operator register : Nat) (address : Nat × Nat)
  deriving Repr, BEq, DecidableEq

abbrev ProbeAsmWithLab := AsmWithLab Nat Nat String
abbrev ProbeAsmOrCbw := AsmOrCbw ProbeAsm Nat (Nat × Nat)
abbrev ProbeLine := Line ProbeAsmOrCbw ProbeAsmWithLab Nat
abbrev ProbeSection := Section ProbeLine

def checks : AsmChecks ProbeAsm Nat (Nat × Nat) Nat :=
  { zeroWord := 0
    addr := fun register offset => (register, offset)
    store8 := 8
    instMem := ProbeAsm.mem
    asmOk
      | .skip => true
      | .mem 8 2 (1, 0) => true
      | .mem 4 3 (5, 0) => true
      | _ => false }

def asmLine (instruction : ProbeAsmOrCbw) : ProbeLine :=
  .asm instruction [1, 2] 99

def labOnlySection : ProbeSection :=
  { sectionId := 3
    lines := [.label 3 1 0, .labAsm .halt 0 [7] 19] }

def cbwSection : ProbeSection :=
  { sectionId := 4
    lines := [asmLine (.cbw 1 2), .label 4 1 0] }

#guard cbwToAsm checks (.asmi .skip) == .skip
#guard cbwToAsm checks (.cbw 1 2) == .mem 8 2 (1, 0)
#guard cbwToAsm checks (.shareMem 4 3 (5, 0)) == .mem 4 3 (5, 0)

#guard lineOkPre checks (asmLine (.asmi .skip))
#guard lineOkPre checks (asmLine (.cbw 1 2))
#guard lineOkPre checks (asmLine (.shareMem 4 3 (5, 0)))
#guard !(lineOkPre checks (asmLine (.asmi (.mem 9 2 (1, 0)))))
#guard lineOkPre checks (.label 1 2 3 : ProbeLine)
#guard lineOkPre checks (.labAsm .halt 0 [] 0 : ProbeLine)

#guard secOkPre checks labOnlySection
#guard secOkPre checks cbwSection
#guard allEncOkPre checks [labOnlySection, cbwSection]
#guard allEncOkPre checks ([] : List ProbeSection)
#guard !(allEncOkPre checks [cbwSection,
  { sectionId := 5, lines := [asmLine (.asmi (.mem 9 2 (1, 0)))] }])

end Flapjack.Test.LabProps
