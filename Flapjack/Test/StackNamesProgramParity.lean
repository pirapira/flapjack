import Flapjack.Compiler.Backend.StackNames.ProgramNames
namespace Flapjack.Test.StackNamesProgramParity
open Flapjack.Compiler.Backend.StackNames Flapjack.Compiler.Backend.StackLang
private def names : Flapjack.Spt Nat := Flapjack.sptInsert 3 7 .ln
example : progCompHOL names (.seq (.halt 3) (.ret 4) : HolProg 8) = .seq (.halt 7) (.ret 4) := by
  simp [progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : progCompHOL names (.ite .equal 3 (.reg 3) (.raise 3) (.break 3) : HolProg 8) = .ite .equal 7 (.reg 7) (.raise 7) (.break 3) := by
  simp [progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup, riFindNameHOL]
example : progCompHOL names (.loop (.inst (.const 3 255)) : HolProg 8) = .loop (.inst (.const 7 255)) := by
  simp [progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup, instFindNameHOL]
example : progCompHOL names (.call none (.inr 3) none : HolProg 8) = .call none (.inr 7) none := by
  simp [progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup, destFindNameHOL]
example : progCompHOL names (.call (some (.ret 3,3,8,9)) (.inl 3) none : HolProg 8) = .call (some (.ret 7,7,8,9)) (.inl 3) none := by
  simp [progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup, destFindNameHOL]
example : progCompHOL names (.call none (.inr 4) (some (.raise 3,8,9)) : HolProg 8) = .call none (.inr 4) (some (.raise 7,8,9)) := by
  simp [progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup, destFindNameHOL]
example : progCompHOL names (.call (some (.ret 3,3,8,9)) (.inr 3) (some (.raise 3,6,7)) : HolProg 8) = .call (some (.ret 7,7,8,9)) (.inr 7) (some (.raise 7,6,7)) := by
  simp [progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup, destFindNameHOL]
example : progCompHOL names (.install 3 4 3 4 3 : HolProg 8) = .install 7 4 7 4 7 := by
  simp [progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : progCompHOL names (.shMemOp .load 3 (.addr 3 255) : HolProg 8) = .shMemOp .load 7 (.addr 7 255) := by
  simp [progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : progCompHOL names (.codeBufferWrite 3 4 : HolProg 8) = .codeBufferWrite 7 4 := by
  simp [progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : progCompHOL names (.jumpLower 3 4 3 : HolProg 8) = .jumpLower 7 4 3 := by
  simp [progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : progCompHOL names (.locValue 3 3 4 : HolProg 8) = .locValue 7 3 4 := by
  simp [progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
example : progCompHOL names (.continue 3 : HolProg 8) = .continue 3 := by
  rfl
example : progCompHOL names (.tick : HolProg 8) = .tick := by
  rfl
example : compileHOL names ([(8,.halt 3),(9,.ret 4)] : List (Nat × HolProg 8)) = [(8,.halt 7),(9,.ret 4)] := by
  simp [compileHOL, progCompEntryHOL, progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
-- HOL's section names are polymorphic (stack_names_carrier_probe compile_string_names).
example : compileHOL names ([("a",.halt 3),("b",.ret 4)] : List (String × HolProg 8)) = [("a",.halt 7),("b",.ret 4)] := by
  simp [compileHOL, progCompEntryHOL, progCompHOL, findNameSpt, names, Flapjack.sptInsert, Flapjack.sptLookup]
end Flapjack.Test.StackNamesProgramParity
