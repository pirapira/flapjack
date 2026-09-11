import Flapjack.Compile

namespace Flapjack

theorem allocatedNames_slot_le
    (context : CompileContext α) (shape : Shape) (slot : Nat)
    (hslot : slot ∈ allocatedNames context shape) :
    slot ≤ context.maxVar + Shape.shapeSize shape := by
  simp only [allocatedNames, List.mem_map] at hslot
  obtain ⟨offset, hoffset, hslot⟩ := hslot
  have hoffset' := List.mem_range.1 hoffset
  omega

theorem compileContext_extend_vars_bounded
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (name : VarName) (shape : Shape)
    (hbound : ∀ oldName oldShape oldSlots,
      lookupInfo oldName context.vars = some (oldShape, oldSlots) →
      ∀ slot ∈ oldSlots, slot ≤ context.maxVar) :
    ∀ oldName oldShape oldSlots,
      lookupInfo oldName
          ((name, (shape, allocatedNames context shape)) :: context.vars) =
        some (oldShape, oldSlots) →
      ∀ slot ∈ oldSlots,
        slot ≤ context.maxVar + Shape.shapeSize shape := by
  intro oldName oldShape oldSlots hlookup
  change (if name == oldName then
      some (shape, allocatedNames context shape)
    else lookupInfo oldName context.vars) = some (oldShape, oldSlots) at hlookup
  by_cases hname : (name == oldName) = true
  · simp [hname] at hlookup
    rcases hlookup with ⟨hshape, hslots⟩
    subst oldShape
    subst oldSlots
    intro slot hslot
    exact allocatedNames_slot_le context shape slot hslot
  · simp [hname] at hlookup
    intro slot hslot
    have hslotOld := hbound oldName oldShape oldSlots hlookup slot hslot
    omega

end Flapjack
