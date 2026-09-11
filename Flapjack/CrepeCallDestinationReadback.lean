import Flapjack.CrepeAssignmentReadback

/-!
Destination-aware normal calls expose both the caller state produced by the
call and the flattened values written to its destination slots.  The latter
is the observation required when that call is used as a declaration-call
callee.
-/

namespace Flapjack

theorem evalCrepFullCall_returned_destinations_read_back
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (functions : List (CompiledFunction α))
    (primitive : CrepPrimitiveHandler α) (ffi : CrepFfiHandler α)
    (sharedMem : CrepSharedMemHandler α)
    (baseAddress topAddress : α) (fuel : Nat)
    (caller : CrepState α) (function : FunName)
    (destinations : List Nat) (arguments : List (CrepExp α))
    (values : List α) (parameters : List Nat) (body : CrepProg α)
    (calleeLocals : Nat → Option α) (callee : CrepState α)
    (calleeValues : List α) (callerLocals : Nat → Option α)
    (hvalues : evalCrepFullExps caller.locals caller.memory
      baseAddress topAddress arguments = some values)
    (hlookup : lookupCompiledFunction function functions =
      some (parameters, body))
    (hassign : assignCrepValues (fun _ => none) parameters values =
      some calleeLocals)
    (hcallee : evalCrepFullProg functions primitive ffi sharedMem
      baseAddress topAddress fuel
      { locals := calleeLocals, memory := caller.memory } body =
      some (.returned callee calleeValues))
    (hdestinations : assignCrepValues caller.locals destinations calleeValues =
      some callerLocals)
    (hdistinct : CrepDistinctNames destinations) :
    evalCrepFullCall functions primitive ffi sharedMem
      baseAddress topAddress (fuel + 1) caller
      (some (destinations, none)) function arguments =
      some (.normal { locals := callerLocals, memory := callee.memory }) ∧
    readCrepLocals callerLocals destinations = some calleeValues := by
  have hcall := evalCrepFullCall_returned_with_destinations
    functions primitive ffi sharedMem baseAddress topAddress fuel caller
    function destinations arguments values parameters body calleeLocals callee
    calleeValues callerLocals hvalues hlookup hassign hcallee hdestinations
  exact ⟨hcall, assignCrepValues_read_back caller.locals destinations
    calleeValues callerLocals hdestinations hdistinct⟩

end Flapjack
