import Flapjack.CrepeWordExpressionContract
import Flapjack.CrepeProgramRaiseCorrectness
import Flapjack.CrepeProgramStoreCorrectness
import Flapjack.CrepeProgramStoreByteCorrectness
import Flapjack.CrepeProgramGenericStoreCorrectness

/-!
Lift source-word correctness constructors for effectful Pancake statements to
the original `Exp` syntax.  These wrappers keep the semantic side conditions
explicit while removing the auxiliary `SourceWordExp` representation from
program-induction cases.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_raise_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (exception : ExceptionId) (expression : Exp α) (hword : wordExp expression)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hlookupException : ∀ (context : CompileContext α),
      ∃ exceptionCode, lookupInfo exception context.exceptions = some exceptionCode)
    (hfresh : ∀ (context : CompileContext α) (state : CrepState α),
      state.locals (context.maxVar + 1) = none)
    (hexception : ∀ (context : CompileContext α)
      (exceptionRel : ExceptionId → PanValue α → α → Prop)
      (value exceptionCode : α),
      lookupInfo exception context.exceptions = some exceptionCode →
      exceptionRel exception (.word value) exceptionCode) :
    PanValueCrepProgramCorrect (.raise exception expression) := by
  have htoExp : (sourceWordExpOf expression hword).toExp = expression :=
    sourceWordExpOf_toExp expression hword
  simpa [htoExp] using
    (panValueCrepProgramCorrect_raise_source_word exception
      (sourceWordExpOf expression hword) hbytesInWord hlookup hlookupException
      hfresh hexception)

theorem panValueCrepProgramCorrect_store32_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : Exp α) (haddress : wordExp address)
    (hvalue : wordExp value)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramCorrect (.store32 address value) := by
  have haddressToExp : (sourceWordExpOf address haddress).toExp = address :=
    sourceWordExpOf_toExp address haddress
  have hvalueToExp : (sourceWordExpOf value hvalue).toExp = value :=
    sourceWordExpOf_toExp value hvalue
  simpa [haddressToExp, hvalueToExp] using
    (panValueCrepProgramCorrect_store32_source_word
      (sourceWordExpOf address haddress) (sourceWordExpOf value hvalue)
      hbytesInWord hlookup)

theorem panValueCrepProgramCorrect_storeByte_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : Exp α) (haddress : wordExp address)
    (hvalue : wordExp value)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
    PanValueCrepProgramCorrect (.storeByte address value) := by
  have haddressToExp : (sourceWordExpOf address haddress).toExp = address :=
    sourceWordExpOf_toExp address haddress
  have hvalueToExp : (sourceWordExpOf value hvalue).toExp = value :=
    sourceWordExpOf_toExp value hvalue
  simpa [haddressToExp, hvalueToExp] using
    (panValueCrepProgramCorrect_storeByte_source_word
      (sourceWordExpOf address haddress) (sourceWordExpOf value hvalue)
      hbytesInWord hlookup)

theorem panValueCrepProgramCorrect_store_wordExp
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (address value : Exp α) (haddress : wordExp address)
    (hvalue : wordExp value)
    (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
      context.bytesInWord = bytesInWord)
    (hlookup : ∀ (context : CompileContext α)
      (sourceLocals : VarName → Option (PanValue α))
      (name : VarName) (value : PanValue α),
      sourceLocals name = some value →
      ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
    (hstable : ∀ (state : CrepState α) (baseAddress topAddress : α)
      (temporary : Nat) (compiled : CrepExp α) (value updateValue : α),
      evalCrepFullExp state.locals state.memory baseAddress topAddress compiled =
        some value →
      evalCrepFullExp
        (updateCrepLocal state.locals temporary updateValue) state.memory
        baseAddress topAddress compiled = some value) :
    PanValueCrepProgramCorrect (.store address value) := by
  have haddressToExp : (sourceWordExpOf address haddress).toExp = address :=
    sourceWordExpOf_toExp address haddress
  have hvalueToExp : (sourceWordExpOf value hvalue).toExp = value :=
    sourceWordExpOf_toExp value hvalue
  simpa [haddressToExp, hvalueToExp] using
    (panValueCrepProgramCorrect_store_source_word
      (sourceWordExpOf address haddress) (sourceWordExpOf value hvalue)
      hbytesInWord hlookup hstable)

end Flapjack
