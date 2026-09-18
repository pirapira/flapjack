import Flapjack.CrepeProgramInduction
import Flapjack.CrepeWordProgramCases
import Flapjack.CrepeWordEffectProgramCases
import Flapjack.CrepeWordLoopProgramCase
import Flapjack.CrepeWordExtCallProgramCase

/-!
An induction assembly for the stateful source-to-Crep correctness boundary.

`panValueCrepProgramStateCorrect_induction` is intentionally fully generic:
its constructor hypotheses are useful when a new source case is being proved,
but they do not describe the supported Pancake fragment as a whole.  The
predicate below records the fragment for which the existing Cake-faithful
stateful constructor theorems are already available.  In particular, the
expression side is restricted to `wordExp`, while all state, local-slot,
exception, loop-safety, and FFI obligations remain explicit in the
constructors that need them.

This is an induction assembly, not a replacement for the HOL
`pc_compile_correct` theorem: unsupported calls, declaration calls, and
structured expressions remain outside the predicate and must acquire their
own Cake-equivalent constructors before they can be admitted here.
-/

namespace Flapjack

inductive StatefulWordProg (α : Type)
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α] :
    Prog α → Prop where
  | skip : StatefulWordProg α (.skip : Prog α)
  | tick : StatefulWordProg α (.tick : Prog α)
  | controlBreak : StatefulWordProg α (.break : Prog α)
  | controlContinue : StatefulWordProg α (.continue : Prog α)
  | annot (tag text : String) :
      StatefulWordProg α (.annot tag text : Prog α)
  | returnConst (value : α) :
      StatefulWordProg α (.return (.const value) : Prog α)
  | returnWord
      (expression : Exp α) (hword : wordExp expression)
      (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
        context.bytesInWord = bytesInWord)
      (hlookup : ∀ (context : CompileContext α)
        (sourceLocals : VarName → Option (PanValue α))
        (name : VarName) (value : PanValue α),
        sourceLocals name = some value →
        ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
      StatefulWordProg α (.return expression)
  | seq {first second : Prog α} :
      StatefulWordProg α first →
      StatefulWordProg α second →
      StatefulWordProg α (.seq first second)
  | iteWord
      (condition : Exp α) (hcondition : wordExp condition)
      (thenBranch elseBranch : Prog α)
      (hthen : StatefulWordProg α thenBranch)
      (helse : StatefulWordProg α elseBranch)
      (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
        context.bytesInWord = bytesInWord)
      (hlookup : ∀ (context : CompileContext α)
        (sourceLocals : VarName → Option (PanValue α))
        (name : VarName) (value : PanValue α),
        sourceLocals name = some value →
        ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
      StatefulWordProg α (.ite condition thenBranch elseBranch)
  | whileWord
      (condition : Exp α) (hcondition : wordExp condition)
      (body : Prog α)
      (hbody : StatefulWordProg α body)
      (hbodySafe : PanValueCrepProgramLoopStateControlSafe (α := α) body)
      (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
        context.bytesInWord = bytesInWord)
      (hlookup : ∀ (context : CompileContext α)
        (sourceLocals : VarName → Option (PanValue α))
        (name : VarName) (value : PanValue α),
        sourceLocals name = some value →
        ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
      StatefulWordProg α (.while condition body)
  | raiseWord
      (exception : ExceptionId) (expression : Exp α)
      (hword : wordExp expression)
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
      StatefulWordProg α (.raise exception expression)
  | storeWord
      (address value : Exp α)
      (haddress : wordExp address) (hvalue : wordExp value)
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
      StatefulWordProg α (.store address value)
  | store32Word
      (address value : Exp α)
      (haddress : wordExp address) (hvalue : wordExp value)
      (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
        context.bytesInWord = bytesInWord)
      (hlookup : ∀ (context : CompileContext α)
        (sourceLocals : VarName → Option (PanValue α))
        (name : VarName) (value : PanValue α),
        sourceLocals name = some value →
        ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
      StatefulWordProg α (.store32 address value)
  | storeByteWord
      (address value : Exp α)
      (haddress : wordExp address) (hvalue : wordExp value)
      (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
        context.bytesInWord = bytesInWord)
      (hlookup : ∀ (context : CompileContext α)
        (sourceLocals : VarName → Option (PanValue α))
        (name : VarName) (value : PanValue α),
        sourceLocals name = some value →
        ∃ slot, lookupInfo name context.vars = some (.one, [slot])) :
      StatefulWordProg α (.storeByte address value)
  | extCallWord
      (function : FunName)
      (configuration configurationLength array arrayLength : Exp α)
      (hconfiguration : wordExp configuration)
      (hconfigurationLength : wordExp configurationLength)
      (harray : wordExp array) (harrayLength : wordExp arrayLength)
      (hffi : ∀ (sourceHandler : PanValueFfiHandler α)
        (ffi : CrepFfiHandler α) (temporaryBase : Nat),
        panValueCrepExtCallCorrectAt temporaryBase sourceHandler ffi)
      (hbytesInWord : ∀ (context : CompileContext α) (bytesInWord : α),
        context.bytesInWord = bytesInWord)
      (hlookup : ∀ (context : CompileContext α)
        (sourceLocals : VarName → Option (PanValue α))
        (name : VarName) (value : PanValue α),
        sourceLocals name = some value →
        ∃ slot, lookupInfo name context.vars = some (.one, [slot]))
      (hfresh : ∀ (context : CompileContext α) (expression : SourceWordExp α)
        (compiled : CrepExp α),
        compileExp context expression.toExp = ([compiled], .one) →
        ∀ temporary, temporary ∉ crepExpVars compiled) :
      StatefulWordProg α
        (.extCall function configuration configurationLength array arrayLength)

theorem panValueCrepProgramStateCorrect_statefulWord
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (program : Prog α) (hprogram : StatefulWordProg α program) :
    PanValueCrepProgramStateCorrect program := by
  induction hprogram with
  | skip => exact panValueCrepProgramStateCorrect_skip
  | tick => exact panValueCrepProgramStateCorrect_tick
  | controlBreak => exact panValueCrepProgramStateCorrect_break
  | controlContinue => exact panValueCrepProgramStateCorrect_continue
  | annot tag text => exact panValueCrepProgramStateCorrect_annot tag text
  | returnConst value => exact panValueCrepProgramStateCorrect_return_const value
  | returnWord expression hword hbytesInWord hlookup =>
      exact panValueCrepProgramStateCorrect_return_wordExp expression hword
        hbytesInWord hlookup
  | @seq first second hfirst hsecond ihfirst ihsecond =>
      exact panValueCrepProgramStateCorrect_seq first second ihfirst ihsecond
  | iteWord condition hcondition thenBranch elseBranch hthen helse
      hbytesInWord hlookup ihthen ihelse =>
      exact panValueCrepProgramStateCorrect_ite_wordExp condition hcondition
        thenBranch elseBranch ihthen ihelse hbytesInWord hlookup
  | whileWord condition hcondition body hbody hbodySafe hbytesInWord hlookup ihbody =>
      exact panValueCrepProgramStateCorrect_while_wordExp condition hcondition
        body ihbody hbodySafe hbytesInWord hlookup
  | raiseWord exception expression hword hbytesInWord hlookup hlookupException
      hfresh hexception =>
      exact panValueCrepProgramStateCorrect_raise_wordExp exception expression
        hword hbytesInWord hlookup hlookupException hfresh hexception
  | storeWord address value haddress hvalue hbytesInWord hlookup hstable =>
      exact panValueCrepProgramStateCorrect_store_wordExp address value
        haddress hvalue hbytesInWord hlookup hstable
  | store32Word address value haddress hvalue hbytesInWord hlookup =>
      exact panValueCrepProgramStateCorrect_store32_wordExp address value
        haddress hvalue hbytesInWord hlookup
  | storeByteWord address value haddress hvalue hbytesInWord hlookup =>
      exact panValueCrepProgramStateCorrect_storeByte_wordExp address value
        haddress hvalue hbytesInWord hlookup
  | extCallWord function configuration configurationLength array arrayLength
      hconfiguration hconfigurationLength harray harrayLength hffi hbytesInWord
      hlookup hfresh =>
      exact panValueCrepProgramStateCorrect_extCall_wordExp function
        configuration configurationLength array arrayLength hconfiguration
        hconfigurationLength harray harrayLength hffi hbytesInWord hlookup hfresh

end Flapjack
