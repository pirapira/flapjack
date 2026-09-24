import Flapjack.HolRef

/-!
# Faithful Cake StackLang syntax

This module records the generic `store_name` and `prog` datatype shapes from
`cakeml/compiler/backend/stackLangScript.sml`. It is kept separate from
`Flapjack.Stack.StackProg`, whose executable fields intentionally use Flapjack
representations such as `Nat` registers, `FunName`, and RISC-V word
instructions. The generic carriers below preserve the HOL datatype boundary
without claiming that the existing executable AST is already related to it.
The word-independent program combinator `list_Seq` is ported over this carrier.
-/

namespace Flapjack.Compiler.Backend.StackLang

/-- Exact port of HOL `stackLang$store_name`
    (`cakeml/compiler/backend/stackLangScript.sml:18-25`):

```
store_name =
  NextFree | EndOfHeap | TriggerGC | HeapLength | ProgStart | BitmapBase |
  CurrHeap | OtherHeap | AllocSize | Globals | GlobReal | Handler | GenStart |
  CodeBuffer | CodeBufferEnd | BitmapBuffer | BitmapBufferEnd |
  Temp (5 word)
```

    `store_name` is monomorphic in HOL (no type parameter) and uses one fixed
    5-bit `Temp` field, so the Lean `BitVec 5` field is the exact width-indexed
    counterpart with no further side condition. -/
@[hol "cakeml/compiler/backend/stackLangScript.sml" "store_name"]
inductive StoreName where
  | nextFree
  | endOfHeap
  | triggerGC
  | heapLength
  | progStart
  | bitmapBase
  | currHeap
  | otherHeap
  | allocSize
  | globals
  | globReal
  | handler
  | genStart
  | codeBuffer
  | codeBufferEnd
  | bitmapBuffer
  | bitmapBufferEnd
  | temp (value : BitVec 5)
  deriving Repr

/-- HOL `stackLang$prog`, with its imported HOL carrier types explicit.

NOT TAGGED (exact HOL `stackLang$prog` differs in carrier arity): HOL
`stackLangScript.sml:27-66` parameterises `prog` by a SINGLE shared word type
`'a`, with the fields typed by `asm$inst`, `asm$reg_imm`, `asm$addr`, and the
monomorphic `asm$binop`/`asm$cmp`/`asm$memop`/`mlstring`; the Lean carrier has
SEVEN independent type parameters, so it is a strict generalisation rather than
the HOL datatype. An exact width-indexed tag needs the asm syntax carriers
(`reg_imm`, `addr`, `inst`, `arith`, `fp`) ported first, tracked by
`flapjack-pxn.18.5.15.3.11`. The `StoreName` carrier above and the word-
independent combinators over this generic `Prog` are unaffected.

The target of `Call` is `num + num`, represented by `Sum Nat Nat`; the two
optional continuations retain their distinct tuple arities. -/
inductive Prog (Inst Cmp RegImm Binop Memop Addr MlString : Type) where
  | skip
  | inst (instruction : Inst)
  | get (destination : Nat) (store : StoreName)
  | set (store : StoreName) (source : Nat)
  | opCurrHeap (operator : Binop) (destination source : Nat)
  | call (returnHandler : Option (Prog Inst Cmp RegImm Binop Memop Addr MlString ×
        Nat × Nat × Nat))
      (target : Sum Nat Nat)
      (handler : Option (Prog Inst Cmp RegImm Binop Memop Addr MlString ×
        Nat × Nat))
  | seq (first second : Prog Inst Cmp RegImm Binop Memop Addr MlString)
  | ite (operator : Cmp) (condition : Nat) (right : RegImm)
      (thenBranch elseBranch : Prog Inst Cmp RegImm Binop Memop Addr MlString)
  | loop (body : Prog Inst Cmp RegImm Binop Memop Addr MlString)
  | jumpLower (left right target : Nat)
  | alloc (words : Nat)
  | storeConsts (source bitmap : Nat) (stub : Option Nat)
  | raise (exception : Nat)
  | ret (value : Nat)
  | break (label : Nat)
  | continue (label : Nat)
  | ffi (function : MlString) (configuration configurationLength array arrayLength returnAddress : Nat)
  | tick
  | locValue (destination label entry : Nat)
  | install (codeBuffer codeLength dataBuffer dataLength returnAddress : Nat)
  | shMemOp (operator : Memop) (register : Nat) (address : Addr)
  | codeBufferWrite (address value : Nat)
  | dataBufferWrite (address value : Nat)
  | rawCall (target : Nat)
  | stackAlloc (words : Nat)
  | stackFree (words : Nat)
  | stackStore (offset register : Nat)
  | stackStoreAny (register offsetRegister : Nat)
  | stackLoad (offset register : Nat)
  | stackLoadAny (register offsetRegister : Nat)
  | stackGetSize (register : Nat)
  | stackSetSize (register : Nat)
  | bitmapLoad (destination address : Nat)
  | halt (register : Nat)
  deriving Repr

/-- Untagged structural analogue of HOL `list_Seq_def`
    (`cakeml/compiler/backend/stackLangScript.sml:86`):

```
(list_Seq [] = Skip) /\
(list_Seq [x] = x) /\
(list_Seq (x::y::xs) = Seq x (list_Seq (y::xs)))
```

    `list_Seq` builds the right-associated `Seq` chain of a program list, the
    canonical stackLang combinator used by the Word-to-Stack stubs and
    `compile_prog`.  HOL `list_Seq` is polymorphic in the word type `'a` and
    touches only the word-independent `Skip`/`Seq` constructors, whose fields are
    the program itself; the Lean definition is correspondingly polymorphic in the
    carrier's type parameters (`Inst`/`Cmp`/`RegImm`/`Binop`/`Memop`/`Addr`/
    `MlString`) and uses none of them. HOL's `prog` has one shared word type,
    whereas this carrier admits seven independent types; the exact tagged
    statement awaits the width-indexed `prog` carrier. -/
def listSeq {Inst Cmp RegImm Binop Memop Addr MlString : Type} :
    List (Prog Inst Cmp RegImm Binop Memop Addr MlString) →
      Prog Inst Cmp RegImm Binop Memop Addr MlString
  | [] => .skip
  | [x] => x
  | x :: y :: xs => .seq x (listSeq (y :: xs))

namespace Prog

/-- Carrier-changing structural map for `Prog`: applies one function to each of
the seven type parameters.  Used by the bridge in
`Flapjack.Compiler.Backend.MlStringBridge` to convert the exact
`HolProg` (`MlString` FFI) into the executable `ProgW` (`String` FFI) and back. -/
def map {Inst Cmp RegImm Binop Memop Addr MlString
         Inst' Cmp' RegImm' Binop' Memop' Addr' MlString' : Type}
    (fInst : Inst → Inst') (fCmp : Cmp → Cmp') (fRegImm : RegImm → RegImm')
    (fBinop : Binop → Binop') (fMemop : Memop → Memop') (fAddr : Addr → Addr')
    (fMlString : MlString → MlString') :
    Prog Inst Cmp RegImm Binop Memop Addr MlString →
      Prog Inst' Cmp' RegImm' Binop' Memop' Addr' MlString'
  | .skip => .skip
  | .inst i => .inst (fInst i)
  | .get d s => .get d s
  | .set s x => .set s x
  | .opCurrHeap b d s => .opCurrHeap (fBinop b) d s
  | .call rh t h =>
      .call (match rh with
              | none => none
              | some (returnProgram, linkRegister, returnSection, returnLabel) =>
                  some (map fInst fCmp fRegImm fBinop fMemop fAddr fMlString returnProgram,
                        linkRegister, returnSection, returnLabel))
            t
            (match h with
             | none => none
             | some (handlerProgram, handlerSection, handlerLabel) =>
                 some (map fInst fCmp fRegImm fBinop fMemop fAddr fMlString handlerProgram,
                       handlerSection, handlerLabel))
  | .seq a b => .seq (map fInst fCmp fRegImm fBinop fMemop fAddr fMlString a)
      (map fInst fCmp fRegImm fBinop fMemop fAddr fMlString b)
  | .ite c condition r t e => .ite (fCmp c) condition (fRegImm r)
      (map fInst fCmp fRegImm fBinop fMemop fAddr fMlString t)
      (map fInst fCmp fRegImm fBinop fMemop fAddr fMlString e)
  | .loop b => .loop (map fInst fCmp fRegImm fBinop fMemop fAddr fMlString b)
  | .jumpLower a b c => .jumpLower a b c
  | .alloc n => .alloc n
  | .storeConsts a b c => .storeConsts a b c
  | .raise n => .raise n
  | .ret n => .ret n
  | .break n => .break n
  | .continue n => .continue n
  | .ffi f cfg cl arr al ra => .ffi (fMlString f) cfg cl arr al ra
  | .tick => .tick
  | .locValue d l e => .locValue d l e
  | .install a b c d e => .install a b c d e
  | .shMemOp op r addr => .shMemOp (fMemop op) r (fAddr addr)
  | .codeBufferWrite a b => .codeBufferWrite a b
  | .dataBufferWrite a b => .dataBufferWrite a b
  | .rawCall n => .rawCall n
  | .stackAlloc n => .stackAlloc n
  | .stackFree n => .stackFree n
  | .stackStore o r => .stackStore o r
  | .stackStoreAny r o => .stackStoreAny r o
  | .stackLoad o r => .stackLoad o r
  | .stackLoadAny r o => .stackLoadAny r o
  | .stackGetSize r => .stackGetSize r
  | .stackSetSize r => .stackSetSize r
  | .bitmapLoad d a => .bitmapLoad d a
  | .halt r => .halt r
termination_by p => sizeOf p
decreasing_by all_goals decreasing_trivial

end Prog

end Flapjack.Compiler.Backend.StackLang
