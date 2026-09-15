import Flapjack.LoopAnalysis
import Flapjack.NumSet

/-!
The Word intermediate language used by CakeML's backend. This first port
keeps the register-level instruction set small but preserves the structure
needed by `loop_to_word`: words, register expressions, memory instructions,
calls, loops, and foreign calls.
-/

namespace Flapjack

inductive WordStore (α : Type u) where
  | temp (address : α)
  | nextFree
  | endOfHeap
  | triggerGC
  | currHeap
  | heapLength
  | progStart
  | bitmapBase
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
  deriving DecidableEq, Repr

inductive WordExp (α : Type u) where
  | const (value : α)
  | var (name : Nat)
  | lookup (store : WordStore α)
  | load (address : WordExp α)
  | op (operator : BinOp) (args : List (WordExp α))
  | shift (operator : Shift) (left right : WordExp α)
  deriving Repr

inductive WordRegImm (α : Type u) where
  | imm (value : α)
  | reg (name : Nat)
  deriving DecidableEq, Repr

inductive WordArith where
  | longMul (destinationLeft destinationRight sourceLeft sourceRight : Nat)
  | longDiv (destinationLeft destinationRight sourceLeft sourceRight quotient : Nat)
  | addCarry (destination resultCarry sourceLeft sourceRight carryIn : Nat)
  /- CakeML WordLang's AddCarry has four registers: r1 is the sum
     destination, r2/r3 are the addends, and r4 is both carry input and
     carry output.  Keep this distinct from Pancake's five-register
     two-result primitive so the compiler boundary cannot silently encode a
     different operation. -/
  | cakeAddCarry (destination sourceLeft sourceRight carry : Nat)
  | div (destination dividend divisor : Nat)
  deriving DecidableEq, Repr

inductive WordMemOp where
  | load
  | load8
  | load16
  | load32
  | store
  | store8
  | store16
  | store32
  deriving DecidableEq, Repr

inductive WordInst where
  | arith (operation : WordArith)
  | mem (operator : WordMemOp) (destination address : Nat)
  deriving DecidableEq, Repr

inductive WordProg (α : Type u) where
  | skip
  | move (priority : Nat) (moves : List (Nat × Nat))
  | assign (name : Nat) (value : WordExp α)
  | inst (instruction : WordInst)
  | get (destination : Nat) (store : WordStore α)
  | store (address : WordExp α) (value : Nat)
  | set (store : WordStore α) (value : WordExp α)
  | seq (first second : WordProg α)
  | ite (operator : Cmp) (condition : Nat) (right : WordRegImm α)
      (thenBranch elseBranch : WordProg α)
  | loop (liveIn : List Nat) (body : WordProg α) (liveOut : List Nat)
  | mustTerminate (body : WordProg α)
  | break (label : Nat)
  | continue (label : Nat)
  | raise (exception : Nat)
  | return (label : Nat) (values : List Nat)
  | tick
  | locValue (destination source : Nat)
  /- CakeML's WordLang call metadata consists of returned registers, the
     normal/exception cut sets, a return-handler program, and the two labels
     used by the handler.  Keeping all five fields here is important: the
     allocator and StackLang lowering use the cut sets to establish the
     caller boundary and the handler program/labels to preserve control flow.
     The reduced Loop carrier is lifted to this shape by `loopToWordProg`
     until the Loop syntax itself is migrated to the exact carrier. -/
  | call (returns : Option
      (List Nat × (List Nat × List Nat) × WordProg α × Nat × Nat))
      (target : Option Nat) (arguments : List Nat)
      (handler : Option (Nat × WordProg α × Nat × Nat))
  | alloc (destination : Nat) (cutsets : List Nat × List Nat)
  | storeConsts (source bitmap codeLength dataLength : Nat)
      (constants : List (Bool × α))
  | opCurrHeap (operator : BinOp) (destination source : Nat)
  | install (codeBuffer codeLength dataBuffer dataLength : Nat)
      (cutsets : List Nat × List Nat)
  | codeBufferWrite (address value : Nat)
  | dataBufferWrite (address value : Nat)
  | ffi (function : FunName) (configuration configurationLength array arrayLength : Nat)
      (live : List Nat × List Nat)
  | shareInst (operator : WordMemOp) (name : Nat) (address : WordExp α)
  deriving Repr

structure WordContext where
  vars : NatInfoMap Nat
  deriving DecidableEq, Repr

def wordFindVar (context : WordContext) (name : Nat) : Nat :=
  match lookupNatInfo name context.vars with
  | some value => value
  | none => name

def wordMapVars (context : WordContext) : List Nat → List Nat
  | [] => []
  | name :: names => wordFindVar context name :: wordMapVars context names

/-! `comp_def` rebuilds loop live sets through `mk_new_cutset`, retaining
    register zero and removing duplicates after context mapping. -/
def wordToNumSet : List Nat → List Nat
  | [] => []
  | name :: names => loopInsert name (wordToNumSet names)

def wordMkNewCutset (context : WordContext) (live : List Nat) : List Nat :=
  /- This is CakeML's `mk_new_cutset_def`, not merely a list-set map:
     `fromNumSet` exposes the source Patricia-tree traversal order before
     context registers are mapped and rebuilt with `toNumSet`. -/
  loopInsert 0
    (Flapjack.NumSet.toSet
      ((Flapjack.NumSet.fromList live).map (wordFindVar context)))

def wordRegImm (context : WordContext) : RegImm α → WordRegImm α
  | .imm value => .imm value
  | .reg name => .reg (wordFindVar context name)

def wordArith (context : WordContext) : LoopArith → WordArith
  | .longMul left right sourceLeft sourceRight =>
      .longMul (wordFindVar context left) (wordFindVar context right)
        (wordFindVar context sourceLeft) (wordFindVar context sourceRight)
  | .longDiv left right sourceLeft sourceRight quotient =>
      .longDiv (wordFindVar context left) (wordFindVar context right)
        (wordFindVar context sourceLeft) (wordFindVar context sourceRight)
        (wordFindVar context quotient)
  | .div destination dividend divisor =>
      .div (wordFindVar context destination) (wordFindVar context dividend)
        (wordFindVar context divisor)

def wordMemOp : CrepMemOp → Option WordMemOp
  | .load => some .load
  | .load8 => some .load8
  | .load16 => some .load16
  | .load32 => some .load32
  | .store => some .store
  | .store8 => some .store8
  | .store16 => some .store16
  | .store32 => some .store32

def loopToWordExp [OfNat α 1] : LoopExp α → Option (WordExp α)
  | .const value => some (.const value)
  | .var name => some (.var name)
  | .lookup address => some (.lookup (.temp address))
  | .load address => (loopToWordExp address).map .load
  | .op operator arguments =>
      (loopToWordExpList arguments).map (.op operator)
  | .crepOp _ _ => none
  | .cmp _ _ _ => none
  | .shift operator left right => do
      let left ← loopToWordExp left
      let right ← loopToWordExp right
      pure (.shift operator left right)
  | .baseAddr => some (.lookup .currHeap)
  | .topAddr => some (.op .add
      [.lookup .currHeap,
       .shift .lsl (.lookup .heapLength) (.const (by exact 1))])
termination_by expression => sizeOf expression
where
  loopToWordExpList [OfNat α 1] : List (LoopExp α) → Option (List (WordExp α))
    | [] => some []
    | expression :: expressions => do
        let expression ← loopToWordExp expression
        let expressions ← loopToWordExpList expressions
        pure (expression :: expressions)
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def loopToWordExpList [OfNat α 1] (expressions : List (LoopExp α)) :
    Option (List (WordExp α)) :=
  loopToWordExp.loopToWordExpList expressions

def wordCompileExp [OfNat α 1] (context : WordContext) :
    LoopExp α → Option (WordExp α)
  | .const value => some (.const value)
  | .var name => some (.var (wordFindVar context name))
  | .lookup address => some (.lookup (.temp address))
  | .load address => (wordCompileExp context address).map .load
  | .op operator arguments =>
      (wordCompileExpList context arguments).map (.op operator)
  | .crepOp _ _ => none
  | .cmp _ _ _ => none
  | .shift operator left right => do
      let left ← wordCompileExp context left
      let right ← wordCompileExp context right
      pure (.shift operator left right)
  | .baseAddr => some (.lookup .currHeap)
  | .topAddr => some (.op .add
      [.lookup .currHeap,
       .shift .lsl (.lookup .heapLength) (.const (by exact 1))])
termination_by expression => sizeOf expression
where
  wordCompileExpList [OfNat α 1] (context : WordContext) :
      List (LoopExp α) → Option (List (WordExp α))
    | [] => some []
    | expression :: expressions => do
        let expression ← wordCompileExp context expression
        let expressions ← wordCompileExpList context expressions
        pure (expression :: expressions)
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def wordCompileExpWithContext [OfNat α 1] (context : WordContext)
    (expression : LoopExp α) : Option (WordExp α) :=
  wordCompileExp context expression

/-! The original Pancake compiler discards statements that follow an
    unconditional control transfer inside a statement sequence, so its lowered
    word program never carries unreachable continuations.  A `.seq` whose first
    component ends in a transfer is terminal itself, hence the recursion in
    `wordProgIsTerminal`.  `wordProgDCE` mirrors that discarding as a pass over
    an already lowered program; keeping it separate from `loopToWordProg`
    preserves the raw translation used by the correctness proofs. -/
def wordProgIsTerminal : WordProg α → Bool
  | .raise _ | .return _ _ | .break _ | .continue _ => true
  | .call none _ _ _ => true
  | .seq _ second => wordProgIsTerminal second
  | _ => false

def wordProgDCE : WordProg α → WordProg α
  | .seq first second =>
      let first := wordProgDCE first
      if wordProgIsTerminal first then first
      else .seq first (wordProgDCE second)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right
        (wordProgDCE thenBranch) (wordProgDCE elseBranch)
  | .loop liveIn body liveOut =>
      .loop liveIn (wordProgDCE body) liveOut
  | .mustTerminate body => .mustTerminate (wordProgDCE body)
  /- The call continuation program is `.skip` at this pipeline stage; only the
     exception-handler body can carry a reachable sub-program. -/
  | .call returns target arguments (some (exception, handlerProg, l1, l2)) =>
      .call returns target arguments
        (some (exception, wordProgDCE handlerProg, l1, l2))
  | .call returns target arguments none =>
      .call returns target arguments none
  | program => program
  termination_by program => sizeOf program
  decreasing_by
    all_goals decreasing_trivial

/-- Label-threading core of `loop_to_word$comp`
    (`cakeml/pancake/loop_to_wordScript.sml:64-150`).  `sectionLabel` is the
    constant first label component (the function name in CakeML's
    `comp_func`); the returned counter is the threaded second component.
    Handled calls append a `Tick`, compile the normal-return handler into
    the return slot, and receive fresh labels; tail calls drop their
    handler and prepend register `0` to the arguments, exactly as the
    source. -/
def loopToWordProgFrom [OfNat α 1] (context : WordContext) (sectionLabel : Nat) :
    Nat → LoopProg α → WordProg α × Nat
  | counter, .skip => (.skip, counter)
  | counter, .assign name value =>
      match wordCompileExp context value with
      | some value => (.assign (wordFindVar context name) value, counter)
      | none => (.skip, counter)
  | counter, .primitive [result, resultCarry] .addCarry [left, right, carryIn] =>
      /- Keep the carry input explicit at this boundary.  CakeML's
         loop_to_word pass lowers this to virtual scratch registers 1 and 3,
         but Flapjack has not yet ported the subsequent word allocator.  The
         RISC-V instruction selector can lower this five-register Word
         operation directly using its architectural x31 scratch, preserving
         the x1 link register for call-aware code. -/
      (.inst (.arith (.addCarry (wordFindVar context result)
        (wordFindVar context resultCarry) (wordFindVar context left)
        (wordFindVar context right) (wordFindVar context carryIn))), counter)
  | counter, .primitive _ _ _ => (.skip, counter)
  | counter, .arith operation => (.inst (.arith (wordArith context operation)), counter)
  | counter, .store address value =>
      match wordCompileExp context address with
      | some address => (.store address (wordFindVar context value), counter)
      | none => (.skip, counter)
  | counter, .setGlobal address value =>
      match wordCompileExp context value with
      | some value => (.set (.temp address) value, counter)
      | none => (.skip, counter)
  | counter, .load32 address destination =>
      (.inst (.mem .load32 (wordFindVar context destination) (wordFindVar context address)),
        counter)
  | counter, .loadByte address destination =>
      (.inst (.mem .load8 (wordFindVar context destination) (wordFindVar context address)),
        counter)
  | counter, .store32 address value =>
      (.inst (.mem .store32 (wordFindVar context value) (wordFindVar context address)),
        counter)
  | counter, .storeByte address value =>
      (.inst (.mem .store8 (wordFindVar context value) (wordFindVar context address)),
        counter)
  | counter, .seq first second =>
      let (first', counter) := loopToWordProgFrom context sectionLabel counter first
      let (second', counter) := loopToWordProgFrom context sectionLabel counter second
      (.seq first' second', counter)
  | counter, .ite operator condition right thenBranch elseBranch _ =>
      let (then', counter) := loopToWordProgFrom context sectionLabel counter thenBranch
      let (else', counter) := loopToWordProgFrom context sectionLabel counter elseBranch
      (.seq (.ite operator (wordFindVar context condition) (wordRegImm context right)
        then' else') .tick, counter)
  | counter, .loop liveIn body liveOut =>
      let (body', counter) := loopToWordProgFrom context sectionLabel counter body
      (.seq .tick (.seq (.loop (wordMkNewCutset context liveIn)
        body' (wordMkNewCutset context liveOut)) .tick), counter)
  | counter, .break label => (.break label, counter)
  | counter, .continue label => (.continue label, counter)
  | counter, .raise exception => (.raise (wordFindVar context exception), counter)
  | counter, .return values => (.return 0 (wordMapVars context values), counter)
  | counter, .tick => (.tick, counter)
  | counter, .mark body => loopToWordProgFrom context sectionLabel counter body
  | counter, .fail => (.skip, counter)
  | counter, .locValue destination source =>
      /- The second field is a code label, not a virtual register.  CakeML's
         loop_to_word pass renames only the destination variable and preserves
         the label for the later code-environment lookup. -/
      (.locValue (wordFindVar context destination) source, counter)
  | counter, .call none target arguments _ =>
      /- Tail call: CakeML drops the handler and prepends register 0 to the
         argument list (`loop_to_wordScript.sml:131`). -/
      (.call none target (0 :: wordMapVars context arguments) none, counter)
  | counter, .call (some (values, live)) target arguments none =>
      (.call (some (wordMapVars context values,
          (wordMkNewCutset context live, []), .skip, sectionLabel, counter)) target
        (wordMapVars context arguments) none, counter + 1)
  | counter, .call (some (values, live)) target arguments
      (some (exception, body, normal, _)) =>
      /- Handled call: the handler body and the normal-return handler are
         compiled with the threaded counter, the return slot keeps the
         entry label, the handler receives the label after both compilations,
         and a trailing `Tick` accounts for the clock
         (`loop_to_wordScript.sml:138-143`). -/
      let (body', counter') := loopToWordProgFrom context sectionLabel (counter + 1) body
      let (normal', counter'') := loopToWordProgFrom context sectionLabel counter' normal
      (.seq (.call (some (wordMapVars context values,
            (wordMkNewCutset context live, []), normal', sectionLabel, counter)) target
          (wordMapVars context arguments)
          (some (wordFindVar context exception, body', sectionLabel, counter''))) .tick,
        counter'' + 1)
  | counter, .ffi function configuration configurationLength array arrayLength live =>
      (.ffi function (wordFindVar context configuration)
        (wordFindVar context configurationLength) (wordFindVar context array)
        (wordFindVar context arrayLength) (wordMkNewCutset context live, []), counter)
  | counter, .shMem operator name address =>
      match wordMemOp operator, wordCompileExp context address with
      | some operator, some address =>
          (.shareInst operator (wordFindVar context name) address, counter)
      | _, _ => (.skip, counter)
  termination_by _ program => sizeOf program
  decreasing_by
    all_goals decreasing_trivial

def loopToWordProg [OfNat α 1] (context : WordContext) (program : LoopProg α) :
    WordProg α :=
  (loopToWordProgFrom context 0 2 program).1

/-! Stateful Loop-to-Word companion for the source-shaped compiler boundary.
    Cake's `comp` threads `(function label, fresh local label)` through calls;
    the return and handler labels are observable in the final RISC-V artifact.
    The older stateless helper above remains available to the pass-local
    semantics and uses the historical zero labels. -/
def loopToWordProgWithLabels [OfNat α 1] (context : WordContext) :
    (Nat × Nat) → LoopProg α → WordProg α × (Nat × Nat)
  | labels, .seq first second =>
      let (first, labels) := loopToWordProgWithLabels context labels first
      let (second, labels) := loopToWordProgWithLabels context labels second
      (.seq first second, labels)
  | labels, .ite operator condition right thenBranch elseBranch _ =>
      let (thenBranch, labels) := loopToWordProgWithLabels context labels thenBranch
      let (elseBranch, labels) := loopToWordProgWithLabels context labels elseBranch
      (.seq (.ite operator (wordFindVar context condition) (wordRegImm context right)
        thenBranch elseBranch) .tick, labels)
  | labels, .loop liveIn body liveOut =>
      let (body, labels) := loopToWordProgWithLabels context labels body
      (.seq .tick (.seq (.loop (wordMkNewCutset context liveIn) body
        (wordMkNewCutset context liveOut)) .tick), labels)
  | labels, .mark body =>
      loopToWordProgWithLabels context labels body
  | labels, .call none target arguments _ =>
      (.call none target (wordMapVars context arguments) none, labels)
  | labels, .call (some (values, live)) target arguments none =>
      let nextLabels := (labels.1, labels.2 + 1)
      (.call (some (wordMapVars context values,
          (wordMkNewCutset context live, []), .skip, labels.1, labels.2)) target
        (wordMapVars context arguments) none, nextLabels)
  | labels, .call (some (values, live)) target arguments
      (some (exception, handlerBody, returnBody, _)) =>
      let nextLabels := (labels.1, labels.2 + 1)
      let (handlerBody, handlerLabels) :=
        loopToWordProgWithLabels context nextLabels handlerBody
      let (returnBody, handlerLabels) :=
        loopToWordProgWithLabels context handlerLabels returnBody
      let finalLabels := (handlerLabels.1, handlerLabels.2 + 1)
      (.seq
        (.call (some (wordMapVars context values,
            (wordMkNewCutset context live, []), returnBody, labels.1, labels.2)) target
          (wordMapVars context arguments)
          (some (wordFindVar context exception, handlerBody,
            handlerLabels.1, handlerLabels.2))) .tick, finalLabels)
  | labels, program => (loopToWordProg context program, labels)
  termination_by _ program => sizeOf program
  decreasing_by
    all_goals decreasing_trivial

theorem loopToWordProg_skip [OfNat α 1] (context : WordContext) :
    loopToWordProg context (.skip : LoopProg α) = .skip := by
  simp [loopToWordProg, loopToWordProgFrom]

theorem loopToWordProgFrom_seq [OfNat α 1] (context : WordContext)
    (sectionLabel counter : Nat) (first second : LoopProg α) :
    loopToWordProgFrom context sectionLabel counter (.seq first second) =
      (let (first', counter') := loopToWordProgFrom context sectionLabel counter first
       let (second', counter'') := loopToWordProgFrom context sectionLabel counter' second
       (.seq first' second', counter'')) := by
  simp [loopToWordProgFrom]

end Flapjack
