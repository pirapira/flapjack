import Flapjack.RiscV.Allocator

namespace Flapjack.RiscV

/-!
# Flatten Word expressions before allocation

Cake's `crep_to_loop` pass turns expression trees into assignments to fresh
Loop temporaries before the Word allocator sees them.  A few Word expressions
can nevertheless be reconstructed by the current Loop-to-Word boundary (for
example the address arithmetic in `topAddr`).  The old RISC-V lowering tried
to evaluate those trees directly with four reserved registers, which made
the result depend on accidental dead registers and rejected large real
functions such as `op_extcodecopy`.

This pass restores the source shape at the Word-to-Stack temporary boundary.
The Word-to-Stack expression compiler draws its intermediate results from a
pool that starts with the reserved scratch registers and continues with
allocator registers that hold no variable; each nested node consumes pool
entries, and `ror` nodes consume two.  A plain depth bound does not model
that consumption, so register-pressure-heavy functions (for example
`ripemd160_block`) still failed lowering on trees the depth bound kept.
Expressions whose pool consumption exceeds the reserved-pool size are
materialized in fresh names, with fresh names using the same `+4` stream as
the SSA allocator.  The generated assignments are then ordinary Word
instructions and therefore participate in the existing clash/spill analysis.
-/

structure WordFlattenExpResult (α : Type u) where
  code : WordProg α
  expression : WordExp α
  next : Nat
  budget : Nat

structure WordFlattenProgResult (α : Type u) where
  program : WordProg α
  next : Nat

def wordFlattenSeq (first second : WordProg α) : WordProg α :=
  match first, second with
  | .skip, program => program
  | program, .skip => program
  | _, _ => .seq first second

def wordFlattenFresh (next : Nat) (expression : WordExp α)
    (code : WordProg α) : WordFlattenExpResult α :=
  { code := wordFlattenSeq code (.assign next expression)
    expression := .var next
    next := next + 4
    budget := 0 }

/-- An expression the Word-to-Stack atom compiler accepts directly. -/
def wordExpIsAtom : WordExp α → Bool
  | .const _ | .var _ | .lookup _ => true
  | .load _ | .op _ _ | .shift _ _ _ => false

/-! Pool consumption of the Word-to-Stack expression compiler.  Binary
    operators draw one pool entry for the right subtree and recurse with the
    remaining pool; rotate nodes draw two (a destination distinct from the
    scratch target plus the right subtree); wider operator applications draw
    one entry and recurse with the remainder for every argument; loads reuse
    their target and pool.  Pairs of atoms use fallback registers and consume
    nothing.  `wordProgFirstExpressionLoweringFailure` reports the first
    expression that needs more entries than the pool provides. -/
mutual
def wordExpLoweringBudget : WordExp α → Nat
  | .const _ | .var _ | .lookup _ => 0
  | .load address => wordExpLoweringBudget address
  | .op _ [] => 0
  | .op _ [value] => wordExpLoweringBudget value
  | .op _ [left, right] =>
      if wordExpIsAtom left && wordExpIsAtom right then 0
      else 1 + max (wordExpLoweringBudget left) (wordExpLoweringBudget right)
  | .op _ (first :: rest) =>
      1 + max (wordExpLoweringBudget first) (wordExpLoweringBudgetList rest)
  | .shift .ror left right =>
      if wordExpIsAtom left && wordExpIsAtom right then 0
      else 2 + max (wordExpLoweringBudget left) (wordExpLoweringBudget right)
  | .shift _ left right =>
      if wordExpIsAtom left && wordExpIsAtom right then 0
      else 1 + max (wordExpLoweringBudget left) (wordExpLoweringBudget right)
termination_by expression => sizeOf expression
decreasing_by
  all_goals
    first
      | decreasing_trivial
      | simp +arith

def wordExpLoweringBudgetList : List (WordExp α) → Nat
  | [] => 0
  | argument :: arguments =>
      max (wordExpLoweringBudget argument) (wordExpLoweringBudgetList arguments)
termination_by arguments => sizeOf arguments
decreasing_by
  all_goals decreasing_trivial
end

/-- The reserved pool holds the four scratch registers minus the lowering
    target.  Materialize exactly the expressions that could exceed it; free
    allocator registers can only enlarge the pool. -/
def wordFlattenBudgetLimit : Nat := 3

inductive WordFlattenWorkResult (α : Type u) where
  | expression (result : WordFlattenExpResult α)
  | expressions (code : WordProg α) (expressions : List (WordExp α))
      (next budget : Nat)

inductive WordFlattenWorkInput (α : Type u) where
  | expression (value : WordExp α)
  | expressions (values : List (WordExp α))

def wordFlattenNode (next : Nat) (flattened : WordExp α) (code : WordProg α) :
    WordFlattenExpResult α :=
  let budget := wordExpLoweringBudget flattened
  if budget > wordFlattenBudgetLimit then
    wordFlattenFresh next flattened code
  else
    { code := code, expression := flattened, next, budget }

def wordFlattenWork (next : Nat) : WordFlattenWorkInput α → WordFlattenWorkResult α
  | .expressions [] => .expressions .skip [] next 0
  | .expressions (value :: values) =>
      let first := wordFlattenWork next (.expression value)
      let first := match first with
        | .expression result => result
        | .expressions _ _ _ _ =>
            { code := .skip, expression := .var 0, next, budget := 0 }
      let rest := wordFlattenWork first.next (.expressions values)
      match rest with
      | .expressions code expressions next budget =>
          .expressions (wordFlattenSeq first.code code)
            (first.expression :: expressions) next (max first.budget budget)
      | .expression _ => .expressions first.code [first.expression] first.next first.budget
  | .expression (.const value) =>
      .expression { code := .skip, expression := .const value, next, budget := 0 }
  | .expression (.var name) =>
      .expression { code := .skip, expression := .var name, next, budget := 0 }
  | .expression (.lookup store) =>
      .expression { code := .skip, expression := .lookup store, next, budget := 0 }
  | .expression (.load address) =>
      let address := wordFlattenWork next (.expression address)
      match address with
      | .expression address =>
          .expression (wordFlattenNode address.next (.load address.expression)
            address.code)
      | .expressions _ _ _ _ =>
          .expression { code := .skip, expression := .var 0, next, budget := 0 }
  | .expression (.op operator arguments) =>
      let arguments := wordFlattenWork next (.expressions arguments)
      match arguments with
      | .expressions code arguments next _ =>
          .expression (wordFlattenNode next (.op operator arguments) code)
      | .expression result => .expression result
  | .expression (.shift operator left right) =>
      let left := wordFlattenWork next (.expression left)
      match left with
      | .expression left =>
          let right := wordFlattenWork left.next (.expression right)
          match right with
          | .expression right =>
              .expression (wordFlattenNode right.next
                (.shift operator left.expression right.expression)
                (wordFlattenSeq left.code right.code))
          | .expressions code _ next _ =>
              let fallback : WordFlattenExpResult α :=
                { code := wordFlattenSeq left.code code,
                  expression := left.expression, next, budget := left.budget }
              .expression fallback
      | .expressions code _ next _ =>
          .expression { code := code, expression := .var 0, next, budget := 0 }
termination_by input => sizeOf input
decreasing_by all_goals decreasing_trivial

def wordFlattenExpList (next : Nat) (expressions : List (WordExp α)) :
    WordProg α × List (WordExp α) × Nat :=
  match wordFlattenWork next (.expressions expressions) with
  | .expressions code expressions next _ => (code, expressions, next)
  | .expression result => (result.code, [result.expression], result.next)

def wordFlattenExp (next : Nat) (expression : WordExp α) : WordFlattenExpResult α :=
  match wordFlattenWork next (.expression expression) with
  | .expression result => result
  | .expressions code _ next _ =>
      { code := code, expression := .var 0, next, budget := 0 }

/-- The Word-to-Stack `set` compiler accepts only atoms, so a compound value
    is materialized into a fresh temporary before the store. -/
def wordFlattenSetStore (next : Nat) (store : WordStore α) (value : WordExp α) :
    WordFlattenProgResult α :=
  let value := wordFlattenExp next value
  if wordExpIsAtom value.expression then
    { program := wordFlattenSeq value.code (.set store value.expression),
      next := value.next }
  else
    { program := wordFlattenSeq value.code
        (wordFlattenSeq (.assign value.next value.expression)
          (.set store (.var value.next))),
      next := value.next + 4 }

def wordFlattenProgram (next : Nat) : WordProg α → WordFlattenProgResult α
  | .skip => { program := .skip, next }
  | .move priority moves => { program := .move priority moves, next }
  | .assign destination value =>
      let value := wordFlattenExp next value
      { program := wordFlattenSeq value.code (.assign destination value.expression)
        next := value.next }
  | .inst instruction => { program := .inst instruction, next }
  | .get destination store => { program := .get destination store, next }
  | .store address value =>
      let address := wordFlattenExp next address
      { program := wordFlattenSeq address.code (.store address.expression value)
        next := address.next }
  | .set store value => wordFlattenSetStore next store value
  | .seq first second =>
      let first := wordFlattenProgram next first
      let second := wordFlattenProgram first.next second
      { program := wordFlattenSeq first.program second.program, next := second.next }
  | .ite operator condition right thenBranch elseBranch =>
      let thenBranch := wordFlattenProgram next thenBranch
      let elseBranch := wordFlattenProgram thenBranch.next elseBranch
      { program := .ite operator condition right thenBranch.program elseBranch.program
        next := elseBranch.next }
  | .loop liveIn body liveOut =>
      let body := wordFlattenProgram next body
      { program := .loop liveIn body.program liveOut, next := body.next }
  | .mustTerminate body =>
      let body := wordFlattenProgram next body
      { program := .mustTerminate body.program, next := body.next }
  | .break label => { program := .break label, next }
  | .continue label => { program := .continue label, next }
  | .raise exception => { program := .raise exception, next }
  | .return label values => { program := .return label values, next }
  | .tick => { program := .tick, next }
  | .locValue destination source =>
      { program := .locValue destination source, next }
  | .call returns target arguments handler =>
      let returns := match returns with
        | none => (none, next)
        | some (values, cutsets, returnCode, returnLabel, entryLabel) =>
            let returnCode := wordFlattenProgram next returnCode
            (some (values, cutsets, returnCode.program, returnLabel, entryLabel),
              returnCode.next)
      let handler := match handler with
        | none => (none, returns.2)
        | some (exception, body, handlerLabel, handlerEntryLabel) =>
            let body := wordFlattenProgram returns.2 body
            (some (exception, body.program, handlerLabel, handlerEntryLabel), body.next)
      { program := .call returns.1 target arguments handler.1, next := handler.2 }
  | .alloc destination cutsets =>
      { program := .alloc destination cutsets, next }
  | .storeConsts source bitmap codeLength dataLength constants =>
      { program := .storeConsts source bitmap codeLength dataLength constants, next }
  | .opCurrHeap operator destination source =>
      { program := .opCurrHeap operator destination source, next }
  | .install codeBuffer codeLength dataBuffer dataLength cutsets =>
      { program := .install codeBuffer codeLength dataBuffer dataLength cutsets, next }
  | .codeBufferWrite address value =>
      { program := .codeBufferWrite address value, next }
  | .dataBufferWrite address value =>
      { program := .dataBufferWrite address value, next }
  | .ffi function configuration configurationLength array arrayLength live =>
      { program := .ffi function configuration configurationLength array arrayLength live, next }
  | .shareInst operator name address =>
      let address := wordFlattenExp next address
      { program := wordFlattenSeq address.code (.shareInst operator name address.expression)
        next := address.next }
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def wordFlattenProgramFrom (program : WordProg α) : WordProg α :=
  (wordFlattenProgram (wordSsaLimitVar [] program) program).program

theorem wordFlattenProgramFrom_skip :
    wordFlattenProgramFrom (.skip : WordProg α) = .skip := by
  simp [wordFlattenProgramFrom, wordSsaLimitVar, wordProgVariables,
    wordFlattenProgram]

end Flapjack.RiscV
