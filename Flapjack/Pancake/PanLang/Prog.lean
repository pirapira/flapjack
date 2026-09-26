import Flapjack.Pancake.PanLang.Exp
import Flapjack.Pancake.PanLang.Shape

/-!
Exact `panLang$prog` carrier over the faithful `MlString` identifiers and the
width-indexed `ExpHOL` expression payloads
(`cakeml/pancake/panLangScript.sml:78-100`).

Production `Flapjack.Prog α` uses generic expressions and Lean `String`
identifiers, so it is untagged.  `ProgHOL` mirrors the HOL datatype
constructor-by-constructor with `MlS` names and `ExpHOL width` payloads, and is
related to production syntax by the untagged codec `progToHOL`/`progOfHOL`.
-/

namespace Flapjack.Pancake.PanLang

open Flapjack.Basis.Pure.MlString

/-- Identifier strings whose every character code is `< 256`, i.e. exactly
    representable as the HOL 8-bit `char` list inside `mlstring`. -/
abbrev NameRanged (s : String) : Prop := ∀ c ∈ s.toList, c.toNat < 256

/-- Exact port of HOL `panLang$prog` (`cakeml/pancake/panLangScript.sml:78-100`).

    The 21 constructors match in order and arity.  Identifier payloads
    (`varname`, `funname`, `eid`, and the `Annot` tags) use `MlS`, the faithful
    `mlstring` carrier (names are `mlstring` per lines 23-31); expression
    payloads are the width-indexed `ExpHOL width`; `shape` fields use the exact
    `ShapeHOL`.  The nested `Call` metadata is
    `Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width))`,
    matching HOL
    `(((varkind # varname) option # ((eid # varname # prog) option)) option)`. -/
@[hol "cakeml/pancake/panLangScript.sml" "prog"]
inductive ProgHOL (width : Nat) [NeZero width] where
  | skip
  | dec (name : MlS) (shape : ShapeHOL) (value : ExpHOL width) (body : ProgHOL width)
  | assign (kind : VarKind) (name : MlS) (value : ExpHOL width)
  | primitive (name : MlS) (operator : PrimOp) (args : List (ExpHOL width))
  | store (address value : ExpHOL width)
  | store32 (address value : ExpHOL width)
  | storeByte (address value : ExpHOL width)
  | seq (first second : ProgHOL width)
  | ite (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
  | while (condition : ExpHOL width) (body : ProgHOL width)
  | break
  | continue
  | call (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
      (name : MlS) (args : List (ExpHOL width))
  | decCall (name : MlS) (shape : ShapeHOL) (function : MlS)
      (args : List (ExpHOL width)) (body : ProgHOL width)
  | extCall (function : MlS)
      (configuration configurationLength array arrayLength : ExpHOL width)
  | raise (exception : MlS) (value : ExpHOL width)
  | return (value : ExpHOL width)
  | shMemLoad (size : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width)
  | shMemStore (size : OpSize) (address value : ExpHOL width)
  | tick
  | annot (tag text : MlS)
  deriving Repr

/-! HOL `panLangScript.sml:127-129` declares three `Overload`s that abbreviate
    the `Call` constructor with a partially applied call-info argument:

    ```
    Overload TailCall       = ``Call NONE``
    Overload AssignCall     = ``\s h. Call (SOME (SOME s , h))``
    Overload StandAloneCall = ``\h. Call (SOME (NONE , h))``
    ```

    The exact `ProgHOL.call` constructor has the same info carrier
    (`Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width))`), so
    each overload is reproduced below as the identical partially-applied
    constructor (Lean currying matches HOL's `->` types).  `Overload`s are not
    datatype constructors, but HOL declares them as named constants with these
    bodies, and the reference checker indexes `Overload` lines, so they carry
    `@[hol]` tags. -/

/-- HOL `Overload TailCall = ``Call NONE``` (`panLangScript.sml:127`): a call
    with no call-info. -/
@[hol "cakeml/pancake/panLangScript.sml" "TailCall"]
def tailCallHOL {width : Nat} [NeZero width] :
    MlS → List (ExpHOL width) → ProgHOL width :=
  .call none

/-- HOL `Overload AssignCall = ``\s h. Call (SOME (SOME s , h))```
    (`panLangScript.sml:128`): a call with an assigned destination `s` and a
    optional exception handler `h`. -/
@[hol "cakeml/pancake/panLangScript.sml" "AssignCall"]
def assignCallHOL {width : Nat} [NeZero width]
    (s : VarKind × MlS) (h : Option (MlS × MlS × ProgHOL width)) :
    MlS → List (ExpHOL width) → ProgHOL width :=
  .call (some (some s, h))

/-- HOL `Overload StandAloneCall = ``\h. Call (SOME (NONE , h))```
    (`panLangScript.sml:129`): a call with no destination but an optional
    exception handler `h`. -/
@[hol "cakeml/pancake/panLangScript.sml" "StandAloneCall"]
def standAloneCallHOL {width : Nat} [NeZero width]
    (h : Option (MlS × MlS × ProgHOL width)) :
    MlS → List (ExpHOL width) → ProgHOL width :=
  .call (some (none, h))

/-- Production programs all of whose identifiers are byte-ranged and whose
    expressions are byte-ranged, hence exactly representable over `MlString`. -/
def ProgByteRanged {width : Nat} : Prog (BitVec width) → Prop
  | .skip => True
  | .dec name shape value body =>
      NameRanged name ∧ ShapeByteRanged shape ∧ ExpByteRanged value ∧ ProgByteRanged body
  | .assign _ name value => NameRanged name ∧ ExpByteRanged value
  | .primitive name _ args => NameRanged name ∧ ∀ e ∈ args, ExpByteRanged e
  | .store address value => ExpByteRanged address ∧ ExpByteRanged value
  | .store32 address value => ExpByteRanged address ∧ ExpByteRanged value
  | .storeByte address value => ExpByteRanged address ∧ ExpByteRanged value
  | .seq first second => ProgByteRanged first ∧ ProgByteRanged second
  | .ite condition thenBranch elseBranch =>
      ExpByteRanged condition ∧ ProgByteRanged thenBranch ∧ ProgByteRanged elseBranch
  | .while condition body => ExpByteRanged condition ∧ ProgByteRanged body
  | .break => True
  | .continue => True
  | .call info name args =>
      NameRanged name ∧ (∀ e ∈ args, ExpByteRanged e) ∧
        (match info with
         | none => True
         | some (kindOpt, handlerOpt) =>
             (match kindOpt with
              | none => True
              | some (_, nm) => NameRanged nm) ∧
             (match handlerOpt with
              | none => True
              | some (eid, vn, body) =>
                  NameRanged eid ∧ NameRanged vn ∧ ProgByteRanged body))
  | .decCall name shape function args body =>
      NameRanged name ∧ ShapeByteRanged shape ∧ NameRanged function ∧
        (∀ e ∈ args, ExpByteRanged e) ∧ ProgByteRanged body
  | .extCall function configuration configurationLength array arrayLength =>
      NameRanged function ∧ ExpByteRanged configuration ∧ ExpByteRanged configurationLength ∧
        ExpByteRanged array ∧ ExpByteRanged arrayLength
  | .raise exception value => NameRanged exception ∧ ExpByteRanged value
  | .return value => ExpByteRanged value
  | .shMemLoad _ _ name address => NameRanged name ∧ ExpByteRanged address
  | .shMemStore _ address value => ExpByteRanged address ∧ ExpByteRanged value
  | .tick => True
  | .annot tag text => NameRanged tag ∧ NameRanged text

/-- Encode a production program into the exact HOL-shaped carrier.  Identifiers
    use the total `ofString`, expressions use `expToHOL`, and shapes use
    `shapeToHOL`. -/
def progToHOL {width : Nat} [NeZero width] : Prog (BitVec width) → ProgHOL width
  | .skip => .skip
  | .dec name shape value body =>
      .dec (ofString name) (shapeToHOL shape) (expToHOL value) (progToHOL body)
  | .assign kind name value => .assign kind (ofString name) (expToHOL value)
  | .primitive name operator args => .primitive (ofString name) operator (args.map expToHOL)
  | .store address value => .store (expToHOL address) (expToHOL value)
  | .store32 address value => .store32 (expToHOL address) (expToHOL value)
  | .storeByte address value => .storeByte (expToHOL address) (expToHOL value)
  | .seq first second => .seq (progToHOL first) (progToHOL second)
  | .ite condition thenBranch elseBranch =>
      .ite (expToHOL condition) (progToHOL thenBranch) (progToHOL elseBranch)
  | .while condition body => .while (expToHOL condition) (progToHOL body)
  | .break => .break
  | .continue => .continue
  | .call none name args => .call none (ofString name) (args.map expToHOL)
  | .call (some (kindOpt, none)) name args =>
      .call (some (kindOpt.map (fun kv => (kv.1, ofString kv.2)), none))
        (ofString name) (args.map expToHOL)
  | .call (some (kindOpt, some (eid, v, body))) name args =>
      .call
        (some (kindOpt.map (fun kv => (kv.1, ofString kv.2)),
          some (ofString eid, ofString v, progToHOL body)))
        (ofString name) (args.map expToHOL)
  | .decCall name shape function args body =>
      .decCall (ofString name) (shapeToHOL shape) (ofString function)
        (args.map expToHOL) (progToHOL body)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall (ofString function) (expToHOL configuration) (expToHOL configurationLength)
        (expToHOL array) (expToHOL arrayLength)
  | .raise exception value => .raise (ofString exception) (expToHOL value)
  | .return value => .return (expToHOL value)
  | .shMemLoad size kind name address =>
      .shMemLoad size kind (ofString name) (expToHOL address)
  | .shMemStore size address value => .shMemStore size (expToHOL address) (expToHOL value)
  | .tick => .tick
  | .annot tag text => .annot (ofString tag) (ofString text)
termination_by p => sizeOf p
decreasing_by
  simp_wf
  all_goals
    first
      | decreasing_trivial
      | (simp_all only [Prog.dec.sizeOf_spec, Prog.seq.sizeOf_spec, Prog.ite.sizeOf_spec,
            Prog.while.sizeOf_spec, Prog.call.sizeOf_spec, Prog.decCall.sizeOf_spec]
         omega)

/-- Decode the exact carrier back to a production program.  Identifiers use
    `toStringOfBytes`, expressions use `expOfHOL`, and shapes use
    `shapeOfHOL`. -/
def progOfHOL {width : Nat} [NeZero width] : ProgHOL width → Prog (BitVec width)
  | .skip => .skip
  | .dec name shape value body =>
      .dec (toStringOfBytes name) (shapeOfHOL shape) (expOfHOL value) (progOfHOL body)
  | .assign kind name value => .assign kind (toStringOfBytes name) (expOfHOL value)
  | .primitive name operator args =>
      .primitive (toStringOfBytes name) operator (args.map expOfHOL)
  | .store address value => .store (expOfHOL address) (expOfHOL value)
  | .store32 address value => .store32 (expOfHOL address) (expOfHOL value)
  | .storeByte address value => .storeByte (expOfHOL address) (expOfHOL value)
  | .seq first second => .seq (progOfHOL first) (progOfHOL second)
  | .ite condition thenBranch elseBranch =>
      .ite (expOfHOL condition) (progOfHOL thenBranch) (progOfHOL elseBranch)
  | .while condition body => .while (expOfHOL condition) (progOfHOL body)
  | .break => .break
  | .continue => .continue
  | .call none name args => .call none (toStringOfBytes name) (args.map expOfHOL)
  | .call (some (kindOpt, none)) name args =>
      .call (some (kindOpt.map (fun kv => (kv.1, toStringOfBytes kv.2)), none))
        (toStringOfBytes name) (args.map expOfHOL)
  | .call (some (kindOpt, some (eid, v, body))) name args =>
      .call
        (some (kindOpt.map (fun kv => (kv.1, toStringOfBytes kv.2)),
          some (toStringOfBytes eid, toStringOfBytes v, progOfHOL body)))
        (toStringOfBytes name) (args.map expOfHOL)
  | .decCall name shape function args body =>
      .decCall (toStringOfBytes name) (shapeOfHOL shape) (toStringOfBytes function)
        (args.map expOfHOL) (progOfHOL body)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall (toStringOfBytes function) (expOfHOL configuration) (expOfHOL configurationLength)
        (expOfHOL array) (expOfHOL arrayLength)
  | .raise exception value => .raise (toStringOfBytes exception) (expOfHOL value)
  | .return value => .return (expOfHOL value)
  | .shMemLoad size kind name address =>
      .shMemLoad size kind (toStringOfBytes name) (expOfHOL address)
  | .shMemStore size address value => .shMemStore size (expOfHOL address) (expOfHOL value)
  | .tick => .tick
  | .annot tag text => .annot (toStringOfBytes tag) (toStringOfBytes text)
termination_by p => sizeOf p
decreasing_by
  simp_wf
  all_goals
    first
      | decreasing_trivial
      | (simp_all only [ProgHOL.dec.sizeOf_spec, ProgHOL.seq.sizeOf_spec,
            ProgHOL.ite.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.call.sizeOf_spec,
            ProgHOL.decCall.sizeOf_spec]
         omega)

/-- Round trip on argument lists: encoding then decoding `ExpHOL` expressions
    under `List.map` is the identity. -/
@[simp] theorem listMap_expToHOL_expOfHOL {width : Nat} [NeZero width] :
    (l : List (ExpHOL width)) → (l.map expOfHOL).map expToHOL = l
  | [] => rfl
  | _ :: _ => by simp [expToHOL_expOfHOL, listMap_expToHOL_expOfHOL]

/-- Round trip on the `Call` kind option: re-encoding its `MlS` names after
    decoding is the identity. -/
@[simp] theorem optionMap_stringRoundtrip :
    (o : Option (VarKind × MlS)) →
      (o.map (fun kv => (kv.1, toStringOfBytes kv.2))).map
        (fun kv => (kv.1, ofString kv.2)) = o
  | none => rfl
  | some kv => by
      obtain ⟨kind, name⟩ := kv
      simp [Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]

theorem progToHOL_progOfHOL {width : Nat} [NeZero width] :
    (p : ProgHOL width) → progToHOL (progOfHOL p) = p := by
  intro p
  fun_induction progOfHOL p <;>
    simp_all only [progToHOL, expToHOL_expOfHOL, shapeToHOL_shapeOfHOL,
      Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes,
      listMap_expToHOL_expOfHOL, optionMap_stringRoundtrip]

/-- Round trip on argument lists in the decode direction. -/
theorem listMap_expOfHOL_expToHOL {width : Nat} [NeZero width] :
    (l : List (Flapjack.Exp (BitVec width))) →
      (∀ e ∈ l, ExpByteRanged e) → List.map (expOfHOL ∘ expToHOL) l = l
  | [], _ => rfl
  | h :: t, hl => by
      simp only [List.map_cons, Function.comp_apply]
      rw [expOfHOL_expToHOL h (hl h (by simp)),
        listMap_expOfHOL_expToHOL t (fun e he => hl e (by simp [he]))]

/-- Decoding the encoding of a byte-ranged production program recovers it
    exactly.  The byte-range hypothesis is what makes the reverse direction
    total: identifiers must lie in HOL `char` range and expressions in
    `ExpByteRanged`. -/
theorem progOfHOL_progToHOL {width : Nat} [NeZero width] :
    (p : Prog (BitVec width)) → ProgByteRanged p → progOfHOL (progToHOL p) = p := by
  intro p
  fun_induction progToHOL p
  case case14 kindOpt name args =>
    intro h
    obtain ⟨_, _, _, _⟩ := h
    cases kindOpt <;>
      simp_all [progOfHOL,
        Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes,
        listMap_expOfHOL_expToHOL]
  case case15 kindOpt eid v body name args ih =>
    intro h
    obtain ⟨_, _, _, _, _, _⟩ := h
    cases kindOpt <;>
      simp_all [progOfHOL,
        Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes,
        listMap_expOfHOL_expToHOL]
  all_goals (intros <;>
      simp_all [ProgByteRanged, progOfHOL, expOfHOL_expToHOL,
        shapeOfHOL_shapeToHOL, Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes,
        listMap_expOfHOL_expToHOL])


/-- Extraction: a byte-ranged production `ExtCall` program has a byte-ranged
    FFI function name (the precondition the production FFI boundary witness
    consumes). -/
theorem progByteRanged_extCall_name {width : Nat} {function : String}
    {configuration configurationLength array arrayLength : Flapjack.Exp (BitVec width)}
    (h : ProgByteRanged
      (Flapjack.Prog.extCall function configuration configurationLength array arrayLength :
        Flapjack.Prog (BitVec width))) :
    NameRanged function :=
  h.1

/-! ### Exact `panLang$exp_ids` (bead flapjack-4ac.1.33)

HOL `exp_ids_def` (`cakeml/pancake/panLangScript.sml:222-231`) collects the
exception identifiers syntactically reachable from a program over the exact
`prog` carrier.  `expIdsHOL` mirrors all of its clauses; the raw construction
(`Call (SOME (_, SOME (e, _, ep)))`) contributes the handler identifier `e` and
the identifiers of `ep`, everything else contributes nothing.  The production
`Flapjack.expIds` is polymorphic over `Prog α` with `String` identifiers, so it
cannot literally call this word-indexed definition; the checked bridge
`expIdsHOL_map_toStringOfBytes` connects them clause-for-clause on the exact
HOL carrier. The reverse production-to-HOL roundtrip is available for
`Prog (BitVec width)` only under `ProgByteRanged`, since `MlString` cannot
round-trip arbitrary Lean `String` identifiers. A source audit found
`Pipeline.pipelineGetEids` as the only production definition that calls
`expIds` to form exception codes, but no compiler caller of `pipelineGetEids`;
the executed pipeline therefore does not currently route through either
`expIds` or `expIdsHOL`. -/
@[hol "cakeml/pancake/panLangScript.sml" "exp_ids_def"]
def expIdsHOL {width : Nat} [NeZero width] : ProgHOL width → List MlS
  | .skip => []
  | .dec _ _ _ body => expIdsHOL body
  | .assign _ _ _ => []
  | .primitive _ _ _ => []
  | .store _ _ => []
  | .store32 _ _ => []
  | .storeByte _ _ => []
  | .seq first second => expIdsHOL first ++ expIdsHOL second
  | .ite _ thenBranch elseBranch => expIdsHOL thenBranch ++ expIdsHOL elseBranch
  | .while _ body => expIdsHOL body
  | .break => []
  | .continue => []
  | .call (some (_, some (exception, _, handler))) _ _ => exception :: expIdsHOL handler
  | .call _ _ _ => []
  | .decCall _ _ _ _ body => expIdsHOL body
  | .extCall _ _ _ _ _ => []
  | .raise exception _ => [exception]
  | .return _ => []
  | .shMemLoad _ _ _ _ => []
  | .shMemStore _ _ _ => []
  | .tick => []
  | .annot _ _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-- When a `Call`'s metadata is not the `SOME (_, SOME (eid, _, handler))` shape,
    both the exact `expIdsHOL` and the production `Flapjack.expIds` contribute no
    exception identifiers. -/
theorem expIds_progOfHOL_call_of_not {width : Nat} [NeZero width]
    {info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width))}
    {name : MlS} {args : List (ExpHOL width)}
    (h : ∀ (kindOpt : Option (VarKind × MlS)) (eid binding : MlS) (body : ProgHOL width),
      info ≠ some (kindOpt, some (eid, binding, body))) :
    Flapjack.expIds (progOfHOL (.call info name args : ProgHOL width)) = [] := by
  cases info with
  | none => simp [progOfHOL, Flapjack.expIds]
  | some pair =>
    obtain ⟨kindOpt, rest⟩ := pair
    cases rest with
    | none => simp [progOfHOL, Flapjack.expIds]
    | some triple =>
      obtain ⟨eid, binding, body⟩ := triple
      exact absurd rfl (h kindOpt eid binding body)

/-- The exact `expIdsHOL` projects the same exception identifiers as the
production `Flapjack.expIds` after the `toStringOfBytes` name bridge.  Direct
executable routing is unavailable because production is polymorphic over
`Prog α` with `String` identifiers while the tagged definition is over the
word-indexed `ProgHOL` with `MlS`; this checked relation is the connection
(bead flapjack-4ac.1.33). -/
@[simp] theorem expIdsHOL_map_toStringOfBytes {width : Nat} [NeZero width]
    (program : ProgHOL width) :
    (expIdsHOL program).map toStringOfBytes = Flapjack.expIds (progOfHOL program) := by
  fun_induction expIdsHOL program <;>
    simp_all only [Flapjack.expIds, progOfHOL, List.map_append, List.map_cons,
      List.map_nil]
  case case14 =>
    rename_i infoH nameH argsH hNot
    exact (expIds_progOfHOL_call_of_not (info := infoH) (name := nameH)
      (args := argsH) hNot).symm

/-- Flapjack-specific codec theorem (no HOL original: HOL has no
`ProgByteRanged` predicate or Lean `String`/`MlString` codec premise). On the
byte-ranged production subset, encoding with `progToHOL` and projecting the
exact HOL `exp_ids_def` back through `toStringOfBytes` recovers the production
`expIds` result. This is a checked representation bridge, not a claim that the
generic production compiler path calls `expIdsHOL`. -/
theorem expIdsHOL_progToHOL_byteRanged {width : Nat} [NeZero width]
    (program : Flapjack.Prog (BitVec width))
    (hRanged : ProgByteRanged program) :
    (expIdsHOL (progToHOL program)).map toStringOfBytes = Flapjack.expIds program := by
  rw [expIdsHOL_map_toStringOfBytes, progOfHOL_progToHOL program hRanged]

/-! ### Exact `panLang$fun_ids` (bead flapjack-4ac.1.45)

HOL `fun_ids_def` (`cakeml/pancake/panLangScript.sml:336-343`) collects the
callee names syntactically reachable from a program over the exact `prog`
carrier.  `funIdsHOL` mirrors every clause: a handler `Call` contributes its
name and the names of the handler, a non-handler `Call` contributes just its
name, `DecCall` contributes its name and the body names, and every other
constructor contributes nothing.  The production `Flapjack.funIds` is
polymorphic over `Prog α` with `String` names, so it cannot literally call this
word-indexed definition; the checked bridge `funIdsHOL_map_toStringOfBytes`
connects them clause-for-clause. -/
@[hol "cakeml/pancake/panLangScript.sml" "fun_ids_def"]
def funIdsHOL {width : Nat} [NeZero width] : ProgHOL width → List MlS
  | .skip => []
  | .dec _ _ _ body => funIdsHOL body
  | .assign _ _ _ => []
  | .primitive _ _ _ => []
  | .store _ _ => []
  | .store32 _ _ => []
  | .storeByte _ _ => []
  | .seq first second => funIdsHOL first ++ funIdsHOL second
  | .ite _ thenBranch elseBranch => funIdsHOL thenBranch ++ funIdsHOL elseBranch
  | .while _ body => funIdsHOL body
  | .break => []
  | .continue => []
  | .call (some (_, some (_, _, handler))) name _ => name :: funIdsHOL handler
  | .call _ name _ => [name]
  | .decCall _ _ function _ body => function :: funIdsHOL body
  | .extCall _ _ _ _ _ => []
  | .raise _ _ => []
  | .return _ => []
  | .shMemLoad _ _ _ _ => []
  | .shMemStore _ _ _ => []
  | .tick => []
  | .annot _ _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-- When a `Call`'s metadata is not the `SOME (_, SOME (_, _, handler))` shape,
    both the exact `funIdsHOL` and the production `Flapjack.funIds` contribute
    only the callee name. -/
theorem funIds_progOfHOL_call_of_not {width : Nat} [NeZero width]
    {info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width))}
    {name : MlS} {args : List (ExpHOL width)}
    (h : ∀ (kindOpt : Option (VarKind × MlS)) (eid binding : MlS) (body : ProgHOL width),
      info ≠ some (kindOpt, some (eid, binding, body))) :
    Flapjack.funIds (progOfHOL (.call info name args : ProgHOL width)) =
      [toStringOfBytes name] := by
  cases info with
  | none => simp [progOfHOL, Flapjack.funIds]
  | some pair =>
    obtain ⟨kindOpt, rest⟩ := pair
    cases rest with
    | none => simp [progOfHOL, Flapjack.funIds]
    | some triple =>
      obtain ⟨eid, binding, body⟩ := triple
      exact absurd rfl (h kindOpt eid binding body)

/-- The exact `funIdsHOL` projects the same callee names as the production
`Flapjack.funIds` after the `toStringOfBytes` name bridge.  Direct executable
routing is unavailable because production is polymorphic over `Prog α` with
`String` names while the tagged definition is over the word-indexed `ProgHOL`
with `MlS`; this checked relation is the connection (bead flapjack-4ac.1.45). -/
@[simp] theorem funIdsHOL_map_toStringOfBytes {width : Nat} [NeZero width]
    (program : ProgHOL width) :
    (funIdsHOL program).map toStringOfBytes = Flapjack.funIds (progOfHOL program) := by
  fun_induction funIdsHOL program <;>
    simp_all only [Flapjack.funIds, progOfHOL, List.map_append, List.map_cons,
      List.map_nil]
  case case14 =>
    rename_i infoH nameH argsH hNot
    exact (funIds_progOfHOL_call_of_not (info := infoH) (name := nameH)
      (args := argsH) hNot).symm

/-- Exact port of HOL `panLang$free_var_ids_def` (`cakeml/pancake/panLangScript.sml:347-392`)
    over the MlString/width-indexed `ProgHOL width` carrier.  Every clause mirrors the
    HOL clause, including the five `Call` metadata shapes (none/none, none/some-handler,
    some-local/no-handler, some/none, some/some-handler) and the `ShMemLoad`/`ShMemStore`
    cases.  The expression variable collector is the tagged `varExpHOL` (`var_exp_def`)
    and the local shadowing filter is `FILTER ($≠ vn)`.  There is no production
    Pancake analogue to connect (the only production free-variable collector is the
    unrelated crepLang `assigned_free_vars`). -/
@[hol "cakeml/pancake/panLangScript.sml" "free_var_ids_def"]
def freeVarIdsHOL {width : Nat} [NeZero width] : ProgHOL width → List MlS
  | .skip => []
  | .dec vn _ e body => varExpHOL e ++ (freeVarIdsHOL body).filter (fun candidate => candidate != vn)
  | .assign vk v e => if vk = VarKind.local then v :: varExpHOL e else varExpHOL e
  | .primitive v _ es => v :: (es.map varExpHOL).flatten
  | .store e1 e2 => varExpHOL e1 ++ varExpHOL e2
  | .store32 e1 e2 => varExpHOL e1 ++ varExpHOL e2
  | .storeByte e1 e2 => varExpHOL e1 ++ varExpHOL e2
  | .seq first second => freeVarIdsHOL first ++ freeVarIdsHOL second
  | .ite g first second => varExpHOL g ++ freeVarIdsHOL first ++ freeVarIdsHOL second
  | .while g body => varExpHOL g ++ freeVarIdsHOL body
  | .break => []
  | .continue => []
  | .call none _ args => (args.map varExpHOL).flatten
  | .call (some (none, none)) _ args => (args.map varExpHOL).flatten
  | .call (some (none, some (_, vn, ep))) _ args =>
      vn :: (freeVarIdsHOL ep ++ (args.map varExpHOL).flatten)
  | .call (some (some (vk, vn), none)) _ args =>
      (if vk = VarKind.local then [vn] else []) ++ (args.map varExpHOL).flatten
  | .call (some (some (vk, vn), some (_, en, ep))) _ args =>
      ((if vk = VarKind.local then [vn] else []) ++ (en :: freeVarIdsHOL ep)) ++
        (args.map varExpHOL).flatten
  | .decCall vn _ _ args body =>
      vn :: (freeVarIdsHOL body ++ (args.map varExpHOL).flatten)
  | .extCall _ e1 e2 e3 e4 =>
      varExpHOL e1 ++ varExpHOL e2 ++ varExpHOL e3 ++ varExpHOL e4
  | .raise _ e => varExpHOL e
  | .return e => varExpHOL e
  | .shMemLoad _ vk v e => if vk = VarKind.local then v :: varExpHOL e else varExpHOL e
  | .shMemStore _ e1 e2 => varExpHOL e1 ++ varExpHOL e2
  | .tick => []
  | .annot _ _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-! ### Exact `panLang$nested_seq` (bead flapjack-4ac.1.31)

HOL `nested_seq_def` (`cakeml/pancake/panLangScript.sml:211-213`) is
`nested_seq [] = Skip` and `nested_seq (e::es) = Seq e (nested_seq es)`, over
`'a prog list`.  `nestedSeqHOL` mirrors both clauses over the exact
width-indexed `ProgHOL` carrier (constructor `.skip`/`.seq` with matching
arities and fields).  The production `Flapjack.nestedSeq`
(`Flapjack/Pancake/PanLang.lean:416`) implements the same construction over the
generic `Prog α` with `String` identifiers, so it cannot literally call the
width-indexed definition; the kernel-checked bridge `nestedSeqHOL_progOfHOL`
connects them.  Direct HOL-EVAL rows empty/one/two/assign_seq are in
`scripts/hol-probes/pan_lang_nested_seq_probe.out`, replayed in
`Flapjack/Test/PanNestedSeqParity.lean`. -/
@[hol "cakeml/pancake/panLangScript.sml" "nested_seq_def"]
def nestedSeqHOL {width : Nat} [NeZero width] : List (ProgHOL width) → ProgHOL width
  | [] => .skip
  | statement :: statements => .seq statement (nestedSeqHOL statements)

@[simp] theorem nestedSeqHOL_nil {width : Nat} [NeZero width] :
    nestedSeqHOL ([] : List (ProgHOL width)) = .skip := rfl

@[simp] theorem nestedSeqHOL_cons {width : Nat} [NeZero width]
    (statement : ProgHOL width) (statements : List (ProgHOL width)) :
    nestedSeqHOL (statement :: statements) =
      .seq statement (nestedSeqHOL statements) := rfl

/-- The exact `nestedSeqHOL` decodes to the production `Flapjack.nestedSeq` over
    the decoded program list.  Direct executable routing is unavailable because
    production is polymorphic over `Prog α` with `String` names while the tagged
    definition is over the word-indexed `ProgHOL`; this checked relation is the
    connection (bead flapjack-4ac.1.31). -/
@[simp] theorem nestedSeqHOL_progOfHOL {width : Nat} [NeZero width]
    (statements : List (ProgHOL width)) :
    progOfHOL (nestedSeqHOL statements) =
      Flapjack.nestedSeq (statements.map progOfHOL) := by
  induction statements with
  | nil => simp only [nestedSeqHOL_nil, List.map_nil, progOfHOL, Flapjack.nestedSeq]
  | cons statement statements ih =>
      simp only [nestedSeqHOL_cons, List.map_cons, Flapjack.nestedSeq, progOfHOL, ih]

/-- Encoding a production nested sequence with `progToHOL` equals the exact
    `nestedSeqHOL` over the encoded program list. -/
@[simp] theorem nestedSeqHOL_progToHOL {width : Nat} [NeZero width]
    (statements : List (Prog (BitVec width))) :
    progToHOL (Flapjack.nestedSeq statements) =
      nestedSeqHOL (statements.map progToHOL) := by
  induction statements with
  | nil => simp only [nestedSeqHOL_nil, List.map_nil, progToHOL, Flapjack.nestedSeq]
  | cons statement statements ih =>
      simp only [nestedSeqHOL_cons, List.map_cons, Flapjack.nestedSeq, progToHOL, ih]

/-- Executable width-indexed nested sequence that routes through the reviewed
    `nestedSeqHOL`: encode each production statement with `progToHOL`, apply the
    tagged definition, and decode the result.  On byte-ranged inputs the codec
    round-trip `progOfHOL_progToHOL` makes this agree with the production
    `Flapjack.nestedSeq`; `nestedSeqCake_eq` records that relation.  This is
    production routing infrastructure, not a HOL declaration, so it carries no
    `@[hol]` tag (bead flapjack-4ac.1.31.1). -/
def nestedSeqCake {width : Nat} [NeZero width]
    (statements : List (Prog (BitVec width))) : Prog (BitVec width) :=
  progOfHOL (nestedSeqHOL (statements.map progToHOL))

/-- The encoded list of a byte-ranged program list decodes back to itself, i.e.
    `progOfHOL ∘ progToHOL` is the identity pointwise under `ProgByteRanged`. -/
theorem map_progOfHOL_progToHOL {width : Nat} [NeZero width]
    (statements : List (Prog (BitVec width)))
    (hranged : ∀ statement ∈ statements, ProgByteRanged statement) :
    (statements.map progToHOL).map progOfHOL = statements := by
  induction statements with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons]
      rw [progOfHOL_progToHOL head (hranged head (by simp))]
      congr 1
      exact ih (fun statement hstatement => hranged statement (by simp [hstatement]))

/-- The executable `nestedSeqCake` agrees with the production `Flapjack.nestedSeq`
    whenever every statement round-trips through the exact codec.  This is the
    routing bridge used by the executed compiler's nested-sequence path; it is
    Flapjack-specific infrastructure and is not a HOL theorem. -/
theorem nestedSeqCake_eq {width : Nat} [NeZero width]
    (statements : List (Prog (BitVec width)))
    (hranged : ∀ statement ∈ statements, ProgByteRanged statement) :
    nestedSeqCake statements = Flapjack.nestedSeq statements := by
  unfold nestedSeqCake
  rw [nestedSeqHOL_progOfHOL, map_progOfHOL_progToHOL statements hranged]

end Flapjack.Pancake.PanLang
