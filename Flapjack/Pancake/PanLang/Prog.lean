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

end Flapjack.Pancake.PanLang
