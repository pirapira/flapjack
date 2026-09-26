import Flapjack.Semantics
import Flapjack.PanMemoryModel
import Flapjack.PanStructsAfindi
import Flapjack.Pancake.PanLang.Exp

/-!
Structured source values and the corresponding executable expression/state
semantics.  The original scalar evaluator in `Semantics.lean` is useful for
the first compiler slices, but the Pancake source language distinguishes words
from records and named records.  This file preserves that distinction and
matches the value/shape checks in CakeML's `panSem` evaluator.
-/

namespace Flapjack

/-! `PanWordLab` is the exact Lean counterpart of CakeML's one-constructor
    `word_lab` datatype (`cakeml/pancake/semantics/panSemScript.sml:17`,
    `word_lab = Word ('a word)`): one constructor with a single payload of the
    word type.  `panIsWord`/`panTheWord` are the exact counterparts of HOL
    `isWord_def` (`:26`) and `theWord_def` (`:30`).

    The `@[hol ...]` tag is intentionally NOT attached here: the counterpart
    file for `panSemScript.sml` is `Flapjack/Pancake/Semantics/PanSem.lean`
    (see `docs/HOL-LAYOUT.md`), and this datatype is defined in
    `Flapjack/PanValues.lean`.  An exact-tagged port (or a checked relocation)
    is tracked by bead `flapjack-pxn.18.3.6.8`. -/
inductive PanWordLab (α : Type u) where
  | word (value : α)
  deriving BEq, DecidableEq, Repr

def panIsWord : PanWordLab α → Bool
  | .word _ => true

def panTheWord : PanWordLab α → α
  | .word value => value

/-! `PanValue` is the executable counterpart of CakeML's three-constructor
    value datatype `v` (`cakeml/pancake/semantics/panSemScript.sml:22`,
    `v = Val ('a word_lab) | RStruct (v list) | NStruct stcname ((fldname # v) list)`),
    NOT of `word_lab` (which is the one-constructor wrapper above).

    It is NOT statement-exact: `v`'s `Val` constructor stores an `'a word_lab`
    while `PanValue.word` stores the word payload `α` directly.  Constructor
    arities (1/1/2) and the `RStruct`/`NStruct` field types agree, but the
    first constructor's field type differs, so no exact `@[hol ... "v"]`
    (Datatype) tag is attached.  A faithful port is tracked by bead
    `flapjack-pxn.18.3.6.8`. -/
inductive PanValue (α : Type u) where
  | word (value : α)
  | rStruct (fields : List (PanValue α))
  | nStruct (name : StructName) (fields : List (FieldName × PanValue α))
  deriving Repr

def panIsValWord : PanValue α → Bool
  | .word _ => true
  | .rStruct _ | .nStruct _ _ => false

/- `theValWord` is only defined by CakeML on a word value.  The `Option`
   result records that definedness instead of introducing an arbitrary value
   for structured inputs; this totalized `Option α` version is therefore not
   statement-exact against the partial HOL `theValWord_def` (`:34`). -/
def panTheValWord : PanValue α → Option α
  | .word value => some value
  | .rStruct _ | .nStruct _ _ => none

/-! Target-supplied byte-addressed operations for structured source memory.

    Structured memory may contain records, but Pancake's sub-word operations
    are defined only on word cells.  The access record therefore makes a
    non-word cell fail instead of silently treating it as a scalar. -/
structure PanValueMemoryAccess (α : Type u) where
  domain : α → Bool
  wordOp : BinOp → List α → Option α
  compare : Cmp → α → α → α
  shift : Shift → α → α → Option α
  readWord : (α → Bool) → (α → Option (PanValue α)) → α → α → Option α
  readByte : (α → Bool) → (α → Option (PanValue α)) → α → α → Option α
  read16 : (α → Bool) → (α → Option (PanValue α)) → α → α → Option α
  read32 : (α → Bool) → (α → Option (PanValue α)) → α → α → Option α
  storeWord : (α → Bool) → (α → Option (PanValue α)) → α → α → α →
    Option (α → Option (PanValue α))
  storeByte : (α → Bool) → (α → Option (PanValue α)) → α → α → α →
    Option (α → Option (PanValue α))
  store16 : (α → Bool) → (α → Option (PanValue α)) → α → α → α →
    Option (α → Option (PanValue α))
  store32 : (α → Bool) → (α → Option (PanValue α)) → α → α → α →
    Option (α → Option (PanValue α))
  /-- Shared-memory operations are separate from ordinary source-memory
      operations.  The callback may ignore the source memory when it is
      backed by an external FFI oracle. -/
  sharedRead : (α → Option (PanValue α)) → α → OpSize → α → Option (PanValue α)
  sharedStore : (α → Option (PanValue α)) → α → OpSize → α → PanValue α →
    Option (α → Option (PanValue α))

def panValueWordMemory (memory : α → Option (PanValue α)) : α → Option α :=
  fun address => match memory address with
    | some (.word value) => some value
    | _ => none

def panValueMemoryAccessOfModel [BEq α] [Add α] [OfNat α 0] [OfNat α 1]
    [OfNat α 2] [OfNat α 3] (model : PanMemoryModel α)
    (domain : α → Bool := fun _ => true)
    (sharedDomain : α → Bool := domain)
    (bigEndian : Bool := false) : PanValueMemoryAccess α :=
  { domain := domain
    wordOp := model.wordOp
    compare := model.compare
    shift := model.shift
    readWord := fun _ memory _ address => do
      let value ← if domain address then memory address else none
      let .word value := value | none
      pure value
    storeWord := fun _ memory _ address value =>
      if domain address then
        some (fun current =>
          if current == address then some (.word value) else memory current)
      else none
    readByte := fun _ memory bytesInWord address =>
      panModelReadByte model domain (panValueWordMemory memory)
        bytesInWord address bigEndian
    read16 := fun _ memory bytesInWord address =>
      if model.aligned 2 address then
        let alignedAddress := model.byteAlign bytesInWord address
        if domain alignedAddress then do
          let cell ← memory alignedAddress
          let .word cell := cell | none
          pure (model.wordOfBytes bigEndian
            [model.getByte bytesInWord address cell bigEndian,
             model.getByte bytesInWord (address + 1) cell bigEndian])
        else none
      else none
    read32 := fun _ memory bytesInWord address =>
      panModelRead32 model domain (panValueWordMemory memory)
        bytesInWord address bigEndian
    storeByte := fun _ memory bytesInWord address value => do
      let alignedAddress := model.byteAlign bytesInWord address
      if domain alignedAddress then
        let cell ← memory alignedAddress
        let .word cell := cell | none
        let updated := model.setByte bytesInWord address value cell bigEndian
        pure (fun current =>
          if current == alignedAddress then some (.word updated) else memory current)
      else none
    store16 := fun _ memory bytesInWord address value => do
      if model.aligned 2 address then
        let alignedAddress := model.byteAlign bytesInWord address
        if domain alignedAddress then
          let cell ← memory alignedAddress
          let .word cell := cell | none
          let cell0 := model.setByte bytesInWord address
            (model.getByte bytesInWord 0 value bigEndian) cell bigEndian
          let cell1 := model.setByte bytesInWord (address + 1)
            (model.getByte bytesInWord 1 value bigEndian) cell0 bigEndian
          pure (fun current =>
            if current == alignedAddress then some (.word cell1) else memory current)
        else none
      else none
    store32 := fun _ memory bytesInWord address value => do
      if model.aligned 4 address then
        let alignedAddress := model.byteAlign bytesInWord address
        if domain alignedAddress then
          let cell ← memory alignedAddress
          let .word cell := cell | none
          let cell0 := model.setByte bytesInWord address
            (model.getByte bytesInWord 0 value bigEndian) cell bigEndian
          let cell1 := model.setByte bytesInWord (address + 1)
            (model.getByte bytesInWord 1 value bigEndian) cell0 bigEndian
          let cell2 := model.setByte bytesInWord (address + 2)
            (model.getByte bytesInWord 2 value bigEndian) cell1 bigEndian
          let cell3 := model.setByte bytesInWord (address + 3)
            (model.getByte bytesInWord 3 value bigEndian) cell2 bigEndian
          pure (fun current =>
            if current == alignedAddress then some (.word cell3) else memory current)
        else none
      else none
    sharedRead := fun memory bytesInWord size address =>
      match size with
      | .opW => (panModelReadWord sharedDomain (panValueWordMemory memory) address).map .word
      | .op8 => (panModelReadByte model sharedDomain (panValueWordMemory memory)
          bytesInWord address bigEndian).map .word
      /- CakeML's `sh_mem_load` has no `aligned` requirement for Op16/Op32;
         the only check is `byte_align addr ∈ sh_memaddrs`
         (`panSemScript.sml:519-520`). -/
      | .op16 =>
          let alignedAddress := model.byteAlign bytesInWord address
          if sharedDomain alignedAddress then do
            let cell ← memory alignedAddress
            let .word cell := cell | none
            pure (.word (model.wordOfBytes bigEndian
              [model.getByte bytesInWord address cell bigEndian,
               model.getByte bytesInWord (address + 1) cell bigEndian]))
          else none
      | .op32 =>
          let alignedAddress := model.byteAlign bytesInWord address
          if sharedDomain alignedAddress then do
            let cell ← memory alignedAddress
            let .word cell := cell | none
            pure (.word (model.wordOfBytes bigEndian
              [model.getByte bytesInWord address cell bigEndian,
               model.getByte bytesInWord (address + 1) cell bigEndian,
               model.getByte bytesInWord (address + 2) cell bigEndian,
               model.getByte bytesInWord (address + 3) cell bigEndian]))
          else none
    sharedStore := fun memory bytesInWord size address value =>
      match value with
      | .word value => match size with
          | .opW => if sharedDomain address then
              some (fun current =>
                if current == address then some (.word value) else memory current)
            else none
          | .op8 => (panModelStoreByte model sharedDomain (panValueWordMemory memory)
              bytesInWord address value bigEndian).map fun wordMemory current =>
                if current == model.byteAlign bytesInWord address then
                  (wordMemory current).map .word
                else memory current
          /- CakeML's `sh_mem_store` has no `aligned` requirement for
             Op16/Op32; the only check is `byte_align addr ∈ sh_memaddrs`
             (`panSemScript.sml:537-540`). -/
          | .op16 =>
              let alignedAddress := model.byteAlign bytesInWord address
              if sharedDomain alignedAddress then do
                let cell ← memory alignedAddress
                let .word cell := cell | none
                let cell0 := model.setByte bytesInWord address
                  (model.getByte bytesInWord 0 value bigEndian) cell bigEndian
                let cell1 := model.setByte bytesInWord (address + 1)
                  (model.getByte bytesInWord 1 value bigEndian) cell0 bigEndian
                pure (fun current =>
                  if current == alignedAddress then some (.word cell1) else memory current)
              else none
          | .op32 =>
              let alignedAddress := model.byteAlign bytesInWord address
              if sharedDomain alignedAddress then do
                let cell ← memory alignedAddress
                let .word cell := cell | none
                let cell0 := model.setByte bytesInWord address
                  (model.getByte bytesInWord 0 value bigEndian) cell bigEndian
                let cell1 := model.setByte bytesInWord (address + 1)
                  (model.getByte bytesInWord 1 value bigEndian) cell0 bigEndian
                let cell2 := model.setByte bytesInWord (address + 2)
                  (model.getByte bytesInWord 2 value bigEndian) cell1 bigEndian
                let cell3 := model.setByte bytesInWord (address + 3)
                  (model.getByte bytesInWord 3 value bigEndian) cell2 bigEndian
                pure (fun current =>
                  if current == alignedAddress then some (.word cell3) else memory current)
              else none
      | .rStruct _ | .nStruct _ _ => none
  }

def panValueFlatOffset [Add α] (bytesInWord address : α) : Nat → α
  | 0 => address
  | count + 1 => panValueFlatOffset bytesInWord address count + bytesInWord

def panValueFlatValueFuel : PanValue α → Nat
  | .word _ => 1
  | .rStruct fields => 1 + panValueFlatValueListFuel fields
  | .nStruct _ fields => 1 + panValueFlatValueFieldListFuel fields
where
  panValueFlatValueListFuel : List (PanValue α) → Nat
    | [] => 0
    | value :: values =>
        panValueFlatValueFuel value + panValueFlatValueListFuel values

  panValueFlatValueFieldListFuel : List (FieldName × PanValue α) → Nat
    | [] => 0
    | (_, value) :: fields =>
        panValueFlatValueFuel value + panValueFlatValueFieldListFuel fields

def panValueFlatWordsFuel : Nat → PanValue α → List α
  | 0, _ => []
  | _fuel + 1, .word value => [value]
  | fuel + 1, .rStruct fields => panValueFlatWordsListFuel fuel fields
  | fuel + 1, .nStruct _ fields => panValueFlatWordsFieldListFuel fuel fields
where
  panValueFlatWordsListFuel : Nat → List (PanValue α) → List α
    | _, [] => []
    | 0, _ :: _ => []
    | fuel + 1, value :: values =>
        panValueFlatWordsFuel fuel value ++ panValueFlatWordsListFuel fuel values

  panValueFlatWordsFieldListFuel : Nat →
      List (FieldName × PanValue α) → List α
    | _, [] => []
    | 0, _ :: _ => []
    | fuel + 1, (_, value) :: fields =>
        panValueFlatWordsFuel fuel value ++
          panValueFlatWordsFieldListFuel fuel fields

def panValueFlatWords (value : PanValue α) : List α :=
  -- The list helper consumes one unit both when descending through a
  -- container and when entering each contained value.  Twice the structural
  -- fuel is therefore needed to flatten nested records without truncating
  -- their leaves.
  panValueFlatWordsFuel (2 * panValueFlatValueFuel value + 1) value

theorem panValueFlatWords_nStruct_word_fields
    (name : StructName) (values : List (FieldName × α)) :
    panValueFlatWords
        (.nStruct name (values.map (fun (field, value) => (field, .word value)))) =
      values.map Prod.snd := by
  have hlistFuel : ∀ values : List (FieldName × α),
      panValueFlatValueFuel.panValueFlatValueFieldListFuel
          (values.map (fun (field, value) => (field, .word value))) =
        values.length := by
    intro values
    induction values with
    | nil => simp [panValueFlatValueFuel.panValueFlatValueFieldListFuel]
    | cons value values ih =>
        simp [panValueFlatValueFuel.panValueFlatValueFieldListFuel,
          panValueFlatValueFuel, ih, Nat.add_comm]
  have hvalueFuel :
      panValueFlatValueFuel
          (.nStruct name
            (values.map (fun (field, value) => (field, .word value)))) =
        values.length + 1 := by
    simp only [panValueFlatValueFuel]
    rw [hlistFuel values]
    omega
  have hwordsFuel : ∀ (fuel : Nat) (values : List (FieldName × α)),
      values.length < fuel →
        panValueFlatWordsFuel.panValueFlatWordsFieldListFuel fuel
            (values.map (fun (field, value) => (field, .word value))) =
          values.map Prod.snd := by
    intro fuel values
    induction values generalizing fuel with
    | nil => intro; simp [panValueFlatWordsFuel.panValueFlatWordsFieldListFuel]
    | cons value values ih =>
        cases fuel with
        | zero => simp_all
        | succ fuel =>
            intro hlength
            cases fuel with
            | zero => simp_all
            | succ fuel =>
                simp only [List.length_cons] at hlength
                have htail : values.length < fuel + 1 := by omega
                simp [panValueFlatWordsFuel.panValueFlatWordsFieldListFuel,
                  panValueFlatWordsFuel, ih (fuel + 1) htail]
  rw [panValueFlatWords, hvalueFuel]
  simp only [panValueFlatWordsFuel]
  exact hwordsFuel (2 * (values.length + 1)) values (by omega)

def panValueFlatShapeFuel : Shape → Nat
  | .one => 1
  | .comb shapes => 1 + panValueFlatShapeListFuel shapes
  | .named _ => 1
where
  panValueFlatShapeListFuel : List Shape → Nat
    | [] => 0
    | shape :: shapes =>
        1 + panValueFlatShapeFuel shape + panValueFlatShapeListFuel shapes

def panValueFlatFieldsFuel : List (FieldName × Shape) → Nat
  | [] => 0
  | (_, shape) :: fields =>
      1 + panValueFlatShapeFuel shape + panValueFlatFieldsFuel fields

def panValueFlatContextFuel : StructContext → Nat
  | [] => 0
  | (_, info) :: context =>
      panValueFlatFieldsFuel info.fields + panValueFlatContextFuel context

def panValueFlatReadWord [BEq α]
    (memory : α → Option (PanValue α)) (bytesInWord : α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (address : α) : Option α :=
  match memoryAccess with
  | none =>
      match memory address with
      | some (.word value) => some value
      | _ => none
  | some access => access.readWord access.domain memory bytesInWord address

mutual
  def panValueFlatLoadFuel [BEq α] [Add α]
      (structs : StructContext) (readWord : α → Option α)
      (bytesInWord : α) : Nat → Shape → α → Option (PanValue α)
    | 0, _, _ => none
    | _fuel + 1, .one, address => (readWord address).map .word
    | fuel + 1, .comb shapes, address =>
        (panValueFlatLoadListFuel structs readWord bytesInWord fuel shapes address).map
          .rStruct
    | fuel + 1, .named name, address => do
        let (info, structs') ← lookupInfoWithRest name structs
        let fields ← panValueFlatLoadFieldsFuel structs' readWord bytesInWord fuel
          info.fields address
        pure (.nStruct name fields)
  termination_by fuel _shape _address => fuel

  def panValueFlatLoadListFuel [BEq α] [Add α]
      (structs : StructContext) (readWord : α → Option α)
      (bytesInWord : α) : Nat → List Shape → α → Option (List (PanValue α))
    | _, [], _ => some []
    | 0, _ :: _, _ => none
    | fuel + 1, shape :: shapes, address => do
        let value ← panValueFlatLoadFuel structs readWord bytesInWord fuel shape address
        let values ← panValueFlatLoadListFuel structs readWord bytesInWord fuel shapes
          (panValueFlatOffset bytesInWord address (shapeSizeWithContext structs shape))
        pure (value :: values)
  termination_by fuel _shapes _address => fuel

  def panValueFlatLoadFieldsFuel [BEq α] [Add α]
      (structs : StructContext) (readWord : α → Option α)
      (bytesInWord : α) : Nat → List (FieldName × Shape) → α →
      Option (List (FieldName × PanValue α))
    | _, [], _ => some []
    | 0, _ :: _, _ => none
    | fuel + 1, (field, shape) :: fields, address => do
        let value ← panValueFlatLoadFuel structs readWord bytesInWord fuel shape address
        let values ← panValueFlatLoadFieldsFuel structs readWord bytesInWord fuel fields
          (panValueFlatOffset bytesInWord address (shapeSizeWithContext structs shape))
        pure ((field, value) :: values)
  termination_by fuel _fields _address => fuel
end

/-- Field loads preserve field names around the ordinary list load of the
    corresponding shapes. This is the representation bridge needed when a
    named struct load is compiled into a flattened `Comb`. -/
theorem panValueFlatLoadFieldsFuel_eq_zip [BEq α] [Add α]
    (structs : StructContext) (readWord : α → Option α) (bytesInWord : α) :
    ∀ (fuel : Nat) (fields : List (FieldName × Shape)) (address : α),
      panValueFlatLoadFieldsFuel structs readWord bytesInWord fuel fields address =
        (panValueFlatLoadListFuel structs readWord bytesInWord fuel
          (fields.map Prod.snd) address).map
            (fun values => (fields.map Prod.fst).zip values) := by
  intro fuel
  induction fuel with
  | zero =>
      intro fields address
      cases fields <;> simp [panValueFlatLoadFieldsFuel, panValueFlatLoadListFuel]
  | succ fuel ih =>
      intro fields address
      cases fields with
      | nil => simp [panValueFlatLoadFieldsFuel, panValueFlatLoadListFuel]
      | cons field fields =>
          obtain ⟨name, shape⟩ := field
          let nextAddress := panValueFlatOffset bytesInWord address
            (shapeSizeWithContext structs shape)
          simp only [panValueFlatLoadFieldsFuel, panValueFlatLoadListFuel, List.map_cons]
          cases hhead : panValueFlatLoadFuel structs readWord bytesInWord fuel shape address with
          | none => simp
          | some value =>
              have htail := ih fields nextAddress
              dsimp [nextAddress] at htail
              rw [htail]
              cases hvalues : panValueFlatLoadListFuel structs readWord bytesInWord fuel
                  (fields.map Prod.snd)
                  (panValueFlatOffset bytesInWord address
                    (shapeSizeWithContext structs shape)) with
              | none => simp
              | some values => simp [List.zip_cons_cons]

def panValueFlatLoad [BEq α] [Add α]
    (structs : StructContext) (memory : α → Option (PanValue α))
    (bytesInWord : α) (address : α) (shape : Shape)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (PanValue α) :=
  if isWfShape structs shape then
    panValueFlatLoadFuel structs
      (panValueFlatReadWord memory bytesInWord memoryAccess)
      bytesInWord
      (panValueFlatContextFuel structs + panValueFlatShapeFuel shape + 1)
      shape address
  else none

/-- Counterpart of Cake's `mem_loads` (`cakeml/pancake/semantics/panSemScript.sml`):
    the flat load of a whole list of shapes. -/
def panValueFlatLoadList [BEq α] [Add α]
    (structs : StructContext) (memory : α → Option (PanValue α))
    (bytesInWord : α) (address : α) (shapes : List Shape)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (List (PanValue α)) :=
  if shapes.all (isWfShape structs) then
    panValueFlatLoadListFuel structs
      (panValueFlatReadWord memory bytesInWord memoryAccess)
      bytesInWord
      (panValueFlatContextFuel structs +
        panValueFlatShapeFuel.panValueFlatShapeListFuel shapes + 1)
      shapes address
  else none

/-- Counterpart of Cake's `mem_load_flds` (`cakeml/pancake/semantics/panSemScript.sml`):
    the flat load of a record's fields. -/
def panValueFlatLoadFields [BEq α] [Add α]
    (structs : StructContext) (memory : α → Option (PanValue α))
    (bytesInWord : α) (address : α) (fields : List (FieldName × Shape))
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (List (FieldName × PanValue α)) :=
  if fields.all (fun field => isWfShape structs field.2) then
    panValueFlatLoadFieldsFuel structs
      (panValueFlatReadWord memory bytesInWord memoryAccess)
      bytesInWord
      (panValueFlatContextFuel structs + panValueFlatFieldsFuel fields + 1)
      fields address
  else none

def panValueFlatStoreWords [BEq α] [Add α]
    (storeWord : (α → Option (PanValue α)) → α → α →
      Option (α → Option (PanValue α)))
    (bytesInWord : α) (memory : α → Option (PanValue α)) :
    α → List α → Option (α → Option (PanValue α))
  | _, [] => some memory
  | address, value :: values => do
      let memory ← storeWord memory address value
      panValueFlatStoreWords storeWord bytesInWord memory
        (panValueFlatOffset bytesInWord address 1) values
termination_by _address values => values.length
decreasing_by
  simp_wf

/-- Flapjack's context-parameterized scalar-shape function. The
    `StructContext` argument is unused, so this is the context-free tagged
    exact `panSemShapeOf` port with an extra (vacuous) parameter; the equality
    `panValueShape context value = panSemShapeOf value` is proved as
    `panValueShape_eq_panSemShapeOf_tagged` in `Pancake/Semantics/PanSem.lean` (bead
    `flapjack-pxn.18.3.6.4`). It stays untagged because HOL `shape_of` has no
    context parameter, and production callers may eventually be routed through
    `panSemShapeOf` directly. -/
def panValueShape (context : StructContext) : PanValue α → Shape
  | .word _ => .one
  | .rStruct fields => .comb (fields.map (panValueShape context))
  | .nStruct name _ => .named name
termination_by value => sizeOf value

mutual
  /-- Flapjack-only generic helper for the canonical zero-valued expression of
      a production shape. It is not tagged as HOL `shape_val`: its expression
      carrier accepts arbitrary `α`, whereas HOL's `Const` is indexed by a
      fixed word width. The production parser's add-with-carry initializer now
      calls the exact `shapeValHOL` through `shapeValViaHOL`; this helper stays
      for evaluator proofs and the checked bridge below. -/
  def shapeVal [OfNat α 0] : Shape → Exp α
    | .one => .const 0
    | .comb shapes => .rStruct (shapeVals shapes)
    | .named _ => .const 0
  termination_by shape => sizeOf shape
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  /-- Flapjack-only generic list helper; HOL declares no separate theorem or
      definition named `shape_vals` beyond the mutual `shape_val_def`. -/
  def shapeVals [OfNat α 0] : List Shape → List (Exp α)
    | [] => []
    | shape :: shapes => shapeVal shape :: shapeVals shapes
  termination_by shapes => sizeOf shapes
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Flapjack-specific equation: the generic list helper is a map. HOL's
`shape_val_def` defines this behavior recursively and has no separate map
theorem. -/
theorem shapeVals_eq_map {α : Type} [OfNat α 0] (shapes : List Shape) :
    shapeVals (α := α) shapes = shapes.map shapeVal := by
  induction shapes with
  | nil => simp [shapeVals]
  | cons shape shapes ih => simp [shapeVals, ih]

/-- The exact `panLang$shape_val` result, decoded through the reviewed
shape/expression codecs, agrees with the generic evaluator helper. This is a
Flapjack-specific bridge: the generic helper's carrier is not itself the HOL
definition, while parser execution uses `shapeValViaHOL`. -/
theorem expOfHOL_shapeValHOL {width : Nat} [NeZero width] :
    (shape : Flapjack.Pancake.PanLang.ShapeHOL) →
      Flapjack.Pancake.PanLang.expOfHOL
          (Flapjack.Pancake.PanLang.shapeValHOL (width := width) shape) =
        shapeVal (Flapjack.Pancake.PanLang.shapeOfHOL shape)
  | .one => by simp [Flapjack.Pancake.PanLang.shapeValHOL,
      Flapjack.Pancake.PanLang.shapeOfHOL, Flapjack.Pancake.PanLang.expOfHOL,
      shapeVal]
  | .named _ => by simp [Flapjack.Pancake.PanLang.shapeValHOL,
      Flapjack.Pancake.PanLang.shapeOfHOL, Flapjack.Pancake.PanLang.expOfHOL,
      shapeVal]
  | .comb shapes => by
      simp only [Flapjack.Pancake.PanLang.shapeValHOL,
        Flapjack.Pancake.PanLang.shapeValsHOL_eq_map,
        Flapjack.Pancake.PanLang.shapeOfHOL,
        Flapjack.Pancake.PanLang.expOfHOL, shapeVal, shapeVals_eq_map,
        List.map_map]
      congr 1
      exact List.map_congr_left
        (fun field _ => expOfHOL_shapeValHOL (width := width) field)

mutual
  /-- Counterpart of Cake's `is_wf_shape_v`
      (`cakeml/pancake/semantics/panPropsScript.sml:24`): every scalar is well
      formed, a record is well formed when all of its fields are, and a named
      record additionally needs its name in the context. -/
  def panValueIsWf (context : StructContext) : PanValue α → Bool
    | .word _ => true
    | .rStruct fields => panValueIsWfValues context fields
    | .nStruct name fields =>
        (lookupInfo name context).isSome && panValueIsWfFields context fields
  termination_by value => sizeOf value
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  def panValueIsWfValues (context : StructContext) : List (PanValue α) → Bool
    | [] => true
    | value :: values =>
        panValueIsWf context value && panValueIsWfValues context values
  termination_by values => sizeOf values
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  def panValueIsWfFields (context : StructContext) :
      List (FieldName × PanValue α) → Bool
    | [] => true
    | (_, value) :: fields =>
        panValueIsWf context value && panValueIsWfFields context fields
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Counterpart of Cake's `is_wf_shape_of_v`
    (`cakeml/pancake/semantics/panPropsScript.sml:38`). -/
theorem panValueIsWf_isWfShape_panValueShape (structs : StructContext)
    (value : PanValue α) :
    panValueIsWf structs value = true →
      isWfShape structs (panValueShape structs value) = true := by
  induction value using panValueIsWf.induct
    (motive2 := fun fields => panValueIsWfFields structs fields = true →
      fields.all (fun field =>
        isWfShape structs (panValueShape structs field.2)) = true)
    (motive3 := fun values => panValueIsWfValues structs values = true →
      isWfShape.isWfShapeList structs
        (values.map (panValueShape structs)) = true) with
  | case1 scalar => intro _; simp [panValueShape, isWfShape]
  | case2 fields ih =>
      intro h
      simp only [panValueIsWf] at h
      simp only [panValueShape, isWfShape]
      exact ih h
  | case3 name fields ih =>
      intro h
      simp only [panValueIsWf, Bool.and_eq_true] at h
      obtain ⟨hname, _⟩ := h
      simp only [panValueShape, isWfShape]
      simpa only [isWfShapeHOL_named, lookupInfo_toHOL_isSome] using hname
  | case4 => simp
  | case5 fst value fields ihValue ihFields =>
      rename_i h
      simp only [panValueIsWfFields, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨ihValue h1, ihFields h2⟩
  | case6 => simp [isWfShape.isWfShapeList]
  | case7 value values ihValue ihValues =>
      rename_i h
      simp only [panValueIsWfValues, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      simp only [List.map_cons, isWfShape.isWfShapeList, Bool.and_eq_true]
      exact ⟨ihValue h1, ihValues h2⟩

/-- Flapjack's context-parameterized scalar-shape fact. Its extra
    `StructContext` argument means it is not itself the exact HOL
    `shape_of_alt` statement; the context-free `panSemShapeOf` port and exact
    proof counterpart live in `Pancake/Semantics/PanSem.lean` and
    `Pancake/Proofs/PanToCrep.lean`. -/
theorem panValueShape_word (structs : StructContext) (value : α) :
    panValueShape structs (.word value) = .one := by
  simp [panValueShape]

/-- Counterpart of Cake's `is_wf_shape_v_drop`
    (`cakeml/pancake/semantics/panPropsScript.sml:63`): well-formedness of a
    value against a suffix of the struct context implies well-formedness
    against the whole context, because a name found in the suffix is also
    found (at least as far left) in the whole context. -/
theorem panValueIsWf_of_drop (context : StructContext) (value : PanValue α)
    (n : Nat) :
    panValueIsWf (context.drop n) value = true →
      panValueIsWf context value = true := by
  induction value using panValueIsWf.induct
    (motive2 := fun fields =>
      panValueIsWfFields (context.drop n) fields = true →
        panValueIsWfFields context fields = true)
    (motive3 := fun values =>
      panValueIsWfValues (context.drop n) values = true →
        panValueIsWfValues context values = true) with
  | case1 scalar => intro _; simp only [panValueIsWf]
  | case2 fields ih =>
      intro h
      simp only [panValueIsWf] at h ⊢
      exact ih h
  | case3 name fields ih =>
      intro h
      simp only [panValueIsWf, Bool.and_eq_true] at h ⊢
      obtain ⟨hname, hfields⟩ := h
      exact ⟨lookupInfo_isSome_drop name context n hname, ih hfields⟩
  | case4 => simp [panValueIsWfFields]
  | case5 fst value fields ihValue ihFields =>
      rename_i h
      simp only [panValueIsWfFields, Bool.and_eq_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨ihValue h1, ihFields h2⟩
  | case6 => simp [panValueIsWfValues]
  | case7 value values ihValue ihValues =>
      rename_i h
      simp only [panValueIsWfValues, Bool.and_eq_true] at h ⊢
      obtain ⟨h1, h2⟩ := h
      exact ⟨ihValue h1, ihValues h2⟩

/-- Converse direction of `panValueIsWf_isWfShape_panValueShape` at the empty
    struct context: a value whose shape is well formed has no named records,
    hence is well formed itself.  This is the local helper behind Cake's
    `is_wf_shape_v_nil` (`cakeml/pancake/semantics/panPropsScript.sml:56`). -/
theorem panValueIsWf_of_isWfShape_panValueShape_nil (value : PanValue α) :
    isWfShape ([] : StructContext) (panValueShape ([] : StructContext) value) = true →
      panValueIsWf ([] : StructContext) value = true := by
  induction value using panValueIsWf.induct
    (motive2 := fun fields =>
      isWfShape.isWfShapeList ([] : StructContext)
        (fields.map (fun (field : FieldName × PanValue α) =>
          panValueShape ([] : StructContext) field.2)) = true →
        panValueIsWfFields ([] : StructContext) fields = true)
    (motive3 := fun values =>
      isWfShape.isWfShapeList ([] : StructContext)
        (values.map (panValueShape ([] : StructContext))) = true →
        panValueIsWfValues ([] : StructContext) values = true) with
  | case1 _ => intro _; simp only [panValueIsWf]
  | case2 fields ih =>
      intro h
      simp only [panValueIsWf]
      exact ih (by simpa [panValueShape, isWfShape] using h)
  | case3 _ _ _ => intro h; simp [panValueShape, isWfShape, lookupInfo] at h
  | case4 => simp [panValueIsWfFields]
  | case5 fst value fields ihValue ihFields =>
      rename_i h
      simp only [List.map_cons, isWfShape.isWfShapeList, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      simp only [panValueIsWfFields, Bool.and_eq_true]
      exact ⟨ihValue h1, ihFields h2⟩
  | case6 => simp [panValueIsWfValues]
  | case7 value values ihValue ihValues =>
      rename_i h
      simp only [List.map_cons, isWfShape.isWfShapeList, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      simp only [panValueIsWfValues, Bool.and_eq_true]
      exact ⟨ihValue h1, ihValues h2⟩

/-- Counterpart of Cake's `is_wf_shape_v_nil`
    (`cakeml/pancake/semantics/panPropsScript.sml:56`): at the empty struct
    context, well-formedness of a value is exactly well-formedness of its
    shape. -/
theorem panValueIsWf_eq_isWfShape_panValueShape_of_nil (context : StructContext)
    (value : PanValue α) (hcontext : context = []) :
    isWfShape context (panValueShape context value) =
      panValueIsWf context value := by
  subst hcontext
  rw [Bool.eq_iff_iff]
  exact ⟨panValueIsWf_of_isWfShape_panValueShape_nil value,
    panValueIsWf_isWfShape_panValueShape [] value⟩

/-! CakeML `panPropsScript.sml` `mem_load_is_wf_shape_v`: whatever the flat
    memory load returns is a well-formed value.  The fuel-based loaders below
    mirror `mem_load`/`mem_loads`/`mem_load_flds`; the three-conjunct Cake
    statement is expressed as one mutual induction over the three loaders. -/

theorem lookupInfoWithRest_drop [BEq String] (name : String) (structs : StructContext)
    (info : StructInfo) (rest : StructContext)
    (h : lookupInfoWithRest name structs = some (info, rest)) :
    ∃ k, rest = structs.drop k := by
  induction structs with
  | nil => simp [lookupInfoWithRest] at h
  | cons entry tail ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hc : candidate == name
      · simp [lookupInfoWithRest, hc] at h
        obtain ⟨-, hrest⟩ := h
        subst hrest
        exact ⟨1, rfl⟩
      · simp [lookupInfoWithRest, hc] at h
        obtain ⟨k, hk⟩ := ih h
        exact ⟨k + 1, by rw [hk, List.drop_succ_cons]⟩

theorem lookupInfoWithRest_isSome [BEq String] (name : String) (structs : StructContext)
    (info : StructInfo) (rest : StructContext)
    (h : lookupInfoWithRest name structs = some (info, rest)) :
    (lookupInfo name structs).isSome = true := by
  induction structs with
  | nil => simp [lookupInfoWithRest] at h
  | cons entry tail ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hc : candidate == name
      · simp [hc, lookupInfo]
      · simp only [hc, lookupInfo]
        exact ih (by simpa [lookupInfoWithRest, hc] using h)

theorem panValueIsWfFields_of_drop (fields : List (FieldName × PanValue α))
    (context : StructContext) (n : Nat) :
    panValueIsWfFields (context.drop n) fields = true →
      panValueIsWfFields context fields = true := by
  induction fields with
  | nil => intro _; simp [panValueIsWfFields]
  | cons field fields ih =>
      obtain ⟨name, value⟩ := field
      intro h
      simp only [panValueIsWfFields, Bool.and_eq_true] at h ⊢
      exact ⟨panValueIsWf_of_drop context value n h.1, ih h.2⟩

theorem panValueIsWfValues_of_drop (values : List (PanValue α))
    (context : StructContext) (n : Nat) :
    panValueIsWfValues (context.drop n) values = true →
      panValueIsWfValues context values = true := by
  induction values with
  | nil => intro _; simp [panValueIsWfValues]
  | cons value values ih =>
      intro h
      simp only [panValueIsWfValues, Bool.and_eq_true] at h ⊢
      exact ⟨panValueIsWf_of_drop context value n h.1, ih h.2⟩

theorem panValueFlatLoadFuel_wf [BEq α] [Add α]
    (structs : StructContext) (readWord : α → Option α) (bytesInWord : α) :
    ∀ (fuel : Nat) (shape : Shape) (address : α) (value : PanValue α),
      panValueFlatLoadFuel structs readWord bytesInWord fuel shape address = some value →
        panValueIsWf structs value = true := by
  apply panValueFlatLoadFuel.induct (α := α) bytesInWord
    (motive1 := fun structs fuel shape address => ∀ value,
      panValueFlatLoadFuel structs readWord bytesInWord fuel shape address = some value →
        panValueIsWf structs value = true)
    (motive2 := fun structs fuel fields address => ∀ values,
      panValueFlatLoadFieldsFuel structs readWord bytesInWord fuel fields address = some values →
        panValueIsWfFields structs values = true)
    (motive3 := fun structs fuel shapes address => ∀ values,
      panValueFlatLoadListFuel structs readWord bytesInWord fuel shapes address = some values →
        panValueIsWfValues structs values = true)
  · intro structs x x_1 value h
    simp [panValueFlatLoadFuel] at h
  · intro structs fuel address value h
    obtain ⟨word, -, rfl⟩ := by simpa [panValueFlatLoadFuel] using h
    simp [panValueIsWf]
  · intro structs fuel shapes address ih value h
    obtain ⟨values, hvalues, rfl⟩ := by simpa [panValueFlatLoadFuel] using h
    simpa [panValueIsWf] using ih values hvalues
  · intro structs fuel name address ih value h
    cases hlookup : lookupInfoWithRest name structs with
    | none => simp [panValueFlatLoadFuel, hlookup] at h
    | some pair =>
        obtain ⟨info, rest⟩ := pair
        cases hfields : panValueFlatLoadFieldsFuel rest readWord bytesInWord fuel
            info.fields address with
        | none => simp [panValueFlatLoadFuel, hlookup, hfields] at h
        | some fields =>
            simp [panValueFlatLoadFuel, hlookup, hfields] at h
            subst h
            have hisSome := lookupInfoWithRest_isSome name structs info rest hlookup
            obtain ⟨k, hk⟩ := lookupInfoWithRest_drop name structs info rest hlookup
            have hwfFields : panValueIsWfFields structs fields = true := by
              rw [hk] at hfields
              exact panValueIsWfFields_of_drop fields structs k
                (ih info (structs.drop k) fields hfields)
            simp [panValueIsWf, hisSome, hwfFields]
  · intro structs x x_1 values h
    simp [panValueFlatLoadFieldsFuel] at h
    subst h
    simp [panValueIsWfFields]
  · intro structs head tail x values h
    simp [panValueFlatLoadFieldsFuel] at h
  · intro structs fuel field shape fields address ihHead ihTail values h
    cases hvalue : panValueFlatLoadFuel structs readWord bytesInWord fuel shape address with
    | none => simp [panValueFlatLoadFieldsFuel, hvalue] at h
    | some value =>
        cases hvalues : panValueFlatLoadFieldsFuel structs readWord bytesInWord fuel fields
            (panValueFlatOffset bytesInWord address (shapeSizeWithContext structs shape)) with
        | none => simp [panValueFlatLoadFieldsFuel, hvalue, hvalues] at h
        | some rest =>
            simp [panValueFlatLoadFieldsFuel, hvalue, hvalues] at h
            subst h
            simp only [panValueIsWfFields, Bool.and_eq_true]
            exact ⟨ihHead value hvalue, ihTail rest hvalues⟩
  · intro structs x x_1 values h
    simp [panValueFlatLoadListFuel] at h
    subst h
    simp [panValueIsWfValues]
  · intro structs head tail x values h
    simp [panValueFlatLoadListFuel] at h
  · intro structs fuel shape shapes address ihHead ihTail values h
    cases hvalue : panValueFlatLoadFuel structs readWord bytesInWord fuel shape address with
    | none => simp [panValueFlatLoadListFuel, hvalue] at h
    | some value =>
        cases hvalues : panValueFlatLoadListFuel structs readWord bytesInWord fuel shapes
            (panValueFlatOffset bytesInWord address (shapeSizeWithContext structs shape)) with
        | none => simp [panValueFlatLoadListFuel, hvalue, hvalues] at h
        | some rest =>
            simp [panValueFlatLoadListFuel, hvalue, hvalues] at h
            subst h
            simp only [panValueIsWfValues, Bool.and_eq_true]
            exact ⟨ihHead value hvalue, ihTail rest hvalues⟩

/-- Counterpart of Cake's `mem_load_is_wf_shape_v`
    (`cakeml/pancake/semantics/panPropsScript.sml:90`): the flat memory load
    only ever returns well-formed values. -/
theorem panValueFlatLoad_wf [BEq α] [Add α] (structs : StructContext)
    (memory : α → Option (PanValue α)) (bytesInWord : α) (address : α)
    (shape : Shape) (memoryAccess : Option (PanValueMemoryAccess α))
    (value : PanValue α)
    (h : panValueFlatLoad structs memory bytesInWord address shape memoryAccess =
      some value) :
    panValueIsWf structs value = true := by
  rw [panValueFlatLoad] at h
  by_cases hwf : isWfShape structs shape = true
  · rw [if_pos hwf] at h
    exact panValueFlatLoadFuel_wf structs
      (panValueFlatReadWord memory bytesInWord memoryAccess) bytesInWord _ shape address value h
  · rw [if_neg hwf] at h
    simp at h

theorem panValueFlatLoadFuel_shape [BEq α] [Add α]
    (structs : StructContext) (readWord : α → Option α) (bytesInWord : α) :
    ∀ (fuel : Nat) (shape : Shape) (address : α) (value : PanValue α),
      panValueFlatLoadFuel structs readWord bytesInWord fuel shape address = some value →
        panValueShape structs value = shape := by
  apply panValueFlatLoadFuel.induct (α := α) bytesInWord
    (motive1 := fun structs fuel shape address => ∀ value,
      panValueFlatLoadFuel structs readWord bytesInWord fuel shape address = some value →
        panValueShape structs value = shape)
    (motive2 := fun structs fuel fields address => ∀ values,
      panValueFlatLoadFieldsFuel structs readWord bytesInWord fuel fields address = some values →
        (values.map (fun field => panValueShape structs field.2)) = (fields.map Prod.snd))
    (motive3 := fun structs fuel shapes address => ∀ values,
      panValueFlatLoadListFuel structs readWord bytesInWord fuel shapes address = some values →
        (values.map (panValueShape structs)) = shapes)
  · intro structs x x_1 value h
    simp [panValueFlatLoadFuel] at h
  · intro structs fuel address value h
    obtain ⟨word, -, rfl⟩ := by simpa [panValueFlatLoadFuel] using h
    simp [panValueShape]
  · intro structs fuel shapes address ih value h
    obtain ⟨values, hvalues, rfl⟩ := by simpa [panValueFlatLoadFuel] using h
    have hvalues' := ih values hvalues
    simpa [panValueShape] using congrArg Shape.comb hvalues'
  · intro structs fuel name address ih value h
    cases hlookup : lookupInfoWithRest name structs with
    | none => simp [panValueFlatLoadFuel, hlookup] at h
    | some pair =>
        obtain ⟨info, rest⟩ := pair
        cases hfields : panValueFlatLoadFieldsFuel rest readWord bytesInWord fuel
            info.fields address with
        | none => simp [panValueFlatLoadFuel, hlookup, hfields] at h
        | some fields =>
            simp [panValueFlatLoadFuel, hlookup, hfields] at h
            subst h
            simp [panValueShape]
  · intro structs x x_1 values h
    simp [panValueFlatLoadFieldsFuel] at h
    subst h
    simp
  · intro structs head tail x values h
    simp [panValueFlatLoadFieldsFuel] at h
  · intro structs fuel field shape fields address ihHead ihTail values h
    cases hvalue : panValueFlatLoadFuel structs readWord bytesInWord fuel shape address with
    | none => simp [panValueFlatLoadFieldsFuel, hvalue] at h
    | some value =>
        cases hvalues : panValueFlatLoadFieldsFuel structs readWord bytesInWord fuel fields
            (panValueFlatOffset bytesInWord address (shapeSizeWithContext structs shape)) with
        | none => simp [panValueFlatLoadFieldsFuel, hvalue, hvalues] at h
        | some rest =>
            simp [panValueFlatLoadFieldsFuel, hvalue, hvalues] at h
            subst h
            simp only [List.map_cons, ihHead value hvalue, ihTail rest hvalues]
  · intro structs x x_1 values h
    simp [panValueFlatLoadListFuel] at h
    subst h
    simp
  · intro structs head tail x values h
    simp [panValueFlatLoadListFuel] at h
  · intro structs fuel shape shapes address ihHead ihTail values h
    cases hvalue : panValueFlatLoadFuel structs readWord bytesInWord fuel shape address with
    | none => simp [panValueFlatLoadListFuel, hvalue] at h
    | some value =>
        cases hvalues : panValueFlatLoadListFuel structs readWord bytesInWord fuel shapes
            (panValueFlatOffset bytesInWord address (shapeSizeWithContext structs shape)) with
        | none => simp [panValueFlatLoadListFuel, hvalue, hvalues] at h
        | some rest =>
            simp [panValueFlatLoadListFuel, hvalue, hvalues] at h
            subst h
            simp only [List.map_cons, ihHead value hvalue, ihTail rest hvalues]

/-- Counterpart of Cake's `mem_load_some_shape_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:212`): a successful flat load
    returns a value whose shape is exactly the requested shape. -/
theorem panValueFlatLoad_shape [BEq α] [Add α] (structs : StructContext)
    (memory : α → Option (PanValue α)) (bytesInWord : α) (address : α)
    (shape : Shape) (memoryAccess : Option (PanValueMemoryAccess α))
    (value : PanValue α)
    (h : panValueFlatLoad structs memory bytesInWord address shape memoryAccess =
      some value) :
    panValueShape structs value = shape := by
  rw [panValueFlatLoad] at h
  by_cases hwf : isWfShape structs shape = true
  · rw [if_pos hwf] at h
    exact panValueFlatLoadFuel_shape structs
      (panValueFlatReadWord memory bytesInWord memoryAccess) bytesInWord _ shape address value h
  · rw [if_neg hwf] at h
    simp at h

/-- List conjunct of Cake's `mem_loads_some_shape_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:194`). -/
theorem panValueFlatLoadListFuel_shape [BEq α] [Add α]
    (structs : StructContext) (readWord : α → Option α) (bytesInWord : α)
    (fuel : Nat) :
    ∀ (shapes : List Shape) (address : α) (values : List (PanValue α)),
      panValueFlatLoadListFuel structs readWord bytesInWord fuel shapes address = some values →
        values.map (panValueShape structs) = shapes := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      intro shapes address values h
      cases shapes with
      | nil => simp [panValueFlatLoadListFuel] at h; subst h; simp
      | cons shape shapes =>
          cases fuel with
          | zero => simp [panValueFlatLoadListFuel] at h
          | succ fuel' =>
              cases hvalue : panValueFlatLoadFuel structs readWord bytesInWord fuel' shape address with
              | none => simp [panValueFlatLoadListFuel, hvalue] at h
              | some value =>
                  cases hvalues : panValueFlatLoadListFuel structs readWord bytesInWord fuel' shapes
                      (panValueFlatOffset bytesInWord address
                        (shapeSizeWithContext structs shape)) with
                  | none => simp [panValueFlatLoadListFuel, hvalue, hvalues] at h
                  | some rest =>
                      simp [panValueFlatLoadListFuel, hvalue, hvalues] at h
                      subst h
                      have hhead : panValueShape structs value = shape :=
                        panValueFlatLoadFuel_shape structs readWord bytesInWord fuel'
                          shape address value hvalue
                      have htail := ih fuel' (by omega) shapes
                        (panValueFlatOffset bytesInWord address
                          (shapeSizeWithContext structs shape)) rest hvalues
                      rw [List.map_cons, hhead, htail]

/-- Fields conjunct of Cake's `mem_loads_some_shape_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:194`). -/
theorem panValueFlatLoadFieldsFuel_shape [BEq α] [Add α]
    (structs : StructContext) (readWord : α → Option α) (bytesInWord : α)
    (fuel : Nat) :
    ∀ (fields : List (FieldName × Shape)) (address : α)
      (values : List (FieldName × PanValue α)),
      panValueFlatLoadFieldsFuel structs readWord bytesInWord fuel fields address = some values →
        values.map (fun field => panValueShape structs field.2) = fields.map Prod.snd := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      intro fields address values h
      cases fields with
      | nil => simp [panValueFlatLoadFieldsFuel] at h; subst h; simp
      | cons field fields =>
          obtain ⟨fieldName, shape⟩ := field
          cases fuel with
          | zero => simp [panValueFlatLoadFieldsFuel] at h
          | succ fuel' =>
              cases hvalue : panValueFlatLoadFuel structs readWord bytesInWord fuel' shape address with
              | none => simp [panValueFlatLoadFieldsFuel, hvalue] at h
              | some value =>
                  cases hvalues : panValueFlatLoadFieldsFuel structs readWord bytesInWord fuel' fields
                      (panValueFlatOffset bytesInWord address
                        (shapeSizeWithContext structs shape)) with
                  | none => simp [panValueFlatLoadFieldsFuel, hvalue, hvalues] at h
                  | some rest =>
                      simp [panValueFlatLoadFieldsFuel, hvalue, hvalues] at h
                      subst h
                      have hhead : panValueShape structs value = shape :=
                        panValueFlatLoadFuel_shape structs readWord bytesInWord fuel'
                          shape address value hvalue
                      have htail := ih fuel' (by omega) fields
                        (panValueFlatOffset bytesInWord address
                          (shapeSizeWithContext structs shape)) rest hvalues
                      rw [List.map_cons, List.map_cons, hhead, htail]

/-- List conjunct of Cake's `mem_loads_some_shape_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:194`). -/
theorem panValueFlatLoadList_shape [BEq α] [Add α] (structs : StructContext)
    (memory : α → Option (PanValue α)) (bytesInWord : α) (address : α)
    (shapes : List Shape) (memoryAccess : Option (PanValueMemoryAccess α))
    (values : List (PanValue α))
    (h : panValueFlatLoadList structs memory bytesInWord address shapes memoryAccess =
      some values) :
    values.map (panValueShape structs) = shapes := by
  rw [panValueFlatLoadList] at h
  by_cases hwf : shapes.all (isWfShape structs) = true
  · rw [if_pos hwf] at h
    exact panValueFlatLoadListFuel_shape structs
      (panValueFlatReadWord memory bytesInWord memoryAccess) bytesInWord _ shapes address values h
  · rw [if_neg hwf] at h
    simp at h

/-- Fields conjunct of Cake's `mem_loads_some_shape_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:194`). -/
theorem panValueFlatLoadFields_shape [BEq α] [Add α] (structs : StructContext)
    (memory : α → Option (PanValue α)) (bytesInWord : α) (address : α)
    (fields : List (FieldName × Shape)) (memoryAccess : Option (PanValueMemoryAccess α))
    (values : List (FieldName × PanValue α))
    (h : panValueFlatLoadFields structs memory bytesInWord address fields memoryAccess =
      some values) :
    values.map (fun field => panValueShape structs field.2) = fields.map Prod.snd := by
  rw [panValueFlatLoadFields] at h
  by_cases hwf : fields.all (fun field => isWfShape structs field.2) = true
  · rw [if_pos hwf] at h
    exact panValueFlatLoadFieldsFuel_shape structs
      (panValueFlatReadWord memory bytesInWord memoryAccess) bytesInWord _ fields address values h
  · rw [if_neg hwf] at h
    simp at h

/-- Flapjack's executable rendering of HOL structural equality on `Shape`
    (`panSem$shape_of` results are compared with `=` in `evaluate_decls_def`).
    It is a `Bool` function that recurses structurally and compares `Named`
    tags with String `==`, so it agrees with HOL `=` only at lawful String
    equality instances; it is therefore untagged (see bead
    `flapjack-pxn.18.3.6.4`).  `evaluateDecls` uses it together with
    `panValueShape`, which is proved equal to the tagged exact `panSemShapeOf`
    (`panValueShape_eq_panSemShapeOf_tagged`). -/
def panShapeMatches : Shape → Shape → Bool
  | .one, .one => true
  | .named left, .named right => left == right
  | .comb left, .comb right => panShapeListMatches left right
  | _, _ => false
termination_by left right => sizeOf left + sizeOf right
where
  panShapeListMatches : List Shape → List Shape → Bool
    | [], [] => true
    | left :: leftRest, right :: rightRest =>
        panShapeMatches left right && panShapeListMatches leftRest rightRest
    | _, _ => false
    termination_by left right => sizeOf left + sizeOf right
    decreasing_by
      all_goals first | decreasing_trivial

mutual
  theorem panShapeMatches_comm : (left right : Shape) →
      panShapeMatches left right = panShapeMatches right left
    | .one, .one => by simp only [panShapeMatches]
    | .named left, .named right => by
        simp only [panShapeMatches]
        by_cases h : left = right
        · rw [beq_iff_eq.mpr h, beq_iff_eq.mpr h.symm]
        · rw [beq_eq_false_iff_ne.mpr h,
              beq_eq_false_iff_ne.mpr (fun hh => h hh.symm)]
    | .comb left, .comb right => by
        simp only [panShapeMatches]
        exact panShapeListMatches_comm left right
    | .one, .named _ => by simp only [panShapeMatches]
    | .one, .comb _ => by simp only [panShapeMatches]
    | .named _, .one => by simp only [panShapeMatches]
    | .named _, .comb _ => by simp only [panShapeMatches]
    | .comb _, .one => by simp only [panShapeMatches]
    | .comb _, .named _ => by simp only [panShapeMatches]

  theorem panShapeListMatches_comm : (left right : List Shape) →
      panShapeMatches.panShapeListMatches left right =
        panShapeMatches.panShapeListMatches right left
    | [], [] => by simp only [panShapeMatches.panShapeListMatches]
    | left :: leftRest, right :: rightRest => by
        simp only [panShapeMatches.panShapeListMatches]
        rw [panShapeMatches_comm left right,
          panShapeListMatches_comm leftRest rightRest]
    | [], _ :: _ => by simp only [panShapeMatches.panShapeListMatches]
    | _ :: _, [] => by simp only [panShapeMatches.panShapeListMatches]
end

/-! Truth of the executable `panShapeMatches` is exactly HOL structural equality
    on `Shape`, provided the key type has a lawful `BEq`.  This is the bridge used
    to justify rendering HOL's `s = shape_of v` by `panShapeMatches s (shape_of v)`
    in the exact `panSem$eval_def` port. -/
mutual
  theorem panShapeMatches_eq_true [LawfulBEq String] : (left right : Shape) →
      (panShapeMatches left right = true ↔ left = right)
    | .one, .one => by simp only [panShapeMatches]
    | .named left, .named right => by
        simp only [panShapeMatches, Shape.named.injEq]
        exact ⟨fun h => beq_iff_eq.mp h, fun h => beq_iff_eq.mpr h⟩
    | .comb left, .comb right => by
        simp only [panShapeMatches, Shape.comb.injEq]
        exact panShapeListMatches_eq_true left right
    | .one, .named _ => by simp [panShapeMatches]
    | .one, .comb _ => by simp [panShapeMatches]
    | .named _, .one => by simp [panShapeMatches]
    | .named _, .comb _ => by simp [panShapeMatches]
    | .comb _, .one => by simp [panShapeMatches]
    | .comb _, .named _ => by simp [panShapeMatches]

  theorem panShapeListMatches_eq_true [LawfulBEq String] : (left right : List Shape) →
      (panShapeMatches.panShapeListMatches left right = true ↔ left = right)
    | [], [] => by simp only [panShapeMatches.panShapeListMatches]
    | left :: leftRest, right :: rightRest => by
        simp only [panShapeMatches.panShapeListMatches, Bool.and_eq_true]
        rw [panShapeMatches_eq_true left right,
          panShapeListMatches_eq_true leftRest rightRest]
        exact ⟨fun h => (List.cons.injEq ..).mpr h, fun h => (List.cons.injEq ..).mp h⟩
    | [], _ :: _ => by simp [panShapeMatches.panShapeListMatches]
    | _ :: _, [] => by simp [panShapeMatches.panShapeListMatches]
end

/-! Declaration-level contracts used by the call-aware evaluators.  The
    optional wrapper keeps the original hand-built evaluator API useful for
    small compatibility fixtures while allowing declaration-driven execution
    to enforce the same return and exception shape checks as `panSem`. -/
structure PanValueCallContracts where
  returnShapes : InfoMap Shape
  exceptionShapes : InfoMap Shape
  parameterShapes : InfoMap (List (VarName × Shape)) := []

def panValuePayloadSizeFuel : Nat → StructContext → PanValue α → Nat
  | 0, _, _ => 0
  | _fuel + 1, _, .word _ => 1
  | fuel + 1, context, .rStruct fields =>
      panValuePayloadSizeFieldsFuel fuel context fields
  | _fuel + 1, context, .nStruct name _ =>
      (lookupInfo name context).map StructInfo.size |>.getD 1
where
  panValuePayloadSizeFieldsFuel : Nat → StructContext → List (PanValue α) → Nat
    | _, _, [] => 0
    | 0, _, _ :: _ => 0
    | fuel + 1, context, value :: values =>
        panValuePayloadSizeFuel fuel context value +
          panValuePayloadSizeFieldsFuel fuel context values

/-- CakeML limits returned and raised structured values to 32 words. -/
def panValuePayloadWithinLimit (structs : StructContext)
    (value : PanValue α) : Bool :=
  Nat.ble (panValuePayloadSizeFuel (panValueFlatValueFuel value + 1) structs value) 32

def panValueValuesWithinLimit (structs : StructContext) :
    List (PanValue α) → Bool
  | [] => true
  | value :: values =>
      panValuePayloadWithinLimit structs value &&
        panValueValuesWithinLimit structs values

@[simp] theorem panValuePayloadWithinLimit_word (structs : StructContext)
    (value : α) :
    panValuePayloadWithinLimit structs (.word value) = true := by
  simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel]

@[simp] theorem panValueValuesWithinLimit_word_singleton (structs : StructContext)
    (value : α) :
    panValueValuesWithinLimit structs [.word value] = true := by
  simp [panValueValuesWithinLimit]

@[simp] theorem panValuePayloadWithinLimit_rStruct_two_words
    (structs : StructContext) (left right : α) :
    panValuePayloadWithinLimit structs (.rStruct [.word left, .word right]) = true := by
  simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
    panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel,
    panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel]

def panValueReturnValid (structs : StructContext)
    (contracts : Option PanValueCallContracts) (function : FunName)
    (values : List (PanValue α)) : Bool :=
  match contracts with
  | none => true
  | some contracts =>
      match lookupInfo function contracts.returnShapes, values with
      | some shape, [value] => panShapeMatches (panValueShape structs value) shape
      | _, _ => false

def panValueExceptionValid (structs : StructContext)
    (contracts : Option PanValueCallContracts) (exception : ExceptionId)
    (value : PanValue α) : Bool :=
  match contracts with
  | none => true
  | some contracts =>
      match lookupInfo exception contracts.exceptionShapes with
      | some shape => panShapeMatches (panValueShape structs value) shape
      | none => false

def panValueValuesMatchShapes (structs : StructContext) :
    List Shape → List (PanValue α) → Bool
  | [], [] => true
  | shape :: shapes, value :: values =>
      panShapeMatches (panValueShape structs value) shape &&
        panValueValuesMatchShapes structs shapes values
  | _, _ => false

/-! `lookup_code` in CakeML validates both parameter distinctness and the shape
    of every argument.  Hand-built evaluators may omit this optional contract,
    but declaration-driven public evaluation supplies it. -/
def panValueParametersValid (structs : StructContext)
    (contracts : Option PanValueCallContracts) (function : FunName)
    (values : List (PanValue α)) : Bool :=
  match contracts with
  | none => true
  | some contracts =>
      match lookupInfo function contracts.parameterShapes with
      | none => true
      | some parameters =>
          decide (parameters.map (fun parameter => parameter.1)).Nodup &&
            panValueValuesMatchShapes structs
              (parameters.map (fun parameter => parameter.2)) values

@[simp] theorem panValueParametersValid_none (structs : StructContext)
    (function : FunName) (values : List (PanValue α)) :
    panValueParametersValid structs none function values = true := by
  rfl

@[simp] theorem panValueReturnValid_none (structs : StructContext)
    (function : FunName) (values : List (PanValue α)) :
    panValueReturnValid structs none function values = true := by
  rfl

@[simp] theorem panValueExceptionValid_none (structs : StructContext)
    (exception : ExceptionId) (value : PanValue α) :
    panValueExceptionValid structs none exception value = true := by
  rfl

/-! CakeML assignments are shape-preserving updates to an already-bound
    local or global variable.  In particular, an absent destination is not
    an implicit declaration: is_valid_value rejects it. -/
def panValueAssignmentValid (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (kind : VarKind) (name : VarName) (value : PanValue α) : Bool :=
  match kind with
  | .local =>
      match locals name with
      | some oldValue =>
          panShapeMatches (panValueShape structs value)
            (panValueShape structs oldValue)
      | none => false
  | .global =>
      match globals name with
      | some oldValue =>
          panShapeMatches (panValueShape structs value)
            (panValueShape structs oldValue)
      | none => false

/-! CakeML's shared-memory load is a word assignment, rather than a general
    declaration or structured assignment.  The destination must therefore be
    an existing word, and the memory operation must produce a word. -/
def panValueSharedLoadValid (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (kind : VarKind) (name : VarName) (value : PanValue α) : Bool :=
  match value with
  | .word _ => panValueAssignmentValid structs locals globals kind name value
  | _ => false

def panValueHandlerValid (structs : StructContext)
    (contracts : Option PanValueCallContracts)
    (locals : VarName → Option (PanValue α)) (handlerVariable : VarName)
    (value : PanValue α) : Bool :=
  match contracts with
  | none => true
  | some _ => panValueAssignmentValid structs locals (fun _ => none)
      .local handlerVariable value

@[simp] theorem panValueHandlerValid_none (structs : StructContext)
    (locals : VarName → Option (PanValue α)) (handlerVariable : VarName)
    (value : PanValue α) :
    panValueHandlerValid structs none locals handlerVariable value = true := by
  rfl

def panValueFieldsHaveShapes (context : StructContext) :
    List (FieldName × Shape) → List (FieldName × PanValue α) → Bool
  | [], [] => true
  | (expectedName, expectedShape) :: expected,
      (actualName, actualValue) :: actual =>
      expectedName == actualName &&
        panShapeMatches (panValueShape context actualValue) expectedShape &&
        panValueFieldsHaveShapes context expected actual
  | _, _ => false

/-- Literal HOL-shaped rendering of the `NStruct` field check in
    `cakeml/pancake/semantics/panSemScript.sml:209 eval_def`: the context
    field-name list must equal the value field-name list in order
    (`MAP FST info.fields = MAP FST fields`) and every context field shape must
    match the shape of the corresponding value
    (`EVERY (λ(s,v). s = shape_of v)
       (ZIP (MAP SND info.fields, field_vals))`, computing the value shape
    inside the predicate as HOL's `λ` does).
    `panValueShape` is the context-free twin of HOL `shape_of`
    (`Flapjack.Pancake.Semantics.panSemShapeOf`, the tagged exact port) and
    `panShapeMatches` is the Bool rendering of structural `=` on `Shape`; the
    comparison keeps the context shape on the left, as HOL's `λs v. s = shape_of v`
    does. -/
def panValueFieldsExactHOL (context : StructContext)
    (expected : List (FieldName × Shape))
    (actual : List (FieldName × PanValue α)) : Bool :=
  (expected.map Prod.fst == actual.map Prod.fst) &&
    List.all
      ((expected.map Prod.snd).zip (actual.map Prod.snd))
      (fun pair => panShapeMatches pair.1 (panValueShape context pair.2))

/-- The literal HOL-shaped `NStruct` field check agrees with the production
    helper on every input (`Bool.and` is commutative and associative). -/
theorem panValueFieldsExactHOL_eq_haveShapes (context : StructContext)
    (expected : List (FieldName × Shape))
    (actual : List (FieldName × PanValue α)) :
    panValueFieldsExactHOL context expected actual =
      panValueFieldsHaveShapes context expected actual := by
  induction expected generalizing actual with
  | nil =>
      cases actual with
      | nil => rfl
      | cons actualHead actualTail => rfl
  | cons head tail ih =>
      obtain ⟨expectedName, expectedShape⟩ := head
      cases actual with
      | nil => rfl
      | cons actualHead actualTail =>
          obtain ⟨actualName, actualValue⟩ := actualHead
          simp only [panValueFieldsHaveShapes, panValueFieldsExactHOL, List.map_cons,
            List.zip_cons_cons, List.all_cons, List.cons_beq_cons]
          rw [panShapeMatches_comm expectedShape (panValueShape context actualValue)]
          have htail :
              (List.map Prod.fst tail == List.map Prod.fst actualTail &&
                  ((List.map Prod.snd tail).zip (List.map Prod.snd actualTail)).all
                    fun pair => panShapeMatches pair.fst (panValueShape context pair.snd)) =
                panValueFieldsHaveShapes context tail actualTail := ih actualTail
          rw [← htail]
          simp only [Bool.and_assoc, Bool.and_left_comm]

def lookupPanValueField (name : FieldName) :
    List (FieldName × PanValue α) → Option (PanValue α)
  | [] => none
  | (candidate, value) :: fields =>
      if candidate == name then some value else lookupPanValueField name fields

def panValueWordProjection : PanValue α → Option α
  | .word value => some value
  | _ => none

@[simp] theorem panValueWordProjection_word (value : α) :
    panValueWordProjection (.word value) = some value := rfl

@[simp] theorem panValueWordProjection_rStruct (fields : List (PanValue α)) :
    panValueWordProjection (.rStruct fields) = none := rfl

@[simp] theorem panValueWordProjection_nStruct (name : StructName)
    (fields : List (FieldName × PanValue α)) :
    panValueWordProjection (.nStruct name fields) = none := rfl

/-- Executable Pancake source-expression evaluator.

This is the source-shaped recursion used by the production semantics, but it is
NOT a statement-exact port of HOL `panSemScript.sml:209 eval_def`
(resp. the identical `pan_itreeSemScript.sml:79`).  Cluster-by-cluster:

* `Const`, `Var Local`, `Var Global`, `RStruct`, `RField`, `BaseAddr`,
  `TopAddr`, `BytesInWord` follow the HOL clauses; the bounded index lookup
  `fields[index]?` matches HOL's `if index < LENGTH vs then EL index vs` and
  the HOL rows in `scripts/hol-probes/pan_eval_probe.out` are checked in
  `Flapjack/Test/PanEvalParity.lean`.
* `NStruct` / `NField` use the production `lookupInfo` first-match.  The
  `NStruct` field check is the literal HOL form (`panValueFieldsExactHOL`:
  `MAP FST info.fields = MAP FST fields` and `EVERY (λ(s,v). s = shape_of v)
  (ZIP (MAP SND info.fields, values))`, with the value shape computed inside the
  predicate as in HOL), proved equal to the
  legacy pairwise helper `panValueFieldsHaveShapes`; HOL's `ALOOKUP` with HOL
  `=` is still rendered by `lookupInfo` at the concrete `String` instance.
* `Load` / `Load32` / `LoadByte` / `Op` do not read memory through the HOL
  state's `memaddrs`, endianness, and byte width; the default (`memoryAccess =
  none`) reads `memory` directly, and the `.load` case uses `panValueFlatLoad`.
  This is the gap also recorded in `Flapjack/Pancake/Semantics/PanSem/Total.lean`.
* The Lean signature takes `structs locals globals memory baseAddress
  topAddress bytesInWord` (a projection of the HOL state) and an extra
  `memoryAccess` parameter, and `PanValue` stores the raw word in `.word` rather
  than HOL's `Val (Word w)`.

The faithful HOL-shaped expression evaluator, including the state projection and
the memory-codec clauses, is tracked by bead `flapjack-pxn.18.3.6.9`. -/
def evalPanValueExp [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) :
    (expression : Exp α) →
      (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        Option (PanValue α)
  | .const value, _ => some (.word value)
  | .var .local name, _ => locals name
  | .var .global name, _ => globals name
  | .rStruct fields, memoryAccess =>
      (evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord fields (memoryAccess := memoryAccess)).map .rStruct
  | .rField index expression, memoryAccess => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord expression (memoryAccess := memoryAccess)
      match value with
      | .rStruct fields => fields[index]?
      | _ => none
  | .nStruct name fields, memoryAccess => do
      let info ← lookupInfo name structs
      let values ← evalPanValueFields structs locals globals memory
        baseAddress topAddress bytesInWord fields (memoryAccess := memoryAccess)
      if panValueFieldsExactHOL structs info.fields values then
        pure (.nStruct name values)
      else none
  | .nField name expression, memoryAccess => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord expression (memoryAccess := memoryAccess)
      match value with
      | .nStruct structName fields =>
          if (lookupInfo structName structs).isSome then
            lookupPanValueField name fields
          else none
      | _ => none
  | .load shape address, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let .word address := address | none
      panValueFlatLoad structs memory bytesInWord address shape memoryAccess
  | .load32 address, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let .word address := address | none
      match memoryAccess with
      | none => do
          let value ← memory address
          match value with
          | .word value => some (.word value)
          | _ => none
      | some access => (access.read32 access.domain memory bytesInWord address).map .word
  | .loadByte address, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let .word address := address | none
      match memoryAccess with
      | none => do
          let value ← memory address
          match value with
          | .word value => some (.word value)
          | _ => none
      | some access => (access.readByte access.domain memory bytesInWord address).map .word
  | .op operator arguments, memoryAccess => do
      let values ← evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
      let values ← values.mapM panValueWordProjection
      match memoryAccess with
      | none => match values with
          | [left, right] => some (.word (evalPanBinOp operator left right))
          | _ => none
      | some access => (access.wordOp operator values).map .word
  | .panOp operator arguments, memoryAccess => do
      let values ← evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
      match values with
      | [.word left, .word right] => (evalPanOp operator [left, right]).map .word
      | _ => none
  | .cmp operator left right, memoryAccess => do
      let left ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord left (memoryAccess := memoryAccess)
      let right ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord right (memoryAccess := memoryAccess)
      match left, right with
      | .word left, .word right =>
          match memoryAccess with
          | none => some (.word (evalPanCmp operator left right))
          | some access => some (.word (access.compare operator left right))
      | _, _ => none
  | .shift operator left right, memoryAccess => do
      let left ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord left (memoryAccess := memoryAccess)
      let right ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord right (memoryAccess := memoryAccess)
      match left, right with
      | .word left, .word right =>
          match memoryAccess with
          | none => (evalPanShift operator left right).map .word
          | some access => (access.shift operator left right).map .word
      | _, _ => none
  | .baseAddr, _ => some (.word baseAddress)
  | .topAddr, _ => some (.word topAddress)
  | .bytesInWord, _ => some (.word bytesInWord)
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  evalPanValueExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) :
      (expressions : List (Exp α)) →
      (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        Option (List (PanValue α))
    | [], _ => some []
    | expression :: expressions, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord expression (memoryAccess := memoryAccess)
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord expressions (memoryAccess := memoryAccess)
        pure (value :: values)
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  evalPanValueFields [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) :
      (fields : List (FieldName × Exp α)) →
      (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        Option (List (FieldName × PanValue α))
    | [], _ => some []
    | (name, expression) :: fields, memoryAccess => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord expression (memoryAccess := memoryAccess)
        let values ← evalPanValueFields structs locals globals memory
          baseAddress topAddress bytesInWord fields (memoryAccess := memoryAccess)
        pure ((name, value) :: values)
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def evalPanValueExps [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (expressions : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
      Option (List (PanValue α)) :=
  evalPanValueExp.evalPanValueExps structs locals globals memory
    baseAddress topAddress bytesInWord expressions memoryAccess

theorem evalPanValueFields_projection [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (fields : List (FieldName × Exp α)) (values : List (FieldName × PanValue α))
    (heval : evalPanValueExp.evalPanValueFields structs locals globals memory
      baseAddress topAddress bytesInWord fields = some values) :
    fields.map Prod.fst = values.map Prod.fst ∧
      evalPanValueExps structs locals globals memory baseAddress topAddress
        bytesInWord (fields.map Prod.snd) = some (values.map Prod.snd) := by
  induction fields generalizing values with
  | nil =>
      simp [evalPanValueExp.evalPanValueFields] at heval
      subst values
      constructor
      · rfl
      · change evalPanValueExp.evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord [] none = some []
        simp [evalPanValueExp.evalPanValueExps]
  | cons field fields ih =>
      rcases field with ⟨name, expression⟩
      cases hhead : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord expression with
      | none => simp [evalPanValueExp.evalPanValueFields, hhead] at heval
      | some head =>
          cases htail : evalPanValueExp.evalPanValueFields structs locals globals
              memory baseAddress topAddress bytesInWord fields with
          | none =>
              simp [evalPanValueExp.evalPanValueFields, hhead, htail] at heval
          | some tail =>
              have hvalues : values = (name, head) :: tail := by
                simpa [evalPanValueExp.evalPanValueFields, hhead, htail] using heval.symm
              subst values
              have htailProjection := ih tail htail
              constructor
              · simp [htailProjection.1]
              · change evalPanValueExp.evalPanValueExps structs locals globals memory
                  baseAddress topAddress bytesInWord
                  (expression :: fields.map Prod.snd) none =
                    some (head :: tail.map Prod.snd)
                have htailEval : evalPanValueExp.evalPanValueExps structs locals
                    globals memory baseAddress topAddress bytesInWord
                    (fields.map Prod.snd) none = some (tail.map Prod.snd) := by
                  simpa only [evalPanValueExps] using htailProjection.2
                simp [evalPanValueExp.evalPanValueExps, hhead, htailEval]


theorem shapeVal_shape [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (baseAddress topAddress bytesInWord : α)
    (memoryAccess : Option (PanValueMemoryAccess α)) (shape : Shape)
    (hwf : isWfShape ([] : StructContext) shape = true) (value : PanValue α)
    (heval : evalPanValueExp structs locals globals memory baseAddress topAddress
      bytesInWord (shapeVal shape) memoryAccess = some value) :
    panValueShape structs value = shape := by
  have hmain : ∀ shape, isWfShape ([] : StructContext) shape = true →
      ∀ value, evalPanValueExp structs locals globals memory baseAddress
        topAddress bytesInWord (shapeVal shape) memoryAccess = some value →
        panValueShape structs value = shape := by
    apply shapeVal.induct
      (motive1 := fun shape => isWfShape ([] : StructContext) shape = true →
        ∀ value, evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord (shapeVal shape) memoryAccess = some value →
          panValueShape structs value = shape)
      (motive2 := fun shapes =>
        isWfShape.isWfShapeList ([] : StructContext) shapes = true →
        ∀ values, evalPanValueExp.evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord (shapeVals shapes) memoryAccess =
          some values → values.map (panValueShape structs) = shapes)
    · intro _ value h
      simp only [shapeVal, evalPanValueExp, Option.some.injEq] at h
      subst h
      simp [panValueShape]
    · intro shapes ih hwf value h
      simp only [shapeVal] at h
      have hwfList : isWfShape.isWfShapeList ([] : StructContext) shapes = true := by
        rw [isWfShape.eq_def] at hwf
        exact hwf
      cases hvalues : evalPanValueExp.evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord (shapeVals shapes) memoryAccess with
      | none => simp [evalPanValueExp, hvalues] at h
      | some values =>
          simp [evalPanValueExp, hvalues] at h
          subst h
          rw [panValueShape]
          rw [ih hwfList values hvalues]
    · intro name hwf value h
      simp [isWfShape, lookupInfo] at hwf
    · intro _ values h
      simp only [shapeVals, evalPanValueExp.evalPanValueExps, Option.some.injEq] at h
      subst h
      simp
    · intro shape shapes ihHead ihTail hwf values h
      rw [isWfShape.isWfShapeList.eq_def] at hwf
      rw [Bool.and_eq_true] at hwf
      obtain ⟨hwfHead, hwfTail⟩ := hwf
      simp only [shapeVals, evalPanValueExp.evalPanValueExps] at h
      cases hvalue : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord (shapeVal shape) memoryAccess with
      | none => simp [hvalue] at h
      | some head =>
          cases hvalues : evalPanValueExp.evalPanValueExps structs locals globals
              memory baseAddress topAddress bytesInWord (shapeVals shapes)
              memoryAccess with
          | none => simp [hvalue, hvalues] at h
          | some tail =>
              simp [hvalue, hvalues] at h
              subst h
              rw [List.map_cons, ihHead hwfHead head hvalue, ihTail hwfTail tail hvalues]
  exact hmain shape hwf value heval


theorem shapeVal_isSome [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (baseAddress topAddress bytesInWord : α)
    (memoryAccess : Option (PanValueMemoryAccess α)) (shape : Shape) :
    (evalPanValueExp structs locals globals memory baseAddress topAddress
      bytesInWord (shapeVal shape) memoryAccess).isSome = true := by
  have hmain : ∀ shape, (evalPanValueExp structs locals globals memory baseAddress
        topAddress bytesInWord (shapeVal shape) memoryAccess).isSome = true := by
    apply shapeVal.induct
      (motive1 := fun shape => (evalPanValueExp structs locals globals memory baseAddress
        topAddress bytesInWord (shapeVal shape) memoryAccess).isSome = true)
      (motive2 := fun shapes => (evalPanValueExp.evalPanValueExps structs locals globals
        memory baseAddress topAddress bytesInWord (shapeVals shapes) memoryAccess).isSome = true)
    · simp [shapeVal, evalPanValueExp]
    · intro shapes ih
      simp only [shapeVal]
      cases hvalues : evalPanValueExp.evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord (shapeVals shapes) memoryAccess with
      | none => rw [hvalues] at ih; exact absurd ih (by simp)
      | some values => simp [evalPanValueExp, hvalues]
    · intro name
      simp [shapeVal, evalPanValueExp]
    · simp [shapeVals, evalPanValueExp.evalPanValueExps]
    · intro shape shapes ihHead ihTail
      simp only [shapeVals, evalPanValueExp.evalPanValueExps]
      cases hvalue : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord (shapeVal shape) memoryAccess with
      | none => rw [hvalue] at ihHead; exact absurd ihHead (by simp)
      | some head =>
          cases hvalues : evalPanValueExp.evalPanValueExps structs locals globals
              memory baseAddress topAddress bytesInWord (shapeVals shapes) memoryAccess with
          | none => rw [hvalues] at ihTail; exact absurd ihTail (by simp)
          | some tail => simp
  exact hmain shape

theorem panValueIsWf_word (structs : StructContext) (value : α) :
    panValueIsWf structs (.word value) = true := by
  simp [panValueIsWf]

/-- Counterpart of Cake's `evaluate_replicate_const`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:3051`): evaluating a
    list of zero constants always succeeds, producing the same number of zero
    words.  This is the `OPT_MMAP (eval s) (REPLICATE n (Const 0w))` shape used
    when flattening zero-initialised aggregate values. -/
theorem evalPanValueExps_replicate_const [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (baseAddress topAddress bytesInWord : α)
    (count : Nat) :
    (List.replicate count (.const (0 : α))).mapM
        (fun expression => evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord expression) =
      some (List.replicate count (.word (0 : α))) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.mapM_cons]
      simp [evalPanValueExp, ih, List.replicate_succ]

theorem panValueIsWfValues_getElem? {context : StructContext} {values : List (PanValue α)}
    {index : Nat} {value : PanValue α}
    (hwf : panValueIsWfValues context values = true)
    (hget : values[index]? = some value) :
    panValueIsWf context value = true := by
  induction values generalizing index with
  | nil => simp at hget
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget
          simp only [panValueIsWfValues, Bool.and_eq_true] at hwf
          exact hwf.1
      | succ index =>
          simp only [List.getElem?_cons_succ] at hget
          simp only [panValueIsWfValues, Bool.and_eq_true] at hwf
          exact ih hwf.2 hget

theorem panValueIsWfFields_lookupPanValueField {context : StructContext}
    {fields : List (FieldName × PanValue α)} {name : FieldName} {value : PanValue α}
    (hwf : panValueIsWfFields context fields = true)
    (hlookup : lookupPanValueField name fields = some value) :
    panValueIsWf context value = true := by
  induction fields with
  | nil => simp [lookupPanValueField] at hlookup
  | cons field fields ih =>
      obtain ⟨candidate, fieldValue⟩ := field
      simp only [lookupPanValueField] at hlookup
      by_cases hname : (candidate == name) = true
      · rw [if_pos hname] at hlookup
        have heq : fieldValue = value := Option.some.inj hlookup
        subst heq
        simp only [panValueIsWfFields, Bool.and_eq_true] at hwf
        exact hwf.1
      · rw [if_neg hname] at hlookup
        simp only [panValueIsWfFields, Bool.and_eq_true] at hwf
        exact ih hwf.2 hlookup

theorem evalPanValueExp_isWfShape [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (hlocals : ∀ name value, locals name = some value → panValueIsWf structs value = true)
    (hglobals : ∀ name value, globals name = some value → panValueIsWf structs value = true)
    (expression : Exp α) (memoryAccess : Option (PanValueMemoryAccess α))
    (value : PanValue α)
    (heval : evalPanValueExp structs locals globals memory baseAddress topAddress
      bytesInWord expression memoryAccess = some value) :
    panValueIsWf structs value = true := by
  have hmain : ∀ (expression : Exp α) (memoryAccess : Option (PanValueMemoryAccess α)),
      (∀ value : PanValue α,
        evalPanValueExp structs locals globals memory baseAddress topAddress
          bytesInWord expression memoryAccess = some value →
          panValueIsWf structs value = true) := by
    apply evalPanValueExp.induct
      (motive1 := fun expressions memoryAccess =>
        ∀ values : List (PanValue α),
          evalPanValueExps structs locals globals memory baseAddress topAddress
            bytesInWord expressions memoryAccess = some values →
            panValueIsWfValues structs values = true)
      (motive2 := fun expression memoryAccess =>
        ∀ value : PanValue α,
          evalPanValueExp structs locals globals memory baseAddress topAddress
            bytesInWord expression memoryAccess = some value →
            panValueIsWf structs value = true)
      (motive3 := fun fields memoryAccess =>
        ∀ values : List (FieldName × PanValue α),
          evalPanValueExp.evalPanValueFields structs locals globals memory
            baseAddress topAddress bytesInWord fields memoryAccess = some values →
            panValueIsWfFields structs values = true)
    · intro memoryAccess values h
      simp only [evalPanValueExps, evalPanValueExp.evalPanValueExps,
        Option.some.injEq] at h
      subst h
      simp [panValueIsWfValues]
    · intro expression expressions memoryAccess ihHead ihTail values h
      simp only [evalPanValueExps, evalPanValueExp.evalPanValueExps] at h
      cases hvalue : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord expression memoryAccess with
      | none => simp [hvalue] at h
      | some head =>
          cases hvalues : evalPanValueExp.evalPanValueExps structs locals
              globals memory baseAddress topAddress bytesInWord expressions
              memoryAccess with
          | none => simp [hvalue, hvalues] at h
          | some tail =>
              simp [hvalue, hvalues] at h
              subst h
              simp only [panValueIsWfValues, Bool.and_eq_true]
              exact ⟨ihHead head hvalue, ihTail tail hvalues⟩
    · intro memoryAccess payload value h
      simp only [evalPanValueExp, Option.some.injEq] at h
      subst h
      exact panValueIsWf_word structs payload
    · intro memoryAccess name value h
      simp only [evalPanValueExp] at h
      exact hlocals name value h
    · intro memoryAccess name value h
      simp only [evalPanValueExp] at h
      exact hglobals name value h
    · intro fields memoryAccess ih values h
      cases hfields : evalPanValueExp.evalPanValueExps structs locals globals
          memory baseAddress topAddress bytesInWord fields memoryAccess with
      | none => simp [evalPanValueExp, hfields] at h
      | some fieldValues =>
          simp [evalPanValueExp, hfields] at h
          subst h
          simpa [panValueIsWf] using ih fieldValues hfields
    · intro index expression memoryAccess ih value h
      cases hexpr : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord expression memoryAccess with
      | none => simp [evalPanValueExp, hexpr] at h
      | some inner =>
          cases inner with
          | word w => simp [evalPanValueExp, hexpr] at h
          | rStruct innerFields =>
              cases hget : innerFields[index]? with
              | none => simp [evalPanValueExp, hexpr, hget] at h
              | some fieldValue =>
                  simp [evalPanValueExp, hexpr, hget] at h
                  subst h
                  exact panValueIsWfValues_getElem?
                    (by simpa [panValueIsWf] using ih (.rStruct innerFields) hexpr) hget
          | nStruct nm fs => simp [evalPanValueExp, hexpr] at h
    · intro name fields memoryAccess ih values h
      cases hinfo : lookupInfo name structs with
      | none => simp [evalPanValueExp, hinfo] at h
      | some info =>
          cases hfields : evalPanValueExp.evalPanValueFields structs locals
              globals memory baseAddress topAddress bytesInWord fields
              memoryAccess with
          | none => simp [evalPanValueExp, hinfo, hfields] at h
          | some fieldValues =>
              by_cases hshapes :
                  panValueFieldsExactHOL structs info.fields fieldValues = true
              · simp [evalPanValueExp, hinfo, hfields, hshapes] at h
                subst h
                simp only [panValueIsWf, Bool.and_eq_true]
                refine ⟨?_, ih fieldValues hfields⟩
                rw [hinfo]
                rfl
              · simp [evalPanValueExp, hinfo, hfields, hshapes] at h
    · intro name expression memoryAccess ih value h
      cases hexpr : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord expression memoryAccess with
      | none => simp [evalPanValueExp, hexpr] at h
      | some inner =>
          cases inner with
          | word w => simp [evalPanValueExp, hexpr] at h
          | rStruct fs => simp [evalPanValueExp, hexpr] at h
          | nStruct structName fields =>
              by_cases hsome : (lookupInfo structName structs).isSome = true
              · cases hlookup : lookupPanValueField name fields with
                | none => simp [evalPanValueExp, hexpr, hsome, hlookup] at h
                | some fieldValue =>
                    simp [evalPanValueExp, hexpr, hsome, hlookup] at h
                    subst h
                    have hwfInner : panValueIsWf structs (.nStruct structName fields) = true :=
                      ih (.nStruct structName fields) hexpr
                    simp only [panValueIsWf, Bool.and_eq_true] at hwfInner
                    exact panValueIsWfFields_lookupPanValueField hwfInner.2 hlookup
              · simp [evalPanValueExp, hexpr, hsome] at h
    · intro shape address memoryAccess ih value h
      cases haddr : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord address memoryAccess with
      | none => simp [evalPanValueExp, haddr] at h
      | some addrValue =>
          cases addrValue with
          | word addr =>
              simp [evalPanValueExp, haddr] at h
              exact panValueFlatLoad_wf structs memory bytesInWord addr shape
                memoryAccess value h
          | rStruct fs => simp [evalPanValueExp, haddr] at h
          | nStruct nm fs => simp [evalPanValueExp, haddr] at h
    · intro address memoryAccess ih value h
      cases memoryAccess with
      | none =>
          cases haddr : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord address none with
          | none => simp [evalPanValueExp, haddr] at h
          | some addrValue =>
              cases addrValue with
              | word addr =>
                  cases hread : memory addr with
                  | none => simp [evalPanValueExp, haddr, hread] at h
                  | some memValue =>
                      cases memValue with
                      | word w =>
                          simp [evalPanValueExp, haddr, hread] at h
                          subst h
                          exact panValueIsWf_word structs w
                      | rStruct fs => simp [evalPanValueExp, haddr, hread] at h
                      | nStruct nm fs => simp [evalPanValueExp, haddr, hread] at h
              | rStruct fs => simp [evalPanValueExp, haddr] at h
              | nStruct nm fs => simp [evalPanValueExp, haddr] at h
      | some access =>
          cases haddr : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord address (some access) with
          | none => simp [evalPanValueExp, haddr] at h
          | some addrValue =>
              cases addrValue with
              | word addr =>
                  cases hread : access.read32 access.domain memory bytesInWord addr with
                  | none => simp [evalPanValueExp, haddr, hread] at h
                  | some w =>
                      simp [evalPanValueExp, haddr, hread] at h
                      subst h
                      exact panValueIsWf_word structs w
              | rStruct fs => simp [evalPanValueExp, haddr] at h
              | nStruct nm fs => simp [evalPanValueExp, haddr] at h
    · intro address memoryAccess ih value h
      cases memoryAccess with
      | none =>
          cases haddr : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord address none with
          | none => simp [evalPanValueExp, haddr] at h
          | some addrValue =>
              cases addrValue with
              | word addr =>
                  cases hread : memory addr with
                  | none => simp [evalPanValueExp, haddr, hread] at h
                  | some memValue =>
                      cases memValue with
                      | word w =>
                          simp [evalPanValueExp, haddr, hread] at h
                          subst h
                          exact panValueIsWf_word structs w
                      | rStruct fs => simp [evalPanValueExp, haddr, hread] at h
                      | nStruct nm fs => simp [evalPanValueExp, haddr, hread] at h
              | rStruct fs => simp [evalPanValueExp, haddr] at h
              | nStruct nm fs => simp [evalPanValueExp, haddr] at h
      | some access =>
          cases haddr : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord address (some access) with
          | none => simp [evalPanValueExp, haddr] at h
          | some addrValue =>
              cases addrValue with
              | word addr =>
                  cases hread : access.readByte access.domain memory bytesInWord addr with
                  | none => simp [evalPanValueExp, haddr, hread] at h
                  | some w =>
                      simp [evalPanValueExp, haddr, hread] at h
                      subst h
                      exact panValueIsWf_word structs w
              | rStruct fs => simp [evalPanValueExp, haddr] at h
              | nStruct nm fs => simp [evalPanValueExp, haddr] at h
    · intro operator arguments memoryAccess ih value h
      cases memoryAccess with
      | none =>
          cases hargs : evalPanValueExp.evalPanValueExps structs locals globals
              memory baseAddress topAddress bytesInWord arguments none with
          | none => simp [evalPanValueExp, hargs] at h
          | some argValues =>
              simp [evalPanValueExp, hargs] at h
              rw [Option.bind_eq_some_iff] at h
              obtain ⟨nums, _hmap, hnums⟩ := h
              cases nums with
              | nil => simp at hnums
              | cons a rest =>
                  cases rest with
                  | nil => simp at hnums
                  | cons b rest2 =>
                      cases rest2 with
                      | nil =>
                          simp at hnums
                          subst hnums
                          exact panValueIsWf_word structs _
                      | cons c rest3 => simp at hnums
      | some access =>
          cases hargs : evalPanValueExp.evalPanValueExps structs locals globals
              memory baseAddress topAddress bytesInWord arguments (some access) with
          | none => simp [evalPanValueExp, hargs] at h
          | some argValues =>
              simp [evalPanValueExp, hargs] at h
              rw [Option.bind_eq_some_iff] at h
              obtain ⟨nums, _hmap, hnums⟩ := h
              cases hword : access.wordOp operator nums with
              | none => simp [hword] at hnums
              | some w =>
                  simp [hword] at hnums
                  subst hnums
                  exact panValueIsWf_word structs w
    · intro operator arguments memoryAccess ih value h
      cases hargs : evalPanValueExp.evalPanValueExps structs locals globals
          memory baseAddress topAddress bytesInWord arguments memoryAccess with
      | none => simp [evalPanValueExp, hargs] at h
      | some argValues =>
          cases argValues with
          | nil => simp [evalPanValueExp, hargs] at h
          | cons first rest =>
              cases rest with
              | nil => simp [evalPanValueExp, hargs] at h
              | cons second rest2 =>
                  cases rest2 with
                  | cons third rest3 => simp [evalPanValueExp, hargs] at h
                  | nil =>
                      cases first with
                      | word left =>
                          cases second with
                          | word right =>
                              cases hpan : evalPanOp operator [left, right] with
                              | none => simp [evalPanValueExp, hargs, hpan] at h
                              | some w =>
                                  simp [evalPanValueExp, hargs, hpan] at h
                                  subst h
                                  exact panValueIsWf_word structs w
                          | rStruct fs => simp [evalPanValueExp, hargs] at h
                          | nStruct nm fs => simp [evalPanValueExp, hargs] at h
                      | rStruct fs => simp [evalPanValueExp, hargs] at h
                      | nStruct nm fs => simp [evalPanValueExp, hargs] at h
    · intro operator left right memoryAccess ihLeft ihRight value h
      cases memoryAccess with
      | none =>
          cases hleft : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord left none with
          | none => simp [evalPanValueExp, hleft] at h
          | some leftValue =>
              cases hright : evalPanValueExp structs locals globals memory baseAddress
                  topAddress bytesInWord right none with
              | none => simp [evalPanValueExp, hleft, hright] at h
              | some rightValue =>
                  cases leftValue with
                  | word l =>
                      cases rightValue with
                      | word r =>
                          simp [evalPanValueExp, hleft, hright] at h
                          subst h
                          exact panValueIsWf_word structs _
                      | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                      | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
                  | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                  | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
      | some access =>
          cases hleft : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord left (some access) with
          | none => simp [evalPanValueExp, hleft] at h
          | some leftValue =>
              cases hright : evalPanValueExp structs locals globals memory baseAddress
                  topAddress bytesInWord right (some access) with
              | none => simp [evalPanValueExp, hleft, hright] at h
              | some rightValue =>
                  cases leftValue with
                  | word l =>
                      cases rightValue with
                      | word r =>
                          simp [evalPanValueExp, hleft, hright] at h
                          subst h
                          exact panValueIsWf_word structs _
                      | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                      | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
                  | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                  | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
    · intro operator left right memoryAccess ihLeft ihRight value h
      cases memoryAccess with
      | none =>
          cases hleft : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord left none with
          | none => simp [evalPanValueExp, hleft] at h
          | some leftValue =>
              cases hright : evalPanValueExp structs locals globals memory baseAddress
                  topAddress bytesInWord right none with
              | none => simp [evalPanValueExp, hleft, hright] at h
              | some rightValue =>
                  cases leftValue with
                  | word l =>
                      cases rightValue with
                      | word r =>
                          cases hshift : evalPanShift operator l r with
                          | none => simp [evalPanValueExp, hleft, hright, hshift] at h
                          | some w =>
                              simp [evalPanValueExp, hleft, hright, hshift] at h
                              subst h
                              exact panValueIsWf_word structs w
                      | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                      | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
                  | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                  | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
      | some access =>
          cases hleft : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord left (some access) with
          | none => simp [evalPanValueExp, hleft] at h
          | some leftValue =>
              cases hright : evalPanValueExp structs locals globals memory baseAddress
                  topAddress bytesInWord right (some access) with
              | none => simp [evalPanValueExp, hleft, hright] at h
              | some rightValue =>
                  cases leftValue with
                  | word l =>
                      cases rightValue with
                      | word r =>
                          cases hshift : access.shift operator l r with
                          | none => simp [evalPanValueExp, hleft, hright, hshift] at h
                          | some w =>
                              simp [evalPanValueExp, hleft, hright, hshift] at h
                              subst h
                              exact panValueIsWf_word structs w
                      | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                      | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
                  | rStruct fs => simp [evalPanValueExp, hleft, hright] at h
                  | nStruct nm fs => simp [evalPanValueExp, hleft, hright] at h
    · intro memoryAccess value h
      simp only [evalPanValueExp, Option.some.injEq] at h
      subst h
      exact panValueIsWf_word structs _
    · intro memoryAccess value h
      simp only [evalPanValueExp, Option.some.injEq] at h
      subst h
      exact panValueIsWf_word structs _
    · intro memoryAccess value h
      simp only [evalPanValueExp, Option.some.injEq] at h
      subst h
      exact panValueIsWf_word structs _
    · intro memoryAccess values h
      simp only [evalPanValueExp.evalPanValueFields, Option.some.injEq] at h
      subst h
      simp [panValueIsWfFields]
    · intro name expression fields memoryAccess ihHead ihTail values h
      cases hvalue : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord expression memoryAccess with
      | none => simp [evalPanValueExp.evalPanValueFields, hvalue] at h
      | some head =>
          cases hvalues : evalPanValueExp.evalPanValueFields structs locals
              globals memory baseAddress topAddress bytesInWord fields
              memoryAccess with
          | none => simp [evalPanValueExp.evalPanValueFields, hvalue,
              hvalues] at h
          | some tail =>
              simp [evalPanValueExp.evalPanValueFields, hvalue, hvalues] at h
              subst h
              simp only [panValueIsWfFields, Bool.and_eq_true]
              exact ⟨ihHead head hvalue, ihTail tail hvalues⟩
  exact hmain expression memoryAccess value heval

/-! Cake's `opt_mmap_eval_is_wf_shape_v` (`pan_to_crepProofScript.sml:2328`)
    lifts the single-expression evaluator result relation to a successful list
    evaluation.  The local and global well-formedness premises remain explicit,
    matching the source state's evaluator invariants. -/
theorem evalPanValueExps_isWfShape [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (hlocals : ∀ name value, locals name = some value → panValueIsWf structs value = true)
    (hglobals : ∀ name value, globals name = some value → panValueIsWf structs value = true)
    (expressions : List (Exp α)) (memoryAccess : Option (PanValueMemoryAccess α))
    (values : List (PanValue α))
    (heval : evalPanValueExps structs locals globals memory baseAddress topAddress
      bytesInWord expressions memoryAccess = some values) :
    panValueIsWfValues structs values = true := by
  induction expressions generalizing values with
  | nil =>
      simp [evalPanValueExps, evalPanValueExp.evalPanValueExps] at heval
      subst values
      simp [panValueIsWfValues]
  | cons expression expressions ih =>
      simp only [evalPanValueExps, evalPanValueExp.evalPanValueExps] at heval
      cases hhead : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord expression memoryAccess with
      | none => simp [hhead] at heval
      | some head =>
          cases htail : evalPanValueExp.evalPanValueExps structs locals globals
              memory baseAddress topAddress bytesInWord expressions memoryAccess with
          | none => simp [hhead, htail] at heval
          | some tail =>
              simp [hhead, htail] at heval
              subst values
              simp only [panValueIsWfValues, Bool.and_eq_true]
              exact ⟨evalPanValueExp_isWfShape structs locals globals memory
                baseAddress topAddress bytesInWord hlocals hglobals expression
                memoryAccess head hhead, ih tail htail⟩

theorem evalPanValueExp_isSome_local
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (baseAddress topAddress bytesInWord : α)
    (expression : Exp α) (memoryAccess : Option (PanValueMemoryAccess α))
    (value : PanValue α)
    (heval : evalPanValueExp structs locals globals memory baseAddress topAddress
      bytesInWord expression memoryAccess = some value)
    {name : VarName} (hmem : name ∈ expLocalVars expression) :
    ∃ w, locals name = some w := by
  have hmain : ∀ expression memoryAccess,
      (∀ value, evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord expression memoryAccess = some value →
        ∀ name, name ∈ expLocalVars expression → ∃ w, locals name = some w) := by
    apply evalPanValueExp.induct
      (motive1 := fun expressions memoryAccess =>
        ∀ values, evalPanValueExp.evalPanValueExps structs locals globals memory
            baseAddress topAddress bytesInWord expressions memoryAccess = some values →
          ∀ name, name ∈ expLocalVars.expLocalVarsList expressions →
            ∃ w, locals name = some w)
      (motive2 := fun expression memoryAccess =>
        ∀ value, evalPanValueExp structs locals globals memory baseAddress
            topAddress bytesInWord expression memoryAccess = some value →
          ∀ name, name ∈ expLocalVars expression → ∃ w, locals name = some w)
      (motive3 := fun fields memoryAccess =>
        ∀ values, evalPanValueExp.evalPanValueFields structs locals globals memory
            baseAddress topAddress bytesInWord fields memoryAccess = some values →
          ∀ name, name ∈ expLocalVars.expLocalVarsFieldList fields →
            ∃ w, locals name = some w)
    · intro memoryAccess values hvalues name hmem
      simp only [evalPanValueExp.evalPanValueExps,
        Option.some.injEq] at hvalues
      subst hvalues
      simp [expLocalVars.expLocalVarsList] at hmem
    · intro expression expressions memoryAccess ihExpr ihExprs values hvalues name hmem
      simp only [evalPanValueExp.evalPanValueExps] at hvalues
      cases hvalue : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord expression memoryAccess with
      | none => simp [hvalue] at hvalues
      | some head =>
          cases hvalues' : evalPanValueExp.evalPanValueExps structs locals globals
              memory baseAddress topAddress bytesInWord expressions memoryAccess with
          | none => simp [hvalue, hvalues'] at hvalues
          | some tail =>
              simp [hvalue, hvalues'] at hvalues
              subst hvalues
              simp only [expLocalVars.expLocalVarsList, List.mem_append] at hmem
              rcases hmem with hmem | hmem
              · exact ihExpr head hvalue name hmem
              · exact ihExprs tail hvalues' name hmem
    · intro memoryAccess payload value heval name hmem
      simp only [evalPanValueExp, Option.some.injEq] at heval
      simp [expLocalVars] at hmem
    · intro memoryAccess name value heval name' hmem
      simp only [evalPanValueExp] at heval
      simp [expLocalVars] at hmem
      subst hmem
      exact ⟨value, heval⟩
    · intro memoryAccess name value heval name' hmem
      simp only [evalPanValueExp] at heval
      simp [expLocalVars] at hmem
    · intro fields memoryAccess ihFields value hvalue name hmem
      cases hfields : evalPanValueExp.evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord fields memoryAccess with
      | none => simp [evalPanValueExp, hfields] at hvalue
      | some fieldValues =>
          simp [evalPanValueExp, hfields] at hvalue
          subst hvalue
          simp only [expLocalVars] at hmem
          exact ihFields fieldValues hfields name hmem
    · intro index expression memoryAccess ihExpr value hvalue name hmem
      simp only [evalPanValueExp] at hvalue
      cases hinner : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord expression memoryAccess with
      | none => simp [hinner] at hvalue
      | some inner =>
          simp [hinner] at hvalue
          simp only [expLocalVars] at hmem
          exact ihExpr inner hinner name hmem
    · intro name fields memoryAccess ihFields value hvalue name' hmem
      cases hinfo : lookupInfo name structs with
      | none => simp [evalPanValueExp, hinfo] at hvalue
      | some info =>
          cases hfields : evalPanValueExp.evalPanValueFields structs locals globals
              memory baseAddress topAddress bytesInWord fields memoryAccess with
          | none => simp [evalPanValueExp, hinfo, hfields] at hvalue
          | some fieldValues =>
              by_cases hshapes : panValueFieldsExactHOL structs info.fields fieldValues = true
              · simp [evalPanValueExp, hinfo, hfields, hshapes] at hvalue
                subst hvalue
                simp only [expLocalVars] at hmem
                exact ihFields fieldValues hfields name' hmem
              · simp [evalPanValueExp, hinfo, hfields, hshapes] at hvalue
    · intro name expression memoryAccess ihExpr value hvalue name' hmem
      simp only [evalPanValueExp] at hvalue
      cases hinner : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord expression memoryAccess with
      | none => simp [hinner] at hvalue
      | some inner =>
          simp [hinner] at hvalue
          simp only [expLocalVars] at hmem
          exact ihExpr inner hinner name' hmem
    · intro shape address memoryAccess ihAddr value hvalue name hmem
      simp only [evalPanValueExp] at hvalue
      cases haddr : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord address memoryAccess with
      | none => simp [haddr] at hvalue
      | some addrValue =>
          simp [haddr] at hvalue
          simp only [expLocalVars] at hmem
          exact ihAddr addrValue haddr name hmem
    · intro address memoryAccess ihAddr value hvalue name hmem
      cases memoryAccess with
      | none =>
          simp only [evalPanValueExp] at hvalue
          cases haddr : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord address none with
          | none => simp [haddr] at hvalue
          | some addrValue =>
              simp [haddr] at hvalue
              simp only [expLocalVars] at hmem
              exact ihAddr addrValue haddr name hmem
      | some access =>
          simp only [evalPanValueExp] at hvalue
          cases haddr : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord address (some access) with
          | none => simp [haddr] at hvalue
          | some addrValue =>
              simp [haddr] at hvalue
              simp only [expLocalVars] at hmem
              exact ihAddr addrValue haddr name hmem
    · intro address memoryAccess ihAddr value hvalue name hmem
      cases memoryAccess with
      | none =>
          simp only [evalPanValueExp] at hvalue
          cases haddr : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord address none with
          | none => simp [haddr] at hvalue
          | some addrValue =>
              simp [haddr] at hvalue
              simp only [expLocalVars] at hmem
              exact ihAddr addrValue haddr name hmem
      | some access =>
          simp only [evalPanValueExp] at hvalue
          cases haddr : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord address (some access) with
          | none => simp [haddr] at hvalue
          | some addrValue =>
              simp [haddr] at hvalue
              simp only [expLocalVars] at hmem
              exact ihAddr addrValue haddr name hmem
    · intro operator arguments memoryAccess ihArgs value hvalue name hmem
      cases memoryAccess with
      | none =>
          simp only [evalPanValueExp] at hvalue
          cases hargs : evalPanValueExp.evalPanValueExps structs locals globals memory
              baseAddress topAddress bytesInWord arguments none with
          | none => simp [hargs] at hvalue
          | some argValues =>
              simp [hargs] at hvalue
              simp only [expLocalVars] at hmem
              exact ihArgs argValues hargs name hmem
      | some access =>
          simp only [evalPanValueExp] at hvalue
          cases hargs : evalPanValueExp.evalPanValueExps structs locals globals memory
              baseAddress topAddress bytesInWord arguments (some access) with
          | none => simp [hargs] at hvalue
          | some argValues =>
              simp [hargs] at hvalue
              simp only [expLocalVars] at hmem
              exact ihArgs argValues hargs name hmem
    · intro operator arguments memoryAccess ihArgs value hvalue name hmem
      simp only [evalPanValueExp] at hvalue
      cases hargs : evalPanValueExp.evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments memoryAccess with
      | none => simp [hargs] at hvalue
      | some argValues =>
          simp [hargs] at hvalue
          simp only [expLocalVars] at hmem
          exact ihArgs argValues hargs name hmem
    · intro operator left right memoryAccess ihLeft ihRight value hvalue name hmem
      cases memoryAccess with
      | none =>
          simp only [evalPanValueExp] at hvalue
          cases hleft : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord left none with
          | none => simp [hleft] at hvalue
          | some leftValue =>
              cases hright : evalPanValueExp structs locals globals memory baseAddress
                  topAddress bytesInWord right none with
              | none => simp [hleft, hright] at hvalue
              | some rightValue =>
                  simp [hleft, hright] at hvalue
                  simp only [expLocalVars, List.mem_append] at hmem
                  rcases hmem with hmem | hmem
                  · exact ihLeft leftValue hleft name hmem
                  · exact ihRight rightValue hright name hmem
      | some access =>
          simp only [evalPanValueExp] at hvalue
          cases hleft : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord left (some access) with
          | none => simp [hleft] at hvalue
          | some leftValue =>
              cases hright : evalPanValueExp structs locals globals memory baseAddress
                  topAddress bytesInWord right (some access) with
              | none => simp [hleft, hright] at hvalue
              | some rightValue =>
                  simp [hleft, hright] at hvalue
                  simp only [expLocalVars, List.mem_append] at hmem
                  rcases hmem with hmem | hmem
                  · exact ihLeft leftValue hleft name hmem
                  · exact ihRight rightValue hright name hmem
    · intro operator left right memoryAccess ihLeft ihRight value hvalue name hmem
      cases memoryAccess with
      | none =>
          simp only [evalPanValueExp] at hvalue
          cases hleft : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord left none with
          | none => simp [hleft] at hvalue
          | some leftValue =>
              cases hright : evalPanValueExp structs locals globals memory baseAddress
                  topAddress bytesInWord right none with
              | none => simp [hleft, hright] at hvalue
              | some rightValue =>
                  simp [hleft, hright] at hvalue
                  simp only [expLocalVars, List.mem_append] at hmem
                  rcases hmem with hmem | hmem
                  · exact ihLeft leftValue hleft name hmem
                  · exact ihRight rightValue hright name hmem
      | some access =>
          simp only [evalPanValueExp] at hvalue
          cases hleft : evalPanValueExp structs locals globals memory baseAddress
              topAddress bytesInWord left (some access) with
          | none => simp [hleft] at hvalue
          | some leftValue =>
              cases hright : evalPanValueExp structs locals globals memory baseAddress
                  topAddress bytesInWord right (some access) with
              | none => simp [hleft, hright] at hvalue
              | some rightValue =>
                  simp [hleft, hright] at hvalue
                  simp only [expLocalVars, List.mem_append] at hmem
                  rcases hmem with hmem | hmem
                  · exact ihLeft leftValue hleft name hmem
                  · exact ihRight rightValue hright name hmem
    · intro memoryAccess value heval name hmem
      simp only [evalPanValueExp, Option.some.injEq] at heval
      simp [expLocalVars] at hmem
    · intro memoryAccess value heval name hmem
      simp only [evalPanValueExp, Option.some.injEq] at heval
      simp [expLocalVars] at hmem
    · intro memoryAccess value heval name hmem
      simp only [evalPanValueExp, Option.some.injEq] at heval
      simp [expLocalVars] at hmem
    · intro memoryAccess values hvalues name hmem
      simp only [evalPanValueExp.evalPanValueFields, Option.some.injEq] at hvalues
      subst hvalues
      simp [expLocalVars.expLocalVarsFieldList] at hmem
    · intro fieldName expression fields memoryAccess ihExpr ihFields values hvalues name hmem
      simp only [evalPanValueExp.evalPanValueFields] at hvalues
      cases hvalue : evalPanValueExp structs locals globals memory baseAddress
          topAddress bytesInWord expression memoryAccess with
      | none => simp [hvalue] at hvalues
      | some head =>
          cases hvalues' : evalPanValueExp.evalPanValueFields structs locals globals
              memory baseAddress topAddress bytesInWord fields memoryAccess with
          | none => simp [hvalue, hvalues'] at hvalues
          | some tail =>
              simp [hvalue, hvalues'] at hvalues
              subst hvalues
              simp only [expLocalVars.expLocalVarsFieldList, List.mem_append] at hmem
              rcases hmem with hmem | hmem
              · exact ihExpr head hvalue name hmem
              · exact ihFields tail hvalues' name hmem
  exact hmain expression memoryAccess value heval name hmem

/-! Target-word counterpart of the structured expression evaluator.

    The generic evaluator above intentionally keeps the historical abstract
    `evalPanShift` contract.  A RISC-V word, however, has CakeML's complete
    `word_sh` operation, including arithmetic shift-right, rotate-right, and
    the width check.  This mutually recursive entrypoint preserves the full
    structured-value and memory-access cases while changing only that target
    operation boundary. -/
mutual
  def evalPanValueExpFull [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) :
      (expression : Exp α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
          Option (PanValue α)
    | .const value, _ => some (.word value)
    | .var .local name, _ => locals name
    | .var .global name, _ => globals name
    | .rStruct fields, memoryAccess =>
        (evalPanValueExpsFull structs locals globals memory
          baseAddress topAddress bytesInWord fields
          (memoryAccess := memoryAccess)).map .rStruct
    | .rField index expression, memoryAccess => do
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord expression
          (memoryAccess := memoryAccess)
        match value with
        | .rStruct fields => fields[index]?
        | _ => none
    | .nStruct name fields, memoryAccess => do
        let info ← lookupInfo name structs
        let values ← evalPanValueFieldsFull structs locals globals memory
          baseAddress topAddress bytesInWord fields
          (memoryAccess := memoryAccess)
        if panValueFieldsExactHOL structs info.fields values then
          pure (.nStruct name values)
        else none
    | .nField name expression, memoryAccess => do
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord expression
          (memoryAccess := memoryAccess)
        match value with
        | .nStruct structName fields =>
            if (lookupInfo structName structs).isSome then
              lookupPanValueField name fields
            else none
        | _ => none
    | .load shape address, memoryAccess => do
        let address ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord address
          (memoryAccess := memoryAccess)
        let .word address := address | none
        panValueFlatLoad structs memory bytesInWord address shape memoryAccess
    | .load32 address, memoryAccess => do
        let address ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord address
          (memoryAccess := memoryAccess)
        let .word address := address | none
        match memoryAccess with
        | none => do
            let value ← memory address
            match value with
            | .word value => some (.word value)
            | _ => none
        | some access => (access.read32 access.domain memory bytesInWord address).map .word
    | .loadByte address, memoryAccess => do
        let address ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord address
          (memoryAccess := memoryAccess)
        let .word address := address | none
        match memoryAccess with
        | none => do
            let value ← memory address
            match value with
            | .word value => some (.word value)
            | _ => none
        | some access => (access.readByte access.domain memory bytesInWord address).map .word
    | .op operator arguments, memoryAccess => do
        let values ← evalPanValueExpsFull structs locals globals memory
          baseAddress topAddress bytesInWord arguments
          (memoryAccess := memoryAccess)
        let values ← values.mapM fun value => match value with
          | .word value => some value
          | _ => none
        match memoryAccess with
        | none => match values with
            | [left, right] => some (.word (evalPanBinOp operator left right))
            | _ => none
        | some access => (access.wordOp operator values).map .word
    | .panOp operator arguments, memoryAccess => do
        let values ← evalPanValueExpsFull structs locals globals memory
          baseAddress topAddress bytesInWord arguments
          (memoryAccess := memoryAccess)
        match values with
        | [.word left, .word right] =>
            (evalPanOp operator [left, right]).map .word
        | _ => none
    | .cmp operator left right, memoryAccess => do
        let left ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord left
          (memoryAccess := memoryAccess)
        let right ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord right
          (memoryAccess := memoryAccess)
        match left, right with
        | .word left, .word right =>
            match memoryAccess with
            | none => some (.word (evalPanCmp operator left right))
            | some access => some (.word (access.compare operator left right))
        | _, _ => none
    | .shift operator left right, memoryAccess => do
        let left ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord left
          (memoryAccess := memoryAccess)
        let right ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord right
          (memoryAccess := memoryAccess)
        match left, right with
        | .word left, .word right =>
            match memoryAccess with
            | none => (evalPanShiftFull operator left right).map .word
            | some access => (access.shift operator left right).map .word
        | _, _ => none
    | .baseAddr, _ => some (.word baseAddress)
    | .topAddr, _ => some (.word topAddress)
    | .bytesInWord, _ => some (.word bytesInWord)
    termination_by expression => sizeOf expression
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  def evalPanValueExpsFull [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) :
      (expressions : List (Exp α)) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
          Option (List (PanValue α))
    | [], _ => some []
    | expression :: expressions, memoryAccess => do
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord expression
          (memoryAccess := memoryAccess)
        let values ← evalPanValueExpsFull structs locals globals memory
          baseAddress topAddress bytesInWord expressions
          (memoryAccess := memoryAccess)
        pure (value :: values)
    termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  def evalPanValueFieldsFull [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (structs : StructContext)
      (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
      (baseAddress topAddress bytesInWord : α) :
      (fields : List (FieldName × Exp α)) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
          Option (List (FieldName × PanValue α))
    | [], _ => some []
    | (name, expression) :: fields, memoryAccess => do
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord expression
          (memoryAccess := memoryAccess)
        let values ← evalPanValueFieldsFull structs locals globals memory
          baseAddress topAddress bytesInWord fields
          (memoryAccess := memoryAccess)
        pure ((name, value) :: values)
    termination_by fields => sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial
end

def updatePanValueMap [BEq γ] (values : γ → Option α)
    (name : γ) (value : α) : γ → Option α :=
  fun current => if current == name then some value else values current

def updatePanValueMemory [BEq α] (memory : α → Option (PanValue α))
    (address : α) (value : PanValue α) : α → Option (PanValue α) :=
  updatePanValueMap memory address value

def panValueStoreWithAccess [BEq α] [Add α]
    (memory : α → Option (PanValue α)) (bytesInWord address : α)
    (value : PanValue α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option (α → Option (PanValue α)) :=
  match memoryAccess with
  | none =>
      panValueFlatStoreWords
        (fun memory address value =>
          some (updatePanValueMemory memory address (.word value)))
        bytesInWord memory address (panValueFlatWords value)
  | some access =>
      panValueFlatStoreWords
        (fun memory address value =>
          access.storeWord access.domain memory bytesInWord address value)
        bytesInWord memory address (panValueFlatWords value)

abbrev PanPrimitiveHandler (α : Type u) :=
  PrimOp → List (PanValue α) → Option (PanValue α)

/-! Bare-metal accelerator calls may update both the local environment and
    source memory.  This is separate from the stateful CakeML FFI handler in
    `PanValueFfiSemantics`, whose state transition models byte-array FFI. -/
abbrev PanValueAcceleratorFfiHandler (α : Type u) :=
  FunName → α → α → α → α →
    (VarName → Option (PanValue α)) →
    (α → Option (PanValue α)) →
    Option ((VarName → Option (PanValue α)) ×
      (α → Option (PanValue α)))

/-! Exact executable counterpart of Pancake's `res_var_def`: restore a
    local binding after a scoped declaration, deleting it when the saved value
    is `NONE` and updating it otherwise. -/
def panValueResVar [BEq String]
    (locals : VarName → Option (PanValue α)) (name : VarName)
    (oldValue : Option (PanValue α)) : VarName → Option (PanValue α) :=
  fun current => if current == name then oldValue else locals current

/-- Counterpart of Cake's `flookup_res_var_some_eq_lookup`
    (`cakeml/pancake/semantics/panPropsScript.sml:220`): looking up the restored
    name returns the saved value. -/
theorem panValueResVar_lookup_same [BEq String] [LawfulBEq String]
    (locals locals' : VarName → Option (PanValue α)) (name : VarName)
    {value : PanValue α}
    (h : panValueResVar locals name (locals' name) name = some value) :
    locals' name = some value := by
  simpa [panValueResVar] using h

/-- Counterpart of Cake's `flookup_res_var_diff_eq_org`
    (`cakeml/pancake/semantics/panPropsScript.sml:228`): a different name keeps
    the original binding. -/
theorem panValueResVar_lookup_diff [BEq String] [LawfulBEq String]
    (locals : VarName → Option (PanValue α)) (name other : VarName)
    (oldValue : Option (PanValue α)) (hne : other ≠ name) :
    panValueResVar locals name oldValue other = locals other := by
  simp [panValueResVar, beq_iff_eq, hne]

/-- Counterpart of Cake's `FLOOKUP_pan_res_var_thm`
    (`cakeml/pancake/semantics/panPropsScript.sml:236`): the restored lookup is
    the saved value at the restored name and the original binding elsewhere. -/
theorem panValueResVar_eq_ite [BEq String] [LawfulBEq String]
    (locals : VarName → Option (PanValue α)) (name : VarName)
    (oldValue : Option (PanValue α)) (other : VarName) :
    panValueResVar locals name oldValue other =
      if other == name then oldValue else locals other := rfl

/-- Flapjack-specific function-map analogue of Cake's `res_var_commutes'`.
    The exact HOL finite-map theorem is tagged in `Proofs/PanToCrep.lean`. -/
theorem panValueResVar_comm [BEq String] [LawfulBEq String]
    (locals : VarName → Option (PanValue α)) (h n : VarName)
    (v v' : Option (PanValue α)) (hne : n ≠ h) :
    panValueResVar (panValueResVar locals h v) n v' =
      panValueResVar (panValueResVar locals n v') h v := by
  funext name
  simp only [panValueResVar]
  by_cases hh : (name == h) = true <;>
    by_cases hn : (name == n) = true <;>
    simp_all [beq_iff_eq]

/-- Counterpart of Cake's `res_var_commutes_strong`
    (`cakeml/pancake/proofs/crep_inlineProofScript.sml:699`): restoring two
    locals commutes even when the two names coincide, because each side reads
    the original binding of the other name from `locals'`. -/
theorem panValueResVar_comm_strong [BEq String] [LawfulBEq String]
    (locals locals' : VarName → Option (PanValue α)) (h n : VarName) :
    panValueResVar (panValueResVar locals h (locals' h)) n (locals' n) =
      panValueResVar (panValueResVar locals n (locals' n)) h (locals' h) := by
  funext x
  by_cases hx : (x == n) = true <;> by_cases hh : (x == h) = true <;>
    simp_all [panValueResVar, beq_iff_eq]

/-- Cake's `FOLDL res_var lc1 (ZIP (vs, MAP (FLOOKUP lc2) vs))`
    (`cakeml/pancake/proofs/crep_inlineProofScript.sml`), used to restore a list
    of locals. -/
def panValueResVarFold [BEq String]
    (locals locals' : VarName → Option (PanValue α)) (names : List VarName) :
    VarName → Option (PanValue α) :=
  (names.zip (names.map locals')).foldl
    (fun (current : VarName → Option (PanValue α))
      (entry : VarName × Option (PanValue α)) =>
      panValueResVar current entry.1 entry.2) locals

theorem panValueResVarFold_cons [BEq String]
    (locals locals' : VarName → Option (PanValue α)) (name : VarName)
    (names : List VarName) :
    panValueResVarFold locals locals' (name :: names) =
      panValueResVarFold (panValueResVar locals name (locals' name)) locals' names := by
  simp [panValueResVarFold]

theorem panValueResVarFold_comm [BEq String] [LawfulBEq String]
    (locals locals' : VarName → Option (PanValue α)) (h : VarName) :
    ∀ names,
      panValueResVar (panValueResVarFold locals locals' names) h (locals' h) =
        panValueResVarFold (panValueResVar locals h (locals' h)) locals' names := by
  intro names
  induction names generalizing locals with
  | nil => simp [panValueResVarFold]
  | cons name names ih =>
      simp only [panValueResVarFold, List.zip_cons_cons, List.map_cons,
        List.foldl_cons] at ih ⊢
      rw [ih (panValueResVar locals name (locals' name))]
      rw [← panValueResVar_comm_strong locals locals' h name]

theorem panValueResVarFold_not_mem [BEq String] [LawfulBEq String]
    (locals locals' : VarName → Option (PanValue α)) (names : List VarName) (x : VarName)
    (hmem : x ∉ names) :
    panValueResVarFold locals locals' names x = locals x := by
  induction names generalizing locals with
  | nil => simp [panValueResVarFold]
  | cons name names ih =>
      rw [panValueResVarFold_cons]
      simp only [List.mem_cons, not_or] at hmem
      have hstep : panValueResVar locals name (locals' name) x = locals x := by
        rw [panValueResVar_eq_ite]
        simp [beq_iff_eq, hmem.1]
      rw [ih (panValueResVar locals name (locals' name)) hmem.2, hstep]

theorem panValueResVarFold_mem [BEq String] [LawfulBEq String]
    (locals locals' : VarName → Option (PanValue α)) (names : List VarName) {x : VarName}
    (hmem : x ∈ names) :
    panValueResVarFold locals locals' names x = locals' x := by
  induction names generalizing locals with
  | nil => simp at hmem
  | cons name names ih =>
      rw [panValueResVarFold_cons]
      simp only [List.mem_cons] at hmem
      by_cases hmemRest : x ∈ names
      · exact ih _ hmemRest
      · rcases hmem with heq | hmem
        · rw [panValueResVarFold_not_mem _ locals' names x hmemRest]
          rw [panValueResVar_eq_ite]
          rw [if_pos (by rw [beq_iff_eq]; exact heq)]
          rw [heq]
        · exact absurd hmem hmemRest


def restorePanValueLocal [BEq String]
    (locals : VarName → Option (PanValue α)) (name : VarName)
    (oldValue : Option (PanValue α)) : VarName → Option (PanValue α) :=
  fun current => if current == name then oldValue else locals current

def evalPanValueProgWithPrimitive [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (primitive : PanPrimitiveHandler α) :
    (program : Prog α) →
    (memoryAccess : Option (PanValueMemoryAccess α) := none) →
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (α → Option (PanValue α)) × List (PanValue α))
  | .skip, _ => some (locals, globals, memory, [])
  | .dec name shape value body, memoryAccess => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panShapeMatches (panValueShape structs value) shape then
        let oldValue := locals name
        let result ← evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
          (updatePanValueMap locals name value) globals memory primitive body
          (memoryAccess := memoryAccess)
        pure (restorePanValueLocal result.1 name oldValue,
          result.2.1, result.2.2.1, result.2.2.2)
      else none
  | .assign .local name value, memoryAccess => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panValueAssignmentValid structs locals globals .local name value then
        pure (updatePanValueMap locals name value, globals, memory, [])
      else none
  | .assign .global name value, memoryAccess => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panValueAssignmentValid structs locals globals .global name value then
        pure (locals, updatePanValueMap globals name value, memory, [])
      else none
  | .primitive name operator arguments, memoryAccess => do
      let values ← evalPanValueExps structs locals globals memory
        baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
      let value ← primitive operator values
      let oldValue ← locals name
      if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
        pure (updatePanValueMap locals name value, globals, memory, [])
      else none
  | .store address value, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let memory ← panValueStoreWithAccess memory bytesInWord address value memoryAccess
      pure (locals, globals, memory, [])
  | .store32 address value, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let .word value := value | none
      let memory ← match memoryAccess with
        | none => some (updatePanValueMemory memory address (.word value))
        | some access => access.store32 access.domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .storeByte address value, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let .word value := value | none
      let memory ← match memoryAccess with
        | none => some (updatePanValueMemory memory address (.word value))
        | some access => access.storeByte access.domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .return value, memoryAccess => do
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panValuePayloadWithinLimit structs value then
        pure ((fun _ => none), globals, memory, [value])
      else none
  | .seq first second, memoryAccess => do
      let result ← evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
        locals globals memory primitive first (memoryAccess := memoryAccess)
      if result.2.2.2.isEmpty then
        evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
          result.1 result.2.1 result.2.2.1 primitive second (memoryAccess := memoryAccess)
      else pure result
  | .ite condition thenBranch elseBranch, memoryAccess => do
      let condition ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord condition (memoryAccess := memoryAccess)
      let .word condition := condition | none
      if condition != 0 then
        evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
          locals globals memory primitive thenBranch (memoryAccess := memoryAccess)
      else
        evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
          locals globals memory primitive elseBranch (memoryAccess := memoryAccess)
  | .shMemLoad size kind name address, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let .word address := address | none
      let value ← match memoryAccess with
        | none => memory address
        | some access => access.sharedRead memory bytesInWord size address
      if panValueSharedLoadValid structs locals globals kind name value then
        match kind with
        | .local => pure (updatePanValueMap locals name value, globals, memory, [])
        | .global => pure (locals, updatePanValueMap globals name value, memory, [])
      else none
  | .shMemStore size address value, memoryAccess => do
      let address ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanValueExp structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let .word value := value | none
      let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.sharedStore memory bytesInWord size address (.word value)
      pure (locals, globals, memory, [])
  | .tick, _ | .annot _ _, _ => some (locals, globals, memory, [])
  | _, _ => none
termination_by program => sizeOf program

/-! Target-word structured program evaluator.  This mirrors
    `evalPanValueProgWithPrimitive` but routes every expression through the
    complete Cake `word_sh` boundary.  The older evaluator remains available
    for abstract proofs that intentionally use the compatibility contract. -/
def evalPanValueProgWithPrimitiveFull [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (primitive : PanPrimitiveHandler α) :
    (program : Prog α) →
    (memoryAccess : Option (PanValueMemoryAccess α) := none) →
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (α → Option (PanValue α)) × List (PanValue α))
  | .skip, _ => some (locals, globals, memory, [])
  | .dec name shape value body, memoryAccess => do
      let value ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panShapeMatches (panValueShape structs value) shape then
        let oldValue := locals name
        let result ← evalPanValueProgWithPrimitiveFull structs
          baseAddress topAddress bytesInWord
          (updatePanValueMap locals name value) globals memory primitive body
          (memoryAccess := memoryAccess)
        pure (restorePanValueLocal result.1 name oldValue,
          result.2.1, result.2.2.1, result.2.2.2)
      else none
  | .assign .local name value, memoryAccess => do
      let value ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panValueAssignmentValid structs locals globals .local name value then
        pure (updatePanValueMap locals name value, globals, memory, [])
      else none
  | .assign .global name value, memoryAccess => do
      let value ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panValueAssignmentValid structs locals globals .global name value then
        pure (locals, updatePanValueMap globals name value, memory, [])
      else none
  | .primitive name operator arguments, memoryAccess => do
      let values ← evalPanValueExpsFull structs locals globals memory
        baseAddress topAddress bytesInWord arguments
        (memoryAccess := memoryAccess)
      let value ← primitive operator values
      let oldValue ← locals name
      if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
        pure (updatePanValueMap locals name value, globals, memory, [])
      else none
  | .store address value, memoryAccess => do
      let address ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let memory ← panValueStoreWithAccess memory bytesInWord address value memoryAccess
      pure (locals, globals, memory, [])
  | .store32 address value, memoryAccess => do
      let address ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let .word value := value | none
      let memory ← match memoryAccess with
        | none => some (updatePanValueMemory memory address (.word value))
        | some access => access.store32 access.domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .storeByte address value, memoryAccess => do
      let address ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let .word value := value | none
      let memory ← match memoryAccess with
        | none => some (updatePanValueMemory memory address (.word value))
        | some access => access.storeByte access.domain memory bytesInWord address value
      pure (locals, globals, memory, [])
  | .return value, memoryAccess => do
      let value ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      if panValuePayloadWithinLimit structs value then
        pure ((fun _ => none), globals, memory, [value])
      else none
  | .seq first second, memoryAccess => do
      let result ← evalPanValueProgWithPrimitiveFull structs
        baseAddress topAddress bytesInWord locals globals memory primitive first
        (memoryAccess := memoryAccess)
      if result.2.2.2.isEmpty then
        evalPanValueProgWithPrimitiveFull structs
          baseAddress topAddress bytesInWord
          result.1 result.2.1 result.2.2.1 primitive second
          (memoryAccess := memoryAccess)
      else pure result
  | .ite condition thenBranch elseBranch, memoryAccess => do
      let condition ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord condition
        (memoryAccess := memoryAccess)
      let .word condition := condition | none
      if condition != 0 then
        evalPanValueProgWithPrimitiveFull structs
          baseAddress topAddress bytesInWord locals globals memory primitive thenBranch
          (memoryAccess := memoryAccess)
      else
        evalPanValueProgWithPrimitiveFull structs
          baseAddress topAddress bytesInWord locals globals memory primitive elseBranch
          (memoryAccess := memoryAccess)
  | .shMemLoad size kind name address, memoryAccess => do
      let address ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let .word address := address | none
      let value ← match memoryAccess with
        | none => memory address
        | some access => access.sharedRead memory bytesInWord size address
      if panValueSharedLoadValid structs locals globals kind name value then
        match kind with
        | .local => pure (updatePanValueMap locals name value, globals, memory, [])
        | .global => pure (locals, updatePanValueMap globals name value, memory, [])
      else none
  | .shMemStore size address value, memoryAccess => do
      let address ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
      let value ← evalPanValueExpFull structs locals globals memory
        baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
      let .word address := address | none
      let .word value := value | none
      let memory ← match memoryAccess with
        | none => some (updatePanValueMemory memory address (.word value))
        | some access => access.sharedStore memory bytesInWord size address (.word value)
      pure (locals, globals, memory, [])
  | .tick, _ | .annot _ _, _ => some (locals, globals, memory, [])
  | _, _ => none
termination_by program => sizeOf program

def evalPanValueProgFull [BEq α] [OfNat α 0] [OfNat α 1]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (α → Option (PanValue α)) × List (PanValue α)) :=
  evalPanValueProgWithPrimitiveFull structs baseAddress topAddress bytesInWord
    locals globals memory (fun _ _ => none) program memoryAccess

def evalPanValueProgWithPrimitiveExact
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (memoryAccess : PanValueMemoryAccess α)
    (primitive : PanPrimitiveHandler α) (program : Prog α) :
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (α → Option (PanValue α)) × List (PanValue α)) :=
  evalPanValueProgWithPrimitiveFull structs baseAddress topAddress bytesInWord
    locals globals memory primitive program (memoryAccess := some memoryAccess)

def evalPanValueProgExact
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (memoryAccess : PanValueMemoryAccess α) (program : Prog α) :
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (α → Option (PanValue α)) × List (PanValue α)) :=
  evalPanValueProgWithPrimitiveExact structs baseAddress topAddress bytesInWord
    locals globals memory memoryAccess (fun _ _ => none) program

/-! A checked exact-memory load equation for the structured program boundary.
    This is the source-side `panSem` shared-load shape: the address expression
    is evaluated with the full word contract, then the required memory adapter
    supplies the fixed-width value before the destination validity check. -/
theorem evalPanValueProgWithPrimitiveExact_shMemLoad_local_word
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [PanShiftWidth α]
    [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (memoryAccess : PanValueMemoryAccess α)
    (primitive : PanPrimitiveHandler α)
    (size : OpSize) (name : VarName) (address value : α)
    (sourceAddress : Exp α)
    (haddress : evalPanValueExpFull structs locals globals memory
      baseAddress topAddress bytesInWord sourceAddress
      (memoryAccess := some memoryAccess) = some (.word address))
    (hvalue : memoryAccess.sharedRead memory bytesInWord size address =
      some (.word value))
    (hvalid : panValueSharedLoadValid structs locals globals .local name
      (.word value) = true) :
    evalPanValueProgWithPrimitiveExact structs baseAddress topAddress bytesInWord
      locals globals memory memoryAccess primitive
      (.shMemLoad size .local name sourceAddress) =
      some (updatePanValueMap locals name (.word value), globals, memory, []) := by
  simp [evalPanValueProgWithPrimitiveExact,
    evalPanValueProgWithPrimitiveFull, haddress, hvalue, hvalid]

def evalPanValueProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (baseAddress topAddress bytesInWord : α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) ×
      (α → Option (PanValue α)) × List (PanValue α)) :=
  evalPanValueProgWithPrimitive structs baseAddress topAddress bytesInWord
    locals globals memory (fun _ _ => none) program memoryAccess

inductive PanValueControlResult (α : Type u) where
  | normal (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | returned (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (values : List (PanValue α))
  | raised (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (exception : ExceptionId)
      (value : PanValue α)
  | broke (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))
  | continued (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α))

def restorePanValueControlLocal [BEq String]
    (name : VarName) (oldValue : Option (PanValue α)) :
    PanValueControlResult α → PanValueControlResult α
  | .normal locals globals memory =>
      .normal (restorePanValueLocal locals name oldValue) globals memory
  | .returned locals globals memory values =>
      .returned (restorePanValueLocal locals name oldValue) globals memory values
  | .raised locals globals memory exception value =>
      .raised (restorePanValueLocal locals name oldValue) globals memory exception value
  | .broke locals globals memory =>
      .broke (restorePanValueLocal locals name oldValue) globals memory
  | .continued locals globals memory =>
      .continued (restorePanValueLocal locals name oldValue) globals memory

/-! Exact executable counterpart of Pancake's `upd_locals_def`
    (`cakeml/pancake/semantics/panSemScript.sml:431-434`).  The source
    installs the zipped argument bindings into an empty local map; folding
    updates gives the same last-wins behavior for duplicate names. -/
def bindPanValueParameters (parameters : List VarName)
    (values : List (PanValue α)) :
    Option (VarName → Option (PanValue α)) :=
  if parameters.length != values.length then none
  else
    some ((parameters.zip values).foldl
      (fun locals (name, value) => updatePanValueMap locals name value)
      (fun _ => none))

def assignPanValueCallResult
    (locals : VarName → Option (PanValue α))
    (globals : VarName → Option (PanValue α))
    (destination : Option (VarKind × VarName))
    (values : List (PanValue α))
    (structs : StructContext := []) :
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α))) :=
  match destination, values with
  | none, [] => some (locals, globals)
  | none, [_] => some (locals, globals)
  | some (.local, name), [value] =>
      if panValueAssignmentValid structs locals (fun _ => none) .local name value then
        some (updatePanValueMap locals name value, globals)
      else none
  | some (.global, name), [value] =>
      if panValueAssignmentValid structs locals globals .global name value then
        some (locals, updatePanValueMap globals name value)
      else none
  | _, _ => none

abbrev PanValueFfiHandler (α : Type u) :=
  FunName → α → α → α → α →
    (VarName → Option (PanValue α)) →
      Option (VarName → Option (PanValue α))

def evalPanValueExtCall [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext) (handler : PanValueFfiHandler α)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α)
    (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    Option ((VarName → Option (PanValue α)) ×
      (VarName → Option (PanValue α)) × (α → Option (PanValue α))) := do
  let configuration ← evalPanValueExp structs locals globals memory
    baseAddress topAddress bytesInWord configuration (memoryAccess := memoryAccess)
  let configurationLength ← evalPanValueExp structs locals globals memory
    baseAddress topAddress bytesInWord configurationLength (memoryAccess := memoryAccess)
  let array ← evalPanValueExp structs locals globals memory
    baseAddress topAddress bytesInWord array (memoryAccess := memoryAccess)
  let arrayLength ← evalPanValueExp structs locals globals memory
    baseAddress topAddress bytesInWord arrayLength (memoryAccess := memoryAccess)
  let .word configuration := configuration | none
  let .word configurationLength := configurationLength | none
  let .word array := array | none
  let .word arrayLength := arrayLength | none
  let locals ← handler function configuration configurationLength array arrayLength locals
  pure (locals, globals, memory)

/-!
Fuel-bounded structured source semantics for calls, exceptions, and FFI.  This
is the structured-value counterpart of the scalar control-result evaluator in
`Semantics.lean`; unlike the earlier state evaluator, it keeps caller and
callee state separate and propagates matching exception handlers.
-/
mutual
  def evalPanValueCallWithCallsAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (handler : PanValueFfiHandler α)
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        Option (PanValueControlResult α)
    | 0, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, info, function, arguments, memoryAccess, contracts => do
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
        let (parameters, body) ← lookupPanFunction function functions
        if panValueParametersValid structs contracts function values then
          let calleeLocals ← bindPanValueParameters parameters values
          let result ← evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel calleeLocals globals memory body
            (memoryAccess := memoryAccess) (contracts := contracts)
          match result with
          | .normal _ _ _ => none
          | .returned _ calleeGlobals calleeMemory values =>
              -- HOL's Call checks only `shape_of retv <> return_sh`; the
              -- payload-size limit is enforced by the callee `Return`.
              if panValueReturnValid structs contracts function values then
                match info with
                | none => pure (.returned (fun _ => none) calleeGlobals calleeMemory values)
                | some (destination, _) => do
                    let (locals, globals) ← assignPanValueCallResult locals calleeGlobals
                      destination values
                      (structs := structs)
                    pure (.normal locals globals calleeMemory)
              else none
          | .raised _ calleeGlobals calleeMemory exception value =>
              if panValueExceptionValid structs contracts exception value &&
                  panValuePayloadWithinLimit structs value then
                match info with
                | some (_, some (caught, handlerVariable, handlerProgram)) =>
                    if caught == exception then
                      if panValueHandlerValid structs contracts locals handlerVariable value then
                        evalPanValueProgWithCallsAndFfi structs functions handler
                          baseAddress topAddress bytesInWord fuel
                          (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory
                          handlerProgram (memoryAccess := memoryAccess) (contracts := contracts)
                      else none
                    else pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value)
                | _ => pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value)
              else none
          | .broke _ _ _ | .continued _ _ _ => none
        else none
    termination_by fuel _ _ _ _ _ _ => fuel

  def evalPanValueProgWithCallsAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (handler : PanValueFfiHandler α)
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Prog α →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        Option (PanValueControlResult α)
    | 0, _, _, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, .skip, _, _ =>
        some (.normal locals globals memory)
    | fuel + 1, locals, globals, memory,
        .dec name shape value body, memoryAccess, contracts => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let result ← evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel
            (updatePanValueMap locals name value) globals memory body
            (memoryAccess := memoryAccess) (contracts := contracts)
          pure (restorePanValueControlLocal name oldValue result)
        else none
    | _fuel + 1, locals, globals, memory, .assign .local name value, memoryAccess, _contracts => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValueAssignmentValid structs locals globals .local name value then
          pure (.normal (updatePanValueMap locals name value) globals memory)
        else none
    | _fuel + 1, locals, globals, memory, .assign .global name value, memoryAccess, _contracts => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValueAssignmentValid structs locals globals .global name value then
          pure (.normal locals (updatePanValueMap globals name value) memory)
        else none
    | _fuel + 1, locals, globals, memory, .store address value, memoryAccess, _contracts => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let memory ← panValueStoreWithAccess memory bytesInWord address value memoryAccess
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory, .store32 address value, memoryAccess, _contracts => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.store32 access.domain memory bytesInWord address value
        pure (.normal locals globals
          memory)
    | _fuel + 1, locals, globals, memory, .storeByte address value, memoryAccess, _contracts => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.storeByte access.domain memory bytesInWord address value
        pure (.normal locals globals
          memory)
    | fuel + 1, locals, globals, memory, .seq first second, memoryAccess, contracts => do
        let result ← evalPanValueProgWithCallsAndFfi structs functions handler
          baseAddress topAddress bytesInWord fuel locals globals memory first
          (memoryAccess := memoryAccess) (contracts := contracts)
        match result with
        | .normal locals globals memory =>
            evalPanValueProgWithCallsAndFfi structs functions handler
              baseAddress topAddress bytesInWord fuel locals globals memory second
              (memoryAccess := memoryAccess) (contracts := contracts)
        | result => pure result
    | fuel + 1, locals, globals, memory,
        .ite condition thenBranch elseBranch, memoryAccess, contracts => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord condition (memoryAccess := memoryAccess)
        let .word condition := condition | none
        if condition != 0 then
          evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel locals globals memory thenBranch
            (memoryAccess := memoryAccess) (contracts := contracts)
        else
          evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel locals globals memory elseBranch
            (memoryAccess := memoryAccess) (contracts := contracts)
    | fuel + 1, locals, globals, memory, .call info function arguments, memoryAccess, contracts =>
        evalPanValueCallWithCallsAndFfi structs functions handler
          baseAddress topAddress bytesInWord fuel locals globals memory info function arguments
          (memoryAccess := memoryAccess) (contracts := contracts)
    | fuel + 1, locals, globals, memory,
        .decCall name shape function arguments body, memoryAccess, contracts => do
        let oldValue := locals name
        let result ← evalPanValueCallWithCallsAndFfi structs functions handler
          baseAddress topAddress bytesInWord fuel locals globals memory
          none function arguments
          (memoryAccess := memoryAccess) (contracts := contracts)
        match result with
        | .returned _ globals memory [value] =>
            if panShapeMatches (panValueShape structs value) shape then
              let result ← evalPanValueProgWithCallsAndFfi structs functions handler
                baseAddress topAddress bytesInWord fuel
                (updatePanValueMap locals name value) globals memory body
                (memoryAccess := memoryAccess) (contracts := contracts)
              pure (restorePanValueControlLocal name oldValue result)
            else none
        | .raised _ globals memory exception value =>
            pure (.raised (fun _ => none) globals memory exception value)
        | _ => none
    | _fuel + 1, locals, globals, memory,
        .extCall function configuration configurationLength array arrayLength, memoryAccess, _contracts => do
        let (locals, globals, memory) ← evalPanValueExtCall structs handler
          locals globals memory baseAddress topAddress bytesInWord function
          configuration configurationLength array arrayLength (memoryAccess := memoryAccess)
        pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .while conditionExp body, memoryAccess, contracts => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord conditionExp (memoryAccess := memoryAccess)
        let .word conditionValue := condition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory)
        else
          let result ← evalPanValueProgWithCallsAndFfi structs functions handler
            baseAddress topAddress bytesInWord fuel locals globals memory body
            (memoryAccess := memoryAccess) (contracts := contracts)
          match result with
          | .normal locals globals memory | .continued locals globals memory =>
              evalPanValueProgWithCallsAndFfi structs functions handler
                baseAddress topAddress bytesInWord fuel locals globals memory
                (.while conditionExp body) (memoryAccess := memoryAccess)
                (contracts := contracts)
          | .broke locals globals memory => pure (.normal locals globals memory)
          | result => pure result
    | _fuel + 1, locals, globals, memory, .break, _, _ =>
        pure (.broke locals globals memory)
    | _fuel + 1, locals, globals, memory, .continue, _, _ =>
        pure (.continued locals globals memory)
    | _fuel + 1, locals, globals, memory, .raise exception value, memoryAccess, contracts => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValueExceptionValid structs contracts exception value &&
            panValuePayloadWithinLimit structs value then
          pure (.raised (fun _ => none) globals memory exception value)
        else none
    | _fuel + 1, locals, globals, memory, .return value, memoryAccess, _contracts => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValuePayloadWithinLimit structs value then
          pure (.returned (fun _ => none) globals memory [value])
        else none
    | _fuel + 1, locals, globals, memory,
        .shMemLoad size kind name address, memoryAccess, _contracts => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let .word address := address | none
        let value ← match memoryAccess with
          | none => memory address
          | some access => access.sharedRead memory bytesInWord size address
        if panValueSharedLoadValid structs locals globals kind name value then
          match kind with
          | .local => pure (.normal (updatePanValueMap locals name value) globals memory)
          | .global => pure (.normal locals (updatePanValueMap globals name value) memory)
        else none
    | _fuel + 1, locals, globals, memory, .shMemStore size address value, memoryAccess, _contracts => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.sharedStore memory bytesInWord size address (.word value)
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory, .tick, _, _ |
        _fuel + 1, locals, globals, memory, .annot _ _, _, _ =>
        pure (.normal locals globals memory)
    | _, _, _, _, _, _, _ => none
    termination_by fuel _ _ _ _ _ => fuel
end

/-!
The combined source evaluator with an explicit primitive environment.  The
ordinary combined evaluator above is useful for programs without primitive
instructions; this version is the one used when a compiler correctness
statement includes `Primitive`, because primitive calls may occur inside
declarations, loops, callees, or exception handlers.
-/
mutual
  def evalPanValueCallWithPrimitiveCallsAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueAcceleratorFfiHandler α) := none) →
        Option (PanValueControlResult α)
    | 0, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, info, function, arguments, memoryAccess, contracts,
        memoryHandler => do
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
        let (parameters, body) ← lookupPanFunction function functions
        if panValueParametersValid structs contracts function values then
          let calleeLocals ← bindPanValueParameters parameters values
          let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            calleeLocals globals memory body (memoryAccess := memoryAccess)
            (contracts := contracts) (memoryHandler := memoryHandler)
          match result with
          | .normal _ _ _ => none
          | .returned _ calleeGlobals calleeMemory values =>
              -- HOL's Call checks only `shape_of retv <> return_sh`; the
              -- payload-size limit is enforced by the callee `Return`.
              if panValueReturnValid structs contracts function values then
                match info with
                | none => pure (.returned (fun _ => none) calleeGlobals calleeMemory values)
                | some (destination, _) => do
                    let (locals, globals) ← assignPanValueCallResult locals calleeGlobals
                      destination values
                      (structs := structs)
                    pure (.normal locals globals calleeMemory)
              else none
          | .raised _ calleeGlobals calleeMemory exception value =>
              if panValueExceptionValid structs contracts exception value &&
                  panValuePayloadWithinLimit structs value then
                match info with
                | some (_, some (caught, handlerVariable, handlerProgram)) =>
                    if caught == exception then
                      if panValueHandlerValid structs contracts locals handlerVariable value then
                        evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
                          structs functions baseAddress topAddress bytesInWord fuel
                          (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory
                          handlerProgram (memoryAccess := memoryAccess) (contracts := contracts)
                          (memoryHandler := memoryHandler)
                      else none
                    else pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value)
                | _ => pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value)
              else none
          | .broke _ _ _ | .continued _ _ _ => none
        else none
    termination_by fuel _ _ _ _ _ _ => fuel

  def evalPanValueProgWithPrimitiveCallsAndFfi
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Prog α →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueAcceleratorFfiHandler α) := none) →
        Option (PanValueControlResult α)
    | 0, _, _, _, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, .skip, _, _, _ =>
        some (.normal locals globals memory)
    | fuel + 1, locals, globals, memory,
        .dec name shape value body, memoryAccess, contracts, memoryHandler => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            (updatePanValueMap locals name value) globals memory body
            (memoryAccess := memoryAccess) (contracts := contracts)
            (memoryHandler := memoryHandler)
          pure (restorePanValueControlLocal name oldValue result)
        else none
    | _fuel + 1, locals, globals, memory, .assign .local name value, memoryAccess,
        _contracts, _memoryHandler => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValueAssignmentValid structs locals globals .local name value then
          pure (.normal (updatePanValueMap locals name value) globals memory)
        else none
    | _fuel + 1, locals, globals, memory, .assign .global name value, memoryAccess,
        _contracts, _memoryHandler => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValueAssignmentValid structs locals globals .global name value then
          pure (.normal locals (updatePanValueMap globals name value) memory)
        else none
    | _fuel + 1, locals, globals, memory, .primitive name operator arguments, memoryAccess,
        _contracts, _memoryHandler => do
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
        let value ← primitive operator values
        let oldValue ← locals name
        if panShapeMatches (panValueShape structs value)
            (panValueShape structs oldValue) then
          pure (.normal (updatePanValueMap locals name value) globals memory)
        else none
    | _fuel + 1, locals, globals, memory, .store address value, memoryAccess,
        _contracts, _memoryHandler => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let memory ← panValueStoreWithAccess memory bytesInWord address value memoryAccess
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory, .store32 address value, memoryAccess,
        _contracts, _memoryHandler => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.store32 access.domain memory bytesInWord address value
        pure (.normal locals globals
          memory)
    | _fuel + 1, locals, globals, memory, .storeByte address value, memoryAccess,
        _contracts, _memoryHandler => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.storeByte access.domain memory bytesInWord address value
        pure (.normal locals globals
          memory)
    | fuel + 1, locals, globals, memory, .seq first second, memoryAccess, contracts,
        memoryHandler => do
        let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
          structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory first (memoryAccess := memoryAccess)
          (contracts := contracts) (memoryHandler := memoryHandler)
        match result with
        | .normal locals globals memory =>
            evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
              structs functions baseAddress topAddress bytesInWord fuel
              locals globals memory second (memoryAccess := memoryAccess)
              (contracts := contracts) (memoryHandler := memoryHandler)
        | result => pure result
    | fuel + 1, locals, globals, memory,
        .ite condition thenBranch elseBranch, memoryAccess, contracts, memoryHandler => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord condition (memoryAccess := memoryAccess)
        let .word condition := condition | none
        if condition != 0 then
          evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            locals globals memory thenBranch (memoryAccess := memoryAccess)
            (contracts := contracts) (memoryHandler := memoryHandler)
        else
          evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            locals globals memory elseBranch (memoryAccess := memoryAccess)
            (contracts := contracts) (memoryHandler := memoryHandler)
    | fuel + 1, locals, globals, memory, .call info function arguments, memoryAccess, contracts,
        memoryHandler =>
        evalPanValueCallWithPrimitiveCallsAndFfi primitive handler
          structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory info function arguments (memoryAccess := memoryAccess)
          (contracts := contracts) (memoryHandler := memoryHandler)
    | fuel + 1, locals, globals, memory, .decCall name shape function arguments body,
        memoryAccess, contracts, memoryHandler => do
        let oldValue := locals name
        let result ← evalPanValueCallWithPrimitiveCallsAndFfi primitive handler
          structs functions baseAddress topAddress bytesInWord fuel
          locals globals memory none function arguments
          (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
        match result with
        | .returned _ globals memory [value] =>
            if panShapeMatches (panValueShape structs value) shape then
              let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
                structs functions baseAddress topAddress bytesInWord fuel
                (updatePanValueMap locals name value) globals memory body
                (memoryAccess := memoryAccess) (contracts := contracts)
                (memoryHandler := memoryHandler)
              pure (restorePanValueControlLocal name oldValue result)
            else none
        | .raised _ globals memory exception value =>
            pure (.raised (fun _ => none) globals memory exception value)
        | _ => none
    | _fuel + 1, locals, globals, memory,
        .extCall function configuration configurationLength array arrayLength, memoryAccess,
        _contracts, memoryHandler => do
        let values ← evalPanValueExps structs locals globals memory
          baseAddress topAddress bytesInWord
          [configuration, configurationLength, array, arrayLength]
          (memoryAccess := memoryAccess)
        let [.word configuration, .word configurationLength, .word array, .word arrayLength] := values |
          none
        match memoryHandler with
        | some memoryHandler =>
            let (locals, memory) ← memoryHandler function configuration configurationLength
              array arrayLength locals memory
            pure (.normal locals globals memory)
        | none =>
            let locals ← handler function configuration configurationLength array arrayLength locals
            pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .while conditionExp body, memoryAccess, contracts,
        memoryHandler => do
        let condition ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord conditionExp (memoryAccess := memoryAccess)
        let .word conditionValue := condition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory)
        else
          let result ← evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            locals globals memory body (memoryAccess := memoryAccess)
            (contracts := contracts) (memoryHandler := memoryHandler)
          match result with
          | .normal locals globals memory | .continued locals globals memory =>
              evalPanValueProgWithPrimitiveCallsAndFfi primitive handler
                structs functions baseAddress topAddress bytesInWord fuel
                locals globals memory (.while conditionExp body)
                (memoryAccess := memoryAccess) (contracts := contracts)
                (memoryHandler := memoryHandler)
          | .broke locals globals memory => pure (.normal locals globals memory)
          | result => pure result
    | _fuel + 1, locals, globals, memory, .break, _, _, _ =>
        pure (.broke locals globals memory)
    | _fuel + 1, locals, globals, memory, .continue, _, _, _ =>
        pure (.continued locals globals memory)
    | _fuel + 1, locals, globals, memory, .raise exception value, memoryAccess, contracts,
        _memoryHandler => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValueExceptionValid structs contracts exception value &&
            panValuePayloadWithinLimit structs value then
          pure (.raised (fun _ => none) globals memory exception value)
        else none
    | _fuel + 1, locals, globals, memory, .return value, memoryAccess, _contracts,
        _memoryHandler => do
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValuePayloadWithinLimit structs value then
          pure (.returned (fun _ => none) globals memory [value])
        else none
    | _fuel + 1, locals, globals, memory,
        .shMemLoad size kind name address, memoryAccess, _contracts, _memoryHandler => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let .word address := address | none
        let value ← match memoryAccess with
          | none => memory address
          | some access => access.sharedRead memory bytesInWord size address
        if panValueSharedLoadValid structs locals globals kind name value then
          match kind with
          | .local => pure (.normal (updatePanValueMap locals name value) globals memory)
          | .global => pure (.normal locals (updatePanValueMap globals name value) memory)
        else none
    | _fuel + 1, locals, globals, memory, .shMemStore size address value, memoryAccess,
        _contracts, _memoryHandler => do
        let address ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExp structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.sharedStore memory bytesInWord size address (.word value)
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory,
        .tick, _, _, _ | _fuel + 1, locals, globals, memory, .annot _ _, _, _, _ =>
        pure (.normal locals globals memory)
    termination_by fuel _ _ _ _ _ => fuel
end

/-! Target-word structured calls/FFI.  This is the target-width counterpart
    of `evalPanValueProgWithPrimitiveCallsAndFfi`: every expression crossing a
    call, declaration, control-flow, or FFI boundary is evaluated with the
    complete Cake `word_sh` semantics.  The older evaluator above remains the
    compatibility entrypoint for abstract proofs. -/
mutual
  def evalPanValueCallWithPrimitiveCallsAndFfiFull
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Option (Option (VarKind × VarName) ×
          Option (ExceptionId × VarName × Prog α)) → FunName → List (Exp α) →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueAcceleratorFfiHandler α) := none) →
        Option (PanValueControlResult α)
    | 0, _, _, _, _, _, _, _, _, _ => none
    | fuel + 1, locals, globals, memory, info, function, arguments, memoryAccess,
        contracts, memoryHandler => do
        let values ← evalPanValueExpsFull structs locals globals memory
          baseAddress topAddress bytesInWord arguments
          (memoryAccess := memoryAccess)
        let (parameters, body) ← lookupPanFunction function functions
        if panValueParametersValid structs contracts function values then
          let calleeLocals ← bindPanValueParameters parameters values
          let result ← evalPanValueProgWithPrimitiveCallsAndFfiFull primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            calleeLocals globals memory body (memoryAccess := memoryAccess)
            (contracts := contracts) (memoryHandler := memoryHandler)
          match result with
          | .normal _ _ _ => none
          | .returned _ calleeGlobals calleeMemory values =>
              -- HOL's Call checks only `shape_of retv <> return_sh`; the
              -- payload-size limit is enforced by the callee `Return`.
              if panValueReturnValid structs contracts function values then
                match info with
                | none => pure (.returned (fun _ => none) calleeGlobals calleeMemory values)
                | some (destination, _) => do
                    let (locals, globals) ← assignPanValueCallResult locals calleeGlobals
                      destination values (structs := structs)
                    pure (.normal locals globals calleeMemory)
              else none
          | .raised _ calleeGlobals calleeMemory exception value =>
              if panValueExceptionValid structs contracts exception value &&
                  panValuePayloadWithinLimit structs value then
                match info with
                | some (_, some (caught, handlerVariable, handlerProgram)) =>
                    if caught == exception then
                      if panValueHandlerValid structs contracts locals handlerVariable value then
                        evalPanValueProgWithPrimitiveCallsAndFfiFull primitive handler
                          structs functions baseAddress topAddress bytesInWord fuel
                          (updatePanValueMap locals handlerVariable value) calleeGlobals calleeMemory
                          handlerProgram (memoryAccess := memoryAccess) (contracts := contracts)
                          (memoryHandler := memoryHandler)
                      else none
                    else pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value)
                | _ => pure (.raised (fun _ => none) calleeGlobals calleeMemory exception value)
              else none
          | .broke _ _ _ | .continued _ _ _ => none
        else none
    termination_by fuel _ _ _ _ _ _ => fuel

  def evalPanValueProgWithPrimitiveCallsAndFfiFull
      [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
      [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
      [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
      [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
      (primitive : PanPrimitiveHandler α) (handler : PanValueFfiHandler α)
      (structs : StructContext)
      (functions : List (FunName × List VarName × Prog α))
      (baseAddress topAddress bytesInWord : α) :
      Nat → (VarName → Option (PanValue α)) →
        (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
        Prog α →
        (memoryAccess : Option (PanValueMemoryAccess α) := none) →
        (contracts : Option PanValueCallContracts := none) →
        (memoryHandler : Option (PanValueAcceleratorFfiHandler α) := none) →
        Option (PanValueControlResult α)
    | 0, _, _, _, _, _, _, _ => none
    | _fuel + 1, locals, globals, memory, .skip, _, _, _ =>
        some (.normal locals globals memory)
    | fuel + 1, locals, globals, memory,
        .dec name shape value body, memoryAccess, contracts, memoryHandler => do
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panShapeMatches (panValueShape structs value) shape then
          let oldValue := locals name
          let result ← evalPanValueProgWithPrimitiveCallsAndFfiFull primitive handler
            structs functions baseAddress topAddress bytesInWord fuel
            (updatePanValueMap locals name value) globals memory body
            (memoryAccess := memoryAccess) (contracts := contracts)
            (memoryHandler := memoryHandler)
          pure (restorePanValueControlLocal name oldValue result)
        else none
    | _fuel + 1, locals, globals, memory, .assign .local name value, memoryAccess,
        _contracts, _memoryHandler => do
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValueAssignmentValid structs locals globals .local name value then
          pure (.normal (updatePanValueMap locals name value) globals memory)
        else none
    | _fuel + 1, locals, globals, memory, .assign .global name value, memoryAccess,
        _contracts, _memoryHandler => do
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValueAssignmentValid structs locals globals .global name value then
          pure (.normal locals (updatePanValueMap globals name value) memory)
        else none
    | _fuel + 1, locals, globals, memory, .primitive name operator arguments, memoryAccess,
        _contracts, _memoryHandler => do
        let values ← evalPanValueExpsFull structs locals globals memory
          baseAddress topAddress bytesInWord arguments (memoryAccess := memoryAccess)
        let value ← primitive operator values
        let oldValue ← locals name
        if panShapeMatches (panValueShape structs value) (panValueShape structs oldValue) then
          pure (.normal (updatePanValueMap locals name value) globals memory)
        else none
    | _fuel + 1, locals, globals, memory, .store address value, memoryAccess,
        _contracts, _memoryHandler => do
        let address ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let memory ← panValueStoreWithAccess memory bytesInWord address value memoryAccess
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory, .store32 address value, memoryAccess,
        _contracts, _memoryHandler => do
        let address ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.store32 access.domain memory bytesInWord address value
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory, .storeByte address value, memoryAccess,
        _contracts, _memoryHandler => do
        let address ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.storeByte access.domain memory bytesInWord address value
        pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .seq first second, memoryAccess, contracts,
        memoryHandler => do
        let result ← evalPanValueProgWithPrimitiveCallsAndFfiFull primitive handler
          structs functions baseAddress topAddress bytesInWord fuel locals globals memory first
          (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler)
        match result with
        | .normal locals globals memory =>
            evalPanValueProgWithPrimitiveCallsAndFfiFull primitive handler
              structs functions baseAddress topAddress bytesInWord fuel locals globals memory second
              (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler)
        | result => pure result
    | fuel + 1, locals, globals, memory,
        .ite condition thenBranch elseBranch, memoryAccess, contracts, memoryHandler => do
        let condition ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord condition (memoryAccess := memoryAccess)
        let .word condition := condition | none
        if condition != 0 then
          evalPanValueProgWithPrimitiveCallsAndFfiFull primitive handler
            structs functions baseAddress topAddress bytesInWord fuel locals globals memory thenBranch
            (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler)
        else
          evalPanValueProgWithPrimitiveCallsAndFfiFull primitive handler
            structs functions baseAddress topAddress bytesInWord fuel locals globals memory elseBranch
            (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler)
    | fuel + 1, locals, globals, memory, .call info function arguments, memoryAccess, contracts,
        memoryHandler =>
        evalPanValueCallWithPrimitiveCallsAndFfiFull primitive handler
          structs functions baseAddress topAddress bytesInWord fuel locals globals memory info function
          arguments (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
    | fuel + 1, locals, globals, memory, .decCall name shape function arguments body,
        memoryAccess, contracts, memoryHandler => do
        let oldValue := locals name
        let result ← evalPanValueCallWithPrimitiveCallsAndFfiFull primitive handler
          structs functions baseAddress topAddress bytesInWord fuel locals globals memory none function
          arguments (memoryAccess := memoryAccess) (contracts := contracts)
          (memoryHandler := memoryHandler)
        match result with
        | .returned _ globals memory [value] =>
            if panShapeMatches (panValueShape structs value) shape then
              let result ← evalPanValueProgWithPrimitiveCallsAndFfiFull primitive handler
                structs functions baseAddress topAddress bytesInWord fuel
                (updatePanValueMap locals name value) globals memory body
                (memoryAccess := memoryAccess) (contracts := contracts)
                (memoryHandler := memoryHandler)
              pure (restorePanValueControlLocal name oldValue result)
            else none
        | .raised _ globals memory exception value =>
            pure (.raised (fun _ => none) globals memory exception value)
        | _ => none
    | _fuel + 1, locals, globals, memory,
        .extCall function configuration configurationLength array arrayLength, memoryAccess,
        _contracts, memoryHandler => do
        let values ← evalPanValueExpsFull structs locals globals memory
          baseAddress topAddress bytesInWord
          [configuration, configurationLength, array, arrayLength]
          (memoryAccess := memoryAccess)
        let [.word configuration, .word configurationLength, .word array, .word arrayLength] := values |
          none
        match memoryHandler with
        | some memoryHandler =>
            let (locals, memory) ← memoryHandler function configuration configurationLength
              array arrayLength locals memory
            pure (.normal locals globals memory)
        | none =>
            let locals ← handler function configuration configurationLength array arrayLength locals
            pure (.normal locals globals memory)
    | fuel + 1, locals, globals, memory, .while conditionExp body, memoryAccess, contracts,
        memoryHandler => do
        let condition ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord conditionExp (memoryAccess := memoryAccess)
        let .word conditionValue := condition | none
        if conditionValue == 0 then
          pure (.normal locals globals memory)
        else
          let result ← evalPanValueProgWithPrimitiveCallsAndFfiFull primitive handler
            structs functions baseAddress topAddress bytesInWord fuel locals globals memory body
            (memoryAccess := memoryAccess) (contracts := contracts) (memoryHandler := memoryHandler)
          match result with
          | .normal locals globals memory | .continued locals globals memory =>
              evalPanValueProgWithPrimitiveCallsAndFfiFull primitive handler
                structs functions baseAddress topAddress bytesInWord fuel locals globals memory
                (.while conditionExp body) (memoryAccess := memoryAccess) (contracts := contracts)
                (memoryHandler := memoryHandler)
          | .broke locals globals memory => pure (.normal locals globals memory)
          | result => pure result
    | _fuel + 1, locals, globals, memory, .break, _, _, _ =>
        pure (.broke locals globals memory)
    | _fuel + 1, locals, globals, memory, .continue, _, _, _ =>
        pure (.continued locals globals memory)
    | _fuel + 1, locals, globals, memory, .raise exception value, memoryAccess, contracts,
        _memoryHandler => do
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValueExceptionValid structs contracts exception value &&
            panValuePayloadWithinLimit structs value then
          pure (.raised (fun _ => none) globals memory exception value)
        else none
    | _fuel + 1, locals, globals, memory, .return value, memoryAccess, _contracts,
        _memoryHandler => do
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        if panValuePayloadWithinLimit structs value then
          pure (.returned (fun _ => none) globals memory [value])
        else none
    | _fuel + 1, locals, globals, memory,
        .shMemLoad size kind name address, memoryAccess, _contracts, _memoryHandler => do
        let address ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let .word address := address | none
        let value ← match memoryAccess with
          | none => memory address
          | some access => access.sharedRead memory bytesInWord size address
        if panValueSharedLoadValid structs locals globals kind name value then
          match kind with
          | .local => pure (.normal (updatePanValueMap locals name value) globals memory)
          | .global => pure (.normal locals (updatePanValueMap globals name value) memory)
        else none
    | _fuel + 1, locals, globals, memory, .shMemStore size address value, memoryAccess,
        _contracts, _memoryHandler => do
        let address ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord address (memoryAccess := memoryAccess)
        let value ← evalPanValueExpFull structs locals globals memory
          baseAddress topAddress bytesInWord value (memoryAccess := memoryAccess)
        let .word address := address | none
        let .word value := value | none
        let memory ← match memoryAccess with
          | none => some (updatePanValueMemory memory address (.word value))
          | some access => access.sharedStore memory bytesInWord size address (.word value)
        pure (.normal locals globals memory)
    | _fuel + 1, locals, globals, memory,
        .tick, _, _, _ | _fuel + 1, locals, globals, memory, .annot _ _, _, _, _ =>
        pure (.normal locals globals memory)
    termination_by fuel _ _ _ _ _ => fuel
end

/-! Target-word calls/FFI boundary without primitive operations.  This is the
    full counterpart of `evalPanValueProgWithCallsAndFfi`: use the already
    Cake-faithful primitive/call evaluator with an empty primitive handler so
    target-word callers do not fall back to the partial `evalPanShift` path. -/
def evalPanValueProgWithCallsAndFfiFull
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [PanShiftWidth α] [ArithmeticShiftRight α] [RotateRightOp α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (handler : PanValueFfiHandler α)
    (baseAddress topAddress bytesInWord : α) :
    Nat → (VarName → Option (PanValue α)) →
      (VarName → Option (PanValue α)) → (α → Option (PanValue α)) →
      Prog α →
    (memoryAccess : Option (PanValueMemoryAccess α) := none) →
    (contracts : Option PanValueCallContracts := none) →
      Option (PanValueControlResult α) := by
  intro fuel locals globals memory program memoryAccess contracts
  exact evalPanValueProgWithPrimitiveCallsAndFfiFull
    (fun _ _ => none) handler structs functions
    baseAddress topAddress bytesInWord fuel locals globals memory program
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := none)

theorem evalPanValueExp_rField_word
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (structs : StructContext)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α))
    (baseAddress topAddress bytesInWord : α) (left right : α) :
    evalPanValueExp structs locals globals memory baseAddress topAddress bytesInWord
      (.rField 1 (.rStruct [.const left, .const right])) = some (.word right) := by
  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps]

end Flapjack
