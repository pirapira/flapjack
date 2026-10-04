import Lean

/-!
# `@[hol ...]`: cross-reference to the original HOL4 declaration

Every Lean theorem or definition that ports a declaration from the CakeML/HOL4
development carries

    @[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"]

naming the HOL source file (repository-relative, inside the `cakeml`
submodule) and the exact HOL declaration name (`Theorem`, `Triviality`,
`Definition`, `Datatype`, ...). When a script declares the same name twice,
append its source line, e.g. `@[hol "...Script.sml" "name" 123]`. HOL4
library declarations are cited inside the pinned upstream `HOL` submodule, e.g.
`@[hol "HOL/src/list/src/listScript.sml" "EL_def"]`; `scripts/check-hol-refs.py`
accepts such a path only when the recorded gitlink, the checkout and the cited
blob are all the pinned commit. The older per-file `hol4/` snapshots remain
accepted during migration. The
experimental `list_as_array` qualifier records HOL list fields represented by
Lean arrays, e.g. `@[hol "...Script.sml" "dec_deg_def"
(list_as_array := [degrees])]`. It does not authorize a qualified tag until a
checked same-module representation lemma and checker gate exist. The
`names_as_string` qualifier records a narrowly reviewed HOL `mlstring` name
represented by Lean `String`. Its identifiers can name parameters or other
uses, not just structure fields, e.g.
`@[hol "...Script.sml" "fresh_name_def" (names_as_string := [name])]`.
The theorem-map reviewer classifies each identifier as equality/map-key-only
or byte-observable. Byte-observable identifiers are the explicit subset
`(names_as_string_boundary := [name])` and require a same-module checked
`holMlStringWitness_<LeanDeclaration>` whose conclusion establishes
`NameRanged` for the declaration's output. The witness may require
`NameRanged` input premises; the checker verifies only its name/result shape,
while Lean checks its proof and source review checks that the executed path
supplies its premises.
The `fmap_as_finite_support` qualifier records structure fields whose HOL
`|->` finite map is represented by the reviewed canonical Lean translation
`HolFiniteMapExact` (a `lookup` function together with a `finiteSupport`
proposition). It names fields, e.g.
`@[hol "...Script.sml" "set_var_def" (fmap_as_finite_support := [locals])]`.
The checker requires each named field to be declared in a same-module
structure, to actually use the `HolFiniteMapExact` carrier (a raw
`α → Option β` map is ineligible), and requires the same-module canonical
witness `holFmapAsFiniteSupportWitness` (`toExact`/`ofExact` roundtrips).
Extensionality is proved separately by `HolFiniteMapExact.ext`. This is a
representation statement only and
does not authorize changed quantifiers, hypotheses, conclusions, `BEq` side
conditions, or word-model differences.
It does not authorize any other carrier, statement, or behavior difference.
Qualified declarations remain subject to the checker and reviewed manifest.
The `fmap_as_finite_support_parameters` qualifier records explicitly named
standalone HOL `|->` input binders represented directly as
`HolFiniteMapExact`, for declarations whose result is not a finite map. Each
listed identifier must be an actual input binder of that type and must have a
same-module checked `holFmapAsFiniteSupportParamWitness_<declaration>_<binder>`
roundtrip through lookup and finite-support evidence. This is distinct from
both field-owned carriers and the result-map qualifier; source review must
still preserve HOL binder order, hypotheses, and conclusions.
The `fmap_as_finite_support_existentials` qualifier records named existential
finite-map binders represented as `HolFiniteMapExact`. Each listed binder
must be an explicit existential at that carrier and have a same-module
`holFmapAsFiniteSupportExistentialWitness_<declaration>_<binder>` roundtrip
through lookup and finite-support evidence. It is intended for HOL relations
whose statement existentially quantifies a finite map; it does not alter the
quantifier or witness role.
The `fmap_as_finite_support_relation` qualifier is the multi-owner form for a
HOL relation whose finite maps come from several carrier structures. It lists
`Owner.field` entries, requires each field to use `HolFiniteMapExact` and each
owner to appear in the tagged statement, and requires one same-module checked
`holFmapAsFiniteSupportRelationWitness_<Owner>` per owner. Each witness must
state a real `toX`/`ofX` roundtrip with that owner's broad counterpart. The
qualifier records only the finite-map carrier translations; the relation's
quantifiers, hypotheses, conclusions, and lookup semantics need their own
source comparison.
The `words_as_type_indexed_bitvec` qualifier records the candidate standard
translation of HOL's type-indexed `'a word` (dimension `dimindex (:α)`) to
Lean's positive-width `BitVec width`, and of HOL's `'ffi ffi_state` to a
universe-0 Lean host type. It is a translation statement only: a tagged
declaration must retain `[NeZero width]` (the discharge of HOL's
`dimindex (:α) ≥ 1`), must not restate positivity as an extra hypothesis, and
must bind the FFI host type as `{σ : Type}` (or `Type 0`) without a
universe-level variable or `Sort` when it mentions `HolFfiState`. Every word
dimension in scope (not only the first) must be bound at its own `Nat` width
with its own `[NeZero <id>]` discharge; a literal `BitVec 0` and a `[NeZero 0]`
discharge are rejected as non-positive. The signature need not pronounce
`BitVec` directly when it is
stated over a reviewed width-indexed carrier (declared locally or reached
through imports) whose own header carries `[NeZero <width>]` for its width
parameter and some field of that SAME owner mentions `BitVec <width>` with that
same width identifier; the carrier is resolved from its
declaration, never accepted by name alone, and its `[NeZero <width>]` discharge
and `BitVec <width>` field must belong to the SAME owning declaration and the
same width identifier (a header with `[NeZero other]` or a field such as
`BitVec 5 × HolWordLab width` does not qualify; a name with
several owners is rejected as ambiguous unless the signature uniquely resolves
it). It changes no quantifier,
hypothesis, side condition, or
conclusion, and it requires no cross-assistant agreement theorem. When the
declaration also carries `fmap_as_finite_support`, use the combined manifest
status `reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec`; when it
also carries `fmap_as_finite_support_relation`, use
`reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec` (both
qualifiers required together in either case). The
reference checker reads only the tagged declaration's signature (not its proof
or body) and records both qualifiers.
The separate `word_dimension_as_width := width` qualifier is only for a
word-free HOL type dimension used numerically: it records the named explicit
`Nat` width and its own `[NeZero width]` discharge. It cannot be combined with
`words_as_type_indexed_bitvec`, and, like every qualifier, it permits no change
to the HOL declaration's equation or behavior.
The attribute is inert for the kernel; it exists so that

* a reader can find the original statement without a lookup table, whatever
  the Lean name is;
* `scripts/check-hol-refs.py` can verify that the cited file and declaration
  exist, and emit the HOL-to-Lean mapping;
* `#hol_refs` can list every cross-referenced declaration in scope.

When one HOL theorem is split across several Lean declarations (for example,
one per `evaluate` case of `pc_compile_correct`), every piece carries the same
attribute.  The rules for using it are in `AGENTS.md`.
-/

namespace Flapjack

/-- Location of the original HOL4 declaration. -/
structure HolRef where
  /-- Repository-relative path of the HOL script (CakeML, or the explicitly
      allowed byte-pinned external HOL4 snapshot), e.g.
      `cakeml/pancake/proofs/pan_to_crepProofScript.sml`. -/
  path : String
  /-- Exact HOL declaration name, e.g. `pc_compile_correct`. -/
  name : String
  /-- Source line, required when the HOL script declares this name more than once. -/
  line? : Option Nat := none
  /-- HOL list fields represented by arrays in this Lean port.  An empty array
      denotes an exact port; qualified ports require a checked representation
      lemma before the tag may be applied. Each named field must be declared in
      a same-module structure and have a checked theorem named
      `holListArrayWitness_<field>` whose conclusion relates that field to a HOL
      list through `RepresentsHOLNodeList`, without assuming that relation in
      the witness premises. The reference checker validates this shape; it does
      not independently prove source-to-Lean semantic correspondence. -/
  listAsArray : Array String := #[]
  /-- Lean identifiers whose `String` carrier represents HOL `mlstring` names.
      Identifiers need not be structure fields. The manifest reviewer
      classifies each as equality/map-key-only or byte-observable. For a
      byte-observable identifier, a same-module
      `holMlStringWitness_<LeanDeclaration>` theorem must establish `NameRanged`
      for the declaration's output; input `NameRanged` premises are allowed.
      The checker checks only the witness name/result shape, not source
      correspondence or executed-path premise discharge. -/
  namesAsString : Array String := #[]
  /-- Subset of `namesAsString` identifiers classified by source review as
      byte-observable; these require a same-module checked witness. -/
  namesAsStringBoundary : Array String := #[]
  /-- Structure fields whose HOL `|->` finite-map carrier is represented by the
      reviewed canonical translation `HolFiniteMapExact`. Each named field must
      be a field of a same-module structure whose declared type uses
      `HolFiniteMapExact` (a raw `α → Option β` map is ineligible), and the
      module must contain the checked canonical witness
      `holFmapAsFiniteSupportWitness`. This is a representation statement only;
      it does not authorize changed hypotheses, results, `BEq` side conditions,
      or word-model differences. -/
  fmapAsFiniteSupport : Array String := #[]
  /-- A type abbreviation for a HOL function type whose argument and result
      contain canonical `HolFiniteMapExact` carriers at the named product
      positions (`argument_N` / `result_N`, one-based). The checker verifies
      the complete function/product shape, both selected carriers, and that no
      other finite-map carrier occurs in the alias. This records the pointwise
      canonical finite-map translation under the function space; source review
      must still compare the surrounding HOL function domain/codomain and all
      other type components. -/
  fmapAsFiniteSupportFunction : Array String := #[]
  /-- A HOL function whose named argument and result product slots are both
      canonical `HolFiniteMapExact` carriers but have distinct map types.
      This qualifier requires a same-module
      `holFmapAsFiniteSupportHeterogeneousFunctionWitness_<decl>` theorem. The
      witness must compare the `Option.map` result projection with an
      independent raw lookup using the canonical input map's `.lookup`, over
      exactly the target operation's explicit inputs. It does not imply the
      input and result maps share a key/value type. -/
  fmapAsFiniteSupportHeterogeneousFunction : Array String := #[]
  /-- Standalone declarations (definitions or theorems) whose own input or
      result carrier is the reviewed canonical `HolFiniteMapExact` translation,
      rather than a structure field. Distinct from `fmapAsFiniteSupport`, which
      names fields of an owning carrier structure. The module must contain a
      checked canonical witness of lookup-level correspondence to the HOL
      finite-map operation/result. This is a representation statement only; it
      does not authorize changed hypotheses, results, or word-model differences. -/
  fmapAsFiniteSupportResult : Bool := false
  /-- Named standalone input binders represented by HolFiniteMapExact. Each
      parameter must be explicitly bound at that carrier and have a same-module
      `holFmapAsFiniteSupportParamWitness_<declaration>_<parameter>` roundtrip
      through its lookup function and finite-support proof. This qualifier is
      for consumed map inputs whose declaration result is not a map; it is
      distinct from the map-valued result qualifier. -/
  fmapAsFiniteSupportParameters : Array String := #[]
  /-- Explicit imported map-result producers observed by this declaration's type.
      Every producer must already carry `fmap_as_finite_support_result`, return
      `HolFiniteMapExact`, have its checked same-module result witness, and have
      a reviewed result-qualifier manifest record. The observer manifest names
      exactly the same producers with a separate source-comparison note and
      `reviewed_fmap_as_finite_support_result_observations` status. This records
      only that existing canonical map translation; it permits no changed
      evaluator, carrier, quantifiers, premises or conclusions. Other
      representation qualifiers cannot be combined with this narrow qualifier.
      The syntactic checker does not prove cross-language equivalence; source
      review must compare the complete observer, not infer it from the producer. -/
  fmapAsFiniteSupportResultObservations : Array String := #[]
  /-- Existentially bound standalone finite maps represented by
      HolFiniteMapExact. Each named binder must be an explicit existential at
      that carrier and have a same-module
      `holFmapAsFiniteSupportExistentialWitness_<declaration>_<binder>` lookup
      and finite-support roundtrip. This records only the map representation;
      it does not change the existential's scope or role. -/
  fmapAsFiniteSupportExistentials : Array String := #[]
  /-- Multi-carrier finite-map relation entries, each written `Carrier.field`
      or, for a standalone map parameter with no owning carrier, a bare
      parameter name. Used when a relation spans more than one carrier
      structure (for example a PanSem state and a CrepSem state), which the
      single-owner `fmapAsFiniteSupport` qualifier cannot express. Every named
      carrier must be a structure declared in the same module or reachable
      through its imports, the field must use `HolFiniteMapExact`, the tagged
      declaration must name every carrier it relates, and the module must
      contain a checked carrier-specific witness
      `holFmapAsFiniteSupportRelationWitness_<carrier>` stating a real
      `toX`/`ofX` roundtrip with its broad counterpart. A bare parameter entry
      requires the tagged declaration to bind that name at a
      `HolFiniteMapExact` type and needs no carrier witness. This does not
      relax the single-owner gate. -/
  fmapAsFiniteSupportRelation : Array (String × String) := #[]
  /-- Theorem-level finite-map equalities: the tagged declaration's conclusion
      is a conjunction of `HolFiniteMapExact` equalities, each corresponding to a
      HOL finite-map equality. The module must contain, for every conjunct, a
      checked lookup-level witness
      `holFmapAsFiniteSupportEqualityWitness_<decl>_<index>`; the witnesses must
      not mention the tagged theorem, so an ignored-proof/threaded-argument
      witness is rejected. This is a representation statement only; it does not
      authorize changed hypotheses, conclusions, side conditions, or word-model
      differences. -/
  fmapAsFiniteSupportEqualities : Bool := false
  /-- A single theorem-level finite-map equality: the tagged declaration's
      conclusion is exactly one whole `HolFiniteMapExact` equality (not a
      conjunction and not an iff). The module must contain a checked,
      unconditional lookup-level witness
      `holFmapAsFiniteSupportEqualityWitness_<decl>` whose two sides are exactly
      the tagged conclusion's two sides at one universally bound key; the
      witness must not mention the tagged theorem. This is a representation
      statement only; it does not authorize changed hypotheses, conclusions,
      side conditions, or word-model differences. -/
  fmapAsFiniteSupportEquality : Bool := false
  /-- The candidate standard translation of HOL's type-indexed `'a word` (with
      dimension `dimindex (:α)`) to Lean's positive-width `BitVec width` and of
      HOL's `'ffi ffi_state` to a universe-0 Lean host type. A declaration
      carrying this qualifier must still name `BitVec`, must retain `[NeZero
      width]` as the discharge of HOL's `dimindex (:α) ≥ 1`, must not restate
      word-dimension positivity as an extra hypothesis, and (when it mentions
      the FFI carrier `HolFfiState`) must bind the host type at a `Type`
      universe without a universe-level variable. The qualifier records a
      conventional data-structure translation only; it authorizes no change to
      quantifiers, hypotheses, side conditions, or conclusions, and no
      cross-assistant agreement theorem is required. -/
  wordsAsTypeIndexedBitvec : Bool := false
  /-- Word-free type-dimension translation: HOL `dimindex (:'a)` is named by
      an explicit Nat width parameter when the declaration uses the dimension
      only as a Nat value, without carrying a word. The checker requires the
      named binder to be Nat and retain its own `[NeZero width]` discharge;
      source review compares how the dimension is used in both bodies. -/
  wordDimensionAsWidth : Option String := none
  /-- Two independent word-free HOL type dimensions, retained as two distinct
      explicit Nat binders with separate NeZero instances. This records only
      numeric dimindex/dimword translation, not word or real approximation. -/
  wordDimensionsAsWidths : Array String := #[]
  /-- Reviewed binary64 real-rendering translation: HOL `real` values inside
      the HOL standard-library IEEE rounding specification (`binary_ieee`,
      `machine_ieee`) are represented by Lean `Rat` when the real is rational
      and by the rational cut of `sqrt r` for `fp64_sqrt`
      (`Flapjack/Misc/BinaryIeee*.lean`, `docs/SOUNDNESS.md` item 8).  It
      records only that representation; it authorizes no change to the HOL
      declaration's clauses, hypotheses or conclusions, and the agreement
      with HOL's real-number specification remains the documented external
      assumption. -/
  realsAsRationalCuts : Bool := false
  deriving Inhabited, Repr, BEq

open Lean Meta

declare_syntax_cat holQualifier
syntax "(" "list_as_array" ":=" "[" ident,+ "]" ")" : holQualifier
syntax "(" "names_as_string" ":=" "[" ident,+ "]" ")" : holQualifier
syntax "(" "names_as_string_boundary" ":=" "[" ident,+ "]" ")" : holQualifier
syntax "(" "fmap_as_finite_support" ":=" "[" ident,+ "]" ")" : holQualifier
syntax "(" "fmap_as_finite_support_function" ":=" "[" ident,+ "]" ")" : holQualifier
syntax "(" "fmap_as_finite_support_heterogeneous_function" ":=" "[" ident,+ "]" ")" : holQualifier
syntax "(" "fmap_as_finite_support_result" ")" : holQualifier
syntax "(" "fmap_as_finite_support_parameters" ":=" "[" ident,+ "]" ")" : holQualifier
syntax "(" "fmap_as_finite_support_result_observations" ":=" "[" ident,+ "]" ")" : holQualifier
syntax "(" "fmap_as_finite_support_existentials" ":=" "[" ident,+ "]" ")" : holQualifier
syntax "(" "fmap_as_finite_support_relation" ":=" "[" ident,* "]" ")" : holQualifier
syntax "(" "fmap_as_finite_support_equalities" ")" : holQualifier
syntax "(" "fmap_as_finite_support_equality" ")" : holQualifier
syntax "(" "words_as_type_indexed_bitvec" ")" : holQualifier
syntax "(" "word_dimension_as_width" ":=" ident ")" : holQualifier
syntax "(" "word_dimensions_as_widths" ":=" "[" ident,* "]" ")" : holQualifier
syntax "(" "reals_as_rational_cuts" ")" : holQualifier
syntax (name := hol) "hol " str str (num)? holQualifier* : attr

private def checkedHolRef (path name : String) (line? : Option Nat := none)
    (listAsArray namesAsString namesAsStringBoundary fmapAsFiniteSupport : Array String := #[])
    (fmapAsFiniteSupportResult : Bool := false)
    (fmapAsFiniteSupportFunction : Array String := #[])
    (fmapAsFiniteSupportHeterogeneousFunction : Array String := #[])
    (fmapAsFiniteSupportParameters : Array String := #[])
    (fmapAsFiniteSupportExistentials : Array String := #[])
    (fmapAsFiniteSupportRelation : Array (String × String) := #[])
    (fmapAsFiniteSupportEqualities : Bool := false)
    (fmapAsFiniteSupportEquality : Bool := false)
    (wordsAsTypeIndexedBitvec : Bool := false)
    (wordDimensionAsWidth : Option String := none)
    (realsAsRationalCuts : Bool := false)
    (fmapAsFiniteSupportResultObservations : Array String := #[])
    (wordDimensionsAsWidths : Array String := #[]) : CoreM HolRef := do
  unless (path.startsWith "cakeml/" && path.endsWith ".sml" ||
      -- Pinned upstream HOL submodule; `scripts/check-hol-refs.py` verifies the
      -- gitlink, checkout commit and blob of every cited `HOL/...` file.
      path.startsWith "HOL/" && path.endsWith ".sml" ||
      path == "hol4/src/finite_maps/sptreeScript.sml" ||
      path == "hol4/src/coretypes/optionScript.sml" ||
      path == "hol4/src/coalgebras/llistScript.sml" ||
      path == "hol4/src/n-bit/fcpScript.sml" ||
      path == "hol4/examples/pl-semantics/lprefix_lub/lprefix_lubScript.sml") &&
      (path.splitOn "/").all (fun part => part != "" && part != "." && part != "..") do
    throwError "@[hol]: path must be a safe `cakeml/...Script.sml` or `HOL/...Script.sml` file or a pinned HOL4 snapshot, got {path}"
  if name.isEmpty || name.any Char.isWhitespace then
    throwError "@[hol]: declaration name must be a single HOL identifier, got {repr name}"
  if listAsArray.toList.eraseDups.length != listAsArray.size then
    throwError "@[hol]: list_as_array fields must be distinct"
  if namesAsString.toList.eraseDups.length != namesAsString.size then
    throwError "@[hol]: names_as_string identifiers must be distinct"
  if namesAsStringBoundary.toList.eraseDups.length != namesAsStringBoundary.size then
    throwError "@[hol]: names_as_string_boundary identifiers must be distinct"
  unless namesAsStringBoundary.all namesAsString.contains do
    throwError "@[hol]: names_as_string_boundary identifiers must also appear in names_as_string"
  if fmapAsFiniteSupport.toList.eraseDups.length != fmapAsFiniteSupport.size then
    throwError "@[hol]: fmap_as_finite_support fields must be distinct"
  if fmapAsFiniteSupportFunction.toList.eraseDups.length != fmapAsFiniteSupportFunction.size then
    throwError "@[hol]: fmap_as_finite_support_function positions must be distinct"
  if fmapAsFiniteSupportHeterogeneousFunction.toList.eraseDups.length !=
      fmapAsFiniteSupportHeterogeneousFunction.size then
    throwError "@[hol]: fmap_as_finite_support_heterogeneous_function positions must be distinct"
  if fmapAsFiniteSupportParameters.toList.eraseDups.length != fmapAsFiniteSupportParameters.size then
    throwError "@[hol]: fmap_as_finite_support_parameters binders must be distinct"
  if fmapAsFiniteSupportExistentials.toList.eraseDups.length != fmapAsFiniteSupportExistentials.size then
    throwError "@[hol]: fmap_as_finite_support_existentials binders must be distinct"
  if fmapAsFiniteSupportRelation.toList.eraseDups.length != fmapAsFiniteSupportRelation.size then
    throwError "@[hol]: fmap_as_finite_support_relation entries must be distinct"
  if !wordDimensionsAsWidths.isEmpty then
    unless wordDimensionsAsWidths.size == 2 &&
        wordDimensionsAsWidths.toList.eraseDups.length == 2 do
      throwError "@[hol]: word_dimensions_as_widths requires exactly two distinct dimensions"
    if wordDimensionAsWidth.isSome || wordsAsTypeIndexedBitvec ||
        !listAsArray.isEmpty || !namesAsString.isEmpty || !namesAsStringBoundary.isEmpty ||
        !fmapAsFiniteSupport.isEmpty || fmapAsFiniteSupportResult ||
        !fmapAsFiniteSupportFunction.isEmpty || !fmapAsFiniteSupportHeterogeneousFunction.isEmpty ||
        !fmapAsFiniteSupportParameters.isEmpty || !fmapAsFiniteSupportExistentials.isEmpty ||
        !fmapAsFiniteSupportRelation.isEmpty || fmapAsFiniteSupportEqualities ||
        fmapAsFiniteSupportEquality || !fmapAsFiniteSupportResultObservations.isEmpty then
      throwError "@[hol]: word_dimensions_as_widths conflicts with other representation qualifiers except reals_as_rational_cuts"
  if wordDimensionAsWidth.isSome && wordsAsTypeIndexedBitvec then
    throwError "@[hol]: word_dimension_as_width is mutually exclusive with words_as_type_indexed_bitvec"
  if fmapAsFiniteSupportEquality &&
      (fmapAsFiniteSupport.size > 0 || fmapAsFiniteSupportResult ||
       fmapAsFiniteSupportFunction.size > 0 ||
       fmapAsFiniteSupportHeterogeneousFunction.size > 0 ||
       fmapAsFiniteSupportParameters.size > 0 ||
       fmapAsFiniteSupportExistentials.size > 0 ||
       fmapAsFiniteSupportRelation.size > 0 ||
       fmapAsFiniteSupportEqualities) then
    throwError "@[hol]: fmap_as_finite_support_equality is mutually exclusive with other finite-map qualifiers"
  if fmapAsFiniteSupportResultObservations.toList.eraseDups.length != fmapAsFiniteSupportResultObservations.size then
    throwError "@[hol]: fmap_as_finite_support_result_observations producers must be distinct"
  if !fmapAsFiniteSupportResultObservations.isEmpty &&
      (!listAsArray.isEmpty || !namesAsString.isEmpty || wordsAsTypeIndexedBitvec ||
       wordDimensionAsWidth.isSome || realsAsRationalCuts || !fmapAsFiniteSupport.isEmpty || fmapAsFiniteSupportResult ||
       !fmapAsFiniteSupportFunction.isEmpty || !fmapAsFiniteSupportHeterogeneousFunction.isEmpty ||
       !fmapAsFiniteSupportParameters.isEmpty || !fmapAsFiniteSupportExistentials.isEmpty ||
       !fmapAsFiniteSupportRelation.isEmpty || fmapAsFiniteSupportEqualities || fmapAsFiniteSupportEquality) then
    throwError "@[hol]: fmap_as_finite_support_result_observations is mutually exclusive with other finite-map qualifiers"
  pure { fmapAsFiniteSupportResultObservations, path, name, line?, listAsArray, namesAsString, namesAsStringBoundary, fmapAsFiniteSupport, fmapAsFiniteSupportResult, fmapAsFiniteSupportFunction, fmapAsFiniteSupportHeterogeneousFunction, fmapAsFiniteSupportParameters, fmapAsFiniteSupportExistentials, fmapAsFiniteSupportRelation, fmapAsFiniteSupportEqualities, fmapAsFiniteSupportEquality, wordsAsTypeIndexedBitvec, wordDimensionAsWidth, wordDimensionsAsWidths, realsAsRationalCuts }

private def parseHolQualifier (stx : Syntax) : CoreM (String × Array String × Bool × Array (String × String)) := do
  match stx with
  | `(holQualifier| (list_as_array := [$fields:ident,*])) =>
      pure ("list_as_array", fields.getElems.map (fun field => field.getId.eraseMacroScopes.toString), false, #[])
  | `(holQualifier| (names_as_string := [$names:ident,*])) =>
      pure ("names_as_string", names.getElems.map (fun name => name.getId.eraseMacroScopes.toString), false, #[])
  | `(holQualifier| (names_as_string_boundary := [$names:ident,*])) =>
      pure ("names_as_string_boundary", names.getElems.map (fun name => name.getId.eraseMacroScopes.toString), false, #[])
  | `(holQualifier| (fmap_as_finite_support := [$fields:ident,*])) =>
      pure ("fmap_as_finite_support", fields.getElems.map (fun field => field.getId.eraseMacroScopes.toString), false, #[])
  | `(holQualifier| (fmap_as_finite_support_function := [$positions:ident,*])) =>
      pure ("fmap_as_finite_support_function", positions.getElems.map (fun position => position.getId.eraseMacroScopes.toString), false, #[])
  | `(holQualifier| (fmap_as_finite_support_heterogeneous_function := [$positions:ident,*])) =>
      pure ("fmap_as_finite_support_heterogeneous_function", positions.getElems.map (fun position => position.getId.eraseMacroScopes.toString), false, #[])
  | `(holQualifier| (fmap_as_finite_support_result)) =>
      pure ("fmap_as_finite_support_result", #[], true, #[])
  | `(holQualifier| (fmap_as_finite_support_parameters := [$parameters:ident,*])) =>
      pure ("fmap_as_finite_support_parameters", parameters.getElems.map
        (fun parameter => parameter.getId.eraseMacroScopes.toString), false, #[])
  | `(holQualifier| (fmap_as_finite_support_result_observations := [$producers:ident,*])) =>
      pure ("fmap_as_finite_support_result_observations", producers.getElems.map
        (fun producer => producer.getId.eraseMacroScopes.toString), false, #[])
  | `(holQualifier| (fmap_as_finite_support_existentials := [$binders:ident,*])) =>
      pure ("fmap_as_finite_support_existentials", binders.getElems.map
        (fun binder => binder.getId.eraseMacroScopes.toString), false, #[])
  | `(holQualifier| (fmap_as_finite_support_relation := [$entries:ident,*])) =>
      let pairs : Array (String × String) := entries.getElems.map fun entry =>
        let text := entry.getId.eraseMacroScopes.toString
        match text.splitOn "." with
        | [] => (text, "")
        | parts =>
            let field := parts.getLast!
            let carrier := ".".intercalate parts.dropLast
            (carrier, field)
      pure ("fmap_as_finite_support_relation", #[], false, pairs)
  | `(holQualifier| (fmap_as_finite_support_equalities)) =>
      pure ("fmap_as_finite_support_equalities", #[], true, #[])
  | `(holQualifier| (fmap_as_finite_support_equality)) =>
      pure ("fmap_as_finite_support_equality", #[], true, #[])
  | `(holQualifier| (words_as_type_indexed_bitvec)) =>
      pure ("words_as_type_indexed_bitvec", #[], true, #[])
  | `(holQualifier| (word_dimension_as_width := $width:ident)) =>
      pure ("word_dimension_as_width", #[width.getId.eraseMacroScopes.toString], false, #[])
  | `(holQualifier| (word_dimensions_as_widths := [$widths:ident,*])) =>
      pure ("word_dimensions_as_widths", widths.getElems.map
        (fun width => width.getId.eraseMacroScopes.toString), false, #[])
  | `(holQualifier| (reals_as_rational_cuts)) =>
      pure ("reals_as_rational_cuts", #[], true, #[])
  | _ => throwError "@[hol]: malformed qualifier"

private def parseHolRefAttribute (stx : Syntax) : CoreM HolRef := do
  let parse path name line? qualifiers := do
    let mut listAsArray : Array String := #[]
    let mut namesAsString : Array String := #[]
    let mut namesAsStringBoundary : Array String := #[]
    let mut fmapAsFiniteSupport : Array String := #[]
    let mut fmapAsFiniteSupportFunction : Array String := #[]
    let mut fmapAsFiniteSupportHeterogeneousFunction : Array String := #[]
    let mut fmapAsFiniteSupportResult : Bool := false
    let mut fmapAsFiniteSupportParameters : Array String := #[]
    let mut fmapAsFiniteSupportExistentials : Array String := #[]
    let mut fmapAsFiniteSupportRelation : Array (String × String) := #[]
    let mut fmapAsFiniteSupportEqualities : Bool := false
    let mut fmapAsFiniteSupportEquality : Bool := false
    let mut wordsAsTypeIndexedBitvec : Bool := false
    let mut wordDimensionAsWidth : Option String := none
    let mut wordDimensionsAsWidths : Array String := #[]
    let mut seenWordDimensionsAsWidths := false
    let mut fmapAsFiniteSupportResultObservations : Array String := #[]
    let mut realsAsRationalCuts : Bool := false
    for qualifier in qualifiers do
      let (kind, fields, isResult, pairs) ← parseHolQualifier qualifier
      if kind == "list_as_array" then listAsArray := listAsArray ++ fields
      else if kind == "names_as_string" then namesAsString := namesAsString ++ fields
      else if kind == "names_as_string_boundary" then namesAsStringBoundary := namesAsStringBoundary ++ fields
      else if kind == "fmap_as_finite_support_result" then fmapAsFiniteSupportResult := isResult
      else if kind == "fmap_as_finite_support_function" then fmapAsFiniteSupportFunction := fmapAsFiniteSupportFunction ++ fields
      else if kind == "fmap_as_finite_support_heterogeneous_function" then fmapAsFiniteSupportHeterogeneousFunction := fmapAsFiniteSupportHeterogeneousFunction ++ fields
      else if kind == "fmap_as_finite_support_parameters" then fmapAsFiniteSupportParameters := fmapAsFiniteSupportParameters ++ fields
      else if kind == "fmap_as_finite_support_result_observations" then fmapAsFiniteSupportResultObservations := fmapAsFiniteSupportResultObservations ++ fields
      else if kind == "fmap_as_finite_support_existentials" then fmapAsFiniteSupportExistentials := fmapAsFiniteSupportExistentials ++ fields
      else if kind == "fmap_as_finite_support_relation" then fmapAsFiniteSupportRelation := fmapAsFiniteSupportRelation ++ pairs
      else if kind == "fmap_as_finite_support_equalities" then fmapAsFiniteSupportEqualities := isResult
      else if kind == "fmap_as_finite_support_equality" then
        if fmapAsFiniteSupportEquality then
          throwError "@[hol]: fmap_as_finite_support_equality may appear only once"
        fmapAsFiniteSupportEquality := true
      else if kind == "words_as_type_indexed_bitvec" then wordsAsTypeIndexedBitvec := isResult
      else if kind == "word_dimension_as_width" then
        if wordDimensionAsWidth.isSome then
          throwError "@[hol]: word_dimension_as_width may appear only once"
        wordDimensionAsWidth := fields[0]!
      else if kind == "word_dimensions_as_widths" then
        if seenWordDimensionsAsWidths then
          throwError "@[hol]: word_dimensions_as_widths may appear only once"
        seenWordDimensionsAsWidths := true
        unless fields.size == 2 && fields.toList.eraseDups.length == 2 do
          throwError "@[hol]: word_dimensions_as_widths requires exactly two distinct dimensions"
        wordDimensionsAsWidths := fields
      else if kind == "reals_as_rational_cuts" then
        if realsAsRationalCuts then
          throwError "@[hol]: reals_as_rational_cuts may appear only once"
        realsAsRationalCuts := true
      else fmapAsFiniteSupport := fmapAsFiniteSupport ++ fields
    checkedHolRef path name line? listAsArray namesAsString namesAsStringBoundary fmapAsFiniteSupport fmapAsFiniteSupportResult fmapAsFiniteSupportFunction fmapAsFiniteSupportHeterogeneousFunction fmapAsFiniteSupportParameters fmapAsFiniteSupportExistentials fmapAsFiniteSupportRelation fmapAsFiniteSupportEqualities fmapAsFiniteSupportEquality wordsAsTypeIndexedBitvec wordDimensionAsWidth realsAsRationalCuts fmapAsFiniteSupportResultObservations wordDimensionsAsWidths
  match stx with
  | `(attr| hol $path:str $name:str $line:num $qualifiers:holQualifier*) =>
      parse path.getString name.getString (some line.getNat) qualifiers
  | `(attr| hol $path:str $name:str $qualifiers:holQualifier*) =>
      parse path.getString name.getString none qualifiers
  | _ => throwError "@[hol]: expected `hol \"<cakeml path>\" \"<HOL declaration name>\" [line] [(list_as_array := [fields])] [(names_as_string := [fields])]`"

/-! Elaborated-type width validation for `(words_as_type_indexed_bitvec)`.
Runs in the attribute handler on the elaborated declaration type (no textual
parsing): every `BitVec` dimension must be a nonzero literal or a `Nat` binder
discharged by a `NeZero` binder of its own. This discharges the policy that the
qualifier only records the standard positive-width translation of HOL's
type-indexed `'a word`. -/

private partial def natValue? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    match e.getAppFn with
    | .const ``OfNat.ofNat _ =>
        match e.getAppArgs[1]? with
        | some inner => natValue? inner
        | none => none
    | _ => none

private def neZeroArg? (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const ``NeZero _ => e.getAppArgs.back?
  | _ => none

private def stripMdata : Expr → Expr
  | .mdata _ b => stripMdata b
  | e => e

private def isNatBinder (e : Expr) : Bool :=
  stripMdata e == (.const ``Nat [])

/-- Every `NeZero` instance must discharge a local width variable; a literal or
    a compound expression is not a valid positivity discharge. -/
private def neZeroProblem (arg : Expr) : Option String :=
  match stripMdata arg with
  | .bvar _ => none
  | _ =>
      some "NeZero must discharge a local width variable, not a literal or \
        compound dimension"

/-- Problems with one word dimension. `ctx` is the current local binder context,
    innermost last, so a `.bvar k` refers to `ctx[ctx.size - 1 - k]`. A `NeZero`
    binder at `ctx[i]` with argument `.bvar j` refers to `ctx[i - 1 - j]`; the
    width binder and its discharge are matched in that same de Bruijn context. -/
private def dimensionProblem (dim : Expr) (ctx : Array Expr) :
    MetaM (Option String) := do
  let dim ← if dim.hasLooseBVars then pure dim
    else withTransparency .reducible (whnf dim)
  match natValue? dim with
  | some 0 => return some "word dimension is the literal 0"
  | some _ => return none
  | none =>
    match dim with
    | .bvar k =>
        if k < ctx.size then
          let idx := ctx.size - 1 - k
          if isNatBinder ctx[idx]! then
            let hasNeZero := (List.range ctx.size).any (fun i =>
              match neZeroArg? ctx[i]! with
              | some (.bvar j) => j < i && i - 1 - j == idx
              | _ => false)
            if hasNeZero then return none
            else return some s!"word dimension bvar {k} has no NeZero binder"
          else
            return some s!"word dimension bvar {k} is not bound at Nat"
        else
          return some s!"word dimension bvar {k} is out of range"
    | _ =>
        return some "word dimension is neither a nonzero literal nor a local \
          width identifier"

private partial def widthProblemsGo (e : Expr) (ctx : Array Expr)
    (acc : Array String) : MetaM (Array String) := do
  match e with
  | .mdata _ b => widthProblemsGo b ctx acc
  | .forallE _ dom body _ =>
      let acc ← widthProblemsGo dom ctx acc
      widthProblemsGo body (ctx.push dom) acc
  | .lam _ dom body _ =>
      let acc ← widthProblemsGo dom ctx acc
      widthProblemsGo body (ctx.push dom) acc
  | .letE _ ty val body _ =>
      let acc ← widthProblemsGo ty ctx acc
      let acc ← widthProblemsGo val ctx acc
      widthProblemsGo body (ctx.push ty) acc
  | .proj _ _ structType => widthProblemsGo structType ctx acc
  | .app _ _ =>
      match e.getAppFn with
      | .const ``BitVec _ =>
          let dim := e.getAppArgs.back!
          let acc := match ← dimensionProblem dim ctx with
            | some msg => acc.push msg
            | none => acc
          let mut acc := acc
          for arg in e.getAppArgs do acc ← widthProblemsGo arg ctx acc
          return acc
      | .const ``NeZero _ =>
          let acc := match neZeroProblem e.getAppArgs.back! with
            | some msg => acc.push msg
            | none => acc
          let mut acc := acc
          for arg in e.getAppArgs do acc ← widthProblemsGo arg ctx acc
          return acc
      | _ =>
          if e.hasLooseBVars then
            let mut acc := acc
            for arg in e.getAppArgs do acc ← widthProblemsGo arg ctx acc
            return acc
          else
            let unfolded ← withTransparency .reducible (whnf e)
            if unfolded != e then
              widthProblemsGo unfolded ctx acc
            else
              let mut acc := acc
              for arg in e.getAppArgs do acc ← widthProblemsGo arg ctx acc
              return acc
  | _ =>
      if e.hasLooseBVars then
        return acc
      else
        -- A nullary reducible abbreviation used as a type is a bare `.const`,
        -- not an application: unfold it like the `.app` default so that
        -- `abbrev ZeroWord := BitVec 0` cannot hide a zero-width word.
        let unfolded ← withTransparency .reducible (whnf e)
        if unfolded != e then
          widthProblemsGo unfolded ctx acc
        else
          return acc

/-- Problems with the width dimensions of an elaborated declaration type. -/
private def widthProblems (type : Expr) : MetaM (Array String) :=
  widthProblemsGo type #[] #[]

/-- Require a producer constant in the actual elaborated type after eliminating
    inert lets and beta redexes. Textual mentions and proof-body uses do not count. -/
private def resultObservationProblems (type : Expr) (producers : Array String) :
    MetaM (Array String) := do
  let reduced ← zetaReduce type
  let used := reduced.getUsedConstants
  return producers.filterMap fun producer =>
    let producerMatches := used.filter fun name =>
      name.toString == producer || name.toString.endsWith ("." ++ producer)
    if producerMatches.size == 1 then none else
      some s!"producer {producer} must resolve to exactly one constant in the elaborated observer type"

initialize holRefAttribute : ParametricAttribute HolRef ←
  registerParametricAttribute {
    name := `hol
    descr := "original HOL4 declaration (file path and declaration name) ported by this Lean declaration"
    getParam := fun _ stx => parseHolRefAttribute stx
    afterSet := fun decl ref => do
      if !ref.fmapAsFiniteSupportResultObservations.isEmpty then
        let env ← getEnv
        match env.find? decl with
        | some info =>
            let problems ← (resultObservationProblems info.type
              ref.fmapAsFiniteSupportResultObservations).run'
            for problem in problems do
              logError m!"{decl}: (fmap_as_finite_support_result_observations) {problem}"
        | none => logError m!"{decl}: missing elaborated observer declaration"
      if ref.wordsAsTypeIndexedBitvec then
        let env ← getEnv
        match env.find? decl with
        | some info =>
            let problems ← (widthProblems info.type).run'
            for problem in problems do
              logError m!"{decl}: (words_as_type_indexed_bitvec) {problem}"
        | none => pure ()
  }

private def HolRef.qualifierSuffix (ref : HolRef) : String :=
  let listAsArray := if ref.listAsArray.isEmpty then "" else
    s!" (list_as_array := [{String.intercalate ", " ref.listAsArray.toList}])"
  let namesAsString := if ref.namesAsString.isEmpty then "" else
    s!" (names_as_string := [{String.intercalate ", " ref.namesAsString.toList}])"
  let namesAsStringBoundary := if ref.namesAsStringBoundary.isEmpty then "" else
    s!" (names_as_string_boundary := [{String.intercalate ", " ref.namesAsStringBoundary.toList}])"
  let fmapAsFiniteSupport := if ref.fmapAsFiniteSupport.isEmpty then "" else
    s!" (fmap_as_finite_support := [{String.intercalate ", " ref.fmapAsFiniteSupport.toList}])"
  let fmapAsFiniteSupportResult := if ref.fmapAsFiniteSupportResult then
    " (fmap_as_finite_support_result)" else ""
  let fmapAsFiniteSupportFunction := if ref.fmapAsFiniteSupportFunction.isEmpty then "" else
    s!" (fmap_as_finite_support_function := [{String.intercalate ", " ref.fmapAsFiniteSupportFunction.toList}])"
  let fmapAsFiniteSupportHeterogeneousFunction := if ref.fmapAsFiniteSupportHeterogeneousFunction.isEmpty then "" else
    s!" (fmap_as_finite_support_heterogeneous_function := [{String.intercalate ", " ref.fmapAsFiniteSupportHeterogeneousFunction.toList}])"
  let fmapAsFiniteSupportParameters := if ref.fmapAsFiniteSupportParameters.isEmpty then "" else
    s!" (fmap_as_finite_support_parameters := [{String.intercalate ", " ref.fmapAsFiniteSupportParameters.toList}])"
  let fmapAsFiniteSupportExistentials := if ref.fmapAsFiniteSupportExistentials.isEmpty then "" else
    s!" (fmap_as_finite_support_existentials := [{String.intercalate ", " ref.fmapAsFiniteSupportExistentials.toList}])"
  let fmapAsFiniteSupportRelation := if ref.fmapAsFiniteSupportRelation.isEmpty then "" else
    s!" (fmap_as_finite_support_relation := [{String.intercalate ", " (ref.fmapAsFiniteSupportRelation.toList.map (fun entry => if entry.1.isEmpty then entry.2 else s!"{entry.1}.{entry.2}"))}])"
  let fmapAsFiniteSupportEqualities := if ref.fmapAsFiniteSupportEqualities then
    " (fmap_as_finite_support_equalities)" else ""
  let fmapAsFiniteSupportEquality := if ref.fmapAsFiniteSupportEquality then
    " (fmap_as_finite_support_equality)" else ""
  let wordsAsTypeIndexedBitvec := if ref.wordsAsTypeIndexedBitvec then
    " (words_as_type_indexed_bitvec)" else ""
  let wordDimensionAsWidth := ref.wordDimensionAsWidth.map
    (fun width => s!" (word_dimension_as_width := {width})") |>.getD ""
  let wordDimensionsAsWidths := if ref.wordDimensionsAsWidths.isEmpty then "" else
    s!" (word_dimensions_as_widths := [{String.intercalate ", " ref.wordDimensionsAsWidths.toList}])"
  let realsAsRationalCuts := if ref.realsAsRationalCuts then
    " (reals_as_rational_cuts)" else ""
  let observations := if ref.fmapAsFiniteSupportResultObservations.isEmpty then "" else
    s!" (fmap_as_finite_support_result_observations := [{String.intercalate ", " ref.fmapAsFiniteSupportResultObservations.toList}])"
  observations ++ listAsArray ++ namesAsString ++ namesAsStringBoundary ++ fmapAsFiniteSupport ++ fmapAsFiniteSupportResult ++ fmapAsFiniteSupportFunction ++ fmapAsFiniteSupportHeterogeneousFunction ++ fmapAsFiniteSupportParameters ++ fmapAsFiniteSupportExistentials ++ fmapAsFiniteSupportRelation ++ fmapAsFiniteSupportEqualities ++ fmapAsFiniteSupportEquality ++ wordsAsTypeIndexedBitvec ++ wordDimensionAsWidth ++ wordDimensionsAsWidths ++ realsAsRationalCuts

/-! Parser regressions for the original syntax, each qualifier alone, and both
qualifiers together. These elaborate temporary syntax values only; they do not
add test declarations to the HOL-reference inventory. -/
run_cmd do
  let plainSyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname" 7)
  let plain ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute plainSyntax)
  unless plain.line? == some 7 && plain.listAsArray.isEmpty && plain.namesAsString.isEmpty &&
      plain.namesAsStringBoundary.isEmpty do
    throwError "@[hol] unqualified syntax regression"
  let listSyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname" (list_as_array := [fields]))
  let listRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute listSyntax)
  unless listRef.listAsArray == #["fields"] && listRef.namesAsString.isEmpty &&
      listRef.namesAsStringBoundary.isEmpty do
    throwError "@[hol] list_as_array syntax regression"
  let namesSyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname" (names_as_string := [name]))
  let namesRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute namesSyntax)
  unless namesRef.listAsArray.isEmpty && namesRef.namesAsString == #["name"] &&
      namesRef.namesAsStringBoundary.isEmpty do
    throwError "@[hol] names_as_string syntax regression"
  let bothSyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname"
    9 (list_as_array := [fields]) (names_as_string := [name, fieldName]))
  let both ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute bothSyntax)
  unless both.line? == some 9 && both.listAsArray == #["fields"] &&
      both.namesAsString == #["name", "fieldName"] && both.namesAsStringBoundary.isEmpty do
    throwError "@[hol] combined qualifier syntax regression"
  unless HolRef.qualifierSuffix both ==
      " (list_as_array := [fields]) (names_as_string := [name, fieldName])" do
    throwError "@[hol] #hol_refs qualifier-output regression"
  let dimensionSyntax ← `(attr| hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "MustTerminate_limit_def"
    (word_dimension_as_width := width))
  let dimensionRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute dimensionSyntax)
  unless dimensionRef.wordDimensionAsWidth == some "width" &&
      HolRef.qualifierSuffix dimensionRef == " (word_dimension_as_width := width)" do
    throwError "@[hol] word_dimension_as_width syntax regression"
  let duplicateDimensionSyntax ← `(attr| hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "MustTerminate_limit_def"
    (word_dimension_as_width := width) (word_dimension_as_width := width))
  let duplicateDimensionRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute duplicateDimensionSyntax
      pure false
    catch _ => pure true
  unless duplicateDimensionRejected do
    throwError "@[hol] duplicate word_dimension_as_width qualifiers must be rejected"
  let conflictingDimensionSyntax ← `(attr| hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "MustTerminate_limit_def"
    (word_dimension_as_width := width) (words_as_type_indexed_bitvec))
  let conflictingDimensionRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute conflictingDimensionSyntax
      pure false
    catch _ => pure true
  unless conflictingDimensionRejected do
    throwError "@[hol] word_dimension_as_width and words_as_type_indexed_bitvec must be mutually exclusive"
  let dimensionsSyntax ← `(attr| hol "HOL/src/floating-point/binary_ieeeScript.sml" "largest_def"
    (word_dimensions_as_widths := [t, w]) (reals_as_rational_cuts))
  let dimensionsRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute dimensionsSyntax)
  unless dimensionsRef.wordDimensionsAsWidths == #["t", "w"] &&
      dimensionsRef.wordDimensionAsWidth.isNone && dimensionsRef.realsAsRationalCuts &&
      HolRef.qualifierSuffix dimensionsRef ==
        " (word_dimensions_as_widths := [t, w]) (reals_as_rational_cuts)" do
    throwError "@[hol] word_dimensions_as_widths syntax/output regression"
  let badDimensionsSyntax0 ← `(attr| hol "HOL/src/floating-point/binary_ieeeScript.sml" "largest_def"
    (word_dimensions_as_widths := []))
  let badDimensionsRejected0 ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute badDimensionsSyntax0
      pure false
    catch _ => pure true
  unless badDimensionsRejected0 do
    throwError "@[hol] invalid two-dimension qualifier 0 must be rejected"
  let badDimensionsSyntax1 ← `(attr| hol "HOL/src/floating-point/binary_ieeeScript.sml" "largest_def"
    (word_dimensions_as_widths := [t]))
  let badDimensionsRejected1 ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute badDimensionsSyntax1
      pure false
    catch _ => pure true
  unless badDimensionsRejected1 do
    throwError "@[hol] invalid two-dimension qualifier 1 must be rejected"
  let badDimensionsSyntax2 ← `(attr| hol "HOL/src/floating-point/binary_ieeeScript.sml" "largest_def"
    (word_dimensions_as_widths := [t, t]))
  let badDimensionsRejected2 ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute badDimensionsSyntax2
      pure false
    catch _ => pure true
  unless badDimensionsRejected2 do
    throwError "@[hol] invalid two-dimension qualifier 2 must be rejected"
  let badDimensionsSyntax3 ← `(attr| hol "HOL/src/floating-point/binary_ieeeScript.sml" "largest_def"
    (word_dimensions_as_widths := [t, w, x]))
  let badDimensionsRejected3 ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute badDimensionsSyntax3
      pure false
    catch _ => pure true
  unless badDimensionsRejected3 do
    throwError "@[hol] invalid two-dimension qualifier 3 must be rejected"
  let badDimensionsSyntax4 ← `(attr| hol "HOL/src/floating-point/binary_ieeeScript.sml" "largest_def"
    (word_dimensions_as_widths := [t, w]) (word_dimensions_as_widths := [t, w]))
  let badDimensionsRejected4 ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute badDimensionsSyntax4
      pure false
    catch _ => pure true
  unless badDimensionsRejected4 do
    throwError "@[hol] invalid two-dimension qualifier 4 must be rejected"
  let badDimensionsSyntax5 ← `(attr| hol "HOL/src/floating-point/binary_ieeeScript.sml" "largest_def"
    (word_dimensions_as_widths := [t, w]) (word_dimension_as_width := t))
  let badDimensionsRejected5 ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute badDimensionsSyntax5
      pure false
    catch _ => pure true
  unless badDimensionsRejected5 do
    throwError "@[hol] invalid two-dimension qualifier 5 must be rejected"
  let badDimensionsSyntax6 ← `(attr| hol "HOL/src/floating-point/binary_ieeeScript.sml" "largest_def"
    (word_dimensions_as_widths := [t, w]) (words_as_type_indexed_bitvec))
  let badDimensionsRejected6 ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute badDimensionsSyntax6
      pure false
    catch _ => pure true
  unless badDimensionsRejected6 do
    throwError "@[hol] invalid two-dimension qualifier 6 must be rejected"
  let badDimensionsSyntax7 ← `(attr| hol "HOL/src/floating-point/binary_ieeeScript.sml" "largest_def"
    (word_dimensions_as_widths := [t, w]) (names_as_string := [name]))
  let badDimensionsRejected7 ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute badDimensionsSyntax7
      pure false
    catch _ => pure true
  unless badDimensionsRejected7 do
    throwError "@[hol] invalid two-dimension qualifier 7 must be rejected"
  let realsSyntax ← `(attr| hol "cakeml/semantics/fpSemScript.sml" "fp_uop_comp_def"
    (reals_as_rational_cuts))
  let realsRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute realsSyntax)
  unless realsRef.realsAsRationalCuts &&
      HolRef.qualifierSuffix realsRef == " (reals_as_rational_cuts)" do
    throwError "@[hol] reals_as_rational_cuts syntax regression"
  let realsCombinedSyntax ← `(attr| hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "inst_def"
    (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)
    (reals_as_rational_cuts))
  let realsCombinedRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute realsCombinedSyntax)
  unless realsCombinedRef.realsAsRationalCuts && realsCombinedRef.wordsAsTypeIndexedBitvec &&
      HolRef.qualifierSuffix realsCombinedRef ==
        " (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec) (reals_as_rational_cuts)" do
    throwError "@[hol] combined reals_as_rational_cuts syntax regression"
  let duplicateRealsSyntax ← `(attr| hol "cakeml/semantics/fpSemScript.sml" "fp_uop_comp_def"
    (reals_as_rational_cuts) (reals_as_rational_cuts))
  let duplicateRealsRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute duplicateRealsSyntax
      pure false
    catch _ => pure true
  unless duplicateRealsRejected do
    throwError "@[hol] duplicate reals_as_rational_cuts qualifiers must be rejected"
  let equalitySyntax ← `(attr| hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "res_var_FEMPTY"
    (fmap_as_finite_support_equality))
  let equalityRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute equalitySyntax)
  unless equalityRef.fmapAsFiniteSupportEquality &&
      HolRef.qualifierSuffix equalityRef == " (fmap_as_finite_support_equality)" do
    throwError "@[hol] fmap_as_finite_support_equality syntax regression"
  let duplicateEqualitySyntax ← `(attr| hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "res_var_FEMPTY"
    (fmap_as_finite_support_equality) (fmap_as_finite_support_equality))
  let duplicateEqualityRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute duplicateEqualitySyntax
      pure false
    catch _ => pure true
  unless duplicateEqualityRejected do
    throwError "@[hol] duplicate fmap_as_finite_support_equality qualifiers must be rejected"
  let conflictingEqualitySyntax ← `(attr| hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "res_var_FEMPTY"
    (fmap_as_finite_support_equality) (fmap_as_finite_support_equalities))
  let conflictingEqualityRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute conflictingEqualitySyntax
      pure false
    catch _ => pure true
  unless conflictingEqualityRejected do
    throwError "@[hol] fmap_as_finite_support_equality and fmap_as_finite_support_equalities must be mutually exclusive"
  let boundarySyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname"
    (names_as_string := [name, generated]) (names_as_string_boundary := [generated]))
  let boundaryRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute boundarySyntax)
  unless boundaryRef.namesAsString == #["name", "generated"] &&
      boundaryRef.namesAsStringBoundary == #["generated"] &&
      HolRef.qualifierSuffix boundaryRef ==
        " (names_as_string := [name, generated]) (names_as_string_boundary := [generated])" do
    throwError "@[hol] names_as_string_boundary syntax regression"
  let duplicateSyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname"
    (names_as_string := [name, name]))
  let duplicateRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute duplicateSyntax
      pure false
    catch _ => pure true
  unless duplicateRejected do
    throwError "@[hol] duplicate names_as_string identifiers must be rejected"
  let boundaryOutsideSyntax ← `(attr| hol "cakeml/pancake/panLangScript.sml" "varname"
    (names_as_string := [name]) (names_as_string_boundary := [generated]))
  let boundaryOutsideRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute boundaryOutsideSyntax
      pure false
    catch _ => pure true
  unless boundaryOutsideRejected do
    throwError "@[hol] boundary identifiers outside names_as_string must be rejected"
  let fmapSyntax ← `(attr| hol "cakeml/pancake/semantics/panSemScript.sml" "set_var_def"
    (fmap_as_finite_support := [locals, globals]))
  let fmapRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute fmapSyntax)
  unless fmapRef.fmapAsFiniteSupport == #["locals", "globals"] &&
      HolRef.qualifierSuffix fmapRef ==
        " (fmap_as_finite_support := [locals, globals])" do
    throwError "@[hol] fmap_as_finite_support syntax regression"
  let fmapFunctionSyntax ← `(attr| hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "gc_fun_type"
    (fmap_as_finite_support_function := [argument_4, result_3]))
  let fmapFunctionRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute fmapFunctionSyntax)
  unless fmapFunctionRef.fmapAsFiniteSupportFunction == #["argument_4", "result_3"] &&
      HolRef.qualifierSuffix fmapFunctionRef ==
        " (fmap_as_finite_support_function := [argument_4, result_3])" do
    throwError "@[hol] fmap_as_finite_support_function syntax regression"
  let fmapHeterogeneousFunctionSyntax ← `(attr| hol "cakeml/pancake/semantics/panSemScript.sml" "lookup_code_def"
    (fmap_as_finite_support_heterogeneous_function := [argument_1, result_2]))
  let fmapHeterogeneousFunctionRef ← Lean.Elab.Command.liftCoreM
    (parseHolRefAttribute fmapHeterogeneousFunctionSyntax)
  unless fmapHeterogeneousFunctionRef.fmapAsFiniteSupportHeterogeneousFunction ==
      #["argument_1", "result_2"] &&
      HolRef.qualifierSuffix fmapHeterogeneousFunctionRef ==
        " (fmap_as_finite_support_heterogeneous_function := [argument_1, result_2])" do
    throwError "@[hol] fmap_as_finite_support_heterogeneous_function syntax regression"
  let fmapFunctionDuplicateSyntax ← `(attr| hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "gc_fun_type"
    (fmap_as_finite_support_function := [argument_4, argument_4]))
  let fmapFunctionDuplicateRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute fmapFunctionDuplicateSyntax
      pure false
    catch _ => pure true
  unless fmapFunctionDuplicateRejected do
    throwError "@[hol] duplicate fmap_as_finite_support_function positions must be rejected"
  let fmapParametersSyntax ← `(attr| hol "cakeml/pancake/semantics/panSemScript.sml" "set_var_def"
    (fmap_as_finite_support_parameters := [fm, fm2]))
  let fmapParametersRef ← Lean.Elab.Command.liftCoreM
    (parseHolRefAttribute fmapParametersSyntax)
  unless fmapParametersRef.fmapAsFiniteSupportParameters == #["fm", "fm2"] &&
      HolRef.qualifierSuffix fmapParametersRef ==
        " (fmap_as_finite_support_parameters := [fm, fm2])" do
    throwError "@[hol] fmap_as_finite_support_parameters syntax regression"
  let unusedLet := Expr.letE `ignored (.const ``Nat []) (.lit (.natVal 0))
    (.const ``True []) false
  let ignoredProblems ← Lean.Elab.Command.liftCoreM
    ((resultObservationProblems unusedLet #["Nat"]).run')
  unless ignoredProblems.size == 1 do
    throwError "@[hol] discarded let must not establish result producer dependency"
  let usedProblems ← Lean.Elab.Command.liftCoreM
    ((resultObservationProblems (.const ``True []) #["True"]).run')
  unless usedProblems.isEmpty do
    throwError "@[hol] actual elaborated result producer dependency must be retained"
  let observationSyntax ← `(attr| hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "to_fmap_key_set"
    (fmap_as_finite_support_result_observations := [BalancedMap.toFmap]))
  let observationRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute observationSyntax)
  unless observationRef.fmapAsFiniteSupportResultObservations == #["BalancedMap.toFmap"] &&
      HolRef.qualifierSuffix observationRef ==
        " (fmap_as_finite_support_result_observations := [BalancedMap.toFmap])" do
    throwError "@[hol] result observation syntax regression"
  let duplicateObservationSyntax ← `(attr| hol "HOL/examples/data-structures/balanced_bst/balanced_mapScript.sml" "to_fmap_key_set"
    (fmap_as_finite_support_result_observations := [toFmap, toFmap]))
  let duplicateObservationRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute duplicateObservationSyntax
      pure false
    catch _ => pure true
  unless duplicateObservationRejected do
    throwError "@[hol] duplicate result observation producers must be rejected"
  let fmapExistentialsSyntax ← `(attr| hol "cakeml/pancake/proofs/crep_inlineProofScript.sml" "code_inl_rel_def"
    (fmap_as_finite_support_existentials := [inl_bag]))
  let fmapExistentialsRef ← Lean.Elab.Command.liftCoreM
    (parseHolRefAttribute fmapExistentialsSyntax)
  unless fmapExistentialsRef.fmapAsFiniteSupportExistentials == #["inl_bag"] &&
      HolRef.qualifierSuffix fmapExistentialsRef ==
        " (fmap_as_finite_support_existentials := [inl_bag])" do
    throwError "@[hol] fmap_as_finite_support_existentials syntax regression"
  let fmapDuplicateSyntax ← `(attr| hol "cakeml/pancake/semantics/panSemScript.sml" "set_var_def"
    (fmap_as_finite_support := [locals, locals]))
  let fmapDuplicateRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute fmapDuplicateSyntax
      pure false
    catch _ => pure true
  unless fmapDuplicateRejected do
    throwError "@[hol] duplicate fmap_as_finite_support fields must be rejected"
  let fmapResultSyntax ← `(attr| hol "cakeml/pancake/pan_to_crepScript.sml" "get_eids_from_decls_def"
    (fmap_as_finite_support_result))
  let fmapResultRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute fmapResultSyntax)
  unless fmapResultRef.fmapAsFiniteSupportResult && fmapResultRef.fmapAsFiniteSupport.isEmpty &&
      HolRef.qualifierSuffix fmapResultRef == " (fmap_as_finite_support_result)" do
    throwError "@[hol] fmap_as_finite_support_result syntax regression"
  let fmapRelationSyntax ← `(attr| hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_def"
    (fmap_as_finite_support_relation := [PanSemStateFiniteExact.globals, CrepSemHOLState.locals]))
  let fmapRelationRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute fmapRelationSyntax)
  unless fmapRelationRef.fmapAsFiniteSupportRelation.toList ==
      [("PanSemStateFiniteExact", "globals"), ("CrepSemHOLState", "locals")] &&
      HolRef.qualifierSuffix fmapRelationRef ==
        " (fmap_as_finite_support_relation := [PanSemStateFiniteExact.globals, CrepSemHOLState.locals])" do
    throwError "@[hol] fmap_as_finite_support_relation syntax regression"
  let fmapRelationDuplicateSyntax ← `(attr| hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "state_rel_def"
    (fmap_as_finite_support_relation := [PanSemStateFiniteExact.globals, PanSemStateFiniteExact.globals]))
  let fmapRelationDuplicateRejected ← Lean.Elab.Command.liftCoreM do
    try
      let _ ← parseHolRefAttribute fmapRelationDuplicateSyntax
      pure false
    catch _ => pure true
  unless fmapRelationDuplicateRejected do
    throwError "@[hol] duplicate fmap_as_finite_support_relation entries must be rejected"
  let fmapRelationParameterSyntax ← `(attr| hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "locals_rel_def"
    (fmap_as_finite_support_relation := [PanToCrepContextExact.vars, sourceLocals, targetLocals]))
  let fmapRelationParameterRef ← Lean.Elab.Command.liftCoreM (parseHolRefAttribute fmapRelationParameterSyntax)
  unless fmapRelationParameterRef.fmapAsFiniteSupportRelation.toList ==
      [("PanToCrepContextExact", "vars"), ("", "sourceLocals"), ("", "targetLocals")] &&
      HolRef.qualifierSuffix fmapRelationParameterRef ==
        " (fmap_as_finite_support_relation := [PanToCrepContextExact.vars, sourceLocals, targetLocals])" do
    throwError "@[hol] fmap_as_finite_support_relation bare-parameter syntax regression"
  let widthProblemsOf (stx : Syntax) : Lean.Elab.Command.CommandElabM (Array String) := do
    let type ← Lean.Elab.Command.liftTermElabM (Lean.Elab.Term.elabType stx)
    Lean.Elab.Command.liftCoreM (widthProblems type).run'
  let hasNeZero (message : String) : Bool := (message.splitOn "NeZero").length > 1
  let validWidth ← widthProblemsOf (← `(∀ {w : Nat} [NeZero w], BitVec w → True))
  unless validWidth.isEmpty do
    throwError "valid width binder was rejected: {validWidth}"
  let nestedWidth ← widthProblemsOf (← `((∀ {w : Nat} [NeZero w], BitVec w) → True))
  unless nestedWidth.isEmpty do
    throwError "nested width binder was rejected: {nestedWidth}"
  let literalWidth ← widthProblemsOf (← `(∀ [NeZero 5], BitVec 5 → True))
  unless literalWidth.any hasNeZero do
    throwError "literal NeZero argument was accepted: {literalWidth}"
  let compoundWidth ← widthProblemsOf (← `(∀ {w : Nat} [NeZero (w - w)], BitVec w → True))
  unless compoundWidth.any hasNeZero do
    throwError "compound NeZero argument was accepted: {compoundWidth}"
  let missingWidth ← widthProblemsOf (← `((u : Unit) → (m : Nat) → BitVec m → True))
  unless missingWidth.any hasNeZero do
    throwError "undischarged nested width was accepted: {missingWidth}"

/-- The HOL cross-reference attached to `declName`, if any. -/
def HolRef.get? (env : Environment) (declName : Name) : Option HolRef :=
  holRefAttribute.getParam? env declName

/-- Every declaration carrying `@[hol ...]` in the current environment, from the
    current module and from imported modules. -/
def HolRef.all (env : Environment) : Array (Name × HolRef) := Id.run do
  let mut result : Array (Name × HolRef) := #[]
  let (_, current) := holRefAttribute.ext.getState env
  result := current.foldl (fun acc declName ref => acc.push (declName, ref)) result
  for module in holRefAttribute.ext.toEnvExtension.getState env |>.importedEntries do
    for entry in module do
      result := result.push entry
  return result.qsort (fun left right => Name.lt left.1 right.1)

/-- `#hol_refs` prints every `@[hol]`-tagged declaration visible here as
    `<lean name>  <hol path>  <hol name> [:line]`. -/
syntax (name := holRefsCmd) "#hol_refs" : command

open Elab Command in
@[command_elab holRefsCmd] def elabHolRefs : CommandElab := fun _ => do
  let env ← getEnv
  for (declName, ref) in HolRef.all env do
    logInfo m!"{declName}  {ref.path}  {ref.name}{ref.line?.map (fun line => s!" :{line}") |>.getD ""}{HolRef.qualifierSuffix ref}"

end Flapjack
