import Flapjack.Pipeline

/-!
Concrete exception-code relation for the source-to-Crep correctness boundary.

This is the Lean counterpart of `get_eids_from_decls` and
`get_eids_imp_excp_rel` from
`cakeml/pancake/pan_to_crepScript.sml` and
`cakeml/pancake/proofs/pan_to_crepProofScript.sml`.

Cake numbers the source exception declarations in source order and proves that
any exception table with the same finite domain is related to that table: the
numbering table is injective.  The original proof obtains injectivity from
`size_of_eids < dimword`; the Lean statement exposes the corresponding
bounded injectivity premise for the abstract `fromNat` word representation.
This keeps the theorem usable for `BitVec` as well as small executable models.
-/

namespace Flapjack

/-! Number the exception entries starting at the supplied source index. -/
def panExceptionCodeEntriesAux (fromNat : Nat → α) (index : Nat) :
    List (ExceptionId × Shape) → InfoMap α
  | [] => []
  | (exception, _) :: entries =>
      (exception, fromNat index) ::
        panExceptionCodeEntriesAux fromNat (index + 1) entries
termination_by entries => sizeOf entries

/-! The existing executable port calls this table
`crepGetEidsFromDecls`.  The auxiliary representation above is only used to
prove its finite-word injectivity. -/
theorem pipelineExceptionCodes_eq_panExceptionCodeEntriesAux
    (fromNat : Nat → α) (index : Nat)
    (declarations : List (Decl α)) :
    pipelineExceptionCodes fromNat index declarations =
      panExceptionCodeEntriesAux fromNat index (exceptionEntries declarations) := by
  induction declarations generalizing index with
  | nil => simp [pipelineExceptionCodes, exceptionEntries, panExceptionCodeEntriesAux]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [pipelineExceptionCodes, exceptionEntries,
          panExceptionCodeEntriesAux, ih]

/-! A list-backed analogue of Cake's `excp_rel`: the two tables have the same
domain, and the expected table is injective.  The actual table's values are
intentionally unconstrained, just as in the HOL theorem. -/
def panValuePcExceptionCodeRel [BEq String]
    (expected actual : InfoMap α) : Prop :=
  (∀ exception,
    lookupInfo exception expected = none ↔
      lookupInfo exception actual = none) ∧
  (∀ exception exception' code code',
    lookupInfo exception expected = some code →
    lookupInfo exception' expected = some code' →
    code = code' → exception = exception')

theorem panExceptionCodeEntries_lookup_code_index [BEq String]
    (fromNat : Nat → α) (index : Nat)
    (entries : List (ExceptionId × Shape))
    (exception : ExceptionId) (code : α)
    (hlookup : lookupInfo exception
      (panExceptionCodeEntriesAux fromNat index entries) = some code) :
    ∃ offset, offset < entries.length ∧
      code = fromNat (index + offset) := by
  induction entries generalizing index with
  | nil =>
      simp [panExceptionCodeEntriesAux, lookupInfo] at hlookup
  | cons head tail ih =>
      rcases head with ⟨head, shape⟩
      by_cases heq : head == exception
      · simp [panExceptionCodeEntriesAux, lookupInfo, heq] at hlookup
        exact ⟨0, by simp, by simpa using hlookup.symm⟩
      · simp [panExceptionCodeEntriesAux, lookupInfo, heq] at hlookup
        obtain ⟨offset, hlt, hcode⟩ := ih (index + 1) hlookup
        refine ⟨offset + 1, by simp [hlt], ?_⟩
        rw [hcode]
        congr 1
        omega

/-! Injectivity of the numbering table.  The bounds are explicit so this is
the exact finite-word premise used by Cake, rather than an unnecessarily
global injectivity assumption on `fromNat`. -/
theorem panExceptionCodeEntries_lookup_injective_bounded
    [BEq String] [LawfulBEq String]
    (fromNat : Nat → α) (limit : Nat)
    (hfrom : ∀ i j, i < limit → j < limit →
      fromNat i = fromNat j → i = j)
    (index : Nat) (entries : List (ExceptionId × Shape))
    (hbound : index + entries.length ≤ limit)
    (hnodup : (entries.map Prod.fst).Nodup)
    (left right : ExceptionId) (leftCode rightCode : α)
    (hleft : lookupInfo left
      (panExceptionCodeEntriesAux fromNat index entries) = some leftCode)
    (hright : lookupInfo right
      (panExceptionCodeEntriesAux fromNat index entries) = some rightCode)
    (hcode : leftCode = rightCode) :
    left = right := by
  induction entries generalizing index with
  | nil =>
      simp [panExceptionCodeEntriesAux, lookupInfo] at hleft
  | cons head tail ih =>
      rcases head with ⟨head, shape⟩
      have hnodup' := List.nodup_cons.mp hnodup
      simp only [List.length_cons] at hbound
      by_cases hleftHead : head == left
      · simp [panExceptionCodeEntriesAux, lookupInfo, hleftHead] at hleft
        by_cases hrightHead : head == right
        · have hleftName : head = left := LawfulBEq.eq_of_beq hleftHead
          have hrightName : head = right := LawfulBEq.eq_of_beq hrightHead
          exact hleftName.symm.trans hrightName
        · simp [panExceptionCodeEntriesAux, lookupInfo, hrightHead] at hright
          obtain ⟨offset, hlt, hrightCode⟩ :=
            panExceptionCodeEntries_lookup_code_index fromNat
              (index + 1) tail right rightCode hright
          have hbad : index = index + 1 + offset :=
            hfrom index (index + 1 + offset) (by omega) (by omega)
              (hleft.trans (hcode.trans hrightCode))
          omega
      · simp [panExceptionCodeEntriesAux, lookupInfo, hleftHead] at hleft
        by_cases hrightHead : head == right
        · simp [panExceptionCodeEntriesAux, lookupInfo, hrightHead] at hright
          obtain ⟨offset, hlt, hleftCode⟩ :=
            panExceptionCodeEntries_lookup_code_index fromNat
              (index + 1) tail left leftCode hleft
          have hbad : index + 1 + offset = index :=
            hfrom (index + 1 + offset) index (by omega) (by omega)
              (hleftCode.symm.trans (hcode.trans hright.symm))
          omega
        · simp [panExceptionCodeEntriesAux, lookupInfo, hrightHead] at hright
          exact ih (index + 1) (by omega) hnodup'.2 hleft hright

theorem getEidsImpExcpRel
    [BEq String] [LawfulBEq String]
    (fromNat : Nat → α) (declarations : List (Decl α))
    (actual : InfoMap α)
    (hfrom : ∀ i j,
      i < (exceptionEntries declarations).length →
      j < (exceptionEntries declarations).length →
      fromNat i = fromNat j → i = j)
    (hnodup : ((exceptionEntries declarations).map Prod.fst).Nodup)
    (hdomain : ∀ exception,
      lookupInfo exception (crepGetEidsFromDecls fromNat declarations) = none ↔
        lookupInfo exception actual = none) :
    panValuePcExceptionCodeRel
      (crepGetEidsFromDecls fromNat declarations) actual := by
  constructor
  · exact hdomain
  · intro exception exception' code code' hlookup hlookup' hcode
    have hlookup'aux : lookupInfo exception
        (panExceptionCodeEntriesAux fromNat 0 (exceptionEntries declarations)) =
        some code := by
      change lookupInfo exception
          (pipelineExceptionCodes fromNat 0 declarations) = some code at hlookup
      rw [pipelineExceptionCodes_eq_panExceptionCodeEntriesAux
        fromNat 0 declarations] at hlookup
      exact hlookup
    have hlookup''aux : lookupInfo exception'
        (panExceptionCodeEntriesAux fromNat 0 (exceptionEntries declarations)) =
        some code' := by
      change lookupInfo exception'
          (pipelineExceptionCodes fromNat 0 declarations) = some code' at hlookup'
      rw [pipelineExceptionCodes_eq_panExceptionCodeEntriesAux
        fromNat 0 declarations] at hlookup'
      exact hlookup'
    exact panExceptionCodeEntries_lookup_injective_bounded
      fromNat (exceptionEntries declarations).length hfrom 0
      (exceptionEntries declarations) (by simp) hnodup
      exception exception' code code' hlookup'aux hlookup''aux hcode

end Flapjack
