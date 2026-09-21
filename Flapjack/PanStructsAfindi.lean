import Flapjack.Static

/-!
Faithful executable port of CakeML Pancake's `pan_structs$afindi` helper.
`afindi` returns the first zero-based position of a key in an association
list, preserving the original first-match behavior on duplicate keys.
-/

namespace Flapjack

def afindi [BEq α] (key : α) : List (α × β) → Option Nat
  | [] => none
  | (candidate, _) :: entries =>
      if key == candidate then some 0
      else match afindi key entries with
        | none => none
        | some index => some (index + 1)
termination_by entries => sizeOf entries
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial

/-! CakeML `pan_structsProofScript.sml` lemmas about `afindi`
    (`afindi_less_length`, `afindi_EL`, `afindi_append`, `afindi_MAP_eq`). -/

theorem afindi_cons [BEq α] (key : α) (entry : α × β) (rest : List (α × β)) :
    afindi key (entry :: rest) =
      if key == entry.1 then some 0
      else match afindi key rest with
        | none => none
        | some index => some (index + 1) := by
  obtain ⟨candidate, value⟩ := entry
  simp [afindi]

theorem afindi_less_length [BEq α] (key : α) :
    ∀ (entries : List (α × β)) (index : Nat),
      afindi key entries = some index → index < entries.length := by
  intro entries
  induction entries with
  | nil =>
      intro index h
      simp [afindi] at h
  | cons entry rest ih =>
      intro index h
      obtain ⟨candidate, value⟩ := entry
      simp only [afindi] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp
      · split at h
        · simp at h
        · rename_i found hfound
          simp only [Option.some.injEq] at h
          subst h
          have hlt := ih found hfound
          simp only [List.length_cons]
          omega

theorem afindi_el_fst [BEq α] [LawfulBEq α] (key : α) :
    ∀ (entries : List (α × β)) (index : Nat),
      afindi key entries = some index →
        (entries[index]?).map Prod.fst = some key := by
  intro entries
  induction entries with
  | nil =>
      intro index h
      simp [afindi] at h
  | cons entry rest ih =>
      intro index h
      obtain ⟨candidate, value⟩ := entry
      simp only [afindi] at h
      split at h
      · rename_i hbeq
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.getElem?_cons_zero, Option.map_some]
        exact congrArg some (eq_of_beq hbeq).symm
      · split at h
        · simp at h
        · rename_i found hfound
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.getElem?_cons_succ]
          exact ih found hfound

theorem afindi_append [BEq α] (key : α) (xs ys : List (α × β)) :
    afindi key (xs ++ ys) =
      (match afindi key xs with
        | none => (afindi key ys).map (fun index => index + xs.length)
        | some index => some index) := by
  induction xs with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hbeq : key == candidate
      · simp [afindi, hbeq]
      · simp only [List.cons_append, afindi, hbeq]
        rw [ih]
        cases ha : afindi key rest with
        | none =>
            cases hb : afindi key ys with
            | none => simp
            | some index => simp; omega
        | some index => simp

theorem afindi_map_eq [BEq α] (key : α) (f : α × β → α × γ)
    (entries : List (α × β))
    (hf : ∀ x y, (x, y) ∈ entries → (f (x, y)).1 = x) :
    afindi key (entries.map f) = afindi key entries := by
  induction entries with
  | nil => simp only [List.map_nil, afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      have hhead : (f (candidate, value)).1 = candidate :=
        hf candidate value (by simp)
      have htail : ∀ x y, (x, y) ∈ rest → (f (x, y)).1 = x :=
        fun x y hxy => hf x y (by simp [hxy])
      simp only [List.map_cons]
      rw [afindi_cons, afindi_cons, hhead, ih htail]

theorem afindi_dropWhile [BEq α] (key : α) (entries : List (α × β)) :
    entries.dropWhile (fun entry => !(key == entry.1)) =
      match afindi key entries with
      | none => []
      | some index => entries.drop index := by
  induction entries with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      cases hb : (key == candidate) with
      | true => simp [afindi_cons, hb]
      | false =>
          simp only [List.dropWhile_cons, afindi_cons, hb]
          rw [ih]
          cases afindi key rest with
          | none => simp
          | some index => simp [List.drop_succ_cons]

theorem afindi_lookup [BEq α] (key : α) (entries : List (α × β)) :
    entries.lookup key =
      (afindi key entries).bind (fun index => (entries[index]?).map Prod.snd) := by
  induction entries with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hbeq : key == candidate
      · simp [List.lookup_cons, afindi_cons, hbeq]
      · simp only [List.lookup_cons, hbeq, afindi_cons]
        rw [ih]
        cases afindi key rest with
        | none => simp
        | some index => simp [List.getElem?_cons_succ]

end Flapjack
