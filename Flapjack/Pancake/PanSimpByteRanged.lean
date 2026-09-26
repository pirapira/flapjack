import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.PanLang.Decl

/-!
Byte-range preservation facts for the executable `pan_simp` transform.
These are Flapjack-specific representation invariants, not HOL correctness
theorems: the rewrites reassociate sequences and move existing names and
expressions without changing their character data.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

theorem smartSeq_byteRanged {width : Nat} (pre program : Prog (BitVec width))
    (hpre : ProgByteRanged pre) (hprogram : ProgByteRanged program) :
    ProgByteRanged (smartSeq pre program) := by
  cases pre <;>
    first
    | exact hprogram
    | exact ⟨hpre, hprogram⟩

theorem seqCallRet_byteRanged {width : Nat} (program : Prog (BitVec width))
    (h : ProgByteRanged program) : ProgByteRanged (seqCallRet program) := by
  unfold seqCallRet
  split
  · split
    · exact ⟨h.1.1, h.1.2.1, trivial⟩
    · exact h
  · exact h

theorem seqAssoc_byteRanged {width : Nat} (pre program : Prog (BitVec width))
    (hpre : ProgByteRanged pre) (hprogram : ProgByteRanged program) :
    ProgByteRanged (seqAssoc pre program) := by
  let rec go (pre : Prog (BitVec width)) (hpre : ProgByteRanged pre) :
      (program : Prog (BitVec width)) → ProgByteRanged program →
        ProgByteRanged (seqAssoc pre program)
    | .skip, _ => by simpa [seqAssoc] using hpre
    | .dec name shape value body, hbody => by
        simp only [seqAssoc]
        exact smartSeq_byteRanged pre _ hpre
          ⟨hbody.1, hbody.2.1, hbody.2.2.1, go .skip trivial body hbody.2.2.2⟩
    | .seq first second, hbody => by
        simp only [seqAssoc]
        exact go (seqAssoc pre first) (go pre hpre first hbody.1) second hbody.2
    | .ite condition thenBranch elseBranch, hbody => by
        simp only [seqAssoc]
        exact smartSeq_byteRanged pre _ hpre
          ⟨hbody.1, go .skip trivial thenBranch hbody.2.1,
            go .skip trivial elseBranch hbody.2.2⟩
    | .while condition body, hbody => by
        simp only [seqAssoc]
        exact smartSeq_byteRanged pre _ hpre ⟨hbody.1, go .skip trivial body hbody.2⟩
    | .call none function arguments, hbody => by
        simp only [seqAssoc]
        exact smartSeq_byteRanged pre _ hpre hbody
    | .call (some (kindOpt, none)) function arguments, hbody => by
        simp only [seqAssoc]
        exact smartSeq_byteRanged pre _ hpre hbody
    | .call (some (kindOpt, some (eid, vn, handlerProgram))) function arguments, hbody => by
        simp only [seqAssoc]
        refine smartSeq_byteRanged pre _ hpre ?_
        simp only [ProgByteRanged] at hbody ⊢
        exact ⟨hbody.1, hbody.2.1, hbody.2.2.1, hbody.2.2.2.1,
          hbody.2.2.2.2.1, go .skip trivial handlerProgram hbody.2.2.2.2.2⟩
    | .decCall name shape function arguments body, hbody => by
        simp only [seqAssoc]
        exact smartSeq_byteRanged pre _ hpre
          ⟨hbody.1, hbody.2.1, hbody.2.2.1, hbody.2.2.2.1,
            go .skip trivial body hbody.2.2.2.2⟩
    | .annot tag text, _ => by simpa [seqAssoc] using hpre
    | .assign kind name value, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    | .primitive name operator args, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    | .store address value, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    | .store32 address value, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    | .storeByte address value, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    | .break, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    | .continue, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    | .extCall function configuration configurationLength array arrayLength, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    | .raise exception value, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    | .return value, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    | .shMemLoad size kind name address, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    | .shMemStore size address value, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    | .tick, hbody => by
        simp only [seqAssoc]; exact smartSeq_byteRanged pre _ hpre hbody
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
  exact go pre hpre program hprogram

theorem retToTail_byteRanged {width : Nat} (program : Prog (BitVec width))
    (h : ProgByteRanged program) : ProgByteRanged (retToTail program) := by
  let rec go : (program : Prog (BitVec width)) → ProgByteRanged program →
      ProgByteRanged (retToTail program)
    | .skip, _ => by simp [retToTail, ProgByteRanged]
    | .dec name shape value body, hbody => by
        simp only [retToTail]
        exact ⟨hbody.1, hbody.2.1, hbody.2.2.1, go body hbody.2.2.2⟩
    | .seq first second, hbody => by
        simp only [retToTail]
        exact seqCallRet_byteRanged _ ⟨go first hbody.1, go second hbody.2⟩
    | .ite condition thenBranch elseBranch, hbody => by
        simp only [retToTail]
        exact ⟨hbody.1, go thenBranch hbody.2.1, go elseBranch hbody.2.2⟩
    | .while condition body, hbody => by
        simp only [retToTail]
        exact ⟨hbody.1, go body hbody.2⟩
    | .call none function arguments, hbody => by simpa [retToTail] using hbody
    | .call (some (kindOpt, none)) function arguments, hbody => by
        simpa [retToTail] using hbody
    | .call (some (kindOpt, some (eid, vn, handlerProgram))) function arguments, hbody => by
        simp only [retToTail]
        simp only [ProgByteRanged] at hbody ⊢
        exact ⟨hbody.1, hbody.2.1, hbody.2.2.1, hbody.2.2.2.1,
          hbody.2.2.2.2.1, go handlerProgram hbody.2.2.2.2.2⟩
    | .decCall name shape function arguments body, hbody => by
        simp only [retToTail]
        exact ⟨hbody.1, hbody.2.1, hbody.2.2.1, hbody.2.2.2.1,
          go body hbody.2.2.2.2⟩
    | .annot tag text, hbody => by simpa [retToTail] using hbody
    | .assign kind name value, hbody => by simpa [retToTail] using hbody
    | .primitive name operator args, hbody => by simpa [retToTail] using hbody
    | .store address value, hbody => by simpa [retToTail] using hbody
    | .store32 address value, hbody => by simpa [retToTail] using hbody
    | .storeByte address value, hbody => by simpa [retToTail] using hbody
    | .break, hbody => by simpa [retToTail] using hbody
    | .continue, hbody => by simpa [retToTail] using hbody
    | .extCall function configuration configurationLength array arrayLength, hbody => by
        simpa [retToTail] using hbody
    | .raise exception value, hbody => by simpa [retToTail] using hbody
    | .return value, hbody => by simpa [retToTail] using hbody
    | .shMemLoad size kind name address, hbody => by simpa [retToTail] using hbody
    | .shMemStore size address value, hbody => by simpa [retToTail] using hbody
    | .tick, hbody => by simpa [retToTail] using hbody
    termination_by program => sizeOf program
    decreasing_by all_goals decreasing_trivial
  exact go program h

theorem panSimpProg_byteRanged {width : Nat} (program : Prog (BitVec width))
    (h : ProgByteRanged program) : ProgByteRanged (panSimpProg program) := by
  unfold panSimpProg
  exact retToTail_byteRanged _ (seqAssoc_byteRanged .skip program trivial h)

theorem panSimpDecl_byteRanged {width : Nat} (declaration : Decl (BitVec width))
    (h : DeclByteRanged declaration) : DeclByteRanged (panSimpDecl declaration) := by
  cases declaration with
  | function d =>
      simp only [panSimpDecl]
      simp only [DeclByteRanged, FunDeclByteRanged] at h ⊢
      exact ⟨h.1, h.2.1, panSimpProg_byteRanged d.body h.2.2.1, h.2.2.2⟩
  | _ => simpa [panSimpDecl] using h

theorem panSimpDecls_byteRanged {width : Nat} (declarations : List (Decl (BitVec width)))
    (h : ∀ d ∈ declarations, DeclByteRanged d) :
    ∀ d ∈ panSimpDecls declarations, DeclByteRanged d := by
  intro d hd
  rw [panSimpDecls_eq_map] at hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  exact panSimpDecl_byteRanged e (h e he)

end Flapjack
