/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/CodingGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.CodingDiagonal

/-!
# Coding Generic
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CodingGeneric
open CodingForcing CodingColumns CodingDiagonal

def Dense (A : ℕ → Oracle) (R : Condition → Prop) : Prop :=
  ∀ p, ∃ q, Extends A p q ∧ R q

theorem extend_dense (A : ℕ → Oracle) (R : Condition → Prop)
    (hR : Dense A R) (p : Condition) (n : ℕ) :
    ∃ q, Extends A p q ∧ R q ∧ n < q.active ∧ n < q.left.length := by
  obtain ⟨r, hpr, hn⟩ := length_dense A p (n+1)
  obtain ⟨s, hrs, ha⟩ := active_dense A r n
  obtain ⟨q, hsq, hRq⟩ := hR s
  exact ⟨q, extends_trans hpr (extends_trans hrs hsq), hRq,
    ha.trans_le hsq.2.2.1,
    (Nat.lt_succ_self n).trans_le (hn.trans (hrs.1.length_le.trans hsq.1.length_le))⟩

noncomputable def stage (A : ℕ → Oracle) (R : ℕ → Condition → Prop)
    (hR : ∀ n, Dense A (R n)) : ℕ → Condition
  | 0 => ⟨[], [], rfl, 0⟩
  | n+1 => Classical.choose (extend_dense A (R n) (hR n) (stage A R hR n) n)

theorem stage_spec (A : ℕ → Oracle) (R : ℕ → Condition → Prop)
    (hR : ∀ n, Dense A (R n)) (n : ℕ) :
    Extends A (stage A R hR n) (stage A R hR (n+1)) ∧
      R n (stage A R hR (n+1)) ∧ n < (stage A R hR (n+1)).active ∧
        n < (stage A R hR (n+1)).left.length :=
  Classical.choose_spec (extend_dense A (R n) (hR n) (stage A R hR n) n)

theorem stage_mono (A : ℕ → Oracle) (R : ℕ → Condition → Prop)
    (hR : ∀ n, Dense A (R n)) {m n : ℕ} (h : m ≤ n) :
    Extends A (stage A R hR m) (stage A R hR n) := by
  induction h with
  | refl => exact extends_refl A _
  | step h ih => exact extends_trans ih (stage_spec A R hR _).1

noncomputable def leftReal (A : ℕ → Oracle) (R : ℕ → Condition → Prop)
    (hR : ∀ n, Dense A (R n)) : Oracle := fun n => (stage A R hR (n+1)).left.getD n false
noncomputable def rightReal (A : ℕ → Oracle) (R : ℕ → Condition → Prop)
    (hR : ∀ n, Dense A (R n)) : Oracle := fun n => (stage A R hR (n+1)).right.getD n false

theorem leftReal_extends (A : ℕ → Oracle) (R : ℕ → Condition → Prop)
    (hR : ∀ n, Dense A (R n)) (s n : ℕ) (hn : n < (stage A R hR s).left.length) :
    leftReal A R hR n = (stage A R hR s).left.getD n false := by
  unfold leftReal
  by_cases h : s ≤ n+1
  · exact getD_of_prefix (stage_mono A R hR h).1 hn
  · exact (getD_of_prefix (stage_mono A R hR (Nat.le_of_not_ge h)).1
      (stage_spec A R hR n).2.2.2).symm

theorem rightReal_extends (A : ℕ → Oracle) (R : ℕ → Condition → Prop)
    (hR : ∀ n, Dense A (R n)) (s n : ℕ) (hn : n < (stage A R hR s).left.length) :
    rightReal A R hR n = (stage A R hR s).right.getD n false := by
  unfold rightReal
  by_cases h : s ≤ n+1
  · exact getD_of_prefix (stage_mono A R hR h).2.1 (by simpa [← Condition.sameLength] using hn)
  · exact (getD_of_prefix (stage_mono A R hR (Nat.le_of_not_ge h)).2.1
      (by simpa [← Condition.sameLength] using (stage_spec A R hR n).2.2.2)).symm

theorem coding_agreement (A : ℕ → Oracle) (R : ℕ → Condition → Prop)
    (hR : ∀ n, Dense A (R n)) (s m : ℕ)
    (hm : CodingLocation A (stage A R hR s) m) :
    leftReal A R hR m = rightReal A R hR m := by
  let t := max s (m+1)
  have hst := stage_mono A R hR (Nat.le_max_left s (m+1))
  have hmt := stage_mono A R hR (Nat.le_max_right s (m+1))
  have hlen : m < (stage A R hR t).left.length :=
    (stage_spec A R hR m).2.2.2.trans_le hmt.1.length_le
  rw [leftReal_extends A R hR t m hlen, rightReal_extends A R hR t m hlen]
  exact hst.2.2.2 m hm hlen

abbrev RequirementIndex := ℕ × ℕ × OracleCode

def requirements (A : ℕ → Oracle) (hA : ∀ k, {a | A k a = true}.Infinite)
    (n : ℕ) (p : Condition) : Prop :=
  match Encodable.decode (α := RequirementIndex) n with
  | none => True
  | some (k, cutoff, e) => Diagonal A hA k cutoff e p

theorem requirements_dense (A : ℕ → Oracle) (hA : ∀ k, {a | A k a = true}.Infinite)
    (n : ℕ) : Dense A (requirements A hA n) := by
  intro p
  unfold requirements
  cases hd : Encodable.decode (α := RequirementIndex) n with
  | none => exact ⟨p, extends_refl A p, trivial⟩
  | some v => exact diagonal_dense A hA v.1 v.2.1 v.2.2 p

theorem readColumn_not_reduces (A : ℕ → Oracle) (hA : ∀ k, {a | A k a = true}.Infinite)
    (k cutoff : ℕ) :
    ¬ Reduces (readColumn (A k) (hA k) k cutoff
      (leftReal A (requirements A hA) (requirements_dense A hA))) (A k) := by
  intro h
  obtain ⟨e, he⟩ := OracleCode.turingReducible_iff_exists_code _ _ |>.mp h
  let i := Encodable.encode (k, cutoff, e)
  have hd := (stage_spec A (requirements A hA) (requirements_dense A hA) i).2.1
  have hd' : Diagonal A hA k cutoff e
      (stage A (requirements A hA) (requirements_dense A hA) (i+1)) := by
    simpa [requirements, i] using hd
  obtain ⟨n, hn, hne⟩ := hd'
  apply hne
  rw [he]
  change Part.some (if leftReal A (requirements A hA) (requirements_dense A hA)
    (location (A k) (hA k) k cutoff n) then 1 else 0) = _
  rw [leftReal_extends A (requirements A hA) (requirements_dense A hA) (i+1) _ hn]

theorem common_noncomputable_columns (A : ℕ → Oracle)
    (hA : ∀ k, {a | A k a = true}.Infinite) :
    ∃ G₀ G₁ : Oracle, ∀ k, ∃ C : Oracle,
      Reduces C (join G₀ (A k)) ∧ Reduces C (join G₁ (A k)) ∧ ¬ Reduces C (A k) := by
  let R := requirements A hA
  let hR := requirements_dense A hA
  let G₀ := leftReal A R hR
  let G₁ := rightReal A R hR
  refine ⟨G₀, G₁, ?_⟩
  intro k
  let p := stage A R hR (k+1)
  let cutoff := p.left.length
  let C := readColumn (A k) (hA k) k cutoff G₀
  have heq : C = readColumn (A k) (hA k) k cutoff G₁ := by
    funext n
    apply coding_agreement A R hR (k+1)
    have hm := location_mem (A k) (hA k) k cutoff n
    simp only [column] at hm
    split at hm
    next h =>
      refine ⟨h.1, ?_, ?_⟩
      · rw [h.2]
        exact (stage_spec A R hR k).2.2.1
      · simpa only [h.2] using hm
    next h => simp at hm
  exact ⟨C, readColumn_reduces _ _ _ _ _, heq ▸ readColumn_reduces _ _ _ _ _,
    readColumn_not_reduces A hA k cutoff⟩

theorem coding_first_clause (A : ℕ → Oracle) :
    ∃ G₀ G₁ : Oracle, ∀ k, ∃ C : Oracle,
      Reduces C (join G₀ (A k)) ∧ Reduces C (join G₁ (A k)) ∧ ¬ Reduces C (A k) := by
  let B := fun k => Introreducible.prefixSet (A k)
  obtain ⟨G₀, G₁, h⟩ := common_noncomputable_columns B
    (fun k => Introreducible.prefixSet_infinite (A k))
  refine ⟨G₀, G₁, ?_⟩
  intro k
  obtain ⟨C, h₀, h₁, hn⟩ := h k
  have hBA := Introreducible.prefixSet_reduces (A k)
  have hAB := ((degree_eq_iff _ _).mp (Introreducible.prefixSet_degree (A k))).2
  exact ⟨C, reduces_trans h₀ (join_mono (reduces_refl G₀) hBA),
    reduces_trans h₁ (join_mono (reduces_refl G₁) hBA), fun hCA => hn (reduces_trans hCA hAB)⟩

end TuringRigidity.CodingGeneric

end OAI
