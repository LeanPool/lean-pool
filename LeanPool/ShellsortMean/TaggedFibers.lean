/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import LeanPool.ShellsortMean.FiberEquivalences
public import LeanPool.ShellsortMean.TagThreshold

/-! Rank and position labels for the fibers determined by a tagged rank. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Classify a rank as below, equal to or above the tagged rank. -/
def rankTagLabel {n : ℕ} (m : ℕ) (x : Fin n) : Fin 3 :=
  if x.val < m then 0 else if x.val = m then 1 else 2

/-- Classify a slot as a lower-key slot, the tagged slot or an upper-key slot. -/
def positionTagLabel {n : ℕ} (B : Finset (Fin n)) (i a : Fin n) : Fin 3 :=
  if a ∈ B then 0 else if a = i then 1 else 2

theorem rankTagLabel_zero {n m : ℕ} (x : Fin n) :
    rankTagLabel m x = 0 ↔ x.val < m := by
  unfold rankTagLabel
  split_ifs <;> norm_num <;> omega

theorem rankTagLabel_one {n m : ℕ} (x : Fin n) :
    rankTagLabel m x = 1 ↔ x.val = m := by
  unfold rankTagLabel
  split_ifs <;> norm_num <;> omega

theorem rankTagLabel_two {n m : ℕ} (x : Fin n) :
    rankTagLabel m x = 2 ↔ ¬ x.val < m + 1 := by
  unfold rankTagLabel
  split_ifs <;> norm_num <;> omega

theorem positionTagLabel_zero {n : ℕ} (B : Finset (Fin n)) (i a : Fin n) :
    positionTagLabel B i a = 0 ↔ a ∈ B := by
  unfold positionTagLabel
  split_ifs <;> norm_num <;> tauto

theorem positionTagLabel_one {n : ℕ} (B : Finset (Fin n)) (i a : Fin n)
    (hi : i ∉ B) :
    positionTagLabel B i a = 1 ↔ a = i := by
  unfold positionTagLabel
  split_ifs <;> norm_num <;> aesop

theorem positionTagLabel_two {n : ℕ} (B : Finset (Fin n)) (i a : Fin n) :
    positionTagLabel B i a = 2 ↔ a ∉ insert i B := by
  unfold positionTagLabel
  split_ifs <;> norm_num <;> aesop

theorem rankTagLabel_card_zero {n m : ℕ} (hm : m ≤ n) :
    Fintype.card {x : Fin n // rankTagLabel m x = 0} = m := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (rankTagLabel_zero (m := m))),
    Fintype.card_subtype, Fin.card_filter_val_lt, min_eq_right hm]

theorem rankTagLabel_card_one {n m : ℕ} (hm : m < n) :
    Fintype.card {x : Fin n // rankTagLabel m x = 1} = 1 := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (rankTagLabel_one (m := m))),
    Fintype.card_subtype]
  have hset : (Finset.univ.filter (fun x : Fin n => x.val = m)) = {⟨m, hm⟩} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · exact fun hv => Fin.ext hv
    · exact fun he => congrArg Fin.val he
  rw [hset, Finset.card_singleton]

theorem rankTagLabel_card_two {n m : ℕ} (hm : m < n) :
    Fintype.card {x : Fin n // rankTagLabel m x = 2} = n - 1 - m := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (rankTagLabel_two (m := m))),
    Fintype.card_subtype_compl, Fintype.card_subtype, Fin.card_filter_val_lt]
  simp only [Fintype.card_fin, min_eq_right (Nat.succ_le_of_lt hm)]
  omega

theorem positionTagLabel_card_zero {n : ℕ} (B : Finset (Fin n)) (i : Fin n) :
    Fintype.card {a : Fin n // positionTagLabel B i a = 0} = B.card := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (positionTagLabel_zero B i))]
  exact Fintype.card_coe B

theorem positionTagLabel_card_one {n : ℕ} (B : Finset (Fin n)) (i : Fin n)
    (hi : i ∉ B) :
    Fintype.card {a : Fin n // positionTagLabel B i a = 1} = 1 := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun a => positionTagLabel_one B i a hi))]
  simp

theorem positionTagLabel_card_two {n : ℕ} (B : Finset (Fin n)) (i : Fin n)
    (hi : i ∉ B) :
    Fintype.card {a : Fin n // positionTagLabel B i a = 2} = n - 1 - B.card := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (positionTagLabel_two B i)),
    Fintype.card_subtype_compl, Fintype.card_coe, Finset.card_insert_of_notMem hi]
  simp only [Fintype.card_fin]
  omega

theorem tagged_subset_card_lt {n : ℕ} (B : Finset (Fin n)) (i : Fin n)
    (hi : i ∉ B) : B.card < n := by
  have hc := Finset.card_le_univ (insert i B)
  rw [Finset.card_insert_of_notMem hi, Fintype.card_fin] at hc
  omega

theorem matching_tag_iff {n : ℕ} (p : RankPlacement n) (x : Fin n)
    (B : Finset (Fin n)) (i : Fin n) (hi : i ∉ B) :
    (∀ a, positionTagLabel B i (p a) = rankTagLabel x.val a) ↔
      p x = i ∧ thresholdSet p x.val = B := by
  constructor
  · intro h
    constructor
    · apply (positionTagLabel_one B i (p x) hi).mp
      rw [h x]
      exact (rankTagLabel_one x).mpr rfl
    · ext a
      rw [threshold_mem, ← rankTagLabel_zero (p.symm a),
        ← h (p.symm a), Equiv.apply_symm_apply, positionTagLabel_zero]
  · rintro ⟨howner, hB⟩ a
    have hmem : p a ∈ B ↔ a.val < x.val := by
      rw [← hB, threshold_mem, Equiv.symm_apply_apply]
    unfold rankTagLabel
    split_ifs with hlt heq
    · exact (positionTagLabel_zero B i (p a)).mpr (hmem.mpr hlt)
    · exact (positionTagLabel_one B i (p a) hi).mpr
        ((congrArg p (Fin.ext heq)).trans howner)
    · have hnotB : p a ∉ B := fun ha => hlt (hmem.mp ha)
      have hnoti : p a ≠ i := by
        intro he
        have hax := p.injective (he.trans howner.symm)
        exact heq (congrArg Fin.val hax)
      simp [positionTagLabel, hnotB, hnoti]

/-- Exact finite multiplicity of one persistent tagged state under all permutations.
The tag rank is forced to be the cardinality of its smaller-key position subset. -/
theorem tagged_fiber_card {n : ℕ} (B : Finset (Fin n)) (i : Fin n)
    (hi : i ∉ B) :
    let x : Fin n := ⟨B.card, tagged_subset_card_lt B i hi⟩
    Fintype.card {p : RankPlacement n // p x = i ∧ thresholdSet p B.card = B} =
      B.card.factorial * (n - 1 - B.card).factorial := by
  classical
  dsimp only
  let x : Fin n := ⟨B.card, tagged_subset_card_lt B i hi⟩
  have hm : B.card < n := tagged_subset_card_lt B i hi
  have hcard : ∀ r : Fin 3,
      Fintype.card {a : Fin n // rankTagLabel B.card a = r} =
      Fintype.card {a : Fin n // positionTagLabel B i a = r} := by
    intro r
    fin_cases r
    · dsimp only
      exact (rankTagLabel_card_zero (Nat.le_of_lt hm)).trans
        (positionTagLabel_card_zero B i).symm
    · dsimp only
      exact (rankTagLabel_card_one hm).trans (positionTagLabel_card_one B i hi).symm
    · dsimp only
      exact (rankTagLabel_card_two hm).trans (positionTagLabel_card_two B i hi).symm
  have he : matchingEquiv (rankTagLabel B.card) (positionTagLabel B i) ≃
      {p : RankPlacement n // p x = i ∧ thresholdSet p B.card = B} :=
    Equiv.subtypeEquivRight (fun p => matching_tag_iff p x B i hi)
  have hc := matchingEquiv_card (rankTagLabel B.card) (positionTagLabel B i) hcard
  have hp : (∏ r : Fin 3, (Fintype.card {a : Fin n // rankTagLabel B.card a = r}).factorial) =
      B.card.factorial * (n - 1 - B.card).factorial := by
    rw [Fin.prod_univ_three]
    change (Fintype.card {a : Fin n // rankTagLabel B.card a = 0}).factorial *
      (Fintype.card {a : Fin n // rankTagLabel B.card a = 1}).factorial *
      (Fintype.card {a : Fin n // rankTagLabel B.card a = 2}).factorial = _
    rw [rankTagLabel_card_zero (Nat.le_of_lt hm), rankTagLabel_card_one hm,
      rankTagLabel_card_two hm]
    simp
  apply (Fintype.card_congr he).symm.trans
  convert hc.trans hp using 1
  exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)

end Shellsort
end
