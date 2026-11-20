/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.HarmonicCoefficients

/-! # Harmonic coefficient sums with selected and excluded indices -/

@[expose] public section
namespace NoncommutativeAMGM
open scoped BigOperators

/-- Sum of homogeneous coefficients containing `R` and avoiding `U`. -/
noncomputable def excludedUpperSum {n : ℕ} (j : ℕ) (c : Finset (Fin n) → ℝ)
    (R U : Finset (Fin n)) : ℝ :=
  ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
    if R ⊆ T ∧ Disjoint U T then c T else 0

theorem excludedUpperSum_empty {n : ℕ} (j : ℕ) (c : Finset (Fin n) → ℝ)
    (R : Finset (Fin n)) : excludedUpperSum j c R ∅ = homogeneousUpperSum j c R := by
  classical
  simp [excludedUpperSum, homogeneousUpperSum]

theorem excludedUpperSum_insert {n : ℕ} (j : ℕ) (c : Finset (Fin n) → ℝ)
    (R U : Finset (Fin n)) (i : Fin n) :
    excludedUpperSum j c R (insert i U) =
      excludedUpperSum j c R U - excludedUpperSum j c (insert i R) U := by
  classical
  simp only [excludedUpperSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hRT : R ⊆ T <;> by_cases hiT : i ∈ T <;> by_cases hUT : Disjoint U T <;>
    simp [Finset.disjoint_insert_left, Finset.insert_subset_iff, hRT, hiT, hUT]

/-- Inclusion-exclusion for the actual homogeneous coefficient sums. -/
theorem excludedUpperSum_expansion {n : ℕ} (j : ℕ) (c : Finset (Fin n) → ℝ)
    (R U : Finset (Fin n)) :
    excludedUpperSum j c R U = ∑ V ∈ U.powerset,
      (-1 : ℝ) ^ V.card * homogeneousUpperSum j c (R ∪ V) := by
  classical
  induction U using Finset.induction_on generalizing R with
  | empty => simp [excludedUpperSum_empty]
  | @insert i U hi ih =>
    rw [excludedUpperSum_insert, ih, ih, Finset.sum_powerset_insert hi,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro V hV
    have hiV : i ∉ V := fun h ↦ hi ((Finset.mem_powerset.mp hV) h)
    rw [Finset.card_insert_of_notMem hiV, pow_succ]
    rw [show R ∪ insert i V = insert i R ∪ V by ext a; simp]
    ring

/-- Harmonic coefficients cancel even after specifying any pattern on fewer than `j` indices. -/
theorem harmonic_excludedUpperSum_zero {n j : ℕ} (c : Finset (Fin n) → ℝ)
    (hc : HarmonicCoefficients j c) (R U : Finset (Fin n))
    (hsize : (R ∪ U).card < j) : excludedUpperSum j c R U = 0 := by
  rw [excludedUpperSum_expansion]
  apply Finset.sum_eq_zero
  intro V hV
  have hle : (R ∪ V).card ≤ (R ∪ U).card :=
    Finset.card_le_card (Finset.union_subset_union_right (Finset.mem_powerset.mp hV))
  rw [harmonicCoefficients_upperSum_zero j c hc _ (hle.trans_lt hsize), mul_zero]

theorem intersection_eq_iff_pattern {n : ℕ} (S R T : Finset (Fin n)) (hRS : R ⊆ S) :
    S ∩ T = R ↔ R ⊆ T ∧ Disjoint (S \ R) T := by
  classical
  constructor
  · intro he
    constructor
    · rw [← he]
      exact Finset.inter_subset_right
    · rw [Finset.disjoint_left]
      intro i hi hiT
      have hiR : i ∈ R := he ▸ Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hi).1, hiT⟩
      exact (Finset.mem_sdiff.mp hi).2 hiR
  · rintro ⟨hRT, hd⟩
    ext i
    constructor
    · intro hi
      by_contra hiR
      exact Finset.disjoint_left.mp hd (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hi).1,
        hiR⟩) (Finset.mem_inter.mp hi).2
    · intro hi
      exact Finset.mem_inter.mpr ⟨hRS hi, hRT hi⟩

theorem intersection_weighted_sum {n : ℕ} (j : ℕ) (c : Finset (Fin n) → ℝ)
    (S : Finset (Fin n)) (φ : Finset (Fin n) → ℝ) :
    (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard j, c T * φ (S ∩ T)) =
      ∑ R ∈ S.powerset, φ R * excludedUpperSum j c R (S \ R) := by
  classical
  calc
    _ = ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        ∑ R ∈ S.powerset, if S ∩ T = R then c T * φ R else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      simp [Finset.inter_subset_left]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro R hR
      rw [excludedUpperSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      simp only [intersection_eq_iff_pattern S R T (Finset.mem_powerset.mp hR)]
      split_ifs <;> ring

/-- A harmonic coefficient vector annihilates every function of the intersection
with a set of strictly smaller size. No interpolation hypothesis is needed. -/
theorem harmonic_intersection_weighted_sum_zero {n j : ℕ} (c : Finset (Fin n) → ℝ)
    (hc : HarmonicCoefficients j c) (S : Finset (Fin n)) (hS : S.card < j)
    (φ : Finset (Fin n) → ℝ) :
    (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard j, c T * φ (S ∩ T)) = 0 := by
  rw [intersection_weighted_sum]
  apply Finset.sum_eq_zero
  intro R hR
  have hunion : R ∪ (S \ R) = S := by
    ext i
    have hRS := Finset.mem_powerset.mp hR
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hi | ⟨hi, _⟩)
      · exact hRS hi
      · exact hi
    · intro hi
      by_cases hiR : i ∈ R
      · exact Or.inl hiR
      · exact Or.inr ⟨hi, hiR⟩
  rw [harmonic_excludedUpperSum_zero c hc R (S \ R) (by rwa [hunion]), mul_zero]

theorem homogeneousUpperSum_self {n j : ℕ} (c : Finset (Fin n) → ℝ)
    (S : Finset (Fin n)) (hS : S.card = j) : homogeneousUpperSum j c S = c S := by
  classical
  unfold homogeneousUpperSum
  rw [Finset.sum_eq_single S]
  · simp
  · intro T hT hTS
    have hTcard := (Finset.mem_powersetCard.mp hT).2
    rw [ite_eq_right]
    intro hST
    exact hTS (Finset.eq_of_subset_of_card_le hST (by omega)).symm
  · simp [Finset.mem_powersetCard, hS]

/-- On a full-degree set, harmonicity determines every intersection-pattern mass. -/
theorem harmonic_excludedUpperSum_top {n j : ℕ} (c : Finset (Fin n) → ℝ)
    (hc : HarmonicCoefficients j c) (S R : Finset (Fin n))
    (hS : S.card = j) (hRS : R ⊆ S) :
    excludedUpperSum j c R (S \ R) = (-1 : ℝ) ^ (j - R.card) * c S := by
  classical
  have hunion : R ∪ (S \ R) = S := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hi | ⟨hi, _⟩)
      · exact hRS hi
      · exact hi
    · intro hi
      by_cases hiR : i ∈ R
      · exact Or.inl hiR
      · exact Or.inr ⟨hi, hiR⟩
  rw [excludedUpperSum_expansion, Finset.sum_eq_single (S \ R)]
  · rw [hunion, homogeneousUpperSum_self c S hS,
      Finset.card_sdiff_of_subset hRS, hS]
  · intro V hV hne
    have hVU : V ⊆ S \ R := Finset.mem_powerset.mp hV
    have hsub : R ∪ V ⊆ S := Finset.union_subset hRS
      (hVU.trans Finset.sdiff_subset)
    have hneq : R ∪ V ≠ S := by
      intro he
      apply hne
      apply Finset.Subset.antisymm hVU
      intro i hi
      have hiS := (Finset.mem_sdiff.mp hi).1
      rw [← he, Finset.mem_union] at hiS
      exact hiS.resolve_left (Finset.mem_sdiff.mp hi).2
    have hcard : (R ∪ V).card < j := by
      rw [← hS]
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hneq⟩)
    rw [harmonicCoefficients_upperSum_zero j c hc _ hcard, mul_zero]
  · simp

theorem harmonic_intersection_weighted_sum_top {n j : ℕ} (c : Finset (Fin n) → ℝ)
    (hc : HarmonicCoefficients j c) (S : Finset (Fin n)) (hS : S.card = j)
    (φ : Finset (Fin n) → ℝ) :
    (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard j, c T * φ (S ∩ T)) =
      c S * ∑ R ∈ S.powerset, (-1 : ℝ) ^ (j - R.card) * φ R := by
  rw [intersection_weighted_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R hR
  rw [harmonic_excludedUpperSum_top c hc S R hS (Finset.mem_powerset.mp hR)]
  ring

end NoncommutativeAMGM
