/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

module

public import LeanPool.NoncommutativeAMGM.Boolean

/-!
# Harmonic coefficient cancellation

For a homogeneous multilinear polynomial of degree `j`, the coefficient of `z_R`
in its Laplacian is the sum of coefficients over `j`-sets containing `R`, where
`|R| = j-1`. This file uses these coefficient equations as the definition of
harmonicity, and proves their consequence for every smaller set (Lemma C.2).
-/

@[expose] public section

namespace NoncommutativeAMGM

open scoped BigOperators

/-- Sum of homogeneous degree-`j` coefficients over the supersets of `R`. -/
noncomputable def homogeneousUpperSum {n : ℕ} (j : ℕ) (c : Finset (Fin n) → ℝ)
    (R : Finset (Fin n)) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard j, if R ⊆ S then c S else 0

/-- The equations for the Laplacian of a homogeneous multilinear polynomial to vanish. -/
def HarmonicCoefficients {n : ℕ} (j : ℕ) (c : Finset (Fin n) → ℝ) : Prop :=
  ∀ R : Finset (Fin n), R.card + 1 = j → homogeneousUpperSum j c R = 0

/-- Counting the ways to extend `R` by one element inside a fixed `j`-set. -/
theorem homogeneousUpperSum_step {n : ℕ} (j : ℕ) (c : Finset (Fin n) → ℝ)
    (R : Finset (Fin n)) :
    ∑ i ∈ (Finset.univ \ R), homogeneousUpperSum j c (insert i R) =
      ((j : ℝ) - R.card) * homogeneousUpperSum j c R := by
  classical
  unfold homogeneousUpperSum
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hcS : S.card = j := (Finset.mem_powersetCard.mp hS).2
  by_cases hRS : R ⊆ S
  · simp only [Finset.insert_subset_iff, hRS, and_true]
    have hfilter : (Finset.univ \ R).filter (fun i ↦ i ∈ S) = S \ R := by
      ext i
      simp [and_comm]
    rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul]
    have hcard : R.card ≤ j := by simpa [hcS] using Finset.card_le_card hRS
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hRS, hcS, Nat.cast_sub hcard]
    simp
  · have hnot (i : Fin n) : ¬insert i R ⊆ S := by
      intro h
      exact hRS ((Finset.subset_insert i R).trans h)
    simp [hnot, hRS]

/-- Lemma C.2: the top-level harmonic equations imply cancellation over every proper subset. -/
theorem harmonicCoefficients_upperSum_zero {n : ℕ} (j : ℕ) (c : Finset (Fin n) → ℝ)
    (hc : HarmonicCoefficients j c) (R : Finset (Fin n)) (hR : R.card < j) :
    homogeneousUpperSum j c R = 0 := by
  classical
  by_cases hbase : R.card + 1 = j
  · exact hc R hbase
  have hz : (∑ i ∈ (Finset.univ \ R), homogeneousUpperSum j c (insert i R)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiR : i ∉ R := (Finset.mem_sdiff.mp hi).2
    have hcard : (insert i R).card = R.card + 1 := Finset.card_insert_of_notMem hiR
    exact harmonicCoefficients_upperSum_zero j c hc (insert i R) (by omega)
  have hstep := homogeneousUpperSum_step j c R
  rw [hz] at hstep
  have hpos : (0 : ℝ) < (j : ℝ) - R.card := by
    have : (R.card : ℝ) < j := by exact_mod_cast hR
    linarith
  exact (mul_eq_zero.mp hstep.symm).resolve_left hpos.ne'
termination_by j - R.card
decreasing_by
  omega

end NoncommutativeAMGM
