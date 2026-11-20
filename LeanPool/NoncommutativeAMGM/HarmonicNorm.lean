/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.HarmonicRaising
public import LeanPool.NoncommutativeAMGM.HarmonicIntersection
public import LeanPool.NoncommutativeAMGM.SliceDifference

/-! # Orthogonality and the slice norm of homogeneous harmonic polynomials -/

@[expose] public section
namespace NoncommutativeAMGM
open scoped BigOperators

theorem sum_homogeneousCoefficient {n k : ℕ} (c : HomogeneousSpace n k)
    (φ : Finset (Fin n) → ℝ) :
    (∑ T : HomogeneousIndex n k, c T * φ T.val) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        homogeneousCoefficient c T * φ T := by
  classical
  rw [Finset.sum_subtype (p := fun T : Finset (Fin n) ↦ T.card = k)
    ((Finset.univ : Finset (Fin n)).powersetCard k)
    (by intro T; simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and])]
  apply Finset.sum_congr rfl
  intro T _
  simp [homogeneousCoefficient, T.property]

theorem slice_homogeneous_product {n j k : ℕ} (s : ℝ)
    (c : HomogeneousSpace n j) (d : HomogeneousSpace n k) :
    sliceFunctional n s (homogeneousPolynomial c * homogeneousPolynomial d) =
      ∑ S : HomogeneousIndex n j, c S *
        ∑ T : HomogeneousIndex n k, d T * sliceMoment n s (j + k - (S.val ∩ T.val).card) := by
  classical
  rw [homogeneousPolynomial_eq_sum c, homogeneousPolynomial_eq_sum d, Finset.sum_mul,
    map_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.mul_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [booleanMonomial_mul, sliceFunctional_monomial, Finset.card_union, S.property, T.property]
  ring

/-- Harmonic polynomials are orthogonal to every homogeneous polynomial of smaller degree. -/
theorem slice_harmonic_orthogonal {n j k : ℕ} (s : ℝ)
    (c : HomogeneousSpace n j) (d : HomogeneousSpace n k)
    (hd : HarmonicCoefficients k (homogeneousCoefficient d)) (hjk : j < k) :
    sliceFunctional n s (homogeneousPolynomial c * homogeneousPolynomial d) = 0 := by
  rw [slice_homogeneous_product]
  apply Finset.sum_eq_zero
  intro S _
  rw [sum_homogeneousCoefficient d (fun R ↦ sliceMoment n s (j + k - (S.val ∩ R).card))]
  have he := harmonic_intersection_weighted_sum_zero (homogeneousCoefficient d) hd S.val
    (by rw [S.property]; exact hjk) (fun R ↦ sliceMoment n s (j + k - R.card))
  rw [he, mul_zero]

/-- The exact diagonal norm factor in equation (28), with no positivity assumption on `s`. -/
theorem slice_harmonic_product {n j : ℕ} (s : ℝ)
    (c d : HomogeneousSpace n j)
    (hd : HarmonicCoefficients j (homogeneousCoefficient d)) (hsize : 2 * j ≤ n) :
    sliceFunctional n s (homogeneousPolynomial c * homogeneousPolynomial d) =
      (falling s j * falling ((n : ℝ) - s) j / falling n (2 * j)) *
        ∑ S : HomogeneousIndex n j, c S * d S := by
  rw [slice_homogeneous_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [sum_homogeneousCoefficient d (fun R ↦ sliceMoment n s (j + j - (S.val ∩ R).card))]
  have he := harmonic_intersection_weighted_sum_top (homogeneousCoefficient d) hd S.val
    S.property (fun R ↦ sliceMoment n s (j + j - R.card))
  rw [he]
  have hweight := powerset_harmonic_weight s S.val (by rwa [S.property])
  simp only [S.property] at hweight
  rw [← two_mul j, hweight]
  simp only [homogeneousCoefficient, dite_eq_left S.property]
  ring

theorem slice_harmonic_square {n j : ℕ} (s : ℝ) (c : HomogeneousSpace n j)
    (hc : HarmonicCoefficients j (homogeneousCoefficient c)) (hsize : 2 * j ≤ n) :
    sliceFunctional n s (homogeneousPolynomial c ^ 2) =
      (falling s j * falling ((n : ℝ) - s) j / falling n (2 * j)) *
        ∑ S : HomogeneousIndex n j, (c S) ^ 2 := by
  simpa only [pow_two] using slice_harmonic_product s c c hc hsize

/-- The orthogonal norm identity for a finite sum of homogeneous harmonic pieces. -/
theorem slice_harmonic_sum_square {n d : ℕ} (s : ℝ)
    (h : (k : ℕ) → HomogeneousSpace n k)
    (hhar : ∀ k, k ≤ d → HarmonicCoefficients k (homogeneousCoefficient (h k)))
    (hsize : 2 * d ≤ n) :
    sliceFunctional n s ((∑ k ∈ Finset.range (d + 1), homogeneousPolynomial (h k)) ^ 2) =
      ∑ k ∈ Finset.range (d + 1),
        (falling s k * falling ((n : ℝ) - s) k / falling n (2 * k)) *
          ∑ S : HomogeneousIndex n k, (h k S) ^ 2 := by
  classical
  rw [pow_two, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j ≤ d := by have := Finset.mem_range.mp hj; omega
  rw [Finset.mul_sum, map_sum, Finset.sum_eq_single j]
  · simpa only [pow_two] using
      slice_harmonic_product s (h j) (h j) (hhar j hjd) (by omega)
  · intro k hk hkj
    have hkd : k ≤ d := by have := Finset.mem_range.mp hk; omega
    rcases lt_or_gt_of_ne hkj with hkj | hjk
    · rw [mul_comm]
      exact slice_harmonic_orthogonal s (h k) (h j) (hhar j hjd) hkj
    · exact slice_harmonic_orthogonal s (h j) (h k) (hhar k hkd) hjk
  · simp [hj]

end NoncommutativeAMGM
