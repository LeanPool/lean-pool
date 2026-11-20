/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.CosineGridFold
public import LeanPool.NoncommutativeAMGM.RootCoefficientExtraction

/-! # Cosine parity quadratures and the normalized Chebyshev interpolation weights -/

@[expose] public section
namespace NoncommutativeAMGM
open Polynomial
open scoped BigOperators

/-- Positive quadrature on one parity of the Chebyshev extrema. -/
noncomputable def cosineParityQuadrature (m s : ℕ) (F : ℝ → ℝ) : ℝ :=
  (2 / (m : ℝ)) * ∑ j ∈ Finset.range (m + 1), cosineEndpointFactor m j *
    (if j % 2 = s then F (chebyshevNode m j) else 0)

theorem rootRealAverage_cosine_even {m : ℕ} (hm : 0 < m) (F : ℝ → ℝ) :
    rootRealAverage m 1 (cosineRoot m) (fun z ↦ F z.re) = cosineParityQuadrature m 0 F := by
  unfold rootRealAverage cosineParityQuadrature
  simp only [one_mul, cosineRoot_pow_re]
  have he := cosine_grid_parity_fold hm F 0 (by decide)
  simp only [Nat.add_zero] at he
  rw [he]
  ring

theorem rootRealAverage_cosine_odd {m : ℕ} (hm : 0 < m) (F : ℝ → ℝ) :
    rootRealAverage m (cosineHalfRoot m) (cosineRoot m) (fun z ↦ F z.re) =
      cosineParityQuadrature m 1 F := by
  unfold rootRealAverage cosineParityQuadrature
  simp only [cosineHalfRoot_mul_pow_re]
  rw [cosine_grid_parity_fold hm F 1 (by decide)]
  ring

/-- The normalized signed interpolation weights, including half-weight endpoints. -/
noncomputable def chebyshevWeight (m j : ℕ) : ℝ :=
  ((-1 : ℝ) ^ j / m) * cosineEndpointFactor m j

theorem cosineParity_difference (m : ℕ) (F : ℝ → ℝ) :
    cosineParityQuadrature m 0 F - cosineParityQuadrature m 1 F =
      2 * ∑ j ∈ Finset.range (m + 1), chebyshevWeight m j * F (chebyshevNode m j) := by
  have hterm (j : ℕ) :
      cosineEndpointFactor m j * (if j % 2 = 0 then F (chebyshevNode m j) else 0) -
        cosineEndpointFactor m j * (if j % 2 = 1 then F (chebyshevNode m j) else 0) =
          (-1 : ℝ) ^ j * cosineEndpointFactor m j * F (chebyshevNode m j) := by
    rw [neg_one_pow_eq_pow_mod_two]
    rcases Nat.mod_two_eq_zero_or_one j with he | he <;> simp [he]
  unfold cosineParityQuadrature
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [hterm]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold chebyshevWeight
  ring

/-- The normalized cosine weights extract the top coefficient of every polynomial
of degree at most `m`. -/
theorem chebyshevWeight_extracts {m : ℕ} (hm : 0 < m) (p : Polynomial ℝ) (hp : p.natDegree ≤ m) :
    (∑ j ∈ Finset.range (m + 1), chebyshevWeight m j * p.eval (chebyshevNode m j)) =
      p.coeff m / (2 : ℝ) ^ (m - 1) := by
  have he := rootPolynomialAverage_difference hm (cosineRoot_primitive hm)
    (show (1 : ℂ) ^ m = 1 by simp) (cosineHalfRoot_pow hm) p hp
  rw [rootPolynomialAverage_apply, rootPolynomialAverage_apply,
    rootRealAverage_cosine_even hm (fun t ↦ p.eval t),
    rootRealAverage_cosine_odd hm (fun t ↦ p.eval t), cosineParity_difference] at he
  linear_combination (1 / 2 : ℝ) * he

theorem chebyshevWeight_zero (m : ℕ) : chebyshevWeight m 0 = 1 / (2 * (m : ℝ)) := by
  unfold chebyshevWeight cosineEndpointFactor
  simp only [pow_zero, true_or, ite_true]
  ring

theorem chebyshevWeight_last (m : ℕ) : chebyshevWeight m m = (-1 : ℝ) ^ m / (2 * (m : ℝ)) := by
  unfold chebyshevWeight cosineEndpointFactor
  simp only [or_true, ite_true]
  ring

theorem chebyshevWeight_interior {m j : ℕ} (hj : 0 < j) (hjm : j < m) :
    chebyshevWeight m j = (-1 : ℝ) ^ j / m := by
  simp [chebyshevWeight, cosineEndpointFactor, ne_of_gt hj, ne_of_lt hjm]

end NoncommutativeAMGM
