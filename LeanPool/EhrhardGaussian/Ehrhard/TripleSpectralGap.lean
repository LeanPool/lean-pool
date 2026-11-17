/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.TripleCovariance

/-! # An explicit coercivity bound and kernel for the singular triple -/

@[expose] public noncomputable section

open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

/-- A correlated quadratic form dominates one minus the absolute correlation times the Euclidean
squared norm. -/
theorem correlated_quadratic_lower_bound (ρ u v : ℝ) :
    (1 - |ρ|) * (u ^ 2 + v ^ 2) ≤ (u + ρ * v) ^ 2 + (1 - ρ ^ 2) * v ^ 2 := by
  by_cases hρ : 0 ≤ ρ
  · rw [abs_of_nonneg hρ]
    have h := mul_nonneg hρ (sq_nonneg (u + v))
    nlinarith only [h]
  · rw [abs_of_neg (lt_of_not_ge hρ)]
    have h := mul_nonneg (neg_nonneg.mpr (le_of_not_ge hρ)) (sq_nonneg (u - v))
    nlinarith only [h]

/-- The explicit lower bound replaces an abstract positive spectral gap on
the complement of the one-dimensional kernel. -/
theorem tripleHessianMatrix_quadratic_lower_bound (p q σ : ℝ) {ρ : ℝ}
    (hρ : |ρ| ≤ 1) (x : Fin 3 → ℝ) :
    (1 - |ρ|) * min (p ^ 2) (q ^ 2) *
        ((x 0 - σ * x 2) ^ 2 + (x 1 - σ * x 2) ^ 2) ≤
      x ⬝ᵥ (tripleHessianMatrix p q ρ σ *ᵥ x) := by
  let a := x 0 - σ * x 2
  let b := x 1 - σ * x 2
  have hmin : min (p ^ 2) (q ^ 2) * (a ^ 2 + b ^ 2) ≤ (p * a) ^ 2 + (q * b) ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right (min_le_left (p ^ 2) (q ^ 2)) (sq_nonneg a)
    have h₂ := mul_le_mul_of_nonneg_right (min_le_right (p ^ 2) (q ^ 2)) (sq_nonneg b)
    nlinarith only [h₁, h₂]
  calc
    _ ≤ (1 - |ρ|) * ((p * a) ^ 2 + (q * b) ^ 2) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmin (sub_nonneg.mpr hρ)
    _ ≤ (p * a + ρ * (q * b)) ^ 2 + (1 - ρ ^ 2) * (q * b) ^ 2 :=
      correlated_quadratic_lower_bound ρ (p * a) (q * b)
    _ = _ := by rw [tripleHessianMatrix_quadratic]; dsimp only [a, b]; ring

/-- Nonzero input weights and strict correlation give a positive triple Hessian gap constant. -/
theorem tripleHessianMatrix_gap_pos {p q ρ : ℝ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hρ : |ρ| < 1) : 0 < (1 - |ρ|) * min (p ^ 2) (q ^ 2) :=
  mul_pos (sub_pos.mpr hρ) (lt_min (sq_pos_of_ne_zero hp) (sq_pos_of_ne_zero hq))



end EhrhardGaussian.Ehrhard

end
