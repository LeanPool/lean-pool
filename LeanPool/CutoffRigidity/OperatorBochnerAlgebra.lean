/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EuclideanBochner

/-! # Finite algebra for weak Bochner localization

The vectors and Hessian entries here may be genuine weak derivatives.
No classical representative is needed for either contraction or Young's
inequality. These are the pointwise algebraic steps in the cutoff proof.
-/

public section

namespace CutoffRigidity

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The boundary cross term is absorbed by half the Hessian energy. -/
theorem weak_bochner_boundary_young (η : ℝ) (g b : E)
    (H : Fin d → Fin d → ℝ) :
    -(∑ i : Fin d, ∑ j : Fin d, 2 * η * b j * g i * H i j) ≤
      (1 / 2 : ℝ) * η ^ 2 * (∑ i : Fin d, ∑ j : Fin d, (H i j) ^ 2) +
        2 * ‖b‖ ^ 2 * ‖g‖ ^ 2 := by
  have hp (i j : Fin d) : -(2 * η * b j * g i * H i j) ≤
      (1 / 2 : ℝ) * η ^ 2 * (H i j) ^ 2 + 2 * (g i) ^ 2 * (b j) ^ 2 := by
    nlinarith [sq_nonneg (η * H i j + 2 * g i * b j)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  have hfactor : (∑ i : Fin d, ∑ j : Fin d, 2 * (g i) ^ 2 * (b j) ^ 2) =
      2 * ‖b‖ ^ 2 * ‖g‖ ^ 2 := by
    simp only [← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib] at hs
  rw [hfactor] at hs
  simp only [← Finset.mul_sum] at hs
  exact hs

/-- The localized curvature/energy estimate after the weak Bochner identity. -/
theorem weak_bochner_pointwise_absorption (η rate ρ : ℝ) (g b : E)
    (H : Fin d → Fin d → ℝ) (Q : ℝ) (hQ : ρ * ‖g‖ ^ 2 ≤ Q) :
    (1 / 2 : ℝ) * η ^ 2 * (∑ i : Fin d, ∑ j : Fin d, (H i j) ^ 2) +
        (ρ - rate) * η ^ 2 * ‖g‖ ^ 2 ≤
      η ^ 2 * (∑ i : Fin d, ∑ j : Fin d, (H i j) ^ 2) +
        η ^ 2 * Q - rate * η ^ 2 * ‖g‖ ^ 2 +
        (∑ i : Fin d, ∑ j : Fin d, 2 * η * b j * g i * H i j) +
        2 * ‖b‖ ^ 2 * ‖g‖ ^ 2 := by
  have hy := weak_bochner_boundary_young η g b H
  have hc := mul_le_mul_of_nonneg_left hQ (sq_nonneg η)
  nlinarith

end CutoffRigidity
