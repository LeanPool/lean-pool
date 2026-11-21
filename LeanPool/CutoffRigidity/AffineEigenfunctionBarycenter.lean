/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.AffineEigenspace
public import LeanPool.CutoffRigidity.GibbsMoments

/-! # Affine Gibbs eigenfunctions are centered at the barycenter -/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem affineEigenConstant_eq_neg_inner_mean {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (a : affineEigenRows V ρ) :
    affineEigenConstant V ρ a = -inner ℝ (a : E) (∫ x, x ∂gibbsMeasure volume V) := by
  let := hp
  by_cases ha : (a : E) = 0
  · simp [affineEigenConstant, ha]
  · have hm := affine_eigenfunction_mean_zero V (hV.differentiable (by norm_num)) a ha
      (affineEigenConstant V ρ a) ρ hρ (affineEigenRows_eigenfunction V hρ a) hp
    have hi := (gibbs_memLp_two_id_of_hessian_bound hV ρ hρ hHess).integrable (by norm_num)
    rw [integral_add (hi.const_inner (a : E)) (integrable_const _), integral_inner hi,
      integral_const] at hm
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hm
    linarith

end CutoffRigidity
