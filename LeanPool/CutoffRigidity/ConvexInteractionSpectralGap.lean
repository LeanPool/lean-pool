/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.ConvexInteractionSpectral
public import LeanPool.CutoffRigidity.GibbsOperatorCurvatureGap

/-! # Exact actual first spectral gap for convex invariant interactions

The coordinate sum gives an actual operator eigenvalue equal to the
quadratic confinement rate. The weak Bochner curvature bound gives the
opposite spectral inequality, proving the precise first gap in Section 3.5.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ} {ρ : ℝ} {W : EuclideanSpace ℝ (Fin d) → ℝ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "V" => (fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x)

/-- The true self-adjoint first gap equals the confinement rate for the
paper's convex diagonally invariant interaction. -/
theorem convexInteraction_spectralGap_eq (hd : 0 < d)
    (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ Set.univ W) (hρ : 0 < ρ)
    (hinv : ∀ x : E, ∀ t : ℝ, W (x + t • diagonalDirection d) = W x)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hV : ContDiff ℝ 2 V) : gibbsSpectralGap hV hp = ρ := by
  have hHess := hessian_quadratic_add_convex_lower hW hconv ρ
  apply le_antisymm
  · obtain ⟨u, hu⟩ := diagonal_interaction_has_operator_eigenvector hd hW hρ hinv hp hV
    exact gibbsSpectralGap_le_positive_eigenvalue hV hp hd ρ hρ hHess ρ hρ u hu
  · exact gibbsSpectralGap_ge_curvature hV hp hd ρ hρ hHess

/-- After the source's additive normalization the exact spectral gap is
proved without any probability, partition-integral or spectral assumption. -/
theorem normalized_convexInteraction_spectralGap_eq (hd : 0 < d)
    (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ Set.univ W) (hρ : 0 < ρ)
    (hinv : ∀ x : E, ∀ t : ℝ, W (x + t • diagonalDirection d) = W x) :
    let Z := ∫ x : E, Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x))
    let Vn := fun x : E => ρ / 2 * ‖x‖ ^ 2 + (W x + Real.log Z)
    ∃ (hVn : ContDiff ℝ 2 Vn)
      (hp : IsProbabilityMeasure (gibbsMeasure volume Vn)),
      gibbsSpectralGap hVn hp = ρ := by
  intro Z Vn
  obtain ⟨hVn, hp, _, _⟩ := normalized_convexInteraction_has_operator_eigenvector hd hW hconv hρ
    hinv
  refine ⟨hVn, hp, ?_⟩
  apply convexInteraction_spectralGap_eq hd (hW.add contDiff_const) (hconv.add_const _) hρ
    (fun x t => by rw [hinv]) hp hVn

end CutoffRigidity
