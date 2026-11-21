/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorAffineRepresentative
public import LeanPool.CutoffRigidity.GibbsSpectralPoincare

/-! # The actual first Gibbs eigenspace at the curvature bound -/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The proved identification is an isometry for the actual Gibbs L² norm. -/
@[expose] noncomputable def operatorEigenClassicalIsometry {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    gibbsOperatorEigenspace hV hp ρ ≃ₗᵢ[ℝ] classicalL2Eigenspace V ρ :=
  LinearIsometryEquiv.ofEq _ _ (gibbsOperatorEigenspace_eq_classicalL2Eigenspace hV hp ρ hρ hHess)

theorem operatorEigenClassicalIsometry_coe {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsOperatorEigenspace hV hp ρ) :
    (operatorEigenClassicalIsometry hV hp ρ hρ hHess u : E →₂[gibbsMeasure volume V] ℝ) = u := rfl

theorem operatorEigenspace_finiteDimensional {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    FiniteDimensional ℝ (gibbsOperatorEigenspace hV hp ρ) := by
  let := classicalL2Eigenspace_finiteDimensional hV ρ hρ hHess
  exact FiniteDimensional.of_injective
    (operatorEigenClassicalIsometry hV hp ρ hρ hHess).toLinearMap
    (operatorEigenClassicalIsometry hV hp ρ hρ hHess).injective

theorem operatorEigenspace_finrank_eq_classical {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    Module.finrank ℝ (gibbsOperatorEigenspace hV hp ρ) = Module.finrank ℝ (classicalL2Eigenspace V
      ρ) :=
  (operatorEigenClassicalIsometry hV hp ρ hρ hHess).toLinearEquiv.finrank_eq

theorem operatorEigenspace_finrank_le {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    Module.finrank ℝ (gibbsOperatorEigenspace hV hp ρ) ≤ d := by
  rw [operatorEigenspace_finrank_eq_classical hV hp ρ hρ hHess]
  exact classicalL2Eigenspace_finrank_le hV ρ hρ hHess

/-- The genuine first eigenspace of the self-adjoint Gibbs operator is
taken at its canonical attained positive spectral gap. -/
@[expose] noncomputable def gibbsFirstEigenspace {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Submodule ℝ (E →₂[gibbsMeasure volume V] ℝ) :=
  gibbsOperatorEigenspace hV hp (gibbsSpectralGap hV hp)

/-- Identify the first eigenspace with the rate-`ρ` eigenspace when the spectral gap equals `ρ`.
-/
@[expose] noncomputable def firstEigenCurvatureIsometry {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hgap : gibbsSpectralGap hV hp = ρ) :
    gibbsFirstEigenspace hV hp ≃ₗᵢ[ℝ] gibbsOperatorEigenspace hV hp ρ :=
  LinearIsometryEquiv.ofEq _ _ (congrArg (gibbsOperatorEigenspace hV hp) hgap)

theorem firstEigenspace_finrank_eq_operator {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hgap : gibbsSpectralGap hV hp = ρ) :
    Module.finrank ℝ (gibbsFirstEigenspace hV hp) =
      Module.finrank ℝ (gibbsOperatorEigenspace hV hp ρ) :=
  (firstEigenCurvatureIsometry hV hp ρ hgap).toLinearEquiv.finrank_eq

theorem firstEigenspace_finiteDimensional {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) :
    FiniteDimensional ℝ (gibbsFirstEigenspace hV hp) := by
  let := operatorEigenspace_finiteDimensional hV hp ρ hρ hHess
  exact FiniteDimensional.of_injective (firstEigenCurvatureIsometry hV hp ρ hgap).toLinearMap
    (firstEigenCurvatureIsometry hV hp ρ hgap).injective

theorem firstEigenspace_finrank_pos {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) :
    0 < Module.finrank ℝ (gibbsFirstEigenspace hV hp) := by
  let := firstEigenspace_finiteDimensional hV hp ρ hρ hHess hgap
  exact Module.finrank_pos_iff_exists_ne_zero.mpr
    (gibbsSpectralGap_hasEigenvector hV hp hd ρ hρ hHess)

theorem firstEigenspace_finrank_le {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ) :
    Module.finrank ℝ (gibbsFirstEigenspace hV hp) ≤ d := by
  rw [firstEigenspace_finrank_eq_operator hV hp ρ hgap]
  exact operatorEigenspace_finrank_le hV hp ρ hρ hHess

end CutoffRigidity
