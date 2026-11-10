/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.ShiftedFunctional

/-! The matrix condition holds throughout the shifted strict sublevel set. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

/-- A sufficiently large scale gives the restricted time derivative and positive semidefinite
Hessian conditions. -/
theorem exists_shifted_interpolation_conditions {p q ρ σ κ ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1) (hρ : |ρ| < 1)
    (hσ : 0 < σ) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ)
    (hκ : 0 < κ) (hε : 0 < ε) (L : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, ε ≤ t → ∀ x : Fin 3 → ℝ,
      x ∈ probabilityBox → (∀ i, |quantileVector x i| ≤ L) →
      interpolationFunctional (tripleTheta p q σ) R ε (t, x) < gaussianCDF (-R * κ) →
      fderiv ℝ (interpolationFunctional (tripleTheta p q σ) R ε) (t, x) (1, 0) ≤ 0 ∧
      (tripleCovariance p q ρ ⊙
          coordinateHessian (fun z => interpolationFunctional (tripleTheta p q σ) R ε (t, z)) x -
        ((Real.exp (2 * t) - 1) *
          fderiv ℝ (interpolationFunctional (tripleTheta p q σ) R ε) (t, x) (1, 0)) •
          interpolationWeightMatrix (tripleInterpolationWeights p q σ) (tripleVariances σ)
            (fun i => gaussianPDFReal 0 1 (gaussianCDFChart.symm (x i)))).PosSemidef := by
  obtain ⟨R, hR, hbase⟩ := exists_time_interpolation_conditions hp hq hsum hρ hσ hvar hκ hε L
  refine ⟨R, hR, ?_⟩
  intro t ht x hx hbound hsub
  have hgap := (interpolationFunctional_sublevel_gap (tripleTheta p q σ) hR.le hκ.le ε t x hsub).le
  rw [quantileLinear_tripleTheta] at hgap
  have h := hbase (t - ε) (sub_nonneg.mpr ht) x hx hbound hgap
  rw [← fderiv_interpolationFunctional_time (tripleTheta p q σ) R hε ht hx] at h
  simpa only [interpolationFunctional, sub_add_cancel] using h


end EhrhardGaussian.Ehrhard

end
