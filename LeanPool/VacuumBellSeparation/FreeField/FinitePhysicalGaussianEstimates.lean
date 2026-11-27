/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FinitePhysicalRenyiEffects
public import LeanPool.VacuumBellSeparation.Gaussian.DensityRenyiCovariance

/-!
# Gaussian quantitative estimates on the actual finite physical observables

Both comparison directions use the actual fixed density and reference.
The covariance bound controls the original complex vacuum covariance of
arbitrary bounded contractions. The remaining hypotheses concern the
literal intrinsic covariance perturbation, not representation existence.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian
open scoped InnerProductSpace ENNReal Matrix.Norms.L2Operator

variable {m : ℝ} {hm : 0 < m} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {V : FreeFieldVacuum m H} {S T : Submodule ℝ TimeZeroSource}

namespace FiniteGaussianPairModel

variable (X : FiniteGaussianPairModel hm V S T)

theorem reference_covariance_posDef :
    (labelDecorrelatedCovariance (finiteSourceCovarianceMatrix hm (S ⊔ T) X.basis)
      (finiteSourceLabelSubspace hm (S ⊔ T) X.basis S)
      (finiteSourceLabelSubspace hm (S ⊔ T) X.basis T) X.complementary).PosDef := by
  let : FiniteDimensional ℝ ↥(S ⊔ T) := X.basis.finiteDimensional_of_finite
  exact labelDecorrelatedCovariance_posDef
    (real_posDef_of_quantum_posDef (actual_faithful_gaussian_quantum_posDef
      X.faithful_density (finiteSourceCovarianceMatrix_isHermitian hm (S ⊔ T) X.basis)
      X.characteristic)) _ _ X.complementary

theorem renyi_exp_bound {r : ℝ} (hr : 1 < r)
    (hsmall : ‖intrinsicGaussianRelativePerturbation X.density X.reference (gaussianRenyiTau r)‖ ≤
      (4 * max 2 (gaussianRenyiTau r)⁻¹)⁻¹) :
    sandwichedRenyiQuantity X.density X.reference r ≤
      ENNReal.ofReal (Real.exp (gaussianRenyiExponent X.density X.reference r)) := by
  let : FiniteDimensional ℝ ↥(S ⊔ T) := X.basis.finiteDimensional_of_finite
  exact faithful_gaussian_renyi_exp_bound X.faithful_density X.faithful_reference
    (finiteSourceCovarianceMatrix_isHermitian hm (S ⊔ T) X.basis)
    X.reference_covariance_posDef.isHermitian X.characteristic X.reference_characteristic hr hsmall

theorem reverse_renyi_exp_bound {r : ℝ} (hr : 1 < r)
    (hsmall : ‖intrinsicGaussianRelativePerturbation X.reference X.density (gaussianRenyiTau r)‖ ≤
      (4 * max 2 (gaussianRenyiTau r)⁻¹)⁻¹) :
    sandwichedRenyiQuantity X.reference X.density r ≤
      ENNReal.ofReal (Real.exp (gaussianRenyiExponent X.reference X.density r)) := by
  let : FiniteDimensional ℝ ↥(S ⊔ T) := X.basis.finiteDimensional_of_finite
  exact faithful_gaussian_renyi_exp_bound X.faithful_reference X.faithful_density
    X.reference_covariance_posDef.isHermitian
    (finiteSourceCovarianceMatrix_isHermitian hm (S ⊔ T) X.basis)
    X.reference_characteristic X.characteristic hr hsmall

/-- Actual original-vacuum covariance, allowing complex nonselfadjoint
contractions and an infinite Rényi quantity. -/
theorem contraction_covariance_le_renyi {r : ℝ} (hr : 2 ≤ r)
    {A B : H →L[ℂ] H} (hA : A ∈ canonicalSourceAlgebra V hm S)
    (hB : B ∈ canonicalSourceAlgebra V hm T) (hAn : ‖A‖ ≤ 1) (hBn : ‖B‖ ≤ 1) :
    ENNReal.ofReal ‖⟪V.vacuum, (A * B) V.vacuum⟫_ℂ -
      ⟪V.vacuum, A V.vacuum⟫_ℂ * ⟪V.vacuum, B V.vacuum⟫_ℂ‖ ≤
      (sandwichedRenyiQuantity X.density X.reference r ^ (1 / (r - 1)) - 1) ^ (1 / 2 : ℝ) := by
  have hAS := canonicalSourceAlgebra_mono V hm (show S ≤ S ⊔ T from le_sup_left) hA
  have hBT := canonicalSourceAlgebra_mono V hm (show T ≤ S ⊔ T from le_sup_right) hB
  have hρ := X.vacuum_expectation (A * B) ((canonicalSourceAlgebra V hm (S ⊔ T)).mul_mem hAS hBT)
  have hσ := X.product_expectation A hA B hB
  have h := enorm_densityExpectation_sub_le_renyi (multiModeNumberBasis X.modes)
    X.faithful_density.1 X.faithful_density.2.1 X.faithful_reference hr (X.toOperator (A * B))
  rw [← hρ, hσ] at h
  have hn : ENNReal.ofReal ‖X.toOperator (A * B)‖ ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    exact (X.map_norm_le _).trans ((norm_mul_le A B).trans
      ((mul_le_mul_of_nonneg_right hAn (norm_nonneg B)).trans
        (by simpa only [one_mul] using hBn)))
  exact h.trans (by
    simpa only [mul_one] using
      (_root_.mul_le_mul_right hn
        ((sandwichedRenyiQuantity X.density X.reference r ^ (1 / (r - 1)) - 1) ^ (1 / 2 : ℝ))))

/-- The finite source form of the Gaussian trace-distance covariance estimate. -/
theorem contraction_covariance_exp_bound {r : ℝ} (hr : 2 ≤ r)
    (hsmall : ‖intrinsicGaussianRelativePerturbation X.density X.reference (gaussianRenyiTau r)‖ ≤
      (4 * max 2 (gaussianRenyiTau r)⁻¹)⁻¹)
    {A B : H →L[ℂ] H} (hA : A ∈ canonicalSourceAlgebra V hm S)
    (hB : B ∈ canonicalSourceAlgebra V hm T) (hAn : ‖A‖ ≤ 1) (hBn : ‖B‖ ≤ 1) :
    ENNReal.ofReal ‖⟪V.vacuum, (A * B) V.vacuum⟫_ℂ -
      ⟪V.vacuum, A V.vacuum⟫_ℂ * ⟪V.vacuum, B V.vacuum⟫_ℂ‖ ≤
      (ENNReal.ofReal (Real.exp (gaussianRenyiExponent X.density X.reference r)) ^
        (1 / (r - 1)) - 1) ^ (1 / 2 : ℝ) := by
  have hr1 : 1 < r := lt_of_lt_of_le (by norm_num) hr
  exact (X.contraction_covariance_le_renyi hr hA hB hAn hBn).trans
    (ENNReal.rpow_le_rpow (tsub_le_tsub_right (ENNReal.rpow_le_rpow
      (X.renyi_exp_bound hr1 hsmall) (one_div_nonneg.mpr (sub_pos.mpr hr1).le)) 1) (by norm_num))

end FiniteGaussianPairModel

end VacuumBellSeparation
