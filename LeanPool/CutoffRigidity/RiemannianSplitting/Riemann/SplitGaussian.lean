/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Probability.Distributions.Gaussian.Density

/-! # Lebesgue density of the isotropic Gaussian on Euclidean space -/

@[expose] public section

open ProbabilityTheory MeasureTheory
open scoped ENNReal Matrix

namespace CutCur

theorem multivariateGaussian_eq_withDensity (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) =
      (volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
        (fun t => ENNReal.ofReal ((ρ / (2 * Real.pi)) ^ ((k : ℝ) / 2) *
          Real.exp (-(ρ / 2) * ‖t‖ ^ 2))) := by
  let covariance := ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)
  have positive_definite : covariance.PosDef := Matrix.PosDef.one.smul (inv_pos.mpr hρ)
  have precision : covariance⁻¹ = ρ • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    apply Matrix.inv_eq_left_inv
    simp only [covariance, Matrix.mul_smul, mul_one, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
  change multivariateGaussian 0 covariance = _
  rw [TauCeti.Probability.multivariateGaussian_eq_withDensity positive_definite]
  congr 1
  funext t
  rw [TauCeti.Probability.multivariateGaussianPDF_def,
    TauCeti.Probability.multivariateGaussianPDFReal_def]
  dsimp only
  rw [sub_zero, precision]
  have quadratic : (ρ • (1 : Matrix (Fin k) (Fin k) ℝ)).toEuclideanLin t = ρ • t := by
    rw [Matrix.toLpLin_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [quadratic, real_inner_smul_right, real_inner_self_eq_norm_sq]
  congr 1
  have normalization : (2 * Real.pi) ^ (-(k : ℝ) / 2) *
      covariance.det ^ (-(1 : ℝ) / 2) = (ρ / (2 * Real.pi)) ^ ((k : ℝ) / 2) := by
    have hπ : 0 < 2 * Real.pi := by positivity
    rw [show covariance.det = ρ⁻¹ ^ k by simp [covariance], ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), Real.inv_rpow hρ.le,
      show (k : ℝ) * (-(1 : ℝ) / 2) = -((k : ℝ) / 2) by ring,
      show -(k : ℝ) / 2 = -((k : ℝ) / 2) by ring,
      Real.rpow_neg hπ.le, Real.rpow_neg hρ.le, inv_inv, Real.div_rpow hρ.le hπ.le]
    simp only [div_eq_mul_inv, mul_comm]
  rw [Fintype.card_fin, normalization]
  congr 2
  ring

end CutCur
