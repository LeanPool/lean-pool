/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianSandwichTrace
public import LeanPool.VacuumBellSeparation.Gaussian.MatrixGaussianCriterion

/-!
# Exact noncommuting Gaussian inverse-sandwich trace-class criterion

The actual Gaussian characteristic yields the true inverse-domain
coherent diagonal. Its extended integral is finite precisely for a
positive precision matrix, including necessity at singular and indefinite
boundaries. The proved matrix order equivalence then gives the source
strict covariance gap and an actual positive trace-class factorization.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
variable {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
variable {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

theorem thermalCoherentPrecision_isHermitian
    (hq₀ : ∀ j, 0 < q j) (τ : ℝ)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) :
    (thermalCoherentPrecision q τ V).IsHermitian := by
  let T := thermalQuadratureDilation q τ
  have hT : T.PosDef := thermalQuadratureDilation_posDef hq₀ τ
  have hTT : (T * T).IsHermitian := by
    simpa only [hT.isHermitian.eq] using Matrix.isHermitian_mul_conjTranspose_self T
  have hmid : (T * (V + (1 / 2 : ℝ) • 1)⁻¹ * T).PosDef := by
    have h := hT.isUnit.posDef_star_right_conjugate_iff (x := (V + (1 / 2 : ℝ) • 1)⁻¹)
    simpa only [Matrix.star_eq_conjTranspose, hT.isHermitian.eq] using h.mpr hC.inv
  exact (Matrix.isHermitian_one.sub hTT).add hmid.isHermitian

theorem lintegral_gaussianThermalSandwich_lt_top_iff
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) :
    (∫⁻ z : Fin m → ℂ, ENNReal.ofReal (multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A z)) < ⊤ ↔
      (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef := by
  let c : ℝ := (Real.pi ^ m)⁻¹ * (∏ j, (1 - q j)) ^ (-τ) *
    (Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹
  have hZ : 0 < ∏ j, (1 - q j) := Finset.prod_pos fun j _ => sub_pos.mpr (hq₁ j)
  have hc : 0 < c := mul_pos
    (mul_pos (inv_pos.mpr (pow_pos Real.pi_pos m)) (Real.rpow_pos_of_pos hZ _))
    (inv_pos.mpr (Real.sqrt_pos.mpr hC.det_pos))
  simp_rw [gaussianThermalSandwich_coherent_diagonal hq₀ hq₁ hτ hA hG hC]
  change (∫⁻ z : Fin m → ℂ, ENNReal.ofReal (c *
    coherentMatrixGaussian (thermalCoherentPrecision q τ V) z)) < ⊤ ↔ _
  simp_rw [ENNReal.ofReal_mul hc.le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfinite (t : ℝ≥0∞) : ENNReal.ofReal c * t < ⊤ ↔ t < ⊤ := by
    constructor
    · intro h
      by_contra! ht
      have he : t = ⊤ := top_le_iff.mp ht
      rw [he, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hc))] at h
      exact lt_irrefl _ h
    · intro h
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h
  rw [hfinite, lintegral_coherentMatrixGaussian_lt_top_iff
    (thermalCoherentPrecision_isHermitian hq₀ τ hC),
    thermalCoherentPrecision_posDef_iff hq₀ hq₁ hτ V hC]

/-- Exact source domain criterion for an actual noncommuting Gaussian
operator relative to the faithful product thermal reference. -/
theorem exists_gaussian_positiveTraceClass_sandwich_iff
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) :
    (∃ Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass Θ ∧
      (multiModeThermalDensity q ^ (τ / 2)) * Θ *
        (multiModeThermalDensity q ^ (τ / 2)) = A) ↔
      (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef := by
  rw [exists_positiveTraceClass_multiThermal_factorization_iff_coherentIntegral hq₀ hq₁ hτ hA.1,
    lintegral_gaussianThermalSandwich_lt_top_iff hq₀ hq₁ hτ hA hG hC]

theorem gaussianThermalSandwich_infinite_diagonal_of_not_gap
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : ¬ (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef) :
    (∑' k, ENNReal.ofReal (multiInverseThermalDiagonal q τ A k)) = ⊤ := by
  rw [← lintegral_multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ hA.1]
  exact top_le_iff.mp (not_lt.mp (fun h => hgap
    ((lintegral_gaussianThermalSandwich_lt_top_iff hq₀ hq₁ hτ hA hG hC).mp h)))

end VacuumBellSeparation.Gaussian
