/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalDensity

/-!
# Coherent coordinates on the actual one-mode oscillator space

The exponential vector has coefficients `z^k / sqrt(k!)` in ℓ². Its inner
product and the thermal operator's coherent kernel follow from convergent
series.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal ComplexConjugate

/-- Coherent coefficient given by `z ^ k / (Real.sqrt (k.factorial : ℝ) : ℂ)`. -/
noncomputable def coherentCoefficient (z : ℂ) (k : ℕ) : ℂ :=
  z ^ k / (Real.sqrt (k.factorial : ℝ) : ℂ)

theorem coherentCoefficient_norm_sq (z : ℂ) (k : ℕ) :
    ‖coherentCoefficient z k‖ ^ 2 = (‖z‖ ^ 2) ^ k / (k.factorial : ℝ) := by
  rw [coherentCoefficient, norm_div, norm_pow,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]

theorem coherentCoefficient_memℓp (z : ℂ) : Memℓp (coherentCoefficient z) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
  have h : Summable fun k => ‖coherentCoefficient z k‖ ^ 2 := by
    simpa only [coherentCoefficient_norm_sq] using Real.summable_pow_div_factorial (‖z‖ ^ 2)
  simpa [Real.rpow_two] using h

/-- The unnormalized coherent (exponential) vector in ℓ². -/
noncomputable def exponentialVector (z : ℂ) : OscillatorSpace :=
  ⟨coherentCoefficient z, coherentCoefficient_memℓp z⟩

@[simp]
theorem exponentialVector_apply (z : ℂ) (k : ℕ) :
    exponentialVector z k = coherentCoefficient z k := rfl

theorem coherentCoefficient_inner (z w : ℂ) (k : ℕ) :
    inner ℂ (coherentCoefficient z k) (coherentCoefficient w k) =
      (conj z * w) ^ k / (k.factorial : ℂ) := by
  have hden : (Real.sqrt (k.factorial : ℝ) : ℂ) ^ 2 = (k.factorial : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg k.factorial : 0 ≤ (k.factorial : ℝ))
  rw [RCLike.inner_apply', coherentCoefficient, coherentCoefficient, map_div₀,
    map_pow, Complex.conj_ofReal, div_mul_div_comm, ← mul_pow, ← pow_two, hden]

theorem inner_exponentialVector (z w : ℂ) :
    inner ℂ (exponentialVector z) (exponentialVector w) = Complex.exp (conj z * w) := by
  rw [lp.inner_eq_tsum]
  simp_rw [exponentialVector_apply, coherentCoefficient_inner]
  rw [Complex.exp_eq_exp_ℂ]
  exact (NormedSpace.expSeries_div_hasSum_exp (conj z * w)).tsum_eq

theorem norm_exponentialVector_sq (z : ℂ) :
    ‖exponentialVector z‖ ^ 2 = Real.exp (‖z‖ ^ 2) := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (exponentialVector z)
  have hn : ‖exponentialVector z‖ ^ 2 =
      ∑' k, (‖z‖ ^ 2) ^ k / (k.factorial : ℝ) := by
    simpa [Real.rpow_two, coherentCoefficient_norm_sq] using h
  rw [hn, Real.exp_eq_exp_ℝ]
  exact (NormedSpace.expSeries_div_hasSum_exp (‖z‖ ^ 2)).tsum_eq

theorem numberBasis_inner (x : OscillatorSpace) (k : ℕ) :
    inner ℂ (numberBasis k) x = x k := by
  rw [← numberBasis.repr_apply_apply]
  rfl

theorem thermalDensity_apply_coordinate {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (x : OscillatorSpace) (k : ℕ) :
    thermalDensity q x k = (thermalWeight q k : ℂ) * x k := by
  have h := diagonalOperator_inner numberBasis (hasSum_thermalWeight hq₀ hq₁).summable
    (fun j => mul_nonneg (sub_nonneg.mpr hq₁.le) (pow_nonneg hq₀ j)) x k
  simpa only [thermalDensity, numberBasis_inner] using h

theorem thermalDensity_apply_exponentialVector {q : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (z : ℂ) :
    thermalDensity q (exponentialVector z) = (1 - q) • exponentialVector ((q : ℂ) * z) := by
  ext k
  rw [thermalDensity_apply_coordinate hq₀ hq₁]
  change (thermalWeight q k : ℂ) * coherentCoefficient z k =
    (1 - q) • coherentCoefficient ((q : ℂ) * z) k
  simp only [coherentCoefficient, thermalWeight, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_one, RCLike.real_smul_eq_coe_mul,
    RCLike.ofReal_eq_complex_ofReal, mul_pow]
  ring

/-- The thermal Bargmann kernel in actual ℓ² coherent coordinates. -/
theorem thermalDensity_coherent_kernel {q : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (z w : ℂ) :
    inner ℂ (exponentialVector z) (thermalDensity q (exponentialVector w)) =
      ((1 - q : ℝ) : ℂ) * Complex.exp ((q : ℂ) * (conj z * w)) := by
  rw [thermalDensity_apply_exponentialVector hq₀ hq₁,
    inner_smul_right_eq_smul, inner_exponentialVector, RCLike.real_smul_eq_coe_mul]
  congr 2
  ring

end VacuumBellSeparation.Gaussian
