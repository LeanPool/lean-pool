/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeThermalDensity
public import LeanPool.VacuumBellSeparation.Gaussian.CoherentCoordinates
public import LeanPool.VacuumBellSeparation.Gaussian.FiniteComplexProductSeries

/-!
# Actual coherent coordinates on the full finite-mode oscillator space

All occupation tuples occur in the coefficient series. Absolute finite
product Fubini proves membership in ℓ² and the exponential inner-product
kernel; the thermal density acts coordinatewise and has its genuine
finite-mode Bargmann kernel.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal

open scoped ComplexConjugate

/-- Multi coherent coefficient given by `∏ j, coherentCoefficient (z j) (k j)`. -/
noncomputable def multiCoherentCoefficient {m : ℕ} (z : Fin m → ℂ)
    (k : Fin m → ℕ) : ℂ := ∏ j, coherentCoefficient (z j) (k j)

theorem hasSum_multiCoherent_norm_sq {m : ℕ} (z : Fin m → ℂ) :
    HasSum (fun k => ‖multiCoherentCoefficient z k‖ ^ 2)
      (Real.exp (∑ j, ‖z j‖ ^ 2)) := by
  have hs (j : Fin m) : HasSum (fun n => ‖coherentCoefficient (z j) n‖ ^ 2)
      (Real.exp (‖z j‖ ^ 2)) := by
    simpa only [coherentCoefficient_norm_sq, Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (‖z j‖ ^ 2)
  have hp := hasSum_fin_product_nonneg m (fun j n => ‖coherentCoefficient (z j) n‖ ^ 2)
    (fun j => Real.exp (‖z j‖ ^ 2)) (fun j n => sq_nonneg _) hs
  convert hp using 1
  · funext k
    rw [multiCoherentCoefficient, norm_prod, ← Finset.prod_pow]
  · exact Real.exp_sum _ _

theorem multiCoherentCoefficient_memℓp {m : ℕ} (z : Fin m → ℂ) :
    Memℓp (multiCoherentCoefficient z) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
  simpa [Real.rpow_two] using
    (hasSum_multiCoherent_norm_sq z).summable

/-- Multi exponential vector represented by `multiCoherentCoefficient z`. -/
noncomputable def multiExponentialVector {m : ℕ} (z : Fin m → ℂ) :
    MultiModeOscillatorSpace m :=
  ⟨multiCoherentCoefficient z, multiCoherentCoefficient_memℓp z⟩

@[simp] theorem multiExponentialVector_apply {m : ℕ} (z : Fin m → ℂ) (k : Fin m → ℕ) :
    multiExponentialVector z k = multiCoherentCoefficient z k := rfl

theorem multiCoherentCoefficient_inner {m : ℕ} (z w : Fin m → ℂ) (k : Fin m → ℕ) :
    inner ℂ (multiCoherentCoefficient z k) (multiCoherentCoefficient w k) =
      ∏ j, (conj (z j) * w j) ^ (k j) / ((k j).factorial : ℂ) := by
  rw [RCLike.inner_apply', multiCoherentCoefficient, multiCoherentCoefficient,
    map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simpa only [RCLike.inner_apply'] using coherentCoefficient_inner (z j) (w j) (k j)

theorem inner_multiExponentialVector {m : ℕ} (z w : Fin m → ℂ) :
    inner ℂ (multiExponentialVector z) (multiExponentialVector w) =
      Complex.exp (∑ j, conj (z j) * w j) := by
  have habs (j : Fin m) :
      Summable (fun n : ℕ => ‖(conj (z j) * w j) ^ n / (n.factorial : ℂ)‖) := by
    simpa only [norm_div, norm_pow, Complex.norm_natCast] using
      Real.summable_pow_div_factorial ‖conj (z j) * w j‖
  have hs (j : Fin m) : HasSum (fun n : ℕ => (conj (z j) * w j) ^ n / (n.factorial : ℂ))
      (Complex.exp (conj (z j) * w j)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  rw [lp.inner_eq_tsum]
  simp_rw [multiExponentialVector_apply, multiCoherentCoefficient_inner]
  rw [(hasSum_fin_complex_product m _ _ habs hs).tsum_eq, ← Complex.exp_sum]

theorem norm_multiExponentialVector_sq {m : ℕ} (z : Fin m → ℂ) :
    ‖multiExponentialVector z‖ ^ 2 = Real.exp (∑ j, ‖z j‖ ^ 2) := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (multiExponentialVector z)
  have heq : ‖multiExponentialVector z‖ ^ 2 =
      ∑' k, ‖multiCoherentCoefficient z k‖ ^ 2 := by
    simpa [Real.rpow_two] using h
  exact heq.trans (hasSum_multiCoherent_norm_sq z).tsum_eq

theorem multiModeNumberBasis_inner {m : ℕ} (x : MultiModeOscillatorSpace m) (k : Fin m → ℕ) :
    inner ℂ (multiModeNumberBasis m k) x = x k := by
  rw [← (multiModeNumberBasis m).repr_apply_apply]
  rfl

theorem multiModeThermalDensity_apply_coordinate {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    (x : MultiModeOscillatorSpace m) (k : Fin m → ℕ) :
    multiModeThermalDensity q x k = (multiModeThermalWeight q k : ℂ) * x k := by
  have h := indexedDiagonalOperator_inner (multiModeNumberBasis m)
    (hasSum_multiModeThermalWeight hq₀ hq₁).summable
    (multiModeThermalWeight_nonneg hq₀ hq₁) x k
  simpa only [multiModeNumberBasis_inner, multiModeThermalDensity] using h

theorem multiModeThermalDensity_apply_exponentialVector {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (z : Fin m → ℂ) :
    multiModeThermalDensity q (multiExponentialVector z) =
      (∏ j, (1 - q j)) • multiExponentialVector (fun j => (q j : ℂ) * z j) := by
  ext k
  rw [multiModeThermalDensity_apply_coordinate hq₀ hq₁]
  change (multiModeThermalWeight q k : ℂ) * multiCoherentCoefficient z k =
    (∏ j, (1 - q j)) • multiCoherentCoefficient (fun j => (q j : ℂ) * z j) k
  simp only [multiModeThermalWeight, multiCoherentCoefficient,
    RCLike.real_smul_eq_coe_mul, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [thermalWeight, coherentCoefficient, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_one, mul_pow]
  ring

/-- The genuine finite-mode thermal Bargmann kernel. -/
theorem multiModeThermalDensity_coherent_kernel {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (z w : Fin m → ℂ) :
    inner ℂ (multiExponentialVector z) (multiModeThermalDensity q (multiExponentialVector w)) =
      ((∏ j, (1 - q j) : ℝ) : ℂ) *
        Complex.exp (∑ j, (q j : ℂ) * (conj (z j) * w j)) := by
  rw [multiModeThermalDensity_apply_exponentialVector hq₀ hq₁,
    inner_smul_right_eq_smul, inner_multiExponentialVector, RCLike.real_smul_eq_coe_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  ring

end VacuumBellSeparation.Gaussian
