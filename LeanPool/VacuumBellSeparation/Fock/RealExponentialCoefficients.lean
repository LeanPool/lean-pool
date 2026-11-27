/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Fock.ExponentialTotality

/-!
# Recovering tensor coefficients using only real multiples

Real and imaginary parts of the actual convergent exponential pairing
series are genuine real power series. Their uniqueness recovers every
complex coefficient, using only vanishing on the real line.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Fock
open Filter
open scoped Topology InnerProductSpace

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem complex_coefficients_zero_of_real_series_zero (c : ℕ → ℂ)
    (hc : ∀ t : ℝ, HasSum (fun n => (t : ℂ) ^ n * c n) 0) : ∀ n, c n = 0 := by
  have hre : HasFPowerSeriesAt (0 : ℝ → ℝ)
      (FormalMultilinearSeries.ofScalars ℝ (fun n => (c n).re)) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    apply Eventually.of_forall
    intro t
    simpa only [zero_add, Pi.zero_apply, FormalMultilinearSeries.coeff_ofScalars,
      smul_eq_mul, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] using Complex.hasSum_re (hc t)
  have him : HasFPowerSeriesAt (0 : ℝ → ℝ)
      (FormalMultilinearSeries.ofScalars ℝ (fun n => (c n).im)) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    apply Eventually.of_forall
    intro t
    simpa only [zero_add, Pi.zero_apply, FormalMultilinearSeries.coeff_ofScalars,
      smul_eq_mul, ← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] using Complex.hasSum_im (hc t)
  intro n
  apply Complex.ext
  · exact (FormalMultilinearSeries.ofScalars_eq_zero ℝ n).mp (congrFun hre.eq_zero n)
  · exact (FormalMultilinearSeries.ofScalars_eq_zero ℝ n).mp (congrFun him.eq_zero n)

theorem inner_pureTensor_zero_of_real_exponential_zero
    (x : SymmetricFockSpace H) (v : H)
    (hx : ∀ t : ℝ, inner ℂ x (exponentialVector H (t • v)) = 0) (n : ℕ) :
    inner ℂ (x n) (pureSymmetricTensor H n v) = 0 := by
  have hc := complex_coefficients_zero_of_real_series_zero
    (fun n => inner ℂ (x n) (exponentialComponent H v n)) (fun t => by
      have h := hasSum_exponentialAnalysis H x v (t : ℂ)
      have ht : (t : ℂ) • v = t • v := algebraMap_smul ℂ t v
      rw [ht, hx t] at h
      simpa only [exponentialAnalysisSeries, FormalMultilinearSeries.coeff_ofScalars,
        smul_eq_mul] using h)
  have hn := hc n
  rw [exponentialComponent, inner_smul_right] at hn
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hden : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hfac))
  exact (mul_eq_zero.mp hn).resolve_left (inv_ne_zero hden)

end VacuumBellSeparation.Fock
