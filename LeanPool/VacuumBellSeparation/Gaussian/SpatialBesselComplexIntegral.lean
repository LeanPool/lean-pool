/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialBesselScaledBounds

/-!
# Complex Bessel cosh integrals on the right half-plane

The complex quantity is the literal scalar Bochner integral. Its
integrand norm is exactly the real integrand at Re z, proving actual
convergence and the source domination for orders one and two.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Set

/-- Modified Bessel complex integral given by `∫ u in Ioi (0 : ℝ), Complex.exp (-z * (Real.cosh u :
ℂ)) * (Real.cosh ((n : ℝ) * u) : ℂ)`. -/
noncomputable def modifiedBesselComplexIntegral (n : ℕ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), Complex.exp (-z * (Real.cosh u : ℂ)) *
    (Real.cosh ((n : ℝ) * u) : ℂ)

theorem modifiedBesselComplex_integrand_norm (n : ℕ) (z : ℂ) (u : ℝ) :
    ‖Complex.exp (-z * (Real.cosh u : ℂ)) * (Real.cosh ((n : ℝ) * u) : ℂ)‖ =
      Real.exp (-z.re * Real.cosh u) * Real.cosh ((n : ℝ) * u) := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _)]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem integrableOn_modifiedBessel_complex_of_real (n : ℕ) (z : ℂ)
    (h : IntegrableOn (fun u : ℝ => Real.exp (-z.re * Real.cosh u) *
      Real.cosh ((n : ℝ) * u)) (Ioi 0)) :
    IntegrableOn (fun u : ℝ => Complex.exp (-z * (Real.cosh u : ℂ)) *
      (Real.cosh ((n : ℝ) * u) : ℂ)) (Ioi 0) := by
  apply h.mono'
  · exact (show Continuous (fun u : ℝ => Complex.exp (-z * (Real.cosh u : ℂ)) *
        (Real.cosh ((n : ℝ) * u) : ℂ)) by fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u => (modifiedBesselComplex_integrand_norm n z u).le)

theorem modifiedBesselComplexIntegral_norm_le (n : ℕ) (z : ℂ) :
    ‖modifiedBesselComplexIntegral n z‖ ≤ modifiedBesselIntegral n z.re := by
  unfold modifiedBesselComplexIntegral modifiedBesselIntegral
  calc
    _ ≤ ∫ u in Ioi (0 : ℝ),
        ‖Complex.exp (-z * (Real.cosh u : ℂ)) * (Real.cosh ((n : ℝ) * u) : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp_rw [modifiedBesselComplex_integrand_norm]

theorem modifiedBesselComplexIntegral_ofReal (n : ℕ) (x : ℝ) :
    modifiedBesselComplexIntegral n (x : ℂ) = (modifiedBesselIntegral n x : ℂ) := by
  unfold modifiedBesselComplexIntegral modifiedBesselIntegral
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by
    simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg])

theorem integrableOn_modifiedBessel_complex_one {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-z * (Real.cosh u : ℂ)) *
      (Real.cosh u : ℂ)) (Ioi 0) := by
  simpa only [Nat.cast_one, one_mul] using
    integrableOn_modifiedBessel_complex_of_real 1 z
      (by simpa only [Nat.cast_one, one_mul] using integrableOn_modifiedBessel_one hz)

theorem integrableOn_modifiedBessel_complex_two {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-z * (Real.cosh u : ℂ)) *
      (Real.cosh (2 * u) : ℂ)) (Ioi 0) := by
  simpa only [Nat.cast_ofNat] using
    integrableOn_modifiedBessel_complex_of_real 2 z
      (by simpa only [Nat.cast_ofNat] using integrableOn_modifiedBessel_two hz)

theorem modifiedBesselComplexIntegral_one_le {z : ℂ} (hz : 0 < z.re) :
    ‖modifiedBesselComplexIntegral 1 z‖ ≤ Real.exp (-z.re) *
      (z.re⁻¹ + Real.sqrt (Real.pi / (2 * z.re))) :=
  (modifiedBesselComplexIntegral_norm_le 1 z).trans (modifiedBesselIntegral_one_le hz)

theorem modifiedBesselComplexIntegral_two_le {z : ℂ} (hz : 0 < z.re) :
    ‖modifiedBesselComplexIntegral 2 z‖ ≤ Real.exp (-z.re) *
      (2 * (z.re ^ 2)⁻¹ + 4 * z.re⁻¹ + Real.sqrt (Real.pi / (2 * z.re))) :=
  (modifiedBesselComplexIntegral_norm_le 2 z).trans (modifiedBesselIntegral_two_le hz)

end VacuumBellSeparation.Gaussian
