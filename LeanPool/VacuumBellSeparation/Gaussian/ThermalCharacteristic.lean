/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalCoherentTrace
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalCoherentAction
public import LeanPool.VacuumBellSeparation.Gaussian.WeylCoherentKernel
public import LeanPool.VacuumBellSeparation.Gaussian.ComplexGaussianPhase

/-!
# The actual one-mode thermal Weyl characteristic

This theorem concerns the constructed bounded state and the actual Weyl
unitary on oscillator ℓ². Its proof uses the absolutely justified coherent
trace integral, the actual square-root action, and the complex-plane
Gaussian Fourier integral. The pure endpoint is included.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap MeasureTheory
open scoped ComplexConjugate

theorem thermalWeyl_coherent_integrand {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (z w : ℂ) :
    (Real.pi : ℂ)⁻¹ * inner ℂ (CFC.sqrt (thermalDensity q) (coherentVector w))
      (oscillatorWeyl z (CFC.sqrt (thermalDensity q) (coherentVector w))) =
        (((1 - q) / Real.pi : ℝ) : ℂ) * Complex.exp ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) *
          Complex.exp (((-(1 - q) * ‖w‖ ^ 2 : ℝ) : ℂ) +
            2 * Complex.I * (Real.sqrt q : ℂ) * ((conj w * z).im : ℂ)) := by
  let s : ℝ := Real.sqrt (1 - q) * Real.exp (-(1 - q) * ‖w‖ ^ 2 / 2)
  have hs : s * s = (1 - q) * Real.exp (-(1 - q) * ‖w‖ ^ 2) := by
    dsimp [s]
    rw [mul_mul_mul_comm, Real.mul_self_sqrt (sub_nonneg.mpr hq₁.le), ← Real.exp_add]
    congr 2
    ring
  have hphase : (conj ((Real.sqrt q : ℂ) * w) * z).im =
      Real.sqrt q * (conj w * z).im := by
    rw [map_mul, Complex.conj_ofReal]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [sqrt_thermalDensity_apply_coherentVector hq₀ hq₁,
    map_smul, inner_smul_left, inner_smul_right, oscillatorWeyl_coherent_diagonal]
  change (Real.pi : ℂ)⁻¹ * (conj (s : ℂ) * ((s : ℂ) *
    Complex.exp (((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) +
      2 * Complex.I * ((conj ((Real.sqrt q : ℂ) * w) * z).im : ℂ)))) = _
  rw [Complex.conj_ofReal, hphase, Complex.ofReal_mul (Real.sqrt q) (conj w * z).im]
  calc
    _ = (Real.pi : ℂ)⁻¹ * ((s * s : ℝ) : ℂ) *
        Complex.exp (((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) +
          2 * Complex.I * (Real.sqrt q : ℂ) * ((conj w * z).im : ℂ)) := by
      rw [Complex.ofReal_mul s s]
      ring_nf
    _ = _ := by
      rw [hs, Complex.ofReal_mul, Complex.ofReal_exp,
        Complex.exp_add, Complex.exp_add, Complex.ofReal_div]
      ring

theorem integrable_thermalWeyl_coherent_integrand {q : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (z : ℂ) :
    Integrable (fun w : ℂ => (Real.pi : ℂ)⁻¹ *
      inner ℂ (CFC.sqrt (thermalDensity q) (coherentVector w))
        (oscillatorWeyl z (CFC.sqrt (thermalDensity q) (coherentVector w)))) := by
  simp_rw [thermalWeyl_coherent_integrand hq₀ hq₁]
  exact (integrable_complex_gaussian_phase (sub_pos.mpr hq₁) (Real.sqrt q) z).const_mul _

/-- The genuine characteristic function has the thermal covariance
coefficient `(1+q)/(2(1-q))`, with pure value `1/2` at `q=0`. -/
theorem thermalState_oscillatorWeyl {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) (z : ℂ) :
    thermalState hq₀ hq₁ (oscillatorWeyl z) =
      Complex.exp (((-((1 + q) / (2 * (1 - q))) * ‖z‖ ^ 2 : ℝ) : ℂ)) := by
  rw [thermalState_eq_coherent_integral hq₀ hq₁]
  simp_rw [thermalWeyl_coherent_integrand hq₀ hq₁]
  rw [integral_const_mul, integral_complex_gaussian_phase (sub_pos.mpr hq₁),
    Real.sq_sqrt hq₀]
  have hcoeff : (((1 - q) / Real.pi : ℝ) : ℂ) * ((Real.pi / (1 - q) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have h : (1 - q) / Real.pi * (Real.pi / (1 - q)) = 1 := by
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt (sub_pos.mpr hq₁)]
    rw [h, Complex.ofReal_one]
  calc
    _ = (Complex.exp ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) *
        Complex.exp (((-q * ‖z‖ ^ 2 / (1 - q) : ℝ) : ℂ))) := by
      calc
        _ = ((((1 - q) / Real.pi : ℝ) : ℂ) * ((Real.pi / (1 - q) : ℝ) : ℂ)) *
            (Complex.exp ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) *
              Complex.exp (((-q * ‖z‖ ^ 2 / (1 - q) : ℝ) : ℂ))) := by ring
        _ = _ := by rw [hcoeff, one_mul]
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.ofReal_add]
      congr 1
      congr 1
      field_simp [ne_of_gt (sub_pos.mpr hq₁)]
      ring

end VacuumBellSeparation.Gaussian
