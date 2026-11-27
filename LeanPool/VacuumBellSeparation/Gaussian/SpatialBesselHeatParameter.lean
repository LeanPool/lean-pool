/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialBesselFullLine

/-!
# Actual heat-parameter integrals and the existing Bessel K

The substitution t=(r/(2μ))exp(u) is implemented by two genuine
Lebesgue changes of variables. Absolute convergence is proved separately.
This identifies the scalar heat kernels, without asserting a Fourier
distribution identity or an unproved exchange with spatial test functions.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Set

/-- Heat Bessel integrand given by `t ^ (-(n + 1 : ℤ)) * Real.exp (-(μ ^ 2 * t) - r ^ 2 / (4 *
t))`. -/
noncomputable def heatBesselIntegrand (n : ℕ) (μ r t : ℝ) : ℝ :=
  t ^ (-(n + 1 : ℤ)) * Real.exp (-(μ ^ 2 * t) - r ^ 2 / (4 * t))

theorem heatBessel_exponent {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r) (u : ℝ) :
    -(μ ^ 2 * ((r / (2 * μ)) * Real.exp u)) -
        r ^ 2 / (4 * ((r / (2 * μ)) * Real.exp u)) =
      -(μ * r) * Real.cosh u := by
  rw [Real.cosh_eq, Real.exp_neg]
  field_simp [hμ.ne', hr.ne', (Real.exp_pos u).ne']; ring

theorem heatBessel_jacobian_power (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    t * t ^ (-(n + 1 : ℤ)) = (t⁻¹) ^ n := by
  rw [zpow_neg, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp,
    zpow_natCast, pow_succ, inv_pow]
  field_simp [ht]

theorem heatBessel_change_integrand (n : ℕ) {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r)
    (u : ℝ) :
    ((r / (2 * μ)) * Real.exp u) *
        heatBesselIntegrand n μ r ((r / (2 * μ)) * Real.exp u) =
      (2 * μ / r) ^ n * (Real.exp (-(n : ℝ) * u) *
        Real.exp (-(μ * r) * Real.cosh u)) := by
  have ht : (r / (2 * μ)) * Real.exp u ≠ 0 := ne_of_gt (by positivity)
  unfold heatBesselIntegrand
  rw [← mul_assoc, heatBessel_jacobian_power n ht, heatBessel_exponent hμ hr]
  have hinv : ((r / (2 * μ)) * Real.exp u)⁻¹ =
      (2 * μ / r) * Real.exp (-u) := by
    rw [Real.exp_neg]
    field_simp [hμ.ne', hr.ne', (Real.exp_pos u).ne']
  rw [hinv, mul_pow, ← Real.exp_nat_mul]
  rw [show (n : ℝ) * -u = -(n : ℝ) * u by ring]
  ring

theorem integrableOn_heatBesselIntegrand (n : ℕ) {μ r : ℝ}
    (hμ : 0 < μ) (hr : 0 < r) :
    IntegrableOn (heatBesselIntegrand n μ r) (Ioi 0) := by
  let a := r / (2 * μ)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hi : Integrable (fun u : ℝ => (a * Real.exp u) *
      heatBesselIntegrand n μ r (a * Real.exp u)) := by
    simpa only [a, heatBessel_change_integrand n hμ hr] using
      (integrable_bessel_exp_fullLine (n : ℝ) (mul_pos hμ hr)).const_mul ((2 * μ / r) ^ n)
  have hi' : Integrable (fun u : ℝ => Real.exp u * heatBesselIntegrand n μ r (a * Real.exp u)) := by
    convert hi.const_mul a⁻¹ using 1
    funext u
    field_simp [ha.ne']
  have hv : IntegrableOn (fun v => heatBesselIntegrand n μ r (a * v)) (Ioi 0) :=
    (integrable_comp_exp (fun v => heatBesselIntegrand n μ r (a * v))).mp hi'
  simpa only [mul_zero] using
    (integrableOn_Ioi_comp_mul_left_iff (heatBesselIntegrand n μ r) 0 ha).mp hv

theorem integral_heatBesselIntegrand (n : ℕ) {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), heatBesselIntegrand n μ r t) =
      2 * (2 * μ / r) ^ n * besselKReal (n : ℝ) (μ * r) := by
  let a := r / (2 * μ)
  have ha : 0 < a := by dsimp only [a]; positivity
  calc
    _ = a * ∫ v in Ioi (0 : ℝ), heatBesselIntegrand n μ r (a * v) := by
      simpa only [mul_zero, smul_eq_mul] using
        (integral_comp_mul_left_Ioi' (heatBesselIntegrand n μ r) 0 ha).symm
    _ = a * ∫ u : ℝ, Real.exp u * heatBesselIntegrand n μ r (a * Real.exp u) := by
      rw [← integral_comp_exp (fun v => heatBesselIntegrand n μ r (a * v))]
      rfl
    _ = ∫ u : ℝ, (a * Real.exp u) * heatBesselIntegrand n μ r (a * Real.exp u) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => by ring)
    _ = (2 * μ / r) ^ n * ∫ u : ℝ,
        Real.exp (-(n : ℝ) * u) * Real.exp (-(μ * r) * Real.cosh u) := by
      simp_rw [a, heatBessel_change_integrand n hμ hr]
      rw [integral_const_mul]
    _ = _ := by rw [integral_bessel_exp_fullLine _ (mul_pos hμ hr)]; ring

theorem heatFieldKernel_eq_bessel {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r) :
    (1 / (16 * Real.pi ^ 2)) *
      (∫ t in Ioi (0 : ℝ), heatBesselIntegrand 1 μ r t) =
      μ / (4 * Real.pi ^ 2 * r) * besselKReal 1 (μ * r) := by
  rw [integral_heatBesselIntegrand 1 hμ hr]
  norm_num only [pow_one, Nat.cast_one]
  field_simp [Real.pi_ne_zero, hr.ne']; ring

theorem heatMomentumKernel_eq_bessel {μ r : ℝ} (hμ : 0 < μ) (hr : 0 < r) :
    -(1 / (32 * Real.pi ^ 2)) *
      (∫ t in Ioi (0 : ℝ), heatBesselIntegrand 2 μ r t) =
      -(μ ^ 2) / (4 * Real.pi ^ 2 * r ^ 2) * besselKReal 2 (μ * r) := by
  rw [integral_heatBesselIntegrand 2 hμ hr]
  norm_num only [Nat.cast_ofNat]
  field_simp [Real.pi_ne_zero, hr.ne']; ring

end VacuumBellSeparation.Gaussian
