/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialBesselComplexIntegral
import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Holomorphy of the actual Bessel cosh integrals

Differentiation under the positive-half-line integral uses a genuine
locally uniform integrable majorant. Orders one and two discharge that
majorant with the previously proved real integral convergence.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Set Filter
open scoped Topology

theorem laplace_linear_absorption {b y : ℝ} (hb : 0 < b) :
    y * Real.exp (-b * y) ≤ b⁻¹ := by
  have h := Real.mul_exp_neg_le_exp_neg_one (b * y)
  have he : Real.exp (-1 : ℝ) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
  rw [← one_div]
  apply (le_div_iff₀ hb).mpr
  simpa only [neg_mul, mul_neg, mul_assoc, mul_comm, mul_left_comm] using h.trans he

theorem laplace_derivative_majorant {a r y : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hy : 0 ≤ y) :
    y * Real.exp (-r * y) ≤ (2 / a) * Real.exp (-(a / 2) * y) := by
  calc
    y * Real.exp (-r * y) ≤ y * Real.exp (-a * y) := by
      apply mul_le_mul_of_nonneg_left _ hy
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg har) hy
    _ = (y * Real.exp (-(a / 2) * y)) * Real.exp (-(a / 2) * y) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (2 / a) * Real.exp (-(a / 2) * y) := by
      have h := laplace_linear_absorption (y := y) (show 0 < a / 2 by positivity)
      have heq : (a / 2)⁻¹ = 2 / a := by field_simp
      rw [heq] at h
      exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- Modified Bessel derivative integrand. -/
noncomputable def modifiedBesselDerivativeIntegrand (n : ℕ) (z : ℂ) (u : ℝ) : ℂ :=
  -(Real.cosh u : ℂ) * (Complex.exp (-z * (Real.cosh u : ℂ)) *
    (Real.cosh ((n : ℝ) * u) : ℂ))

theorem hasDerivAt_modifiedBessel_integrand (n : ℕ) (z : ℂ) (u : ℝ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-w * (Real.cosh u : ℂ)) *
      (Real.cosh ((n : ℝ) * u) : ℂ)) (modifiedBesselDerivativeIntegrand n z u) z := by
  have h := ((Complex.hasDerivAt_exp (-z * (Real.cosh u : ℂ))).comp z
    ((hasDerivAt_id z).neg.mul_const (Real.cosh u : ℂ))).mul_const
      (Real.cosh ((n : ℝ) * u) : ℂ)
  simpa only [modifiedBesselDerivativeIntegrand, Function.comp_def, Pi.neg_apply, id_eq,
    neg_one_mul,
    mul_assoc, mul_comm, mul_left_comm] using h

theorem modifiedBesselDerivativeIntegrand_norm_le (n : ℕ) {a : ℝ} (ha : 0 < a)
    {z : ℂ} (hz : a ≤ z.re) (u : ℝ) :
    ‖modifiedBesselDerivativeIntegrand n z u‖ ≤
      (2 / a) * (Real.exp (-(a / 2) * Real.cosh u) * Real.cosh ((n : ℝ) * u)) := by
  unfold modifiedBesselDerivativeIntegrand
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _), modifiedBesselComplex_integrand_norm]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (laplace_derivative_majorant ha hz (Real.cosh_pos u).le) (Real.cosh_pos _).le

theorem hasDerivAt_modifiedBesselComplexIntegral (n : ℕ)
    (hint : ∀ x : ℝ, 0 < x → IntegrableOn
      (fun u : ℝ => Real.exp (-x * Real.cosh u) * Real.cosh ((n : ℝ) * u)) (Ioi 0))
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (modifiedBesselComplexIntegral n)
      (∫ u in Ioi (0 : ℝ), modifiedBesselDerivativeIntegrand n z u) z := by
  let a : ℝ := z.re / 2
  have ha : 0 < a := by dsimp only [a]; positivity
  have haz : a < z.re := by dsimp only [a]; linarith
  have hs : {w : ℂ | a < w.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds haz
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w u => Complex.exp (-w * (Real.cosh u : ℂ)) *
      (Real.cosh ((n : ℝ) * u) : ℂ))
    (F' := modifiedBesselDerivativeIntegrand n)
    (bound := fun u => (2 / a) *
      (Real.exp (-(a / 2) * Real.cosh u) * Real.cosh ((n : ℝ) * u))) hs
    (Eventually.of_forall (fun w => (show Continuous (fun u : ℝ =>
      Complex.exp (-w * (Real.cosh u : ℂ)) * (Real.cosh ((n : ℝ) * u) : ℂ)) by
      fun_prop).aestronglyMeasurable))
    (integrableOn_modifiedBessel_complex_of_real n z (hint _ hz))
    (show AEStronglyMeasurable (modifiedBesselDerivativeIntegrand n z)
      (volume.restrict (Ioi (0 : ℝ))) from
      (show Continuous (modifiedBesselDerivativeIntegrand n z) by
        unfold modifiedBesselDerivativeIntegrand
        fun_prop).aestronglyMeasurable)
    (Eventually.of_forall (fun u w hw => modifiedBesselDerivativeIntegrand_norm_le n ha hw.le u))
    ((hint (a / 2) (by positivity)).const_mul (2 / a))
    (Eventually.of_forall (fun u w _ => hasDerivAt_modifiedBessel_integrand n w u))
  exact h.2

theorem differentiableOn_modifiedBesselComplexIntegral_one :
    DifferentiableOn ℂ (modifiedBesselComplexIntegral 1) {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (hasDerivAt_modifiedBesselComplexIntegral 1
    (fun x hx => by simpa only [Nat.cast_one, one_mul] using integrableOn_modifiedBessel_one hx)
    hz).differentiableAt.differentiableWithinAt

theorem differentiableOn_modifiedBesselComplexIntegral_two :
    DifferentiableOn ℂ (modifiedBesselComplexIntegral 2) {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (hasDerivAt_modifiedBesselComplexIntegral 2
    (fun x hx => by simpa only [Nat.cast_ofNat] using integrableOn_modifiedBessel_two hx)
    hz).differentiableAt.differentiableWithinAt

end VacuumBellSeparation.Gaussian
