/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.ModifiedBesselKAnalytic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Recurrences for the integral modified-Bessel K functions

This file proves the order-zero and order-two derivative recurrences on the open right
half-plane by rigorous improper integration by parts. It also introduces the integral order-one
function `K1` and derives its value and derivative recurrences.
-/

@[expose] public section

noncomputable section

namespace FastDynamo.ModifiedBessel

open Complex MeasureTheory Set Filter

/-- The derivative of the boundary term `t ↦ exp (-z cosh t) sinh t`, written in a form adapted
to `K₀` and `K₂`. -/
private def KRecurrenceBoundaryDeriv (z : ℂ) (t : ℝ) : ℂ :=
  -K0DerivIntegrand z t + z / 2 * (K0Integrand z t - K2Integrand z t)

/-- The integration-by-parts boundary term `t ↦ exp (-z cosh t) sinh t` is differentiable in `t`
with derivative `KRecurrenceBoundaryDeriv z t`, expressed through the `K₀` and `K₂` kernels. -/
private theorem hasDerivAt_KRecurrenceBoundary (z : ℂ) (t : ℝ) :
    @HasDerivAt ℝ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup _ _ _
      ((fun s : ℝ ↦ Complex.exp (-z * Real.cosh s)) *
        fun s : ℝ ↦ (Real.sinh s : ℂ))
      (KRecurrenceBoundaryDeriv z t) t := by
  have hcosh : HasDerivAt (fun s : ℝ ↦ (Real.cosh s : ℂ)) (Real.sinh t : ℂ) t :=
    (Real.hasDerivAt_cosh t).ofReal_comp
  have hsinh : HasDerivAt (fun s : ℝ ↦ (Real.sinh s : ℂ)) (Real.cosh t : ℂ) t :=
    (Real.hasDerivAt_sinh t).ofReal_comp
  have hmain := (hcosh.const_mul (-z)).cexp.mul hsinh
  have heq :
      Complex.exp (-z * Real.cosh t) * (-z * (Real.sinh t : ℂ)) *
            (Real.sinh t : ℂ) +
          Complex.exp (-z * Real.cosh t) * (Real.cosh t : ℂ) =
        KRecurrenceBoundaryDeriv z t := by
    unfold KRecurrenceBoundaryDeriv
    rw [K0DerivIntegrand, K0Integrand, K2Integrand, Real.cosh_two_mul,
      Real.cosh_sq' t]
    push_cast
    ring
  exact hmain.congr_deriv heq

/-- Doubling the argument increases the hyperbolic cosine: `cosh t ≤ cosh (2t)`. -/
private lemma cosh_le_cosh_two_mul (t : ℝ) : Real.cosh t ≤ Real.cosh (2 * t) := by
  rw [Real.cosh_le_cosh]
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  nlinarith [abs_nonneg t]

/-- The hyperbolic sine is dominated in absolute value by the hyperbolic cosine. -/
private lemma abs_sinh_le_cosh (t : ℝ) : |Real.sinh t| ≤ Real.cosh t := by
  rw [abs_le]
  constructor <;> nlinarith [Real.cosh_sq_sub_sinh_sq t, Real.cosh_pos t]

/-- Combining the two previous bounds: `|sinh t| ≤ cosh (2t)`, the domination used to make every
boundary term integrable against the `K₂` kernel. -/
private lemma abs_sinh_le_cosh_two_mul (t : ℝ) :
    |Real.sinh t| ≤ Real.cosh (2 * t) := by
  exact (abs_sinh_le_cosh t).trans (cosh_le_cosh_two_mul t)

/-- The integration-by-parts boundary term is dominated pointwise by the `K₂` kernel. -/
private lemma norm_KRecurrenceBoundary_le_K2Integrand (z : ℂ) (t : ℝ) :
    ‖((fun s : ℝ ↦ Complex.exp (-z * Real.cosh s)) *
        fun s : ℝ ↦ (Real.sinh s : ℂ)) t‖ ≤ ‖K2Integrand z t‖ := by
  rw [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_K2Integrand, Complex.norm_exp]
  simp only [neg_mul, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (abs_sinh_le_cosh_two_mul t) (Real.exp_pos _).le

/-- The `K₀` parameter-derivative kernel is dominated pointwise by the `K₂` kernel, since
`cosh t ≤ cosh (2t)`. -/
private lemma norm_K0DerivIntegrand_le_K2Integrand (z : ℂ) (t : ℝ) :
    ‖K0DerivIntegrand z t‖ ≤ ‖K2Integrand z t‖ := by
  rw [norm_K0DerivIntegrand, norm_K2Integrand]
  calc
    Real.cosh t * Real.exp (-z.re * Real.cosh t) =
        Real.exp (-z.re * Real.cosh t) * Real.cosh t := mul_comm _ _
    _ ≤ Real.exp (-z.re * Real.cosh t) * Real.cosh (2 * t) :=
      mul_le_mul_of_nonneg_left (cosh_le_cosh_two_mul t) (Real.exp_pos _).le

/-- For `Re z > 0` the boundary term `exp (-z cosh t) sinh t` is integrable on the line. -/
private theorem integrable_KRecurrenceBoundary {z : ℂ} (hz : 0 < z.re) :
    Integrable ((fun t : ℝ ↦ Complex.exp (-z * Real.cosh t)) *
      fun t : ℝ ↦ (Real.sinh t : ℂ)) := by
  apply Integrable.mono (integrable_K2Integrand hz)
  · fun_prop
  · exact ae_of_all _ (norm_KRecurrenceBoundary_le_K2Integrand z)

/-- For `Re z > 0` the `K₀` parameter-derivative kernel is integrable on the line. -/
private theorem integrable_K0DerivIntegrand {z : ℂ} (hz : 0 < z.re) :
    Integrable (K0DerivIntegrand z) := by
  apply Integrable.mono (integrable_K2Integrand hz)
  · exact (by unfold K0DerivIntegrand; fun_prop : Continuous (K0DerivIntegrand z))
      |>.aestronglyMeasurable
  · exact ae_of_all _ (norm_K0DerivIntegrand_le_K2Integrand z)

/-- For `Re z > 0` the derivative of the boundary term is integrable, being a combination of the
`K₀` derivative kernel and the `K₀`, `K₂` kernels. -/
private theorem integrable_KRecurrenceBoundaryDeriv {z : ℂ} (hz : 0 < z.re) :
    Integrable (KRecurrenceBoundaryDeriv z) := by
  have hd := integrable_K0DerivIntegrand hz
  have h0 := integrable_K0Integrand hz
  have h2 := integrable_K2Integrand hz
  unfold KRecurrenceBoundaryDeriv
  exact hd.neg.add ((h0.sub h2).const_mul (z / 2))

/-- The integration-by-parts identity underlying the order-zero/order-two recurrence. -/
theorem integral_K0DerivIntegrand_eq_K0_sub_K2 {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), K0DerivIntegrand z t = z / 2 * (K0 z - K2 z) := by
  have hd : IntegrableOn (KRecurrenceBoundaryDeriv z) (Ioi (0 : ℝ)) :=
    (integrable_KRecurrenceBoundaryDeriv hz).integrableOn
  have hb : IntegrableOn ((fun t : ℝ ↦ Complex.exp (-z * Real.cosh t)) *
      fun t : ℝ ↦ (Real.sinh t : ℂ)) (Ioi (0 : ℝ)) :=
    (integrable_KRecurrenceBoundary hz).integrableOn
  have hlim : Tendsto ((fun t : ℝ ↦ Complex.exp (-z * Real.cosh t)) *
      fun t : ℝ ↦ (Real.sinh t : ℂ)) atTop (nhds 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
      (a := (0 : ℝ)) (f' := KRecurrenceBoundaryDeriv z)
      (fun t _ht ↦ hasDerivAt_KRecurrenceBoundary z t) hd hb
  have hzero : ∫ t in Ioi (0 : ℝ), KRecurrenceBoundaryDeriv z t = 0 := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := (0 : ℝ))
      (f := (fun t : ℝ ↦ Complex.exp (-z * Real.cosh t)) *
        fun t : ℝ ↦ (Real.sinh t : ℂ))
      (f' := KRecurrenceBoundaryDeriv z)
      (m := (0 : ℂ)) (fun t _ht ↦ hasDerivAt_KRecurrenceBoundary z t) hd hlim
    simpa only [Pi.mul_apply, Real.sinh_zero, ofReal_zero, mul_zero, sub_self] using h
  have hd0 : IntegrableOn (K0DerivIntegrand z) (Ioi (0 : ℝ)) :=
    (integrable_K0DerivIntegrand hz).integrableOn
  have h0 : IntegrableOn (K0Integrand z) (Ioi (0 : ℝ)) :=
    integrableOn_K0Integrand hz
  have h2 : IntegrableOn (K2Integrand z) (Ioi (0 : ℝ)) :=
    integrableOn_K2Integrand hz
  unfold KRecurrenceBoundaryDeriv at hzero
  have hzero' :
      (∫ t in Ioi (0 : ℝ), (-K0DerivIntegrand z) t) +
          ∫ t in Ioi (0 : ℝ), z / 2 * (K0Integrand z - K2Integrand z) t = 0 := by
    rw [← integral_add hd0.neg ((h0.sub h2).const_mul (z / 2))]
    simpa only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] using hzero
  rw [integral_neg' (K0DerivIntegrand z),
    integral_const_mul (z / 2) (K0Integrand z - K2Integrand z),
    integral_sub' h0 h2, ← K0, ← K2] at hzero'
  rwa [neg_add_eq_zero] at hzero'

/-- The derivative recurrence `K₀'(z) = z (K₀(z) - K₂(z)) / 2` on the right half-plane. -/
theorem hasDerivAt_K0_eq_K0_sub_K2 {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt K0 (z / 2 * (K0 z - K2 z)) z :=
  (hasDerivAt_K0 hz).congr_deriv (integral_K0DerivIntegrand_eq_K0_sub_K2 hz)

/-! ## The order-two derivative recurrence -/

/-- Derivative of the second integration-by-parts boundary, written using the kernels defined
above. -/
private def K2RecurrenceBoundaryDeriv (z : ℂ) (t : ℝ) : ℂ :=
  2 * K2Integrand z t + z * (K2DerivIntegrand z t - K0DerivIntegrand z t)

/-- The second integration-by-parts boundary term `t ↦ exp (-z cosh t) sinh (2t)` is
differentiable in `t` with derivative `K2RecurrenceBoundaryDeriv z t`. -/
private theorem hasDerivAt_K2RecurrenceBoundary (z : ℂ) (t : ℝ) :
    @HasDerivAt ℝ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup _ _ _
      ((fun s : ℝ ↦ Complex.exp (-z * Real.cosh s)) *
        fun s : ℝ ↦ (Real.sinh (2 * s) : ℂ))
      (K2RecurrenceBoundaryDeriv z t) t := by
  have hcosh : HasDerivAt (fun s : ℝ ↦ (Real.cosh s : ℂ)) (Real.sinh t : ℂ) t :=
    (Real.hasDerivAt_cosh t).ofReal_comp
  have hsinh2 := ((hasDerivAt_id t).const_mul 2).sinh.ofReal_comp
  have hmain := (hcosh.const_mul (-z)).cexp.mul hsinh2
  simp only [id, mul_one] at hmain
  have heq :
      Complex.exp (-z * Real.cosh t) * (-z * (Real.sinh t : ℂ)) *
            (Real.sinh (2 * t) : ℂ) +
          Complex.exp (-z * Real.cosh t) * (Real.cosh (2 * t) * 2 : ℝ) =
        K2RecurrenceBoundaryDeriv z t := by
    unfold K2RecurrenceBoundaryDeriv
    rw [K2Integrand, K2DerivIntegrand, K0DerivIntegrand, Real.sinh_two_mul,
      Real.cosh_two_mul, Real.cosh_sq' t]
    push_cast
    ring
  exact hmain.congr_deriv heq

/-- The second boundary term is dominated pointwise by the `K₂` kernel. -/
private lemma norm_K2RecurrenceBoundary_le_K2Integrand (z : ℂ) (t : ℝ) :
    ‖((fun s : ℝ ↦ Complex.exp (-z * Real.cosh s)) *
        fun s : ℝ ↦ (Real.sinh (2 * s) : ℂ)) t‖ ≤ ‖K2Integrand z t‖ := by
  rw [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_K2Integrand, Complex.norm_exp]
  simp only [neg_mul, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (abs_sinh_le_cosh (2 * t)) (Real.exp_pos _).le

/-- For `Re z > 0` the second boundary term `exp (-z cosh t) sinh (2t)` is integrable. -/
private theorem integrable_K2RecurrenceBoundary {z : ℂ} (hz : 0 < z.re) :
    Integrable ((fun t : ℝ ↦ Complex.exp (-z * Real.cosh t)) *
      fun t : ℝ ↦ (Real.sinh (2 * t) : ℂ)) := by
  apply Integrable.mono (integrable_K2Integrand hz)
  · fun_prop
  · exact ae_of_all _ (norm_K2RecurrenceBoundary_le_K2Integrand z)

/-- For `Re z > 0` the `K₂` parameter-derivative kernel is integrable, by the Gaussian majorant
of `norm_K2DerivIntegrand_le_gaussian`. -/
private theorem integrable_K2DerivIntegrand {z : ℂ} (hz : 0 < z.re) :
    Integrable (K2DerivIntegrand z) := by
  let bound : ℝ → ℝ := fun t ↦
    Real.exp (18 / z.re) * Real.exp (-(z.re / 8) * t ^ 2)
  have hbound : Integrable bound := by
    exact (integrable_exp_neg_mul_sq (show 0 < z.re / 8 by positivity)).const_mul _
  apply Integrable.mono' hbound
  · exact (by unfold K2DerivIntegrand; fun_prop : Continuous (K2DerivIntegrand z))
      |>.aestronglyMeasurable
  · apply ae_of_all
    intro t
    exact norm_K2DerivIntegrand_le_gaussian hz
      (by simp only [Metric.mem_ball, dist_self]; positivity) t

/-- For `Re z > 0` the derivative of the second boundary term is integrable. -/
private theorem integrable_K2RecurrenceBoundaryDeriv {z : ℂ} (hz : 0 < z.re) :
    Integrable (K2RecurrenceBoundaryDeriv z) := by
  have h2 := integrable_K2Integrand hz
  have hd2 := integrable_K2DerivIntegrand hz
  have hd0 := integrable_K0DerivIntegrand hz
  unfold K2RecurrenceBoundaryDeriv
  exact h2.const_mul 2 |>.add ((hd2.sub hd0).const_mul z)

/-- The integral recurrence `K₂' = K₀' - (2/z)K₂` on the right half-plane. -/
theorem integral_K2DerivIntegrand_eq_K0Deriv_sub {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), K2DerivIntegrand z t =
      (∫ t in Ioi (0 : ℝ), K0DerivIntegrand z t) - 2 / z * K2 z := by
  have hd : IntegrableOn (K2RecurrenceBoundaryDeriv z) (Ioi (0 : ℝ)) :=
    (integrable_K2RecurrenceBoundaryDeriv hz).integrableOn
  have hb : IntegrableOn ((fun t : ℝ ↦ Complex.exp (-z * Real.cosh t)) *
      fun t : ℝ ↦ (Real.sinh (2 * t) : ℂ)) (Ioi (0 : ℝ)) :=
    (integrable_K2RecurrenceBoundary hz).integrableOn
  have hlim : Tendsto ((fun t : ℝ ↦ Complex.exp (-z * Real.cosh t)) *
      fun t : ℝ ↦ (Real.sinh (2 * t) : ℂ)) atTop (nhds 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
      (a := (0 : ℝ)) (f' := K2RecurrenceBoundaryDeriv z)
      (fun t _ht ↦ hasDerivAt_K2RecurrenceBoundary z t) hd hb
  have hzero : ∫ t in Ioi (0 : ℝ), K2RecurrenceBoundaryDeriv z t = 0 := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := (0 : ℝ))
      (f := (fun t : ℝ ↦ Complex.exp (-z * Real.cosh t)) *
        fun t : ℝ ↦ (Real.sinh (2 * t) : ℂ))
      (f' := K2RecurrenceBoundaryDeriv z)
      (m := (0 : ℂ)) (fun t _ht ↦ hasDerivAt_K2RecurrenceBoundary z t) hd hlim
    simpa only [Pi.mul_apply, mul_zero, Real.sinh_zero, ofReal_zero, sub_self] using h
  have h2 : IntegrableOn (K2Integrand z) (Ioi (0 : ℝ)) := integrableOn_K2Integrand hz
  have hd2 : IntegrableOn (K2DerivIntegrand z) (Ioi (0 : ℝ)) :=
    (integrable_K2DerivIntegrand hz).integrableOn
  have hd0 : IntegrableOn (K0DerivIntegrand z) (Ioi (0 : ℝ)) :=
    (integrable_K0DerivIntegrand hz).integrableOn
  unfold K2RecurrenceBoundaryDeriv at hzero
  have hzero' :
      (∫ t in Ioi (0 : ℝ), 2 * K2Integrand z t) +
          ∫ t in Ioi (0 : ℝ), z * (K2DerivIntegrand z - K0DerivIntegrand z) t = 0 := by
    rw [← integral_add (h2.const_mul 2) ((hd2.sub hd0).const_mul z)]
    simpa only [Pi.add_apply, Pi.sub_apply] using hzero
  rw [integral_const_mul 2 (K2Integrand z),
    integral_const_mul z (K2DerivIntegrand z - K0DerivIntegrand z),
    integral_sub' hd2 hd0, ← K2] at hzero'
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  field_simp [hz0]
  linear_combination hzero'

/-- The exact derivative recurrence for `K₂` on the open right half-plane. -/
theorem hasDerivAt_K2_eq_K0_sub_K2 {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt K2 (z / 2 * (K0 z - K2 z) - 2 / z * K2 z) z := by
  apply (hasDerivAt_K2 hz).congr_deriv
  rw [integral_K2DerivIntegrand_eq_K0Deriv_sub hz,
    integral_K0DerivIntegrand_eq_K0_sub_K2 hz]

/-! ## Integral order one -/

/-- The order-one hyperbolic kernel. -/
def K1Integrand (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-z * Real.cosh t) * (Real.cosh t : ℂ)

/-- The integral order-one modified Bessel function on the right half-plane. As with `K0` and
`K2`, the Bochner integral is totalized outside that half-plane. -/
noncomputable def K1 (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), K1Integrand z t

/-- The modulus of the order-one kernel is `exp (-(Re z) cosh t) · cosh t`. -/
lemma norm_K1Integrand (z : ℂ) (t : ℝ) :
    ‖K1Integrand z t‖ = Real.exp (-z.re * Real.cosh t) * Real.cosh t := by
  rw [K1Integrand, norm_mul, Complex.norm_exp]
  simp only [neg_mul, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]

/-- The order-one kernel is dominated pointwise by the `K₂` kernel. -/
lemma norm_K1Integrand_le_K2Integrand (z : ℂ) (t : ℝ) :
    ‖K1Integrand z t‖ ≤ ‖K2Integrand z t‖ := by
  rw [norm_K1Integrand, norm_K2Integrand]
  exact mul_le_mul_of_nonneg_left (cosh_le_cosh_two_mul t) (Real.exp_pos _).le

/-- For `Re z > 0` the order-one kernel is integrable on the line, so `K₁` is well defined by its
hyperbolic integral. -/
theorem integrable_K1Integrand {z : ℂ} (hz : 0 < z.re) :
    Integrable (K1Integrand z) := by
  apply Integrable.mono (integrable_K2Integrand hz)
  · exact (by unfold K1Integrand; fun_prop : Continuous (K1Integrand z)).aestronglyMeasurable
  · exact ae_of_all _ (norm_K1Integrand_le_K2Integrand z)

/-- Restriction of the integrability of the order-one kernel to the positive half-line, the
domain of the defining integral for `K₁`. -/
theorem integrableOn_K1Integrand {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (K1Integrand z) (Ioi (0 : ℝ)) :=
  (integrable_K1Integrand hz).integrableOn

/-- The `K₀` parameter-derivative kernel is exactly the negative of the order-one kernel; this is
the kernel-level form of `K₀' = -K₁`. -/
lemma K0DerivIntegrand_eq_neg_K1Integrand (z : ℂ) (t : ℝ) :
    K0DerivIntegrand z t = -K1Integrand z t := by
  unfold K0DerivIntegrand K1Integrand
  ring

/-- The integral `K1` agrees with the usual order recurrence in the right half-plane. -/
theorem K1_eq_z_div_two_mul_K2_sub_K0 {z : ℂ} (hz : 0 < z.re) :
    K1 z = z / 2 * (K2 z - K0 z) := by
  have hk : (∫ t in Ioi (0 : ℝ), K0DerivIntegrand z t) = -K1 z := by
    calc
      (∫ t in Ioi (0 : ℝ), K0DerivIntegrand z t) =
          ∫ t in Ioi (0 : ℝ), -K1Integrand z t := by
        exact integral_congr_ae
          (ae_of_all _ fun t ↦ K0DerivIntegrand_eq_neg_K1Integrand z t)
      _ = -(∫ t in Ioi (0 : ℝ), K1Integrand z t) := integral_neg _
      _ = -K1 z := rfl
  rw [integral_K0DerivIntegrand_eq_K0_sub_K2 hz] at hk
  calc
    K1 z = -(z / 2 * (K0 z - K2 z)) := by
      simpa only [neg_neg] using (congrArg Neg.neg hk).symm
    _ = z / 2 * (K2 z - K0 z) := by ring

/-- The usual order-zero derivative identity in terms of the integral `K1`. -/
theorem hasDerivAt_K0_eq_neg_K1 {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt K0 (-K1 z) z := by
  apply (hasDerivAt_K0_eq_K0_sub_K2 hz).congr_deriv
  rw [K1_eq_z_div_two_mul_K2_sub_K0 hz]
  ring

/-- The order-one derivative recurrence, with `K1` retaining its hyperbolic integral
representation. -/
theorem hasDerivAt_K1_eq_neg_K0_add_K2 {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt K1 (-(K0 z + K2 z) / 2) z := by
  have halg := ((hasDerivAt_id z).div_const 2).mul
    ((hasDerivAt_K2_eq_K0_sub_K2 hz).sub (hasDerivAt_K0_eq_K0_sub_K2 hz))
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hz
  have heq :
      1 / 2 * (K2 z - K0 z) + z / 2 *
          ((z / 2 * (K0 z - K2 z) - 2 / z * K2 z) -
            z / 2 * (K0 z - K2 z)) =
        -(K0 z + K2 z) / 2 := by
    field_simp [hz0]
    ring
  have halg' := halg.congr_deriv heq
  apply halg'.congr_of_eventuallyEq
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    continuous_re.isOpen_preimage _ isOpen_Ioi
  filter_upwards [hopen.mem_nhds hz] with w hw
  simpa only [id_eq, Pi.div_apply, Pi.sub_apply, Pi.mul_apply] using
    K1_eq_z_div_two_mul_K2_sub_K0 hw

end FastDynamo.ModifiedBessel
