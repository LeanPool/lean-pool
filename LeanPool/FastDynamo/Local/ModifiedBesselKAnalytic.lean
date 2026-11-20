/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.ModifiedBesselK
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analyticity of the integral modified-Bessel functions

This file differentiates the hyperbolic integral definitions of `K₀` and `K₂` under the
integral sign. Explicit locally uniform integrable majorants prove that both functions are
complex analytic throughout their natural open right half-plane.
-/

@[expose] public section

noncomputable section

namespace FastDynamo.ModifiedBessel

open Complex MeasureTheory Set

/-- Every point of the ball of radius `Re z / 2` about `z` has real part greater than `Re z / 2`;
this is the locally uniform half-plane on which the differentiation-under-the-integral majorants
are built. -/
private lemma half_re_lt_re_of_mem_ball {z w : ℂ}
    (hw : w ∈ Metric.ball z (z.re / 2)) : z.re / 2 < w.re := by
  have hre : z.re - w.re ≤ ‖z - w‖ := by
    rw [← sub_re]
    exact re_le_norm (z - w)
  have hnorm : ‖z - w‖ < z.re / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw
  linarith

/-! ## Order zero -/

/-- The derivative of the `K₀` hyperbolic kernel with respect to its complex parameter. -/
def K0DerivIntegrand (z : ℂ) (t : ℝ) : ℂ :=
  -(Real.cosh t : ℂ) * Complex.exp (-z * Real.cosh t)

/-- The `K₀` kernel `w ↦ exp (-w cosh t)` is complex differentiable in the parameter with
derivative `-cosh t · exp (-z cosh t)`. -/
lemma hasDerivAt_K0Integrand (z : ℂ) (t : ℝ) :
    HasDerivAt (fun w : ℂ ↦ K0Integrand w t) (K0DerivIntegrand z t) z := by
  simpa [K0Integrand, K0DerivIntegrand, mul_comm] using
    (((hasDerivAt_id z).neg.mul_const (Real.cosh t : ℂ)).cexp)

/-- The modulus of the `K₀` parameter-derivative kernel is
`cosh t · exp (-(Re z) cosh t)`. -/
lemma norm_K0DerivIntegrand (z : ℂ) (t : ℝ) :
    ‖K0DerivIntegrand z t‖ = Real.cosh t * Real.exp (-z.re * Real.cosh t) := by
  rw [K0DerivIntegrand, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _), Complex.norm_exp]
  simp only [neg_mul, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

/-- On the ball of radius `Re z / 2` about `z` the `K₀` derivative kernel is dominated by the
`K₂` kernel at the real point `Re z / 2`, using `cosh t ≤ cosh (2t)`.  This is the locally
uniform integrable majorant for differentiating `K₀` under the integral. -/
lemma norm_K0DerivIntegrand_le_K2_half_re {z w : ℂ}
    (hw : w ∈ Metric.ball z (z.re / 2)) (t : ℝ) :
    ‖K0DerivIntegrand w t‖ ≤ ‖K2Integrand (z.re / 2 : ℝ) t‖ := by
  rw [norm_K0DerivIntegrand, norm_K2Integrand]
  have hwre : z.re / 2 < w.re := half_re_lt_re_of_mem_ball hw
  have hexp : Real.exp (-w.re * Real.cosh t) ≤
      Real.exp (-(z.re / 2) * Real.cosh t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.cosh_pos t]
  have hcosh : Real.cosh t ≤ Real.cosh (2 * t) := by
    rw [Real.cosh_le_cosh]
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    nlinarith [abs_nonneg t]
  calc
    Real.cosh t * Real.exp (-w.re * Real.cosh t) =
        Real.exp (-w.re * Real.cosh t) * Real.cosh t := mul_comm _ _
    _ ≤ Real.exp (-(z.re / 2) * Real.cosh t) * Real.cosh (2 * t) :=
      mul_le_mul hexp hcosh (Real.cosh_pos _).le (Real.exp_pos _).le

/-- Differentiation under the hyperbolic integral for `K₀` in its natural right half-plane. -/
theorem hasDerivAt_K0 {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt K0 (∫ t in Ioi (0 : ℝ), K0DerivIntegrand z t) z := by
  let s : Set ℂ := Metric.ball z (z.re / 2)
  let bound : ℝ → ℝ := fun t ↦ ‖K2Integrand (z.re / 2 : ℝ) t‖
  have hs : s ∈ nhds z := Metric.ball_mem_nhds z (by positivity)
  have hmeas : ∀ᶠ w in nhds z,
      AEStronglyMeasurable (K0Integrand w) (volume.restrict (Ioi 0)) := by
    filter_upwards with w
    exact (by unfold K0Integrand; fun_prop : Continuous (K0Integrand w)).aestronglyMeasurable
  have hint : Integrable (K0Integrand z) (volume.restrict (Ioi 0)) :=
    integrableOn_K0Integrand hz
  have hdmeas : AEStronglyMeasurable (K0DerivIntegrand z)
      (volume.restrict (Ioi 0)) :=
    (by unfold K0DerivIntegrand; fun_prop : Continuous (K0DerivIntegrand z)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi 0), ∀ w ∈ s,
      ‖K0DerivIntegrand w t‖ ≤ bound t := by
    filter_upwards with t
    intro w hw
    exact norm_K0DerivIntegrand_le_K2_half_re hw t
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) := by
    have hhalf : 0 < ((z.re / 2 : ℝ) : ℂ).re := by
      rw [ofReal_re]
      exact half_pos hz
    exact (integrableOn_K2Integrand (z := (z.re / 2 : ℝ)) hhalf).norm
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioi 0), ∀ w ∈ s,
      HasDerivAt (fun u : ℂ ↦ K0Integrand u t) (K0DerivIntegrand w t) w := by
    filter_upwards with t
    intro w _
    exact hasDerivAt_K0Integrand w t
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hint hdmeas hbound
    hbound_int hdiff
  change HasDerivAt (fun w : ℂ ↦ ∫ t in Ioi (0 : ℝ), K0Integrand w t)
    (∫ t in Ioi (0 : ℝ), K0DerivIntegrand z t) z
  exact h.2

/-- `K₀` is complex differentiable at every point of the open right half-plane. -/
theorem differentiableAt_K0 {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ K0 z :=
  (hasDerivAt_K0 hz).differentiableAt

/-- `K₀` is analytic on the open right half-plane. -/
theorem analyticOnNhd_K0 : AnalyticOnNhd ℂ K0 {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := by
    exact continuous_re.isOpen_preimage _ isOpen_Ioi
  rw [analyticOnNhd_iff_differentiableOn hopen]
  intro z hz
  exact (differentiableAt_K0 hz).differentiableWithinAt

/-! ## Order two -/

/-- The derivative of the order-two hyperbolic kernel with respect to its complex parameter. -/
def K2DerivIntegrand (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-z * Real.cosh t) * (-(Real.cosh t : ℂ)) * (Real.cosh (2 * t) : ℂ)

/-- Young's inequality in the normalization used for the derivative of the `K₂` kernel. -/
lemma three_abs_le_quadratic {a : ℝ} (ha : 0 < a) (t : ℝ) :
    3 * |t| ≤ a / 4 * t ^ 2 + 9 / a := by
  have ht : |t| ^ 2 = t ^ 2 := sq_abs t
  have hp : 12 * a * |t| ≤ a ^ 2 * t ^ 2 + 36 := by
    nlinarith [sq_nonneg (a * |t| - 6)]
  rw [show a / 4 * t ^ 2 + 9 / a = (a ^ 2 * t ^ 2 + 36) / (4 * a) by
    field_simp [ha.ne']; ring]
  rw [le_div_iff₀ (show 0 < 4 * a by positivity)]
  nlinarith

/-- The modulus of the `K₂` parameter-derivative kernel is
`cosh t · exp (-(Re z) cosh t) · cosh (2t)`. -/
lemma norm_K2DerivIntegrand (z : ℂ) (t : ℝ) :
    ‖K2DerivIntegrand z t‖ =
      Real.cosh t * Real.exp (-z.re * Real.cosh t) * Real.cosh (2 * t) := by
  rw [K2DerivIntegrand, norm_mul, norm_mul, Complex.norm_exp]
  simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, neg_mul, mul_re, neg_re,
    ofReal_re, ofReal_im, mul_zero, sub_zero]
  rw [abs_of_pos (Real.cosh_pos _), abs_of_pos (Real.cosh_pos _)]
  ring

/-- On the ball of radius `Re z / 2` about `z` the `K₂` derivative kernel is dominated by the
integrable Gaussian `exp (18 / Re z) · exp (-(Re z / 8) t²)`, obtained from `cosh t ≤ exp |t|`,
the quadratic lower bound on `cosh`, and Young's inequality. -/
lemma norm_K2DerivIntegrand_le_gaussian {z w : ℂ} (hz : 0 < z.re)
    (hw : w ∈ Metric.ball z (z.re / 2)) (t : ℝ) :
    ‖K2DerivIntegrand w t‖ ≤
      Real.exp (18 / z.re) * Real.exp (-(z.re / 8) * t ^ 2) := by
  rw [norm_K2DerivIntegrand]
  have hwre : z.re / 2 < w.re := half_re_lt_re_of_mem_ball hw
  calc
    Real.cosh t * Real.exp (-w.re * Real.cosh t) * Real.cosh (2 * t)
        ≤ Real.exp |t| * Real.exp (-(z.re / 2) * Real.cosh t) * Real.exp |2 * t| := by
          gcongr
          · exact cosh_le_exp_abs t
          · exact cosh_le_exp_abs (2 * t)
    _ = Real.exp (-(z.re / 2) * Real.cosh t + 3 * |t|) := by
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    _ ≤ Real.exp (-(z.re / 8) * t ^ 2 + 18 / z.re) := by
          apply Real.exp_le_exp.mpr
          have hc := sq_div_two_le_cosh t
          have hy := three_abs_le_quadratic (show 0 < z.re / 2 by positivity) t
          nlinarith
    _ = Real.exp (18 / z.re) * Real.exp (-(z.re / 8) * t ^ 2) := by
          rw [add_comm, Real.exp_add]

/-- The `K₂` kernel `w ↦ exp (-w cosh t) cosh (2t)` is complex differentiable in the parameter
with derivative `K2DerivIntegrand z t`. -/
lemma hasDerivAt_K2Integrand (z : ℂ) (t : ℝ) :
    HasDerivAt (fun w : ℂ ↦ K2Integrand w t) (K2DerivIntegrand z t) z := by
  have hinner : HasDerivAt (fun w : ℂ ↦ -w * (Real.cosh t : ℂ))
      (-(Real.cosh t : ℂ)) z := by
    simpa [id] using (hasDerivAt_id z).neg.mul_const (Real.cosh t : ℂ)
  have h := ((Complex.hasDerivAt_exp (-z * Real.cosh t)).comp z hinner).mul_const
    (Real.cosh (2 * t) : ℂ)
  simpa [K2Integrand, K2DerivIntegrand, Function.comp_def] using h

/-- Differentiation under the hyperbolic integral for `K₂` in its natural right half-plane. -/
theorem hasDerivAt_K2 {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt K2 (∫ t in Ioi (0 : ℝ), K2DerivIntegrand z t) z := by
  let bound : ℝ → ℝ := fun t ↦
    Real.exp (18 / z.re) * Real.exp (-(z.re / 8) * t ^ 2)
  have hbound : Integrable bound := by
    exact (integrable_exp_neg_mul_sq (show 0 < z.re / 8 by positivity)).const_mul _
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w t ↦ K2Integrand w t)
    (F' := fun w t ↦ K2DerivIntegrand w t)
    (bound := bound)
    (Metric.ball_mem_nhds z (show 0 < z.re / 2 by positivity))
    (Filter.Eventually.of_forall fun w ↦
      (by unfold K2Integrand; fun_prop : Continuous (K2Integrand w))
        |>.aestronglyMeasurable.restrict)
    (integrableOn_K2Integrand hz)
    ((by unfold K2DerivIntegrand; fun_prop : Continuous (K2DerivIntegrand z))
      |>.aestronglyMeasurable.restrict)
    (ae_of_all _ fun t w hw ↦ norm_K2DerivIntegrand_le_gaussian hz hw t)
    hbound.integrableOn
    (ae_of_all _ fun t w _hw ↦ hasDerivAt_K2Integrand w t)
  change HasDerivAt (fun w : ℂ ↦ ∫ t in Ioi (0 : ℝ), K2Integrand w t)
    (∫ t in Ioi (0 : ℝ), K2DerivIntegrand z t) z
  exact hmain.2

/-- `K₂` is complex differentiable at every point of the open right half-plane. -/
theorem differentiableAt_K2 {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ K2 z :=
  (hasDerivAt_K2 hz).differentiableAt

/-- `K₂` is analytic on the open right half-plane. -/
theorem analyticOnNhd_K2 : AnalyticOnNhd ℂ K2 {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := by
    exact continuous_re.isOpen_preimage _ isOpen_Ioi
  rw [analyticOnNhd_iff_differentiableOn hopen]
  intro z hz
  exact (differentiableAt_K2 hz).differentiableWithinAt

end FastDynamo.ModifiedBessel
