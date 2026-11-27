/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.L2DominatedDifferentiation
public import LeanPool.VacuumBellSeparation.FreeField.LpMultiplication
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Entire exponential evolution by an actual bounded measurable coefficient

All vectors lie in the original arbitrary-measure L2 space. The entire curve is
literal multiplication by exp(z a(x)); its derivative is proved by dominated
actual difference quotients. No finite measure or point evaluation of L2 limits
is used.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

omit [MeasurableSpace α] in
lemma norm_boundedCoefficient_exp_le (a : α → ℂ) {C : ℝ}
    (hb : ∀ x, ‖a x‖ ≤ C) (z : ℂ) (x : α) :
    ‖Complex.exp (z * a x)‖ ≤ Real.exp (‖z‖ * C) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  exact (Complex.re_le_norm _).trans (by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _))

theorem memLp_boundedCoefficient_exp (a : α → ℂ) (ha : Measurable a)
    {C : ℝ} (hb : ∀ x, ‖a x‖ ≤ C) (z : ℂ) :
    MemLp (fun x => Complex.exp (z * a x)) ⊤ μ :=
  memLp_top_of_bound (Complex.continuous_exp.measurable.comp
    (measurable_const.mul ha)).aestronglyMeasurable (Real.exp (‖z‖ * C))
    (Eventually.of_forall (norm_boundedCoefficient_exp_le a hb z))

/-- Continuous linear map for the l² bounded exponential, of type `Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ`. -/
noncomputable def l2BoundedExponential (a : α → ℂ) (ha : Measurable a)
    {C : ℝ} (hb : ∀ x, ‖a x‖ ≤ C) (z : ℂ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  lpMultiplication μ (fun x => Complex.exp (z * a x))
    (memLp_boundedCoefficient_exp μ a ha hb z)

theorem l2BoundedExponential_ae (a : α → ℂ) (ha : Measurable a)
    {C : ℝ} (hb : ∀ x, ‖a x‖ ≤ C) (z : ℂ) (f : Lp ℂ 2 μ) :
    l2BoundedExponential μ a ha hb z f =ᵐ[μ] fun x => Complex.exp (z * a x) * f x :=
  lpMultiplication_ae μ _ _ f

theorem hasDerivAt_l2BoundedExponential (a : α → ℂ) (ha : Measurable a)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖a x‖ ≤ C) (f : Lp ℂ 2 μ) (z₀ : ℂ) :
    HasDerivAt (fun z => l2BoundedExponential μ a ha hb z f)
      (lpMultiplication μ a (memLp_top_of_bound ha.aestronglyMeasurable C
        (Eventually.of_forall hb)) (l2BoundedExponential μ a ha hb z₀ f)) z₀ := by
  let F (z : ℂ) (x : α) : ℂ := Complex.exp (z * a x) * f x
  let G (z : ℂ) (x : α) : ℂ := a x * F z x
  let D : ℝ := C * Real.exp ((‖z₀‖ + 1) * C)
  have hder (z : ℂ) (x : α) : HasDerivAt (fun w => F w x) (G z x) z := by
    convert! ((hasDerivAt_id z).mul_const (a x)).cexp.mul_const (f x) using 1;
      dsimp [F, G]; ring
  have hrepG : lpMultiplication μ a (memLp_top_of_bound ha.aestronglyMeasurable C
      (Eventually.of_forall hb)) (l2BoundedExponential μ a ha hb z₀ f) =ᵐ[μ] G z₀ := by
    filter_upwards [lpMultiplication_ae μ a _ (l2BoundedExponential μ a ha hb z₀ f),
      l2BoundedExponential_ae μ a ha hb z₀ f] with x hx hz
    exact hx.trans (by rw [hz])
  have hD (z : ℂ) (hz : z ∈ Metric.ball z₀ 1) (x : α) : ‖G z x‖ ≤ D * ‖f x‖ := by
    have hzbound : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have hdist : ‖z - z₀‖ < 1 := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hz
      have hnorm := norm_add_le (z - z₀) z₀
      rw [sub_add_cancel] at hnorm
      linarith
    have hExp : ‖Complex.exp (z * a x)‖ ≤ Real.exp ((‖z₀‖ + 1) * C) :=
      (norm_boundedCoefficient_exp_le a hb z x).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hzbound hC))
    dsimp [G, F, D]
    rw [norm_mul, norm_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hb x) hExp (norm_nonneg _) hC) (norm_nonneg _)
  have hint : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  apply hasDerivAt_L2_of_dominated_representatives μ _ F
    (l2BoundedExponential_ae μ a ha hb · f) _ (G z₀) hrepG z₀
    (Eventually.of_forall (hder z₀)) (fun x => (2 * D) ^ 2 * ‖f x‖ ^ 2)
    (hint.const_mul _)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ (show (0 : ℝ) < 1 by norm_num))]
    with z hne hz
  have hzneq : z ≠ z₀ := hne
  exact Eventually.of_forall fun x => by
    have hz₀ : z₀ ∈ Metric.ball z₀ 1 := Metric.mem_ball_self (by norm_num)
    have hd : ‖F z x - F z₀ x‖ ≤ D * ‖f x‖ * ‖z - z₀‖ :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun w _ => (hder w x).hasDerivWithinAt) (fun w hw => hD w hw x)
        (convex_ball z₀ 1) hz₀ hz
    have hs : ‖(z - z₀)⁻¹ • (F z x - F z₀ x)‖ ≤ D * ‖f x‖ := by
      rw [norm_smul, norm_inv]
      calc
        _ ≤ ‖z - z₀‖⁻¹ * (D * ‖f x‖ * ‖z - z₀‖) :=
          mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (norm_nonneg _))
        _ = _ := by field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzneq)]
    have hr : ‖(z - z₀)⁻¹ • (F z x - F z₀ x) - G z₀ x‖ ≤ 2 * D * ‖f x‖ :=
      (norm_sub_le _ _).trans (by linarith [hD z₀ hz₀ x])
    calc
      _ ≤ (2 * D * ‖f x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hr 2
      _ = _ := by ring

theorem differentiable_l2BoundedExponential (a : α → ℂ) (ha : Measurable a)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖a x‖ ≤ C) (f : Lp ℂ 2 μ) :
    Differentiable ℂ (fun z => l2BoundedExponential μ a ha hb z f) :=
  fun z => (hasDerivAt_l2BoundedExponential μ a ha hC hb f z).differentiableAt

end VacuumBellSeparation
