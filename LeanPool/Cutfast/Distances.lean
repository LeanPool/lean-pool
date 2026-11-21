/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Barenblatt
public import LeanPool.Cutfast.Wasserstein
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Exact formulas for `W₂²`, `Hₘ` and `Iₘ` between `v(t)` and `v_∞`

With `a = a(t) = (1-e^{-t/α})^α`, `h = e^{-t}x₀`, `M₂ = ∫ |x|² v_∞`:
* `W₂²(v(t), v_∞) = (1-a)² M₂ + |h|²` (eq. (w2_exact));
* `Hₘ(v(t) | v_∞) = M₂ ((1-a^κ)/κ - (1-a²)/2) + |h|²/2` with `κ = d(1-m)`;
* `Iₘ(v(t) | v_∞) = a² (1-a^{-1/α})² M₂ + |h|²`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace

namespace Cutfast

/-- `g(κ, a) = (1-a^κ)/κ - (1-a²)/2`. -/
noncomputable def entropyProfile (κ a : ℝ) : ℝ := (1 - a ^ κ) / κ - (1 - a ^ 2) / 2

variable {d : ℕ} {m : ℝ}

namespace Distances

theorem measurable_equilibrium (h : Admissible d m) : Measurable (equilibrium d m) := by
  rw [show equilibrium d m = fun x =>
      (max (equilibriumConst d m + (1 - m) / (2 * m) * ‖x‖ ^ 2) 0) ^ (1 / (m - 1)) from
    funext (equilibrium_eq h)]
  fun_prop

/-- Integrals against `densityMeasure f` are integrals against `f(x) dx`. -/
theorem integral_densityMeasure {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (g : E d → F) :
    ∫ x, g x ∂densityMeasure f = ∫ x, f x • g x := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hf0 _)]

theorem integrable_densityMeasure_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (g : E d → F) :
    Integrable g (densityMeasure f) ↔ Integrable (fun x => f x • g x) := by
  rw [densityMeasure, integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hf0 _)]

theorem integrable_smul_equilibrium (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) :
    Integrable (fun y => equilibrium d m y • y) := by
  refine (integrable_norm_mul_equilibrium h h2).mono'
    ((measurable_equilibrium h).aestronglyMeasurable.smul aestronglyMeasurable_id)
    (ae_of_all _ fun y => ?_)
  rw [norm_smul, Real.norm_of_nonneg (equilibrium_nonneg h y), mul_comm]

theorem integral_inner_mul_equilibrium (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m)
    (q : E d) : ∫ y, ⟪y, q⟫_ℝ * equilibrium d m y = 0 := by
  have : ∀ y, ⟪y, q⟫_ℝ * equilibrium d m y = ⟪q, equilibrium d m y • y⟫_ℝ := fun y => by
    rw [real_inner_smul_right, real_inner_comm, mul_comm]
  simp_rw [this]
  rw [integral_inner (integrable_smul_equilibrium h h2), integral_smul_equilibrium h,
    inner_zero_right]

theorem sq_affine_eq (p : ℝ) (q y : E d) (v : ℝ) :
    ‖p • y + q‖ ^ 2 * v = p ^ 2 * (‖y‖ ^ 2 * v) + 2 * p * (⟪y, q⟫_ℝ * v) + ‖q‖ ^ 2 * v := by
  rw [norm_add_sq_real, norm_smul, mul_pow, real_inner_smul_left, Real.norm_eq_abs, sq_abs]
  ring

theorem integrable_inner_mul_equilibrium (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m)
    (q : E d) : Integrable (fun y => ⟪y, q⟫_ℝ * equilibrium d m y) := by
  refine ((integrable_norm_mul_equilibrium h h2).mul_const ‖q‖).mono'
    (((continuous_id.inner continuous_const).aestronglyMeasurable).mul
      (measurable_equilibrium h).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
  rw [norm_mul, Real.norm_of_nonneg (equilibrium_nonneg h y), Real.norm_eq_abs]
  calc |⟪y, q⟫_ℝ| * equilibrium d m y ≤ (‖y‖ * ‖q‖) * equilibrium d m y :=
        mul_le_mul_of_nonneg_right (abs_real_inner_le_norm y q) (equilibrium_nonneg h y)
    _ = ‖y‖ * equilibrium d m y * ‖q‖ := by ring

/-- Integrability of a quadratic function of an affine image against `v_∞`. -/
theorem integrable_sq_affine_mul_equilibrium (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m)
    (p : ℝ) (q : E d) : Integrable (fun y => ‖p • y + q‖ ^ 2 * equilibrium d m y) := by
  simp_rw [sq_affine_eq]
  exact (((integrable_sq_mul_equilibrium h h2).const_mul _).add
    ((integrable_inner_mul_equilibrium h h2 q).const_mul _)).add
    ((integrable_equilibrium h).const_mul _)

/-- `∫ |p y + q|² v_∞(y) dy = p² M₂ + |q|²` (the mean of `v_∞` vanishes). -/
theorem integral_sq_affine_mul_equilibrium (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m)
    (p : ℝ) (q : E d) :
    ∫ y, ‖p • y + q‖ ^ 2 * equilibrium d m y = p ^ 2 * eqSecondMoment d m + ‖q‖ ^ 2 := by
  simp_rw [sq_affine_eq]
  have i1 := (integrable_sq_mul_equilibrium h h2).const_mul (p ^ 2)
  have i2 := (integrable_inner_mul_equilibrium h h2 q).const_mul (2 * p)
  have i3 := (integrable_equilibrium h).const_mul (‖q‖ ^ 2)
  rw [integral_add (by exact i1.add i2) i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_inner_mul_equilibrium h h2, integral_equilibrium h, eqSecondMoment]
  ring

/-- `v(t, a y + h) = a^{-d} v_∞(y)`. -/
theorem solution_affine (h : Admissible d m) (x₀ : E d) {t : ℝ} (ht : 0 < t) (y : E d) :
    solution d m x₀ t (scaleFactor d m t • y + exp (-t) • x₀) =
      (scaleFactor d m t ^ d)⁻¹ * equilibrium d m y := by
  rw [solution_eq h x₀ ht, add_sub_cancel_right,
    inv_smul_smul₀ (scaleFactor_pos h ht).ne']

theorem solution_nonneg (h : Admissible d m) (x₀ : E d) {t : ℝ} (ht : 0 < t) (x : E d) :
    0 ≤ solution d m x₀ t x :=
  (solution_isProbabilityDensity' h.1 h.2.1 h.2.2.1 h.2.2.2 x₀ ht).1 x

/-- `(a^{-d})^{m-1} = a^{d(1-m)}`. -/
theorem inv_pow_rpow_eq {a : ℝ} (ha : 0 < a) :
    ((a ^ d)⁻¹) ^ (m - 1) = a ^ ((d : ℝ) * (1 - m)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg ha.le, ← Real.rpow_mul ha.le]
  ring_nf

theorem rpow_sub_one_mul_self {x : ℝ} (hx : 0 ≤ x) (hm : 0 < m) : x ^ (m - 1) * x = x ^ m := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [Real.zero_rpow hm.ne']
  · rw [Real.rpow_sub_one hx.ne', div_mul_cancel₀ _ hx.ne']

/-- Second moment of `v(t)`. -/
theorem integral_sq_mul_solution (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) (x₀ : E d)
    {t : ℝ} (ht : 0 < t) (p : ℝ) (q : E d) :
    Integrable (fun x => ‖p • x + q‖ ^ 2 * solution d m x₀ t x) ∧
    ∫ x, ‖p • x + q‖ ^ 2 * solution d m x₀ t x =
      (p * scaleFactor d m t) ^ 2 * eqSecondMoment d m + ‖p • exp (-t) • x₀ + q‖ ^ 2 := by
  have e : ∀ y, ‖p • (scaleFactor d m t • y + exp (-t) • x₀) + q‖ ^ 2 * equilibrium d m y =
      ‖(p * scaleFactor d m t) • y + (p • exp (-t) • x₀ + q)‖ ^ 2 * equilibrium d m y := by
    intro y; rw [smul_add, smul_smul, add_assoc]
  refine ⟨(integrable_mul_solution_iff h x₀ ht _).2 ?_, ?_⟩
  · simp_rw [e]; exact integrable_sq_affine_mul_equilibrium h h2 _ _
  · rw [integral_mul_solution h x₀ ht]; simp_rw [e]
    exact integral_sq_affine_mul_equilibrium h h2 _ _

/-- `∫ v(t)ᵐ = a^{d(1-m)} ∫ v_∞ᵐ`. -/
theorem integral_solution_rpow (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) (x₀ : E d)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => solution d m x₀ t x ^ m) ∧
    ∫ x, solution d m x₀ t x ^ m =
      scaleFactor d m t ^ ((d : ℝ) * (1 - m)) * ∫ y, equilibrium d m y ^ m := by
  have ha := scaleFactor_pos h ht
  have e1 : ∀ x, solution d m x₀ t x ^ m =
      solution d m x₀ t x ^ (m - 1) * solution d m x₀ t x := fun x =>
    (rpow_sub_one_mul_self (solution_nonneg h x₀ ht x) h.2.1).symm
  have e2 : ∀ y, solution d m x₀ t (scaleFactor d m t • y + exp (-t) • x₀) ^ (m - 1) *
      equilibrium d m y = scaleFactor d m t ^ ((d : ℝ) * (1 - m)) * equilibrium d m y ^ m := by
    intro y
    rw [solution_affine h x₀ ht, Real.mul_rpow (inv_nonneg.2 (pow_nonneg ha.le _))
      (equilibrium_nonneg h y), inv_pow_rpow_eq ha, mul_assoc,
      rpow_sub_one_mul_self (equilibrium_nonneg h y) h.2.1]
  simp_rw [e1]
  refine ⟨(integrable_mul_solution_iff h x₀ ht _).2 ?_, ?_⟩
  · simp_rw [e2]; exact (integrable_equilibrium_rpow h h2).const_mul _
  · rw [integral_mul_solution h x₀ ht]; simp_rw [e2]; exact integral_const_mul _ _


/-- `a^{d(1-m)} a^{-2} = a^{-1/α}`. -/
theorem rpow_mul_inv_sq_eq {a : ℝ} (ha : 0 < a) :
    a ^ ((d : ℝ) * (1 - m)) * (a⁻¹) ^ 2 = a ^ (-1 / alpha d m) := by
  rw [← Real.rpow_two, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le, ← Real.rpow_add ha, alpha]
  congr 1
  rw [div_div_eq_mul_div, div_one]
  ring

/-- Pointwise value of the Fisher integrand along `v(t)`:
`v |x + m/(m-1) ∇(v^{m-1})|² = v |(1 - a^{-1/α}) x + a^{-1/α} h|²`. -/
theorem fisher_integrand_solution (h : Admissible d m) (x₀ : E d) {t : ℝ} (ht : 0 < t)
    (x : E d) :
    solution d m x₀ t x * ‖x + (m / (m - 1)) •
        gradient (fun y => solution d m x₀ t y ^ (m - 1)) x‖ ^ 2 =
      ‖(1 - scaleFactor d m t ^ (-1 / alpha d m)) • x +
        scaleFactor d m t ^ (-1 / alpha d m) • exp (-t) • x₀‖ ^ 2 * solution d m x₀ t x := by
  rcases (solution_nonneg h x₀ ht x).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  set a := scaleFactor d m t
  have ha := scaleFactor_pos h ht
  set q := exp (-t) • x₀
  set C := equilibriumConst d m
  set b := (1 - m) / (2 * m)
  set K := a ^ ((d : ℝ) * (1 - m))
  have hm1 : m - 1 ≠ 0 := sub_ne_zero.2 h.2.2.1
  have hsol : ∀ y, solution d m x₀ t y =
      (a ^ d)⁻¹ * (max (C + b * ((a⁻¹) ^ 2 * ‖y - q‖ ^ 2)) 0) ^ (1 / (m - 1)) := by
    intro y
    rw [solution_eq h x₀ ht, equilibrium_eq h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  set B : E d → ℝ := fun y => C + b * ((a⁻¹) ^ 2 * ‖y - q‖ ^ 2)
  have hB : Continuous B := by fun_prop
  have hBx : 0 < B x := by
    by_contra hneg
    rw [hsol, max_eq_right (not_lt.1 hneg), Real.zero_rpow (one_div_ne_zero hm1),
      mul_zero] at hpos
    exact lt_irrefl _ hpos
  have hev : (fun y => solution d m x₀ t y ^ (m - 1)) =ᶠ[𝓝 x] fun y => K * B y := by
    filter_upwards [continuousAt_const.eventually_lt hB.continuousAt hBx] with y hy
    rw [hsol, max_eq_left hy.le, Real.mul_rpow (inv_nonneg.2 (pow_nonneg ha.le _))
      (Real.rpow_nonneg hy.le _), ← Real.rpow_mul hy.le, one_div_mul_cancel hm1, Real.rpow_one,
      inv_pow_rpow_eq ha]
  set w : E d := (K * b * (a⁻¹) ^ 2 * 2) • (x - q)
  have hder : HasFDerivAt (fun y => K * B y) (InnerProductSpace.toDual ℝ (E d) w) x := by
    have := ((((hasFDerivAt_id x).sub_const q).norm_sq.const_mul ((a⁻¹) ^ 2)).const_mul
      b).const_add C |>.const_mul K
    refine (this.congr_fderiv ?_ : HasFDerivAt (fun y => K * B y) _ x)
    ext v
    simp [w]
    ring
  have hgrad : gradient (fun y => solution d m x₀ t y ^ (m - 1)) x = w :=
    (hder.congr_of_eventuallyEq hev).hasGradientAt.gradient.trans (by simp)
  rw [hgrad, mul_comm]
  congr 3
  have hc : K * (a⁻¹) ^ 2 = a ^ (-1 / alpha d m) := rpow_mul_inv_sq_eq ha
  have hs : m / (m - 1) * (K * b * (a⁻¹) ^ 2 * 2) = -(K * (a⁻¹) ^ 2) := by
    have hm0 : m ≠ 0 := h.2.1.ne'
    have hm1' : 1 - m = -(m - 1) := by ring
    simp only [b, hm1']
    field_simp
  simp only [w, smul_smul, hs, hc]
  module

end Distances

open Distances

/-- Eq. (w2_exact): `W₂²(v(t), v_∞) = (1-a)² M₂ + e^{-2t}|x₀|²`. -/
theorem wassersteinSq_solution (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) (x₀ : E d)
    {t : ℝ} (ht : 0 < t) :
    wassersteinSq (densityMeasure (solution d m x₀ t)) (densityMeasure (equilibrium d m)) =
      ENNReal.ofReal ((1 - scaleFactor d m t) ^ 2 * eqSecondMoment d m + exp (-t) ^ 2 * ‖x₀‖ ^ 2)
        := by
  have hv := measurable_equilibrium h
  have hv0 := equilibrium_nonneg h
  have := (equilibrium_isProbabilityDensity' h.1 h.2.1 h.2.2.1 h.2.2.2).2
  set a := scaleFactor d m t
  have ha := scaleFactor_pos h ht
  set A : E d →L[ℝ] E d := a • 1
  have hA : A.IsPositive := ContinuousLinearMap.isPositive_one.smul_of_nonneg ha.le
  have hA1 : ∀ x, (A - 1) x = (a - 1) • x := fun x => by simp [A, sub_smul]
  have hμ : Integrable (fun x => ‖x‖ ^ 2) (densityMeasure (equilibrium d m)) := by
    rw [integrable_densityMeasure_iff hv hv0]
    simpa only [smul_eq_mul, mul_comm] using integrable_sq_mul_equilibrium h h2
  have hmap : (fun y => a • y + exp (-t) • x₀) = fun y => A y + exp (-t) • x₀ := by
    funext y; simp [A]
  rw [wassersteinSq_comm, densityMeasure_solution h x₀ ht, hmap,
    wassersteinSq_map_affine' _ hμ A hA, integral_densityMeasure hv hv0,
    integral_densityMeasure hv hv0, integral_smul_equilibrium h, map_zero, inner_zero_left]
  simp_rw [hA1, smul_eq_mul]
  have := integral_sq_affine_mul_equilibrium h h2 (a - 1) 0
  simp only [add_zero, norm_zero] at this
  simp_rw [mul_comm (equilibrium d m _)]
  rw [this, norm_smul, Real.norm_of_nonneg (exp_pos _).le]
  ring_nf

/-- The relative entropy integrand of `v(t)` w.r.t. `v_∞` is integrable. -/
theorem integrable_relEntropyDensity_solution (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m)
    (x₀ : E d) {t : ℝ} (ht : 0 < t) :
    Integrable (relEntropyDensity m (solution d m x₀ t) (equilibrium d m)) := by
  have e : relEntropyDensity m (solution d m x₀ t) (equilibrium d m) = fun x =>
      (solution d m x₀ t x ^ m - equilibrium d m x ^ m -
        (1 - m) / 2 * (‖(1 : ℝ) • x + 0‖ ^ 2 * solution d m x₀ t x) +
        (1 - m) / 2 * (‖x‖ ^ 2 * equilibrium d m x)) / (m - 1) := by
    funext x; simp only [relEntropyDensity, one_smul, add_zero]; ring
  rw [e]
  exact (((((integral_solution_rpow h h2 x₀ ht).1.sub (integrable_equilibrium_rpow h h2)).sub
    ((integral_sq_mul_solution h h2 x₀ ht 1 0).1.const_mul _)).add
    ((integrable_sq_mul_equilibrium h h2).const_mul _)).div_const _)

/-- `Hₘ(v(t) | v_∞) = M₂ ((1-a^κ)/κ - (1-a²)/2) + e^{-2t}|x₀|²/2` with `κ = d(1-m)`. -/
theorem relEntropy_solution (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) (x₀ : E d)
    {t : ℝ} (ht : 0 < t) :
    relEntropy m (solution d m x₀ t) (equilibrium d m) =
      eqSecondMoment d m * entropyProfile (d * (1 - m)) (scaleFactor d m t) +
        exp (-t) ^ 2 * ‖x₀‖ ^ 2 / 2 := by
  have e : relEntropyDensity m (solution d m x₀ t) (equilibrium d m) = fun x =>
      (solution d m x₀ t x ^ m - equilibrium d m x ^ m -
        (1 - m) / 2 * (‖(1 : ℝ) • x + 0‖ ^ 2 * solution d m x₀ t x) +
        (1 - m) / 2 * (‖x‖ ^ 2 * equilibrium d m x)) / (m - 1) := by
    funext x; simp only [relEntropyDensity, one_smul, add_zero]; ring
  obtain ⟨i1, e1⟩ := integral_solution_rpow h h2 x₀ ht
  have i2 := integrable_equilibrium_rpow h h2
  obtain ⟨i3, e3⟩ := integral_sq_mul_solution h h2 x₀ ht 1 0
  have i3' := i3.const_mul ((1 - m) / 2)
  have i4 := (integrable_sq_mul_equilibrium h h2).const_mul ((1 - m) / 2)
  rw [relEntropy, e, integral_div, integral_add (by exact (i1.sub i2).sub i3') i4,
    integral_sub (by exact i1.sub i2) i3', integral_sub i1 i2, integral_const_mul,
    integral_const_mul, e1, e3, integral_equilibrium_rpow h h2, ← eqSecondMoment, entropyProfile]
  simp only [one_mul, add_zero, one_smul]
  rw [norm_smul, Real.norm_of_nonneg (exp_pos _).le]
  have hd : (d : ℝ) ≠ 0 := by have := h.1; positivity
  have hm1 : m - 1 ≠ 0 := sub_ne_zero.2 h.2.2.1
  have hm1' : 1 - m ≠ 0 := sub_ne_zero.2 (Ne.symm h.2.2.1)
  field_simp
  ring

/-- `Iₘ(v(t) | v_∞) = a² (1-a^{-1/α})² M₂ + e^{-2t}|x₀|²`. -/
theorem fisherInfo_solution (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) (x₀ : E d)
    {t : ℝ} (ht : 0 < t) :
    fisherInfo m (solution d m x₀ t) =
      ENNReal.ofReal (scaleFactor d m t ^ 2 * (1 - scaleFactor d m t ^ (-1 / alpha d m)) ^ 2 *
        eqSecondMoment d m + exp (-t) ^ 2 * ‖x₀‖ ^ 2) := by
  set c := scaleFactor d m t ^ (-1 / alpha d m)
  obtain ⟨i, e⟩ := integral_sq_mul_solution h h2 x₀ ht (1 - c) (c • exp (-t) • x₀)
  rw [fisherInfo]
  simp_rw [fisher_integrand_solution h x₀ ht]
  rw [← ofReal_integral_eq_lintegral_ofReal i
    (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (solution_nonneg h x₀ ht x)), e,
    ← add_smul, sub_add_cancel, one_smul, norm_smul, Real.norm_of_nonneg (exp_pos _).le]
  ring_nf

end Cutfast
