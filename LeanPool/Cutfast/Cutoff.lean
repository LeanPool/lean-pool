/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Distances
public import LeanPool.Cutfast.Asymptotics
public import Mathlib.Order.CompletePartialOrder

/-!
# Cutoff phenomenon (Theorems 1.1 and 1.2)

Using the exact formulas of `Cutfast.Distances`, with `u = e^{-t/α}` and `a = (1-u)^α`,
each of `W₂²`, `Hₘ`, `Iₘ` is, for `u ≤ 1/2`, bounded above by `C u² M₂ + C' e^{-2t}|x₀|²`,
and below by `c e^{-2t}|x₀|²` and, when `α ≥ 1`, by `c u² M₂`. Since `M₂ ≍ d`
(Lemmas 3.1, 4.1, 4.2), the cutoff follows from `d u² = d^{1 - 2t/(α log d)}` and
`d e^{-2t} = d^{1 - 2t/log d}`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace

namespace Cutfast

namespace Cutoff

/-! ### Elementary estimates on the scale factor -/

/-- `1 - (1-u)^α ≤ max(1,α) u` for `u ∈ [0,1]`. -/
lemma one_sub_rpow_le {α u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 - (1 - u) ^ α ≤ max 1 α * u := by
  rcases le_total α 1 with h | h
  · have := self_le_rpow_of_le_one (by linarith : (0 : ℝ) ≤ 1 - u) (by linarith) h
    have : u ≤ max 1 α * u := le_mul_of_one_le_left hu0 (le_max_left _ _)
    linarith
  · have := one_add_mul_self_le_rpow_one_add (by linarith : (-1:ℝ) ≤ -u) h
    rw [max_eq_right h]
    rw [← sub_eq_add_neg] at this
    nlinarith

/-- `u ≤ 1 - (1-u)^α` for `u ∈ [0,1]` and `α ≥ 1`. -/
lemma le_one_sub_rpow {α u : ℝ} (hα : 1 ≤ α) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u ≤ 1 - (1 - u) ^ α := by
  have := rpow_le_self_of_le_one (by linarith : (0 : ℝ) ≤ 1 - u) (by linarith) hα
  linarith

lemma rpow_one_sub_le_one {α u : ℝ} (hα : 0 < α) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - u) ^ α ≤ 1 :=
  rpow_le_one (by linarith) (by linarith) hα.le

/-- The Fisher information factor: `a²(1-a^{-1/α})² = a² (u/(1-u))²` with `a = (1-u)^α`. -/
lemma fisher_factor_eq {α u : ℝ} (hα : 0 < α) (hu1 : u < 1) :
    ((1 - u) ^ α) ^ 2 * (1 - ((1 - u) ^ α) ^ (-1 / α)) ^ 2 =
      ((1 - u) ^ α) ^ 2 * (u / (1 - u)) ^ 2 := by
  have hw : 0 < 1 - u := by linarith
  rw [← rpow_mul hw.le, show α * (-1 / α) = -1 by field_simp, rpow_neg_one]
  congr 1
  field_simp
  ring

lemma fisher_factor_le {α u : ℝ} (hα : 0 < α) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    ((1 - u) ^ α) ^ 2 * (1 - ((1 - u) ^ α) ^ (-1 / α)) ^ 2 ≤ 4 * u ^ 2 := by
  rw [fisher_factor_eq hα (by linarith)]
  have ha0 : 0 ≤ (1 - u) ^ α := rpow_nonneg (by linarith) _
  have ha1 := rpow_one_sub_le_one hα hu0 (by linarith)
  have h1 : (u / (1 - u)) ^ 2 ≤ 4 * u ^ 2 := by
    have h4 : 1 / 4 ≤ (1 - u) ^ 2 := by nlinarith
    rw [div_pow, div_le_iff₀ (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg u)]
  calc ((1 - u) ^ α) ^ 2 * (u / (1 - u)) ^ 2 ≤ 1 * (4 * u ^ 2) := by
        apply mul_le_mul (by nlinarith) h1 (sq_nonneg _) zero_le_one
    _ = 4 * u ^ 2 := one_mul _

lemma le_fisher_factor {α u : ℝ} (hα : 0 < α) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    ((1 / 2) ^ α) ^ 2 * u ^ 2 ≤
      ((1 - u) ^ α) ^ 2 * (1 - ((1 - u) ^ α) ^ (-1 / α)) ^ 2 := by
  rw [fisher_factor_eq hα (by linarith)]
  have h1 : (1 / 2 : ℝ) ^ α ≤ (1 - u) ^ α := rpow_le_rpow (by norm_num) (by linarith) hα.le
  have h2 : u ^ 2 ≤ (u / (1 - u)) ^ 2 := by
    have h4 : (1 - u) ^ 2 ≤ 1 := by nlinarith
    rw [div_pow, le_div_iff₀ (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg u)]
  exact mul_le_mul (pow_le_pow_left₀ (rpow_nonneg (by norm_num) _) h1 2) h2 (sq_nonneg _)
    (sq_nonneg _)

/-! ### The entropy profile -/

lemma integral_mul_one_sub (c w : ℝ) : ∫ s in w..1, c * (1 - s) = c * (1 - w) ^ 2 / 2 := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (by simp) (by simp),
    integral_id]
  simp
  ring

/-- Integral representation `g(κ, w^α) = ∫_w^1 α s^{2α-2}(1-s) ds` with `κ = 2 - 1/α`. -/
lemma entropyProfile_eq_integral {α w : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hw : 0 < w)
    (hw1 : w ≤ 1) :
    entropyProfile (2 - 1 / α) (w ^ α) =
      ∫ s in w..1, α * (s ^ (2 * α - 2) - s ^ (2 * α - 1)) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc w 1 := by
    rw [Set.uIcc_of_le hw1]; intro h; linarith [h.1]
  have hne : 2 * α - 1 ≠ 0 := by intro h; apply hα2; linarith
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_rpow (Or.inr h0))
      (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)),
    integral_rpow (Or.inr ⟨by intro h; apply hα2; linarith, h0⟩),
    integral_rpow (Or.inl (by linarith))]
  unfold entropyProfile
  rw [← rpow_mul hw.le, ← rpow_natCast, ← rpow_mul hw.le]
  have e1 : α * (2 - 1 / α) = 2 * α - 1 := by field_simp
  have e2 : 2 * α - 2 + 1 = 2 * α - 1 := by ring
  have e3 : 2 * α - 1 + 1 = 2 * α := by ring
  have e4 : 2 - 1 / α = (2 * α - 1) / α := by field_simp
  rw [e1, e2, e3, e4, one_rpow, one_rpow]
  push_cast
  rw [mul_comm α 2]
  field_simp

lemma entropy_integrand_eq {α s : ℝ} (hs : 0 < s) :
    α * (s ^ (2 * α - 2) - s ^ (2 * α - 1)) = α * s ^ (2 * α - 2) * (1 - s) := by
  rw [show 2 * α - 1 = (2 * α - 2) + 1 by ring, rpow_add hs, rpow_one]
  ring

lemma entropyProfile_nonneg {α w : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hw : 0 < w)
    (hw1 : w ≤ 1) : 0 ≤ entropyProfile (2 - 1 / α) (w ^ α) := by
  rw [entropyProfile_eq_integral hα hα2 hw hw1]
  apply intervalIntegral.integral_nonneg hw1
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le hw hs.1
  rw [entropy_integrand_eq hs0]
  have := rpow_nonneg hs0.le (2 * α - 2)
  have : 0 ≤ 1 - s := by linarith [hs.2]
  positivity

lemma entropyProfile_le {α w : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hw : 1 / 2 ≤ w)
    (hw1 : w ≤ 1) : entropyProfile (2 - 1 / α) (w ^ α) ≤ 2 * α * (1 - w) ^ 2 := by
  have hw0 : 0 < w := by linarith
  rw [entropyProfile_eq_integral hα hα2 hw0 hw1,
    show 2 * α * (1 - w) ^ 2 = (4 * α) * (1 - w) ^ 2 / 2 by ring, ← integral_mul_one_sub]
  apply intervalIntegral.integral_mono_on hw1
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (by
        rw [Set.uIcc_of_le hw1] at hx; exact ne_of_gt (by simp only [id]; linarith [hx.1]))
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (by
        rw [Set.uIcc_of_le hw1] at hx; exact ne_of_gt (by simp only [id]; linarith [hx.1]))
  · exact (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
  intro s hs
  have hs0 : 0 < s := by linarith [hs.1]
  rw [entropy_integrand_eq hs0]
  have h1 : s ^ (2 * α - 2) ≤ s ^ (-2 : ℝ) :=
    rpow_le_rpow_of_exponent_ge hs0 hs.2 (by linarith)
  have h2 : s ^ (-2 : ℝ) ≤ 4 := by
    rw [rpow_neg hs0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith [hs.1]
  have : 0 ≤ 1 - s := by linarith [hs.2]
  have : α * s ^ (2 * α - 2) ≤ 4 * α := by nlinarith
  nlinarith

lemma le_entropyProfile {α w : ℝ} (hα : 1 ≤ α) (hw : 1 / 2 ≤ w) (hw1 : w ≤ 1) :
    α * (1 / 2) ^ (2 * α - 2) / 2 * (1 - w) ^ 2 ≤ entropyProfile (2 - 1 / α) (w ^ α) := by
  have hw0 : 0 < w := by linarith
  rw [entropyProfile_eq_integral (by linarith) (by intro h; linarith) hw0 hw1,
    show α * (1 / 2) ^ (2 * α - 2) / 2 * (1 - w) ^ 2 =
      (α * (1 / 2) ^ (2 * α - 2)) * (1 - w) ^ 2 / 2 by ring, ← integral_mul_one_sub]
  apply intervalIntegral.integral_mono_on hw1
  · exact (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (by
        rw [Set.uIcc_of_le hw1] at hx; exact ne_of_gt (by simp only [id]; linarith [hx.1]))
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (by
        rw [Set.uIcc_of_le hw1] at hx; exact ne_of_gt (by simp only [id]; linarith [hx.1]))
  intro s hs
  have hs0 : 0 < s := by linarith [hs.1]
  rw [entropy_integrand_eq hs0]
  have h1 : (1 / 2 : ℝ) ^ (2 * α - 2) ≤ s ^ (2 * α - 2) :=
    rpow_le_rpow (by norm_num) (by linarith [hs.1]) (by linarith)
  have : 0 ≤ 1 - s := by linarith [hs.2]
  have : 0 ≤ α := by linarith
  have := mul_le_mul_of_nonneg_left h1 this
  nlinarith

/-! ### Exact formulas rewritten in terms of `u = e^{-t/α}` -/

variable {d : ℕ} {m : ℝ}

lemma two_sub_pos (h : Admissible d m) : 0 < 2 - d * (1 - m) := by
  obtain ⟨hd, -, -, hmd⟩ := h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_lt_iff₀ hd'] at hmd
  linarith

lemma kappa_eq : (d : ℝ) * (1 - m) = 2 - 1 / alpha d m := by
  unfold alpha
  rw [one_div_one_div]
  ring

lemma alpha_ne_half (h : Admissible d m) : alpha d m ≠ 1 / 2 := by
  intro h'
  have h1 := kappa_eq (d := d) (m := m)
  rw [h'] at h1
  obtain ⟨hd, -, hm1, -⟩ := h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : (d : ℝ) * (1 - m) = 0 := by rw [h1]; norm_num
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact hm1 (by linarith)

lemma scaleFactor_eq : scaleFactor d m t = (1 - exp (-t / alpha d m)) ^ alpha d m := rfl

/-- Upper bound for `W₂²`. -/
lemma wassersteinSq_le (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) {t : ℝ} (ht : 0 < t)
    (hu : exp (-t / alpha d m) ≤ 1 / 2) (x₀ : E d) {R2 : ℝ} (hx : ‖x₀‖ ^ 2 ≤ R2) :
    wassersteinSq (densityMeasure (solution d m x₀ t)) (densityMeasure (equilibrium d m)) ≤
      ENNReal.ofReal (max 1 (alpha d m) ^ 2 * exp (-t / alpha d m) ^ 2 * eqSecondMoment d m +
        exp (-t) ^ 2 * R2) := by
  rw [wassersteinSq_solution h h2 x₀ ht, scaleFactor_eq]
  apply ENNReal.ofReal_le_ofReal
  have hα := alpha_pos h
  have hM := (eqSecondMoment_pos h h2).le
  have hu0 : 0 ≤ exp (-t / alpha d m) := (exp_pos _).le
  have h1 := one_sub_rpow_le (α := alpha d m) hu0 (by linarith)
  have h0 := rpow_one_sub_le_one hα hu0 (by linarith)
  have h3 : (1 - (1 - exp (-t / alpha d m)) ^ alpha d m) ^ 2 ≤
      max 1 (alpha d m) ^ 2 * exp (-t / alpha d m) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h1 2
  have h4 := mul_le_mul_of_nonneg_right h3 hM
  have h5 := mul_le_mul_of_nonneg_left hx (sq_nonneg (exp (-t)))
  linarith

/-- Lower bound for `W₂²` when `α ≥ 1`. -/
lemma le_wassersteinSq_of_one_le (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) {t : ℝ}
    (ht : 0 < t) (hα : 1 ≤ alpha d m) (hu : exp (-t / alpha d m) ≤ 1 / 2) (x₀ : E d) :
    ENNReal.ofReal (exp (-t / alpha d m) ^ 2 * eqSecondMoment d m) ≤
      wassersteinSq (densityMeasure (solution d m x₀ t)) (densityMeasure (equilibrium d m)) := by
  rw [wassersteinSq_solution h h2 x₀ ht, scaleFactor_eq]
  apply ENNReal.ofReal_le_ofReal
  have hM := (eqSecondMoment_pos h h2).le
  have hu0 : 0 ≤ exp (-t / alpha d m) := (exp_pos _).le
  have h1 := le_one_sub_rpow hα hu0 (by linarith)
  have h3 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu0 h1 2) hM
  have : 0 ≤ exp (-t) ^ 2 * ‖x₀‖ ^ 2 := by positivity
  linarith

/-- Lower bound for `W₂²` by the translation part. -/
lemma le_wassersteinSq (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) {t : ℝ}
    (ht : 0 < t) (x₀ : E d) :
    ENNReal.ofReal (exp (-t) ^ 2 * ‖x₀‖ ^ 2) ≤
      wassersteinSq (densityMeasure (solution d m x₀ t)) (densityMeasure (equilibrium d m)) := by
  rw [wassersteinSq_solution h h2 x₀ ht]
  apply ENNReal.ofReal_le_ofReal
  have hM := (eqSecondMoment_pos h h2).le
  have : 0 ≤ (1 - scaleFactor d m t) ^ 2 * eqSecondMoment d m := by positivity
  linarith

lemma relEntropy_eq (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) {t : ℝ} (ht : 0 < t)
    (x₀ : E d) :
    relEntropy m (solution d m x₀ t) (equilibrium d m) =
      eqSecondMoment d m * entropyProfile (2 - 1 / alpha d m)
        ((1 - exp (-t / alpha d m)) ^ alpha d m) + exp (-t) ^ 2 * ‖x₀‖ ^ 2 / 2 := by
  rw [relEntropy_solution h h2 x₀ ht, kappa_eq, scaleFactor_eq]

lemma entropy_nonneg_aux (h : Admissible d m) {t : ℝ} (ht : 0 < t) :
    0 ≤ entropyProfile (2 - 1 / alpha d m) ((1 - exp (-t / alpha d m)) ^ alpha d m) := by
  have hα := alpha_pos h
  apply entropyProfile_nonneg hα (alpha_ne_half h)
  · have : exp (-t / alpha d m) < 1 := exp_lt_one_iff.2 (div_neg_of_neg_of_pos (by linarith) hα)
    linarith
  · linarith [exp_pos (-t / alpha d m)]

/-- Bounds for `Hₘ`: `0 ≤ Hₘ ≤ 2α u² M₂ + e^{-2t} R²/2`. -/
lemma relEntropy_le (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) {t : ℝ} (ht : 0 < t)
    (hu : exp (-t / alpha d m) ≤ 1 / 2) (x₀ : E d) {R2 : ℝ} (hx : ‖x₀‖ ^ 2 ≤ R2) :
    0 ≤ relEntropy m (solution d m x₀ t) (equilibrium d m) ∧
    relEntropy m (solution d m x₀ t) (equilibrium d m) ≤
      2 * alpha d m * exp (-t / alpha d m) ^ 2 * eqSecondMoment d m + exp (-t) ^ 2 * R2 / 2 := by
  rw [relEntropy_eq h h2 ht]
  have hα := alpha_pos h
  have hM := (eqSecondMoment_pos h h2).le
  have hg := entropy_nonneg_aux h ht
  have hu0 : 0 ≤ exp (-t / alpha d m) := (exp_pos _).le
  have h1 := entropyProfile_le hα (alpha_ne_half h) (w := 1 - exp (-t / alpha d m))
    (by linarith) (by linarith)
  rw [sub_sub_cancel] at h1
  have h3 := mul_le_mul_of_nonneg_left h1 hM
  have h5 := mul_le_mul_of_nonneg_left hx (sq_nonneg (exp (-t)))
  constructor
  · positivity
  · linarith

lemma le_relEntropy_of_one_le (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) {t : ℝ}
    (ht : 0 < t) (hα : 1 ≤ alpha d m) (hu : exp (-t / alpha d m) ≤ 1 / 2) (x₀ : E d) :
    alpha d m * (1 / 2) ^ (2 * alpha d m - 2) / 2 * exp (-t / alpha d m) ^ 2 *
        eqSecondMoment d m ≤ relEntropy m (solution d m x₀ t) (equilibrium d m) := by
  rw [relEntropy_eq h h2 ht]
  have hM := (eqSecondMoment_pos h h2).le
  have hu0 : 0 ≤ exp (-t / alpha d m) := (exp_pos _).le
  have h1 := le_entropyProfile hα (w := 1 - exp (-t / alpha d m)) (by linarith) (by linarith)
  rw [sub_sub_cancel] at h1
  have h3 := mul_le_mul_of_nonneg_left h1 hM
  have : 0 ≤ exp (-t) ^ 2 * ‖x₀‖ ^ 2 / 2 := by positivity
  linarith

lemma le_relEntropy (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) {t : ℝ}
    (ht : 0 < t) (x₀ : E d) :
    exp (-t) ^ 2 * ‖x₀‖ ^ 2 / 2 ≤ relEntropy m (solution d m x₀ t) (equilibrium d m) := by
  rw [relEntropy_eq h h2 ht]
  have hM := (eqSecondMoment_pos h h2).le
  have hg := entropy_nonneg_aux h ht
  have : 0 ≤ eqSecondMoment d m * entropyProfile (2 - 1 / alpha d m)
      ((1 - exp (-t / alpha d m)) ^ alpha d m) := mul_nonneg hM hg
  linarith

/-- Upper bound for `Iₘ`. -/
lemma fisherInfo_le (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) {t : ℝ} (ht : 0 < t)
    (hu : exp (-t / alpha d m) ≤ 1 / 2) (x₀ : E d) {R2 : ℝ} (hx : ‖x₀‖ ^ 2 ≤ R2) :
    fisherInfo m (solution d m x₀ t) ≤
      ENNReal.ofReal (4 * exp (-t / alpha d m) ^ 2 * eqSecondMoment d m + exp (-t) ^ 2 * R2) := by
  rw [fisherInfo_solution h h2 x₀ ht, scaleFactor_eq]
  apply ENNReal.ofReal_le_ofReal
  have hM := (eqSecondMoment_pos h h2).le
  have hu0 : 0 ≤ exp (-t / alpha d m) := (exp_pos _).le
  have h1 := fisher_factor_le (alpha_pos h) hu0 hu
  have h3 := mul_le_mul_of_nonneg_right h1 hM
  have h5 := mul_le_mul_of_nonneg_left hx (sq_nonneg (exp (-t)))
  linarith

lemma le_fisherInfo_of_one_le (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) {t : ℝ}
    (ht : 0 < t) (hu : exp (-t / alpha d m) ≤ 1 / 2) (x₀ : E d) :
    ENNReal.ofReal (((1 / 2) ^ alpha d m) ^ 2 * exp (-t / alpha d m) ^ 2 * eqSecondMoment d m) ≤
      fisherInfo m (solution d m x₀ t) := by
  rw [fisherInfo_solution h h2 x₀ ht, scaleFactor_eq]
  apply ENNReal.ofReal_le_ofReal
  have hM := (eqSecondMoment_pos h h2).le
  have hu0 : 0 ≤ exp (-t / alpha d m) := (exp_pos _).le
  have h1 := le_fisher_factor (alpha_pos h) hu0 hu
  have h3 := mul_le_mul_of_nonneg_right h1 hM
  have : 0 ≤ exp (-t) ^ 2 * ‖x₀‖ ^ 2 := by positivity
  linarith

lemma le_fisherInfo (h : Admissible d m) (h2 : (d : ℝ) / (d + 2) < m) {t : ℝ}
    (ht : 0 < t) (x₀ : E d) :
    ENNReal.ofReal (exp (-t) ^ 2 * ‖x₀‖ ^ 2) ≤ fisherInfo m (solution d m x₀ t) := by
  rw [fisherInfo_solution h h2 x₀ ht]
  apply ENNReal.ofReal_le_ofReal
  have hM := (eqSecondMoment_pos h h2).le
  have : 0 ≤ scaleFactor d m t ^ 2 * (1 - scaleFactor d m t ^ (-1 / alpha d m)) ^ 2 *
      eqSecondMoment d m := by positivity
  linarith

/-! ### Suprema over balls -/

lemma tendsto_iSup_ennreal_zero {F : (d : ℕ) → E d → ℝ≥0∞} {R b : ℕ → ℝ}
    (hb : Tendsto b atTop (𝓝 0))
    (h : ∀ᶠ d in atTop, ∀ x₀ ∈ closedBall (0 : E d) (R d), F d x₀ ≤ ENNReal.ofReal (b d)) :
    Tendsto (fun d => ⨆ x₀ ∈ closedBall (0 : E d) (R d), F d x₀) atTop (𝓝 0) := by
  have : Tendsto (fun d => ENNReal.ofReal (b d)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [h] with d hd using iSup₂_le hd

lemma tendsto_iSup_ennreal_top {F : (d : ℕ) → E d → ℝ≥0∞} {R b : ℕ → ℝ}
    (hb : Tendsto b atTop atTop)
    (h : ∀ᶠ d in atTop, ∃ x₀ ∈ closedBall (0 : E d) (R d), ENNReal.ofReal (b d) ≤ F d x₀) :
    Tendsto (fun d => ⨆ x₀ ∈ closedBall (0 : E d) (R d), F d x₀) atTop (𝓝 ⊤) := by
  refine tendsto_nhds_top_mono (ENNReal.tendsto_ofReal_atTop.comp hb) ?_
  filter_upwards [h] with d ⟨x, hx, hle⟩
  exact hle.trans (le_iSup₂ (f := fun x _ => F d x) x hx)

lemma tendsto_iSup_ereal_zero {F : (d : ℕ) → E d → ℝ} {R b : ℕ → ℝ}
    (hb : Tendsto b atTop (𝓝 0)) (hR : ∀ᶠ d in atTop, 0 ≤ R d)
    (h : ∀ᶠ d in atTop, ∀ x₀ ∈ closedBall (0 : E d) (R d), 0 ≤ F d x₀ ∧ F d x₀ ≤ b d) :
    Tendsto (fun d => ⨆ x₀ ∈ closedBall (0 : E d) (R d), (F d x₀ : EReal)) atTop (𝓝 0) := by
  have : Tendsto (fun d => (b d : EReal)) atTop (𝓝 0) := by
    exact EReal.tendsto_coe.2 hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this ?_ ?_
  · filter_upwards [h, hR] with d hd hRd
    have h0 : (0 : E d) ∈ closedBall (0 : E d) (R d) := mem_closedBall_self hRd
    exact (EReal.coe_nonneg.2 (hd 0 h0).1).trans
      (le_iSup₂ (f := fun x _ => (F d x : EReal)) 0 h0)
  · filter_upwards [h] with d hd
    exact iSup₂_le fun x hx => EReal.coe_le_coe_iff.2 (hd x hx).2

lemma tendsto_iSup_ereal_top {F : (d : ℕ) → E d → ℝ} {R b : ℕ → ℝ}
    (hb : Tendsto b atTop atTop)
    (h : ∀ᶠ d in atTop, ∃ x₀ ∈ closedBall (0 : E d) (R d), b d ≤ F d x₀) :
    Tendsto (fun d => ⨆ x₀ ∈ closedBall (0 : E d) (R d), (F d x₀ : EReal)) atTop (𝓝 ⊤) := by
  refine tendsto_nhds_top_mono (EReal.tendsto_coe_nhds_top_iff.2 hb) ?_
  filter_upwards [h] with d ⟨x, hx, hle⟩
  exact (EReal.coe_le_coe_iff.2 hle).trans (le_iSup₂ (f := fun x _ => (F d x : EReal)) x hx)

/-- A point of norm `R` in `ℝᵈ`, `d ≥ 1`. -/
lemma exists_norm_eq_of_one_le {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 ≤ R) :
    ∃ x : E d, ‖x‖ = R :=
  ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) R, by
    simp [abs_of_nonneg hR]⟩

lemma sq_le_of_mem_closedBall {d : ℕ} {r : ℝ} {x : E d}
    (hx : x ∈ closedBall (0 : E d) (r * √d)) : ‖x‖ ^ 2 ≤ r ^ 2 * d := by
  rw [mem_closedBall_zero_iff] at hx
  calc ‖x‖ ^ 2 ≤ (r * √d) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    _ = r ^ 2 * d := by rw [mul_pow, sq_sqrt (Nat.cast_nonneg _)]

/-! ### Powers of `d` -/

lemma natCast_mul_exp_sq {k : ℝ} {d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) * exp (-(k * log d)) ^ 2 = exp ((1 - 2 * k) * log d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [show (1 - 2 * k) * log d = log d + -(k * log d) + -(k * log d) by ring, exp_add, exp_add,
    exp_log hd']
  ring

lemma tendsto_log_natCast : Tendsto (fun d : ℕ => log (d : ℝ)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_mul_exp_sq_zero {k : ℝ} (hk : 1 < 2 * k) :
    Tendsto (fun d : ℕ => (d : ℝ) * exp (-(k * log d)) ^ 2) atTop (𝓝 0) := by
  have : Tendsto (fun d : ℕ => exp ((1 - 2 * k) * log d)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_log_natCast.const_mul_atTop_of_neg (by linarith))
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with d hd using (natCast_mul_exp_sq hd).symm

lemma tendsto_mul_exp_sq_atTop {k : ℝ} (hk : 2 * k < 1) :
    Tendsto (fun d : ℕ => (d : ℝ) * exp (-(k * log d)) ^ 2) atTop atTop := by
  have : Tendsto (fun d : ℕ => exp ((1 - 2 * k) * log d)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_log_natCast.const_mul_atTop (by linarith))
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with d hd using (natCast_mul_exp_sq hd).symm

lemma tendsto_exp_neg_mul_log {k : ℝ} (hk : 0 < k) :
    Tendsto (fun d : ℕ => exp (-(k * log d))) atTop (𝓝 0) :=
  tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_log_natCast.const_mul_atTop hk))

lemma log_natCast_pos {d : ℕ} (hd : 2 ≤ d) : 0 < log (d : ℝ) :=
  log_pos (by exact_mod_cast hd)

/-- From `d u_d² → 0`, eventually `u_d ≤ 1/2`. -/
lemma eventually_le_half {u : ℕ → ℝ}
    (hu : Tendsto (fun d : ℕ => (d : ℝ) * u d ^ 2) atTop (𝓝 0)) :
    ∀ᶠ d in atTop, u d ≤ 1 / 2 := by
  filter_upwards [hu.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    eventually_ge_atTop 1] with d hd hd1
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have : u d ^ 2 < 1 / 4 := by nlinarith [sq_nonneg (u d)]
  nlinarith

/-! ### Generic cutoff statements -/

section Generic

variable {m t : ℕ → ℝ} {r : ℝ}

/-- Common hypotheses for the upper bounds. -/
def UpperHyp (m t : ℕ → ℝ) (A K : ℝ) : Prop :=
  (∀ᶠ d : ℕ in atTop, Admissible d (m d) ∧ (d : ℝ) / (d + 2) < m d ∧ 0 < t d ∧
    alpha d (m d) ≤ A ∧ eqSecondMoment d (m d) ≤ K * d) ∧
  Tendsto (fun d : ℕ => (d : ℝ) * exp (-t d / alpha d (m d)) ^ 2) atTop (𝓝 0) ∧
  Tendsto (fun d : ℕ => (d : ℝ) * exp (-t d) ^ 2) atTop (𝓝 0)

lemma UpperHyp.eventually {A K : ℝ} (H : UpperHyp m t A K) :
    ∀ᶠ d : ℕ in atTop, Admissible d (m d) ∧ (d : ℝ) / (d + 2) < m d ∧ 0 < t d ∧
      alpha d (m d) ≤ A ∧ eqSecondMoment d (m d) ≤ K * d ∧ exp (-t d / alpha d (m d)) ≤ 1 / 2 :=
  by
  filter_upwards [H.1, eventually_le_half H.2.1] with d hd hu
  exact ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2, hu⟩

lemma tendsto_bound {A K C D : ℝ} (H : UpperHyp m t A K) :
    Tendsto (fun d : ℕ => C * K * ((d : ℝ) * exp (-t d / alpha d (m d)) ^ 2) +
      D * ((d : ℝ) * exp (-t d) ^ 2)) atTop (𝓝 0) := by
  simpa using (H.2.1.const_mul (C * K)).add (H.2.2.const_mul D)

lemma wassersteinSq_upper {A K : ℝ} (H : UpperHyp m t A K) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
      wassersteinSq (densityMeasure (solution d (m d) x₀ (t d)))
        (densityMeasure (equilibrium d (m d)))) atTop (𝓝 0) := by
  refine tendsto_iSup_ennreal_zero (tendsto_bound (C := max 1 A ^ 2) (D := r ^ 2) H) ?_
  filter_upwards [H.eventually] with d ⟨h, h2, ht, hA, hK, hu⟩ x₀ hx₀
  refine (wassersteinSq_le h h2 ht hu x₀ (sq_le_of_mem_closedBall hx₀)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hM := (eqSecondMoment_pos h h2).le
  have h1 : max 1 (alpha d (m d)) ^ 2 ≤ max 1 A ^ 2 :=
    pow_le_pow_left₀ (by positivity) (max_le_max le_rfl hA) 2
  have h3 : max 1 (alpha d (m d)) ^ 2 * eqSecondMoment d (m d) ≤ max 1 A ^ 2 * (K * d) :=
    mul_le_mul h1 hK hM (by positivity)
  have := mul_le_mul_of_nonneg_right h3 (sq_nonneg (exp (-t d / alpha d (m d))))
  nlinarith

lemma relEntropy_upper {A K : ℝ} (hr : 0 < r) (H : UpperHyp m t A K) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
      (relEntropy (m d) (solution d (m d) x₀ (t d)) (equilibrium d (m d)) : EReal))
        atTop (𝓝 0) := by
  refine tendsto_iSup_ereal_zero (tendsto_bound (C := 2 * A) (D := r ^ 2 / 2) H)
    (Eventually.of_forall fun d => by positivity) ?_
  filter_upwards [H.eventually] with d ⟨h, h2, ht, hA, hK, hu⟩ x₀ hx₀
  obtain ⟨h0, h1⟩ := relEntropy_le h h2 ht hu x₀ (sq_le_of_mem_closedBall hx₀)
  refine ⟨h0, h1.trans ?_⟩
  have hM := (eqSecondMoment_pos h h2).le
  have hα := (alpha_pos h).le
  have h3 : 2 * alpha d (m d) * eqSecondMoment d (m d) ≤ 2 * A * (K * d) :=
    mul_le_mul (by linarith) hK hM (by linarith)
  have := mul_le_mul_of_nonneg_right h3 (sq_nonneg (exp (-t d / alpha d (m d))))
  nlinarith

lemma fisherInfo_upper {A K : ℝ} (H : UpperHyp m t A K) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
      fisherInfo (m d) (solution d (m d) x₀ (t d))) atTop (𝓝 0) := by
  refine tendsto_iSup_ennreal_zero (tendsto_bound (C := 4) (D := r ^ 2) H) ?_
  filter_upwards [H.eventually] with d ⟨h, h2, ht, hA, hK, hu⟩ x₀ hx₀
  refine (fisherInfo_le h h2 ht hu x₀ (sq_le_of_mem_closedBall hx₀)).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have := mul_le_mul_of_nonneg_left hK
    (by positivity : (0 : ℝ) ≤ 4 * exp (-t d / alpha d (m d)) ^ 2)
  nlinarith

/-- Common hypotheses for the lower bounds driven by the translation `e^{-t}x₀`. -/
def ShiftHyp (m t : ℕ → ℝ) : Prop :=
  (∀ᶠ d : ℕ in atTop, Admissible d (m d) ∧ (d : ℝ) / (d + 2) < m d ∧ 0 < t d) ∧
  Tendsto (fun d : ℕ => (d : ℝ) * exp (-t d) ^ 2) atTop atTop

lemma ShiftHyp.exists (hr : 0 < r) (H : ShiftHyp m t) :
    ∀ᶠ d : ℕ in atTop, Admissible d (m d) ∧ (d : ℝ) / (d + 2) < m d ∧ 0 < t d ∧
      ∃ x₀ ∈ closedBall (0 : E d) (r * √d), ‖x₀‖ ^ 2 = r ^ 2 * d := by
  filter_upwards [H.1] with d ⟨h, h2, ht⟩
  obtain ⟨x, hx⟩ := exists_norm_eq_of_one_le h.1 (by positivity : 0 ≤ r * √d)
  refine ⟨h, h2, ht, x, by rw [mem_closedBall_zero_iff, hx], ?_⟩
  rw [hx, mul_pow, sq_sqrt (Nat.cast_nonneg _)]

lemma wassersteinSq_lower_shift (hr : 0 < r) (H : ShiftHyp m t) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
      wassersteinSq (densityMeasure (solution d (m d) x₀ (t d)))
        (densityMeasure (equilibrium d (m d)))) atTop (𝓝 ⊤) := by
  refine tendsto_iSup_ennreal_top (H.2.const_mul_atTop (by positivity : 0 < r ^ 2)) ?_
  filter_upwards [H.exists hr] with d ⟨h, h2, ht, x, hx, hnx⟩
  refine ⟨x, hx, le_trans (le_of_eq ?_) (le_wassersteinSq h h2 ht x)⟩
  rw [hnx]; ring_nf

lemma relEntropy_lower_shift (hr : 0 < r) (H : ShiftHyp m t) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
      (relEntropy (m d) (solution d (m d) x₀ (t d)) (equilibrium d (m d)) : EReal))
        atTop (𝓝 ⊤) := by
  refine tendsto_iSup_ereal_top (H.2.const_mul_atTop (by positivity : 0 < r ^ 2 / 2)) ?_
  filter_upwards [H.exists hr] with d ⟨h, h2, ht, x, hx, hnx⟩
  refine ⟨x, hx, le_trans (le_of_eq ?_) (le_relEntropy h h2 ht x)⟩
  rw [hnx]; ring

lemma fisherInfo_lower_shift (hr : 0 < r) (H : ShiftHyp m t) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
      fisherInfo (m d) (solution d (m d) x₀ (t d))) atTop (𝓝 ⊤) := by
  refine tendsto_iSup_ennreal_top (H.2.const_mul_atTop (by positivity : 0 < r ^ 2)) ?_
  filter_upwards [H.exists hr] with d ⟨h, h2, ht, x, hx, hnx⟩
  refine ⟨x, hx, le_trans (le_of_eq ?_) (le_fisherInfo h h2 ht x)⟩
  rw [hnx]; ring_nf

/-- Common hypotheses for the lower bounds driven by the dilation, for a fixed `α ≥ 1`. -/
def ScaleHyp (m t : ℕ → ℝ) (α k : ℝ) : Prop :=
  (∀ᶠ d : ℕ in atTop, Admissible d (m d) ∧ (d : ℝ) / (d + 2) < m d ∧ 0 < t d ∧
    alpha d (m d) = α ∧ k * d ≤ eqSecondMoment d (m d)) ∧
  Tendsto (fun d : ℕ => (d : ℝ) * exp (-t d / α) ^ 2) atTop atTop ∧
  Tendsto (fun d : ℕ => exp (-t d / α)) atTop (𝓝 0)

lemma ScaleHyp.eventually {α k : ℝ} (H : ScaleHyp m t α k) :
    ∀ᶠ d : ℕ in atTop, Admissible d (m d) ∧ (d : ℝ) / (d + 2) < m d ∧ 0 < t d ∧
      alpha d (m d) = α ∧ k * d ≤ eqSecondMoment d (m d) ∧ exp (-t d / α) ≤ 1 / 2 := by
  filter_upwards [H.1, H.2.2.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with d hd hu
  exact ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2, hu⟩

lemma lower_scale_bound {α k c : ℝ} {d : ℕ} {M : ℝ} (hc : 0 ≤ c) (hk : k * d ≤ M) :
    c * k * ((d : ℝ) * exp (-t d / α) ^ 2) ≤ c * exp (-t d / α) ^ 2 * M := by
  have := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ c * exp (-t d / α) ^ 2)
  nlinarith

lemma wassersteinSq_lower_scale {α k : ℝ} (hr : 0 < r) (hα : 1 ≤ α) (hk : 0 < k)
    (H : ScaleHyp m t α k) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
      wassersteinSq (densityMeasure (solution d (m d) x₀ (t d)))
        (densityMeasure (equilibrium d (m d)))) atTop (𝓝 ⊤) := by
  refine tendsto_iSup_ennreal_top (H.2.1.const_mul_atTop (by positivity : 0 < 1 * k)) ?_
  filter_upwards [H.eventually] with d ⟨h, h2, ht, hαd, hk', hu⟩
  refine ⟨0, mem_closedBall_self (by positivity), le_trans ?_
    (le_wassersteinSq_of_one_le h h2 ht (hαd ▸ hα) (hαd ▸ hu) 0)⟩
  rw [hαd]
  exact ENNReal.ofReal_le_ofReal (by simpa using lower_scale_bound zero_le_one hk')

lemma relEntropy_lower_scale {α k : ℝ} (hr : 0 < r) (hα : 1 ≤ α) (hk : 0 < k)
    (H : ScaleHyp m t α k) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
      (relEntropy (m d) (solution d (m d) x₀ (t d)) (equilibrium d (m d)) : EReal))
        atTop (𝓝 ⊤) := by
  have hc : 0 < α * (1 / 2) ^ (2 * α - 2) / 2 := by
    have := rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) (2 * α - 2)
    positivity
  refine tendsto_iSup_ereal_top (H.2.1.const_mul_atTop (mul_pos hc hk)) ?_
  filter_upwards [H.eventually] with d ⟨h, h2, ht, hαd, hk', hu⟩
  refine ⟨0, mem_closedBall_self (by positivity), le_trans ?_
    (le_relEntropy_of_one_le h h2 ht (hαd ▸ hα) (hαd ▸ hu) 0)⟩
  rw [hαd]
  exact lower_scale_bound hc.le hk'

lemma fisherInfo_lower_scale {α k : ℝ} (hr : 0 < r) (hk : 0 < k)
    (H : ScaleHyp m t α k) :
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
      fisherInfo (m d) (solution d (m d) x₀ (t d))) atTop (𝓝 ⊤) := by
  have hc : 0 < ((1 / 2 : ℝ) ^ α) ^ 2 := by
    have := rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) α
    positivity
  refine tendsto_iSup_ennreal_top (H.2.1.const_mul_atTop (mul_pos hc hk)) ?_
  filter_upwards [H.eventually] with d ⟨h, h2, ht, hαd, hk', hu⟩
  refine ⟨0, mem_closedBall_self (by positivity), le_trans ?_
    (le_fisherInfo_of_one_le h h2 ht (hαd ▸ hu) 0)⟩
  rw [hαd]
  exact ENNReal.ofReal_le_ofReal (lower_scale_bound hc.le hk')

end Generic

/-! ### Parameters of Theorem 1.1 (`α` fixed) -/

lemma alpha_exponentOfAlpha {α : ℝ} (hα : 0 < α) {d : ℕ} (hd : 1 ≤ d) :
    alpha d (exponentOfAlpha α d) = α := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold alpha exponentOfAlpha
  have : 2 - (d : ℝ) * (1 - ((d - 2) * α + 1) / (d * α)) = 1 / α := by
    field_simp; ring
  rw [this, one_div_one_div]

lemma eventually_admissible_exponentOfAlpha {α : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) :
    ∀ᶠ d : ℕ in atTop, Admissible d (exponentOfAlpha α d) ∧
      (d : ℝ) / (d + 2) < exponentOfAlpha α d ∧ alpha d (exponentOfAlpha α d) = α ∧ 2 ≤ d := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * α)
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop N] with d hd hdN
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdN' : (N : ℝ) ≤ d := by exact_mod_cast hdN
  have hdα : 0 < (d : ℝ) * α := by positivity
  refine ⟨⟨by omega, ?_, ?_, ?_⟩, ?_, alpha_exponentOfAlpha hα (by omega), hd⟩
  · unfold exponentOfAlpha; apply div_pos _ hdα; nlinarith
  · unfold exponentOfAlpha; intro h; rw [div_eq_one_iff_eq hdα.ne'] at h; apply hα2; linarith
  · unfold exponentOfAlpha; rw [div_lt_div_iff₀ (by positivity) hdα]; nlinarith
  · unfold exponentOfAlpha; rw [div_lt_div_iff₀ (by positivity) hdα]; nlinarith

lemma one_sub_exponentOfAlpha {α : ℝ} (hα : 0 < α) {d : ℕ} (hd : 1 ≤ d) :
    1 - exponentOfAlpha α d = (2 * α - 1) / (d * α) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold exponentOfAlpha
  field_simp
  ring

/-- `M₂/d` converges to a positive limit (Lemmas 3.1 and 4.1). -/
lemma tendsto_eqSecondMoment_div {α : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) :
    ∃ K > 0, Tendsto (fun d : ℕ => eqSecondMoment d (exponentOfAlpha α d) / d) atTop (𝓝 K) := by
  rcases lt_or_gt_of_ne hα2 with h | h
  · refine ⟨1 / (2 * π * exp 1) ^ (1 - 2 * α), by positivity,
      (compactBarenblatt_asymptotics' hα h).1.congr' ?_⟩
    filter_upwards [eventually_admissible_exponentOfAlpha hα hα2] with d ⟨hadm, _, _, hd⟩
    have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 1 ≤ d)
    have hm : 1 < exponentOfAlpha α d := by
      have := one_sub_exponentOfAlpha hα (d := d) (by omega)
      have : (2 * α - 1) / (d * α) < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
      linarith
    unfold eqSecondMoment
    rw [equilibrium_eq_compactBarenblatt hadm hm]
  · refine ⟨(2 * π * exp 1) ^ (2 * α - 1), by positivity,
      (fullBarenblatt_asymptotics' h).1.congr' ?_⟩
    filter_upwards [eventually_admissible_exponentOfAlpha hα hα2] with d ⟨hadm, _, _, hd⟩
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have h1m := one_sub_exponentOfAlpha hα (d := d) (by omega)
    have hm : exponentOfAlpha α d < 1 := by
      have : 0 < (2 * α - 1) / (d * α) := div_pos (by linarith) (by positivity)
      linarith
    have e1 : 1 / (1 - exponentOfAlpha α d) = d * α / (2 * α - 1) := by
      rw [h1m, one_div_div]
    have e2 : (1 - exponentOfAlpha α d) / (2 * exponentOfAlpha α d) =
        (2 * α - 1) / (2 * (α * (d - 2) + 1)) := by
      have : 0 < (d - 2) * α + 1 := by nlinarith
      rw [h1m]
      unfold exponentOfAlpha
      field_simp
    unfold eqSecondMoment
    rw [equilibrium_eq_fullBarenblatt hadm hm, e1, e2]

/-- Two-sided linear bounds from a positive limit of `M d / d`. -/
lemma bounds_of_tendsto_div {M : ℕ → ℝ} {K : ℝ} (hK : 0 < K)
    (h : Tendsto (fun d : ℕ => M d / d) atTop (𝓝 K)) :
    ∀ᶠ d : ℕ in atTop, K / 2 * d ≤ M d ∧ M d ≤ 2 * K * d := by
  filter_upwards [h.eventually (Ioo_mem_nhds (by linarith : K / 2 < K) (by linarith : K < 2 * K)),
    eventually_ge_atTop 1] with d hd hd1
  have : (0 : ℝ) < d := by exact_mod_cast hd1
  rw [lt_div_iff₀ this, div_lt_iff₀ this] at hd
  exact ⟨hd.1.le, hd.2.le⟩

lemma neg_mul_div_eq (c x α : ℝ) : -(c * x) / α = -(c / α * x) := by ring

lemma upperHyp_alpha {α ε : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hε : 0 < ε) :
    ∃ K, UpperHyp (fun d => exponentOfAlpha α d) (fun d => (1 + ε) * (max 1 α / 2) * log d)
      α K := by
  obtain ⟨K, hK, hM⟩ := tendsto_eqSecondMoment_div hα hα2
  have hc : 0 < (1 + ε) * (max 1 α / 2) := by positivity
  have hmax : 1 ≤ max 1 α := le_max_left _ _
  have hmaxα : 1 ≤ max 1 α / α := by rw [le_div_iff₀ hα]; simp
  refine ⟨2 * K, ?_, ?_, ?_⟩
  · filter_upwards [eventually_admissible_exponentOfAlpha hα hα2, bounds_of_tendsto_div hK hM]
      with d ⟨h, h2, hαd, hd⟩ hb
    exact ⟨h, h2, mul_pos hc (log_natCast_pos hd), hαd.le, hb.2⟩
  · have : Tendsto (fun d : ℕ => (d : ℝ) *
        exp (-((1 + ε) * (max 1 α / 2) / α * log d)) ^ 2) atTop (𝓝 0) := by
      apply tendsto_mul_exp_sq_zero
      have : 2 * ((1 + ε) * (max 1 α / 2) / α) = (1 + ε) * (max 1 α / α) := by ring
      rw [this]; nlinarith
    refine this.congr' ?_
    filter_upwards [eventually_admissible_exponentOfAlpha hα hα2] with d ⟨_, _, hαd, _⟩
    rw [hαd, neg_mul_div_eq]
  · apply tendsto_mul_exp_sq_zero
    nlinarith

lemma shiftHyp_alpha {α ε : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hε : 0 < ε) (hε1 : ε < 1)
    (h1 : α ≤ 1) :
    ShiftHyp (fun d => exponentOfAlpha α d) (fun d => (1 - ε) * (max 1 α / 2) * log d) := by
  have hmax : max 1 α = 1 := max_eq_left h1
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_admissible_exponentOfAlpha hα hα2] with d ⟨h, h2, _, hd⟩
    refine ⟨h, h2, mul_pos ?_ (log_natCast_pos hd)⟩
    rw [hmax]; linarith
  · apply tendsto_mul_exp_sq_atTop
    rw [hmax]; linarith

lemma scaleHyp_alpha {α ε : ℝ} (hα2 : α ≠ 1 / 2) (hε : 0 < ε) (hε1 : ε < 1) (h1 : 1 < α) :
    ∃ k > 0, ScaleHyp (fun d => exponentOfAlpha α d)
      (fun d => (1 - ε) * (max 1 α / 2) * log d) α k := by
  have hα : 0 < α := by linarith
  have hmax : max 1 α = α := max_eq_right h1.le
  obtain ⟨K, hK, hM⟩ := tendsto_eqSecondMoment_div hα hα2
  refine ⟨K / 2, by positivity, ?_, ?_, ?_⟩
  · filter_upwards [eventually_admissible_exponentOfAlpha hα hα2, bounds_of_tendsto_div hK hM]
      with d ⟨h, h2, hαd, hd⟩ hb
    refine ⟨h, h2, mul_pos ?_ (log_natCast_pos hd), hαd, hb.1⟩
    rw [hmax]; nlinarith
  · simp_rw [neg_mul_div_eq]
    apply tendsto_mul_exp_sq_atTop
    rw [hmax, show 2 * ((1 - ε) * (α / 2) / α) = 1 - ε by field_simp]
    linarith
  · simp_rw [neg_mul_div_eq]
    apply tendsto_exp_neg_mul_log
    rw [hmax]
    have : 0 < 1 - ε := by linarith
    positivity

/-! ### Parameters of Theorem 1.2 (`m > 1` fixed) -/

lemma admissible_of_one_lt {m : ℝ} (hm : 1 < m) {d : ℕ} (hd : 1 ≤ d) :
    Admissible d m ∧ (d : ℝ) / (d + 2) < m := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨⟨hd, by linarith, hm.ne', ?_⟩, ?_⟩
  · exact lt_trans ((div_lt_one hd').2 (by linarith)) hm
  · exact lt_trans ((div_lt_one (by linarith)).2 (by linarith)) hm

lemma alpha_le_half {m : ℝ} (hm : 1 < m) (d : ℕ) : alpha d m ≤ 1 / 2 := by
  unfold alpha
  have : (d : ℝ) * (1 - m) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- `M₂/d → 1/(2πe)` (Lemma 4.2). -/
lemma tendsto_eqSecondMoment_div_fixed {m : ℝ} (hm : 1 < m) :
    Tendsto (fun d : ℕ => eqSecondMoment d m / d) atTop (𝓝 (1 / (2 * π * exp 1))) := by
  have h := (compactBarenblatt_fixedExponent_asymptotics' hm).2.1
  have h' := h.div (Asymptotics.IsEquivalent.refl (u := fun d : ℕ => (d : ℝ)))
  have hlim : Tendsto (fun d : ℕ => (d : ℝ) / (2 * π * exp 1) / d) atTop
      (𝓝 (1 / (2 * π * exp 1))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with d hd
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    field_simp
  refine (h'.symm.tendsto_nhds hlim).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with d hd
  simp only [Pi.div_apply]
  unfold eqSecondMoment
  rw [equilibrium_eq_compactBarenblatt (admissible_of_one_lt hm hd).1 hm]

lemma upperHyp_fixed {m ε : ℝ} (hm : 1 < m) (hε : 0 < ε) :
    ∃ K, UpperHyp (fun _ => m) (fun d => (1 + ε) / 2 * log d) (1 / 2) K := by
  have hK : (0 : ℝ) < 1 / (2 * π * exp 1) := by positivity
  have he : Tendsto (fun d : ℕ => (d : ℝ) * exp (-((1 + ε) / 2 * log d)) ^ 2) atTop (𝓝 0) :=
    tendsto_mul_exp_sq_zero (by linarith)
  refine ⟨2 * (1 / (2 * π * exp 1)), ?_, ?_, he⟩
  · filter_upwards [eventually_ge_atTop 2, bounds_of_tendsto_div hK
      (tendsto_eqSecondMoment_div_fixed hm)] with d hd hb
    obtain ⟨h, h2⟩ := admissible_of_one_lt hm (by omega : 1 ≤ d)
    exact ⟨h, h2, mul_pos (by linarith) (log_natCast_pos hd), alpha_le_half hm d, hb.2⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
      (Eventually.of_forall fun d => by positivity) ?_
    filter_upwards [eventually_ge_atTop 1] with d hd
    obtain ⟨h, -⟩ := admissible_of_one_lt hm hd
    have hα := alpha_pos h
    have hα1 := alpha_le_half hm d
    have ht : 0 ≤ (1 + ε) / 2 * log d := mul_nonneg (by linarith) (log_natCast_nonneg d)
    have : exp (-((1 + ε) / 2 * log d) / alpha d m) ≤ exp (-((1 + ε) / 2 * log d)) := by
      apply exp_le_exp.2
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ hα]
      nlinarith
    have h0 := (exp_pos (-((1 + ε) / 2 * log d) / alpha d m)).le
    have := pow_le_pow_left₀ h0 this 2
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)

lemma shiftHyp_fixed {m ε : ℝ} (hm : 1 < m) (hε : 0 < ε) (hε1 : ε < 1) :
    ShiftHyp (fun _ => m) (fun d => (1 - ε) / 2 * log d) := by
  refine ⟨?_, tendsto_mul_exp_sq_atTop (by linarith)⟩
  filter_upwards [eventually_ge_atTop 2] with d hd
  obtain ⟨h, h2⟩ := admissible_of_one_lt hm (by omega : 1 ≤ d)
  exact ⟨h, h2, mul_pos (by linarith) (log_natCast_pos hd)⟩

end Cutoff

open Cutoff

/-- **Theorem 1.1, Wasserstein distance.** Fix `α ∈ (0,1/2) ∪ (1/2,∞)`, `r > 0`, and let
`m = ((d-2)α+1)/(dα)`. Then `sup_{|x₀| ≤ r√d} W₂²(v(t_d), v_∞)` tends to `+∞` if
`t_d = (1-ε) max(1,α)/2 log d` and to `0` if `t_d = (1+ε) max(1,α)/2 log d`. -/
theorem cutoff_wassersteinSq' {α r ε : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        wassersteinSq
          (densityMeasure (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * (max 1 α / 2) * log d)))
          (densityMeasure (equilibrium d (exponentOfAlpha α d)))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        wassersteinSq
          (densityMeasure (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * (max 1 α / 2) * log d)))
          (densityMeasure (equilibrium d (exponentOfAlpha α d)))) atTop (𝓝 0) := by
  refine ⟨fun hε1 => ?_, ?_⟩
  · rcases le_or_gt α 1 with h1 | h1
    · exact wassersteinSq_lower_shift hr (shiftHyp_alpha hα hα2 hε hε1 h1)
    · obtain ⟨k, hk, H⟩ := scaleHyp_alpha hα2 hε hε1 h1
      exact wassersteinSq_lower_scale hr h1.le hk H
  · obtain ⟨K, H⟩ := upperHyp_alpha hα hα2 hε
    exact wassersteinSq_upper H

/-- **Theorem 1.1, relative entropy.** Same setting as `cutoff_wassersteinSq`. For large `d`
the entropy integrand is integrable for all `t > 0` and `|x₀| ≤ r√d`, and
`sup_{|x₀| ≤ r√d} Hₘ(v(t_d) | v_∞)` tends to `+∞` if `t_d = (1-ε) max(1,α)/2 log d`
and to `0` if `t_d = (1+ε) max(1,α)/2 log d`. -/
theorem cutoff_relEntropy' {α r ε : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (∀ᶠ d : ℕ in atTop, ∀ x₀ ∈ closedBall (0 : E d) (r * √d), ∀ t > 0,
      Integrable (relEntropyDensity (exponentOfAlpha α d) (solution d (exponentOfAlpha α d) x₀ t)
        (equilibrium d (exponentOfAlpha α d)))) ∧
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        (relEntropy (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * (max 1 α / 2) * log d))
          (equilibrium d (exponentOfAlpha α d)) : EReal)) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        (relEntropy (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * (max 1 α / 2) * log d))
          (equilibrium d (exponentOfAlpha α d)) : EReal)) atTop (𝓝 0) := by
  refine ⟨?_, fun hε1 => ?_, ?_⟩
  · filter_upwards [eventually_admissible_exponentOfAlpha hα hα2] with d ⟨h, h2, _, _⟩ x₀ _ t ht
    exact integrable_relEntropyDensity_solution h h2 x₀ ht
  · rcases le_or_gt α 1 with h1 | h1
    · exact relEntropy_lower_shift hr (shiftHyp_alpha hα hα2 hε hε1 h1)
    · obtain ⟨k, hk, H⟩ := scaleHyp_alpha hα2 hε hε1 h1
      exact relEntropy_lower_scale hr h1.le hk H
  · obtain ⟨K, H⟩ := upperHyp_alpha hα hα2 hε
    exact relEntropy_upper hr H

/-- **Theorem 1.1, Fisher information.** Same setting as `cutoff_wassersteinSq`:
`sup_{|x₀| ≤ r√d} Iₘ(v(t_d) | v_∞)` tends to `+∞` if `t_d = (1-ε) max(1,α)/2 log d`
and to `0` if `t_d = (1+ε) max(1,α)/2 log d`. -/
theorem cutoff_fisherInfo' {α r ε : ℝ} (hα : 0 < α) (hα2 : α ≠ 1 / 2) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        fisherInfo (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 - ε) * (max 1 α / 2) * log d))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        fisherInfo (exponentOfAlpha α d)
          (solution d (exponentOfAlpha α d) x₀ ((1 + ε) * (max 1 α / 2) * log d))) atTop (𝓝 0) := by
  refine ⟨fun hε1 => ?_, ?_⟩
  · rcases le_or_gt α 1 with h1 | h1
    · exact fisherInfo_lower_shift hr (shiftHyp_alpha hα hα2 hε hε1 h1)
    · obtain ⟨k, hk, H⟩ := scaleHyp_alpha hα2 hε hε1 h1
      exact fisherInfo_lower_scale hr hk H
  · obtain ⟨K, H⟩ := upperHyp_alpha hα hα2 hε
    exact fisherInfo_upper H

/-- **Theorem 1.2, Wasserstein distance.** Fix `m > 1` and `r > 0` (so that
`α = 1/(2 - d(1-m)) → 0`). Then `sup_{|x₀| ≤ r√d} W₂²(v(t_d), v_∞)` tends to `+∞` if
`t_d = (1-ε)/2 log d` and to `0` if `t_d = (1+ε)/2 log d`. -/
theorem cutoff_fixedExponent_wassersteinSq' {m r ε : ℝ} (hm : 1 < m) (hr : 0 < r)
    (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        wassersteinSq (densityMeasure (solution d m x₀ ((1 - ε) / 2 * log d)))
          (densityMeasure (equilibrium d m))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        wassersteinSq (densityMeasure (solution d m x₀ ((1 + ε) / 2 * log d)))
          (densityMeasure (equilibrium d m))) atTop (𝓝 0) := by
  obtain ⟨K, H⟩ := upperHyp_fixed hm hε
  exact ⟨fun hε1 => wassersteinSq_lower_shift hr (shiftHyp_fixed hm hε hε1),
    wassersteinSq_upper H⟩

/-- **Theorem 1.2, relative entropy.** Same setting as `cutoff_fixedExponent_wassersteinSq`,
with integrability of the entropy integrand for large `d`. -/
theorem cutoff_fixedExponent_relEntropy' {m r ε : ℝ} (hm : 1 < m) (hr : 0 < r) (hε : 0 < ε) :
    (∀ᶠ d : ℕ in atTop, ∀ x₀ ∈ closedBall (0 : E d) (r * √d), ∀ t > 0,
      Integrable (relEntropyDensity m (solution d m x₀ t) (equilibrium d m))) ∧
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        (relEntropy m (solution d m x₀ ((1 - ε) / 2 * log d)) (equilibrium d m) : EReal))
        atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        (relEntropy m (solution d m x₀ ((1 + ε) / 2 * log d)) (equilibrium d m) : EReal))
        atTop (𝓝 0) := by
  obtain ⟨K, H⟩ := upperHyp_fixed hm hε
  refine ⟨?_, fun hε1 => relEntropy_lower_shift hr (shiftHyp_fixed hm hε hε1),
    relEntropy_upper hr H⟩
  filter_upwards [eventually_ge_atTop 1] with d hd x₀ _ t ht
  obtain ⟨h, h2⟩ := admissible_of_one_lt hm hd
  exact integrable_relEntropyDensity_solution h h2 x₀ ht

/-- **Theorem 1.2, Fisher information.** Same setting as
`cutoff_fixedExponent_wassersteinSq`. -/
theorem cutoff_fixedExponent_fisherInfo' {m r ε : ℝ} (hm : 1 < m) (hr : 0 < r) (hε : 0 < ε) :
    (ε < 1 → Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        fisherInfo m (solution d m x₀ ((1 - ε) / 2 * log d))) atTop (𝓝 ⊤)) ∧
    Tendsto (fun d : ℕ => ⨆ x₀ ∈ closedBall (0 : E d) (r * √d),
        fisherInfo m (solution d m x₀ ((1 + ε) / 2 * log d))) atTop (𝓝 0) := by
  obtain ⟨K, H⟩ := upperHyp_fixed hm hε
  exact ⟨fun hε1 => fisherInfo_lower_shift hr (shiftHyp_fixed hm hε hε1), fisherInfo_upper H⟩

end Cutfast
