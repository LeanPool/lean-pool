/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Moments
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# High-dimensional asymptotics of the Barenblatt moments (Lemmas 3.1, 4.1, 4.2)
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace

namespace Cutfast.Asymptotics

/-! ### A crude real Stirling formula -/


/-- Upper bound for factorials from the monotonicity of the Stirling sequence. -/
lemma log_factorial_le {n : ℕ} (hn : 1 ≤ n) :
    log (n.factorial : ℝ) ≤ n * log n - n + (1 / 2) * log n + 1 := by
  have h1 : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  rw [Stirling.stirlingSeq_one] at h1
  unfold Stirling.stirlingSeq at h1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < √(2 * n : ℝ) * (n / exp 1) ^ n := by positivity
  rw [div_le_iff₀ hpos] at h1
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have := log_le_log hf h1
  have hs2 : (0 : ℝ) < √2 := by positivity
  rw [log_mul (by positivity) hpos.ne', log_mul (by positivity) (by positivity), log_div
    (by positivity) hs2.ne',
    log_exp, log_pow, log_div hn'.ne' (exp_pos 1).ne', log_exp] at this
  have h2 : log (√2) = log 2 / 2 := by rw [log_sqrt (by norm_num)]
  have h3 : log (√(2 * n)) = (log 2 + log n) / 2 := by
    rw [log_sqrt (by positivity), log_mul (by norm_num) hn'.ne']
  rw [h2, h3] at this
  linarith

lemma log_factorial_ge (n : ℕ) : n * log n - n ≤ log (n.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Stirling.le_factorial_stirling n
  have h1 : 1 ≤ √(2 * π * n) := by
    rw [Real.one_le_sqrt]
    nlinarith [pi_gt_three, (show (1 : ℝ) ≤ n by exact_mod_cast hn)]
  have h2 : (n / exp 1) ^ n ≤ (n.factorial : ℝ) := by
    have : 0 ≤ (n / exp 1 : ℝ) ^ n := by positivity
    nlinarith
  have := log_le_log (by positivity) h2
  rw [log_pow, log_div hn'.ne' (exp_pos 1).ne', log_exp] at this
  linarith

/-- Crude real Stirling bound: `|log Γ(x) - (x log x - x)| ≤ 2 log x + 2` for `x ≥ 4`. -/
lemma abs_log_Gamma_sub_le {x : ℝ} (hx : 4 ≤ x) :
    |log (Gamma x) - (x * log x - x)| ≤ 2 * log x + 2 := by
  set n := ⌊x⌋₊ with hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hn4 : 4 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hx0 : 0 < x := by linarith
  have hlogx : 1 ≤ log x := by
    rw [le_log_iff_exp_le hx0]; linarith [exp_one_lt_d9]
  -- upper bound
  have hup : Gamma x ≤ Gamma (n + 1) :=
    Gamma_strictMonoOn_Ici.monotoneOn (by simp; linarith) (by simp; linarith) hxn.le
  rw [Gamma_nat_eq_factorial] at hup
  have hup' := (log_le_log (Gamma_pos_of_pos hx0) hup).trans (log_factorial_le (by omega))
  -- lower bound
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hlow : Gamma (k + 1) ≤ Gamma x :=
    Gamma_strictMonoOn_Ici.monotoneOn (by simp; norm_cast; omega) (by simp; linarith)
      (by rw [hk] at hnx; push_cast at hnx; linarith)
  rw [Gamma_nat_eq_factorial] at hlow
  have hlow' := (log_factorial_ge k).trans (log_le_log (by positivity) hlow)
  have hk' : (n : ℝ) = k + 1 := by rw [hk]; push_cast; ring
  have hk0 : (0 : ℝ) < k := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn : log n ≤ log x := log_le_log hn0 hnx
  have hq1 : log x - log n ≤ x / n - 1 := by
    rw [← log_div hx0.ne' hn0.ne']; exact log_le_sub_one_of_pos (by positivity)
  have hq2 : log x - log k ≤ x / k - 1 := by
    rw [← log_div hx0.ne' hk0.ne']; exact log_le_sub_one_of_pos (by positivity)
  have hq1' : n * (log x - log n) ≥ 0 := by
    have := log_le_log hn0 hnx; nlinarith
  have hq2' : k * (log x - log k) ≤ x - k := by
    have := mul_le_mul_of_nonneg_left hq2 hk0.le
    rwa [mul_sub_one, mul_div_cancel₀ _ hk0.ne'] at this
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- Stirling-lite: `log Γ(x) = x log x - x + o(x)`. -/
lemma tendsto_log_Gamma_div_sub :
    Tendsto (fun x => (log (Gamma x) - (x * log x - x)) / x) atTop (𝓝 0) := by
  have hlim : Tendsto (fun x => (2 * log x + 2) / x) atTop (𝓝 0) := by
    have h1 := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul 2
    have h2 := tendsto_inv_atTop_zero.const_mul (2 : ℝ)
    have := h1.add h2
    simp only [pow_one, one_mul, add_zero, mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    field_simp
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 4] with x hx
  simp only [Function.comp_apply, abs_div, abs_of_pos (show 0 < x by linarith)]
  exact div_le_div_of_nonneg_right (abs_log_Gamma_sub_le hx) (by linarith)

lemma tendsto_log_div_self' : Tendsto (fun z : ℝ => log z / z) atTop (𝓝 0) := by
  simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero

lemma tendsto_affine_div {a c : ℝ} : Tendsto (fun z : ℝ => (a * z + c) / z) atTop (𝓝 a) := by
  have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul c |>.const_add a
  simp only [mul_zero, add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with z hz
  field_simp

lemma tendsto_affine_atTop {a c : ℝ} (ha : 0 < a) : Tendsto (fun z : ℝ => a * z + c) atTop atTop :=
  tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop ha)

/-- `log (a z + c) - log z → log a`. -/
lemma tendsto_log_affine_sub_log {a c : ℝ} (ha : 0 < a) :
    Tendsto (fun z : ℝ => log (a * z + c) - log z) atTop (𝓝 (log a)) := by
  have := (tendsto_affine_div (a := a) (c := c)).log ha.ne'
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0, (tendsto_affine_atTop (c := c) ha).eventually_gt_atTop 0]
    with z hz hy
  rw [log_div hy.ne' hz.ne']

/-- Affine Stirling-lite: `log Γ(a z + c) = a z log z + (a log a - a) z + o(z)`. -/
lemma tendsto_log_Gamma_affine {a c : ℝ} (ha : 0 < a) :
    Tendsto (fun z : ℝ => log (Gamma (a * z + c)) / z - a * log z) atTop
      (𝓝 (a * log a - a)) := by
  have hy := tendsto_affine_atTop (c := c) ha
  have h1 := (tendsto_log_Gamma_div_sub.comp hy).mul (tendsto_affine_div (a := a) (c := c))
  have h2 := tendsto_log_div_self'.const_mul c
  have h3 := (tendsto_affine_div (a := a) (c := c)).mul
    ((tendsto_affine_div (a := a) (c := c)).log ha.ne')
  have := ((h1.add h2).add h3).sub (tendsto_affine_div (a := a) (c := c))
  simp only [zero_mul, mul_zero, zero_add] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hy.eventually_gt_atTop 0] with z hz hy
  simp only [Function.comp_apply]
  rw [log_div hy.ne' hz.ne']
  field_simp
  ring

lemma tendsto_log_Gamma_self :
    Tendsto (fun z : ℝ => log (Gamma z) / z - log z) atTop (𝓝 (-1)) := by
  simpa using tendsto_log_Gamma_affine (a := 1) (c := 0) one_pos

/-- The exponent appearing in the second moment of the full Barenblatt profile. -/
noncomputable def phiFull (α z : ℝ) : ℝ :=
  ((2 * α - 1) * z * log π + log (Gamma z) + 2 * α * z * log (4 * α * z - 2) -
    log (Gamma (2 * α * z))) / z

lemma tendsto_phiFull {α : ℝ} (hα : 1 / 2 < α) :
    Tendsto (fun z => phiFull α z - log z) atTop
      (𝓝 ((2 * α - 1) * log π + (2 * α - 1) + 2 * α * log 2)) := by
  have h4 : 0 < 4 * α := by linarith
  have h2 : 0 < 2 * α := by linarith
  have := ((tendsto_log_Gamma_self.const_add ((2 * α - 1) * log π)).add
    ((tendsto_log_affine_sub_log (c := -2) h4).const_mul (2 * α))).sub
    (tendsto_log_Gamma_affine (c := 0) h2)
  rw [show (2 * α - 1) * log π + (2 * α - 1) + 2 * α * log 2 =
      (2 * α - 1) * log π + -1 + 2 * α * log (4 * α) - (2 * α * log (2 * α) - 2 * α) by
    rw [show 4 * α = 2 * (2 * α) by ring, log_mul two_ne_zero h2.ne']
    ring]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with z hz
  unfold phiFull
  simp only [add_zero]
  rw [show 4 * α * z + -2 = 4 * α * z - 2 by ring]
  field_simp
  ring


lemma two_pi_e_rpow (y : ℝ) : (2 * π * exp 1) ^ y = exp (y * log 2 + y * log π + y) := by
  rw [rpow_def_of_pos (by positivity), log_mul (by positivity) (exp_pos 1).ne',
    log_mul two_ne_zero pi_ne_zero, log_exp]
  ring_nf

/-- The normalized second moment `M₂/d` of the full Barenblatt profile, as a function of
`z = p - d/2`. -/
noncomputable def gFull (α z : ℝ) : ℝ := exp (phiFull α z) / (2 * (z - 1))

lemma tendsto_gFull {α : ℝ} (hα : 1 / 2 < α) :
    Tendsto (gFull α) atTop (𝓝 ((2 * π * exp 1) ^ (2 * α - 1))) := by
  have := ((tendsto_phiFull hα).rexp).mul ((tendsto_affine_div (a := 2) (c := -2)).inv₀
    two_ne_zero)
  rw [two_pi_e_rpow]
  rw [show exp ((2 * α - 1) * log 2 + (2 * α - 1) * log π + (2 * α - 1)) =
      exp ((2 * α - 1) * log π + (2 * α - 1) + 2 * α * log 2) * 2⁻¹ by
    rw [← exp_log (show (0 : ℝ) < 2⁻¹ by norm_num), ← exp_add, log_inv]
    ring_nf]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with z hz
  have hz0 : 0 < z := by linarith
  unfold gFull
  rw [exp_sub, exp_log hz0, inv_div, show 2 * z + -2 = 2 * (z - 1) by ring]
  have : z - 1 ≠ 0 := by linarith
  field_simp

/-- Exact rewriting of the second moment of the full Barenblatt profile in terms of
`z = p - d/2`. -/
lemma fullMoment_eq_gFull {α p b t z : ℝ} (hα : 1 / 2 < α) (hz1 : 1 < z)
    (hzt : p - t / 2 = z) (hp : p = 2 * α * z) (ht : t = 2 * (2 * α - 1) * z)
    (hb : b = 1 / (4 * α * z - 2)) :
    (π ^ (t / 2) * Gamma (p - t / 2) / (b ^ p * Gamma p)) ^ (2 / (2 * p - t)) *
        (Gamma ((t + 2) / 2) * Gamma (p - (t + 2) / 2) / (Gamma (t / 2) * Gamma (p - t / 2))) / t =
      gFull α z := by
  have hz0 : 0 < z := by linarith
  have h4 : 0 < 4 * α * z - 2 := by nlinarith
  have hb0 : 0 < b := by rw [hb]; positivity
  have h2α : 0 < 2 * α - 1 := by linarith
  have ht0 : 0 < t := by rw [ht]; positivity
  have hp0 : 0 < p := by linarith
  rw [hzt, show p - (t + 2) / 2 = z - 1 by linarith, show (t + 2) / 2 = t / 2 + 1 by ring,
    show 2 * p - t = 2 * z by linarith, Gamma_add_one (by positivity : t / 2 ≠ 0)]
  have hGz : Gamma z = (z - 1) * Gamma (z - 1) := by
    rw [← Gamma_add_one (by linarith : z - 1 ≠ 0), sub_add_cancel]
  have hX : 0 < π ^ (t / 2) * Gamma z / (b ^ p * Gamma p) := by
    have := Gamma_pos_of_pos hz0; have := Gamma_pos_of_pos hp0; positivity
  rw [rpow_def_of_pos hX, log_div (by positivity) (by positivity),
    log_mul (by positivity) (Gamma_pos_of_pos hz0).ne',
    log_mul (by positivity) (Gamma_pos_of_pos hp0).ne', log_rpow pi_pos, log_rpow hb0, hb,
    one_div, log_inv]
  unfold gFull phiFull
  have hG1 : 0 < Gamma (z - 1) := Gamma_pos_of_pos (by linarith)
  have hGt : 0 < Gamma (t / 2) := Gamma_pos_of_pos (by positivity)
  have hGz' : Gamma (z - 1) = Gamma z / (z - 1) := by
    rw [hGz, mul_div_cancel_left₀ _ (by linarith : z - 1 ≠ 0)]
  rw [hGz', mul_div_assoc, div_eq_mul_one_div (exp _)]
  subst hp ht
  rw [show 2 * (2 * α - 1) * z / 2 = (2 * α - 1) * z by ring] at hGt ⊢
  congr 1
  · congr 1
    field_simp
    ring
  · have := Gamma_pos_of_pos hz0
    have : z - 1 ≠ 0 := by linarith
    have : 2 * α - 1 ≠ 0 := by linarith
    field_simp

/-- The exponent appearing in the second moment of the compact Barenblatt profile. -/
noncomputable def phiComp (α z : ℝ) : ℝ :=
  (log (Gamma (z + 1)) - (1 - 2 * α) * z * log π + 2 * α * z * log (4 * α * z + 2) -
    log (Gamma (2 * α * z + 1))) / z

lemma tendsto_phiComp {α : ℝ} (hα0 : 0 < α) :
    Tendsto (fun z => phiComp α z - log z) atTop
      (𝓝 (-((1 - 2 * α) * log 2 + (1 - 2 * α) * log π + (1 - 2 * α)) + log 2)) := by
  have h4 : 0 < 4 * α := by linarith
  have h2 : 0 < 2 * α := by linarith
  have := (((tendsto_log_Gamma_affine (a := 1) (c := 1) one_pos).sub_const
    ((1 - 2 * α) * log π)).add
    ((tendsto_log_affine_sub_log (c := 2) h4).const_mul (2 * α))).sub
    (tendsto_log_Gamma_affine (c := 1) h2)
  rw [show -((1 - 2 * α) * log 2 + (1 - 2 * α) * log π + (1 - 2 * α)) + log 2 =
      1 * log 1 - 1 - (1 - 2 * α) * log π + 2 * α * log (4 * α) -
        (2 * α * log (2 * α) - 2 * α) by
    rw [show 4 * α = 2 * (2 * α) by ring, log_mul two_ne_zero h2.ne', log_one]
    ring]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with z hz
  unfold phiComp
  simp only [one_mul]
  field_simp
  ring

/-- The normalized second moment `M₂/d` of the compact Barenblatt profile, as a function of
`z = p + d/2`. -/
noncomputable def gComp (α z : ℝ) : ℝ := exp (phiComp α z) / (2 * (z + 1))

lemma tendsto_gComp {α : ℝ} (hα0 : 0 < α) :
    Tendsto (gComp α) atTop (𝓝 (1 / (2 * π * exp 1) ^ (1 - 2 * α))) := by
  have := ((tendsto_phiComp hα0).rexp).mul ((tendsto_affine_div (a := 2) (c := 2)).inv₀
    two_ne_zero)
  rw [two_pi_e_rpow, one_div, ← exp_neg]
  rw [show exp (-((1 - 2 * α) * log 2 + (1 - 2 * α) * log π + (1 - 2 * α))) =
      exp (-((1 - 2 * α) * log 2 + (1 - 2 * α) * log π + (1 - 2 * α)) + log 2) * 2⁻¹ by
    rw [exp_add, exp_log two_pos]; ring]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with z hz
  unfold gComp
  rw [exp_sub, exp_log hz, inv_div, show 2 * z + 2 = 2 * (z + 1) by ring]
  have : z + 1 ≠ 0 := by linarith
  field_simp

/-- Exact rewriting of the second moment of the compact Barenblatt profile in terms of
`z = p + d/2`. -/
lemma compMoment_eq_gComp {α p b t z : ℝ} (hα0 : 0 < α) (hα : α < 1 / 2) (hz : 0 < z)
    (hzt : p + t / 2 = z) (hp : p = 2 * α * z) (ht : t = 2 * (1 - 2 * α) * z)
    (hb : b = 1 / (4 * α * z + 2)) :
    (Gamma (p + 1 + t / 2) / (π ^ (t / 2) * b ^ p * Gamma (p + 1))) ^ (2 / (t + 2 * p)) *
        (Gamma (p + 1 + t / 2) * Gamma ((t + 2) / 2) /
          (Gamma (t / 2) * Gamma (p + 1 + (t + 2) / 2))) / t =
      gComp α z := by
  have h4 : 0 < 4 * α * z + 2 := by positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  have h12 : 0 < 1 - 2 * α := by linarith
  have ht0 : 0 < t := by rw [ht]; positivity
  have hp0 : 0 < p := by rw [hp]; positivity
  rw [show p + 1 + (t + 2) / 2 = z + 1 + 1 by linarith, show p + 1 + t / 2 = z + 1 by linarith,
    show (t + 2) / 2 = t / 2 + 1 by ring, show t + 2 * p = 2 * z by linarith,
    Gamma_add_one (by positivity : t / 2 ≠ 0), Gamma_add_one (by positivity : z + 1 ≠ 0)]
  have hGz := Gamma_pos_of_pos (by positivity : 0 < z + 1)
  have hGp := Gamma_pos_of_pos (by positivity : 0 < p + 1)
  have hGt := Gamma_pos_of_pos (by positivity : 0 < t / 2)
  have hX : 0 < Gamma (z + 1) / (π ^ (t / 2) * b ^ p * Gamma (p + 1)) := by positivity
  rw [rpow_def_of_pos hX, log_div hGz.ne' (by positivity),
    log_mul (by positivity) hGp.ne', log_mul (by positivity) (by positivity), log_rpow pi_pos,
    log_rpow hb0, hb, one_div, log_inv]
  unfold gComp phiComp
  rw [mul_div_assoc, div_eq_mul_one_div (exp _)]
  subst hp ht
  rw [show 2 * (1 - 2 * α) * z / 2 = (1 - 2 * α) * z by ring] at hGt ⊢
  congr 1
  · congr 1
    field_simp
    ring
  · have : z + 1 ≠ 0 := by linarith
    have : 1 - 2 * α ≠ 0 := by linarith
    field_simp

/-- The logarithmic quantity governing the compact Barenblatt profile with a fixed exponent,
as a function of `z = d/2`. -/
noncomputable def psiFixed (p κ ν z : ℝ) : ℝ :=
  (κ * z + ν + log (Gamma (z + (p + 1))) - z * log π - log (Gamma (p + 1))) / (z + p) - log z

lemma tendsto_psiFixed {p : ℝ} (hp : 0 < p) (κ ν : ℝ) :
    Tendsto (psiFixed p κ ν) atTop (𝓝 (κ - 1 - log π)) := by
  have hr : Tendsto (fun z : ℝ => ((1 * z + p) / z)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_affine_div (a := 1) (c := p)).inv₀ one_ne_zero
  have hi : Tendsto (fun z : ℝ => (z + p)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  have := ((hr.mul ((tendsto_log_Gamma_affine (a := 1) (c := p + 1) one_pos).const_add
    (κ - log π))).add (hi.const_mul (ν - log (Gamma (p + 1))))).sub
    ((tendsto_log_div_self'.const_mul p).mul hr)
  simp only [one_mul, mul_zero, add_zero, zero_mul, sub_zero, log_one, zero_sub] at this
  rw [show κ - 1 - log π = κ - log π + -1 by ring]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with z hz
  unfold psiFixed
  have : z + p ≠ 0 := by linarith
  field_simp
  ring

lemma exp_psiFixed_const {b : ℝ} (hb : 0 < b) :
    exp (log b - 1 - log π) * (π * exp 1 / b) = 1 := by
  rw [exp_sub, exp_sub, exp_log hb, exp_log pi_pos]
  field_simp

lemma exp_psiFixed_moment : exp ((0 : ℝ) - 1 - log π) * 1 * (π * exp 1) = 1 := by
  rw [exp_sub, exp_sub, exp_zero, exp_log pi_pos]
  field_simp

/-- Exact rewriting of the normalizing constant of the compact Barenblatt profile. -/
lemma compConst_ratio_eq {p b t z : ℝ} (hp : 0 < p) (hb : 0 < b) (hz : 0 < z) (ht : t = 2 * z) :
    (b ^ (t / 2) * Gamma (p + 1 + t / 2) / (π ^ (t / 2) * Gamma (p + 1))) ^ (2 / (2 * p + t)) /
        (b * t / (2 * π * exp 1)) =
      exp (psiFixed p (log b) 0 z) * (π * exp 1 / b) := by
  subst ht
  rw [show 2 * z / 2 = z by ring, show p + 1 + z = z + (p + 1) by ring,
    show 2 / (2 * p + 2 * z) = 1 / (z + p) by field_simp; ring]
  have hG := Gamma_pos_of_pos (by positivity : 0 < z + (p + 1))
  have hGp := Gamma_pos_of_pos (by positivity : 0 < p + 1)
  rw [rpow_def_of_pos (by positivity), log_div (by positivity) (by positivity),
    log_mul (by positivity) hG.ne', log_mul (by positivity) hGp.ne', log_rpow hb,
    log_rpow pi_pos]
  unfold psiFixed
  rw [exp_sub, exp_log hz]
  have : z + p ≠ 0 := by linarith
  field_simp
  ring_nf

/-- Exact rewriting of the second moment of the compact Barenblatt profile (fixed exponent). -/
lemma compMoment_ratio_eq {p b t z : ℝ} (hp : 0 < p) (hb : 0 < b) (hz : 0 < z) (ht : t = 2 * z) :
    (Gamma (p + 1 + t / 2) / (π ^ (t / 2) * b ^ p * Gamma (p + 1))) ^ (2 / (t + 2 * p)) *
        (Gamma (p + 1 + t / 2) * Gamma ((t + 2) / 2) /
          (Gamma (t / 2) * Gamma (p + 1 + (t + 2) / 2))) / (t / (2 * π * exp 1)) =
      exp (psiFixed p 0 (-(p * log b)) z) * (z / (z + (p + 1))) * (π * exp 1) := by
  subst ht
  rw [show p + 1 + (2 * z + 2) / 2 = z + (p + 1) + 1 by ring, show 2 * z / 2 = z by ring,
    show p + 1 + z = z + (p + 1) by ring, show (2 * z + 2) / 2 = z + 1 by ring,
    show 2 / (2 * z + 2 * p) = 1 / (z + p) by field_simp,
    Gamma_add_one hz.ne', Gamma_add_one (by positivity : z + (p + 1) ≠ 0)]
  have hG := Gamma_pos_of_pos (by positivity : 0 < z + (p + 1))
  have hGp := Gamma_pos_of_pos (by positivity : 0 < p + 1)
  have hGz := Gamma_pos_of_pos hz
  rw [rpow_def_of_pos (by positivity), log_div hG.ne' (by positivity),
    log_mul (by positivity) hGp.ne', log_mul (by positivity) (by positivity), log_rpow hb,
    log_rpow pi_pos]
  unfold psiFixed
  rw [exp_sub, exp_log hz]
  have : z + p ≠ 0 := by linarith
  have : z + (p + 1) ≠ 0 := by linarith
  field_simp
  ring_nf

end Cutfast.Asymptotics

namespace Cutfast

open Cutfast.Asymptotics

/-- **Lemma 3.1, eqs. (M2sim) and (difference-fde).** Fix `α > 1/2` and set
`m = ((d-2)α+1)/(dα)`, `p = 1/(1-m) = dα/(2α-1)`, `b = (2α-1)/(2(α(d-2)+1))`. Then as `d → ∞`,
`∫ |x|² B = (2πe)^{2α-1} d + o(d)`, `∫ Bᵐ = (2πe)^{2α-1} + o(1)`, and
`∫ |x|² B - d ∫ Bᵐ = O(1)`. -/
theorem fullBarenblatt_asymptotics' {α : ℝ} (hα : 1 / 2 < α) :
    Tendsto (fun d : ℕ => (∫ x, ‖x‖ ^ 2 * fullBarenblatt d (d * α / (2 * α - 1))
        ((2 * α - 1) / (2 * (α * (d - 2) + 1))) x) / d) atTop
      (𝓝 ((2 * π * exp 1) ^ (2 * α - 1))) ∧
    Tendsto (fun d : ℕ => ∫ x, fullBarenblatt d (d * α / (2 * α - 1))
        ((2 * α - 1) / (2 * (α * (d - 2) + 1))) x ^ exponentOfAlpha α d) atTop
      (𝓝 ((2 * π * exp 1) ^ (2 * α - 1))) ∧
    (fun d : ℕ => (∫ x, ‖x‖ ^ 2 * fullBarenblatt d (d * α / (2 * α - 1))
        ((2 * α - 1) / (2 * (α * (d - 2) + 1))) x) -
      d * ∫ x, fullBarenblatt d (d * α / (2 * α - 1))
        ((2 * α - 1) / (2 * (α * (d - 2) + 1))) x ^ exponentOfAlpha α d) =O[atTop]
      (fun _ => (1 : ℝ)) := by
  have h2α : 0 < 2 * α - 1 := by linarith
  have h2α' : 2 * α - 1 ≠ 0 := h2α.ne'
  have h2α'' : α * 2 - 1 ≠ 0 := by linarith
  -- eventually, the moment `∫ |x|² B / d` is `gFull α (d / (2(2α-1)))`
  have hd_large : ∀ᶠ d : ℕ in atTop, 1 ≤ d ∧ 2 * (2 * α - 1) + 2 < (d : ℝ) :=
    (eventually_ge_atTop 1).and (tendsto_natCast_atTop_atTop.eventually_gt_atTop _)
  have hmom : ∀ᶠ d : ℕ in atTop, (∫ x, ‖x‖ ^ 2 * fullBarenblatt d (d * α / (2 * α - 1))
        ((2 * α - 1) / (2 * (α * (d - 2) + 1))) x) / d = gFull α (d / (2 * (2 * α - 1))) := by
    filter_upwards [hd_large] with d ⟨hd1, hd⟩
    have hz1 : 1 < (d : ℝ) / (2 * (2 * α - 1)) := by rw [lt_div_iff₀ (by positivity)]; linarith
    have hd0 : (0 : ℝ) < d := by linarith
    have hb : 0 < (2 * α - 1) / (2 * (α * (d - 2) + 1)) := by
      apply div_pos h2α; nlinarith
    have h := fullBarenblatt_moment' (d := d) hd1 (p := d * α / (2 * α - 1))
      (b := (2 * α - 1) / (2 * (α * (d - 2) + 1))) (a := 2)
      (by rw [lt_div_iff₀ h2α]; nlinarith) hb (by linarith)
      (by rw [show 2 * ((d : ℝ) * α / (2 * α - 1)) - d = d / (2 * α - 1) by field_simp; ring,
        lt_div_iff₀ h2α]; linarith)
    simp only [rpow_two] at h
    rw [h]
    have hden : α * (d - 2) + 1 ≠ 0 := by nlinarith
    have e4 : 4 * α * (d / (2 * (2 * α - 1))) - 2 = 2 * (α * (d - 2) + 1) / (2 * α - 1) := by
      field_simp; ring
    exact fullMoment_eq_gFull hα hz1 (by field_simp; ring) (by field_simp)
      (by field_simp) (by rw [e4]; field_simp)
  -- the exact virial identity `∫ |x|² B = d ∫ Bᵐ`
  have hvir : ∀ᶠ d : ℕ in atTop, (∫ x, ‖x‖ ^ 2 * fullBarenblatt d (d * α / (2 * α - 1))
        ((2 * α - 1) / (2 * (α * (d - 2) + 1))) x) =
      d * ∫ x, fullBarenblatt d (d * α / (2 * α - 1))
        ((2 * α - 1) / (2 * (α * (d - 2) + 1))) x ^ exponentOfAlpha α d := by
    filter_upwards [hd_large] with d ⟨hd1, hd⟩
    have hd0 : (0 : ℝ) < d := by linarith
    have hm1 : 1 - exponentOfAlpha α d = (2 * α - 1) / (d * α) := by
      unfold exponentOfAlpha; field_simp; ring
    have h := fullBarenblatt_secondMoment_eq (d := d) hd1 (m := exponentOfAlpha α d)
      (by have : 0 < (2 * α - 1) / (d * α) := by positivity
          linarith)
      (by rw [div_lt_iff₀ (by positivity)]
          unfold exponentOfAlpha
          rw [mul_comm, ← mul_div_assoc, lt_div_iff₀ (by positivity)]
          nlinarith)
    have e1 : 1 / (1 - exponentOfAlpha α d) = d * α / (2 * α - 1) := by
      rw [hm1]; field_simp
    have e2 : (1 - exponentOfAlpha α d) / (2 * exponentOfAlpha α d) =
        (2 * α - 1) / (2 * (α * (d - 2) + 1)) := by
      have : α * (d - 2) + 1 ≠ 0 := by nlinarith
      rw [hm1]; unfold exponentOfAlpha; field_simp
    rwa [e1, e2] at h
  have hlim := (tendsto_gFull hα).comp
    (tendsto_natCast_atTop_atTop.atTop_div_const (by positivity : (0 : ℝ) < 2 * (2 * α - 1)))
  refine ⟨hlim.congr' (hmom.mono fun d hd => hd.symm), ?_, ?_⟩
  · refine hlim.congr' ?_
    filter_upwards [hmom, hvir, hd_large] with d h1 h2 ⟨_, hd⟩
    simp only [Function.comp_apply]
    rw [← h1, h2, mul_div_cancel_left₀ _ (by positivity)]
  · refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [hvir] with d h
    rw [h, sub_self]

/-- **Lemma 4.1, eqs. (limit-alpha-constant-pme) and (difference-pme).** Fix `α ∈ (0,1/2)` and
set `m = 1 + (1-2α)/(dα)` (that is, `m = exponentOfAlpha α d`), `p = 1/(m-1)`, `b = (m-1)/(2m)`.
Then as `d → ∞`, `∫ |x|² B = d/(2πe)^{1-2α} + o(d)`, `∫ Bᵐ = 1/(2πe)^{1-2α} + o(1)`, and
`∫ |x|² B - d ∫ Bᵐ = O(1)`. -/
theorem compactBarenblatt_asymptotics' {α : ℝ} (hα0 : 0 < α) (hα : α < 1 / 2) :
    Tendsto (fun d : ℕ => (∫ x, ‖x‖ ^ 2 * compactBarenblatt d (1 / (exponentOfAlpha α d - 1))
        ((exponentOfAlpha α d - 1) / (2 * exponentOfAlpha α d)) x) / d) atTop
      (𝓝 (1 / (2 * π * exp 1) ^ (1 - 2 * α))) ∧
    Tendsto (fun d : ℕ => ∫ x, compactBarenblatt d (1 / (exponentOfAlpha α d - 1))
        ((exponentOfAlpha α d - 1) / (2 * exponentOfAlpha α d)) x ^ exponentOfAlpha α d) atTop
      (𝓝 (1 / (2 * π * exp 1) ^ (1 - 2 * α))) ∧
    (fun d : ℕ => (∫ x, ‖x‖ ^ 2 * compactBarenblatt d (1 / (exponentOfAlpha α d - 1))
        ((exponentOfAlpha α d - 1) / (2 * exponentOfAlpha α d)) x) -
      d * ∫ x, compactBarenblatt d (1 / (exponentOfAlpha α d - 1))
        ((exponentOfAlpha α d - 1) / (2 * exponentOfAlpha α d)) x ^ exponentOfAlpha α d)
      =O[atTop] (fun _ => (1 : ℝ)) := by
  have h12 : 0 < 1 - 2 * α := by linarith
  have h12' : 1 - 2 * α ≠ 0 := h12.ne'
  have h12'' : 1 - α * 2 ≠ 0 := by linarith
  have hd_large : ∀ᶠ d : ℕ in atTop, 1 ≤ d := eventually_ge_atTop 1
  have hm1 : ∀ d : ℕ, 1 ≤ d → exponentOfAlpha α d - 1 = (1 - 2 * α) / (d * α) := by
    intro d hd
    have : (d : ℝ) ≠ 0 := by positivity
    unfold exponentOfAlpha; field_simp; ring
  have hmom : ∀ᶠ d : ℕ in atTop, (∫ x, ‖x‖ ^ 2 * compactBarenblatt d (1 / (exponentOfAlpha α d - 1))
        ((exponentOfAlpha α d - 1) / (2 * exponentOfAlpha α d)) x) / d =
      gComp α (d / (2 * (1 - 2 * α))) := by
    filter_upwards [hd_large] with d hd1
    have hd0 : (0 : ℝ) < d := by positivity
    have hm := hm1 d hd1
    have hmpos : 0 < exponentOfAlpha α d - 1 := by rw [hm]; positivity
    have h := compactBarenblatt_moment' (d := d) hd1 (p := 1 / (exponentOfAlpha α d - 1))
      (b := (exponentOfAlpha α d - 1) / (2 * exponentOfAlpha α d)) (a := 2) (by positivity)
      (div_pos hmpos (by linarith)) (by linarith)
    simp only [rpow_two] at h
    rw [h]
    have e4 : 4 * α * (d / (2 * (1 - 2 * α))) + 2 = 2 * (α * d + 1 - 2 * α) / (1 - 2 * α) := by
      field_simp; ring
    have hden : α * d + 1 - 2 * α ≠ 0 := by nlinarith
    have hm' : exponentOfAlpha α d = (α * d + 1 - 2 * α) / (d * α) := by
      unfold exponentOfAlpha; field_simp; ring
    exact compMoment_eq_gComp hα0 hα (by positivity) (by rw [hm]; field_simp; ring)
      (by rw [hm]; field_simp) (by field_simp)
      (by rw [e4, hm1 d hd1, hm']; field_simp)
  have hvir : ∀ᶠ d : ℕ in atTop, (∫ x, ‖x‖ ^ 2 * compactBarenblatt d
        (1 / (exponentOfAlpha α d - 1)) ((exponentOfAlpha α d - 1) / (2 * exponentOfAlpha α d)) x) =
      d * ∫ x, compactBarenblatt d (1 / (exponentOfAlpha α d - 1))
        ((exponentOfAlpha α d - 1) / (2 * exponentOfAlpha α d)) x ^ exponentOfAlpha α d := by
    filter_upwards [hd_large] with d hd1
    have hm := hm1 d hd1
    exact compactBarenblatt_secondMoment_eq hd1
      (by have : 0 < exponentOfAlpha α d - 1 := by rw [hm]; positivity
          linarith)
  have hlim := (tendsto_gComp hα0).comp
    (tendsto_natCast_atTop_atTop.atTop_div_const (by positivity : (0 : ℝ) < 2 * (1 - 2 * α)))
  refine ⟨hlim.congr' (hmom.mono fun d hd => hd.symm), ?_, ?_⟩
  · refine hlim.congr' ?_
    filter_upwards [hmom, hvir, hd_large] with d h1 h2 hd
    simp only [Function.comp_apply]
    rw [← h1, h2, mul_div_cancel_left₀ _ (by positivity)]
  · refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [hvir] with d h
    rw [h, sub_self]

/-- **Lemma 4.2.** Fix `m > 1` and set `p = 1/(m-1)`, `b = (m-1)/(2m)`. Then as `d → ∞`,
`c ~ bd/(2πe)`, `∫ |x|² B ~ d/(2πe)` and `∫ Bᵐ ~ 1/(2πe)`. -/
theorem compactBarenblatt_fixedExponent_asymptotics' {m : ℝ} (hm : 1 < m) :
    Asymptotics.IsEquivalent atTop (fun d : ℕ => compactBarenblattConst d (1 / (m - 1))
        ((m - 1) / (2 * m))) (fun d => (m - 1) / (2 * m) * d / (2 * π * exp 1)) ∧
    Asymptotics.IsEquivalent atTop (fun d : ℕ => ∫ x, ‖x‖ ^ 2 * compactBarenblatt d (1 / (m - 1))
        ((m - 1) / (2 * m)) x) (fun d => d / (2 * π * exp 1)) ∧
    Asymptotics.IsEquivalent atTop (fun d : ℕ => ∫ x, compactBarenblatt d (1 / (m - 1))
        ((m - 1) / (2 * m)) x ^ m) (fun _ => 1 / (2 * π * exp 1)) := by
  set p := 1 / (m - 1) with hp_def
  set b := (m - 1) / (2 * m) with hb_def
  have hp : 0 < p := by rw [hp_def]; apply div_pos one_pos; linarith
  have hb : 0 < b := by rw [hb_def]; apply div_pos <;> linarith
  have hz : Tendsto (fun d : ℕ => (d : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const two_pos
  have hd_large : ∀ᶠ d : ℕ in atTop, 1 ≤ d := eventually_ge_atTop 1
  -- the second moment
  have hmom : ∀ᶠ d : ℕ in atTop, (∫ x, ‖x‖ ^ 2 * compactBarenblatt d p b x) /
      (d / (2 * π * exp 1)) =
      exp (psiFixed p 0 (-(p * log b)) (d / 2)) * ((d / 2) / ((d / 2) + (p + 1))) *
        (π * exp 1) := by
    filter_upwards [hd_large] with d hd1
    have h := compactBarenblatt_moment' (d := d) hd1 (p := p) (b := b) (a := 2) hp hb
      (by have : (0 : ℝ) ≤ d := by positivity
          linarith)
    simp only [rpow_two] at h
    rw [h]
    exact compMoment_ratio_eq hp hb (by positivity) (by ring)
  have hlim2 : Tendsto (fun d : ℕ => exp (psiFixed p 0 (-(p * log b)) (d / 2)) *
      ((d / 2) / ((d / 2) + (p + 1))) * (π * exp 1)) atTop (𝓝 1) := by
    have hr : Tendsto (fun z : ℝ => ((1 * z + (p + 1)) / z)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_affine_div (a := 1) (c := p + 1)).inv₀ one_ne_zero
    have := ((((tendsto_psiFixed hp 0 (-(p * log b))).rexp).mul hr).mul_const
      (π * exp 1)).comp hz
    rw [exp_psiFixed_moment] at this
    refine this.congr' ?_
    filter_upwards [hd_large] with d hd
    simp only [Function.comp_apply, one_mul, inv_div]
  have hvir : ∀ᶠ d : ℕ in atTop, (∫ x, ‖x‖ ^ 2 * compactBarenblatt d p b x) =
      d * ∫ x, compactBarenblatt d p b x ^ m := by
    filter_upwards [hd_large] with d hd1
    exact compactBarenblatt_secondMoment_eq hd1 hm
  refine ⟨?_, ?_, ?_⟩
  · apply Asymptotics.isEquivalent_of_tendsto_one
    have := (((tendsto_psiFixed hp (log b) 0).rexp).mul_const (π * exp 1 / b)).comp hz
    rw [exp_psiFixed_const hb] at this
    refine this.congr' ?_
    filter_upwards [hd_large] with d hd1
    simp only [Function.comp_apply, Pi.div_apply]
    unfold compactBarenblattConst
    rw [compConst_ratio_eq (z := d / 2) hp hb (by positivity) (by ring)]
  · apply Asymptotics.isEquivalent_of_tendsto_one
    refine hlim2.congr' ?_
    filter_upwards [hmom] with d h
    simp only [Pi.div_apply]
    rw [h]
  · apply Asymptotics.isEquivalent_of_tendsto_one
    refine hlim2.congr' ?_
    filter_upwards [hmom, hvir, hd_large] with d h hv hd1
    simp only [Pi.div_apply]
    rw [← h, hv]
    have : (d : ℝ) ≠ 0 := by positivity
    field_simp

/-- **Lemma 3.1, eqs. (M2sim) and (difference-fde).** Fix `α > 1/2` and set
`m = ((d-2)α+1)/(dα)`, `p = 1/(1-m) = dα/(2α-1)`, `b = (2α-1)/(2(α(d-2)+1))`. Then as `d → ∞`,
`∫ |x|² B = (2πe)^{2α-1} d + o(d)`, `∫ Bᵐ = (2πe)^{2α-1} + o(1)`, and
`∫ |x|² B - d ∫ Bᵐ = O(1)`. -/
alias fullBarenblatt_asymptotics := fullBarenblatt_asymptotics'

/-- **Lemma 4.1, eqs. (limit-alpha-constant-pme) and (difference-pme).** Fix `α ∈ (0,1/2)` and
set `m = 1 + (1-2α)/(dα)` (that is, `m = exponentOfAlpha α d`), `p = 1/(m-1)`, `b = (m-1)/(2m)`.
Then as `d → ∞`, `∫ |x|² B = d/(2πe)^{1-2α} + o(d)`, `∫ Bᵐ = 1/(2πe)^{1-2α} + o(1)`, and
`∫ |x|² B - d ∫ Bᵐ = O(1)`. -/
alias compactBarenblatt_asymptotics := compactBarenblatt_asymptotics'

/-- **Lemma 4.2.** Fix `m > 1` and set `p = 1/(m-1)`, `b = (m-1)/(2m)`. Then as `d → ∞`,
`c ~ bd/(2πe)`, `∫ |x|² B ~ d/(2πe)` and `∫ Bᵐ ~ 1/(2πe)`. -/
alias compactBarenblatt_fixedExponent_asymptotics := compactBarenblatt_fixedExponent_asymptotics'

end Cutfast
