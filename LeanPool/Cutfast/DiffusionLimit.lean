/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Barenblatt
public import LeanPool.Cutfast.Asymptotics

/-!
# The diffusion limit `m → 1`

Section 1.4.2 of the paper: at fixed `d`, as `m → 1` (from both sides), the Barenblatt profile
tends to the Gaussian `(4π)^{-d/2} e^{-|x|²/4}`, `u` to the heat kernel and `v` to the Mehler
kernel.

The proof identifies `B` with the explicit full-space (`m < 1`) or compact (`m > 1`) profile of
shape `p = 1/|1-m| → ∞` and scale `κ` with `pκ → 1/4`, and uses the Gamma ratio asymptotics
`log Γ(y + a) - log Γ(y) - a log y → 0` (from the log-convexity of `Γ`) to show that the
normalizing constant `c` satisfies `c → 1` and `c^{∓p} → (4π)^{-d/2}`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace BoundedContinuousFunction MatrixOrder

namespace Cutfast

namespace DiffusionLimit

/-! ### Asymptotics of ratios of Gamma functions -/

/-- The defect `log Γ(y + a) - log Γ(y) - a log y`, which tends to `0` as `y → ∞`. -/
noncomputable def gammaDefect (a y : ℝ) : ℝ := log (Gamma (y + a)) - log (Gamma y) - a * log y

/-- Log-convexity bound: `log Γ(y + a) ≤ log Γ(y) + a log y` for `y > 0` and `a ∈ [0,1]`. -/
lemma log_Gamma_add_le {y a : ℝ} (hy : 0 < y) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    log (Gamma (y + a)) ≤ log (Gamma y) + a * log y := by
  have h := convexOn_log_Gamma.2 (show y ∈ Set.Ioi (0 : ℝ) from hy)
    (show y + 1 ∈ Set.Ioi (0 : ℝ) by simp only [Set.mem_Ioi]; linarith)
    (show 0 ≤ 1 - a by linarith) ha0 (by ring)
  simp only [smul_eq_mul, Function.comp_apply] at h
  rw [Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne',
    show (1 - a) * y + a * (y + 1) = y + a by ring] at h
  linarith

lemma gammaDefect_nonpos {y a : ℝ} (hy : 0 < y) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    gammaDefect a y ≤ 0 := by
  unfold gammaDefect
  linarith [log_Gamma_add_le hy ha0 ha1]

lemma gammaDefect_ge {y a : ℝ} (hy : 0 < y) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (1 - a) * (log y - log (y + a)) ≤ gammaDefect a y := by
  have h := log_Gamma_add_le (y := y + a) (a := 1 - a) (by linarith) (by linarith) (by linarith)
  rw [show y + a + (1 - a) = y + 1 by ring, Gamma_add_one hy.ne',
    log_mul hy.ne' (Gamma_pos_of_pos hy).ne'] at h
  unfold gammaDefect
  linarith

/-- `log (y + a) - log y → 0` as `y → ∞`. -/
lemma tendsto_log_add_sub_log (a : ℝ) :
    Tendsto (fun y : ℝ => log (y + a) - log y) atTop (𝓝 0) := by
  have h := Asymptotics.tendsto_log_affine_sub_log (a := 1) (c := a) one_pos
  simpa only [one_mul, log_one] using h

lemma tendsto_gammaDefect_of_le_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Tendsto (gammaDefect a) atTop (𝓝 0) := by
  have hlow : Tendsto (fun y => (1 - a) * (log y - log (y + a))) atTop (𝓝 0) := by
    have := ((tendsto_log_add_sub_log a).neg).const_mul (1 - a)
    simp only [neg_zero, mul_zero] at this
    exact this.congr fun y => by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    (by filter_upwards [eventually_gt_atTop 0] with y hy using gammaDefect_ge hy ha0 ha1)
    (by filter_upwards [eventually_gt_atTop 0] with y hy using gammaDefect_nonpos hy ha0 ha1)

lemma gammaDefect_add (a b y : ℝ) :
    gammaDefect (a + b) y =
      gammaDefect b (y + a) + gammaDefect a y + b * (log (y + a) - log y) := by
  unfold gammaDefect
  rw [show y + a + b = y + (a + b) by ring]
  ring

lemma tendsto_gammaDefect_add {a b : ℝ} (hA : Tendsto (gammaDefect a) atTop (𝓝 0))
    (hB : Tendsto (gammaDefect b) atTop (𝓝 0)) :
    Tendsto (gammaDefect (a + b)) atTop (𝓝 0) := by
  have h1 := hB.comp (tendsto_atTop_add_const_right atTop a tendsto_id)
  have := (h1.add hA).add ((tendsto_log_add_sub_log a).const_mul b)
  simp only [add_zero, mul_zero] at this
  exact this.congr fun y => (gammaDefect_add a b y).symm

/-- **Gamma ratio asymptotics**: `log Γ(y + n/2) - log Γ(y) - (n/2) log y → 0` as `y → ∞`. -/
lemma tendsto_gammaDefect_half (n : ℕ) : Tendsto (gammaDefect ((n : ℝ) / 2)) atTop (𝓝 0) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_div]
    exact tendsto_const_nhds.congr fun y => by simp [gammaDefect]
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℝ) / 2 = n / 2 + 1 / 2 by push_cast; ring]
    exact tendsto_gammaDefect_add ih (tendsto_gammaDefect_of_le_one (by norm_num) (by norm_num))

/-! ### A limit of the form `(c + e)^q → exp(L + Λ)` -/

lemma abs_log_one_add_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) : |log (1 + u) - u| ≤ 2 * u ^ 2 := by
  have h1 : 1 / 2 ≤ 1 + u := by linarith [neg_abs_le u]
  have hpos : 0 < 1 + u := by linarith
  have hup := log_le_sub_one_of_pos hpos
  have hlow := one_sub_inv_le_log_of_pos hpos
  have hq : u - (1 - (1 + u)⁻¹) = u ^ 2 / (1 + u) := by field_simp; ring
  have hq2 : u ^ 2 / (1 + u) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ hpos]; nlinarith [sq_nonneg u]
  rw [abs_le]; constructor <;> nlinarith

/-- If `c → 1`, `e → 0`, `q log c → L` and `q e → Λ`, then `(c + e)^q → exp(L + Λ)`. -/
lemma tendsto_add_rpow {l : Filter ℝ} {c e q : ℝ → ℝ} {L Λ : ℝ}
    (hc : Tendsto c l (𝓝 1)) (he : Tendsto e l (𝓝 0))
    (hqc : Tendsto (fun m => q m * log (c m)) l (𝓝 L))
    (hqe : Tendsto (fun m => q m * e m) l (𝓝 Λ)) :
    Tendsto (fun m => (c m + e m) ^ q m) l (𝓝 (exp (L + Λ))) := by
  set u := fun m => e m / c m with hu_def
  have hu : Tendsto u l (𝓝 0) := by
    have := he.div hc one_ne_zero
    rw [zero_div] at this
    exact this
  have hua : Tendsto (fun m => |u m|) l (𝓝 0) := by simpa using hu.abs
  have hqu : Tendsto (fun m => q m * u m) l (𝓝 Λ) := by
    have := hqe.div hc one_ne_zero
    simp only [div_one] at this
    exact this.congr fun m => by simp only [Pi.div_apply, hu_def]; ring
  have hdiff : Tendsto (fun m => q m * log (1 + u m) - q m * u m) l (𝓝 0) := by
    have hb : Tendsto (fun m => 2 * |q m * u m| * |u m|) l (𝓝 0) := by
      simpa using ((hqu.abs).const_mul 2).mul hua
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hua.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with m hm
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_mul]
    calc |q m| * |log (1 + u m) - u m| ≤ |q m| * (2 * u m ^ 2) :=
          mul_le_mul_of_nonneg_left (abs_log_one_add_sub_le hm) (abs_nonneg _)
      _ = 2 * (|q m| * |u m|) * |u m| := by rw [← sq_abs (u m)]; ring
  have hsum := hqc.add (hdiff.add hqu)
  rw [zero_add] at hsum
  refine ((continuous_exp.tendsto _).comp hsum).congr' ?_
  filter_upwards [hc.eventually (lt_mem_nhds one_pos),
    hua.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with m hcm hum
  have h1u : 0 < 1 + u m := by linarith [neg_abs_le (u m)]
  have hce : c m + e m = c m * (1 + u m) := by simp only [hu_def]; field_simp
  simp only [Function.comp_apply]
  rw [hce, rpow_def_of_pos (mul_pos hcm h1u), log_mul hcm.ne' h1u.ne']
  congr 1
  ring

/-! ### The normalizing constants as `p → ∞` -/

lemma log_four_pi : log (4 * π) = log 4 + log π := log_mul (by norm_num) pi_pos.ne'

/-- From `p log K → L` (with `p → ∞`) and the shape `c = K^{2/(2p+s)}`, the limits of `c` and of
`q log c` for `q = ± p`. -/
lemma tendsto_const_aux {l : Filter ℝ} {p K : ℝ → ℝ} {s A : ℝ}
    (hp : Tendsto p l atTop) (hK : ∀ᶠ m in l, 0 < K m)
    (hlogK : Tendsto (fun m => log (K m)) l (𝓝 A)) :
    Tendsto (fun m => K m ^ (2 / (2 * p m + s))) l (𝓝 1) ∧
      Tendsto (fun m => p m * log (K m ^ (2 / (2 * p m + s)))) l (𝓝 A) := by
  have h2p : Tendsto (fun m => 2 * p m + s) l atTop :=
    tendsto_atTop_add_const_right _ _ (hp.const_mul_atTop two_pos)
  have hlogc : ∀ᶠ m in l, log (K m ^ (2 / (2 * p m + s))) = 2 / (2 * p m + s) * log (K m) := by
    filter_upwards [hK] with m hm using log_rpow hm _
  have hlc : Tendsto (fun m => log (K m ^ (2 / (2 * p m + s)))) l (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop h2p).mul hlogK
    rw [zero_mul] at this
    exact this.congr' (by filter_upwards [hlogc] with m hm using hm.symm)
  refine ⟨?_, ?_⟩
  · have := (continuous_exp.tendsto _).comp hlc
    rw [exp_zero] at this
    refine this.congr' ?_
    filter_upwards [hK] with m hm
    simp only [Function.comp_apply]
    rw [exp_log (rpow_pos_of_pos hm _)]
  · have hr : Tendsto (fun m => 1 - s / (2 * p m + s)) l (𝓝 1) := by
      have := ((tendsto_const_nhds (x := s)).div_atTop h2p).const_sub 1
      rwa [sub_zero] at this
    have := hr.mul hlogK
    rw [one_mul] at this
    refine this.congr' ?_
    filter_upwards [hlogc, h2p.eventually_gt_atTop 0] with m hm hm2
    rw [hm]
    field_simp
    ring

/-- Full-space profile: `(c + κ r)^{-p} → (4π)^{-d/2} e^{-r₀/4}` when `p → ∞`, `pκ → 1/4`,
`r → r₀`, where `c = fullBarenblattConst d p κ`. -/
lemma tendsto_full_core {d : ℕ} {l : Filter ℝ} {p κ r : ℝ → ℝ} {r0 : ℝ}
    (hp : Tendsto p l atTop) (hκ : ∀ᶠ m in l, 0 < κ m) (hκ0 : Tendsto κ l (𝓝 0))
    (hpκ : Tendsto (fun m => p m * κ m) l (𝓝 (1 / 4))) (hr : Tendsto r l (𝓝 r0)) :
    Tendsto (fun m => (fullBarenblattConst d (p m) (κ m) + κ m * r m) ^ (-p m)) l
      (𝓝 (exp (-((d : ℝ) / 2 * log (4 * π)) + -(r0 / 4)))) := by
  set K := fun m => π ^ ((d : ℝ) / 2) * Gamma (p m - d / 2) / (κ m ^ ((d : ℝ) / 2) * Gamma (p m))
    with hK
  have hd2 : (0 : ℝ) ≤ d / 2 := by positivity
  have hpd : ∀ᶠ m in l, (d : ℝ) / 2 + 1 < p m := hp.eventually_gt_atTop _
  have hKpos : ∀ᶠ m in l, 0 < K m := by
    filter_upwards [hpd, hκ] with m hm hκm
    have := Gamma_pos_of_pos (show 0 < p m - d / 2 by linarith)
    have := Gamma_pos_of_pos (show 0 < p m by linarith)
    simp only [hK]
    positivity
  have hq : Tendsto (fun m => p m + -((d : ℝ) / 2)) l atTop := tendsto_atTop_add_const_right _ _ hp
  have hlogK : Tendsto (fun m => log (K m)) l (𝓝 ((d : ℝ) / 2 * log (4 * π))) := by
    have h1 := (tendsto_gammaDefect_half d).comp hq
    have h2 := (tendsto_log_add_sub_log (-((d : ℝ) / 2))).comp hp
    have h3 := hpκ.log (by norm_num)
    have := ((((tendsto_const_nhds (x := (d : ℝ) / 2 * log π)).sub h1).sub
      (h2.const_mul ((d : ℝ) / 2))).sub (h3.const_mul ((d : ℝ) / 2)))
    rw [show (d : ℝ) / 2 * log π - 0 - d / 2 * 0 - d / 2 * log (1 / 4) = d / 2 * log (4 * π) by
      rw [log_four_pi, one_div, log_inv]; ring] at this
    refine this.congr' ?_
    filter_upwards [hpd, hκ] with m hm hκm
    have hg1 := Gamma_pos_of_pos (show 0 < p m - d / 2 by linarith)
    have hg2 := Gamma_pos_of_pos (show 0 < p m by linarith)
    simp only [Function.comp_apply, gammaDefect, hK]
    rw [show p m + -((d : ℝ) / 2) + d / 2 = p m by ring, ← sub_eq_add_neg,
      log_div (by positivity) (by positivity), log_mul (by positivity) hg1.ne',
      log_mul (by positivity) hg2.ne', log_rpow pi_pos, log_rpow hκm,
      log_mul (by linarith) hκm.ne']
    ring
  obtain ⟨hc, hqc⟩ := tendsto_const_aux (s := -(d : ℝ)) hp hKpos hlogK
  have hc' : Tendsto (fun m => fullBarenblattConst d (p m) (κ m)) l (𝓝 1) := by
    refine hc.congr fun m => ?_
    simp only [fullBarenblattConst, hK, sub_eq_add_neg]
  have hqc' : Tendsto (fun m => -p m * log (fullBarenblattConst d (p m) (κ m))) l
      (𝓝 (-((d : ℝ) / 2 * log (4 * π)))) := by
    refine hqc.neg.congr fun m => ?_
    simp only [fullBarenblattConst, hK, sub_eq_add_neg, neg_mul]
  have he : Tendsto (fun m => κ m * r m) l (𝓝 0) := by simpa using hκ0.mul hr
  have hqe : Tendsto (fun m => -p m * (κ m * r m)) l (𝓝 (-(r0 / 4))) := by
    have := (hpκ.mul hr).neg
    rw [show -(1 / 4 * r0) = -(r0 / 4) by ring] at this
    exact this.congr fun m => by ring
  exact tendsto_add_rpow hc' he hqc' hqe

/-- Compact profile: `(c - κ r)^{p} → (4π)^{-d/2} e^{-r₀/4}` when `p → ∞`, `pκ → 1/4`,
`r → r₀`, where `c = compactBarenblattConst d p κ`. -/
lemma tendsto_compact_core {d : ℕ} {l : Filter ℝ} {p κ r : ℝ → ℝ} {r0 : ℝ}
    (hp : Tendsto p l atTop) (hκ : ∀ᶠ m in l, 0 < κ m) (hκ0 : Tendsto κ l (𝓝 0))
    (hpκ : Tendsto (fun m => p m * κ m) l (𝓝 (1 / 4))) (hr : Tendsto r l (𝓝 r0)) :
    Tendsto (fun m => (max (compactBarenblattConst d (p m) (κ m) - κ m * r m) 0) ^ (p m)) l
      (𝓝 (exp (-((d : ℝ) / 2 * log (4 * π)) + -(r0 / 4)))) := by
  set K := fun m => κ m ^ ((d : ℝ) / 2) * Gamma (p m + 1 + d / 2) /
    (π ^ ((d : ℝ) / 2) * Gamma (p m + 1)) with hK
  have hd2 : (0 : ℝ) ≤ d / 2 := by positivity
  have hpd : ∀ᶠ m in l, 1 < p m := hp.eventually_gt_atTop _
  have hKpos : ∀ᶠ m in l, 0 < K m := by
    filter_upwards [hpd, hκ] with m hm hκm
    have := Gamma_pos_of_pos (show 0 < p m + 1 + d / 2 by linarith)
    have := Gamma_pos_of_pos (show 0 < p m + 1 by linarith)
    simp only [hK]
    positivity
  have hq : Tendsto (fun m => p m + 1) l atTop := tendsto_atTop_add_const_right _ _ hp
  have hlogK : Tendsto (fun m => log (K m)) l (𝓝 (-((d : ℝ) / 2 * log (4 * π)))) := by
    have h1 := (tendsto_gammaDefect_half d).comp hq
    have h2 := (tendsto_log_add_sub_log 1).comp hp
    have h3 := hpκ.log (by norm_num)
    have := (((h3.const_mul ((d : ℝ) / 2)).add h1).add (h2.const_mul ((d : ℝ) / 2))).sub
      (tendsto_const_nhds (x := (d : ℝ) / 2 * log π))
    rw [show (d : ℝ) / 2 * log (1 / 4) + 0 + d / 2 * 0 - d / 2 * log π =
      -(d / 2 * log (4 * π)) by rw [log_four_pi, one_div, log_inv]; ring] at this
    refine this.congr' ?_
    filter_upwards [hpd, hκ] with m hm hκm
    have hg1 := Gamma_pos_of_pos (show 0 < p m + 1 + d / 2 by linarith)
    have hg2 := Gamma_pos_of_pos (show 0 < p m + 1 by linarith)
    simp only [Function.comp_apply, gammaDefect, hK]
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) hg1.ne',
      log_mul (by positivity) hg2.ne', log_rpow pi_pos, log_rpow hκm,
      log_mul (by linarith) hκm.ne']
    ring
  obtain ⟨hc, hqc⟩ := tendsto_const_aux (s := (d : ℝ)) hp hKpos hlogK
  have hc' : Tendsto (fun m => compactBarenblattConst d (p m) (κ m)) l (𝓝 1) := hc
  have hqc' : Tendsto (fun m => p m * log (compactBarenblattConst d (p m) (κ m))) l
      (𝓝 (-((d : ℝ) / 2 * log (4 * π)))) := hqc
  have he : Tendsto (fun m => -(κ m * r m)) l (𝓝 0) := by simpa using (hκ0.mul hr).neg
  have hqe : Tendsto (fun m => p m * -(κ m * r m)) l (𝓝 (-(r0 / 4))) := by
    have := (hpκ.mul hr).neg
    rw [show -(1 / 4 * r0) = -(r0 / 4) by ring] at this
    exact this.congr fun m => by ring
  have hlim := tendsto_add_rpow hc' he hqc' hqe
  refine hlim.congr' ?_
  have hpos : ∀ᶠ m in l, 0 < compactBarenblattConst d (p m) (κ m) + -(κ m * r m) := by
    have := hc'.add he
    rw [add_zero] at this
    exact this.eventually (lt_mem_nhds one_pos)
  filter_upwards [hpos] with m hm
  rw [max_eq_left (by linarith), sub_eq_add_neg]

variable {d : ℕ}

/-! ### Identification of `B` with the explicit profiles -/

lemma barenblatt_eq_full {m : ℝ} (h : Admissible d m) (hm : m < 1) (z : E d) :
    barenblatt d m z =
      (fullBarenblattConst d (1 / (1 - m)) (alpha d m * (1 - m) / (2 * m)) +
        alpha d m * (1 - m) / (2 * m) * ‖z‖ ^ 2) ^ (-(1 / (1 - m))) := by
  have hα := alpha_pos h
  have hκ : 0 < alpha d m * (1 - m) / (2 * m) := by
    have := h.2.1
    have : 0 < 1 - m := by linarith
    positivity
  have hp := Barenblatt.half_lt_p_full h hm
  have hc0 := fullBarenblattConst_pos (d := d) hp hκ
  have hbw :
      barenblattWith d m (fullBarenblattConst d (1 / (1 - m)) (alpha d m * (1 - m) / (2 * m))) =
        fullBarenblatt d (1 / (1 - m)) (alpha d m * (1 - m) / (2 * m)) :=
    funext fun x => by
      unfold barenblattWith
      exact Barenblatt.max_rpow_eq_full hc0.le hκ.le x
  have hceq := (barenblattConst_spec' h.1 h.2.1 h.2.2.1 h.2.2.2).2.2.2 _ hc0
    (by rw [hbw]; exact Barenblatt.integrable_fullBarenblatt h.1 hp hκ)
    (by rw [hbw]; exact Barenblatt.integral_fullBarenblatt h.1 hp hκ)
  unfold barenblatt
  rw [← hceq, hbw]
  rfl

lemma barenblatt_eq_compact {m : ℝ} (h : Admissible d m) (hm : 1 < m) (z : E d) :
    barenblatt d m z =
      (max (compactBarenblattConst d (1 / (m - 1)) (alpha d m * (m - 1) / (2 * m)) -
        alpha d m * (m - 1) / (2 * m) * ‖z‖ ^ 2) 0) ^ (1 / (m - 1)) := by
  have hα := alpha_pos h
  have hκ : 0 < alpha d m * (m - 1) / (2 * m) := by
    have := h.2.1
    have : 0 < m - 1 := by linarith
    positivity
  have hp := Barenblatt.p_compact_pos hm
  have hc0 := compactBarenblattConst_pos (d := d) hp hκ
  have hbw : ∀ c, barenblattWith d m c =
      fun x => (max (c - alpha d m * (m - 1) / (2 * m) * ‖x‖ ^ 2) 0) ^ (1 / (m - 1)) :=
    fun c => funext fun x => by
      unfold barenblattWith
      rw [show c + alpha d m * (1 - m) / (2 * m) * ‖x‖ ^ 2 =
        c - alpha d m * (m - 1) / (2 * m) * ‖x‖ ^ 2 by ring]
  have hceq := (barenblattConst_spec' h.1 h.2.1 h.2.2.1 h.2.2.2).2.2.2 _ hc0
    (by rw [hbw]; exact Barenblatt.integrable_compactBarenblatt h.1 hp hκ)
    (by rw [hbw]; exact Barenblatt.integral_compactBarenblatt h.1 hp hκ)
  unfold barenblatt
  rw [← hceq, hbw]

/-! ### The two one-sided limits -/

/-- `α → 1/2` as `m → 1`. -/
lemma tendsto_alpha (d : ℕ) : Tendsto (alpha d) (𝓝 1) (𝓝 (1 / 2)) := by
  have h : Tendsto (fun m : ℝ => 2 - d * (1 - m)) (𝓝 1) (𝓝 2) := by
    have := (tendsto_const_nhds (x := (2 : ℝ))).sub ((tendsto_const_nhds (x := (d : ℝ))).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id (x := 𝓝 (1 : ℝ)))))
    simpa using this
  exact tendsto_const_nhds.div h two_ne_zero

lemma tendsto_barenblatt_lt (hd : 1 ≤ d) {y : ℝ → E d} {y0 : E d}
    (hy : Tendsto y (𝓝[<] 1) (𝓝 y0)) :
    Tendsto (fun m => barenblatt d m (y m)) (𝓝[<] 1)
      (𝓝 (exp (-((d : ℝ) / 2 * log (4 * π)) + -(‖y0‖ ^ 2 / 4)))) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hadm : ∀ᶠ m in 𝓝[<] (1 : ℝ), Admissible d m ∧ m < 1 := by
    have hlt : max 0 (((d : ℝ) - 2) / d) < 1 :=
      max_lt one_pos (by rw [div_lt_one hdpos]; linarith)
    filter_upwards [Ioo_mem_nhdsLT hlt] with m hm
    exact ⟨⟨hd, (le_max_left _ _).trans_lt hm.1, hm.2.ne, (le_max_right _ _).trans_lt hm.1⟩, hm.2⟩
  have hα : Tendsto (alpha d) (𝓝[<] 1) (𝓝 (1 / 2)) := (tendsto_alpha d).mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun m : ℝ => m) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1m : Tendsto (fun m : ℝ => 1 - m) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hid
    · filter_upwards [self_mem_nhdsWithin] with m hm
      exact sub_pos.2 hm
  have hp : Tendsto (fun m : ℝ => 1 / (1 - m)) (𝓝[<] 1) atTop := by
    exact (tendsto_inv_nhdsGT_zero.comp h1m).congr fun m => (one_div _).symm
  have hκ0 : Tendsto (fun m => alpha d m * (1 - m) / (2 * m)) (𝓝[<] 1) (𝓝 0) := by
    have := (hα.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hid)).div
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hid) (by norm_num)
    rw [show (1 : ℝ) / 2 * (1 - 1) / (2 * 1) = 0 by norm_num] at this
    exact this
  have hpκ : Tendsto (fun m => 1 / (1 - m) * (alpha d m * (1 - m) / (2 * m))) (𝓝[<] 1)
      (𝓝 (1 / 4)) := by
    have := hα.div ((tendsto_const_nhds (x := (2 : ℝ))).mul hid) (by norm_num)
    rw [show (1 : ℝ) / 2 / (2 * 1) = 1 / 4 by norm_num] at this
    refine this.congr' ?_
    filter_upwards [hadm] with m hm
    have : 1 - m ≠ 0 := by linarith [hm.2]
    have := hm.1.2.1.ne'
    simp only [Pi.div_apply]
    field_simp
  have hκ : ∀ᶠ m in 𝓝[<] (1 : ℝ), 0 < alpha d m * (1 - m) / (2 * m) := by
    filter_upwards [hadm] with m hm
    have := alpha_pos hm.1
    have := hm.1.2.1
    have : 0 < 1 - m := by linarith [hm.2]
    positivity
  have hr : Tendsto (fun m => ‖y m‖ ^ 2) (𝓝[<] 1) (𝓝 (‖y0‖ ^ 2)) := hy.norm.pow 2
  refine (tendsto_full_core hp hκ hκ0 hpκ hr).congr' ?_
  filter_upwards [hadm] with m hm
  rw [barenblatt_eq_full hm.1 hm.2]

lemma tendsto_barenblatt_gt (hd : 1 ≤ d) {y : ℝ → E d} {y0 : E d}
    (hy : Tendsto y (𝓝[>] 1) (𝓝 y0)) :
    Tendsto (fun m => barenblatt d m (y m)) (𝓝[>] 1)
      (𝓝 (exp (-((d : ℝ) / 2 * log (4 * π)) + -(‖y0‖ ^ 2 / 4)))) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hadm : ∀ᶠ m in 𝓝[>] (1 : ℝ), Admissible d m ∧ 1 < m := by
    have hlt : ((d : ℝ) - 2) / d < 1 := by rw [div_lt_one hdpos]; linarith
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with m hm
    exact ⟨⟨hd, by linarith [hm.1], hm.1.ne', hlt.trans hm.1⟩, hm.1⟩
  have hα : Tendsto (alpha d) (𝓝[>] 1) (𝓝 (1 / 2)) := (tendsto_alpha d).mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun m : ℝ => m) (𝓝[>] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1m : Tendsto (fun m : ℝ => m - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using hid.sub (tendsto_const_nhds (x := (1 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with m hm
      exact sub_pos.2 hm
  have hp : Tendsto (fun m : ℝ => 1 / (m - 1)) (𝓝[>] 1) atTop := by
    exact (tendsto_inv_nhdsGT_zero.comp h1m).congr fun m => (one_div _).symm
  have hκ0 : Tendsto (fun m => alpha d m * (m - 1) / (2 * m)) (𝓝[>] 1) (𝓝 0) := by
    have := (hα.mul (hid.sub (tendsto_const_nhds (x := (1 : ℝ))))).div
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hid) (by norm_num)
    rw [show (1 : ℝ) / 2 * (1 - 1) / (2 * 1) = 0 by norm_num] at this
    exact this
  have hpκ : Tendsto (fun m => 1 / (m - 1) * (alpha d m * (m - 1) / (2 * m))) (𝓝[>] 1)
      (𝓝 (1 / 4)) := by
    have := hα.div ((tendsto_const_nhds (x := (2 : ℝ))).mul hid) (by norm_num)
    rw [show (1 : ℝ) / 2 / (2 * 1) = 1 / 4 by norm_num] at this
    refine this.congr' ?_
    filter_upwards [hadm] with m hm
    have : m - 1 ≠ 0 := by linarith [hm.2]
    have := hm.1.2.1.ne'
    simp only [Pi.div_apply]
    field_simp
  have hκ : ∀ᶠ m in 𝓝[>] (1 : ℝ), 0 < alpha d m * (m - 1) / (2 * m) := by
    filter_upwards [hadm] with m hm
    have := alpha_pos hm.1
    have := hm.1.2.1
    have : 0 < m - 1 := by linarith [hm.2]
    positivity
  have hr : Tendsto (fun m => ‖y m‖ ^ 2) (𝓝[>] 1) (𝓝 (‖y0‖ ^ 2)) := hy.norm.pow 2
  refine (tendsto_compact_core hp hκ hκ0 hpκ hr).congr' ?_
  filter_upwards [hadm] with m hm
  rw [barenblatt_eq_compact hm.1 hm.2]

/-! ### The diffusion limit along converging arguments -/

/-- **Diffusion limit, locally uniform form**: if `y_m → y₀` as `m → 1`, `m ≠ 1`, then
`B_m(y_m) → (4π)^{-d/2} e^{-|y₀|²/4}`. -/
theorem tendsto_barenblatt_of_tendsto (hd : 1 ≤ d) {y : ℝ → E d} {y0 : E d}
    (hy : Tendsto y (𝓝[≠] 1) (𝓝 y0)) :
    Tendsto (fun m => barenblatt d m (y m)) (𝓝[≠] 1)
      (𝓝 ((4 * π) ^ (-(d : ℝ) / 2) * exp (-‖y0‖ ^ 2 / 4))) := by
  have heq : (4 * π) ^ (-(d : ℝ) / 2) * exp (-‖y0‖ ^ 2 / 4) =
      exp (-((d : ℝ) / 2 * log (4 * π)) + -(‖y0‖ ^ 2 / 4)) := by
    rw [rpow_def_of_pos (by positivity), ← exp_add]
    congr 1
    ring
  rw [heq, ← nhdsLT_sup_nhdsGT]
  exact (tendsto_barenblatt_lt hd (hy.mono_left (nhdsWithin_mono _
      fun m hm => (Set.mem_Iio.1 hm).ne))).sup
    (tendsto_barenblatt_gt hd (hy.mono_left (nhdsWithin_mono _
      fun m hm => (Set.mem_Ioi.1 hm).ne')))

/-- Diffusion limit for the self-similar rescalings `τ^{-αd} B(τ^{-α} z)` with `τ → τ₀ > 0`. -/
theorem tendsto_scaled_barenblatt (hd : 1 ≤ d) {τ : ℝ → ℝ} {τ0 : ℝ} (hτ0 : 0 < τ0)
    (hτ : Tendsto τ (𝓝[≠] 1) (𝓝 τ0)) (z : E d) :
    Tendsto (fun m => (τ m ^ (alpha d m * d))⁻¹ * barenblatt d m ((τ m ^ alpha d m)⁻¹ • z))
      (𝓝[≠] 1) (𝓝 ((4 * π * τ0) ^ (-(d : ℝ) / 2) * exp (-‖z‖ ^ 2 / (4 * τ0)))) := by
  have hα : Tendsto (alpha d) (𝓝[≠] 1) (𝓝 (1 / 2)) :=
    (tendsto_alpha d).mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun m => τ m ^ (alpha d m * d)) (𝓝[≠] 1) (𝓝 (τ0 ^ (1 / 2 * (d : ℝ)))) :=
    hτ.rpow (hα.mul_const _) (Or.inl hτ0.ne')
  have h2 : Tendsto (fun m => τ m ^ alpha d m) (𝓝[≠] 1) (𝓝 (τ0 ^ (1 / 2 : ℝ))) :=
    hτ.rpow hα (Or.inl hτ0.ne')
  have hs : 0 < τ0 ^ (1 / 2 : ℝ) := rpow_pos_of_pos hτ0 _
  have h3 := tendsto_barenblatt_of_tendsto hd ((h2.inv₀ hs.ne').smul_const z)
  have := (h1.inv₀ (rpow_pos_of_pos hτ0 _).ne').mul h3
  convert this using 2
  have hs2 : (τ0 ^ (1 / 2 : ℝ)) ^ 2 = τ0 := by
    rw [← rpow_natCast, ← rpow_mul hτ0.le]
    norm_num
  rw [norm_smul, norm_inv, norm_of_nonneg hs.le, mul_pow, inv_pow, hs2,
    mul_rpow (by positivity) hτ0.le, show -(d : ℝ) / 2 = -(1 / 2 * d) by ring,
    rpow_neg hτ0.le]
  rw [show -(τ0⁻¹ * ‖z‖ ^ 2) / 4 = -‖z‖ ^ 2 / (4 * τ0) by field_simp]
  ring

end DiffusionLimit

open DiffusionLimit

/-- Diffusion limit (Section 1.4.2): as `m → 1` at fixed `d`, `B(x) → (4π)^{-d/2} e^{-|x|²/4}`. -/
theorem tendsto_barenblatt_one' {d : ℕ} (hd : 1 ≤ d) (x : E d) :
    Tendsto (fun m => barenblatt d m x) (𝓝[≠] 1)
      (𝓝 ((4 * π) ^ (-(d : ℝ) / 2) * exp (-‖x‖ ^ 2 / 4))) :=
  tendsto_barenblatt_of_tendsto hd tendsto_const_nhds

/-- Diffusion limit, heat kernel (eq. (heatkernel)): as `m → 1`,
`u(t,x) → (4πt)^{-d/2} e^{-|x-x₀|²/(4t)}`. -/
theorem tendsto_fdeSolution_one' {d : ℕ} (hd : 1 ≤ d) (x₀ : E d) {t : ℝ} (ht : 0 < t)
    (x : E d) :
    Tendsto (fun m => fdeSolution d m x₀ t x) (𝓝[≠] 1)
      (𝓝 ((4 * π * t) ^ (-(d : ℝ) / 2) * exp (-‖x - x₀‖ ^ 2 / (4 * t)))) :=
  tendsto_scaled_barenblatt hd ht tendsto_const_nhds (x - x₀)

/-- Diffusion limit, Mehler formula: as `m → 1`, `v(t,·)` tends pointwise to the density of
`𝒩(e^{-t}x₀, (1-e^{-2t}) I)`. -/
theorem tendsto_solution_one' {d : ℕ} (hd : 1 ≤ d) (x₀ : E d) {t : ℝ} (ht : 0 < t) (x : E d) :
    Tendsto (fun m => solution d m x₀ t x) (𝓝[≠] 1)
      (𝓝 ((2 * π * (1 - exp (-2 * t))) ^ (-(d : ℝ) / 2) *
        exp (-‖x - exp (-t) • x₀‖ ^ 2 / (2 * (1 - exp (-2 * t)))))) := by
  have hα : Tendsto (alpha d) (𝓝[≠] 1) (𝓝 (1 / 2)) :=
    (tendsto_alpha d).mono_left nhdsWithin_le_nhds
  have hτ0 : 0 < (1 - exp (-2 * t)) / 2 := by
    have : exp (-2 * t) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hτ : Tendsto (fun m => alpha d m * (1 - exp (-t / alpha d m))) (𝓝[≠] 1)
      (𝓝 ((1 - exp (-2 * t)) / 2)) := by
    have : Tendsto (fun m => alpha d m * (1 - exp (-t / alpha d m))) (𝓝[≠] 1)
        (𝓝 (1 / 2 * (1 - exp (-t / (1 / 2))))) :=
      hα.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub ((continuous_exp.tendsto _).comp
        ((tendsto_const_nhds (x := -t)).div hα (by norm_num))))
    rwa [show -t / (1 / 2) = -2 * t by ring, show 1 / 2 * (1 - exp (-2 * t)) =
      (1 - exp (-2 * t)) / 2 by ring] at this
  have := tendsto_scaled_barenblatt hd hτ0 hτ (x - exp (-t) • x₀)
  rw [show 2 * π * (1 - exp (-2 * t)) = 4 * π * ((1 - exp (-2 * t)) / 2) by ring,
    show 2 * (1 - exp (-2 * t)) = 4 * ((1 - exp (-2 * t)) / 2) by ring]
  exact this

end Cutfast
