/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.Definitions
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.Chebyshev

/-!
# The functions `g_n` of [I71, §3]

Iwaniec's functions `g_n` (`n ≥ 2`) of [I71, (3.1)–(3.3)], defined on all of `ℝ` in
`IwaniecLinearSieve.Definitions`, are:

* `g 2 s = 3 log (3 / (s - 1)) + s - 4` for `2 ≤ s ≤ 4` and `g 2 s = 0` for `s ≥ 4`;
* `g (2n+1) s = ∫_s^∞ g (2n) (t-1) / (t-1) dt` for `s ≥ 3` and `g (2n+1) s = g (2n+1) 3` for
  `s ≤ 3`;
* `g (2n+2) s = ∫_s^∞ g (2n+1) (t-1) / (t-1) dt` for `s ≥ 2`.

Outside the domains of [I71] the argument is clamped (`g 2` and the even functions are constant
on `s ≤ 2`, the odd functions on `s ≤ 3`), and `g 0 = g 1 = 0`. With these conventions every
`g i` is continuous, nonnegative and antitone on all of `ℝ`, and `g i s = 0` for `s ≥ i + 2`.
-/

@[expose] public section

open Real Set MeasureTheory intervalIntegral

namespace IwaniecLinearSieve

theorem g_zero (s : ℝ) : g 0 s = 0 := rfl

theorem g_one (s : ℝ) : g 1 s = 0 := rfl

theorem g_two_def (s : ℝ) : g 2 s = gTwoFormula (max 2 (min s 4)) := rfl

theorem g_add_three (n : ℕ) (s : ℝ) :
    g (n + 3) s = ∫ t in max s (gLower (n + 3))..((n : ℝ) + 5), shiftKernel (g (n + 2)) t := rfl

theorem gLower_le_three (i : ℕ) : gLower i ≤ 3 := by
  unfold gLower; split_ifs <;> norm_num

theorem two_le_gLower (i : ℕ) : 2 ≤ gLower i := by
  unfold gLower; split_ifs <;> norm_num

theorem gLower_even {i : ℕ} (hi : Even i) : gLower i = 2 := by simp [gLower, hi]

theorem gLower_odd {i : ℕ} (hi : ¬ Even i) : gLower i = 3 := by simp [gLower, hi]

theorem shiftKernel_of_two_le (h : ℝ → ℝ) {t : ℝ} (ht : 2 ≤ t) :
    shiftKernel h t = h (t - 1) / (t - 1) := by
  rw [shiftKernel, max_eq_left (by linarith)]

theorem continuous_shiftKernel {h : ℝ → ℝ} (hh : Continuous h) : Continuous (shiftKernel h) :=
  (hh.comp (continuous_sub_right 1)).div ((continuous_sub_right 1).max continuous_const)
    fun _ => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'

theorem shiftKernel_nonneg {h : ℝ → ℝ} (hh : ∀ s, 0 ≤ h s) (t : ℝ) : 0 ≤ shiftKernel h t :=
  div_nonneg (hh _) (le_trans zero_le_one (le_max_right _ _))

theorem continuous_integral_left {k : ℝ → ℝ} (hk : Continuous k) (b : ℝ) :
    Continuous fun u => ∫ t in u..b, k t := by
  have : (fun u => ∫ t in u..b, k t) = fun u => -∫ t in b..u, k t := by
    funext u; exact integral_symm _ _
  rw [this]
  exact (continuous_primitive (fun _ _ => hk.intervalIntegrable _ _) b).neg

/-! ### `g₂` -/
theorem gTwoFormula_four : gTwoFormula 4 = 0 := by norm_num [gTwoFormula]

theorem gTwoFormula_continuousOn : ContinuousOn gTwoFormula (Icc 2 4) := by
  unfold gTwoFormula
  refine ContinuousOn.sub (ContinuousOn.add (continuousOn_const.mul ?_) continuousOn_id)
    continuousOn_const
  refine ContinuousOn.log (continuousOn_const.div (continuousOn_id.sub continuousOn_const) ?_) ?_
  · intro x hx; have := hx.1; linarith
  · intro x hx; have := hx.1; exact div_ne_zero (by norm_num) (by linarith)

/-- `gTwoFormula u - gTwoFormula v ≥ 0` for `2 ≤ u ≤ v ≤ 4`, with strictness when `u < v`. -/
theorem gTwoFormula_sub_ge {u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) (hv : v ≤ 4) :
    (v - u) * (4 - v) / (v - 1) ≤ gTwoFormula u - gTwoFormula v ∧
      (u < v → 0 < gTwoFormula u - gTwoFormula v) := by
  have hu1 : 0 < u - 1 := by linarith
  have hv1 : 0 < v - 1 := by linarith
  have hlog : gTwoFormula u - gTwoFormula v = 3 * (-log ((u - 1) / (v - 1))) - (v - u) := by
    simp only [gTwoFormula]
    rw [log_div (by norm_num) hu1.ne', log_div (by norm_num) hv1.ne',
      log_div hu1.ne' hv1.ne']
    ring
  have key : 1 - (u - 1) / (v - 1) ≤ -log ((u - 1) / (v - 1)) := by
    linarith [log_le_sub_one_of_pos (div_pos hu1 hv1), log_inv ((u - 1) / (v - 1)),
      show ((u - 1) / (v - 1))⁻¹ = (v - 1) / (u - 1) from inv_div _ _]
  have h1 : 1 - (u - 1) / (v - 1) = (v - u) / (v - 1) := by field_simp; ring
  refine ⟨?_, fun huv' => ?_⟩
  · rw [hlog]
    have : (v - u) * (4 - v) / (v - 1) = 3 * ((v - u) / (v - 1)) - (v - u) := by
      field_simp; ring
    rw [this]; linarith
  · rw [hlog]
    have hne : (u - 1) / (v - 1) ≠ 1 := by
      rw [Ne, div_eq_one_iff_eq hv1.ne']; linarith
    have key' : 1 - (u - 1) / (v - 1) < -log ((u - 1) / (v - 1)) := by
      have := log_lt_sub_one_of_pos (div_pos hu1 hv1) hne
      linarith
    have : (v - u) ≤ 3 * ((v - u) / (v - 1)) := by
      rw [mul_div_assoc', le_div_iff₀ hv1]; nlinarith
    linarith

theorem gTwoFormula_nonneg {u : ℝ} (hu : 2 ≤ u) (hu4 : u ≤ 4) : 0 ≤ gTwoFormula u := by
  have := (gTwoFormula_sub_ge hu hu4 le_rfl).1
  rw [gTwoFormula_four] at this
  simpa using this

theorem gTwoFormula_pos {u : ℝ} (hu : 2 ≤ u) (hu4 : u < 4) : 0 < gTwoFormula u := by
  have := (gTwoFormula_sub_ge hu hu4.le le_rfl).2 hu4
  rwa [gTwoFormula_four, sub_zero] at this

/-! ### Basic properties of `g` -/

/-- [I71, (3.1)] on `[2, 4]`. -/
theorem g_two_eq {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 4) : g 2 s = 3 * log (3 / (s - 1)) + s - 4 := by
  rw [g_two_def, min_eq_left hs.2, max_eq_right hs.1]; rfl

/-- [I71, (3.1)] for `s ≥ 4`. -/
theorem g_two_of_four_le {s : ℝ} (hs : 4 ≤ s) : g 2 s = 0 := by
  rw [g_two_def, min_eq_right hs, max_eq_right (by norm_num), gTwoFormula_four]

theorem g_eq_of_le_gLower (i : ℕ) {s : ℝ} (hs : s ≤ gLower i) : g i s = g i (gLower i) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 =>
    have h2 : gLower 2 = 2 := gLower_even even_two
    rw [h2] at hs ⊢
    rw [g_two_def, g_two_def, min_eq_left (hs.trans (by norm_num)), max_eq_left hs]
    norm_num
  | n + 3 => rw [g_add_three, g_add_three, max_eq_right hs, max_self]

theorem g_add_three_eq (n : ℕ) {s : ℝ} (hs : gLower (n + 3) ≤ s) :
    g (n + 3) s = ∫ t in s..((n : ℝ) + 5), g (n + 2) (t - 1) / (t - 1) := by
  rw [g_add_three, max_eq_left hs]
  refine integral_congr fun t ht => shiftKernel_of_two_le _ ?_
  have := two_le_gLower (n + 3)
  rcases le_total s ((n : ℝ) + 5) with h | h
  · rw [uIcc_of_le h] at ht; linarith [ht.1]
  · rw [uIcc_of_ge h] at ht; linarith [ht.1, n.cast_nonneg (α := ℝ)]

theorem continuous_g : ∀ i, Continuous (g i)
  | 0 => continuous_const
  | 1 => continuous_const
  | 2 => by
    have : g 2 = gTwoFormula ∘ fun s => max 2 (min s 4) := rfl
    rw [this]
    exact gTwoFormula_continuousOn.comp_continuous
      (continuous_const.max (continuous_id.min continuous_const))
      fun s => ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  | n + 3 => by
    have : g (n + 3) = (fun u => ∫ t in u..((n : ℝ) + 5), shiftKernel (g (n + 2)) t) ∘
        fun s => max s (gLower (n + 3)) := rfl
    rw [this]
    exact (continuous_integral_left (continuous_shiftKernel (continuous_g (n + 2))) _).comp
      (continuous_id.max continuous_const)

/-- `g i s = 0` for `s ≥ i + 2` ([I71], remark after (3.3)). -/
theorem g_eq_zero_of_le : ∀ (i : ℕ) {s : ℝ}, (i : ℝ) + 2 ≤ s → g i s = 0
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | 2, _, hs => g_two_of_four_le (by norm_num at hs ⊢; linarith)
  | n + 3, s, hs => by
    push_cast at hs
    have hc : gLower (n + 3) ≤ s := (gLower_le_three _).trans (by linarith [n.cast_nonneg (α := ℝ)])
    rw [g_add_three, max_eq_left hc, integral_congr (g := fun _ => (0 : ℝ)),
      intervalIntegral.integral_zero]
    intro t ht
    rw [uIcc_of_ge (by linarith)] at ht
    simp only [shiftKernel]
    rw [g_eq_zero_of_le (n + 2) (by push_cast; linarith [ht.1]), zero_div]

theorem g_nonneg : ∀ (i : ℕ) (s : ℝ), 0 ≤ g i s
  | 0, _ => le_rfl
  | 1, _ => le_rfl
  | 2, _ => gTwoFormula_nonneg (le_max_left _ _) (max_le (by norm_num) (min_le_right _ _))
  | n + 3, s => by
    rcases le_or_gt ((n : ℝ) + 5) s with hs | hs
    · rw [g_eq_zero_of_le (n + 3) (by push_cast; linarith)]
    · rw [g_add_three]
      exact integral_nonneg
        (max_le hs.le (by linarith [gLower_le_three (n + 3), n.cast_nonneg (α := ℝ)]))
        fun t _ => shiftKernel_nonneg (g_nonneg (n + 2)) t

/-- `g i s > 0` for `i ≥ 2` and `s < i + 2`. -/
theorem g_pos : ∀ (i : ℕ), 2 ≤ i → ∀ {s : ℝ}, s < i + 2 → 0 < g i s
  | 0, h, _, _ => by omega
  | 1, h, _, _ => by omega
  | 2, _, s, hs => by
    norm_num at hs
    exact gTwoFormula_pos (le_max_left _ _) (max_lt (by norm_num) ((min_le_left _ _).trans_lt hs))
  | n + 3, _, s, hs => by
    push_cast at hs
    rw [g_add_three]
    have hc := gLower_le_three (n + 3)
    have hn := n.cast_nonneg (α := ℝ)
    refine intervalIntegral_pos_of_pos_on
      ((continuous_shiftKernel (continuous_g _)).intervalIntegrable _ _) (fun t ht => ?_)
      (max_lt (by linarith) (by linarith))
    have ht1 : max s (gLower (n + 3)) < t := ht.1
    have ht2 : t < (n : ℝ) + 5 := ht.2
    have h3 : 2 ≤ t := by linarith [le_max_right s (gLower (n + 3)), two_le_gLower (n + 3)]
    rw [shiftKernel_of_two_le _ h3]
    exact div_pos (g_pos (n + 2) (by omega) (by push_cast; linarith)) (by linarith)

theorem g_antitone : ∀ i, Antitone (g i)
  | 0 => antitone_const
  | 1 => antitone_const
  | 2 => fun u v huv => by
    rw [g_two_def, g_two_def]
    have h := (gTwoFormula_sub_ge (le_max_left 2 (min u 4))
      (max_le_max le_rfl (min_le_min huv le_rfl)) (max_le (by norm_num) (min_le_right v 4))).1
    have h1 : 0 ≤ max 2 (min v 4) - max 2 (min u 4) :=
      sub_nonneg.2 (max_le_max le_rfl (min_le_min huv le_rfl))
    have h2 : 0 ≤ 4 - max 2 (min v 4) := sub_nonneg.2 (max_le (by norm_num) (min_le_right v 4))
    have h3 : 0 ≤ max 2 (min v 4) - 1 := by linarith [le_max_left 2 (min v 4)]
    linarith [div_nonneg (mul_nonneg h1 h2) h3]
  | n + 3 => fun u v huv => by
    rw [g_add_three, g_add_three]
    have hk := continuous_shiftKernel (continuous_g (n + 2))
    rw [← integral_add_adjacent_intervals (hk.intervalIntegrable (max u (gLower (n + 3)))
      (max v (gLower (n + 3)))) (hk.intervalIntegrable _ _)]
    have : 0 ≤ ∫ t in max u (gLower (n + 3))..max v (gLower (n + 3)), shiftKernel (g (n + 2)) t :=
      integral_nonneg (max_le_max huv le_rfl) fun t _ => shiftKernel_nonneg (g_nonneg (n + 2)) t
    linarith

/-- Differences of `g (n + 3)` are integrals of the kernel. -/
theorem g_add_three_sub (n : ℕ) {u v : ℝ} (hu : gLower (n + 3) ≤ u) (hv : gLower (n + 3) ≤ v) :
    g (n + 3) u - g (n + 3) v = ∫ t in u..v, shiftKernel (g (n + 2)) t := by
  have hk := continuous_shiftKernel (continuous_g (n + 2))
  rw [g_add_three, g_add_three, max_eq_left hu, max_eq_left hv,
    ← integral_add_adjacent_intervals (hk.intervalIntegrable u v) (hk.intervalIntegrable v _)]
  ring

/-! ### Improper integrals -/

/-- If `h` is integrable on `(s, b]` and vanishes on `[b, ∞)`, then it is integrable on `(s, ∞)`
and its integral there is `∫_s^b h`. -/
theorem integral_Ioi_eq_of_eq_zero {h : ℝ → ℝ} {s b : ℝ} (hsb : s ≤ b)
    (hint : IntegrableOn h (Ioc s b)) (hz : ∀ t, b ≤ t → h t = 0) :
    IntegrableOn h (Ioi s) ∧ ∫ t in Ioi s, h t = ∫ t in s..b, h t := by
  have hI : IntegrableOn h (Ioi b) :=
    integrableOn_zero.congr_fun (fun t ht => (hz t (le_of_lt ht)).symm) measurableSet_Ioi
  have hI' : IntegrableOn h (Ioi s) := by
    rw [← Ioc_union_Ioi_eq_Ioi hsb]; exact hint.union hI
  refine ⟨hI', ?_⟩
  have := integral_Ioi_sub_Ioi hI' hsb
  rwa [setIntegral_eq_zero_of_forall_eq_zero (t := Ioi b) (fun t ht => hz t (le_of_lt ht)),
    sub_zero] at this

theorem g_add_three_eq_Ioi (n : ℕ) {s : ℝ} (hs : gLower (n + 3) ≤ s) :
    IntegrableOn (fun t => g (n + 2) (t - 1) / (t - 1)) (Ioi s) ∧
      g (n + 3) s = ∫ t in Ioi s, g (n + 2) (t - 1) / (t - 1) := by
  have h2 := two_le_gLower (n + 3)
  have hz : ∀ t, (n : ℝ) + 5 ≤ t → g (n + 2) (t - 1) / (t - 1) = 0 := fun t ht => by
    rw [g_eq_zero_of_le (n + 2) (by push_cast; linarith), zero_div]
  rcases le_or_gt s ((n : ℝ) + 5) with hsb | hsb
  · have hcont : ContinuousOn (fun t => g (n + 2) (t - 1) / (t - 1)) (Icc s ((n : ℝ) + 5)) :=
      (continuous_shiftKernel (continuous_g (n + 2))).continuousOn.congr
        fun t ht => (shiftKernel_of_two_le _ (by linarith [ht.1])).symm
    obtain ⟨hI, hEq⟩ := integral_Ioi_eq_of_eq_zero hsb
      ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self) hz
    exact ⟨hI, by rw [hEq, g_add_three_eq n hs]⟩
  · obtain ⟨hI, hEq⟩ := integral_Ioi_eq_of_eq_zero le_rfl (by simp) fun t ht => hz t (by linarith)
    refine ⟨hI, ?_⟩
    rw [hEq, integral_same, g_eq_zero_of_le (n + 3) (by push_cast; linarith)]

/-! ### The identities (3.2), (3.3) in the form of [I71] -/
theorem not_even_two_mul_add_three (m : ℕ) : ¬ Even (2 * m + 3) := by
  rw [Nat.not_even_iff_odd]; exact ⟨m + 1, by ring⟩

theorem even_two_mul_add_four (m : ℕ) : Even (2 * m + 4) := ⟨m + 2, by ring⟩

/-- [I71, (3.2)], first line: `g_{2n+1}(s) = ∫_s^∞ g_{2n}(t-1)/(t-1) dt` for `s ≥ 3`. -/
theorem g_odd_eq_integral {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 3 ≤ s) :
    IntegrableOn (fun t => g (2 * n) (t - 1) / (t - 1)) (Ioi s) ∧
      g (2 * n + 1) s = ∫ t in Ioi s, g (2 * n) (t - 1) / (t - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
  have e2 : 2 * (m + 1) = 2 * m + 2 := by ring
  rw [e1, e2]
  exact g_add_three_eq_Ioi (2 * m) (by rw [gLower_odd (not_even_two_mul_add_three m)]; exact hs)

/-- [I71, (3.2)], second line: `g_{2n+1}(s) = g_{2n+1}(3)` for `s ≤ 3`. -/
theorem g_odd_of_le_three (n : ℕ) {s : ℝ} (hs : s ≤ 3) : g (2 * n + 1) s = g (2 * n + 1) 3 := by
  rcases n with _ | m
  · rfl
  · have e1 : 2 * (m + 1) + 1 = 2 * m + 3 := by ring
    rw [e1]
    have h := gLower_odd (not_even_two_mul_add_three m)
    rw [g_eq_of_le_gLower _ (h ▸ hs), h]

/-- [I71, (3.3)]: `g_{2n+2}(s) = ∫_s^∞ g_{2n+1}(t-1)/(t-1) dt` for `s ≥ 2`. -/
theorem g_even_eq_integral {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 2 ≤ s) :
    IntegrableOn (fun t => g (2 * n + 1) (t - 1) / (t - 1)) (Ioi s) ∧
      g (2 * n + 2) s = ∫ t in Ioi s, g (2 * n + 1) (t - 1) / (t - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (m + 1) + 2 = (2 * m + 1) + 3 := by ring
  have e2 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
  rw [e1, e2]
  refine g_add_three_eq_Ioi (2 * m + 1) ?_
  rw [show 2 * m + 1 + 3 = 2 * m + 4 by ring, gLower_even (even_two_mul_add_four m)]; exact hs

/-- Even `g` are constant on `s ≤ 2`. -/
theorem g_even_of_le_two (n : ℕ) {s : ℝ} (hs : s ≤ 2) : g (2 * n + 2) s = g (2 * n + 2) 2 := by
  have h : gLower (2 * n + 2) = 2 := gLower_even ⟨n + 1, by ring⟩
  rw [g_eq_of_le_gLower _ (h ▸ hs), h]

end IwaniecLinearSieve
