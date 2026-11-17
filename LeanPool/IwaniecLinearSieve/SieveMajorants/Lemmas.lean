/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.SieveMajorants.Majorants
import LeanPool.IwaniecLinearSieve.SieveMajorants.Delay
import LeanPool.IwaniecLinearSieve.SieveMajorants.Properties
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Polynomial.Basic

/-!
# [I71, Lemmas 8, 9 (lower bound), 10]

* Lemma 8: `𝔐(s-1) < 4 s² 𝔐(s)` for `s ≥ 3`.
* Lemma 10: `log t 𝔐(t) < 2 t/(t-1)² 𝔐(t-1)` for `t ≥ 2`; hence `𝔐(t) t log t / 𝔐(t-1) < 9/2`
  for `t ≥ 3`, and the Corollary `G_{r+1}(t) (t-1)² log t / (G_r(t-1) t) < 4` for `t ≥ 2`.
* Lemma 9 (lower bound): `G_r(s) ≥ exp(-s log s - s log log s - c s)` for `s ≥ 3`.

[I71] proves Lemma 10 assuming that `𝔐(t-1)/𝔐(t)` is increasing; we instead use a first
crossing argument for the inequality itself (cf. [Opera de Cribro, Lemma 11.7]). For Lemma 9 we
compare `𝔐` with the explicit subsolution `exp(-(s log s + s log log s + 2s))` of (3.12),
instead of quoting the asymptotics of Hua's book.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace IwaniecLinearSieve

/-! ### Lemma 8 -/

/-- From (3.12): `𝔐(s - 1/2) ≤ 2(s-1)²/s 𝔐(s)` for `s ≥ 3`. -/
theorem bigM_sub_half_le {s : ℝ} (hs : 3 ≤ s) :
    bigM (s - 1 / 2) ≤ 2 * (s - 1) ^ 2 / s * bigM s := by
  have hs0 : 0 < s := by linarith only [hs]
  have hy : 0 < (s - 1) ^ 2 := by nlinarith only [hs]
  have hs1 : s - 1 ≠ 0 := by linarith only [hs]
  have hwc := continuousOn_weight_mul continuous_bigM (a := s - 1) (b := s) (by linarith only [hs])
  have hI : ∀ a b, s - 1 ≤ a → a ≤ b → b ≤ s →
      IntervalIntegrable (fun x => (1 - 1 / (2 * x ^ 2)) * bigM x) volume a b :=
    fun a b ha hab hb => (hwc.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hI (s - 1) (s - 1 / 2) le_rfl (by linarith) (by linarith))
    (hI (s - 1 / 2) s (by linarith) (by linarith) le_rfl)
  have h2 : 0 ≤ ∫ x in (s - 1 / 2)..s, (1 - 1 / (2 * x ^ 2)) * bigM x :=
    intervalIntegral.integral_nonneg (by linarith only []) fun x hx =>
      (mul_pos (weight_mem (by linarith only [hx.1, hs, hx])).1 (bigM_pos x)).le
  have h1 : ∫ _ in (s - 1)..(s - 1 / 2), (1 - 1 / (2 * (s - 1) ^ 2)) * bigM (s - 1 / 2) ≤
      ∫ x in (s - 1)..(s - 1 / 2), (1 - 1 / (2 * x ^ 2)) * bigM x := by
    refine intervalIntegral.integral_mono_on (by linarith only []) intervalIntegrable_const
      (hI _ _ le_rfl (by linarith) (by linarith)) fun x hx => ?_
    have hw : 1 - 1 / (2 * (s - 1) ^ 2) ≤ 1 - 1 / (2 * x ^ 2) := by
      have : 1 / (2 * x ^ 2) ≤ 1 / (2 * (s - 1) ^ 2) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith only [hx.1, hx, hs])
      linarith only [this]
    exact mul_le_mul hw (bigM_antitone hx.2) (bigM_pos _).le
      (weight_mem (by linarith only [hx.1, hs, hx])).1.le
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  have key := bigM_integral_identity hs
  rw [← hsplit] at key
  have : (s - 1 / 2 - (s - 1)) * ((1 - 1 / (2 * (s - 1) ^ 2)) * bigM (s - 1 / 2)) ≤
      ((s - 1) ^ 2 - 1 / 2) * bigM s / s := by linarith only [h2, h1, key]
  have e1 : (s - 1 / 2 - (s - 1)) * ((1 - 1 / (2 * (s - 1) ^ 2)) * bigM (s - 1 / 2)) =
      ((s - 1) ^ 2 - 1 / 2) * bigM (s - 1 / 2) / (2 * (s - 1) ^ 2) := by
    field_simp; ring
  rw [e1, div_le_div_iff₀ (by positivity) hs0] at this
  have hr : 0 < (s - 1) ^ 2 - 1 / 2 := by nlinarith only [hs, hy]
  rw [div_mul_eq_mul_div, le_div_iff₀ hs0]
  nlinarith only [this, hr]

/-- [I71, Lemma 8]: `𝔐(s-1) < 4 s² 𝔐(s)` for `s ≥ 3`. -/
theorem bigM_sub_one_lt {s : ℝ} (hs : 3 ≤ s) : bigM (s - 1) < 4 * s ^ 2 * bigM s := by
  have hs0 : 0 < s := by linarith only [hs]
  have hB := bigM_sub_half_le hs
  have hMs := bigM_pos s
  rcases le_total s (7 / 2) with h | h
  · have h1 : bigM (s - 1) ≤ 3 := bigM_le_three _
    have h2 : bigM 3 ≤ bigM (s - 1 / 2) := bigM_antitone (by linarith only [h])
    rw [bigM_three] at h2
    have h3 : 2 * (s - 1) ^ 2 / s ≤ s ^ 2 := by
      rw [div_le_iff₀ hs0]; nlinarith only [hs]
    have := mul_le_mul_of_nonneg_right h3 hMs.le
    nlinarith only [log_two_lt_d9, hB, h1, h2, this]
  · have hA := bigM_sub_half_le (s := s - 1 / 2) (by linarith only [h])
    rw [show s - 1 / 2 - 1 / 2 = s - 1 by ring] at hA
    have h3 : 2 * (s - 1 / 2 - 1) ^ 2 / (s - 1 / 2) < 2 * s := by
      rw [div_lt_iff₀ (by linarith only [h])]; nlinarith
    have h4 : 2 * (s - 1) ^ 2 / s < 2 * s := by
      rw [div_lt_iff₀ hs0]; nlinarith only [h]
    have h5 : 0 < 2 * (s - 1) ^ 2 / s := div_pos (by nlinarith only [h, hs]) hs0
    calc bigM (s - 1) ≤ 2 * (s - 1 / 2 - 1) ^ 2 / (s - 1 / 2) * bigM (s - 1 / 2) := hA
      _ ≤ 2 * (s - 1 / 2 - 1) ^ 2 / (s - 1 / 2) * (2 * (s - 1) ^ 2 / s * bigM s) :=
        mul_le_mul_of_nonneg_left hB (div_nonneg (by positivity) (by linarith only [h]))
      _ < 2 * s * (2 * s * bigM s) := by
        apply mul_lt_mul' h3.le (mul_lt_mul_of_pos_right h4 hMs) (by positivity) (by
          linarith only [h])
      _ = 4 * s ^ 2 * bigM s := by ring

/-- [I71, Lemma 8] in ratio form. -/
theorem bigM_sub_one_div_lt {s : ℝ} (hs : 3 ≤ s) : bigM (s - 1) / bigM s < 4 * s ^ 2 := by
  rw [div_lt_iff₀ (bigM_pos s)]; exact bigM_sub_one_lt hs

/-! ### Lemma 10 -/

/-- `∫_{a}^{a+1} exp(-λ(x - a)) dx = (1 - exp(-λ))/λ`. -/
theorem integral_exp_neg_mul_unit (a : ℝ) {l : ℝ} (hl : l ≠ 0) :
    ∫ x in a..(a + 1), exp (-(l * (x - a))) = (1 - exp (-l)) / l := by
  have hderiv : ∀ x ∈ uIcc a (a + 1), HasDerivAt (fun x => -exp (-(l * (x - a))) / l)
      (exp (-(l * (x - a)))) x := by
    intro x _
    have h := ((((hasDerivAt_id' x).sub_const a).const_mul l).neg).exp.neg.div_const l
    refine h.congr_deriv ?_
    simp only [Pi.neg_apply]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun x => exp (-(l * (x - a)))).intervalIntegrable _ _)]
  simp only [add_sub_cancel_left, mul_one, sub_self, mul_zero, neg_zero, exp_zero]
  ring

theorem log_four_lt : log 4 < 1.3863 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
  have := log_two_lt_d9
  push_cast
  linarith only [this]

/-- The numerical comparison in the main range of Lemma 10. With `q² = t - 1`, the
logarithmic bound makes the integrated exponential estimate smaller than `2t/(t-1)²`. -/
theorem log_mul_ratio_lt {t q L : ℝ} (ht0 : 0 < t) (hq1 : 1 < q)
    (hq2 : q ^ 2 = t - 1) (hL : 1 < L) (hLt : log t ≤ L + 1 / (t - 1)) :
    log t * (t / ((t - 1) ^ 2 - 1 / 2) * ((1 - q⁻¹) / (L / 2))) <
      2 * (t / (t - 1) ^ 2) := by
  have hq0 : 0 < q := by linarith only [hq1]
  have hq4 : 0 < q ^ 4 - 1 / 2 := by linarith only [one_lt_pow₀ hq1 (by decide : 4 ≠ 0)]
  have hL0 : 0 < L := by linarith only [hL]
  have hD : 0 < L * q * (q ^ 4 - 1 / 2) := by positivity
  have hy : (t - 1) ^ 2 = q ^ 4 := by rw [← hq2]; ring
  have e1 : log t * (t / ((t - 1) ^ 2 - 1 / 2) * ((1 - q⁻¹) / (L / 2))) =
      t * (2 * (log t * (q - 1)) / (L * q * (q ^ 4 - 1 / 2))) := by
    rw [hy]
    field_simp
  have e2 : 2 * (t / (t - 1) ^ 2) = t * (2 / q ^ 4) := by
    rw [hy]; ring
  rw [e1, e2]
  refine mul_lt_mul_of_pos_left ?_ ht0
  rw [div_lt_div_iff₀ hD (by positivity)]
  -- `log t (q-1) q⁴ < L q (q⁴ - 1/2)` using `log t ≤ L + 1/q²`
  have hLt' : log t ≤ L + 1 / q ^ 2 := by rwa [hq2]
  have h1 := mul_le_mul_of_nonneg_right hLt'
    (show 0 ≤ (q - 1) * q ^ 4 by have : 0 ≤ q - 1 := by linarith only [hq1]
                                 positivity)
  have h2 : (L + 1 / q ^ 2) * ((q - 1) * q ^ 4) = L * (q - 1) * q ^ 4 + (q - 1) * q ^ 2 := by
    field_simp
  have h3 : L * (q - 1) * q ^ 4 + (q - 1) * q ^ 2 < L * q * (q ^ 4 - 1 / 2) := by
    have hA : 0 < q ^ 4 - q / 2 := by
      have hcube := mul_lt_mul_of_pos_right (one_lt_pow₀ hq1 (by decide : 3 ≠ 0)) hq0
      nlinarith only [hcube, hq0]
    have hB' : 0 < q ^ 2 * q * (q - 1) + q * (q - 1 / 2) := by
      have : 0 < q - 1 := by linarith only [hq1]
      have : 0 < q - 1 / 2 := by linarith only [hq1]
      positivity
    nlinarith only [mul_lt_mul_of_pos_right hL hA, hB', hL, hA]
  nlinarith only [h1, h2, h3]

/-- The inequality behind [I71, Lemma 10]: `log t · 𝔐(t) < 2 t/(t-1)² · 𝔐(t-1)` for
`t ≥ 2`. -/
theorem log_mul_bigM_lt {t : ℝ} (ht : 2 ≤ t) :
    log t * bigM t < 2 * (t / (t - 1) ^ 2) * bigM (t - 1) := by
  refine sub_pos.1 <| pos_of_first_crossing
    (f := fun t => 2 * (t / (t - 1) ^ 2) * bigM (t - 1) - log t * bigM t) (a₀ := 2) (a := 2)
    ?_ ?_ ?_ ?_ t ht
  · refine ContinuousOn.sub (ContinuousOn.mul (continuousOn_const.mul
      (continuousOn_id.div ((continuousOn_id.sub continuousOn_const).pow 2) fun x hx => ?_))
      (continuous_bigM.comp (continuous_sub_right 1)).continuousOn)
      ((continuousOn_log.mono fun x hx => ?_).mul continuous_bigM.continuousOn)
    · have : 0 < x - 1 := by linarith only [hx.out, hx]
      positivity
    · simp only [mem_compl_iff, mem_singleton_iff]; linarith only [hx.out, hx]
  · intro x hx
    obtain rfl : x = 2 := le_antisymm hx.2 hx.1
    rw [show (2 : ℝ) - 1 = 1 by norm_num, bigM_of_le_two (by norm_num), bigM_two]
    linarith only [log_two_lt_d9]
  · rw [show (2 : ℝ) - 1 = 1 by norm_num, bigM_of_le_two (by norm_num), bigM_two]
    linarith only [log_two_lt_d9]
  intro t ht _ hpos
  show 0 < 2 * (t / (t - 1) ^ 2) * bigM (t - 1) - log t * bigM t
  rw [sub_pos]
  have ht0 : 0 < t := by linarith
  have hB := bigM_pos (t - 1)
  have hlog0 : 0 ≤ log t := log_nonneg (by linarith)
  rcases le_total t 3 with h3 | h3
  · -- explicit range `2 < t ≤ 3`
    rw [bigM_of_le_two (show t - 1 ≤ 2 by linarith only [h3])]
    have hl : log t < 1.3863 := (log_le_log ht0 (by linarith only [h3])).trans_lt log_four_lt
    have hk : 3 / 4 ≤ t / (t - 1) ^ 2 := by
      rw [le_div_iff₀ (by have : 0 < t - 1 := by linarith
                          positivity)]
      nlinarith
    have := bigM_le_three t
    nlinarith only [hl, hk, hlog0, this]
  rcases le_total t 4 with h4 | h4
  · -- crude range `3 ≤ t ≤ 4`, from `𝔐(t) ≤ t/((t-1)² - 1/2) 𝔐(t-1)`
    have hl : log t < 1.3863 := (log_le_log ht0 h4).trans_lt log_four_lt
    have hR := bigM_le_ratio h3
    have hy : 4 ≤ (t - 1) ^ 2 := by nlinarith
    have hr : 0 < (t - 1) ^ 2 - 1 / 2 := by linarith only [hy]
    have key : log t * (t / ((t - 1) ^ 2 - 1 / 2)) < 2 * (t / (t - 1) ^ 2) := by
      rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ hr (by linarith only [hy])]
      have : 1 < (2 - log t) * (t - 1) ^ 2 := by nlinarith only [hy, hl]
      nlinarith only [mul_lt_mul_of_pos_left this ht0, this, ht0]
    calc log t * bigM t ≤ log t * (t / ((t - 1) ^ 2 - 1 / 2) * bigM (t - 1)) :=
          mul_le_mul_of_nonneg_left hR hlog0
      _ = log t * (t / ((t - 1) ^ 2 - 1 / 2)) * bigM (t - 1) := by ring
      _ < 2 * (t / (t - 1) ^ 2) * bigM (t - 1) := mul_lt_mul_of_pos_right key hB
  -- main range `t > 4`
  set L₁ := log (t - 1) with hL₁
  set l := L₁ / 2 with hl
  have hL₁1 : 1 < L₁ := by
    rw [hL₁, lt_log_iff_exp_lt (by linarith only [h4])]
    linarith only [exp_one_lt_d9, h4]
  have hl0 : 0 < l := by linarith only [hl, hL₁1]
  -- `𝔐(x) ≤ 𝔐(t-1) exp(-l(x - (t-1)))` on `[t-1, t]`
  have hanti : AntitoneOn (fun x => bigM x * exp (l * x)) (Icc (t - 1) t) := by
    have hd : ∀ x, 3 < x → HasDerivAt (fun x => bigM x * exp (l * x))
        (-(x / (x - 1) ^ 2 * bigM (x - 1)) * exp (l * x) + bigM x * (exp (l * x) * l)) x :=
      fun x hx => (hasDerivAt_bigM hx).mul (((hasDerivAt_id x).const_mul l).exp.congr_deriv
        (by simp))
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (continuous_bigM.mul (continuous_const.mul continuous_id).rexp).continuousOn
      (fun x hx => ?_) (fun x hx => ?_) <;> rw [interior_Icc] at hx
    · exact (hd x (by linarith only [hx.1, h4, hx])).differentiableAt.differentiableWithinAt
    · rw [(hd x (by linarith only [hx.1, h4, hx])).deriv]
      have hfx := hpos x ⟨by linarith only [hx.1, h4, hx], hx.2⟩
      have hlx : L₁ ≤ log x := log_le_log (by linarith only [h4]) hx.1.le
      have hMx := bigM_pos x
      have : l * bigM x < x / (x - 1) ^ 2 * bigM (x - 1) := by nlinarith only [hfx, hl, hMx, hlx]
      have he := exp_pos (l * x)
      nlinarith only [this, he]
  have hbound : ∀ x ∈ Icc (t - 1) t,
      (1 - 1 / (2 * x ^ 2)) * bigM x ≤ bigM (t - 1) * exp (-(l * (x - (t - 1)))) := by
    intro x hx
    have h := hanti ⟨le_rfl, by linarith only []⟩ hx hx.1
    simp only at h
    have hw := weight_mem (x := x) (by linarith only [hx.1, h4, hx])
    have hMx := bigM_pos x
    have e : bigM (t - 1) * exp (-(l * (x - (t - 1)))) =
        bigM (t - 1) * exp (l * (t - 1)) / exp (l * x) := by
      rw [div_eq_mul_inv, ← exp_neg, mul_assoc, ← exp_add]; ring_nf
    rw [e, le_div_iff₀ (exp_pos _)]
    calc (1 - 1 / (2 * x ^ 2)) * bigM x * exp (l * x) ≤ 1 * bigM x * exp (l * x) := by
          gcongr; exact hw.2
      _ ≤ _ := by rw [one_mul]; exact h
  have hint : ((t - 1) ^ 2 - 1 / 2) * bigM t / t ≤ bigM (t - 1) * ((1 - exp (-l)) / l) := by
    rw [bigM_integral_identity h3, ← integral_exp_neg_mul_unit (t - 1) hl0.ne',
      sub_add_cancel, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith only [])
      ((continuousOn_weight_mul continuous_bigM (by linarith only [h4])).intervalIntegrable_of_Icc
        (by linarith only [])) ((by fun_prop : Continuous fun x =>
          bigM (t - 1) * exp (-(l * (x - (t - 1))))).intervalIntegrable _ _) hbound
  -- the numerical inequality, with `q = exp l = √(t-1)`
  set q := exp l with hq
  have hq2 : q ^ 2 = t - 1 := by
    rw [hq, sq, ← exp_add, show l + l = L₁ by rw [hl]; ring, hL₁, exp_log (by linarith only [h4])]
  have hq1 : 1 < q := one_lt_exp_iff.2 hl0
  have hel : exp (-l) = q⁻¹ := by rw [exp_neg]
  have hLt : log t ≤ L₁ + 1 / (t - 1) := by
    have := log_le_sub_one_of_pos (div_pos ht0 (by linarith only [h4] : (0 : ℝ) < t - 1))
    rw [log_div (by linarith) (by linarith)] at this
    have : t - 1 ≠ 0 := by linarith only [h4]
    have e : t / (t - 1) - 1 = 1 / (t - 1) := by field_simp; ring
    linarith
  rw [hel] at hint
  have hr : 0 < (t - 1) ^ 2 - 1 / 2 := by nlinarith
  have hMt : bigM t ≤ t / ((t - 1) ^ 2 - 1 / 2) * (bigM (t - 1) * ((1 - q⁻¹) / l)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    rw [div_le_iff₀ ht0] at hint
    linarith only [hint]
  have key := log_mul_ratio_lt ht0 hq1 hq2 hL₁1 hLt
  calc log t * bigM t ≤ log t * (t / ((t - 1) ^ 2 - 1 / 2) * (bigM (t - 1) * ((1 - q⁻¹) / l))) :=
        mul_le_mul_of_nonneg_left hMt hlog0
    _ = log t * (t / ((t - 1) ^ 2 - 1 / 2) * ((1 - q⁻¹) / l)) * bigM (t - 1) := by ring
    _ < 2 * (t / (t - 1) ^ 2) * bigM (t - 1) := mul_lt_mul_of_pos_right key hB

/-- [I71, Lemma 10]: `𝔐(t) t log t / 𝔐(t-1) < 9/2` for `t ≥ 3` (so it is `O(1)`). -/
theorem bigM_mul_log_div_lt {t : ℝ} (ht : 3 ≤ t) :
    bigM t * t * log t / bigM (t - 1) < 9 / 2 := by
  have h := log_mul_bigM_lt (t := t) (by linarith only [ht])
  have hB := bigM_pos (t - 1)
  have ht0 : 0 < t := by linarith only [ht]
  have hy : 0 < (t - 1) ^ 2 := by nlinarith only [ht]
  rw [div_lt_iff₀ hB]
  have h' : log t * bigM t * t ≤ 2 * (t / (t - 1) ^ 2) * bigM (t - 1) * t :=
    mul_le_mul_of_nonneg_right h.le ht0.le
  have hk : 2 * (t / (t - 1) ^ 2) * t ≤ 9 / 2 := by
    rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ hy]; nlinarith only [ht]
  nlinarith only [h, ht, hB, hk]

/-- Corollary to [I71, Lemma 10]: `G_{r+1}(t) (t-1)² log t / (G_r(t-1) t) < 4` for `t ≥ 2`
(and all `r`; [I71] states it for `t > (5 + (-1)^r)/2`). -/
theorem majG_succ_mul_log_div_lt (r : ℕ) {t : ℝ} (ht : 2 ≤ t) :
    majG (r + 1) t * (t - 1) ^ 2 * log t / (majG r (t - 1) * t) < 4 := by
  have h := log_mul_bigM_lt ht
  have ht0 : 0 < t := by linarith only [ht]
  have hy : 0 < (t - 1) ^ 2 := by nlinarith only [ht]
  have hlog : 0 ≤ log t := log_nonneg (by linarith only [ht])
  have hG := majG_mem (r + 1) t
  have hG' := majG_mem r (t - 1)
  have hGpos := majG_pos r (t - 1)
  rw [div_lt_iff₀ (mul_pos hGpos ht0)]
  have h1 : majG (r + 1) t * (t - 1) ^ 2 * log t ≤ 2 * bigM t / 3 * (t - 1) ^ 2 * log t :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hG.2 hy.le) hlog
  have h2 : log t * bigM t * (t - 1) ^ 2 < 2 * t * bigM (t - 1) := by
    have ht1 : t - 1 ≠ 0 := by linarith only [ht]
    have := mul_lt_mul_of_pos_right h hy
    rwa [show 2 * (t / (t - 1) ^ 2) * bigM (t - 1) * (t - 1) ^ 2 = 2 * t * bigM (t - 1) by
      field_simp] at this
  nlinarith only [hG', h1, h2, ht]

/-! ### Lemma 9 (lower bound) -/

/-- The comparison function `exp(-(s log s + s log log s + 2 s))` for [I71, Lemma 9]. -/
noncomputable def lemma9Fun (s : ℝ) : ℝ := exp (-(s * log s + s * log (log s) + 2 * s))

theorem continuousOn_lemma9Fun : ContinuousOn lemma9Fun (Ici 3) := by
  unfold lemma9Fun
  have hlog : ContinuousOn log (Ici 3) := continuousOn_log.mono fun x hx => by
    simp only [mem_compl_iff, mem_singleton_iff]; linarith only [hx.out, hx]
  have hloglog : ContinuousOn (fun x => log (log x)) (Ici 3) :=
    ContinuousOn.log hlog fun x hx => (log_pos (by linarith only [hx.out, hx])).ne'
  exact ((((continuousOn_id.mul hlog).add (continuousOn_id.mul hloglog)).add
    (continuousOn_const.mul continuousOn_id)).neg).rexp

theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ log x := by
  rw [le_log_iff_exp_le (by linarith only [hx])]
  linarith only [exp_one_lt_d9, hx]

theorem lemma9Fun_le_one {x : ℝ} (hx : 3 ≤ x) : lemma9Fun x ≤ 1 := by
  unfold lemma9Fun
  rw [exp_le_one_iff, neg_nonpos]
  have h1 := log_nonneg (one_le_log_of_three_le hx)
  have h2 := log_nonneg (show 1 ≤ x by linarith only [hx])
  have : 0 ≤ x := by linarith only [hx]
  positivity

/-- Convexity estimate: `φ(s) - φ(x) ≥ λ (s - x)` for `3 ≤ s - 1 ≤ x ≤ s`, where
`φ(s) = s log s + s log log s + 2s` and `λ = log(s-1) + log log(s-1) + 3`. -/
theorem lemma9_phi_sub {s x : ℝ} (hs : 4 ≤ s) (hx : s - 1 ≤ x) (hxs : x ≤ s) :
    (log (s - 1) + log (log (s - 1)) + 3) * (s - x) ≤
      (s * log s + s * log (log s) + 2 * s) - (x * log x + x * log (log x) + 2 * x) := by
  have hx0 : 0 < x := by linarith only [hs, hx]
  have hs0 : 0 < s := by linarith only [hs]
  -- `s log s - x log x ≥ (s - x)(1 + log x)`
  have h1 : (s - x) * (1 + log x) ≤ s * log s - x * log x := by
    have := log_le_sub_one_of_pos (div_pos hx0 hs0)
    rw [log_div hx0.ne' hs0.ne'] at this
    have e : s * (x / s - 1) = x - s := by field_simp
    nlinarith only [this, e, hs]
  have h2 : log (s - 1) ≤ log x := log_le_log (by linarith only [hs]) hx
  have hl1 : 1 ≤ log (s - 1) := one_le_log_of_three_le (by linarith only [hs])
  have h3 : log (log (s - 1)) ≤ log (log x) := log_le_log (by linarith only [hl1]) h2
  have h4 : log (log x) ≤ log (log s) := log_le_log (by
    linarith only [h2, hl1]) (log_le_log hx0 hxs)
  have h5 : 0 ≤ log (log (s - 1)) := log_nonneg hl1
  have hsx : 0 ≤ s - x := by linarith only [hxs]
  nlinarith [mul_le_mul_of_nonneg_left h2 hsx, mul_le_mul_of_nonneg_left h3 hsx,
    mul_le_mul_of_nonneg_left h4 hs0.le]

/-- On `[s-1, s]`, convexity of the exponent gives an exponential lower bound for the
weighted comparison function in (3.12). -/
theorem lemma9Fun_weighted_exp_le {s x : ℝ} (hs : 4 ≤ s) (hx : s - 1 ≤ x) (hxs : x ≤ s) :
    let l := log (s - 1) + log (log (s - 1)) + 3
    (1 - 1 / (2 * (s - 1) ^ 2)) * (lemma9Fun s * exp l) *
      exp (-(l * (x - (s - 1)))) ≤ (1 - 1 / (2 * x ^ 2)) * lemma9Fun x := by
  dsimp only
  set l := log (s - 1) + log (log (s - 1)) + 3
  have hweight : 1 - 1 / (2 * (s - 1) ^ 2) ≤ 1 - 1 / (2 * x ^ 2) := by
    have hrecip : 1 / (2 * x ^ 2) ≤ 1 / (2 * (s - 1) ^ 2) :=
      one_div_le_one_div_of_le (by nlinarith only [hs]) (by nlinarith only [hs, hx])
    linarith only [hrecip]
  have hexp : lemma9Fun s * exp l * exp (-(l * (x - (s - 1)))) ≤ lemma9Fun x := by
    unfold lemma9Fun
    rw [← exp_add, ← exp_add, exp_le_exp]
    have hconvex := lemma9_phi_sub hs hx hxs
    dsimp only [l]
    linarith only [hconvex]
  rw [mul_assoc]
  exact mul_le_mul hweight hexp (by unfold lemma9Fun; positivity)
    (weight_mem (by linarith only [hs, hx])).1.le

/-- The exponential lower bound, integrated and multiplied by the factor in (3.12),
has coefficient at least one. The key estimate is `l (s-1)² ≤ s (exp l - 1)`. -/
theorem lemma9_integral_factor_ge_one {s : ℝ} (hs : 4 ≤ s) :
    let l := log (s - 1) + log (log (s - 1)) + 3
    1 ≤ (1 - 1 / (2 * (s - 1) ^ 2)) * (exp l * ((1 - exp (-l)) / l)) *
      (s / ((s - 1) ^ 2 - 1 / 2)) := by
  dsimp only
  set L := log (s - 1) with hL
  set l := L + log L + 3 with hl
  set w₀ := 1 - 1 / (2 * (s - 1) ^ 2) with hw₀
  have hL1 : 1 ≤ L := one_le_log_of_three_le (by linarith only [hs])
  have hlogL : log L ≤ L - 1 := log_le_sub_one_of_pos (by linarith only [hL1])
  have hlogL0 : 0 ≤ log L := log_nonneg hL1
  have hl0 : 0 < l := by linarith only [hL1, hlogL0, hl]
  have hr : 0 < (s - 1) ^ 2 - 1 / 2 := by nlinarith only [hs]
  -- The numerical inequality `l (s-1)² ≤ s (exp l - 1)`.
  have hel : exp l = (s - 1) * L * exp 3 := by
    rw [hl, exp_add, exp_add, hL, exp_log (by linarith), exp_log (by linarith)]
  have he3 : 20 ≤ exp 3 := by
    have : exp 3 = exp 1 ^ 3 := by rw [← exp_nat_mul]; norm_num
    rw [this]
    have h := pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 3
    norm_num at h
    linarith only [this, h]
  have hexp_gain : l * (s - 1) ^ 2 ≤ s * (exp l - 1) := by
    rw [hel]
    have hy : 3 ≤ s - 1 := by linarith only [hs]
    have h0 : 0 ≤ (s - 1) * L := by positivity
    have : 20 * ((s - 1) * L) ≤ (s - 1) * L * exp 3 := by
      nlinarith only [mul_le_mul_of_nonneg_left he3 h0, he3, h0]
    nlinarith [mul_le_mul_of_nonneg_left hL1 (by nlinarith : (0 : ℝ) ≤ (s - 1) ^ 2)]
  have hexp_cancel : exp l * (1 - exp (-l)) = exp l - 1 := by
    rw [mul_sub, mul_one, ← exp_add]; simp
  have hweight_cancel : w₀ / ((s - 1) ^ 2 - 1 / 2) = 1 / (s - 1) ^ 2 := by
    have : s - 1 ≠ 0 := by linarith only [hs]
    rw [hw₀, div_eq_div_iff hr.ne' (by positivity)]
    field_simp
  have hfactor : w₀ * (exp l * ((1 - exp (-l)) / l)) * (s / ((s - 1) ^ 2 - 1 / 2)) =
      s * (exp l - 1) / (l * (s - 1) ^ 2) := by
    rw [← hexp_cancel]
    calc w₀ * (exp l * ((1 - exp (-l)) / l)) * (s / ((s - 1) ^ 2 - 1 / 2))
        = w₀ / ((s - 1) ^ 2 - 1 / 2) * (s * (exp l * (1 - exp (-l))) / l) := by ring
      _ = _ := by rw [hweight_cancel]; field_simp
  rw [hfactor, le_div_iff₀ (mul_pos hl0 (by nlinarith only [hr])), one_mul]
  exact hexp_gain

/-- `lemma9Fun` is a subsolution of (3.12) for `s ≥ 4`. -/
theorem lemma9Fun_le_integral {s : ℝ} (hs : 4 ≤ s) :
    lemma9Fun s ≤ s / ((s - 1) ^ 2 - 1 / 2) *
      ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * lemma9Fun x := by
  set l := log (s - 1) + log (log (s - 1)) + 3
  set w₀ := 1 - 1 / (2 * (s - 1) ^ 2)
  have hL1 : 1 ≤ log (s - 1) := one_le_log_of_three_le (by linarith only [hs])
  have hl0 : 0 < l := by
    dsimp only [l]
    linarith only [hL1, log_nonneg hL1]
  have hr : 0 < (s - 1) ^ 2 - 1 / 2 := by nlinarith only [hs]
  -- Integrate the pointwise exponential lower bound over `[s-1, s]`.
  have hint : w₀ * (lemma9Fun s * exp l) * ((1 - exp (-l)) / l) ≤
      ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * lemma9Fun x := by
    have hexp := integral_exp_neg_mul_unit (s - 1) hl0.ne'
    rw [sub_add_cancel] at hexp
    rw [← hexp, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith only)
      ((by fun_prop : Continuous fun x =>
        w₀ * (lemma9Fun s * exp l) * exp (-(l * (x - (s - 1))))).intervalIntegrable _ _)
      ?_ (fun x hx => lemma9Fun_weighted_exp_le hs hx.1 hx.2)
    refine ContinuousOn.intervalIntegrable_of_Icc (by linarith only) ?_
    refine ContinuousOn.mul (continuousOn_const.sub (continuousOn_const.div
      (continuousOn_const.mul (continuousOn_id.pow 2)) fun x hx => ?_))
      (continuousOn_lemma9Fun.mono fun x hx => by
        simp only [mem_Ici]; linarith only [hs, hx.1])
    have : 0 < x := by linarith only [hs, hx.1]
    positivity
  -- The integrated exponential has a large enough coefficient to recover `lemma9Fun s`.
  have hF : 0 < lemma9Fun s := exp_pos _
  calc
    lemma9Fun s ≤ lemma9Fun s * (w₀ * (exp l * ((1 - exp (-l)) / l)) *
        (s / ((s - 1) ^ 2 - 1 / 2))) :=
      le_mul_of_one_le_right hF.le (lemma9_integral_factor_ge_one hs)
    _ = s / ((s - 1) ^ 2 - 1 / 2) *
        (w₀ * (lemma9Fun s * exp l) * ((1 - exp (-l)) / l)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hint (div_nonneg (by linarith only [hs]) hr.le)

/-- Comparison of `𝔐` with the subsolution `lemma9Fun`: `𝔐(s) > (𝔐(4)/2) lemma9Fun(s)` for
`s ≥ 3`. -/
theorem bigM_gt_lemma9Fun {s : ℝ} (hs : 3 ≤ s) : bigM 4 / 2 * lemma9Fun s < bigM s := by
  set κ := bigM 4 / 2 with hκ
  have hM4 := bigM_pos 4
  have hinit : ∀ x ∈ Icc (3 : ℝ) 4, 0 < bigM x - κ * lemma9Fun x := by
    intro x hx
    have h1 := lemma9Fun_le_one hx.1
    have h2 : bigM 4 ≤ bigM x := bigM_antitone hx.2
    have h3 : κ * lemma9Fun x ≤ κ := by
      have : 0 ≤ κ := by positivity
      nlinarith only [hκ, h1, hM4]
    linarith only [hκ, hM4, h2, h3]
  rcases le_total s 4 with h4 | h4
  · exact sub_pos.1 (hinit s ⟨hs, h4⟩)
  refine sub_pos.1 <| pos_of_first_crossing (f := fun s => bigM s - κ * lemma9Fun s) (a₀ := 3)
    (a := 4) (continuous_bigM.continuousOn.sub (continuousOn_const.mul
      (continuousOn_lemma9Fun.mono fun x hx => by simp only [mem_Ici] at hx ⊢; linarith only [hx])))
    (fun x hx => (hinit x hx).le) (hinit 4 ⟨by norm_num, le_rfl⟩) ?_ s h4
  intro t ht hall hpos
  show 0 < bigM t - κ * lemma9Fun t
  have hpos' : ∀ x ∈ Ioo (t - 1) t, 0 < bigM x - κ * lemma9Fun x := by
    intro x hx
    rcases le_total x 4 with h | h
    · exact hinit x ⟨by linarith only [hx.1, ht, hx], h⟩
    · exact hpos x ⟨h, hx.2⟩
  have ht0 : 0 < t := by linarith only [ht]
  have hr : 0 < (t - 1) ^ 2 - 1 / 2 := by nlinarith only [ht]
  have hcw : ContinuousOn (fun x => (1 - 1 / (2 * x ^ 2)) * (κ * lemma9Fun x)) (Icc (t - 1) t) := by
    refine ContinuousOn.mul (continuousOn_const.sub (continuousOn_const.div
      (continuousOn_const.mul (continuousOn_id.pow 2)) fun x hx => ?_))
      (continuousOn_const.mul (continuousOn_lemma9Fun.mono fun x hx => by
        simp only [mem_Ici]; linarith only [hx.1, ht, hx]))
    have : 0 < x := by linarith only [hx.1, ht, hx]
    positivity
  have hlt : ∫ x in (t - 1)..t, (1 - 1 / (2 * x ^ 2)) * (κ * lemma9Fun x) <
      ∫ x in (t - 1)..t, (1 - 1 / (2 * x ^ 2)) * bigM x := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by linarith) hcw (continuousOn_weight_mul continuous_bigM (by linarith)) ?_ ?_
    · intro x hx
      have hw := (weight_mem (x := x) (by linarith only [hx.1, ht, hx])).1
      rcases hx.2.lt_or_eq with h | rfl
      · exact mul_le_mul_of_nonneg_left (sub_pos.1 (hpos' x ⟨hx.1, h⟩)).le hw.le
      · exact mul_le_mul_of_nonneg_left (sub_nonneg.1 (hall x ⟨by
        linarith only [ht], le_rfl⟩)) hw.le
    · refine ⟨t - 1 / 2, ⟨by linarith, by linarith⟩, ?_⟩
      exact mul_lt_mul_of_pos_left (sub_pos.1 (hpos' _ ⟨by linarith, by linarith⟩))
        (weight_mem (by linarith only [ht])).1
  rw [← bigM_integral_identity (by linarith only [ht]), intervalIntegral.integral_congr
    (g := fun x => κ * ((1 - 1 / (2 * x ^ 2)) * lemma9Fun x)) (fun x _ => by simp only; ring),
    intervalIntegral.integral_const_mul] at hlt
  have hsub := lemma9Fun_le_integral ht.le
  have hκ0 : 0 < κ := by positivity
  have h1 : κ * lemma9Fun t ≤
      t / ((t - 1) ^ 2 - 1 / 2) * (κ * ∫ x in (t - 1)..t, (1 - 1 / (2 * x ^ 2)) * lemma9Fun x) := by
    calc κ * lemma9Fun t ≤ κ * (t / ((t - 1) ^ 2 - 1 / 2) *
          ∫ x in (t - 1)..t, (1 - 1 / (2 * x ^ 2)) * lemma9Fun x) :=
          mul_le_mul_of_nonneg_left hsub hκ0.le
      _ = _ := by ring
  have h2 := mul_lt_mul_of_pos_left hlt (div_pos ht0 hr)
  have e : t / ((t - 1) ^ 2 - 1 / 2) * (((t - 1) ^ 2 - 1 / 2) * bigM t / t) = bigM t := by
    generalize (t - 1) ^ 2 - 1 / 2 = r at hr ⊢
    field_simp
  rw [e] at h2
  linarith only [h1, h2]

/-- [I71, Lemma 9], lower bound for `𝔐`: there is `κ > 0` with
`𝔐(s) ≥ κ exp(-(s log s + s log log s + 2 s))` for `s ≥ 3`. -/
theorem bigM_ge_exp : ∃ κ > 0, ∀ s ≥ 3,
    κ * exp (-(s * log s + s * log (log s) + 2 * s)) ≤ bigM s :=
  ⟨bigM 4 / 2, by linarith only [bigM_pos 4], fun _ hs => (bigM_gt_lemma9Fun hs).le⟩

/-- [I71, Lemma 9], lower bound: there is `c` with
`G_r(s) ≥ exp(-s log s - s log log s - c s)` for all `r` and `s ≥ 3`. -/
theorem majG_ge_exp : ∃ c : ℝ, ∀ (r : ℕ) (s : ℝ), 3 ≤ s →
    exp (-(s * log s) - s * log (log s) - c * s) ≤ majG r s := by
  obtain ⟨κ, hκ, hM⟩ := bigM_ge_exp
  set K := |log (κ / 3)| / 3 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 + K, fun r s hs => ?_⟩
  have hG := (majG_mem r s).1
  have h1 := hM s hs
  have hexp : exp (-(K * s)) ≤ κ / 3 := by
    calc exp (-(K * s)) ≤ exp (log (κ / 3)) := by
          rw [exp_le_exp]
          have : -log (κ / 3) ≤ |log (κ / 3)| := neg_le_abs _
          nlinarith only [hK, this, hK0, hs]
      _ = κ / 3 := exp_log (by positivity)
  have e : exp (-(s * log s) - s * log (log s) - (2 + K) * s) =
      exp (-(K * s)) * exp (-(s * log s + s * log (log s) + 2 * s)) := by
    rw [← exp_add]; ring_nf
  rw [e]
  calc exp (-(K * s)) * exp (-(s * log s + s * log (log s) + 2 * s))
      ≤ κ / 3 * exp (-(s * log s + s * log (log s) + 2 * s)) :=
        mul_le_mul_of_nonneg_right hexp (exp_pos _).le
    _ ≤ bigM s / 3 := by linarith only [h1]
    _ ≤ majG r s := hG

end IwaniecLinearSieve
