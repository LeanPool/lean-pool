/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.SieveMajorants.Defs
import LeanPool.IwaniecLinearSieve.SieveMajorants.Delay
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev

/-!
# Basic properties of `𝔐`, `𝔚` ([I71, §3])

`0 < 𝔐`, `𝔐` antitone, `𝔐 = O(e^{-s})`, and [I71, Lemma 6] `|𝔚| ≤ 𝔐/3`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace IwaniecLinearSieve

/-- On `(-∞, 3]`, `-1/2 ≤ 𝔚 ≤ 1`. -/
theorem initW_mem {s : ℝ} (hs : s ≤ 3) : -(1 / 2) ≤ initW s ∧ initW s ≤ 1 := by
  unfold initW
  set y := max s 2 - 1 with hy
  have hy1 : 1 ≤ y := by have := le_max_right s 2; linarith
  have hy2 : y ≤ 2 := by have : max s 2 ≤ 3 := max_le hs (by norm_num); linarith
  have hlog0 : 0 ≤ log y := log_nonneg hy1
  have hlog1 : log y ≤ y - 1 := log_le_sub_one_of_pos (by linarith)
  have h1 : 1 / y ≤ 1 := by rw [div_le_one (by linarith)]; exact hy1
  have h2 : 1 / 2 ≤ 1 / y := one_div_le_one_div_of_le (by linarith) hy2
  constructor <;> linarith

theorem bigM_pos_of_le_three {s : ℝ} (hs : s ≤ 3) : 0 < bigM s := by
  rw [bigM_of_le_three hs]; linarith [(initW_mem hs).1]

theorem abs_bigW_le_of_le_three {s : ℝ} (hs : s ≤ 3) : |bigW s| ≤ bigM s / 3 := by
  rw [bigW_of_le_three hs, bigM_of_le_three hs, abs_le]
  obtain ⟨h1, h2⟩ := initW_mem hs
  constructor <;> linarith

/-- The weight `1 - 1/(2x²)` of (3.12) is in `(0, 1]` for `x ≥ 1`. -/
theorem weight_mem {x : ℝ} (hx : 1 ≤ x) : 0 < 1 - 1 / (2 * x ^ 2) ∧ 1 - 1 / (2 * x ^ 2) ≤ 1 := by
  have : 1 / (2 * x ^ 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have : 0 < 1 / (2 * x ^ 2) := by positivity
  constructor <;> linarith

theorem continuousOn_weight_mul {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x => (1 - 1 / (2 * x ^ 2)) * g x) (Icc a b) := by
  refine ContinuousOn.mul ?_ hg.continuousOn
  refine continuousOn_const.sub (continuousOn_const.div (continuousOn_const.mul
    (continuousOn_id.pow 2)) fun x hx => ?_)
  have : 0 < x := lt_of_lt_of_le ha hx.1
  positivity

/-- `0 < 𝔐` [I71, after (3.12)]. -/
theorem bigM_pos (s : ℝ) : 0 < bigM s := by
  rcases le_total s 3 with hs | hs
  · exact bigM_pos_of_le_three hs
  refine pos_of_first_crossing (f := bigM) (a₀ := 3) (a := 3) continuous_bigM.continuousOn
    (fun x hx => (bigM_pos_of_le_three hx.2).le) (bigM_pos_of_le_three le_rfl) ?_ s hs
  intro t ht _ hpos
  have hpos' : ∀ x, x < t → 0 < bigM x := fun x hx => by
    rcases le_total x 3 with h | h
    · exact bigM_pos_of_le_three h
    · exact hpos x ⟨h, hx⟩
  have hI : 0 < ∫ x in (t - 1)..t, (1 - 1 / (2 * x ^ 2)) * bigM x := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => ?_) (by linarith)
    · exact (continuousOn_weight_mul continuous_bigM (by linarith)).intervalIntegrable_of_Icc
        (by linarith)
    · exact mul_pos (weight_mem (by linarith [hx.1])).1 (hpos' x hx.2)
  rw [← bigM_integral_identity ht.le] at hI
  have hr : 0 < (t - 1) ^ 2 - 1 / 2 := by nlinarith
  have ht0 : 0 < t := by linarith
  by_contra h
  push Not at h
  have : ((t - 1) ^ 2 - 1 / 2) * bigM t / t ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hr.le h) ht0.le
  linarith

/-- An antitone function on `(-∞, a]` and on `[a, ∞)` is antitone. -/
theorem antitone_of_antitoneOn_Iic_Ici {f : ℝ → ℝ} {a : ℝ} (h₁ : AntitoneOn f (Iic a))
    (h₂ : AntitoneOn f (Ici a)) : Antitone f := by
  intro s t hst
  rcases le_total t a with hta | hta
  · exact h₁ (hst.trans hta) hta hst
  rcases le_total a s with has | has
  · exact h₂ has hta hst
  exact (h₂ (le_refl a) hta hta).trans (h₁ has (le_refl a) has)

theorem antitoneOn_initW : AntitoneOn initW (Iic 3) := by
  intro s _ t _ hst
  unfold initW
  have h1 : 1 ≤ max s 2 - 1 := by have := le_max_right s 2; linarith
  have h2 : max s 2 ≤ max t 2 := max_le_max hst le_rfl
  have h3 : log (max s 2 - 1) ≤ log (max t 2 - 1) := log_le_log (by linarith) (by linarith)
  have h4 : 1 / (max t 2 - 1) ≤ 1 / (max s 2 - 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  linarith

theorem continuousOn_kernel_mul {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (fun x => x / (x - 1) ^ 2 * g (x - 1)) (Ici 2) := by
  refine ContinuousOn.mul (continuousOn_id.div ((continuousOn_id.sub continuousOn_const).pow 2)
    fun x hx => ?_) (hg.comp (continuous_sub_right 1)).continuousOn
  have : (2 : ℝ) ≤ x := hx
  have : 0 < x - 1 := by linarith
  positivity

theorem intervalIntegrable_kernel_mul {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (ha : 2 ≤ a)
    (hb : 2 ≤ b) : IntervalIntegrable (fun x => x / (x - 1) ^ 2 * g (x - 1)) volume a b := by
  refine ((continuousOn_kernel_mul hg).mono fun x hx => ?_).intervalIntegrable
  rcases le_total a b with h | h
  · rw [uIcc_of_le h] at hx; exact ha.trans hx.1
  · rw [uIcc_of_ge h] at hx; exact hb.trans hx.1

theorem kernel_pos {x : ℝ} (hx : 1 < x) : 0 < x / (x - 1) ^ 2 := by
  have : 0 < x - 1 := by linarith
  positivity

/-- `𝔐` is antitone (on all of `ℝ`). -/
theorem bigM_antitone : Antitone bigM := by
  refine antitone_of_antitoneOn_Iic_Ici (a := 3) ?_ ?_
  · intro s hs t ht hst
    rw [bigM_of_le_three hs, bigM_of_le_three ht]
    linarith [antitoneOn_initW hs ht hst]
  · intro s hs t ht hst
    have hs' : (3 : ℝ) ≤ s := hs
    have ht' : (3 : ℝ) ≤ t := ht
    rw [bigM_eq_integral hs', bigM_eq_integral ht',
      ← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_kernel_mul continuous_bigM (by norm_num) (b := s) (by linarith))
        (intervalIntegrable_kernel_mul continuous_bigM (by linarith) (by linarith))]
    have : 0 ≤ ∫ x in s..t, x / (x - 1) ^ 2 * bigM (x - 1) :=
      intervalIntegral.integral_nonneg hst fun x hx =>
        (mul_pos (kernel_pos (by linarith [hx.1])) (bigM_pos _)).le
    linarith

theorem bigM_le_three (s : ℝ) : bigM s ≤ 3 := by
  rcases le_total s 2 with h | h
  · rw [bigM_of_le_two h]
  · exact (bigM_antitone h).trans_eq bigM_two

/-- From (3.12) and monotonicity: `𝔐(s) ≤ s/((s-1)² - 1/2) 𝔐(s-1)` for `s ≥ 3`. -/
theorem bigM_le_ratio {s : ℝ} (hs : 3 ≤ s) :
    bigM s ≤ s / ((s - 1) ^ 2 - 1 / 2) * bigM (s - 1) := by
  have hr : 0 < (s - 1) ^ 2 - 1 / 2 := by nlinarith
  have hs0 : 0 < s := by linarith
  have h := bigM_integral_identity hs
  have hle : ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * bigM x ≤
      ∫ _ in (s - 1)..s, bigM (s - 1) := by
    refine intervalIntegral.integral_mono_on (by linarith)
      ((continuousOn_weight_mul continuous_bigM (by linarith)).intervalIntegrable_of_Icc
        (by linarith)) intervalIntegrable_const fun x hx => ?_
    obtain ⟨h0, h1⟩ := weight_mem (x := x) (by linarith [hx.1])
    calc (1 - 1 / (2 * x ^ 2)) * bigM x ≤ 1 * bigM x :=
          mul_le_mul_of_nonneg_right h1 (bigM_pos x).le
      _ ≤ bigM (s - 1) := by rw [one_mul]; exact bigM_antitone hx.1
  rw [intervalIntegral.integral_const, ← h] at hle
  simp only [sub_sub_cancel, smul_eq_mul, one_mul] at hle
  rw [div_mul_eq_mul_div, le_div_iff₀ hr]
  rw [div_le_iff₀ hs0] at hle
  linarith

/-- `𝔐(s) = O(e^{-s})`. -/
theorem bigM_le_exp (s : ℝ) : bigM s ≤ 3 * exp 5 * exp (-s) := by
  have base : ∀ s : ℝ, s ≤ 5 → bigM s ≤ 3 * exp 5 * exp (-s) := by
    intro s hs
    have : 1 ≤ exp 5 * exp (-s) := by
      rw [← exp_add]; exact one_le_exp (by linarith)
    nlinarith [bigM_le_three s]
  have key : ∀ n : ℕ, ∀ s : ℝ, s ≤ n → bigM s ≤ 3 * exp 5 * exp (-s) := by
    intro n
    induction n with
    | zero => intro s hs; exact base s (by simp at hs; linarith)
    | succ n ih =>
      intro s hs
      rcases le_total s 5 with h5 | h5
      · exact base s h5
      have h1 := bigM_le_ratio (s := s) (by linarith)
      have h2 := ih (s - 1) (by push_cast at hs; linarith)
      have hr : 0 < (s - 1) ^ 2 - 1 / 2 := by nlinarith
      have hc : s / ((s - 1) ^ 2 - 1 / 2) ≤ exp (-1) := by
        rw [div_le_iff₀ hr, exp_neg, ← div_eq_inv_mul, le_div_iff₀ (exp_pos 1)]
        nlinarith [exp_one_lt_d9]
      calc bigM s ≤ s / ((s - 1) ^ 2 - 1 / 2) * bigM (s - 1) := h1
        _ ≤ exp (-1) * (3 * exp 5 * exp (-(s - 1))) :=
          mul_le_mul hc h2 (bigM_pos _).le (exp_pos _).le
        _ = 3 * exp 5 * exp (-s) := by
          rw [show -s = -1 + -(s - 1) by ring, exp_add]; ring
  exact key ⌈s⌉₊ s (Nat.le_ceil s)

theorem tendsto_bigM_atTop : Tendsto bigM atTop (𝓝 0) := by
  have h : Tendsto (fun s => 3 * exp 5 * exp (-s)) atTop (𝓝 0) := by
    simpa using tendsto_exp_neg_atTop_nhds_zero.const_mul (3 * exp 5)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun s => (bigM_pos s).le) bigM_le_exp

theorem lemma6_aux {r x M : ℝ} (hr : r ≠ 0) (hx : x ≠ 0) :
    1 / (3 * r) * ((1 - 1 / (2 * x ^ 2)) * M) - M / 3 / x ^ 2 =
      M * (x ^ 2 - 1 / 2 - r) / (3 * r * x ^ 2) := by
  field_simp

/-- [I71, Lemma 6], strict form for `s ≥ 3`: `|𝔚(s)| < 𝔐(s)/3`. -/
theorem abs_bigW_lt {s : ℝ} (hs : 3 ≤ s) : |bigW s| < bigM s / 3 := by
  refine sub_pos.1 <| pos_of_first_crossing (f := fun s => bigM s / 3 - |bigW s|) (a₀ := 2)
    (a := 3) ((continuous_bigM.div_const 3).sub continuous_bigW.abs).continuousOn
    (fun x hx => sub_nonneg.2 (abs_bigW_le_of_le_three hx.2)) ?_ ?_ s hs
  · rw [bigM_three, bigW_three, abs_of_neg (by linarith [log_two_gt_d9])]
    linarith [log_two_lt_d9]
  intro t ht hall _
  have ht0 : 0 < t := by linarith
  have hr : 0 < (t - 1) ^ 2 - 1 / 2 := by nlinarith
  have hx0 : ∀ x ∈ Icc (t - 1) t, x ^ 2 ≠ 0 := fun x hx =>
    pow_ne_zero 2 (by linarith [hx.1])
  have hcW : ContinuousOn (fun x => |bigW x / x ^ 2|) (Icc (t - 1) t) :=
    (continuous_bigW.continuousOn.div (continuousOn_id.pow 2) hx0).abs
  have hcM : ContinuousOn (fun x => bigM x / 3 / x ^ 2) (Icc (t - 1) t) :=
    (continuous_bigM.div_const 3).continuousOn.div (continuousOn_id.pow 2) hx0
  have hcM' : ContinuousOn (fun x => 1 / (3 * ((t - 1) ^ 2 - 1 / 2)) *
      ((1 - 1 / (2 * x ^ 2)) * bigM x)) (Icc (t - 1) t) :=
    continuousOn_const.mul (continuousOn_weight_mul continuous_bigM (by linarith))
  have h1 : |bigW t| ≤ t * ∫ x in (t - 1)..t, |bigW x / x ^ 2| := by
    rw [bigW_eq_neg_mul_integral ht.le, abs_mul, abs_neg, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (intervalIntegral.abs_integral_le_integral_abs
      (by linarith)) ht0.le
  have h2 : ∫ x in (t - 1)..t, |bigW x / x ^ 2| ≤ ∫ x in (t - 1)..t, bigM x / 3 / x ^ 2 := by
    refine intervalIntegral.integral_mono_on (by linarith) (hcW.intervalIntegrable_of_Icc
      (by linarith)) (hcM.intervalIntegrable_of_Icc (by linarith)) fun x hx => ?_
    have hx2 : 0 < x ^ 2 := pow_pos (by linarith [hx.1]) 2
    rw [abs_div, abs_of_pos hx2]
    have := hall x ⟨by linarith [hx.1], hx.2⟩
    exact div_le_div_of_nonneg_right (by linarith) hx2.le
  have hpt : ∀ x, t - 1 < x → 0 < 1 / (3 * ((t - 1) ^ 2 - 1 / 2)) *
      ((1 - 1 / (2 * x ^ 2)) * bigM x) - bigM x / 3 / x ^ 2 := by
    intro x hx
    have hx' : 0 < x := by linarith
    rw [lemma6_aux hr.ne' hx'.ne']
    have : 0 < x ^ 2 - 1 / 2 - ((t - 1) ^ 2 - 1 / 2) := by nlinarith
    have := bigM_pos x
    positivity
  have h3 : ∫ x in (t - 1)..t, bigM x / 3 / x ^ 2 < ∫ x in (t - 1)..t,
      1 / (3 * ((t - 1) ^ 2 - 1 / 2)) * ((1 - 1 / (2 * x ^ 2)) * bigM x) := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by linarith) hcM hcM' (fun x hx => (sub_pos.1 (hpt x hx.1)).le)
      ⟨t, ⟨by linarith, le_rfl⟩, sub_pos.1 (hpt t (by linarith))⟩
  rw [intervalIntegral.integral_const_mul, ← bigM_integral_identity ht.le] at h3
  have h4 : t * (1 / (3 * ((t - 1) ^ 2 - 1 / 2)) * (((t - 1) ^ 2 - 1 / 2) * bigM t / t)) =
      bigM t / 3 := by
    generalize (t - 1) ^ 2 - 1 / 2 = r at hr ⊢
    field_simp
  have := mul_lt_mul_of_pos_left h3 ht0
  rw [h4] at this
  have := mul_le_mul_of_nonneg_left h2 ht0.le
  linarith

/-- [I71, Lemma 6]: `|𝔚(s)| ≤ 𝔐(s)/3` (for all `s`; [I71] states it for `s ≥ 2`). -/
theorem abs_bigW_le (s : ℝ) : |bigW s| ≤ bigM s / 3 := by
  rcases le_total s 3 with hs | hs
  · exact abs_bigW_le_of_le_three hs
  · exact (abs_bigW_lt hs).le

/-- `𝔚(s) = O(e^{-s})`. -/
theorem abs_bigW_le_exp (s : ℝ) : |bigW s| ≤ exp 5 * exp (-s) := by
  have := bigM_le_exp s
  linarith [abs_bigW_le s]

end IwaniecLinearSieve
