/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.Definitions
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import LeanPool.IwaniecLinearSieve.SieveMajorants.Delay
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.NumberTheory.Chebyshev

/-!
# Iwaniec's functions `𝔐`, `𝔚` ([I71, §3, Definition])

* `𝔚(s) = 1/(s-1) - log(s-1)` on `[2, 3]`, `𝔚'(s) = s/(s-1)² 𝔚(s-1)` for `s > 3`;
* `𝔐(s) = 2 + 1/(s-1) - log(s-1)` on `[2, 3]`, `𝔐'(s) = -s/(s-1)² 𝔐(s-1)` for `s > 3`.

Both are defined on all of `ℝ` (`𝔐` in `IwaniecLinearSieve.Definitions`) and are continuous; to
the left of `2` they are constant
(`𝔚 = 1`, `𝔐 = 3`). We prove the integral equations (3.11) and (3.12) of [I71].
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace IwaniecLinearSieve

/-- Iwaniec's `𝔚` [I71, §3, Definition]. -/
noncomputable def bigW : ℝ → ℝ := Delay.sol delayKer initW

theorem delayKer_of_ge {x : ℝ} (hx : 3 ≤ x) : delayKer x = x / (x - 1) ^ 2 := by
  simp [delayKer, max_eq_left hx]

theorem continuous_delayKer : Continuous delayKer := by
  unfold delayKer
  refine (continuous_id.max continuous_const).div
    (((continuous_id.max continuous_const).sub continuous_const).pow 2) fun x => ?_
  have : (3 : ℝ) ≤ max x 3 := le_max_right _ _
  have : (0 : ℝ) < max x 3 - 1 := by linarith
  positivity

theorem continuous_initW : Continuous initW := by
  unfold initW
  have h1 : Continuous fun s : ℝ => max s 2 - 1 :=
    (continuous_id.max continuous_const).sub continuous_const
  have hne : ∀ s : ℝ, max s 2 - 1 ≠ 0 := fun s => by
    have : (2 : ℝ) ≤ max s 2 := le_max_right _ _
    linarith
  exact (continuous_const.div h1 hne).sub (h1.log hne)

theorem initW_of_le {s : ℝ} (hs : s ≤ 2) : initW s = 1 := by
  simp [initW, max_eq_right hs]
  norm_num

theorem initW_of_ge {s : ℝ} (hs : 2 ≤ s) : initW s = 1 / (s - 1) - log (s - 1) := by
  simp [initW, max_eq_left hs]

theorem continuous_bigW : Continuous bigW :=
  Delay.continuous_sol continuous_delayKer continuous_initW

theorem continuous_initM : Continuous fun s => 2 + initW s :=
  continuous_const.add continuous_initW

theorem continuous_bigM : Continuous bigM :=
  Delay.continuous_sol continuous_delayKer.neg continuous_initM

theorem bigW_of_le_three {s : ℝ} (hs : s ≤ 3) : bigW s = initW s :=
  Delay.sol_of_le hs

theorem bigM_of_le_three {s : ℝ} (hs : s ≤ 3) : bigM s = 2 + initW s :=
  Delay.sol_of_le hs

theorem bigW_of_le_two {s : ℝ} (hs : s ≤ 2) : bigW s = 1 := by
  rw [bigW_of_le_three (by linarith), initW_of_le hs]

theorem bigM_of_le_two {s : ℝ} (hs : s ≤ 2) : bigM s = 3 := by
  rw [bigM_of_le_three (by linarith), initW_of_le hs]; norm_num

theorem bigW_eq {s : ℝ} (hs : 2 ≤ s) (hs' : s ≤ 3) : bigW s = 1 / (s - 1) - log (s - 1) := by
  rw [bigW_of_le_three hs', initW_of_ge hs]

theorem bigM_eq {s : ℝ} (hs : 2 ≤ s) (hs' : s ≤ 3) :
    bigM s = 2 + 1 / (s - 1) - log (s - 1) := by
  rw [bigM_of_le_three hs', initW_of_ge hs]; ring

theorem bigW_two : bigW 2 = 1 := bigW_of_le_two le_rfl

theorem bigM_two : bigM 2 = 3 := bigM_of_le_two le_rfl

theorem bigW_three : bigW 3 = 1 / 2 - log 2 := by
  rw [bigW_eq (by norm_num) le_rfl]; norm_num

theorem bigM_three : bigM 3 = 5 / 2 - log 2 := by
  rw [bigM_eq (by norm_num) le_rfl]; norm_num

/-- The derivative of `1/(x-1) - log(x-1)` is `-x/(x-1)²`. -/
theorem hasDerivAt_initForm {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x => 1 / (x - 1) - log (x - 1)) (-(x / (x - 1) ^ 2)) x := by
  have h0 : x - 1 ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 x := (hasDerivAt_id x).sub_const 1
  have := (h1.inv h0).sub (h1.log h0)
  convert this using 1
  · ext y; simp [one_div]
  · field_simp; ring

theorem bigW_eq_integral {s : ℝ} (hs : 3 ≤ s) :
    bigW s = bigW 3 + ∫ x in (3 : ℝ)..s, x / (x - 1) ^ 2 * bigW (x - 1) := by
  rw [bigW, Delay.sol_of_ge hs, ← bigW, bigW_of_le_three le_rfl]
  congr 1
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hs] at hx
  simp only [delayKer_of_ge hx.1, bigW]

theorem bigM_eq_integral {s : ℝ} (hs : 3 ≤ s) :
    bigM s = bigM 3 - ∫ x in (3 : ℝ)..s, x / (x - 1) ^ 2 * bigM (x - 1) := by
  rw [bigM, Delay.sol_of_ge hs, ← bigM, bigM_of_le_three le_rfl, sub_eq_add_neg,
    ← intervalIntegral.integral_neg]
  congr 1
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hs] at hx
  simp only [delayKer_of_ge hx.1, bigM, neg_mul]

theorem hasDerivAt_bigW {s : ℝ} (hs : 3 < s) :
    HasDerivAt bigW (s / (s - 1) ^ 2 * bigW (s - 1)) s := by
  have := Delay.hasDerivAt_sol continuous_delayKer continuous_initW hs
  rwa [delayKer_of_ge hs.le] at this

theorem hasDerivAt_bigM {s : ℝ} (hs : 3 < s) :
    HasDerivAt bigM (-(s / (s - 1) ^ 2 * bigM (s - 1))) s := by
  have := Delay.hasDerivAt_sol continuous_delayKer.neg
    continuous_initM hs
  rwa [Pi.neg_apply, delayKer_of_ge hs.le, neg_mul] at this

theorem hasDerivWithinAt_bigW_Ici {s : ℝ} (hs : 3 ≤ s) :
    HasDerivWithinAt bigW (s / (s - 1) ^ 2 * bigW (s - 1)) (Ici s) s := by
  have := Delay.hasDerivWithinAt_sol_Ici continuous_delayKer continuous_initW hs
  rwa [delayKer_of_ge hs] at this

theorem hasDerivWithinAt_bigM_Ici {s : ℝ} (hs : 3 ≤ s) :
    HasDerivWithinAt bigM (-(s / (s - 1) ^ 2 * bigM (s - 1))) (Ici s) s := by
  have := Delay.hasDerivWithinAt_sol_Ici continuous_delayKer.neg
    continuous_initM hs
  rwa [Pi.neg_apply, delayKer_of_ge hs, neg_mul] at this

/-! ### Auxiliary calculus -/

/-- `t ↦ ∫_{t-1}^t F` has derivative `F t - F (t - 1)`. -/
theorem hasDerivAt_integral_unit {F : ℝ → ℝ} (hF : Continuous F) (t : ℝ) :
    HasDerivAt (fun t => ∫ x in (t - 1)..t, F x) (F t - F (t - 1)) t := by
  have hI : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hF.intervalIntegrable a b
  have heq : (fun t => ∫ x in (t - 1)..t, F x) =
      fun t => (∫ x in (0 : ℝ)..t, F x) - ∫ x in (0 : ℝ)..(t - 1), F x := by
    ext t
    rw [intervalIntegral.integral_interval_sub_left (hI 0 t) (hI 0 (t - 1))]
  rw [heq]
  have h1 := (hF.integral_hasStrictDerivAt 0 t).hasDerivAt
  have h2 := ((hF.integral_hasStrictDerivAt 0 (t - 1)).hasDerivAt).comp t
    ((hasDerivAt_id t).sub_const 1)
  convert h1.sub h2 using 1
  · funext x; simp [Function.comp_def]
  · ring

/-- A function continuous on `[a, ∞)` with zero derivative on `(a, ∞)` is constant there. -/
theorem eq_of_hasDerivAt_zero {g : ℝ → ℝ} {a : ℝ} (hg : ContinuousOn g (Ici a))
    (hd : ∀ x, a < x → HasDerivAt g 0 x) {s : ℝ} (hs : a ≤ s) : g s = g a := by
  rcases hs.eq_or_lt with rfl | hs
  · rfl
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope g (fun _ => (0 : ℝ)) hs
    (hg.mono Icc_subset_Ici_self) fun x hx => hd x hx.1
  have : s - a ≠ 0 := by linarith
  field_simp at hc'
  linarith

/-! ### (3.11) -/

/-- The integrand of (3.11), made continuous on `ℝ`. -/
noncomputable def wIntegrand (x : ℝ) : ℝ := bigW x / max x 1 ^ 2

theorem continuous_wIntegrand : Continuous wIntegrand := by
  unfold wIntegrand
  refine continuous_bigW.div ((continuous_id.max continuous_const).pow 2) fun x => ?_
  have : (1 : ℝ) ≤ max x 1 := le_max_right _ _
  positivity

theorem wIntegrand_of_ge {x : ℝ} (hx : 1 ≤ x) : wIntegrand x = bigW x / x ^ 2 := by
  simp [wIntegrand, max_eq_left hx]

theorem integral_wIntegrand_two_three :
    ∫ x in (2 : ℝ)..3, wIntegrand x = (1 + log 2) / 3 - 1 / 2 := by
  have hcongr : ∫ x in (2 : ℝ)..3, wIntegrand x =
      ∫ x in (2 : ℝ)..3, (1 / (x - 1) - log (x - 1)) / x ^ 2 := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    rw [wIntegrand_of_ge (by linarith [hx.1]), bigW_eq hx.1 hx.2]
  rw [hcongr]
  have hderiv : ∀ x ∈ uIcc (2 : ℝ) 3, HasDerivAt (fun x => (1 + log (x - 1)) / x)
      ((1 / (x - 1) - log (x - 1)) / x ^ 2) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 x := (hasDerivAt_id x).sub_const 1
    have := ((h1.log hx1).const_add 1).div (hasDerivAt_id x) hx0
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => (1 / (x - 1) - log (x - 1)) / x ^ 2) (uIcc 2 3) := by
    rw [uIcc_of_le (by norm_num)]
    intro x hx
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    have hx0 : x ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [hx.1])
    exact (((continuousAt_const.div (continuousAt_id.sub continuousAt_const) hx1).sub
      ((continuousAt_id.sub continuousAt_const).log hx1)).div
      (continuousAt_id.pow 2) hx0).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  norm_num

/-- [I71, (3.11)]: `𝔚(s) = -s ∫_{s-1}^s 𝔚(x)/x² dx` for `s ≥ 3`. -/
theorem bigW_eq_neg_mul_integral {s : ℝ} (hs : 3 ≤ s) :
    bigW s = -s * ∫ x in (s - 1)..s, bigW x / x ^ 2 := by
  set g : ℝ → ℝ := fun t => bigW t / t + ∫ x in (t - 1)..t, wIntegrand x
  have hgc : ContinuousOn g (Ici 3) := by
    refine ContinuousOn.add ?_ ?_
    · exact continuous_bigW.continuousOn.div continuousOn_id fun x hx => by
        linarith [hx.out]
    · exact fun t _ => (hasDerivAt_integral_unit continuous_wIntegrand t).continuousAt
        |>.continuousWithinAt
  have hgd : ∀ t, 3 < t → HasDerivAt g 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith
    have ht1 : t - 1 ≠ 0 := by linarith
    have := ((hasDerivAt_bigW ht).div (hasDerivAt_id t) ht0).add
      (hasDerivAt_integral_unit continuous_wIntegrand t)
    refine this.congr_deriv ?_
    rw [wIntegrand_of_ge (by linarith), wIntegrand_of_ge (by linarith)]
    simp only [id]
    field_simp
    ring
  have h3 : g 3 = 0 := by
    simp only [g]
    norm_num
    rw [integral_wIntegrand_two_three, bigW_three]
    ring
  have hgs : g s = 0 := (eq_of_hasDerivAt_zero hgc hgd hs).trans h3
  have hint : ∫ x in (s - 1)..s, wIntegrand x = ∫ x in (s - 1)..s, bigW x / x ^ 2 := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    exact wIntegrand_of_ge (by linarith [hx.1])
  simp only [g, hint] at hgs
  have hs0 : s ≠ 0 := by linarith
  field_simp at hgs
  linarith

/-! ### (3.12) -/

/-- The integrand of (3.12), made continuous on `ℝ`. -/
noncomputable def mIntegrand (x : ℝ) : ℝ := (1 - 1 / (2 * max x 1 ^ 2)) * bigM x

theorem continuous_mIntegrand : Continuous mIntegrand := by
  unfold mIntegrand
  refine (continuous_const.sub (continuous_const.div
    (continuous_const.mul ((continuous_id.max continuous_const).pow 2)) fun x => ?_)).mul
    continuous_bigM
  exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (lt_of_lt_of_le one_pos (le_max_right _ _)).ne')

theorem mIntegrand_of_ge {x : ℝ} (hx : 1 ≤ x) :
    mIntegrand x = (1 - 1 / (2 * x ^ 2)) * bigM x := by
  simp [mIntegrand, max_eq_left hx]

theorem integral_mIntegrand_two_three :
    ∫ x in (2 : ℝ)..3, mIntegrand x = 7 / 2 * (5 / 2 - log 2) / 3 := by
  have hcongr : ∫ x in (2 : ℝ)..3, mIntegrand x =
      ∫ x in (2 : ℝ)..3, (1 - 1 / (2 * x ^ 2)) * (2 + (1 / (x - 1) - log (x - 1))) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by norm_num)] at hx
    rw [mIntegrand_of_ge (by linarith [hx.1]), bigM_eq hx.1 hx.2]
    ring
  rw [hcongr]
  have hderiv : ∀ x ∈ uIcc (2 : ℝ) 3, HasDerivAt
      (fun x => ((x - 1) ^ 2 - 1 / 2) * (2 + (1 / (x - 1) - log (x - 1))) / x + x +
        1 / (2 * (x - 1)))
      ((1 - 1 / (2 * x ^ 2)) * (2 + (1 / (x - 1) - log (x - 1)))) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 x := (hasDerivAt_id x).sub_const 1
    have hr : HasDerivAt (fun x : ℝ => (x - 1) ^ 2 - 1 / 2) (2 * (x - 1)) x := by
      convert (h1.pow 2).sub_const (1 / 2) using 1; ring
    have hm := (hasDerivAt_initForm (x := x) (by linarith [hx.1])).const_add 2
    have hq : HasDerivAt (fun x : ℝ => 2 * (x - 1)) 2 x := by
      convert h1.const_mul 2 using 1; ring
    have := (((hr.mul hm).div (hasDerivAt_id x) hx0).add (hasDerivAt_id x)).add
      ((hasDerivAt_const x (1 : ℝ)).div hq (by positivity))
    refine this.congr_deriv ?_
    simp only [id, Pi.mul_apply]
    field_simp
    ring
  have hcont : ContinuousOn
      (fun x : ℝ => (1 - 1 / (2 * x ^ 2)) * (2 + (1 / (x - 1) - log (x - 1)))) (uIcc 2 3) := by
    rw [uIcc_of_le (by norm_num)]
    intro x hx
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    have hx0 : 2 * x ^ 2 ≠ 0 := by have : x ≠ 0 := by linarith [hx.1]
                                   positivity
    exact ((continuousAt_const.sub (continuousAt_const.div
      (continuousAt_const.mul (continuousAt_id.pow 2)) hx0)).mul
      (continuousAt_const.add ((continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        hx1).sub ((continuousAt_id.sub continuousAt_const).log hx1)))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  norm_num
  ring

/-- [I71, (3.12)]: `((s-1)² - 1/2) 𝔐(s) / s = ∫_{s-1}^s (1 - 1/(2x²)) 𝔐(x) dx` for `s ≥ 3`. -/
theorem bigM_integral_identity {s : ℝ} (hs : 3 ≤ s) :
    ((s - 1) ^ 2 - 1 / 2) * bigM s / s = ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * bigM x := by
  set g : ℝ → ℝ := fun t => ((t - 1) ^ 2 - 1 / 2) * bigM t / t - ∫ x in (t - 1)..t, mIntegrand x
  have hgc : ContinuousOn g (Ici 3) := by
    refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.div ?_ continuousOn_id fun x hx => by linarith [hx.out]
      exact (((continuous_id.sub continuous_const).pow 2).sub continuous_const).continuousOn.mul
        continuous_bigM.continuousOn
    · exact fun t _ => (hasDerivAt_integral_unit continuous_mIntegrand t).continuousAt
        |>.continuousWithinAt
  have hgd : ∀ t, 3 < t → HasDerivAt g 0 t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith
    have ht1 : t - 1 ≠ 0 := by linarith
    have h1 : HasDerivAt (fun x : ℝ => x - 1) 1 t := (hasDerivAt_id t).sub_const 1
    have hr : HasDerivAt (fun x : ℝ => (x - 1) ^ 2 - 1 / 2) (2 * (t - 1)) t := by
      convert (h1.pow 2).sub_const (1 / 2) using 1; ring
    have := ((hr.mul (hasDerivAt_bigM ht)).div (hasDerivAt_id t) ht0).sub
      (hasDerivAt_integral_unit continuous_mIntegrand t)
    refine this.congr_deriv ?_
    rw [mIntegrand_of_ge (by linarith), mIntegrand_of_ge (by linarith)]
    simp only [id, Pi.mul_apply]
    field_simp
    ring
  have h3 : g 3 = 0 := by
    simp only [g]
    norm_num
    rw [integral_mIntegrand_two_three, bigM_three]
    ring
  have hgs : g s = 0 := (eq_of_hasDerivAt_zero hgc hgd hs).trans h3
  have hint : ∫ x in (s - 1)..s, mIntegrand x =
      ∫ x in (s - 1)..s, (1 - 1 / (2 * x ^ 2)) * bigM x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    exact mIntegrand_of_ge (by linarith [hx.1])
  simp only [g, hint] at hgs
  linarith

end IwaniecLinearSieve
