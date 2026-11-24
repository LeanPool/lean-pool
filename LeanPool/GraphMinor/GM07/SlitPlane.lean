/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Opening a slit in the unit ball

To cut a surface along a line we work in a chart in which the line is the segment `[-s, s]` of the
real axis, and we
remove the open ball of radius `s`. The map `slitMap s` of the closed unit ball is the identity on
the unit circle.
It leaves the real part alone and scales the imaginary part by a factor that grows with the norm,
from `0` at norm `s`
to `1` at norm `1`. So the circle of radius `s` is folded onto the segment, and off this circle the
map is one to one
(`slitMap_eq`). Each vertical line is treated on its own, by the intermediate value theorem
(`exists_slitMap_eq`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Metric Complex

/-- The factor at norm `ρ`: `0` up to `s`, and `1` at `1`. -/
noncomputable def slitFactor (s ρ : ℝ) : ℝ := (1 - s / max ρ s) / (1 - s)

/-- The map that folds the circle of radius `s` onto the segment `[-s, s]`. -/
noncomputable def slitMap (s : ℝ) (z : ℂ) : ℂ := ⟨z.re, z.im * slitFactor s ‖z‖⟩

variable {s : ℝ}

theorem slitFactor_nonneg (h0 : 0 < s) (h1 : s < 1) (ρ : ℝ) : 0 ≤ slitFactor s ρ := by
  have hm : s ≤ max ρ s := le_max_right _ _
  have hp : 0 < max ρ s := lt_of_lt_of_le h0 hm
  have : s / max ρ s ≤ 1 := (div_le_one hp).mpr hm
  exact div_nonneg (by linarith) (by linarith)

theorem slitFactor_le_one (h0 : 0 < s) (h1 : s < 1) {ρ : ℝ} (hρ : ρ ≤ 1) : slitFactor s ρ ≤ 1 := by
  have hm : s ≤ max ρ s := le_max_right _ _
  have hp : 0 < max ρ s := lt_of_lt_of_le h0 hm
  have hm1 : max ρ s ≤ 1 := max_le hρ h1.le
  have : s ≤ s / max ρ s := by
    rw [le_div_iff₀ hp]
    nlinarith
  rw [slitFactor, div_le_one (by linarith)]
  linarith

theorem slitFactor_one (h1 : s < 1) : slitFactor s 1 = 1 := by
  have : (1 - s) ≠ 0 := by linarith
  rw [slitFactor, max_eq_left h1.le, div_one, div_self this]

theorem slitFactor_of_le (_h1 : s < 1) {ρ : ℝ} (h : ρ ≤ s) (h0 : 0 < s) : slitFactor s ρ = 0 := by
  rw [slitFactor, max_eq_right h, div_self h0.ne']
  simp

theorem slitFactor_pos (h0 : 0 < s) (h1 : s < 1) {ρ : ℝ} (h : s < ρ) : 0 < slitFactor s ρ := by
  have hp : 0 < ρ := h0.trans h
  rw [slitFactor, max_eq_left h.le]
  have : s / ρ < 1 := (div_lt_one hp).mpr h
  exact div_pos (by linarith) (by linarith)

theorem slitFactor_mono (h0 : 0 < s) (h1 : s < 1) {ρ ρ' : ℝ} (h : ρ ≤ ρ') : slitFactor s ρ
  ≤ slitFactor s ρ' := by
  have hm : max ρ s ≤ max ρ' s := max_le_max_right _ h
  have hp : 0 < max ρ s := lt_of_lt_of_le h0 (le_max_right _ _)
  have : s / max ρ' s ≤ s / max ρ s := div_le_div_of_nonneg_left h0.le hp hm
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

theorem continuous_slitFactor (h0 : 0 < s) : Continuous (slitFactor s) := by
  have hne : ∀ ρ : ℝ, max ρ s ≠ 0 := fun ρ => (lt_of_lt_of_le h0 (le_max_right _ _)).ne'
  unfold slitFactor
  exact ((continuous_const.sub (continuous_const.div (continuous_id.max continuous_const)
    hne))).div_const _

theorem continuous_slitMap (h0 : 0 < s) : Continuous (slitMap s) := by
  have h : Continuous fun z : ℂ => z.im * slitFactor s ‖z‖ :=
    continuous_im.mul ((continuous_slitFactor h0).comp continuous_norm)
  have hre := Complex.continuous_re
  have : slitMap s = fun z => (z.re : ℂ) + ((z.im * slitFactor s ‖z‖ : ℝ) : ℂ) * I := by
    funext z
    apply Complex.ext <;> simp [slitMap]
  rw [this]
  exact (continuous_ofReal.comp hre).add ((continuous_ofReal.comp h).mul continuous_const)

theorem slitMap_re (z : ℂ) : (slitMap s z).re = z.re := rfl

theorem slitMap_im (z : ℂ) : (slitMap s z).im = z.im * slitFactor s ‖z‖ := rfl

theorem slitMap_of_norm_eq_one (h1 : s < 1) {z : ℂ} (hz : ‖z‖ = 1) : slitMap s z = z := by
  apply Complex.ext
  · rfl
  · rw [slitMap_im, hz, slitFactor_one h1, mul_one]

theorem slitMap_of_norm_le (h0 : 0 < s) (h1 : s < 1) {z : ℂ} (hz : ‖z‖ ≤ s) : slitMap s z =
  (z.re : ℂ) := by
  apply Complex.ext
  · simp [slitMap_re]
  · rw [slitMap_im, slitFactor_of_le h1 hz h0]
    simp

theorem norm_of_re_im (x y : ℝ) : ‖(⟨x, y⟩ : ℂ)‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]

theorem norm_slitMap_le (h0 : 0 < s) (h1 : s < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖slitMap s z‖ ≤ 1 := by
  have hf := slitFactor_nonneg h0 h1 ‖z‖
  have hf1 := slitFactor_le_one h0 h1 hz
  have : ‖slitMap s z‖ ≤ ‖z‖ := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
    apply Real.sqrt_le_sqrt
    rw [slitMap_re, slitMap_im]
    have : (z.im * slitFactor s ‖z‖) ^ 2 ≤ z.im ^ 2 := by
      rw [mul_pow]
      have : slitFactor s ‖z‖ ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg z.im]
    linarith
  linarith

/-- On a vertical line and above the circle of radius `s`, the map is strictly increasing. -/
theorem slit_strict (h0 : 0 < s) (h1 : s < 1) {x y y' : ℝ} (hy : 0 ≤ y) (hyy : y < y')
    (hs : s ≤ ‖(⟨x, y⟩ : ℂ)‖) : y * slitFactor s ‖(⟨x, y⟩ : ℂ)‖ < y' * slitFactor s ‖(⟨x, y'⟩ : ℂ)‖
      := by
  have hn : ‖(⟨x, y⟩ : ℂ)‖ < ‖(⟨x, y'⟩ : ℂ)‖ := by
    rw [norm_of_re_im, norm_of_re_im]
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith
  have hp := slitFactor_pos h0 h1 (lt_of_le_of_lt hs hn)
  have hm := slitFactor_mono h0 h1 hn.le
  have hf := slitFactor_nonneg h0 h1 ‖(⟨x, y⟩ : ℂ)‖
  nlinarith

/-- A point and its mirror image have the same norm. -/
theorem norm_neg_im (x y : ℝ) : ‖(⟨x, -y⟩ : ℂ)‖ = ‖(⟨x, y⟩ : ℂ)‖ := by
  rw [norm_of_re_im, norm_of_re_im, neg_sq]

/-- Two points off the open ball of radius `s` with the same image are equal, or are mirror images
on the circle. -/
theorem slitMap_eq (h0 : 0 < s) (h1 : s < 1) {z w : ℂ} (hz : s ≤ ‖z‖) (hw : s ≤ ‖w‖)
    (he : slitMap s z = slitMap s w) : z = w ∨ (‖z‖ = s ∧ ‖w‖ = s ∧ w = (starRingEnd ℂ) z) := by
  have hre : z.re = w.re := by simpa only [slitMap_re] using congrArg Complex.re he
  have him : z.im * slitFactor s ‖z‖ = w.im * slitFactor s ‖w‖ := by
    simpa only [slitMap_im] using congrArg Complex.im he
  obtain ⟨x, y⟩ := z
  obtain ⟨x', y'⟩ := w
  simp only at hre him
  subst hre
  -- Same sign: the map is strictly monotone. Opposite signs: both values vanish.
  have key : ∀ {a b : ℝ}, 0 ≤ a → a < b → s ≤ ‖(⟨x, a⟩ : ℂ)‖ →
      a * slitFactor s ‖(⟨x, a⟩ : ℂ)‖ ≠ b * slitFactor s ‖(⟨x, b⟩ : ℂ)‖ := fun ha hab hs =>
    (slit_strict h0 h1 ha hab hs).ne
  have hconj : (starRingEnd ℂ) (⟨x, y⟩ : ℂ) = ⟨x, -y⟩ := rfl
  rcases lt_trichotomy y y' with hlt | rfl | hlt
  · rcases le_or_gt 0 y with hy | hy
    · exact (key hy hlt hz him).elim
    · rcases le_or_gt y' 0 with hy' | hy'
      · have hz' : s ≤ ‖(⟨x, -y'⟩ : ℂ)‖ := by rwa [norm_neg_im]
        have := key (a := -y') (b := -y) (by linarith) (by linarith) hz'
        rw [norm_neg_im, norm_neg_im] at this
        exact (this (by linarith)).elim
      · have hf := slitFactor_nonneg h0 h1 ‖(⟨x, y⟩ : ℂ)‖
        have hf' := slitFactor_nonneg h0 h1 ‖(⟨x, y'⟩ : ℂ)‖
        have h3 : y * slitFactor s ‖(⟨x, y⟩ : ℂ)‖ = 0 := by nlinarith
        have h4 : y' * slitFactor s ‖(⟨x, y'⟩ : ℂ)‖ = 0 := by nlinarith
        have h5 : slitFactor s ‖(⟨x, y⟩ : ℂ)‖ = 0 := (mul_eq_zero.mp h3).resolve_left hy.ne
        have h6 : slitFactor s ‖(⟨x, y'⟩ : ℂ)‖ = 0 := (mul_eq_zero.mp h4).resolve_left hy'.ne'
        have h7 : ‖(⟨x, y⟩ : ℂ)‖ = s := le_antisymm (not_lt.mp fun h =>
          (slitFactor_pos h0 h1 h).ne' h5) hz
        have h8 : ‖(⟨x, y'⟩ : ℂ)‖ = s := le_antisymm (not_lt.mp fun h =>
          (slitFactor_pos h0 h1 h).ne' h6) hw
        have h9 : y' ^ 2 = y ^ 2 := by
          have h10 := congrArg (· ^ 2) (h7.trans h8.symm)
          simp only [norm_of_re_im] at h10
          rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h10
          linarith
        have h11 : y' = -y := by nlinarith
        exact .inr ⟨h7, h8, by rw [hconj, h11]⟩
  · exact .inl rfl
  · rcases le_or_gt 0 y' with hy | hy
    · exact (key hy hlt hw him.symm).elim
    · rcases le_or_gt y 0 with hy' | hy'
      · have hz' : s ≤ ‖(⟨x, -y⟩ : ℂ)‖ := by rwa [norm_neg_im]
        have := key (a := -y) (b := -y') (by linarith) (by linarith) hz'
        rw [norm_neg_im, norm_neg_im] at this
        exact (this (by linarith)).elim
      · have hf := slitFactor_nonneg h0 h1 ‖(⟨x, y⟩ : ℂ)‖
        have hf' := slitFactor_nonneg h0 h1 ‖(⟨x, y'⟩ : ℂ)‖
        have h3 : y' * slitFactor s ‖(⟨x, y'⟩ : ℂ)‖ = 0 := by nlinarith
        have h4 : y * slitFactor s ‖(⟨x, y⟩ : ℂ)‖ = 0 := by nlinarith
        have h5 : slitFactor s ‖(⟨x, y'⟩ : ℂ)‖ = 0 := (mul_eq_zero.mp h3).resolve_left hy.ne
        have h6 : slitFactor s ‖(⟨x, y⟩ : ℂ)‖ = 0 := (mul_eq_zero.mp h4).resolve_left hy'.ne'
        have h7 : ‖(⟨x, y'⟩ : ℂ)‖ = s := le_antisymm (not_lt.mp fun h =>
          (slitFactor_pos h0 h1 h).ne' h5) hw
        have h8 : ‖(⟨x, y⟩ : ℂ)‖ = s := le_antisymm (not_lt.mp fun h =>
          (slitFactor_pos h0 h1 h).ne' h6) hz
        have h9 : y' ^ 2 = y ^ 2 := by
          have h10 := congrArg (· ^ 2) (h7.trans h8.symm)
          simp only [norm_of_re_im] at h10
          rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h10
          linarith
        have h11 : y' = -y := by nlinarith
        exact .inr ⟨h8, h7, by rw [hconj, h11]⟩

/-- Over a real point of norm less than `s`, the two points of the circle. Over any other point of
the ball there is a
point off the open ball of radius `s`, by the intermediate value theorem on the vertical line
through it. -/
theorem exists_slitMap_eq (h0 : 0 < s) (h1 : s < 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ∃ z : ℂ, s ≤ ‖z‖ ∧ ‖z‖ ≤ 1 ∧ slitMap s z = w := by
  -- It is enough to treat `0 ≤ w.im`, by the mirror image.
  have hmirror : ∀ z : ℂ, slitMap s ((starRingEnd ℂ) z) = (starRingEnd ℂ) (slitMap s z) := fun z
    => by
    apply Complex.ext
    · simp [slitMap_re]
    · simp [slitMap_im]
  suffices key : ∀ w : ℂ, ‖w‖ ≤ 1 → 0 ≤ w.im → ∃ z : ℂ, s ≤ ‖z‖ ∧ ‖z‖ ≤ 1 ∧ slitMap s z = w by
    rcases le_total 0 w.im with h | h
    · exact key w hw h
    · have hconj : ‖(starRingEnd ℂ) w‖ ≤ 1 := by simpa only [Complex.norm_conj] using hw
      obtain ⟨z, h2, h3, h4⟩ := key ((starRingEnd ℂ) w) hconj (by simpa using h)
      refine ⟨(starRingEnd ℂ) z, by rwa [Complex.norm_conj], by rwa [Complex.norm_conj], ?_⟩
      rw [hmirror, h4]
      simp
  intro w hw him
  set x := w.re with hx
  set η := w.im with hη
  have hsq : x ^ 2 + η ^ 2 ≤ 1 := by
    have : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    rw [Complex.sq_norm, Complex.normSq_apply] at this
    nlinarith
  -- The lower end of the vertical segment: on the circle of radius `s`, or on the real axis.
  set y₀ := Real.sqrt (max (s ^ 2 - x ^ 2) 0) with hy₀
  set y₁ := Real.sqrt (1 - x ^ 2) with hy₁
  have hx1 : 0 ≤ 1 - x ^ 2 := by nlinarith [sq_nonneg η]
  have hy₀nn : 0 ≤ y₀ := Real.sqrt_nonneg _
  have hy₀sq : y₀ ^ 2 = max (s ^ 2 - x ^ 2) 0 := Real.sq_sqrt (le_max_right _ _)
  have hy₁sq : y₁ ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hx1
  have hy₁nn : 0 ≤ y₁ := Real.sqrt_nonneg _
  have hs2 : s ^ 2 < 1 := by nlinarith
  have hy₀₁ : y₀ ≤ y₁ := by
    apply Real.sqrt_le_sqrt
    exact max_le (by linarith) hx1
  have hηy₁ : η ≤ y₁ := by
    apply Real.le_sqrt_of_sq_le
    linarith
  let f : ℝ → ℝ := fun y => y * slitFactor s ‖(⟨x, y⟩ : ℂ)‖
  have hfc : Continuous f := by
    have h2 : Continuous fun y : ℝ => (⟨x, y⟩ : ℂ) := by
      have : (fun y : ℝ => (⟨x, y⟩ : ℂ)) = fun y : ℝ => (x : ℂ) + (y : ℂ) * I := by
        funext y
        apply Complex.ext <;> simp
      rw [this]
      exact continuous_const.add (continuous_ofReal.mul continuous_const)
    exact continuous_id.mul ((continuous_slitFactor h0).comp (continuous_norm.comp h2))
  have hn₀ : ‖(⟨x, y₀⟩ : ℂ)‖ ≤ s ∨ y₀ = 0 := by
    rcases le_total (s ^ 2 - x ^ 2) 0 with h | h
    · right
      rw [hy₀, max_eq_right h, Real.sqrt_zero]
    · left
      rw [norm_of_re_im]
      rw [max_eq_left h] at hy₀sq
      rw [hy₀sq]
      refine Real.sqrt_le_iff.mpr ⟨h0.le, by linarith⟩
  have hf0 : f y₀ = 0 := by
    rcases hn₀ with h | h
    · change y₀ * slitFactor s _ = 0
      rw [slitFactor_of_le h1 h h0, mul_zero]
    · change y₀ * _ = 0
      rw [h, zero_mul]
  have hn₁ : ‖(⟨x, y₁⟩ : ℂ)‖ = 1 := by
    rw [norm_of_re_im, hy₁sq]
    simp
  have hf1 : f y₁ = y₁ := by
    change y₁ * slitFactor s _ = _
    rw [hn₁, slitFactor_one h1, mul_one]
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc hy₀₁ hfc.continuousOn (show η ∈ Icc (f y₀) (f y₁) by
    rw [hf0, hf1]
    exact ⟨him, hηy₁⟩)
  have hy0 : 0 ≤ y := hy₀nn.trans hy.1
  have hsq₀ : s ≤ ‖(⟨x, y⟩ : ℂ)‖ := by
    rw [norm_of_re_im]
    apply Real.le_sqrt_of_sq_le
    have h2 : y₀ ^ 2 ≤ y ^ 2 := by nlinarith [hy.1]
    have h3 : s ^ 2 - x ^ 2 ≤ y₀ ^ 2 := by
      rw [hy₀sq]
      exact le_max_left _ _
    linarith
  have hle1 : ‖(⟨x, y⟩ : ℂ)‖ ≤ 1 := by
    rw [norm_of_re_im]
    refine Real.sqrt_le_iff.mpr ⟨zero_le_one, ?_⟩
    have h2 : y ^ 2 ≤ y₁ ^ 2 := by nlinarith [hy.2]
    rw [hy₁sq] at h2
    linarith
  refine ⟨⟨x, y⟩, hsq₀, hle1, ?_⟩
  apply Complex.ext
  · rfl
  · exact hfy

/-- Off the closed ball of radius `s`, the image is not on the segment. -/
theorem slitMap_notMem_segment (h0 : 0 < s) (h1 : s < 1) {z : ℂ} (hz : s < ‖z‖) (him :
  (slitMap s z).im = 0) :
    s < |z.re| := by
  rw [slitMap_im] at him
  have h2 : z.im = 0 := (mul_eq_zero.mp him).resolve_right (slitFactor_pos h0 h1 hz).ne'
  have h3 : ‖z‖ = |z.re| := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, h2]
    simp [Real.sqrt_sq_eq_abs]
  linarith

end GraphMinor.GM07
