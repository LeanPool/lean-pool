/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Nested cylinders and absorption for the interior analyticity induction

Two elementary facts used in the proof of `thm:analytic:interior`. The region of depth `τ` is
`{|x| < R' + (1 - τ) d} × [s₁ - (1 - τ) d², s₂]`. A backward window of radius
`ρ = θ τ d / (k + 1)` around a point of depth `τ` lies in the region of depth
`τ (1 - θ / (k + 1))`, and moving to that depth costs at most a factor `2` on the weights
`(τ d)^j`, `j ≤ k + 2`. The second fact is the limit form of the absorption step.
-/

public section

open Set
open CKN.Foundation.Parabolic


noncomputable section



namespace CIV

/-- A backward window of radius `θ τ d / (k + 1)` around a point of depth `τ` lies in the region
of depth `τ (1 - θ / (k + 1))`, and the weights change by at most a factor `2` up to order
`k + 2`. -/
theorem kahane_window_subset_deeper {R' d s₁ s₂ τ θ : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1)
    (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4) (k : ℕ) :
    0 < θ * τ * d / (k + 1) ∧ θ * τ * d / (k + 1) ≤ 1 ∧
      0 < τ * (1 - θ / (k + 1)) ∧ τ * (1 - θ / (k + 1)) ≤ τ ∧
      (∀ (x : Vec3) (t : ℝ), vec3EuclideanNorm x < R' + (1 - τ) * d →
        s₁ - (1 - τ) * d ^ 2 ≤ t → t ≤ s₂ →
        ∀ z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ θ * τ * d / (k + 1)} ×ˢ
            Icc (t - (θ * τ * d / (k + 1)) ^ 2) t,
          vec3EuclideanNorm z.1 < R' + (1 - τ * (1 - θ / (k + 1))) * d ∧
            s₁ - (1 - τ * (1 - θ / (k + 1))) * d ^ 2 ≤ z.2 ∧ z.2 ≤ s₂) ∧
      ∀ j : ℕ, j ≤ k + 2 → (τ * d) ^ j ≤ 2 * (τ * (1 - θ / (k + 1)) * d) ^ j := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith only [this]
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith only [hk1]
  set e : ℝ := θ / (k + 1) with he_def
  have he0 : 0 < e := div_pos hθ hkpos
  have he4 : e ≤ 1 / 4 := by
    rw [he_def, div_le_iff₀ hkpos]
    nlinarith only [hθ4, hk1, hθ]
  have hρ : θ * τ * d / (k + 1) = τ * d * e := by rw [he_def]; ring
  have hτd : 0 < τ * d := mul_pos hτ hd
  have hτd1 : τ * d ≤ 1 := by nlinarith only [hτ1, hd1, hτ, hd]
  rw [hρ]
  refine ⟨by positivity, by nlinarith only [hτd, hτd1, he4, he0], by nlinarith only [hτ, he4],
    by nlinarith only [hτ, he0], ?_, ?_⟩
  · intro x t hx ht₁ ht₂ z hz
    obtain ⟨hzx, hzt₁, hzt₂⟩ := hz
    change vec3EuclideanNorm (z.1 - x) ≤ τ * d * e at hzx
    have htri : vec3EuclideanNorm z.1 ≤ vec3EuclideanNorm x + vec3EuclideanNorm (z.1 - x) := by
      have h := norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 (z.1 - x))
      rw [← WithLp.toLp_add, add_sub_cancel] at h
      simpa only [← vec3EuclideanNorm_eq_l2] using h
    have hd2 : 0 < d ^ 2 := by positivity
    refine ⟨?_, ?_, hzt₂.trans ht₂⟩
    · nlinarith only [htri, hzx, hx]
    · have hsq : (τ * d * e) ^ 2 ≤ τ * e * d ^ 2 := by
        have h1 : τ * e ≤ 1 := by nlinarith only [hτ1, he4, hτ, he0]
        have h2 : 0 ≤ τ * e := by positivity
        have hid : (τ * d * e) ^ 2 = (τ * e) * ((τ * e) * d ^ 2) := by ring
        rw [hid]
        have := mul_le_mul_of_nonneg_right h1 (mul_nonneg h2 hd2.le)
        linarith only [this]
      nlinarith only [hzt₁, ht₁, hsq]
  · intro j hj
    have hbern : 1 - (j : ℝ) * e ≤ (1 - e) ^ j := by
      have := one_add_mul_le_pow (a := -e) (by linarith only [he4]) j
      simpa only [sub_eq_add_neg, mul_neg] using this
    have hj' : (j : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast hj
    have hje : (j : ℝ) * e ≤ 1 / 2 := by
      rw [he_def, mul_div_assoc']
      rw [div_le_iff₀ hkpos]
      nlinarith only [hj', hθ4, hθ, hk1]
    have hhalf : 1 / 2 ≤ (1 - e) ^ j := by linarith only [hbern, hje]
    have heq : (τ * (1 - e) * d) ^ j = (τ * d) ^ j * (1 - e) ^ j := by
      rw [← mul_pow]; ring
    rw [heq]
    have hp : 0 ≤ (τ * d) ^ j := by positivity
    nlinarith only [hp, hhalf]

/-- A number below `X + Y₀ / 2ⁿ` for every `n` is below `X`. -/
theorem le_of_forall_le_add_div_two_pow {a X Y₀ : ℝ} (h : ∀ n : ℕ, a ≤ X + Y₀ / 2 ^ n) :
    a ≤ X := by
  have ht : Filter.Tendsto (fun n : ℕ => X + Y₀ / 2 ^ n) Filter.atTop (nhds (X + 0)) := by
    refine tendsto_const_nhds.add ?_
    simpa [div_eq_mul_inv, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul Y₀
  rw [add_zero] at ht
  exact ge_of_tendsto' ht h

end CIV
