/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.GaussianConvexity.CrossingInterval
public import LeanPool.EhrhardGaussian.GaussianConvexity.ExponentialInterpolation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Two exponential cancellations give a scalar comparison when the positive set is convex,
including negative and mixed-sign exponents. -/

@[expose] public section

open MeasureTheory Set Filter

namespace EhrhardGaussian.GaussianConvexity

/-- The exponential difference with two zero endpoint integrals has nonnegative middle integral. -/
theorem integral_exp_mul_nonneg_of_convex_positive {f : ℝ → ℝ} {p₀ p p₁ : ℝ}
    (hp₀ : p₀ < p) (hp₁ : p < p₁) (hc : Convex ℝ {t | 0 < f t})
    (h₀ : Integrable (fun t => Real.exp (p₀ * t) * f t))
    (h₁ : Integrable (fun t => Real.exp (p₁ * t) * f t))
    (hp : Integrable (fun t => Real.exp (p * t) * f t))
    (hz₀ : ∫ t, Real.exp (p₀ * t) * f t = 0)
    (hz₁ : ∫ t, Real.exp (p₁ * t) * f t = 0) :
    0 ≤ ∫ t, Real.exp (p * t) * f t := by
  rcases ae_zero_or_two_crossings (hp₀.trans hp₁) hc h₀ h₁ hz₀ hz₁ with hzero | ⟨a, b, hab, hpos,
    hneg⟩
  · have heq : (fun t => Real.exp (p * t) * f t) =ᵐ[volume] 0 := by
      filter_upwards [hzero] with t ht
      change f t = 0 at ht
      change Real.exp (p * t) * f t = 0
      rw [ht, mul_zero]
    rw [integral_congr_ae heq]
    simp only [Pi.zero_apply, integral_zero, le_refl]
  let d := p₁ - p₀
  let θ := (p - p₀) / d
  have hd : 0 < d := sub_pos.mpr (hp₀.trans hp₁)
  have hθ0 : 0 ≤ θ := (div_pos (sub_pos.mpr hp₀) hd).le
  have hθ1 : θ ≤ 1 := (div_le_one hd).mpr (by dsimp [d]; linarith only [hp₁])
  have hmid : p₀ + d * θ = p := by
    dsimp [θ]
    rw [mul_div_cancel₀ _ hd.ne']
    ring
  have hhigh : p₀ + d = p₁ := by dsimp [d]; ring
  let U := Real.exp (d * a)
  let V := Real.exp (d * b)
  have hUV : U < V := Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hab hd)
  have hVU : V - U ≠ 0 := sub_ne_zero.mpr hUV.ne'
  let A := (V * U ^ θ - U * V ^ θ) / (V - U)
  let B := (V ^ θ - U ^ θ) / (V - U)
  let ψ := fun t => Real.exp (p * t) - A * Real.exp (p₀ * t) - B * Real.exp (p₁ * t)
  have hfact : ∀ t, ψ t = Real.exp (p₀ * t) *
      ((Real.exp (d * t)) ^ θ -
        ((V - Real.exp (d * t)) * U ^ θ + (Real.exp (d * t) - U) * V ^ θ) / (V - U)) := by
    intro t
    dsimp [ψ]
    rw [← hmid, ← hhigh, three_exponential_factorization, chord_eq_affine]
    dsimp [A, B]
    ring
  have hψa : ψ a = 0 := by
    rw [hfact]
    change Real.exp (p₀ * a) * (U ^ θ - ((V - U) * U ^ θ + (U - U) * V ^ θ) / (V - U)) = 0
    rw [sub_self, zero_mul, add_zero, mul_div_cancel_left₀ _ hVU, sub_self, mul_zero]
  have hψb : ψ b = 0 := by
    rw [hfact]
    change Real.exp (p₀ * b) * (V ^ θ - ((V - V) * U ^ θ + (V - U) * V ^ θ) / (V - U)) = 0
    rw [sub_self, zero_mul, zero_add, mul_div_cancel_left₀ _ hVU, sub_self, mul_zero]
  have hsign : ∀ t, 0 ≤ ψ t * f t := by
    intro t
    by_cases hta : t = a
    · rw [hta, hψa, zero_mul]
    by_cases htb : t = b
    · rw [htb, hψb, zero_mul]
    have hpow := rpow_chord_sign hθ0 hθ1 (Real.exp_pos (d * a)).le hUV (Real.exp_pos (d * t)).le
    by_cases ht : t ∈ Ioo a b
    · have hψ : 0 ≤ ψ t := by
        rw [hfact]
        apply mul_nonneg (Real.exp_pos _).le
        exact hpow.1 ⟨(Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.1.le hd.le)),
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2.le hd.le)⟩
      exact mul_nonneg hψ (hpos t ht).le
    · have hout : t < a ∨ b < t := by
        simp only [mem_Ioo, not_and_or, not_lt] at ht
        rcases ht with ht | ht
        · exact Or.inl (lt_of_le_of_ne ht hta)
        · exact Or.inr (lt_of_le_of_ne ht (Ne.symm htb))
      have hψ : ψ t ≤ 0 := by
        rw [hfact]
        apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        apply hpow.2
        rcases hout with ht | ht
        · exact Or.inl (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.le hd.le))
        · exact Or.inr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.le hd.le))
      exact mul_nonneg_of_nonpos_of_nonpos hψ (hneg t hout)
  have hfun : (fun t => ψ t * f t) = fun t => Real.exp (p * t) * f t -
      A * (Real.exp (p₀ * t) * f t) - B * (Real.exp (p₁ * t) * f t) := by
    funext t
    dsimp [ψ]
    ring
  have hint : Integrable (fun t => ψ t * f t) := by
    rw [hfun]
    exact (hp.sub (h₀.const_mul A)).sub (h₁.const_mul B)
  have heq : ∫ t, ψ t * f t = ∫ t, Real.exp (p * t) * f t := by
    rw [hfun]
    have hA : Integrable (A • (fun t => Real.exp (p₀ * t) * f t)) := h₀.smul A
    have hB : Integrable (B • (fun t => Real.exp (p₁ * t) * f t)) := h₁.smul B
    change (∫ t, (((fun t => Real.exp (p * t) * f t) -
      A • (fun t => Real.exp (p₀ * t) * f t)) -
      B • (fun t => Real.exp (p₁ * t) * f t)) t) = _
    rw [integral_sub' (hp.sub hA) hB, integral_sub' hp hA]
    change ((∫ t, Real.exp (p * t) * f t) -
      ∫ t, A * (Real.exp (p₀ * t) * f t)) - ∫ t, B * (Real.exp (p₁ * t) * f t) = _
    rw [integral_const_mul, integral_const_mul, hz₀, hz₁, mul_zero, mul_zero, sub_zero, sub_zero]
  rw [← heq]
  exact integral_nonneg hsign

end EhrhardGaussian.GaussianConvexity
