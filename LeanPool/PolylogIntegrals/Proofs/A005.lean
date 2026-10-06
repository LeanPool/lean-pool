/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Proofs.A004

/-!
# A005: `∫₀¹ log²(1+x²)/x³ dx = π²/12 - log²2`

Write `L(x) = log(1+x²)` and `H(x) = -L(x)²/(2x²) - L(x)²/2`. For `x ≠ 0`,
`H'(x) = L(x)²/x³ - 2 L(x)/x`, so
`∫₀¹ L²/x³ = (H(1) - H(0)) + 2 ∫₀¹ L/x = -log²2 + 2 · π²/24` by the fundamental theorem of
calculus and A004.

In Lean `H 0 = 0` and the integrands take the value `0` at `x = 0`. All three functions are
continuous at `0`, because `0 ≤ L(x) ≤ x²`.
-/

open Real

namespace LeanPolyLog.Proofs

/-- The antiderivative `H(x) = -log²(1+x²)/(2x²) - log²(1+x²)/2` used for A005. -/
private noncomputable def antiderivA005 (x : ℝ) : ℝ :=
  -(Real.log (1 + x ^ 2) ^ 2 / (2 * x ^ 2)) - Real.log (1 + x ^ 2) ^ 2 / 2

private theorem continuous_antiderivA005 : Continuous antiderivA005 := by
  have hc : Continuous fun x : ℝ => Real.log (1 + x ^ 2) ^ 2 / (2 * x ^ 2) := by
    refine Series.continuous_of_norm_le_of_tendsto_zero (g := fun x => x ^ 2 / 2)
      (fun x hx => ?_) (by simp) (fun x => ?_) ?_
    · have h1 : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
      have h2 : 2 * x ^ 2 ≠ 0 := by positivity
      fun_prop (disch := assumption)
    · rcases eq_or_ne x 0 with rfl | hx
      · simp
      have hL0 := Series.log_one_add_sq_nonneg x
      have hx2 : 0 < 2 * x ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity), abs_of_pos hx2,
        div_le_iff₀ hx2]
      have : Real.log (1 + x ^ 2) ^ 2 ≤ (x ^ 2) ^ 2 :=
        pow_le_pow_left₀ hL0 (Series.log_one_add_sq_le_sq x) 2
      nlinarith
    · have : Continuous fun x : ℝ => x ^ 2 / 2 := by fun_prop
      simpa using this.tendsto 0
  have hc2 : Continuous fun x : ℝ => Real.log (1 + x ^ 2) ^ 2 / 2 := by
    have : ∀ x : ℝ, (1 : ℝ) + x ^ 2 ≠ 0 := fun x => by positivity
    fun_prop (disch := exact this _)
  exact hc.neg.sub hc2

private theorem hasDerivAt_antiderivA005 {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt antiderivA005
      (Real.log (1 + x ^ 2) ^ 2 / x ^ 3 - 2 * (Real.log (1 + x ^ 2) / x)) x := by
  have h1 : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  have hp : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  have hL2 := (hp.log h1).pow 2
  have hd : HasDerivAt (fun x : ℝ => 2 * x ^ 2) (2 * (2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul 2
  have hq := (hL2.div hd (by positivity)).neg.sub (hL2.div_const 2)
  convert hq using 1
  · funext y
    simp only [antiderivA005, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, Pi.pow_apply]
  · simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
    ring

/-- A005: `∫₀¹ log²(1+x²)/x³ dx = π²/12 - log²2`. -/
public theorem A005 :
    ∫ x in (0 : ℝ)..1, Real.log (1 + x ^ 2) ^ 2 / x ^ 3 = π ^ 2 / 12 - Real.log 2 ^ 2 := by
  have hi1 : IntervalIntegrable (fun x : ℝ => Real.log (1 + x ^ 2) ^ 2 / x ^ 3)
      MeasureTheory.volume 0 1 :=
    Series.continuous_log_one_add_sq_sq_div_cube.intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun x : ℝ => 2 * (Real.log (1 + x ^ 2) / x))
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul Series.continuous_log_one_add_sq_div).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    continuous_antiderivA005.continuousOn (fun x hx => hasDerivAt_antiderivA005 hx.1.ne')
    (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul, A004] at hftc
  have h1 : antiderivA005 1 = -Real.log 2 ^ 2 := by
    norm_num [antiderivA005]
    ring
  have h0 : antiderivA005 0 = 0 := by
    simp [antiderivA005]
  rw [h1, h0] at hftc
  linarith

end LeanPolyLog.Proofs
