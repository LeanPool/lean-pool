/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.TransferOperator
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The transfer operator of orders two and three

For `N = 2` and `N = 3` the transfer operator `T = Daubechies.transfer N`,
`(T g)(ξ) = P(ξ/2) g(ξ/2) + P((ξ + 1)/2) g((ξ + 1)/2)` with `P(ξ) = P_N(sin²(πξ))`, has explicit
eigenfunctions among the trigonometric polynomials. They give the growth of the iterates `T^n 1`
exactly: `T^n 1 = 4^n` for `N = 2`, and `T^n 1` is a combination of `9^n` and `(-4)^n` for
`N = 3`. Hence `Daubechies.TransferGrowth 2 4 1` and `Daubechies.TransferGrowth 3 9 2` hold, and
the exponent `N - log₄ λ` of the decay estimates of the symbol product equals `2 - log₄ 4 = 1`
for `N = 2` and `3 - log₄ 9 = 3 - log₂ 3 ≈ 1.415` for `N = 3`.

**Linearity and eigenfunctions.** `T` is linear, hence so are its iterates
(`Daubechies.iterate_transfer_add`, `Daubechies.iterate_transfer_smul`), and an eigenfunction
`T e = μ e` satisfies `T^n e = μ^n e` (`Daubechies.iterate_transfer_eq_pow_smul`).

**The variable `s = sin²(πξ/2)`.** At the two points `ξ/2` and `(ξ + 1)/2` the factor `P` takes
the values `P_N(s)` and `P_N(1 - s)` (`Daubechies.transfer_eq_eval_sin_sq`), and the cosines met
below are polynomials in `s`: `cos(πξ) = 1 - 2s`, `cos(π(ξ + 1)) = 2s - 1` and
`cos(2πξ) = 1 - 8s(1 - s)` (`Daubechies.cos_two_pi_mul_div_two`,
`Daubechies.cos_two_pi_mul_add_one_div_two`, `Daubechies.cos_two_pi_mul_eq_sin_sq`). Each
eigenvalue equation below thereby becomes a polynomial identity in `s`.

**Order two.** `P_2(y) = 1 + 2y`, so `(T 1)(ξ) = (1 + 2s) + (1 + 2(1 - s)) = 4`
(`Daubechies.transfer_two_one`), `T^n 1 = 4^n` (`Daubechies.iterate_transfer_two_one`), and
`Daubechies.transferGrowth_two` follows.

**Order three.** `P_3(y) = 1 + 3y + 6y²`, and with `c(ξ) = cos(2πξ)`,
`T (9 + c) = 9 (9 + c)` and `T (1 + 3c) = -4 (1 + 3c)` (`Daubechies.transfer_three_eigen_one`,
`Daubechies.transfer_three_eigen_two`); in the first identity both sides equal
`90 - 72s(1 - s)`. Since `1 = (3/26)(9 + c) - (1/26)(1 + 3c)`,
`T^n 1 = (3/26) 9^n (9 + c) - (1/26) (-4)^n (1 + 3c)` (`Daubechies.iterate_transfer_three_one`),
which is at most `(30/26) 9^n + (4/26) 4^n ≤ (17/13) 9^n`
(`Daubechies.iterate_transfer_three_one_le`); `Daubechies.transferGrowth_three` follows.
-/

@[expose] public section

open scoped Real

namespace Daubechies

/-! ### Linearity of the iterates and eigenfunctions -/

/-- The iterates of the transfer operator are additive: `T^n (g₁ + g₂) = T^n g₁ + T^n g₂` for
every `n`, since `T` is additive (Mathlib's `Function.Semiconj₂.iterate`). -/
theorem iterate_transfer_add (N n : ℕ) (g₁ g₂ : ℝ → ℝ) :
    (transfer N)^[n] (g₁ + g₂) = (transfer N)^[n] g₁ + (transfer N)^[n] g₂ :=
  have ha : Function.Semiconj₂ (transfer N) (· + ·) (· + ·) := transfer_add N
  (ha.iterate n).eq g₁ g₂

/-- The iterates of the transfer operator are homogeneous: `T^n (c g) = c T^n g` for every `n`
and every real `c`, since `T` commutes with the multiplication by `c` (Mathlib's
`Function.Commute.iterate_left`). -/
theorem iterate_transfer_smul (N n : ℕ) (c : ℝ) (g : ℝ → ℝ) :
    (transfer N)^[n] (c • g) = c • (transfer N)^[n] g :=
  have hc : Function.Commute (transfer N) (c • ·) := transfer_smul N c
  hc.iterate_left n g

/-- **Eigenfunctions of the transfer operator**: if `T e = μ e`, then `T^n e = μ^n e` for every
`n`. The operator `T` commutes with the multiplication by `μ` and agrees with it at `e`, so their
iterates agree at `e` (Mathlib's `Function.Commute.iterate_eq_of_map_eq`), and the `n`-th iterate
of the multiplication by `μ` is the multiplication by `μ^n` (Mathlib's `smul_iterate_apply`). -/
theorem iterate_transfer_eq_pow_smul {N : ℕ} {e : ℝ → ℝ} {μ : ℝ} (he : transfer N e = μ • e)
    (n : ℕ) : (transfer N)^[n] e = μ ^ n • e :=
  have hc : Function.Commute (transfer N) (μ • ·) := transfer_smul N μ
  (hc.iterate_eq_of_map_eq n he).trans (smul_iterate_apply μ n e)

/-! ### The transfer operator in the variable `s = sin²(πξ/2)` -/

/-- **The transfer operator in the variable `s = sin²(πξ/2)`**: for every `N`, `g` and `ξ`,
`(T g)(ξ) = P_N(s) g(ξ/2) + P_N(1 - s) g((ξ + 1)/2)`. Indeed `P(ξ/2) = P_N(sin²(πξ/2))` by
definition, and `P((ξ + 1)/2) = P(ξ/2 + 1/2) = P_N(cos²(πξ/2)) = P_N(1 - s)`
(`Daubechies.daubFun_add_half`). -/
theorem transfer_eq_eval_sin_sq (N : ℕ) (g : ℝ → ℝ) (ξ : ℝ) :
    transfer N g ξ = (daubPoly N).eval (Real.sin (π * (ξ / 2)) ^ 2) * g (ξ / 2) +
      (daubPoly N).eval (1 - Real.sin (π * (ξ / 2)) ^ 2) * g ((ξ + 1) / 2) := by
  rw [transfer, show (ξ + 1) / 2 = ξ / 2 + 1 / 2 by ring, daubFun_add_half, Real.cos_sq']
  rfl

/-- `cos(2π · ξ/2) = cos(πξ) = 1 - 2s` with `s = sin²(πξ/2)` (Mathlib's
`Real.cos_two_mul_eq_one_sub`). -/
theorem cos_two_pi_mul_div_two (ξ : ℝ) :
    Real.cos (2 * π * (ξ / 2)) = 1 - 2 * Real.sin (π * (ξ / 2)) ^ 2 := by
  rw [show 2 * π * (ξ / 2) = 2 * (π * (ξ / 2)) by ring, Real.cos_two_mul_eq_one_sub]

/-- `cos(2π · (ξ + 1)/2) = cos(πξ + π) = -cos(πξ) = 2s - 1` with `s = sin²(πξ/2)` (Mathlib's
`Real.cos_add_pi`). -/
theorem cos_two_pi_mul_add_one_div_two (ξ : ℝ) :
    Real.cos (2 * π * ((ξ + 1) / 2)) = 2 * Real.sin (π * (ξ / 2)) ^ 2 - 1 := by
  rw [show 2 * π * ((ξ + 1) / 2) = 2 * π * (ξ / 2) + π by ring, Real.cos_add_pi,
    cos_two_pi_mul_div_two]
  ring

/-- `cos(2πξ) = 1 - 8s(1 - s)` with `s = sin²(πξ/2)`: for `x = πξ/2`,
`cos(4x) = 1 - 2 sin²(2x) = 1 - 8 sin²x cos²x` (Mathlib's `Real.cos_two_mul_eq_one_sub` and
`Real.sin_two_mul`), and `cos²x = 1 - sin²x`. -/
theorem cos_two_pi_mul_eq_sin_sq (ξ : ℝ) :
    Real.cos (2 * π * ξ) =
      1 - 8 * Real.sin (π * (ξ / 2)) ^ 2 * (1 - Real.sin (π * (ξ / 2)) ^ 2) := by
  have h := Real.cos_sq' (π * (ξ / 2))
  rw [show 2 * π * ξ = 2 * (2 * (π * (ξ / 2))) by ring, Real.cos_two_mul_eq_one_sub,
    Real.sin_two_mul]
  linear_combination (-8 * Real.sin (π * (ξ / 2)) ^ 2) * h

/-! ### Order two -/

/-- **The transfer operator of order two maps `1` to `4`**: for `N = 2`, `(T 1)(ξ) = 4` for every
`ξ`. With `s = sin²(πξ/2)` and `P_2(y) = 1 + 2y`, `(T 1)(ξ) = (1 + 2s) + (1 + 2(1 - s)) = 4`. -/
theorem transfer_two_one : transfer 2 (fun _ => 1) = fun _ => 4 := by
  ext ξ
  simp only [transfer_eq_eval_sin_sq, daubPoly_two, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  ring

/-- For `N = 2` the iterates of the transfer operator at `1` are the constants `T^n 1 = 4^n`,
since `1` is an eigenfunction with eigenvalue `4` (`Daubechies.transfer_two_one`). -/
theorem iterate_transfer_two_one (n : ℕ) :
    (transfer 2)^[n] (fun _ => 1) = fun _ => 4 ^ n := by
  have h : transfer 2 (fun _ => 1) = (4 : ℝ) • fun _ => (1 : ℝ) := by
    rw [transfer_two_one]
    ext ξ
    simp
  rw [iterate_transfer_eq_pow_smul h]
  ext ξ
  simp

/-- **The growth bound of order two**: `T^n 1 ≤ 1 · 4^n` for `N = 2`, every `n` and every `ξ`,
with equality (`Daubechies.iterate_transfer_two_one`). The exponent `N - log₄ λ` of this bound
is `2 - log₄ 4 = 1` (`Daubechies.two_sub_logb_four_four`). -/
theorem transferGrowth_two : TransferGrowth 2 4 1 :=
  ⟨by norm_num, fun n ξ => by simp [iterate_transfer_two_one]⟩

/-- The exponent `N - log₄ λ` for `N = 2` and `λ = 4`: `2 - log₄ 4 = 1`. -/
theorem two_sub_logb_four_four : (2 : ℝ) - Real.logb 4 4 = 1 := by
  rw [Real.logb_self_eq_one (by norm_num)]
  norm_num

/-! ### Order three -/

/-- **The first eigenfunction of order three**: for `N = 3`,
`T (9 + cos(2π·)) = 9 (9 + cos(2π·))`. With `s = sin²(πξ/2)` and `P_3(y) = 1 + 3y + 6y²`, the
left side at `ξ` is `(1 + 3s + 6s²)(10 - 2s) + (1 + 3(1 - s) + 6(1 - s)²)(8 + 2s)` and the right
side is `9 (10 - 8s(1 - s))`; both equal `90 - 72s(1 - s)`. -/
theorem transfer_three_eigen_one :
    transfer 3 (fun ξ => 9 + Real.cos (2 * π * ξ)) = fun ξ => 9 * (9 + Real.cos (2 * π * ξ)) := by
  ext ξ
  simp only [transfer_eq_eval_sin_sq, daubPoly_three, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  rw [cos_two_pi_mul_div_two ξ, cos_two_pi_mul_add_one_div_two ξ, cos_two_pi_mul_eq_sin_sq ξ]
  ring

/-- **The second eigenfunction of order three**: for `N = 3`,
`T (1 + 3 cos(2π·)) = -4 (1 + 3 cos(2π·))`. With `s = sin²(πξ/2)` the left side at `ξ` is
`(1 + 3s + 6s²)(4 - 6s) + (1 + 3(1 - s) + 6(1 - s)²)(6s - 2)` and the right side is
`-4 (4 - 24s(1 - s))`; both equal `-16 + 96s(1 - s)`. -/
theorem transfer_three_eigen_two :
    transfer 3 (fun ξ => 1 + 3 * Real.cos (2 * π * ξ)) =
      fun ξ => -4 * (1 + 3 * Real.cos (2 * π * ξ)) := by
  ext ξ
  simp only [transfer_eq_eval_sin_sq, daubPoly_three, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  rw [cos_two_pi_mul_div_two ξ, cos_two_pi_mul_add_one_div_two ξ, cos_two_pi_mul_eq_sin_sq ξ]
  ring

/-- **The iterates of order three at `1`**: for `N = 3`, every `n` and every `ξ`,
`(T^n 1)(ξ) = (3/26) 9^n (9 + cos(2πξ)) - (1/26) (-4)^n (1 + 3 cos(2πξ))`. The constant `1` is
the combination `(3/26)(9 + cos(2π·)) - (1/26)(1 + 3 cos(2π·))` of the two eigenfunctions
(`Daubechies.transfer_three_eigen_one`, `Daubechies.transfer_three_eigen_two`), and the iterates
of `T` are linear. -/
theorem iterate_transfer_three_one (n : ℕ) :
    (transfer 3)^[n] (fun _ => 1) = fun ξ => 3 / 26 * 9 ^ n * (9 + Real.cos (2 * π * ξ)) -
      1 / 26 * (-4) ^ n * (1 + 3 * Real.cos (2 * π * ξ)) := by
  have h₁ : transfer 3 (fun ξ => 9 + Real.cos (2 * π * ξ)) =
      (9 : ℝ) • fun ξ => 9 + Real.cos (2 * π * ξ) := by
    rw [transfer_three_eigen_one]
    ext ξ
    simp only [Pi.smul_apply, smul_eq_mul]
  have h₂ : transfer 3 (fun ξ => 1 + 3 * Real.cos (2 * π * ξ)) =
      (-4 : ℝ) • fun ξ => 1 + 3 * Real.cos (2 * π * ξ) := by
    rw [transfer_three_eigen_two]
    ext ξ
    simp only [Pi.smul_apply, smul_eq_mul]
  have h₀ : (fun _ : ℝ => (1 : ℝ)) = (3 / 26 : ℝ) • (fun ξ => 9 + Real.cos (2 * π * ξ)) +
      (-1 / 26 : ℝ) • fun ξ => 1 + 3 * Real.cos (2 * π * ξ) := by
    ext ξ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h₀, iterate_transfer_add, iterate_transfer_smul, iterate_transfer_smul,
    iterate_transfer_eq_pow_smul h₁, iterate_transfer_eq_pow_smul h₂]
  ext ξ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The growth of order three**: `(T^n 1)(ξ) ≤ (17/13) 9^n` for `N = 3`, every `n` and every
`ξ`. In the closed form `Daubechies.iterate_transfer_three_one`, `9 + cos(2πξ) ≤ 10` and
`|(-4)^n (1 + 3 cos(2πξ))| ≤ 4^n · 4 ≤ 9^n · 4`, so `T^n 1 ≤ (30/26 + 4/26) 9^n`. -/
theorem iterate_transfer_three_one_le (n : ℕ) (ξ : ℝ) :
    (transfer 3)^[n] (fun _ => 1) ξ ≤ 17 / 13 * 9 ^ n := by
  simp only [iterate_transfer_three_one]
  have hc := Real.cos_le_one (2 * π * ξ)
  have hc' := Real.neg_one_le_cos (2 * π * ξ)
  have h9 : (0 : ℝ) ≤ 9 ^ n := by positivity
  have h4 : |(-4 : ℝ) ^ n| ≤ 9 ^ n := by
    rw [abs_pow, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h13 : |1 + 3 * Real.cos (2 * π * ξ)| ≤ 4 := abs_le.2 ⟨by linarith, by linarith⟩
  have hprod : -((-4 : ℝ) ^ n * (1 + 3 * Real.cos (2 * π * ξ))) ≤ 9 ^ n * 4 :=
    (neg_le_abs _).trans ((abs_mul _ _).le.trans (mul_le_mul h4 h13 (abs_nonneg _) h9))
  have h9c : 9 ^ n * Real.cos (2 * π * ξ) ≤ 9 ^ n := mul_le_of_le_one_right h9 hc
  linarith

/-- **The growth bound of order three**: `T^n 1 ≤ 2 · 9^n` for `N = 3`, every `n` and every `ξ`
(`Daubechies.iterate_transfer_three_one_le` and `17/13 ≤ 2`). The exponent `N - log₄ λ` of this
bound is `3 - log₄ 9 = 3 - log₂ 3 ≈ 1.415` (`Daubechies.three_sub_logb_four_nine`). -/
theorem transferGrowth_three : TransferGrowth 3 9 2 :=
  ⟨by norm_num, fun n ξ => (iterate_transfer_three_one_le n ξ).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))⟩

/-- The exponent `N - log₄ λ` for `N = 3` and `λ = 9`: `3 - log₄ 9 = 3 - log₂ 3`, since
`log₄ 9 = log 3² / log 2² = 2 log 3 / (2 log 2) = log₂ 3` (Mathlib's `Real.log_pow`). -/
theorem three_sub_logb_four_nine : (3 : ℝ) - Real.logb 4 9 = 3 - Real.logb 2 3 := by
  rw [← Real.log_div_log, ← Real.log_div_log, show (9 : ℝ) = 3 ^ 2 by norm_num,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Real.log_pow,
    mul_div_mul_left _ _ (by norm_num : ((2 : ℕ) : ℝ) ≠ 0)]

end Daubechies
