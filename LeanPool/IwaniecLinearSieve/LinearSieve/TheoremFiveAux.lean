/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.LinearSieve.Defs
public import LeanPool.IwaniecLinearSieve.PrimeSums.Error
import LeanPool.IwaniecLinearSieve.LinearSieve.LemmaEleven
import LeanPool.IwaniecLinearSieve.LinearSieve.TheoremFourAsymp
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Real-variable estimates for [I71, Theorem 5]

With `L = log y`, `λ = log log 3y` (`TheoremFive.lam`) and `ξ = L / λ^{11/5}` (`xi`), this file
collects the "for `y ≥ y₀`" facts used in the proof of Theorem 5:

* `eventually_scalar`: `λ`, `log λ`, `λ^{1/5}` are large, `λ - 1 ≤ log L ≤ λ`, `24 λ ≤ ξ`,
  `16 λ² ≤ L`, `λ/2 ≤ log (ξ/2)`, `4 log λ + c ≤ log ξ ≤ λ`;
* `crude_exponent_le`: the comparison of the crude count of `rosserSet lower y y^{1/(ξ-1)}` with
  `y exp(-ξ log ξ + (3/2) ξ log λ) / (8 L⁴)` ([I71, p. 27]);
* `exists_slack`: the losses `δ(e^{32}, y) (1 + C ξ² pntE(y^{1/ξ})) - 1` of Corollary 3 are at
  most `(log log y)² / (8 L²)`, reusing `TheoremFour.eventually_delta_mul_le`.
-/

@[expose] public section

open Real Filter Topology

namespace IwaniecLinearSieve.TheoremFive

/-- `λ(y) = log log 3y`, the denominator variable of `ξ(y) = log y / λ^{11/5}`. -/
noncomputable def lam (y : ℝ) : ℝ := log (log (3 * y))

theorem xi_eq_lam (y : ℝ) : xi y = log y / lam y ^ (11 / 5 : ℝ) := rfl

theorem tendsto_lam : Tendsto lam atTop atTop := tendsto_log_log_three_mul

/-- `α + β log x ≤ x` for large `x`. -/
theorem eventually_add_mul_log_le (α β : ℝ) : ∀ᶠ x in atTop, α + β * log x ≤ x := by
  have hε : (0 : ℝ) < 1 / (2 * (|β| + 1)) := by positivity
  filter_upwards [isLittleO_log_id_atTop.bound hε, eventually_ge_atTop (2 * α),
    eventually_ge_atTop 1] with x hx hxα hx1
  have hl : 0 ≤ log x := log_nonneg hx1
  rw [norm_of_nonneg hl, id, norm_of_nonneg (by linarith)] at hx
  have h1 : β * log x ≤ |β| * log x := mul_le_mul_of_nonneg_right (le_abs_self β) hl
  have h2 : |β| * log x ≤ x / 2 := by
    have hq : |β| / (|β| + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc |β| * log x ≤ |β| * (1 / (2 * (|β| + 1)) * x) := by gcongr
      _ = |β| / (|β| + 1) * (x / 2) := by field_simp
      _ ≤ 1 * (x / 2) := by gcongr
      _ = x / 2 := one_mul _
  linarith

theorem one_lt_log_three : 1 < log 3 := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  linarith [exp_one_lt_d9]

theorem lam_pos {y : ℝ} (hy : 1 < y) : 0 < lam y := by
  have h3 : log 3 + log y = log (3 * y) := (log_mul (by norm_num) (by linarith)).symm
  have := log_pos hy
  exact log_pos (by linarith [one_lt_log_three])

/-- `log ξ = log L - (11/5) log λ`. -/
theorem log_xi_eq {y : ℝ} (hy : 1 < y) : log (xi y) = log (log y) - 11 / 5 * log (lam y) := by
  rw [xi_eq_lam, log_div (log_pos hy).ne' (rpow_pos_of_pos (lam_pos hy) _).ne',
    log_rpow (lam_pos hy)]

theorem xi_pos {y : ℝ} (hy : 1 < y) : 0 < xi y :=
  div_pos (log_pos hy) (rpow_pos_of_pos (lam_pos hy) _)

/-- The scalar facts about `L = log y`, `λ = lam y` and `ξ = xi y` used for Theorem 5, valid for
large `y`; `c ≥ 100` is a free threshold. -/
theorem eventually_scalar (c : ℝ) (hc : 100 ≤ c) : ∀ᶠ y in atTop,
    3 ≤ y ∧ c ≤ log (lam y) ∧ c ≤ lam y ^ (1 / 5 : ℝ) ∧ c ≤ lam y ∧
    log (log y) ≤ lam y ∧ lam y - 1 ≤ log (log y) ∧
    24 * lam y ≤ xi y ∧ 16 * lam y ^ 2 ≤ log y ∧ lam y / 2 ≤ log (xi y / 2) ∧
    4 * log (lam y) + c ≤ log (xi y) ∧ log (xi y) ≤ lam y := by
  filter_upwards [eventually_ge_atTop 3, tendsto_lam.eventually (eventually_ge_atTop c),
    (tendsto_log_atTop.comp tendsto_lam).eventually (eventually_ge_atTop c),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp tendsto_lam).eventually
      (eventually_ge_atTop c),
    tendsto_lam.eventually (eventually_add_mul_log_le (c + 10) 8)] with y hy3 h1 h2 h3 h4
  simp only [Function.comp] at h2 h3
  have hy : 1 < y := by linarith
  have hL : 1 < log y := by
    have := log_le_log (by norm_num) hy3; linarith [one_lt_log_three]
  have hL0 : 0 < log y := by linarith
  have hlam := lam_pos hy
  have h3y : log (3 * y) = log 3 + log y := log_mul (by norm_num) (by linarith)
  have ha : 0 ≤ log (lam y) := by linarith
  -- `log L ≤ λ ≤ log L + 1`
  have hℓ1 : log (log y) ≤ lam y := by
    unfold lam; exact log_le_log hL0 (by rw [h3y]; linarith [one_lt_log_three])
  have hℓ2 : lam y - 1 ≤ log (log y) := by
    have hle : log (3 * y) ≤ exp 1 * log y := by
      have : log 3 ≤ log y := log_le_log (by norm_num) hy3
      have : 2 ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
      rw [h3y]; nlinarith
    have := log_le_log (by rw [h3y]; linarith [one_lt_log_three]) hle
    rw [log_mul (exp_pos 1).ne' hL0.ne', log_exp] at this
    unfold lam; linarith
  have hlogξ := log_xi_eq hy
  have hξ := xi_pos hy
  have hl2 : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hl16 : log 16 ≤ 15 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)]
  have hl24 : log 24 ≤ 23 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 24)]
  refine ⟨hy3, h2, h3, h1, hℓ1, hℓ2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← log_le_log_iff (by positivity) hξ, log_mul (by norm_num) hlam.ne']
    linarith
  · have h := (log_le_log_iff (by positivity) hL0).1 (by
      rw [log_mul (by norm_num) (by positivity), log_pow]; push_cast
      linarith : log (16 * lam y ^ 2) ≤ log (log y))
    exact h
  · rw [log_div hξ.ne' (by norm_num)]
    linarith
  · linarith
  · linarith

/-! ### The crude part ([I71, p. 27]) -/

/-- The comparison at the bottom of [I71, p. 27], in exponential form: with `ℓ = log L`,
`8 L⁴ (1 + e^{L + 2ξ - L/λ} + 2 e^{L - ξ log ξ + ξ a + 5ξ}) ≤ e^{L - ξ log ξ + (3/2) ξ a}`
(here `a = log λ`), under the scalar facts of `eventually_scalar`. -/
theorem crude_exponent_le {L ℓ lam ξ a : ℝ} (hL : 0 < L) (hℓ : ℓ = log L) (hℓlam : ℓ ≤ lam)
    (hlam : 100 ≤ lam) (ha : 12 ≤ a) (hxilam : 4 * (ξ * lam ^ 2) ≤ L) (h24 : 24 * lam ≤ ξ)
    (h16 : 16 * lam ^ 2 ≤ L) (hlogξ : log ξ ≤ lam) :
    8 * L ^ 4 * (1 + exp (L + 2 * ξ - L / lam) + 2 * exp (L - ξ * log ξ + ξ * a + 5 * ξ)) ≤
      exp (L - ξ * log ξ + 3 / 2 * ξ * a) := by
  have hlam0 : 0 < lam := by linarith
  have hξ0 : 0 < ξ := by linarith
  have h8 : 8 * L ^ 4 = exp (log 8 + 4 * ℓ) := by
    rw [exp_add, exp_log (by norm_num), hℓ,
      show (4 : ℝ) * log L = log (L ^ 4) by rw [log_pow]; norm_num, exp_log (by positivity)]
  have hl3 : log 3 ≤ 2 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hl8 : log 8 ≤ 7 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)]
  have hl2 : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  set T := L - ξ * log ξ + 3 / 2 * ξ * a with hT
  have h3 : exp T = 3 * exp (T - log 3) := by
    rw [exp_sub, exp_log (by norm_num)]; field_simp
  -- `ξ log ξ + 2 ξ ≤ L / (2λ)` and `8 + 4λ ≤ L / (2λ)`
  have hLl : ξ * log ξ + 2 * ξ ≤ L / (2 * lam) := by
    rw [le_div_iff₀ (by positivity)]
    have : ξ * log ξ ≤ ξ * lam := mul_le_mul_of_nonneg_left hlogξ hξ0.le
    nlinarith
  have hLm : 8 + 4 * lam ≤ L / (2 * lam) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hLlam : L / lam ≤ L := div_le_self hL.le (by linarith)
  have hξa : 0 ≤ ξ * a := by positivity
  have e1 : 8 * L ^ 4 ≤ exp (T - log 3) := by
    rw [h8, exp_le_exp, hT]
    have : L / lam = 2 * (L / (2 * lam)) := by field_simp
    nlinarith
  have e2 : 8 * L ^ 4 * exp (L + 2 * ξ - L / lam) ≤ exp (T - log 3) := by
    rw [h8, ← exp_add, exp_le_exp, hT]
    have : L / lam = 2 * (L / (2 * lam)) := by field_simp
    nlinarith
  have e3 : 8 * L ^ 4 * (2 * exp (L - ξ * log ξ + ξ * a + 5 * ξ)) ≤ exp (T - log 3) := by
    rw [h8, mul_left_comm, ← exp_add, ← exp_log (by norm_num : (0 : ℝ) < 2), ← exp_add,
      exp_le_exp, hT]
    have : 6 * ξ ≤ 1 / 2 * ξ * a := by nlinarith
    nlinarith
  rw [h3]
  nlinarith

/-! ### The slack ([I71, (4.2), (4.6)]) -/

/-- `(1 + x)^p ≤ e^{p x}` for `x ≥ 0`, `p ≥ 0`. -/
theorem one_add_rpow_le_exp {x p : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p) : (1 + x) ^ p ≤ exp (p * x) := by
  rw [rpow_def_of_pos (by linarith), exp_le_exp, mul_comm]
  gcongr
  linarith [log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)]

/-- For every `C ≥ 0` and large `y`, with `s₀ = e^{32}` and `ℓ = log log y`:
`δ(s₀, y) (1 + C ξ² pntE(y^{1/ξ})) - 1 ≤ ℓ² / (8 L²)` and `ℓ ≥ 1`. -/
theorem exists_slack (C : ℝ) (hC : 0 ≤ C) : ∃ y₀ : ℝ, ∀ y ≥ y₀,
    delta (exp 32) y * (1 + C * xi y ^ 2 * pntE (y ^ (1 / xi y))) - 1 ≤
      log (log y) ^ 2 / (8 * log y ^ 2) ∧ 1 ≤ log (log y) := by
  apply eventually_atTop.1
  filter_upwards [TheoremFour.eventually_delta_mul_le C hC,
    (tendsto_log_atTop.comp tendsto_log_atTop).eventually (eventually_ge_atTop (1 : ℝ))]
    with y hslack hloglog
  exact ⟨sub_le_iff_le_add'.2 hslack, hloglog⟩

end IwaniecLinearSieve.TheoremFive
