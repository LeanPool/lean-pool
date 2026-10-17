/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# FlowArithmetic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Deterministic scalar arithmetic for the diffusivity flow

This module is deterministic scalar-arithmetic infrastructure for the Section
3.4 diffusivity-propagation assembly.  It contains only inequalities between
real numbers: the two logarithmic decay estimates that convert a `|log γ|`
inflation into a `γ`-power gain, the elementary square-root power comparison,
and the two-sided squeeze produced by a small relative error.

Every hypothesis of every statement below is an explicit input binder chosen
for the arithmetic at hand; none of them is a source premise of a frozen
theorem, and no model, probability space, or analytic producer is referenced.

## Main statements

* `sqrt_mul_sq_abs_log_le`: `√γ |log γ|² ≤ 16` on `(0, 1]`.
* `mul_sq_abs_log_le`: `γ |log γ|² ≤ 16 √γ` on `(0, 1]`.
* `sqrt_mul_abs_log_le`: `√γ |log γ| ≤ 4 √(√γ)` on `(0, 1]`.
* `sqrt_le_inv_pow_five`: `γ ≤ (E⁻¹)¹⁰` gives `√γ ≤ (E⁻¹)⁵`.
* `sq_sandwich_of_relative_error`: `|x − √P| ≤ θ x` with `θ ≤ 1/4` gives `P/2 ≤
  x² ≤ 2P`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity

noncomputable section

/-! ### The logarithmic decay estimates -/

/-- The elementary bound `|log γ| ≤ 4 (√(√γ))⁻¹` on `(0, 1]`.

It is `log x ≤ x − 1` evaluated at `x = (√(√γ))⁻¹`, together with
`log γ = 4 log (√(√γ))`.  No numeric tactic sees a logarithm. -/
private theorem abs_log_le_four_mul_inv_sqrt_sqrt {gamma : ℝ}
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    |Real.log gamma| ≤ 4 * (Real.sqrt (Real.sqrt gamma))⁻¹ := by
  have hs : 0 < Real.sqrt gamma := Real.sqrt_pos.mpr hgamma
  have hu : 0 < Real.sqrt (Real.sqrt gamma) := Real.sqrt_pos.mpr hs
  have hlogu : Real.log gamma = 4 * Real.log (Real.sqrt (Real.sqrt gamma)) := by
    rw [Real.log_sqrt hs.le, Real.log_sqrt hgamma.le]
    ring
  have hlogle : -Real.log (Real.sqrt (Real.sqrt gamma))
      ≤ (Real.sqrt (Real.sqrt gamma))⁻¹ := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hu)
    rw [Real.log_inv] at h
    linarith only [h]
  have habs : |Real.log gamma| = -Real.log gamma :=
    abs_of_nonpos (Real.log_nonpos hgamma.le hgamma1)
  rw [habs, hlogu]
  linarith only [hlogle]

/-- `√γ |log γ|² ≤ 16` for `0 < γ ≤ 1`.

The constant `16` is the honest one: writing `u = √(√γ)` the bound
`|log γ| ≤ 4 u⁻¹` gives `√γ |log γ|² ≤ u² · 16 u⁻² = 16`. -/
theorem sqrt_mul_sq_abs_log_le {gamma : ℝ} (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    Real.sqrt gamma * |Real.log gamma| ^ 2 ≤ 16 := by
  have hs : 0 < Real.sqrt gamma := Real.sqrt_pos.mpr hgamma
  have hu : 0 < Real.sqrt (Real.sqrt gamma) := Real.sqrt_pos.mpr hs
  have huu : Real.sqrt (Real.sqrt gamma) * Real.sqrt (Real.sqrt gamma)
      = Real.sqrt gamma := Real.mul_self_sqrt hs.le
  have hbound := abs_log_le_four_mul_inv_sqrt_sqrt hgamma hgamma1
  have hsq : |Real.log gamma| ^ 2 ≤ (4 * (Real.sqrt (Real.sqrt gamma))⁻¹) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hbound 2
  have huinv : ((Real.sqrt (Real.sqrt gamma))⁻¹) ^ 2 = (Real.sqrt gamma)⁻¹ := by
    rw [inv_pow, pow_two, huu]
  have hkey : Real.sqrt gamma * (4 * (Real.sqrt (Real.sqrt gamma))⁻¹) ^ 2 = 16 := by
    rw [mul_pow, huinv]
    calc Real.sqrt gamma * (4 ^ 2 * (Real.sqrt gamma)⁻¹)
        = 16 * (Real.sqrt gamma * (Real.sqrt gamma)⁻¹) := by ring
      _ = 16 := by rw [mul_inv_cancel₀ (ne_of_gt hs), mul_one]
  calc Real.sqrt gamma * |Real.log gamma| ^ 2
      ≤ Real.sqrt gamma * (4 * (Real.sqrt (Real.sqrt gamma))⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hs.le
    _ = 16 := hkey

/-- `γ |log γ|² ≤ 16 √γ` for `0 < γ ≤ 1`: the previous bound multiplied by
`√γ`.  This is the shape consumed by the `γ`-threshold arithmetic, where the
factor `√γ` is the one later traded against a power of `E⁻¹`. -/
theorem mul_sq_abs_log_le {gamma : ℝ} (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    gamma * |Real.log gamma| ^ 2 ≤ 16 * Real.sqrt gamma := by
  have hs : 0 < Real.sqrt gamma := Real.sqrt_pos.mpr hgamma
  have hss : Real.sqrt gamma * Real.sqrt gamma = gamma := Real.mul_self_sqrt hgamma.le
  have hbase := sqrt_mul_sq_abs_log_le hgamma hgamma1
  have hmul := mul_le_mul_of_nonneg_left hbase hs.le
  calc gamma * |Real.log gamma| ^ 2
      = Real.sqrt gamma * (Real.sqrt gamma * |Real.log gamma| ^ 2) := by
        rw [← mul_assoc, hss]
    _ ≤ Real.sqrt gamma * 16 := hmul
    _ = 16 * Real.sqrt gamma := by ring

/-- `√γ |log γ| ≤ 4 √(√γ)` for `0 < γ ≤ 1`.

This is the form in which the amplitude `√γ |log γ|` is absorbed: the residual
`√(√γ)` is a quarter power of `γ` and is later traded against `E⁻²`. -/
theorem sqrt_mul_abs_log_le {gamma : ℝ} (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    Real.sqrt gamma * |Real.log gamma| ≤ 4 * Real.sqrt (Real.sqrt gamma) := by
  have hs : 0 < Real.sqrt gamma := Real.sqrt_pos.mpr hgamma
  have hu : 0 < Real.sqrt (Real.sqrt gamma) := Real.sqrt_pos.mpr hs
  have huu : Real.sqrt (Real.sqrt gamma) * Real.sqrt (Real.sqrt gamma)
      = Real.sqrt gamma := Real.mul_self_sqrt hs.le
  have hbound := abs_log_le_four_mul_inv_sqrt_sqrt hgamma hgamma1
  have hkey : Real.sqrt gamma * (4 * (Real.sqrt (Real.sqrt gamma))⁻¹)
      = 4 * Real.sqrt (Real.sqrt gamma) := by
    calc Real.sqrt gamma * (4 * (Real.sqrt (Real.sqrt gamma))⁻¹)
        = 4 * (Real.sqrt gamma * (Real.sqrt (Real.sqrt gamma))⁻¹) := by ring
      _ = 4 * (Real.sqrt (Real.sqrt gamma) * Real.sqrt (Real.sqrt gamma) *
            (Real.sqrt (Real.sqrt gamma))⁻¹) := by rw [huu]
      _ = 4 * (Real.sqrt (Real.sqrt gamma) *
            (Real.sqrt (Real.sqrt gamma) * (Real.sqrt (Real.sqrt gamma))⁻¹)) := by ring
      _ = 4 * Real.sqrt (Real.sqrt gamma) := by
          rw [mul_inv_cancel₀ (ne_of_gt hu), mul_one]
  calc Real.sqrt gamma * |Real.log gamma|
      ≤ Real.sqrt gamma * (4 * (Real.sqrt (Real.sqrt gamma))⁻¹) :=
        mul_le_mul_of_nonneg_left hbound hs.le
    _ = 4 * Real.sqrt (Real.sqrt gamma) := hkey

/-! ### Square roots of inverse powers -/

/-- From `γ ≤ (E⁻¹)¹⁰` and `0 < E`, `√γ ≤ (E⁻¹)⁵`. -/
theorem sqrt_le_inv_pow_five {E gamma : ℝ} (hE : 0 < E)
    (hgammaE : gamma ≤ (E⁻¹) ^ 10) : Real.sqrt gamma ≤ (E⁻¹) ^ 5 := by
  have h1 : Real.sqrt gamma ≤ Real.sqrt ((E⁻¹) ^ 10) := Real.sqrt_le_sqrt hgammaE
  have h2 : (E⁻¹ : ℝ) ^ 10 = ((E⁻¹) ^ 5) ^ 2 := by ring
  rw [h2, Real.sqrt_sq (pow_nonneg (inv_nonneg.mpr hE.le) 5)] at h1
  exact h1

/-! ### The two-sided squeeze from a small relative error -/

/-- **Squared sandwich from a relative error.**  If `x > 0`, `P > 0`, and `x`
deviates from `√P` by at most `θ x` with `0 ≤ θ ≤ 1/4`, then `x²` and `P` agree
within a factor `2`.

The numerology is exactly `(1 − θ)² ≥ 9/16` and `(1 + θ)² ≤ 25/16 < 2`; both
slack factors `16/9` and `25/16` are below `2`, so the stated constants are
honest with room to spare. -/
theorem sq_sandwich_of_relative_error {x P theta : ℝ}
    (hx : 0 < x) (hP : 0 < P) (htheta : 0 ≤ theta) (htheta' : theta ≤ 1 / 4)
    (hdev : |x - Real.sqrt P| ≤ theta * x) :
    P / 2 ≤ x ^ 2 ∧ x ^ 2 ≤ 2 * P := by
  have hbnn : 0 ≤ Real.sqrt P := Real.sqrt_nonneg P
  have hbsq : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP.le
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdev
  have hupper : Real.sqrt P ≤ (1 + theta) * x := by linarith only [hlo]
  have hlower : (1 - theta) * x ≤ Real.sqrt P := by linarith only [hhi]
  have hlower_nn : 0 ≤ (1 - theta) * x :=
    mul_nonneg (by linarith only [htheta']) hx.le
  have hsq_up : Real.sqrt P ^ 2 ≤ ((1 + theta) * x) ^ 2 :=
    pow_le_pow_left₀ hbnn hupper 2
  have hsq_lo : ((1 - theta) * x) ^ 2 ≤ Real.sqrt P ^ 2 :=
    pow_le_pow_left₀ hlower_nn hlower 2
  rw [hbsq] at hsq_up hsq_lo
  have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have hcoef_up : (1 + theta) ^ 2 ≤ 25 / 16 := by nlinarith only [htheta, htheta']
  have hcoef_lo : (9 : ℝ) / 16 ≤ (1 - theta) ^ 2 := by nlinarith only [htheta, htheta']
  have hup : P ≤ 25 / 16 * x ^ 2 := by
    have hstep : ((1 + theta) * x) ^ 2 = (1 + theta) ^ 2 * x ^ 2 := by ring
    have := mul_le_mul_of_nonneg_right hcoef_up hx2
    linarith only [hsq_up, hstep.le, hstep.ge, this]
  have hlo2 : (9 : ℝ) / 16 * x ^ 2 ≤ P := by
    have hstep : ((1 - theta) * x) ^ 2 = (1 - theta) ^ 2 * x ^ 2 := by ring
    have := mul_le_mul_of_nonneg_right hcoef_lo hx2
    linarith only [hsq_lo, hstep.le, hstep.ge, this]
  exact ⟨by linarith only [hup, hx2], by linarith only [hlo2, hP]⟩

end

end Algsuperdiff.Section3.Provider.Diffusivity
