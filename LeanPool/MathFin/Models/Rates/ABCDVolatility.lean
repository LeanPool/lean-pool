/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# ABCD instantaneous volatility — closed-form integrated variance

The **ABCD parametrization** (Rebonato) is the standard humped
instantaneous-volatility shape used for forward rates / caplets in LIBOR market
models, as a function of the time to maturity `τ`:

  `f(τ) = (a + b·τ) · e^{-c·τ} + d`.

It is a decaying (for `c > 0`) term `(a+bτ)e^{-cτ}` — typically hump-shaped,
rising then decaying — superposed on a floor `d`. The quantity that feeds
cap/caplet and swaption pricing is the **integrated variance** over a window
`[T1, T2]`,

  `∫_{T1}^{T2} f(τ)² dτ`,

an elementary integral of a (quadratic polynomial)×(exponential) plus linear
and constant cross terms. We give the closed-form antiderivative and the
resulting definite-integral formula via the FTC, the same explicit-antiderivative
FTC route as the Vasicek kernel variance integral
(`integral_vasicekIntegratedKernel_sq_eq_sub`, `Models/Rates/VasicekBondPrice.lean`).
Every result below assumes `c ≠ 0` (the antiderivative divides by `c`).

## Main definitions

* `abcdVol`: the ABCD instantaneous volatility `f(τ) = (a + b·τ) · e^{-c·τ} + d`.
* `abcdIntegratedVarAntideriv`: the closed-form antiderivative of `abcdVol a b c d τ ^ 2`.

## Main results

* `hasDerivAt_abcdIntegratedVarAntideriv` — the core calculus fact: its
  derivative is `f(τ)²`, for `c ≠ 0`.
* `abcdVol_sq_integral` — the definite integral
  `∫_{T1}^{T2} f(τ)² dτ = F(T2) - F(T1)` via FTC, for `c ≠ 0`.
* `abcdVol_sq_integral_zero` — the `[0, T]`-window specialization.

## References

* [R. Rebonato, *Modern Pricing of Interest-Rate Derivatives: The LIBOR Market Model and
  Beyond*][Rebonato2002].

## Tags

ABCD volatility, Rebonato, LIBOR market model, integrated variance, caplet volatility,
forward rate volatility, MSC 91G30, JEL E43
-/

@[expose] public section

namespace MathFin

open Real

/-- **ABCD instantaneous volatility**: `f(τ) = (a + b·τ) · e^{-c·τ} + d`. -/
noncomputable def abcdVol (a b c d τ : ℝ) : ℝ := (a + b * τ) * Real.exp (-(c * τ)) + d

/-- Closed-form antiderivative of `abcdVol a b c d τ ^ 2`, obtained by integrating
the three terms of `f² = (a+bτ)²e^{-2cτ} + 2d(a+bτ)e^{-cτ} + d²` separately:
the quadratic-times-exponential antiderivative `-(e^{-2cτ}/2c)·[(a+bτ)² +
b(a+bτ)/c + b²/2c²]`, the linear-times-exponential antiderivative
`-(2d·e^{-cτ}/c)·[(a+bτ) + b/c]`, and `d²τ`. -/
noncomputable def abcdIntegratedVarAntideriv (a b c d τ : ℝ) : ℝ :=
  -(1 / (2 * c)) * (Real.exp (-(2 * c * τ)) *
      ((a + b * τ) * (a + b * τ) + b * (a + b * τ) / c + b ^ 2 / (2 * c ^ 2)))
    + -(2 * d / c) * (Real.exp (-(c * τ)) * ((a + b * τ) + b / c))
    + d ^ 2 * τ

/-- **The core calculus fact**: the closed-form antiderivative differentiates
back to `abcdVol a b c d τ ^ 2`, for `c ≠ 0`. -/
theorem hasDerivAt_abcdIntegratedVarAntideriv (a b c d τ : ℝ) (hc : c ≠ 0) :
    HasDerivAt (abcdIntegratedVarAntideriv a b c d) (abcdVol a b c d τ ^ 2) τ := by
  have h_lin : HasDerivAt (fun τ : ℝ ↦ a + b * τ) b τ := by
    have hbτ : HasDerivAt (fun τ : ℝ ↦ b * τ) b τ := by
      simpa using (hasDerivAt_id τ).const_mul b
    simpa using hbτ.const_add a
  have h_exp2c : HasDerivAt (fun τ : ℝ ↦ Real.exp (-(2 * c * τ)))
      (Real.exp (-(2 * c * τ)) * -(2 * c)) τ := by
    have h2cτ : HasDerivAt (fun τ : ℝ ↦ 2 * c * τ) (2 * c) τ := by
      simpa using (hasDerivAt_id τ).const_mul (2 * c)
    simpa using h2cτ.neg.exp
  have h_expc : HasDerivAt (fun τ : ℝ ↦ Real.exp (-(c * τ)))
      (Real.exp (-(c * τ)) * -c) τ := by
    have hcτ : HasDerivAt (fun τ : ℝ ↦ c * τ) c τ := by
      simpa using (hasDerivAt_id τ).const_mul c
    simpa using hcτ.neg.exp
  -- `P(τ) = (a+bτ)² + b(a+bτ)/c + b²/2c²`, the bracket of the quadratic term.
  have h_P : HasDerivAt
      (fun τ : ℝ ↦ (a + b * τ) * (a + b * τ) + b * (a + b * τ) / c + b ^ 2 / (2 * c ^ 2))
      (b * (a + b * τ) + (a + b * τ) * b + b * b / c) τ := by
    have h1 : HasDerivAt (fun τ : ℝ ↦ (a + b * τ) * (a + b * τ))
        (b * (a + b * τ) + (a + b * τ) * b) τ := h_lin.mul h_lin
    have h2 : HasDerivAt (fun τ : ℝ ↦ b * (a + b * τ) / c) (b * b / c) τ :=
      (h_lin.const_mul b).div_const c
    exact (h1.add h2).add_const (b ^ 2 / (2 * c ^ 2))
  -- `Q(τ) = (a+bτ) + b/c`, the bracket of the linear term.
  have h_Q : HasDerivAt (fun τ : ℝ ↦ (a + b * τ) + b / c) b τ := h_lin.add_const (b / c)
  have h_prod1 : HasDerivAt
      (fun τ : ℝ ↦ Real.exp (-(2 * c * τ)) *
        ((a + b * τ) * (a + b * τ) + b * (a + b * τ) / c + b ^ 2 / (2 * c ^ 2)))
      (Real.exp (-(2 * c * τ)) * -(2 * c) *
          ((a + b * τ) * (a + b * τ) + b * (a + b * τ) / c + b ^ 2 / (2 * c ^ 2))
        + Real.exp (-(2 * c * τ)) * (b * (a + b * τ) + (a + b * τ) * b + b * b / c)) τ :=
    h_exp2c.mul h_P
  have h_prod2 : HasDerivAt
      (fun τ : ℝ ↦ Real.exp (-(c * τ)) * ((a + b * τ) + b / c))
      (Real.exp (-(c * τ)) * -c * ((a + b * τ) + b / c) + Real.exp (-(c * τ)) * b) τ :=
    h_expc.mul h_Q
  have h_F1 := h_prod1.const_mul (-(1 / (2 * c)))
  have h_F2 := h_prod2.const_mul (-(2 * d / c))
  have h_F3 : HasDerivAt (fun τ : ℝ ↦ d ^ 2 * τ) (d ^ 2) τ := by
    simpa using (hasDerivAt_id τ).const_mul (d ^ 2)
  have h_total := (h_F1.add h_F2).add h_F3
  refine h_total.congr_deriv ?_
  have he2 : Real.exp (-(2 * c * τ)) = Real.exp (-(c * τ)) * Real.exp (-(c * τ)) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold abcdVol
  rw [he2]
  field_simp
  ring

/-- **ABCD integrated variance over `[T1, T2]`**, via the FTC, for `c ≠ 0`:
`∫_{T1}^{T2} f(τ)² dτ = F(T2) - F(T1)`, `F = abcdIntegratedVarAntideriv`. -/
theorem abcdVol_sq_integral (a b c d T1 T2 : ℝ) (hc : c ≠ 0) :
    ∫ τ in T1..T2, abcdVol a b c d τ ^ 2
      = abcdIntegratedVarAntideriv a b c d T2 - abcdIntegratedVarAntideriv a b c d T1 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun τ _ ↦ hasDerivAt_abcdIntegratedVarAntideriv a b c d τ hc)
  apply Continuous.intervalIntegrable
  unfold abcdVol
  fun_prop

/-- **The `[0, T]`-window specialization** (`c ≠ 0`), the usual "total integrated variance
to maturity `T`" used in caplet/swaption calibration. -/
theorem abcdVol_sq_integral_zero (a b c d T : ℝ) (hc : c ≠ 0) :
    ∫ τ in (0 : ℝ)..T, abcdVol a b c d τ ^ 2
      = abcdIntegratedVarAntideriv a b c d T - abcdIntegratedVarAntideriv a b c d 0 :=
  abcdVol_sq_integral a b c d 0 T hc

end MathFin
