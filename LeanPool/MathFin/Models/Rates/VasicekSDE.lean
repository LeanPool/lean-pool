/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.Vasicek
public import Mathlib.Algebra.Order.Star.Real

/-!
# Vasicek SDE terminal-distribution form (stated, not derived) (phase 41)

The pre-existing `Models/Rates/Vasicek.lean` derives only the
**deterministic part** of the Vasicek mean-reverting short-rate model
(the `σ = 0` ODE). This file extends to the **full SDE**

  `dr_t = κ (θ − r_t) dt + σ dB_t`,

whose closed-form solution is

  `r_t = r_0 · e^{−κt} + θ · (1 − e^{−κt}) + σ · ∫_0^t e^{−κ(t−s)} dB_s`.

The Itô integral `∫_0^t e^{−κ(t−s)} dB_s` is of a *deterministic*
integrand, so its law is Gaussian (an Itô integral of a deterministic
integrand is an L² limit of independent Gaussian increments; see the
continuous construction in `Probability/Brownian/Ito/ItoIntegralL2.lean`). The integrand's
L² norm gives the variance:

  `Var = σ² · ∫_0^t e^{−2κ(t−s)} ds = σ² · (1 − e^{−2κt}) / (2κ)`.

Hence under the SDE,

  `r_t ~ N( r_0 · e^{−κt} + θ · (1 − e^{−κt}), σ² · (1 − e^{−2κt}) / (2κ) )`.

This file gives the explicit *terminal-distribution* form, parameterised
by a standard normal `Z`, in the same style as `BSCallHyp`.

## Why this is open now

Phase 36 (simple-process Itô integral) + Phase 32 (BQV identities) +
the deterministic Riemann integral `∫ e^{−2κ(t−s)} ds = (1 − e^{−2κt})/(2κ)`
give the variance computation. The Gaussian-distribution conclusion
follows from the structural fact that Itô integrals of deterministic
integrands are Gaussian (a consequence of the simple-process
construction being a sum of independent Gaussian increments).

## What this file is

A **terminal-distribution-form** hypothesis-and-closed-form pairing, in
the BSCallHyp style. The full SDE-to-distribution derivation is the
content of Phase 41 conceptually; the file states the closed form
explicitly so that downstream consumers can use it without re-deriving.

## Main definitions

* `vasicekSDEMean`: the Vasicek mean `r_0 · e^{−κt} + θ · (1 − e^{−κt})`.
* `vasicekSDEVariance`: the Vasicek variance `σ² · (1 − e^{−2κt}) / (2κ)`.
* `vasicekSDETerminal`: the terminal short rate `mean + √var · Z` as a function of `Z ~ N(0, 1)`.

## Main results

* `vasicekSDE_variance_pos`: positivity of variance for `κ > 0`, `σ ≠ 0`.
* `vasicekSDE_mean_at_zero`: `r_t = r_0` at `t = 0`.

## Tags

Vasicek model, short rate SDE, Ornstein–Uhlenbeck, terminal distribution, Gaussian short rate,
mean reversion, MSC 91G30, MSC 60H10, JEL E43
-/

@[expose] public section

namespace MathFin

open Real

/-- **Vasicek SDE mean**: `r_0 · e^{−κt} + θ · (1 − e^{−κt})`. Identical
to the deterministic-part closed form `vasicekDeterministic`. -/
noncomputable def vasicekSDEMean (r_0 θ κ t : ℝ) : ℝ :=
  r_0 * Real.exp (-(κ * t)) + θ * (1 - Real.exp (-(κ * t)))

/-- The SDE mean is the deterministic closed form `vasicekDeterministic`. -/
theorem vasicekSDEMean_eq_deterministic (r_0 θ κ t : ℝ) :
    vasicekSDEMean r_0 θ κ t = vasicekDeterministic r_0 θ κ t := by
  unfold vasicekSDEMean vasicekDeterministic; ring

/-- **Vasicek SDE variance**: `σ² · (1 − e^{−2κt}) / (2κ)`. The L² norm
of the deterministic integrand `e^{−κ(t−·)}` on `[0, t]` against `dB`,
via the simple-Itô isometry. -/
noncomputable def vasicekSDEVariance (σ κ t : ℝ) : ℝ :=
  σ ^ 2 * (1 - Real.exp (-(2 * κ * t))) / (2 * κ)

/-- **Vasicek SDE terminal distribution**: with `Z ~ N(0, 1)`,
`r_t(Z) = mean + √var · Z` has the Gaussian law `N(mean, var)`. -/
noncomputable def vasicekSDETerminal
    (r_0 θ κ σ t : ℝ) (Z : ℝ) : ℝ :=
  vasicekSDEMean r_0 θ κ t + Real.sqrt (vasicekSDEVariance σ κ t) * Z

/-- **Mean at `t = 0`** equals the initial value `r_0`. -/
lemma vasicekSDE_mean_at_zero (r_0 θ κ : ℝ) :
    vasicekSDEMean r_0 θ κ 0 = r_0 := by
  unfold vasicekSDEMean
  simp

/-- **Variance at `t = 0`** is zero (no diffusion yet). -/
lemma vasicekSDE_variance_at_zero (σ κ : ℝ) (_hκ : κ ≠ 0) :
    vasicekSDEVariance σ κ 0 = 0 := by
  unfold vasicekSDEVariance
  simp

/-- **Variance positivity** for positive `κ, t` and non-zero `σ`: as `2κt
> 0`, `e^{−2κt} < 1`, so the variance numerator `1 − e^{−2κt} > 0`. The
denominator `2κ > 0` and `σ² > 0` (from `σ ≠ 0`) make the whole variance
strictly positive. -/
lemma vasicekSDE_variance_pos (σ κ t : ℝ)
    (hκ : 0 < κ) (ht : 0 < t) (hσ : σ ≠ 0) :
    0 < vasicekSDEVariance σ κ t := by
  unfold vasicekSDEVariance
  have h_κt_pos : 0 < 2 * κ * t := by positivity
  have h_exp_lt : Real.exp (-(2 * κ * t)) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h_num_pos : 0 < 1 - Real.exp (-(2 * κ * t)) := by linarith
  have h_den_pos : 0 < 2 * κ := by linarith
  have h_σ_sq_pos : 0 < σ ^ 2 := by
    rw [sq]
    exact mul_self_pos.mpr hσ
  positivity

/-- **Variance nonnegativity** for `κ > 0`, `t ≥ 0`, any `σ` (no sign hypothesis on `σ`
needed, unlike `vasicekSDE_variance_pos`'s strict form). -/
lemma vasicekSDEVariance_nonneg (σ : ℝ) {κ : ℝ} (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ vasicekSDEVariance σ κ t := by
  unfold vasicekSDEVariance
  have : Real.exp (-(2 * κ * t)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
  positivity

open Filter Topology in
/-- **The long-run variance.** For `κ > 0` the closed-form Vasicek variance
`σ²(1 − e^{−2κt})/(2κ)` tends to `σ²/(2κ)` as `t → ∞` — the variance of the textbook
stationary law; no stationary law is constructed here. -/
theorem tendsto_vasicekSDEVariance_atTop (σ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun t ↦ vasicekSDEVariance σ κ t) atTop (𝓝 (σ ^ 2 / (2 * κ))) := by
  have he : Tendsto (fun t : ℝ ↦ Real.exp (-(2 * κ * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop (by positivity) tendsto_id)
  unfold vasicekSDEVariance
  simpa using ((he.const_sub 1).const_mul (σ ^ 2)).div_const (2 * κ)

end MathFin
