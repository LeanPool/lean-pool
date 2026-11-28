/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.BreedenLitzenberger
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# LSV leverage-posterior core

A local-stochastic-volatility (LSV) model is calibrated to the local-volatility surface by the
condition `L²(t,K) · E[v_t | S_t = K] = σ_loc²(t,K)`: the leverage function `L` is pinned by the
posterior mean of the stochastic variance given the state (Gyöngy's mimicking theorem; the
particle calibration of Guyon and Henry-Labordère). We follow S. Bagaria, *Notes on Fixed Income
Derivative Pricing* (lecture notes), ch. 11, where this is eq. 11.1; the equation, example and
calculation numbers below (Thm 11.2, Ex. 11.1–11.2, Calc 11.3) are that chapter's.

The conditioning step itself is Mathlib's: `E[v | σ(S)]` is a Borel function of the state by
`stronglyMeasurable_condExp` and the Doob–Dynkin lemma
`StronglyMeasurable.exists_eq_measurable_comp`, and `L²(S)` comes out of the conditional
expectation by `condExp_mul_of_stronglyMeasurable_left`. Those lemmas are not applied to an LSV
model in this file. This file proves the algebraic and analytic core behind the condition, with no
stochastic-process hypotheses:

* the pinned product and its extremes (`lsv_pinned_product`, eq. 11.6): `m = 1` recovers
  pure local vol, `m = σ_loc²` (with `σ_loc > 0`) switches the leverage off (Ex. 11.1);
* the coin-toss λ-dial family (§11.4 / Calc 11.3): branch variances `29/400 ∓ λ/20` keep
  `E[v^λ]` pinned at `29/400` for every λ; at the λ = 0 endpoint, read as the constant
  posterior `m = 29/400`, the squared leverage at `σ_loc = 1/4` is `25/29` (the exact square of
  the chapter's "0.93");
* the coin-toss posterior of Ex. 11.2 as exact inequalities and limits: ATM posterior on the
  high branch `< 1/2`; ATM posterior variance `m(F)` below the unconditional mean; posterior
  on the high branch → 1 in both wings (the log-density ratio is a downward parabola in
  `ln(K/F)`); and nonconstancy of the posterior variance `m` on the positive strikes;
* the posterior read off option prices (`cointossPhi_eq_deriv_deriv_bsV`,
  `cointossPostHi_eq_strike_convexity`, `cointossM_eq_strike_convexity`): by
  Breeden–Litzenberger (`breedenLitzenberger`), each branch density is the second strike
  derivative of that branch's Black–Scholes call price, so the Bayes weights and the posterior
  variance are ratios of call-price convexities.

## Scope

* Not proved here: Thm 11.2's *iff* content, that the leverage-defined model reprices the
  market (it needs Gyöngy's mimicking theorem with flow uniqueness, which
  `GyongyMimicry.gyongy_mimicry_gated` takes as a hypothesis, weak existence on the
  local-vol side, the Dupire surface formula on a non-Gaussian carrier, and the McKean–Vlasov
  existence question, which is not settled in general); §11.3's grid and particle machinery;
  every decimal figure of the chapter's tables (22.9%, 26.9%, 0.98, 1.09 → 0.71), since the
  statements here are exact. Here `cointossM` and `cointossPostHi` are defined by their Bayes
  formulas; that `cointossM ∘ S_T` is the conditional expectation `E[v | σ(S_T)]` on the
  two-branch mixture, and `cointossPostHi ∘ S_T` the conditional probability of the high
  branch, is proved in `Models/StochVol/LSVPosteriorConditionalExpectation.lean`
  (`cointossM_comp_ae_eq_condExp`, `cointossPostHi_comp_ae_eq_condExp`).

## Main definitions

* `cointossVLo`, `cointossVHi`: the branch variances `29/400 ∓ λ/20` of the coin-toss example.
* `cointossPhi`: the branch density, the Black–Scholes lognormal terminal density with spot `F`,
  zero rate and unit maturity at volatility `σ`, evaluated at the strike `K`.
* `cointossPostHi`: the posterior weight of the high branch at strike `K` under equal priors,
  `φ_hi(K)/(φ_lo(K) + φ_hi(K))`.
* `cointossM`: the posterior mean of the variance at strike `K`,
  `(v_lo φ_lo(K) + v_hi φ_hi(K))/(φ_lo(K) + φ_hi(K))`.

## Main results

* `lsv_pinned_product`: for a posterior variance `m > 0`, the leverage `σ_loc / √m` satisfies
  `L² · m = σ_loc²`.
* `lsv_leverage_of_m_one`, `lsv_leverage_switches_off`: if `m = 1` the leverage is `σ_loc`; if
  `σ_loc > 0` and `m = σ_loc²` the leverage is `1`.
* `cointoss_family_mean`: for every `λ`, the two branch variances average to `29/400`.
* `cointoss_endpoint_l0_pinned`, `cointoss_endpoint_l0_quarter`: at `λ = 0` the pinned product holds
  with `m = 29/400`, and at `σ_loc = 1/4` the squared leverage is `25/29`.
* `cointoss_posterior_atm_lt_half`: at the money, for `σ_lo < σ_hi`, the posterior weight of the
  high branch is below `1/2`.
* `cointossM_atm_lt_uncond`: at the money the posterior variance is below the unconditional mean
  `(v_lo + v_hi)/2`.
* `cointoss_posterior_wing_limit_atTop`, `cointoss_posterior_wing_limit_atZero`: the posterior
  weight of the high branch tends to `1` as the strike tends to `∞` and to `0⁺`.
* `cointossM_wing_limit_atTop`: the posterior variance tends to `v_hi` as `K → ∞`.
* `cointossM_nonconstant`: the posterior variance is not constant in the strike.
* `cointossPostHi_eq_strike_convexity`, `cointossM_eq_strike_convexity`: the posterior weight and
  posterior variance are ratios of second strike derivatives of the branch call prices
  `bsV K 0 σ F 1`.

## References

* [I. Gyöngy, *Mimicking the one-dimensional marginal distributions of processes having an Itô
  differential*][Gyongy1986].
* [J. Guyon and P. Henry-Labordère, *Being particular about calibration*][GuyonHenryLabordere2012].
* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 11.

## Tags

local stochastic volatility, leverage function, Gyöngy mimicking, particle calibration,
conditional variance, Dupire calibration, MSC 91G20, MSC 60J60, JEL G13
-/

@[expose] public section

namespace MathFin.LSV

open MeasureTheory ProbabilityTheory Filter Topology

/-! ## The pinned product and its extremes -/

/-- **The pinned product (eq. 11.6 shape), at one strike.** The leverage of an LSV model
is `L = σ_loc / √m`, where `m` is the posterior mean of the stochastic variance at the strike;
the defining product `L² · m = σ_loc²` is an identity as soon as `m > 0`. The λ = 0
endpoint (`cointoss_endpoint_l0_pinned`) is this telescope at `m = 29/400`. -/
theorem lsv_pinned_product (σ_loc m : ℝ) (hm : 0 < m) :
    (σ_loc / Real.sqrt m) ^ 2 * m = σ_loc ^ 2 := by
  rw [div_pow, Real.sq_sqrt hm.le, div_mul_cancel₀ _ hm.ne']

/-- **First extreme (Ex. 11.1): `m = 1` ⇒ `L = σ_loc`.** With no stochastic content at a
strike the leverage there is the local volatility itself — pure local vol. -/
theorem lsv_leverage_of_m_one (σ_loc m : ℝ) (h : m = 1) :
    σ_loc / Real.sqrt m = σ_loc := by
  simp [h]

/-- **Second extreme (Ex. 11.1): for `σ_loc > 0`, `m = σ_loc²` ⇒ `L = 1`.** When the stochastic
part already fits the surface, `E[v | S = K] = σ_loc²(K)` and the leverage "switches itself off". -/
theorem lsv_leverage_switches_off (σ_loc m : ℝ) (hσ : 0 < σ_loc) (h : m = σ_loc ^ 2) :
    σ_loc / Real.sqrt m = 1 := by
  rw [h, Real.sqrt_sq hσ.le, div_self hσ.ne']

/-! ## The coin-toss λ-dial family (§11.4, Calc 11.3) -/

/-- The λ-dial branch variances of Calc 11.3, against a flat 25% local-volatility surface: a
low and a high branch, `v_lo(λ) = 29/400 − λ/20` and `v_hi(λ) = 29/400 + λ/20`. At `λ = 1`
these are the Ex. 11.2 coin toss `9/400 = 0.15²` and `49/400 = 0.35²`; at `λ = 0` the dial
collapses to the single deterministic variance `29/400 = (0.269…)²`. -/
noncomputable def cointossVLo (lam : ℝ) : ℝ := 29 / 400 - lam / 20

/-- The high branch of the λ-dial (see `cointossVLo`). -/
noncomputable def cointossVHi (lam : ℝ) : ℝ := 29 / 400 + lam / 20

/-- **λ-invariance of the branch mean:** for every λ, the two-branch average of the variance
is exactly `29/400`. The dial moves variance between the branches without moving the mean —
in the chapter's words, "λ changes the answer, does not change the calibration, and therefore
cannot be determined by it". Only the invariance of the mean is proved; calibration is not
modelled here. -/
theorem cointoss_family_mean (lam : ℝ) :
    (cointossVLo lam + cointossVHi lam) / 2 = 29 / 400 := by
  unfold cointossVLo cointossVHi; ring

/-- The low branch stays positive across the whole dial `λ ∈ [0, 1]` (at `λ = 1` it is
`9/400 > 0`). -/
theorem cointossVLo_pos (lam : ℝ) (h1 : lam ≤ 1) : 0 < cointossVLo lam := by
  unfold cointossVLo; linarith

/-- The high branch is positive for every nonnegative λ (at `λ = 0` it is `29/400 > 0`). -/
theorem cointossVHi_pos (lam : ℝ) (h0 : 0 ≤ lam) : 0 < cointossVHi lam := by
  unfold cointossVHi; linarith

/-- **The λ = 0 endpoint in ratio form (Calc 11.3):** the dial collapses to a single
deterministic variance `m ≡ E[v⁰] = 29/400`, so the squared leverage is the flat ratio
`σ_loc² / (29/400)`. The statement is the algebraic identity at `m = 29/400`; that the posterior
`cointossM` equals `29/400` at `λ = 0` is not stated. -/
theorem cointoss_endpoint_l0_sq (σ_loc : ℝ) :
    (σ_loc / Real.sqrt (29 / 400)) ^ 2 = σ_loc ^ 2 / (29 / 400) := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 29 / 400)]

/-- The λ = 0 endpoint in pinned-product form: the constant posterior `29/400` telescopes
with the squared leverage to `σ_loc²`. -/
theorem cointoss_endpoint_l0_pinned (σ_loc : ℝ) :
    (σ_loc / Real.sqrt (29 / 400)) ^ 2 * (29 / 400) = σ_loc ^ 2 :=
  lsv_pinned_product σ_loc _ (by norm_num)

/-- **The exact square of the chapter's flat "0.93":** at `σ_loc = 1/4` the λ = 0 squared
leverage is `L⁰² = 25/29` (Calc 11.3's `L⁰ ≈ 0.93` is the square root of this rational). -/
theorem cointoss_endpoint_l0_quarter :
    ((1:ℝ) / 4 / Real.sqrt (29 / 400)) ^ 2 = 25 / 29 := by
  rw [cointoss_endpoint_l0_sq]; norm_num

/-! ## The coin-toss posterior (Ex. 11.2) -/

/-- The branch density of the coin-toss example: the Black–Scholes lognormal terminal
density with spot `F`, zero rate, unit maturity and branch volatility `σ`, evaluated at
strike `K` — Ex. 11.2's `φ_c(K)` (`MathFin.lognormalTerminalPDF` at `S_0 = F, r = 0,
T = 1`; branch means the coin came up `σ = σ_lo` or `σ = σ_hi`). -/
noncomputable def cointossPhi (F σ K : ℝ) : ℝ :=
  lognormalTerminalPDF F 0 σ 1 K

/-- The branch density is strictly positive wherever `σ, K > 0` (the Gaussian tail is
positive and the Jacobian `K σ √T` is positive). -/
theorem cointossPhi_pos {F σ K : ℝ} (hσ : 0 < σ) (hK : 0 < K) :
    0 < cointossPhi F σ K := by
  unfold cointossPhi lognormalTerminalPDF
  rw [Real.sqrt_one]
  exact div_pos (gaussianPDFReal_pos 0 1 _ one_ne_zero) (by positivity)

/-- At the money the `d₂` of a branch density collapses to `−σ/2` (`r = 0`, `T = 1`,
`K = S_0 = F`). -/
theorem cointoss_bsd2_atm {F σ : ℝ} (hF : 0 < F) (hσ : 0 < σ) :
    bsd2 F F 0 σ 1 = -σ / 2 := by
  have h1 : Real.log (F / F) = 0 := by rw [div_self hF.ne', Real.log_one]
  rw [bsd2_eq hσ one_pos, h1, Real.sqrt_one, mul_one, zero_add, zero_sub]
  field_simp

/-- The ATM branch density in product form (for `F, σ > 0`): the Gaussian normalization constant
times the Jacobian telescope to `exp(−σ²/8)`. (Auxiliary engine for the ATM comparisons; the
`√(2π)` is the normalization constant of `gaussianPDFReal 0 1`.) -/
theorem cointossPhi_atm_prod {F σ : ℝ} (hF : 0 < F) (hσ : 0 < σ) :
    cointossPhi F σ F * (F * σ) * Real.sqrt (2 * Real.pi) =
      Real.exp (-(σ ^ 2 / 8)) := by
  unfold cointossPhi lognormalTerminalPDF
  rw [cointoss_bsd2_atm hF hσ, Real.sqrt_one]
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
  have hFs : (F * σ : ℝ) ≠ 0 := mul_ne_zero hF.ne' hσ.ne'
  have hS : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  rw [div_mul_cancel₀ _ hFs, mul_comm (Real.sqrt (2 * Real.pi))⁻¹, inv_mul_cancel_right₀ hS]
  congr 1
  ring

/-- **The ATM density ratio** — the engine of every ATM comparison that follows: for `F > 0`
and positive branch volatilities, `φ_lo(F)/φ_hi(F) = (σ_hi/σ_lo) · exp((σ_hi² − σ_lo²)/8)`.
For `σ_lo < σ_hi` this exceeds `1` (`cointossPhi_atm_lt`). -/
theorem cointossPhi_ratio_atm {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hσhi : 0 < σ_hi) :
    cointossPhi F σ_lo F / cointossPhi F σ_hi F =
      (σ_hi / σ_lo) * Real.exp ((σ_hi ^ 2 - σ_lo ^ 2) / 8) := by
  have hEdiv : Real.exp (-(σ_lo ^ 2 / 8)) / Real.exp (-(σ_hi ^ 2 / 8)) =
      Real.exp ((σ_hi ^ 2 - σ_lo ^ 2) / 8) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [← hEdiv, ← cointossPhi_atm_prod hF hlo, ← cointossPhi_atm_prod hF hσhi]
  field_simp

/-- **At the money, the narrower (low-vol) branch is the denser branch:** `φ_hi(F) < φ_lo(F)`
— the two-line chapter fact `ln(σ_lo/σ_hi) < 0 < (σ_hi²−σ_lo²)/8`, in exact form. -/
theorem cointossPhi_atm_lt {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) :
    cointossPhi F σ_hi F < cointossPhi F σ_lo F := by
  have hσhi : 0 < σ_hi := hlo.trans hhi
  rw [← one_lt_div (cointossPhi_pos hσhi hF), cointossPhi_ratio_atm hF hlo hσhi]
  refine one_lt_mul_of_le_of_lt ((one_lt_div hlo).2 hhi).le ?_
  rw [Real.one_lt_exp_iff]
  have hs2 : σ_lo ^ 2 < σ_hi ^ 2 := by nlinarith
  linarith

/-- The posterior weight of the high branch at strike `K` under equal branch priors —
Ex. 11.2's Bayes ratio `P(hi | S_T = K) = φ_hi(K)/(φ_lo(K) + φ_hi(K))`. -/
noncomputable def cointossPostHi (F σ_lo σ_hi K : ℝ) : ℝ :=
  cointossPhi F σ_hi K / (cointossPhi F σ_lo K + cointossPhi F σ_hi K)

/-- **The ATM posterior on the high branch is below one half** (the strict inequality behind the
chapter's table entry `P(hi | S_T = F) = 0.30`; the decimal itself is not proved).
Engine: `cointossPhi_atm_lt` plus the positivity of both densities. -/
theorem cointoss_posterior_atm_lt_half {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) :
    cointossPostHi F σ_lo σ_hi F < 1 / 2 := by
  have hden : 0 < cointossPhi F σ_lo F + cointossPhi F σ_hi F :=
    add_pos (cointossPhi_pos hlo hF) (cointossPhi_pos (hlo.trans hhi) hF)
  unfold cointossPostHi
  rw [div_lt_iff₀ hden]
  linarith [cointossPhi_atm_lt hF hlo hhi]

/-- The posterior mean of the variance at strike `K`,
`m(K) = (v_lo φ_lo(K) + v_hi φ_hi(K))/(φ_lo(K) + φ_hi(K))` — the input of eq. 11.1's
leverage `L = σ_loc/√m`. -/
noncomputable def cointossM (F σ_lo σ_hi v_lo v_hi K : ℝ) : ℝ :=
  (v_lo * cointossPhi F σ_lo K + v_hi * cointossPhi F σ_hi K) /
    (cointossPhi F σ_lo K + cointossPhi F σ_hi K)

/-- **The ATM posterior variance sits below the unconditional mean:** for `F, σ_lo > 0`,
`σ_lo < σ_hi` and `v_lo < v_hi`, `m(F) < (v_lo + v_hi)/2`. For `σ_loc > 0` and `m(F) > 0`
this transfers to the leverage, `σ_loc/√m(F) > σ_loc/√((v_lo + v_hi)/2)`; that transfer is
not stated here. Engine: the pinned algebra `(v_hi − v_lo)(φ_lo(F) − φ_hi(F)) > 0`. -/
theorem cointossM_atm_lt_uncond {F σ_lo σ_hi v_lo v_hi : ℝ} (hF : 0 < F)
    (hlo : 0 < σ_lo) (hhi : σ_lo < σ_hi) (hvhi : v_lo < v_hi) :
    cointossM F σ_lo σ_hi v_lo v_hi F < (v_lo + v_hi) / 2 := by
  have hden : 0 < cointossPhi F σ_lo F + cointossPhi F σ_hi F :=
    add_pos (cointossPhi_pos hlo hF) (cointossPhi_pos (hlo.trans hhi) hF)
  have halt := cointossPhi_atm_lt hF hlo hhi
  unfold cointossM
  rw [div_lt_div_iff₀ hden zero_lt_two]
  nlinarith [mul_pos (sub_pos.mpr hvhi) (sub_pos.mpr halt)]

/-- For `r = 0`, `T = 1`, `K > 0`: the branch `d₂` is `−(x + σ²/2)/σ` in the log-moneyness
variable `x = ln(K/F)`. (Auxiliary to the wing limits.) -/
theorem cointoss_bsd2_log {F σ K : ℝ} (hF : 0 < F) (hσ : 0 < σ) (hK : 0 < K) :
    bsd2 F K 0 σ 1 = (-Real.log (K / F) - σ ^ 2 / 2) / σ := by
  have h1 : Real.log (F / K) = -Real.log (K / F) := by
    rw [Real.log_div hF.ne' hK.ne', Real.log_div hK.ne' hF.ne']
    ring
  rw [bsd2_eq hσ one_pos, h1, Real.sqrt_one, mul_one, zero_sub]
  ring

/-- **The log-density ratio is a quadratic in log-moneyness** — the engine of both wing
limits: `log(φ_lo/φ_hi) = b − a·(ln(K/F))²` with `a = (σ_hi² − σ_lo²)/(2σ_lo²σ_hi²)` and
intercept `b = ln(σ_hi/σ_lo) + (σ_hi² − σ_lo²)/8`, for `F, K > 0` and positive branch vols.
For `σ_lo < σ_hi`, `a > 0` (a downward parabola), so `|ln(K/F)| → ∞` drives `φ_lo/φ_hi` to
`0`, i.e. the posterior piles onto the wide branch. -/
theorem cointossPhi_ratio_log {F σ_lo σ_hi K : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hσhi : 0 < σ_hi) (hK : 0 < K) :
    Real.log (cointossPhi F σ_lo K / cointossPhi F σ_hi K) =
      (Real.log (σ_hi / σ_lo) + (σ_hi ^ 2 - σ_lo ^ 2) / 8) -
        (σ_hi ^ 2 - σ_lo ^ 2) / (2 * σ_lo ^ 2 * σ_hi ^ 2) * (Real.log (K / F)) ^ 2 := by
  -- the Gaussian ratio of the two branch densities
  have hgr (d₁ d₂ : ℝ) :
      gaussianPDFReal 0 1 d₁ / gaussianPDFReal 0 1 d₂ = Real.exp ((d₂ ^ 2 - d₁ ^ 2) / 2) := by
    have hstep : gaussianPDFReal 0 1 d₁ / gaussianPDFReal 0 1 d₂ =
        Real.exp (-(d₁ ^ 2 / 2)) / Real.exp (-(d₂ ^ 2 / 2)) := by
      simp only [gaussianPDFReal, sub_zero]
      push_cast
      rw [mul_div_mul_left _ _ (by positivity : (Real.sqrt (2 * Real.pi * (1:ℝ)))⁻¹ ≠ 0)]
      norm_num
      simp only [neg_div]
    rw [hstep, ← Real.exp_sub]
    congr 1
    ring
  -- the strike-ratio assembly (the `K` Jacobians cancel between the branches)
  have hφratio : cointossPhi F σ_lo K / cointossPhi F σ_hi K =
      (σ_hi / σ_lo) * Real.exp (((Real.log (K / F) + σ_hi ^ 2 / 2) ^ 2 / σ_hi ^ 2
        - (Real.log (K / F) + σ_lo ^ 2 / 2) ^ 2 / σ_lo ^ 2) / 2) := by
    have hdiv (g₁ g₂ a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
        (g₁ / a) / (g₂ / b) = (g₁ / g₂) * (b / a) := by
      field_simp
    unfold cointossPhi lognormalTerminalPDF
    rw [cointoss_bsd2_log hF hlo hK, cointoss_bsd2_log hF hσhi hK, Real.sqrt_one, mul_one,
      mul_one,
      hdiv _ _ _ _ (mul_ne_zero hK.ne' hlo.ne') (mul_ne_zero hK.ne' hσhi.ne'), hgr]
    have hscalar : (K * σ_hi) / (K * σ_lo) = σ_hi / σ_lo := by
      rw [mul_div_mul_left _ _ hK.ne']
    rw [hscalar, mul_comm (Real.exp _)]
    congr 2
    ring
  -- take the log of the assembled ratio
  have hQ : (((Real.log (K / F) + σ_hi ^ 2 / 2) ^ 2 / σ_hi ^ 2
      - (Real.log (K / F) + σ_lo ^ 2 / 2) ^ 2 / σ_lo ^ 2) / 2) =
      (σ_hi ^ 2 - σ_lo ^ 2) / 8 -
        (σ_hi ^ 2 - σ_lo ^ 2) / (2 * σ_lo ^ 2 * σ_hi ^ 2) * (Real.log (K / F)) ^ 2 := by
    have h1 : (σ_lo ^ 2 : ℝ) ≠ 0 := pow_ne_zero _ hlo.ne'
    have h2 : (σ_hi ^ 2 : ℝ) ≠ 0 := pow_ne_zero _ hσhi.ne'
    field_simp
    ring
  rw [hφratio, Real.log_mul (div_pos hσhi hlo).ne' (Real.exp_pos _).ne', Real.log_exp, hQ]
  ring

/-- The posterior weight rewrites as `1/(1 + φ_lo/φ_hi)` — the form the wing limits feed
into. -/
theorem cointoss_posterior_eq {F σ_lo σ_hi K : ℝ} (hlo : 0 < σ_lo) (hσhi : 0 < σ_hi)
    (hK : 0 < K) :
    cointossPostHi F σ_lo σ_hi K =
      1 / (1 + cointossPhi F σ_lo K / cointossPhi F σ_hi K) := by
  have hφlo : 0 < cointossPhi F σ_lo K := cointossPhi_pos hlo hK
  have hφhi : 0 < cointossPhi F σ_hi K := cointossPhi_pos hσhi hK
  unfold cointossPostHi
  field_simp
  ring

/-- The shared engine of both wing limits: whenever the squared log-moneyness diverges to
`+∞` along a filter on which strikes are eventually positive, the posterior weight on the
wide branch tends to `1`. (Private; the two public forms below instantiate `l`.) -/
private theorem cointoss_posterior_limit_aux {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) {l : Filter ℝ}
    (hu2 : Tendsto (fun K : ℝ ↦ (Real.log (K / F)) ^ 2) l atTop)
    (hpos : ∀ᶠ K in l, (0:ℝ) < K) :
    Tendsto (cointossPostHi F σ_lo σ_hi) l (𝓝 1) := by
  have hσhi : 0 < σ_hi := hlo.trans hhi
  set a : ℝ := (σ_hi ^ 2 - σ_lo ^ 2) / (2 * σ_lo ^ 2 * σ_hi ^ 2)
  set b : ℝ := Real.log (σ_hi / σ_lo) + (σ_hi ^ 2 - σ_lo ^ 2) / 8
  have hA : 0 < a := div_pos (by nlinarith) (by positivity)
  -- the linear tail `b - a · t` drives `atBot`
  have hlin : Tendsto (fun t : ℝ ↦ b - a * t) atTop atBot := by
    simpa only [sub_eq_add_neg, neg_mul, id_eq] using
      tendsto_atBot_add_const_left _ b (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.2 hA))
  -- so the log-ratio tends to atBot, and exponentiating gives the density ratio → 0
  have hlogR : Tendsto (fun K : ℝ ↦
      Real.log (cointossPhi F σ_lo K / cointossPhi F σ_hi K)) l atBot :=
    (hlin.comp hu2).congr' (by
      filter_upwards [hpos] with K hK
      exact (cointossPhi_ratio_log hF hlo hσhi hK).symm)
  have hR : Tendsto (fun K : ℝ ↦ cointossPhi F σ_lo K / cointossPhi F σ_hi K) l (𝓝 0) := by
    refine (Real.tendsto_exp_atBot.comp hlogR).congr' ?_
    filter_upwards [hpos] with K hK
    exact Real.exp_log (div_pos (cointossPhi_pos hlo hK) (cointossPhi_pos hσhi hK))
  -- and `1/(1 + ·)` is continuous at `0` with value `1`
  have hcont : Tendsto (fun t : ℝ ↦ 1 / (1 + t)) (𝓝 0) (𝓝 1) := by
    have h : Tendsto (fun t : ℝ ↦ 1 / (1 + t)) (𝓝 0) (𝓝 ((1:ℝ) / ((1:ℝ) + 0))) :=
      (tendsto_const_nhds (x := (1:ℝ))).div
        ((tendsto_const_nhds (x := (1:ℝ))).add tendsto_id) (by norm_num)
    simpa using h
  exact (hcont.comp hR).congr' (by
    filter_upwards [hpos] with K hK
    exact (cointoss_posterior_eq hlo hσhi hK).symm)

/-- **Upper wing limit (Ex. 11.2's table, `K → ∞`):** the posterior weight on the wide
branch tends to `1` — the qualitative content behind the chapter's `0.96` at `K = 160`
(the finite-strike decimal itself is not proved). The log-density ratio is a downward
parabola in `ln(K/F)`, so the branch densities separate exponentially in the wing. -/
theorem cointoss_posterior_wing_limit_atTop {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) :
    Tendsto (cointossPostHi F σ_lo σ_hi) atTop (𝓝 1) := by
  have hu : Tendsto (fun K : ℝ ↦ Real.log (K / F)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const hF)
  exact cointoss_posterior_limit_aux hF hlo hhi ((tendsto_pow_atTop two_ne_zero).comp hu)
    (eventually_gt_atTop 0)

/-- **Lower wing limit (Ex. 11.2's table, `K → 0⁺`):** the posterior weight on the wide
branch tends to `1` in the lower wing as well — the qualitative content behind the
chapter's `0.98` at `K = 60` (the decimal itself is not proved). Same parabola, read
at `ln(K/F) → −∞`. -/
theorem cointoss_posterior_wing_limit_atZero {F σ_lo σ_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) :
    Tendsto (cointossPostHi F σ_lo σ_hi) (𝓝[>] 0) (𝓝 1) := by
  have hx : Tendsto (fun K : ℝ ↦ Real.log (K / F)) (𝓝[>] 0) atBot := by
    refine (tendsto_atBot_add_const_right _ (-Real.log F) Real.tendsto_log_nhdsGT_zero).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with K (hK : 0 < K)
    rw [Real.log_div hK.ne' hF.ne', sub_eq_add_neg]
  have hsq : Tendsto (fun x : ℝ ↦ x ^ 2) atBot atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_neg_atBot_atTop).congr fun x ↦ neg_sq x
  exact cointoss_posterior_limit_aux hF hlo hhi (hsq.comp hx) self_mem_nhdsWithin

/-- For positive strikes the posterior mean is the flat branch mix
`m(K) = v_lo + (v_hi − v_lo) · P(hi | K)` — the leverage-relevant reading of the posterior
weight. -/
theorem cointossM_eq_of_pos {F σ_lo σ_hi v_lo v_hi K : ℝ} (hlo : 0 < σ_lo) (hσhi : 0 < σ_hi)
    (hK : 0 < K) :
    cointossM F σ_lo σ_hi v_lo v_hi K =
      v_lo + (v_hi - v_lo) * cointossPostHi F σ_lo σ_hi K := by
  have hφlo : 0 < cointossPhi F σ_lo K := cointossPhi_pos hlo hK
  have hφhi : 0 < cointossPhi F σ_hi K := cointossPhi_pos hσhi hK
  unfold cointossM cointossPostHi
  field_simp
  ring

/-- **The posterior variance's upper-wing limit:** `m(K) → v_hi` as `K → ∞` — the posterior
mean of the variance converges to the wide branch in the upper wing (the analogous lower-wing
statement, `m(K) → v_hi` as `K → 0⁺`, would follow the same way from
`cointoss_posterior_wing_limit_atZero`; it is not stated here). -/
theorem cointossM_wing_limit_atTop {F σ_lo σ_hi v_lo v_hi : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : σ_lo < σ_hi) :
    Tendsto (fun K : ℝ ↦ cointossM F σ_lo σ_hi v_lo v_hi K) atTop (𝓝 v_hi) := by
  have h := ((cointoss_posterior_wing_limit_atTop hF hlo hhi).const_mul (v_hi - v_lo)).const_add
    v_lo
  rw [mul_one, add_sub_cancel] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with K hK
  exact (cointossM_eq_of_pos hlo (hlo.trans hhi) hK).symm

/-- At `K = 0` both branch densities are `0` (`x / 0 = 0`), so `cointossM` is `0` there. -/
theorem cointossM_zero (F σ_lo σ_hi v_lo v_hi : ℝ) :
    cointossM F σ_lo σ_hi v_lo v_hi 0 = 0 := by
  simp [cointossM, cointossPhi, lognormalTerminalPDF]

/-- **The posterior variance is not constant** for `F, σ_lo > 0`, `σ_lo < σ_hi` and
`v_lo < v_hi` (Ex. 11.2's punchline: the posterior `m` is a
genuine function of the strike; for a flat `σ_loc > 0` and `m > 0` the leverage `σ_loc/√m`
is then not flat either, a transfer not stated here).
If `m` were constant on the (economically meaningful) positive strikes it would equal its own
upper-wing limit `v_hi`; but at the money `m(F) < (v_lo + v_hi)/2 < v_hi`. The quantifier is
restricted to `K > 0`: `cointossM F σ_lo σ_hi v_lo v_hi 0 = 0` by the `x / 0 = 0` convention
(`cointossM_zero`), so an unrestricted `¬ ∃ c, ∀ K, … = c` would hold even for a posterior
that is constant on `(0, ∞)`, and would not capture the intended content. -/
theorem cointossM_nonconstant {F σ_lo σ_hi v_lo v_hi : ℝ} (hF : 0 < F)
    (hlo : 0 < σ_lo) (hhi : σ_lo < σ_hi) (hvhi : v_lo < v_hi) :
    ¬ ∃ c : ℝ, ∀ K : ℝ, 0 < K → cointossM F σ_lo σ_hi v_lo v_hi K = c := by
  rintro ⟨c, hc⟩
  have h : v_hi = c := tendsto_nhds_unique (cointossM_wing_limit_atTop hF hlo hhi)
    (tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with K hK using (hc K hK).symm))
  linarith [cointossM_atm_lt_uncond hF hlo hhi hvhi, hc F hF]

/-! ## The posterior from call prices (Breeden–Litzenberger)

Each branch density `φ_c` is the lognormal density that Breeden–Litzenberger reads off the
second strike derivative of the branch's call price: `φ_c(K) = ∂²_K C_c(K)` with
`C_c(K) = bsV K 0 σ_c F 1` (zero rate, unit maturity, so the discount factor is `1`). The Bayes
posterior of Ex. 11.2 is therefore a ratio of call-price convexities, the quantities a
calibration observes. -/

/-- **A branch density is a call-price convexity.** For `F, σ, K > 0`,
`φ_σ(K) = ∂²_K bsV(K, 0, σ, F, 1)`: Breeden–Litzenberger at zero rate and unit maturity. -/
theorem cointossPhi_eq_deriv_deriv_bsV {F σ K : ℝ} (hF : 0 < F) (hσ : 0 < σ) (hK : 0 < K) :
    cointossPhi F σ K = deriv (deriv fun k ↦ bsV k 0 σ F 1) K := by
  rw [(breedenLitzenberger hF hσ hK one_pos).deriv]
  simp [cointossPhi]

/-- **The posterior weight of the high branch from call prices.** For `F, K > 0` and positive
branch volatilities, `P(hi | S_T = K) = C_hi''(K) / (C_lo''(K) + C_hi''(K))`, where
`C_c(K) = bsV K 0 σ_c F 1`. -/
theorem cointossPostHi_eq_strike_convexity {F σ_lo σ_hi K : ℝ} (hF : 0 < F) (hlo : 0 < σ_lo)
    (hhi : 0 < σ_hi) (hK : 0 < K) :
    cointossPostHi F σ_lo σ_hi K =
      deriv (deriv fun k ↦ bsV k 0 σ_hi F 1) K /
        (deriv (deriv fun k ↦ bsV k 0 σ_lo F 1) K + deriv (deriv fun k ↦ bsV k 0 σ_hi F 1) K) := by
  rw [cointossPostHi, cointossPhi_eq_deriv_deriv_bsV hF hlo hK,
    cointossPhi_eq_deriv_deriv_bsV hF hhi hK]

/-- **The posterior variance from call prices.** For `F, K > 0` and positive branch
volatilities, `m(K) = (v_lo·C_lo''(K) + v_hi·C_hi''(K)) / (C_lo''(K) + C_hi''(K))`. -/
theorem cointossM_eq_strike_convexity {F σ_lo σ_hi v_lo v_hi K : ℝ} (hF : 0 < F)
    (hlo : 0 < σ_lo) (hhi : 0 < σ_hi) (hK : 0 < K) :
    cointossM F σ_lo σ_hi v_lo v_hi K =
      (v_lo * deriv (deriv fun k ↦ bsV k 0 σ_lo F 1) K
          + v_hi * deriv (deriv fun k ↦ bsV k 0 σ_hi F 1) K) /
        (deriv (deriv fun k ↦ bsV k 0 σ_lo F 1) K + deriv (deriv fun k ↦ bsV k 0 σ_hi F 1) K) := by
  rw [cointossM, cointossPhi_eq_deriv_deriv_bsV hF hlo hK,
    cointossPhi_eq_deriv_deriv_bsV hF hhi hK]

/-! ## The posterior as a conditional expectation

On the two-branch mixture space `ℝ ⊕ ℝ` (a standard normal draw on the low or the high branch,
each with probability `1/2`), with terminal price `S_T = F·exp(σ_c z − σ_c²/2)` on branch `c` and
branch variance `v`, the posterior of this file is the conditional expectation:
`cointossM F σ_lo σ_hi v_lo v_hi ∘ S_T =ᵐ E[v | σ(S_T)]`. That theorem, and the matching
statement for `cointossPostHi` as the conditional probability of the high branch, is proved in
`Models/StochVol/LSVPosteriorConditionalExpectation.lean`, which pushes each branch's normal law
forward to the density `cointossPhi F σ_c` on `(0, ∞)` with the library's
`jumpDiffusionIncrementLaw_zero_map_mul_exp` and applies Mathlib's
`ae_eq_condExp_of_forall_setIntegral_eq`. -/

end MathFin.LSV
