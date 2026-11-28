/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.Numeraire

/-!
# The T-forward measure — the zero-coupon bond as numéraire

The **T-forward measure** `Q^T` is the pricing measure obtained by taking the
zero-coupon bond `P(·, T)` maturing at `T` as the numéraire, instead of the money
market. Its defining property is that the **forward price is a `Q^T`-martingale**:
for any traded claim,

  `P(0, T) · 𝔼^{Q^T}[X] = 𝔼^Q[X / B_T]`,

with `B` the bank account and `P(0, T) = 𝔼^Q[1/B_T]` the bond price. In the constant-rate
model this gives `𝔼^{Q^T}[S_T] = S_0 / P(0, T) = F(0, T)`.

This is the natural next instance of the change-of-numéraire engine
(`Pricing/Numeraire`), after the stock numéraire and the exchange-option
`S²`-numéraire. Reading off the engine's slots for the bond numéraire against the
bank-account reference: the bond pays one unit at maturity, so `N_T = P(T, T) = 1`, with
`N_0 = P(0, T) = 𝔼^Q[1/B_T]` and `B_0 = 1`. This is the one `T`-forward measure of the
library: the Hull–White `S`-forward measure (`Models/Rates/TimingAdjustment`), the nominal
forward measure of the inflation swap (`Models/Rates/Inflation`) and the constant-rate case
below are all `forwardMeasure Q B` for their bank accounts `B`. It has no model in it, only
the numéraire change, so it lives in `Pricing/` beside `Numeraire`; the Wiener-represented bank
accounts are in `Pricing/WienerIntegralForwardMeasure.lean`.

## Honest scope

In the **constant-rate** world the bond `P(t, T) = e^{−r(T−t)}` is deterministic,
so the density `dQ^T/dQ = (N_T·B_0)/(N_0·B_T) = e^{rT}/e^{rT} = 1` and `Q^T = Q`
coincides with the risk-neutral measure — the forward-price identity below then
reduces to the familiar `𝔼^Q[S_T] = S_0·e^{rT}`. The *construction* and the
change-of-numéraire identity are stated for a general bank account and carry over verbatim
to a stochastic short rate (where `Q^T ≠ Q`); only the concrete constant-rate instance is
degenerate.

## Main definitions

* `forwardMeasure`: the `T`-forward measure `Q^T` for a bank account with terminal value `B`,
  the change-of-numéraire measure with the zero-coupon bond as numéraire (`N_T = 1`,
  `N_0 = 𝔼^Q[1/B]`, `B_0 = 1`).

## Main results

* `forwardMeasure_isProbabilityMeasure` — `Q^T` is a probability measure.
* `forwardMeasure_price` — the bond-numéraire change-of-measure identity
  `P(0,T)·𝔼^{Q^T}[X] = 𝔼^Q[X/B_T]`.
* `forwardMeasure_expected_spot` — `𝔼^{Q^T}[S_T] = S_0·e^{rT}` from the EMM property,
  at the constant bank account `e^{rT}`.
* `futuresForwardBasis_of_integral_mul_exp_neg` — the numéraire step of the futures–forward
  basis, for any law satisfying the covariance identity.

## Tags

T-forward measure, change of numéraire, zero-coupon bond numéraire,
risk-neutral measure, bond as numeraire, MSC 91G30, JEL G13, JEL E43
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **T-forward measure** `Q^T` for the bank account `B` (its terminal value `B_T`): the
change-of-numéraire measure with the zero-coupon bond `P(·, T)` as numéraire, `N_T = 1`,
`N_0 = P(0, T) = 𝔼^Q[1/B_T]`, against the reference `B_T`, `B_0 = 1`. Its density is
`dQ^T/dQ = (1/B_T)/P(0,T)`. It is a probability measure only when `B > 0` and `1/B` is
integrable (`forwardMeasure_isProbabilityMeasure`); when `1/B` is not integrable, `∫ 1/B` is the
Bochner junk value `0` and this is not a price measure. -/
noncomputable def forwardMeasure (Q : Measure Ω) (B : Ω → ℝ) : Measure Ω :=
  numeraireMeasure Q B (fun _ ↦ (1 : ℝ)) 1 (∫ ω, 1 / B ω ∂Q)

/-- The integral `P(0, T) = 𝔼[1/B_T]` of a positive integrable discount factor is positive. -/
lemma integral_one_div_pos {Q : Measure Ω} [IsProbabilityMeasure Q] {B : Ω → ℝ}
    (hB : ∀ ω, 0 < B ω) (hint : Integrable (fun ω ↦ 1 / B ω) Q) :
    0 < ∫ ω, 1 / B ω ∂Q := by
  rw [integral_pos_iff_support_of_nonneg (fun ω ↦ (one_div_pos.2 (hB ω)).le) hint]
  have : Function.support (fun ω ↦ 1 / B ω) = Set.univ :=
    Set.eq_univ_of_forall fun ω ↦ (one_div_pos.2 (hB ω)).ne'
  rw [this, measure_univ]
  exact zero_lt_one

/-- **The T-forward measure is a probability measure**: the normalisation
`𝔼^Q[N_T/B_T] = N_0/B_0` reads `𝔼^Q[1/B_T] = P(0,T)`, which is the definition of `P(0,T)`.
This is the one probability lemma behind every forward measure of the library. (Equivalence with
`Q` is `numeraireMeasure_isEquivProbMeasure`, not proved here.) -/
theorem forwardMeasure_isProbabilityMeasure {Q : Measure Ω} [IsProbabilityMeasure Q]
    {B : Ω → ℝ} (hB : ∀ ω, 0 < B ω) (hint : Integrable (fun ω ↦ 1 / B ω) Q) :
    IsProbabilityMeasure (forwardMeasure Q B) :=
  numeraireMeasure_isProbabilityMeasure (fun _ ↦ one_pos) hB one_pos
    (integral_one_div_pos hB hint) hint (div_one _).symm

/-- **The bond-numéraire change of measure**: `P(0,T)·𝔼^{Q^T}[X] = 𝔼^Q[X/B_T]`.
Directly the change-of-numéraire theorem with the bond slots `N_T = 1`, `N_0 = P(0,T)`,
`B_0 = 1` (no integrability hypothesis needed). -/
theorem forwardMeasure_price {Q : Measure Ω} {B : Ω → ℝ} (X : Ω → ℝ)
    (hBmeas : Measurable B) (hB : ∀ ω, 0 < B ω) (hP0 : 0 < ∫ ω, 1 / B ω ∂Q) :
    (∫ ω, 1 / B ω ∂Q) * ∫ ω, X ω ∂(forwardMeasure Q B) = ∫ ω, X ω / B ω ∂Q := by
  unfold forwardMeasure
  simpa using changeOfNumeraire (Q := Q) (BT := B) (NT := fun _ ↦ (1 : ℝ)) (B0 := 1)
    (N0 := ∫ ω, 1 / B ω ∂Q) X measurable_const hBmeas (fun _ ↦ one_pos) hB zero_le_one hP0

/-- **The forward price is the `Q^T`-expectation of the spot**: at the constant bank account
`e^{rT}` and given the EMM property `𝔼^Q[e^{−rT}·S_T] = S_0`, one has
`𝔼^{Q^T}[S_T] = S_0·e^{rT} = S_0/P(0,T)` — the no-arbitrage forward price. -/
theorem forwardMeasure_expected_spot {Q : Measure Ω} [IsProbabilityMeasure Q] (S_0 r T : ℝ)
    (X : Ω → ℝ) (hEMM : ∫ ω, Real.exp (-(r * T)) * X ω ∂Q = S_0) :
    ∫ ω, X ω ∂(forwardMeasure Q fun _ ↦ Real.exp (r * T)) = S_0 * Real.exp (r * T) := by
  have hp := forwardMeasure_price (Q := Q) X (B := fun _ ↦ Real.exp (r * T))
    measurable_const (fun _ ↦ Real.exp_pos _)
    (by simp only [integral_const, probReal_univ, one_smul]; positivity)
  simp only [integral_const, probReal_univ, one_smul, ← Real.exp_neg,
    div_eq_mul_inv] at hp
  have hEMM' : ∫ ω, X ω * Real.exp (-(r * T)) ∂Q = S_0 := by
    rw [← hEMM]; exact integral_congr_ae (ae_of_all _ fun ω ↦ mul_comm _ _)
  rw [hEMM'] at hp
  have he : Real.exp (-(r * T)) * Real.exp (r * T) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (Real.exp (r * T)) * hp
    - (∫ ω, X ω ∂(forwardMeasure Q fun _ ↦ Real.exp (r * T))) * he

section FuturesForward

variable {μ : Measure Ω}

/-- **The numéraire step of the futures–forward basis, for any law.** Let the bank account be
`e^{Y}` and pass to its `T`-forward measure (`forwardMeasure μ e^{Y}`, the measure of the bond
that pays `1`, worth `𝔼[e^{−Y}]` today). If a payoff `V` satisfies the covariance identity
`𝔼[V·e^{−Y}] = 𝔼[V]·𝔼[e^{−Y}]·e^{−c}` (hypothesis `hcov`), then

  `𝔼^Q[V] = 𝔼^{Q^T}[V] · e^{c}`.

`MathFin.forwardMeasure_price` plus `hcov`. The Gaussian content enters only through `hcov`:
`futuresForwardBasis_gaussian` supplies it from two independent drivers and
`integral_exp_mul_wienerIntegralLp_eq_forwardMeasure` from the Wiener representation of a
short-rate model. -/
theorem futuresForwardBasis_of_integral_mul_exp_neg {V Y : Ω → ℝ} (c : ℝ)
    (hY : Measurable Y) (hN₀ : 0 < ∫ ω, Real.exp (-Y ω) ∂μ)
    (hcov : ∫ ω, V ω * Real.exp (-Y ω) ∂μ
      = (∫ ω, V ω ∂μ) * (∫ ω, Real.exp (-Y ω) ∂μ) * Real.exp (-c)) :
    ∫ ω, V ω ∂μ
      = (∫ ω, V ω ∂(forwardMeasure μ fun ω ↦ Real.exp (Y ω))) * Real.exp c := by
  have hinv : (fun ω ↦ 1 / Real.exp (Y ω)) = fun ω ↦ Real.exp (-Y ω) := by
    funext ω; rw [one_div, Real.exp_neg]
  have h := forwardMeasure_price (Q := μ) V hY.exp (fun ω ↦ Real.exp_pos _) (by rwa [hinv])
  have hc : (fun ω ↦ V ω / Real.exp (Y ω)) = fun ω ↦ V ω * Real.exp (-Y ω) := by
    funext ω; rw [Real.exp_neg, div_eq_mul_inv]
  rw [hc, hcov, hinv] at h
  have h' : ∫ ω, V ω ∂(forwardMeasure μ fun ω ↦ Real.exp (Y ω))
      = (∫ ω, V ω ∂μ) * Real.exp (-c) :=
    mul_left_cancel₀ hN₀.ne' (h.trans (by ring))
  rw [h', mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end FuturesForward

end MathFin
