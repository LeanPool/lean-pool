/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.GSRBond
public import LeanPool.MathFin.Models.Rates.HullWhiteBond
public import LeanPool.MathFin.Models.BlackScholes.Put
public import LeanPool.MathFin.Models.Rates.TimingAdjustment

/-!
# Jamshidian: the zero-coupon bond put and the caplet in the Gaussian short-rate models

A put on `P(T₀, T₁)` struck at `k` expiring at `T₀` is worth `P(0, T₀)` times the put's
expectation under the `T₀`-forward measure (`forwardMeasure`, the change of numéraire
`forwardMeasure_price`). In a Gaussian short-rate model the bond is
`P(T₀, T₁) = a·exp(−β r_{T₀})` (`bondPrice_hullWhite`), and `r_{T₀}` stays Gaussian under the
`T₀`-forward measure, its mean shifted by `−Cov(r_{T₀}, ∫₀^{T₀} r)`
(`HullWhite.shortRate_hasLaw_forwardMeasure`; for the two-piece GSR,
`gsrShortRate_hasLaw_forwardMeasure`, both instances of `hasLaw_forwardMeasure_wienerIntegralLp`).
So the bond is lognormal there, and the put is a Black put (`bs_put_formula`) on it:

  `put = k·P(0, T₀)·Φ(−d₂) − P(0, T₁)·Φ(−d₁)`,   `d₁ = (ln(F/k) + s²/2)/s`,   `d₂ = d₁ − s`,

with forward price `F = P(0, T₁)/P(0, T₀)` and `s = B(T₁ − T₀)·sd(r_{T₀})`, the standard
deviation of `ln P(T₀, T₁)`. The forward price needs no computation with the affine coefficients:
it is the mean of the lognormal under `Q^{T₀}` (`discounted_terminal_eq_S0`) and, by the tower
property (`HasBondPrice.integral_discount_mul`), `𝔼^{T₀}[P(T₀, T₁)] = P(0, T₁)/P(0, T₀)`.

* `HasBondPrice.integral_bond_forward` — the forward price of the bond.
* `HasBondPrice.value_bondPut_gaussian` — the put, for a bond that is an exponential of a
  Gaussian under the `T₀`-forward measure.
* `value_bondPut_wiener` — the plumbing once: for an integrated short rate in Wiener
  representation `R T = M T + c T·∫₀ᵀ g_T dB`, the discount factor is integrable, the forward
  measure is a probability measure, and the put is the Gaussian one above.
* `value_bondPut_hullWhite`, `value_bondPut_vasicek` — the Hull–White put, with
  `s = B(T₁ − T₀)·sd(r_{T₀})`, and the Vasicek put as the constant forcing (`bondRate_const`).
* `value_bondPut_gsr` — the put in the two-piece GSR model: `r_{T₀}` is Gaussian under `Q^{T₀}`
  with the variance `gsrShortRateV` of `Models/Rates/GSRBondPriceAt.lean`, and the coefficient
  `A(T₀, T₁)` of the bond, which depends on `T₀` and `T₁` separately, never enters.
* `value_bondPut_gsr_self` — at one volatility `σ₁ = σ₂` the GSR put is the Vasicek put
  (`zeroCurve_gsr_self`, `gsrShortRateV_self`).
* `value_caplet_hullWhite`, `value_caplet_vasicek`, `value_caplet_gsr` — the caplet of
  `value_caplet_eq_bondPut`, `(1 + δK)` such puts at strike `1/(1 + δK)`.

## What this is, and is not

The measure `μ` is read as the pricing measure and the Wiener representation of the short rate is
the model (as in `bondPrice_vasicek`). The caplet is *not* priced as a Black-76 caplet in these
models: the forward LIBOR `L = (1/P − 1)/δ` of a lognormal bond is a shifted lognormal (a remark,
not a theorem here), so the hypothesis of `value_caplet_black76` is not claimed and not used;
the caplet is `(1 + δK)` bond puts, which are Black puts on the lognormal bond.

## Main results

* `HasBondPrice.integral_bond_forward`: under the `T₀`-forward measure, the expectation of the
  bond `X b T₀` is `zeroCurve Q D T₁ / zeroCurve Q D T₀`.
* `HasBondPrice.value_bondPut_gaussian`: if the bond is `a * exp (-(β r))` almost surely under
  the `T₀`-forward measure, with `r` Gaussian of variance `v > 0` there, the put on the bond
  struck at `k` is worth `P(0, T₀) k Φ(-d₂) - P(0, T₁) Φ(-d₁)`, with `d₁`, `d₂` the Black-Scholes
  quantities at forward `P(0, T₁)/P(0, T₀)`, rate `0` and volatility `β√v`.
* `value_bondPut_wiener`: the same price for an integrated short rate in Wiener
  representation `R T = M T + c T * ∫₀ᵀ g_T dB`.
* `value_bondPut_hullWhite`, `value_bondPut_vasicek`: the Hull-White and Vasicek bond
  puts (`σ ≠ 0`, `0 < T₀ < T₁`), with volatility `vasicekBondB κ (T₁ - T₀)` times the standard
  deviation of `r_{T₀}`.
* `value_bondPut_gsr`: the bond put in the two-piece GSR model with volatilities `σ1`, `σ2`.
* `value_bondPut_gsr_self`, `zeroCurve_gsr_self`: at `σ1 = σ2` the GSR zero curve and bond put
  are the Vasicek ones.
* `value_caplet_hullWhite`, `value_caplet_vasicek`, `value_caplet_gsr`: in a
  `BondModel` for each of these models, the caplet is worth `1 + δK` bond puts struck at
  `1/(1 + δK)`, each priced as above. The caplet is not priced as a Black-76 caplet.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  section 3.2; section 3.3
* [Jamshidian, *An exact bond option formula*][Jamshidian1989]
* [The QuantLib contributors, *QuantLib*][QuantLib], Gsr model

## Tags

Jamshidian decomposition, bond put, caplet pricing, Hull–White model, Vasicek model,
forward measure, Gaussian short rate, MSC 91G30, MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

section Abstract

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ} {D : ℝ≥0 → Ω → ℝ}
  {X : ι → ℝ≥0 → Ω → ℝ} {b : ι} {T₀ T₁ : ℝ≥0}

/-- **The forward price of the bond**: under the `T₀`-forward measure (`forwardMeasure` of the bank
account `1/D T₀`), `𝔼^{T₀}[P(T₀, T₁)] = P(0, T₁)/P(0, T₀)`. The tower property turns `D T₁` into
`D T₀ · P(T₀, T₁)`, and the change of numéraire divides by `P(0, T₀)`. -/
theorem HasBondPrice.integral_bond_forward (h : HasBondPrice Q 𝓕 D X b T₀ T₁)
    (hDm : Measurable (D T₀)) (hD0 : Integrable (D T₀) Q) :
    ∫ ω, X b T₀ ω ∂(forwardMeasure Q fun ω ↦ 1 / D T₀ ω)
      = zeroCurve Q D T₁ / zeroCurve Q D T₀ := by
  obtain ⟨hpos, key⟩ := integral_discount_mul_eq_forward h.D_pos hDm hD0 (X b T₀)
  rw [h.integral_discount] at key
  have hz : zeroCurve Q D T₀ = ∫ ω, D T₀ ω ∂Q := rfl
  rw [hz, eq_div_iff hpos.ne', mul_comm]
  exact key

/-- **A put on the bond is a Black put, when the bond is lognormal at the forward measure.** Let
`Q'` be the `T₀`-forward measure and suppose, under it, `r` is Gaussian `N(m, v)` and the bond
price is `P(T₀, T₁) = a·exp(−β r)` with `β > 0`: a lognormal with log-standard-deviation
`s = β√v`. Then the put paying `(k − P(T₀, T₁))⁺` at `T₀` is worth

  `P(0, T₀)·k·Φ(−d₂) − P(0, T₁)·Φ(−d₁)`,   `d₁ = bsd1 F k 0 s 1`,   `d₂ = bsd2 F k 0 s 1`,

with `F = P(0, T₁)/P(0, T₀)` the forward price of the bond. The mean of the lognormal is `F`
(`HasBondPrice.integral_bond_forward`), so the constants `a`, `m` enter only through `s`. -/
theorem HasBondPrice.value_bondPut_gaussian (h : HasBondPrice Q 𝓕 D X b T₀ T₁)
    {Q' : Measure Ω} [IsProbabilityMeasure Q'] (hQ' : Q' = forwardMeasure Q fun ω ↦ 1 / D T₀ ω)
    (hDm : Measurable (D T₀)) (hD0 : Integrable (D T₀) Q) {r : Ω → ℝ} {m : ℝ} {v : ℝ≥0}
    (hv : 0 < v) (hr : HasLaw r (gaussianReal m v) Q') {a β k : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hk : 0 < k) (hP : X b T₀ =ᵐ[Q'] fun ω ↦ a * Real.exp (-(β * r ω))) :
    (bondPut b T₀ k).value Q D X
      = zeroCurve Q D T₀ * k * Phi (-bsd2 (zeroCurve Q D T₁ / zeroCurve Q D T₀) k 0
            (β * Real.sqrt v) 1)
        - zeroCurve Q D T₁ * Phi (-bsd1 (zeroCurve Q D T₁ / zeroCurve Q D T₀) k 0
            (β * Real.sqrt v) 1) := by
  subst hQ'
  set sd : ℝ := Real.sqrt v with hsd_def
  have hsd : 0 < sd := Real.sqrt_pos.2 (by exact_mod_cast hv)
  have hsd2 : sd ^ 2 = v := Real.sq_sqrt v.coe_nonneg
  set F₀ : ℝ := a * Real.exp (-(β * m) + β ^ 2 * v / 2) with hF₀
  set Z : Ω → ℝ := fun ω ↦ (-1 * r ω - (-1 * m)) / sd with hZdef
  have hZ : HasLaw Z (gaussianReal 0 1) (forwardMeasure Q fun ω ↦ 1 / D T₀ ω) :=
    hasLaw_sub_div_of_gaussianReal (gaussianReal_const_mul hr (-1)) hsd
      (by rw [NNReal.coe_mul, NNReal.coe_mk, hsd2]; ring)
  have hZmain : BSCallHyp (forwardMeasure Q fun ω ↦ 1 / D T₀ ω) F₀ k 0 (β * sd) 1 Z :=
    ⟨mul_pos ha (Real.exp_pos _), hk, mul_pos hβ hsd, one_pos, hZ⟩
  have hL : X b T₀ =ᵐ[forwardMeasure Q fun ω ↦ 1 / D T₀ ω]
      fun ω ↦ bsTerminal F₀ 0 (β * sd) 1 (Z ω) := hP.mono fun ω hω ↦ by
    have hsZ : β * sd * 1 * Z ω = β * (m - r ω) := by
      simp only [hZdef]; field_simp; ring
    have hs2 : (0 - (β * sd) ^ 2 / 2) * 1 = -(β ^ 2 * v / 2) := by rw [mul_pow, hsd2]; ring
    beta_reduce at hω ⊢
    rw [hω]
    unfold bsTerminal
    rw [Real.sqrt_one, hsZ, hs2, hF₀, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  obtain ⟨hpos, key⟩ := integral_discount_mul_eq_forward h.D_pos hDm hD0
    (fun ω ↦ max (k - X b T₀ ω) 0)
  have hF : F₀ = zeroCurve Q D T₁ / zeroCurve Q D T₀ := by
    rw [← h.integral_bond_forward hDm hD0, integral_congr_ae hL]
    simpa using (discounted_terminal_eq_S0 hZmain).symm
  have hput : ∫ ω, max (k - X b T₀ ω) 0 ∂(forwardMeasure Q fun ω ↦ 1 / D T₀ ω)
      = k * Phi (-bsd2 F₀ k 0 (β * sd) 1) - F₀ * Phi (-bsd1 F₀ k 0 (β * sd) 1) := by
    rw [integral_congr_ae (g := fun ω ↦ max (k - bsTerminal F₀ 0 (β * sd) 1 (Z ω)) 0)
      (hL.mono fun ω hω ↦ by simp only [hω])]
    simpa using bs_put_formula hZmain
  simp only [bondPut, Contract.value_pay, Payoff.eval, scenarioAt]
  rw [← key, hput, ← hF]
  have hpos' : 0 < zeroCurve Q D T₀ := hpos
  have h1 : zeroCurve Q D T₁ = zeroCurve Q D T₀ * F₀ := by
    rw [hF]; field_simp [hpos'.ne']
  rw [h1]
  simp only [zeroCurve]
  ring

end Abstract

/-! ### The Gaussian short-rate models -/

section GaussianShortRate

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {X : ι → ℝ≥0 → Ω → ℝ} {b : ι}
  {T₀ T₁ : ℝ≥0}

/-- **The bond put for an integrated short rate in Wiener representation.** Let
`R T = M T + c T·∫₀ᵀ g_T dB` for every `T`, so the discount factor `shortRateDiscount R` is
`exp(−R)`. Then the discount factor is integrable and the `T₀`-forward measure, of density
`exp(R T₀)`, is a probability measure; if `r` is Gaussian `N(m, v)` under it and the bond
`P(T₀, T₁)` is a.e. `a·exp(−β r)`, the put is the Black put of
`HasBondPrice.value_bondPut_gaussian`. The Hull–White and GSR puts are its instances. -/
theorem value_bondPut_wiener (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    {R : ℝ≥0 → Ω → ℝ} {M c : ℝ≥0 → ℝ}
    {g : ∀ T : ℝ≥0, Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))}
    (hR : ∀ T ω, R T ω = M T + c T * WienerIntegralL2.wienerIntegralLp B hB T (g T) ω)
    (hb : X b T₀ =ᵐ[μ] bondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount R) T₀ T₁) {r : Ω → ℝ} {m v : ℝ} (hv : 0 < v)
    (hr : HasLaw r (gaussianReal m v.toNNReal) (forwardMeasure μ fun ω ↦ Real.exp (R T₀ ω)))
    {a β k : ℝ} (ha : 0 < a) (hβ : 0 < β) (hk : 0 < k)
    (hP : bondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount R) T₀ T₁ =ᵐ[μ] fun ω ↦ a * Real.exp (-(β * r ω))) :
    (bondPut b T₀ k).value μ (shortRateDiscount R) X
      = zeroCurve μ (shortRateDiscount R) T₀ * k
          * Phi (-bsd2 (zeroCurve μ (shortRateDiscount R) T₁ / zeroCurve μ (shortRateDiscount R) T₀)
            k 0 (β * Real.sqrt v) 1)
        - zeroCurve μ (shortRateDiscount R) T₁
          * Phi (-bsd1 (zeroCurve μ (shortRateDiscount R) T₁ / zeroCurve μ (shortRateDiscount R) T₀)
            k 0 (β * Real.sqrt v) 1) := by
  have hRm (T : ℝ≥0) : Measurable (R T) := by
    rw [show R T = _ from funext (hR T)]
    exact ((Lp.stronglyMeasurable _).measurable.const_mul _).const_add _
  have hDm (T : ℝ≥0) : Measurable (shortRateDiscount R T) := by
    unfold shortRateDiscount
    exact (hRm T).neg.exp
  have hDi (T : ℝ≥0) : Integrable (shortRateDiscount R T) μ :=
    (integrable_one_div_exp_add_mul_wienerIntegralLp hB T (M T) (c T) (g T)).congr <|
      ae_of_all _ fun ω ↦ by simp only [shortRateDiscount, hR, one_div, ← Real.exp_neg]
  have hbp : HasBondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount R) X b T₀ T₁ := ⟨fun ω ↦ Real.exp_pos _, hDi T₁, hb⟩
  have hfm : (forwardMeasure μ fun ω ↦ 1 / shortRateDiscount R T₀ ω)
      = forwardMeasure μ fun ω ↦ Real.exp (R T₀ ω) := by
    congr 1
    funext ω
    simp [shortRateDiscount, Real.exp_neg]
  have : IsProbabilityMeasure (forwardMeasure μ fun ω ↦ 1 / shortRateDiscount R T₀ ω) := by
    rw [hfm]
    exact forwardMeasure_isProbabilityMeasure (fun ω ↦ Real.exp_pos _)
      ((integrable_one_div_exp_add_mul_wienerIntegralLp hB T₀ (M T₀) (c T₀) (g T₀)).congr
        (ae_of_all _ fun ω ↦ by simp only [hR]))
  rw [← hfm] at hr
  have hac : (forwardMeasure μ fun ω ↦ 1 / shortRateDiscount R T₀ ω) ≪ μ :=
    withDensity_absolutelyContinuous _ _
  have := hbp.value_bondPut_gaussian rfl (hDm T₀) (hDi T₀) (Real.toNNReal_pos.2 hv) hr ha hβ
    hk (hac.ae_le (hb.trans hP))
  rwa [Real.coe_toNNReal _ hv.le] at this

/-- **The zero-coupon bond put in the Hull–White model** (Jamshidian). For continuous forcing `θ`,
`σ ≠ 0` and `0 < T₀ < T₁`, a put struck at `k` expiring at `T₀` on the bond `P(T₀, T₁)` (an
underlying `b` that is a.e. the conditional expectation `bondPrice` of the discount factor) is worth

  `P(0, T₀)·k·Φ(−d₂) − P(0, T₁)·Φ(−d₁)`,   `d₁ = bsd1 F k 0 s 1`,   `d₂ = bsd2 F k 0 s 1`,

with `P(0, T) = zeroCurve` the bond prices of the model (`HullWhite.bondPrice_affine`),
`F = P(0, T₁)/P(0, T₀)` and `s = B(T₁ − T₀)·sd(r_{T₀})`, the standard deviation of
`ln P(T₀, T₁)`: the bond is `a·exp(−B(T₁ − T₀) r_{T₀})` (`bondPrice_hullWhite`) and `r_{T₀}` is
Gaussian under the `T₀`-forward measure with the variance of `HullWhite.integratedRate`
(`HullWhite.shortRate_hasLaw_forwardMeasure`), so `value_bondPut_wiener` prices the put as a
Black put. The measure is read as the pricing measure. -/
theorem value_bondPut_hullWhite (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    {θ : ℝ → ℝ} (hθ : Continuous θ) (κ σ r₀ : ℝ) (hκ : 0 < κ) (h0 : 0 < T₀) (hT : T₀ < T₁)
    (hσ : σ ≠ 0)
    (hb : X b T₀ =ᵐ[μ] bondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀ T₁) {k : ℝ} (hk : 0 < k) :
    (bondPut b T₀ k).value μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) X
      = zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀ * k
          * Phi (-bsd2 (zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀) k 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ)
              * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)
        - zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₁
          * Phi (-bsd1 (zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀) k 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ)
              * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1) := by
  exact value_bondPut_wiener hB hBm (M := fun T ↦ HullWhite.integratedMean θ κ r₀ T)
    (c := fun _ ↦ σ) (g := fun T ↦ vasicekIntegratedKernelLp hκ T) (fun _ _ ↦ rfl) hb
    (vasicekSDE_variance_pos σ κ T₀ hκ (NNReal.coe_pos.2 h0) hσ)
    (HullWhite.shortRate_hasLaw_forwardMeasure hB θ κ σ r₀ hκ T₀) (Real.exp_pos _)
    (vasicekBondB_pos hκ (NNReal.coe_pos.2 (tsub_pos_of_lt hT))) hk
    (bondPrice_hullWhite hB hBm hθ κ σ r₀ hκ hT.le)

/-- **The caplet in the Hull–White model.** In a `BondModel` for the Hull–White discount factor,
the caplet paying `δ (L(T₀, T₁) − K)⁺` at `T₁` is worth `(1 + δK)` bond puts struck at
`1/(1 + δK)` (`value_caplet_eq_bondPut`), each priced by `value_bondPut_hullWhite`. The
forward LIBOR is a shifted lognormal here, not a lognormal: this is not
`value_caplet_black76`. -/
theorem value_caplet_hullWhite (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    {θ : ℝ → ℝ} (hθ : Continuous θ) (κ σ r₀ : ℝ) (hκ : 0 < κ) (h0 : 0 < T₀) (hT : T₀ < T₁)
    (hσ : σ ≠ 0) {ℓ : ι} {δ K : ℝ}
    (h : BondModel μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) X b ℓ T₀ T₁ δ)
    (hK : 0 < 1 + δ * K)
    (hint : Integrable (fun ω ↦ shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ) T₁ ω
      * (δ * max (X ℓ T₀ ω - K) 0)) μ) :
    (caplet ℓ T₀ T₁ δ K).value μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) X
      = (1 + δ * K) *
        (zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀
            * (1 / (1 + δ * K))
          * Phi (-bsd2 (zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀)
            (1 / (1 + δ * K)) 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ) * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)
          - zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₁
            * Phi (-bsd1 (zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (HullWhite.bondRate hB θ κ σ r₀ hκ)) T₀)
            (1 / (1 + δ * K)) 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ) * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)) := by
  rw [value_caplet_eq_bondPut h hK hint]
  exact congrArg _ (value_bondPut_hullWhite hB hBm hθ κ σ r₀ hκ h0 hT hσ h.bond_eq
    (one_div_pos.2 hK))

/-- **The zero-coupon bond put in the Vasicek model**: the Hull–White put at the constant forcing
`θ ≡ κθ_v` (`HullWhite.bondRate_const`), for the Vasicek integrated rate. -/
theorem value_bondPut_vasicek (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (h0 : 0 < T₀) (hT : T₀ < T₁) (hσ : σ ≠ 0)
    (hb : X b T₀ =ᵐ[μ] bondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀ T₁) {k : ℝ} (hk : 0 < k) :
    (bondPut b T₀ k).value μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) X
      = zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀ * k
          * Phi (-bsd2 (zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀) k 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ)
              * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)
        - zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
          * Phi (-bsd1 (zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀) k 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ)
              * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1) := by
  have hD : shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)
      = shortRateDiscount (HullWhite.bondRate hB (fun _ ↦ κ * θ) κ σ r₀ hκ) := by
    funext T ω
    simp only [shortRateDiscount, HullWhite.bondRate_const]
  rw [hD] at hb ⊢
  exact value_bondPut_hullWhite hB hBm continuous_const κ σ r₀ hκ h0 hT hσ hb hk

/-- **The caplet in the Vasicek model**: `(1 + δK)` bond puts at strike `1/(1 + δK)`
(`value_caplet_eq_bondPut`), each `value_bondPut_vasicek`. Not a Black-76 caplet: the
forward LIBOR is a shifted lognormal. -/
theorem value_caplet_vasicek (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (h0 : 0 < T₀) (hT : T₀ < T₁) (hσ : σ ≠ 0) {ℓ : ι}
    {δ K : ℝ}
    (h : BondModel μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) X b ℓ T₀ T₁ δ)
    (hK : 0 < 1 + δ * K)
    (hint : Integrable (fun ω ↦ shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ) T₁ ω
      * (δ * max (X ℓ T₀ ω - K) 0)) μ) :
    (caplet ℓ T₀ T₁ δ K).value μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) X
      = (1 + δ * K) *
        (zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀
            * (1 / (1 + δ * K))
          * Phi (-bsd2 (zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀)
            (1 / (1 + δ * K)) 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ) * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)
          - zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
            * Phi (-bsd1 (zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀)
            (1 / (1 + δ * K)) 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ) * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)) := by
  rw [value_caplet_eq_bondPut h hK hint]
  exact congrArg _ (value_bondPut_vasicek hB hBm r₀ θ σ hκ h0 hT hσ h.bond_eq
    (one_div_pos.2 hK))

/-- **The zero-coupon bond put in the two-piece GSR model.** With volatility `σ₁` up to the
breakpoint `T*` and `σ₂` after, for `0 < T₀ < T₁`, `T* ≤ T₁` and `σ₁, σ₂ ≠ 0`, a put struck at `k`
expiring at `T₀` on the bond `P(T₀, T₁)` (an underlying `b` that is a.e. the conditional
expectation `bondPrice` of the GSR discount factor) is worth

  `P(0, T₀)·k·Φ(−d₂) − P(0, T₁)·Φ(−d₁)`,   `d₁ = bsd1 F k 0 s 1`,   `d₂ = bsd2 F k 0 s 1`,

with `P(0, T) = zeroCurve` the bond prices of the model (`gsrBondPrice_eq`, for `T ≥ T*`),
`F = P(0, T₁)/P(0, T₀)` and `s = B(T₁ − T₀)·sd(r_{T₀})`, the standard deviation of `ln P(T₀, T₁)`:
the bond is `A(T₀, T₁)·exp(−B(T₁ − T₀) r_{T₀})` (`bondPrice_gsr`) and `r_{T₀}` is Gaussian under the
`T₀`-forward measure with variance `gsrShortRateV`, the volatility-weighted
`∫₀^{T₀} σ(u)² e^{−2κ(T₀−u)} du` (`gsrShortRate_hasLaw_forwardMeasure`), so
`value_bondPut_wiener` prices the put as a Black put. The coefficient `A(T₀, T₁)`, which
depends on `T₀` and `T₁` separately, plays no role: only `s` enters. The measure is read as the
pricing measure. -/
theorem value_bondPut_gsr (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    (r₀ θ σ1 σ2 : ℝ) {κ : ℝ} (hκ : 0 < κ) {Tstar : ℝ≥0} (h0 : 0 < T₀) (hT : T₀ < T₁)
    (hTstar : Tstar ≤ T₁) (hσ1 : σ1 ≠ 0) (hσ2 : σ2 ≠ 0)
    (hb : X b T₀ =ᵐ[μ] bondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₀ T₁) {k : ℝ} (hk : 0 < k) :
    (bondPut b T₀ k).value μ (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) X
      = zeroCurve μ (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₀ * k
          * Phi (-bsd2 (zeroCurve μ
              (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₁
              / zeroCurve μ (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₀) k 0
            (vasicekBondB κ ((T₁ : ℝ) - T₀)
              * Real.sqrt (gsrShortRateV κ σ1 σ2 (Tstar : ℝ) T₀)) 1)
        - zeroCurve μ (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₁
          * Phi (-bsd1 (zeroCurve μ
              (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₁
              / zeroCurve μ (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₀) k 0
            (vasicekBondB κ ((T₁ : ℝ) - T₀)
              * Real.sqrt (gsrShortRateV κ σ1 σ2 (Tstar : ℝ) T₀)) 1) := by
  exact value_bondPut_wiener hB hBm (M := fun T ↦ vasicekIntegratedMean r₀ θ κ T)
    (c := fun _ ↦ 1) (g := fun T ↦ gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T)
    (fun _ _ ↦ by simp [gsrIntegratedRate]) hb
    (gsrShortRateV_pos hκ hσ1 hσ2 Tstar.coe_nonneg (t := (T₀ : ℝ)) (NNReal.coe_pos.2 h0))
    (gsrShortRate_hasLaw_forwardMeasure hB r₀ θ σ1 σ2 hκ Tstar T₀) (Real.exp_pos _)
    (vasicekBondB_pos hκ (sub_pos.2 (NNReal.coe_lt_coe.2 hT))) hk
    (bondPrice_gsr hB hBm r₀ θ σ1 σ2 hκ hT.le hTstar)

/-- **The caplet in the two-piece GSR model**: `(1 + δK)` bond puts struck at `1/(1 + δK)`
(`value_caplet_eq_bondPut`), each priced by `value_bondPut_gsr`. As for Hull–White, the
forward LIBOR is a shifted lognormal here, not a lognormal: this is not
`value_caplet_black76`. -/
theorem value_caplet_gsr (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    (r₀ θ σ1 σ2 : ℝ) {κ : ℝ} (hκ : 0 < κ) {Tstar : ℝ≥0} (h0 : 0 < T₀) (hT : T₀ < T₁)
    (hTstar : Tstar ≤ T₁) (hσ1 : σ1 ≠ 0) (hσ2 : σ2 ≠ 0) {ℓ : ι} {δ K : ℝ}
    (h : BondModel μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) X b ℓ T₀ T₁ δ)
    (hK : 0 < 1 + δ * K)
    (hint : Integrable (fun ω ↦ shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar) T₁ ω
      * (δ * max (X ℓ T₀ ω - K) 0)) μ) :
    (caplet ℓ T₀ T₁ δ K).value μ
        (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) X
      = (1 + δ * K) *
        (zeroCurve μ (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₀
            * (1 / (1 + δ * K))
          * Phi (-bsd2 (zeroCurve μ
              (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₁
              / zeroCurve μ (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₀)
            (1 / (1 + δ * K)) 0
            (vasicekBondB κ ((T₁ : ℝ) - T₀) * Real.sqrt (gsrShortRateV κ σ1 σ2 (Tstar : ℝ) T₀)) 1)
          - zeroCurve μ (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₁
            * Phi (-bsd1 (zeroCurve μ
              (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₁
              / zeroCurve μ (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar)) T₀)
            (1 / (1 + δ * K)) 0
            (vasicekBondB κ ((T₁ : ℝ) - T₀) * Real.sqrt (gsrShortRateV κ σ1 σ2 (Tstar : ℝ) T₀))
              1)) := by
  rw [value_caplet_eq_bondPut h hK hint]
  exact congrArg _ (value_bondPut_gsr hB hBm r₀ θ σ1 σ2 hκ h0 hT hTstar hσ1 hσ2 h.bond_eq
    (one_div_pos.2 hK))

/-! ### One volatility: the GSR put is the Vasicek put -/

omit [IsProbabilityMeasure μ] in
/-- **The zero curve of the one-volatility GSR model is Vasicek's**: the integrated rates agree
almost surely (`gsrIntegratedRate_self_ae`), so every `𝔼[D T]` does. -/
theorem zeroCurve_gsr_self (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (Tstar T : ℝ≥0) :
    zeroCurve μ (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ σ hκ Tstar)) T
      = zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T :=
  integral_congr_ae <| (gsrIntegratedRate_self_ae hB r₀ θ σ hκ Tstar T).mono fun ω h ↦ by
    simp only [shortRateDiscount, h]

/-- **The GSR put at `σ₁ = σ₂` is the Vasicek put.** With one volatility `σ` on both sides of the
breakpoint `T*`, the GSR put of `value_bondPut_gsr` is worth the closed form of
`value_bondPut_vasicek`: the zero curve is Vasicek's (`zeroCurve_gsr_self`) and the variance of
`r_{T₀}` is `σ²(1 − e^{−2κT₀})/(2κ)` (`gsrShortRateV_self`), whatever `T*`. -/
theorem value_bondPut_gsr_self (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) {Tstar : ℝ≥0} (h0 : 0 < T₀) (hT : T₀ < T₁)
    (hTstar : Tstar ≤ T₁) (hσ : σ ≠ 0)
    (hb : X b T₀ =ᵐ[μ] bondPrice μ (Filtration.natural B fun s ↦ (hBm s).stronglyMeasurable)
      (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ σ hκ Tstar)) T₀ T₁) {k : ℝ} (hk : 0 < k) :
    (bondPut b T₀ k).value μ (shortRateDiscount (gsrIntegratedRate hB r₀ θ σ σ hκ Tstar)) X
      = zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀ * k
          * Phi (-bsd2 (zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀) k 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ)
              * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1)
        - zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
          * Phi (-bsd1 (zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₁
              / zeroCurve μ (shortRateDiscount (vasicekIntegratedRate hB r₀ θ σ hκ)) T₀) k 0
            (vasicekBondB κ ((T₁ - T₀ : ℝ≥0) : ℝ)
              * Real.sqrt (vasicekSDEVariance σ κ T₀)) 1) := by
  rw [value_bondPut_gsr hB hBm r₀ θ σ σ hκ h0 hT hTstar hσ hσ hb hk]
  simp only [zeroCurve_gsr_self hB r₀ θ σ hκ Tstar, gsrShortRateV_self, NNReal.coe_sub hT.le]

end GaussianShortRate

end MathFin.Contracts
