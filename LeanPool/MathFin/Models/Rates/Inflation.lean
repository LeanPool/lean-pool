/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.ForwardMeasure
public import LeanPool.MathFin.Models.Rates.TimingAdjustment

/-!
# Inflation is FX: the zero-coupon inflation swap and the YoY convexity

The Jarrow–Yildirim identification reads the price index `I_t` as an exchange rate
(nominal currency per real good) and the index-linked bond as a bond denominated in
goods. Under that identification the modelling content is one postulate — the
index-linked bond `I_t·Pʳ(t,T)` is a nominal tradable, priced on the real curve — and
everything else in the zero-coupon inflation swap is change-of-numéraire bookkeeping
(`forwardIndex_eq`, `breakeven_eq`: eqs. 17.6/17.7 of the chapter).

The year-on-year convexity is the quanto correction transplanted to the nominal/real
rate pair: with both rates Gaussian, the expectation of the exponential of the two-rate
deviation is computed by the same ρ-decomposition of a correlated driver into
independent normals that powers `MathFin.quantoForward_of_gaussian`
(`MathFin.Models.BlackScholes.QuantoGrounding`), with the standard-normal MGF
`ProbabilityTheory.integral_exp_mul_stdNormal` (`MathFin.Probability.Brownian.BrownianMartingale`)
applied twice (`yoyRatioExp_gaussian`).
Composing with the Hull–White bond-reconstitution deterministics `Dⁱ = −½Bⁱ²Vⁱ`
collapses the exponent — the real-variance halves cancel, the nominal halves double — to
the chapter's eq. (17.10) (`yoyConvexity_eq`), with the naive ratio of forwards carried
as an explicit multiplicative constant. The deterministic `D = −½B²V` is tied to the library's
Hull–White model (`Models/Rates/HullWhiteCalibration`) by `integral_exp_hwD_forwardMeasure`. With
`V = Var(r_S)` the variance of the Hull–White short rate, the reconstitution factor
`exp(D − B(r_S − f(0,S)))` has mean `1` under the calibrated `S`-forward measure
(`MathFin.forwardMeasure` at the Hull–White bank account, `Models/Rates/TimingAdjustment`).

## Scope

Out of scope, and not claimed: eq. (17.8)'s conditional identity as a named lemma (the
landed anchor is `MathFin.changeOfNumeraire_setIntegral_eq`); eq. (17.9)'s SDE-level
drift-shift derivation `δ = −ρ_{rI}σ_rσ_I`; the two-correlated-Hull–White dynamics (the
means, variances and covariance of the rate deviations are explicit inputs here); and the
chapter's numeric tables. The Jarrow–Yildirim identification is a hypothesis (`hident`),
never derived. The reconstitution formula itself, `P(S,T)` as a function of `r_S`, is not derived
either: only its normalisation under the `S`-forward measure is.

## Main definitions

* `hwD`: the reconstitution deterministic `Dⁱ = −½·Bⁱ²·Vⁱ` of the Hull–White bond reconstitution
  formula.

## Main results

* `forwardIndex_eq`: under the Jarrow–Yildirim identification `hident` and positive `B_T`,
  `𝔼^{Q^{n,T}}[I_T] = I₀ · Pʳ(0,T) / Pⁿ(0,T)` under the nominal `T`-forward measure.
* `breakeven_eq`: for `I₀ > 0`, if a zero-coupon inflation swap is fair under the nominal
  `T`-forward measure, then `(1+b)^T = Pʳ(0,T) / Pⁿ(0,T)`.
* `yoyRatioExp_gaussian`: for independent standard normals `Z₁, Z₂`, `Vⁿ, Vʳ ≥ 0` and `ρ² ≤ 1`,
  the closed form of `𝔼[exp(Bⁿ·yⁿ − Bʳ·yʳ)]` for the two correlated Gaussian rate deviations.
* `yoyRatioExp_gaussian_cov`: the same closed form with the correlation replaced by a covariance
  `Cov = ρ·√(Vⁿ·Vʳ)` given by hypothesis.
* `yoyConvexity_eq`: the year-on-year convexity closed form. The Gaussian expectation of the
  reconstituted bond-ratio factor is the naive ratio of forwards times
  `exp(Bⁿ·mⁿ − Bʳ·mʳ + Bⁿ²·Vⁿ − Bʳ·Bⁿ·Cov)`.
* `integral_exp_hwD_forwardMeasure`: in the Hull–White model calibrated to a `C¹` forward curve with
  `κ > 0`, `𝔼^{Q^S}[exp(hwD b V − b·(r_S − f(0, S)))] = 1` under the `S`-forward measure.

## References

* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 17 §§17.3–17.4
  ("the chapter" throughout); the Hull–White reconstitution formula is from its ch. 8.
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  §3.3

## Tags

zero-coupon inflation swap, Jarrow–Yildirim, year-on-year inflation, convexity adjustment,
breakeven inflation, index-linked bond, quanto, MSC 91G30, MSC 91G20, JEL E31
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

/-! ## The zero-coupon inflation swap (eqs. 17.6/17.7)

`Qⁿ` is the nominal pricing measure, `B_T` the money-market account at `T` (a strictly positive
random variable), `Pⁿ₀T = Pⁿ(0,T)` and `Pʳ₀T = Pʳ(0,T)` the nominal and real T-bond prices, `I₀`
today's index and `I_T` the terminal index. The **identification hypothesis** `hident` is the
chapter's postulate verbatim: the index-linked bond, paying `I_T` at `T`, is priced on the real
curve, `𝔼^{Qⁿ}[I_T/B_T] = I₀·Pʳ(0,T)`.

In `forwardIndex_eq` and `breakeven_eq`, the numéraire measure is the nominal T-forward
measure `MathFin.forwardMeasure Qⁿ B_T` (the T-bond numéraire against the money market), whose
normalising constant is the nominal bond price, tied to the bank account by `hPn0T`:
`Pⁿ₀T = 𝔼^{Qⁿ}[1/B_T]`. When `1/B_T` is integrable and `Qⁿ` is a probability measure it is a
probability measure (`MathFin.forwardMeasure_isProbabilityMeasure`). -/
namespace MathFin.Inflation.ZCSwap

variable {Ω : Type*} [MeasurableSpace Ω] {Qn : Measure Ω}

/-- **The forward index (eq. 17.6).** Under the Jarrow–Yildirim identification
(`hident`: the index-linked bond priced on the real curve), the index under the
nominal T-forward measure (the numéraire measure of the T-bond, terminal value `1`, initial
price `Pⁿ₀T = 𝔼^{Qⁿ}[1/B_T]`) is the real-curve/nominal-curve ratio:

  `𝔼^{Q^{n,T}}[I_T] = I₀ · Pʳ(0,T) / Pⁿ(0,T)`.

The proof is `MathFin.forwardMeasure_price` at `X := I_T`, plus field algebra; no integrability
hypothesis is needed. -/
theorem forwardIndex_eq (BT : Ω → ℝ) (Pn0T Pr0T I0 : ℝ) (IT : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T)
    (hP : Pn0T = ∫ ω, 1 / BT ω ∂Qn) (hident : ∫ ω, IT ω / BT ω ∂Qn = I0 * Pr0T) :
    ∫ ω, IT ω ∂(MathFin.forwardMeasure Qn BT) = I0 * Pr0T / Pn0T := by
  subst hP
  rw [eq_div_iff hPn0T.ne', mul_comm, MathFin.forwardMeasure_price IT hBTmeas hBTpos hPn0T, hident]

/-- **The breakeven inflation rate (eq. 17.7).** A zero-coupon inflation swap pays
`I_T/I₀ − (1+b)^T` at `T`; `b` is quoted as the breakeven. Fairness (`hfair`: under the the nominal
T-forward measure `forwardMeasure Qⁿ B_T` — the fixed leg `I₀(1+b)^T` matches the floating leg
`I_T`) combined with eq. (17.6) — so under the identification `hident` — gives, for `I₀ > 0`, the
curve-only breakeven identity

  `(1+b)^T = Pʳ(0,T) / Pⁿ(0,T)`,

with `T : ℕ` the swap's maturity in whole years (only the `(1+b)^T` exponent; `B_T`, `I_T`
are simply terminal random variables). The breakeven is a *ratio of bond prices*, not a
physical-measure expectation of inflation — the chapter's central warning. -/
theorem breakeven_eq (BT : Ω → ℝ) (Pn0T Pr0T I0 b : ℝ) (T : ℕ) (IT : Ω → ℝ)
    (hBTpos : ∀ ω, 0 < BT ω) (hBTmeas : Measurable BT) (hPn0T : 0 < Pn0T) (hI0 : 0 < I0)
    (hP : Pn0T = ∫ ω, 1 / BT ω ∂Qn) (hident : ∫ ω, IT ω / BT ω ∂Qn = I0 * Pr0T)
    (hfair : ∫ ω, IT ω ∂(MathFin.forwardMeasure Qn BT)
      = I0 * (1 + b) ^ T) :
    (1 + b) ^ T = Pr0T / Pn0T := by
  have hf := forwardIndex_eq BT Pn0T Pr0T I0 IT hBTpos hBTmeas hPn0T hP hident
  rw [hfair, mul_div_assoc] at hf
  exact mul_left_cancel₀ hI0.ne' hf

end MathFin.Inflation.ZCSwap

/-! ## The YoY Gaussian core (eq. 17.10's expectation layer)

With both rates Gaussian, the year-on-year ratio's convexity is an expectation of an
exponential of a normal. `yoyRatioExp_gaussian` computes it: two rate deviations
`yⁿ = mⁿ + √Vⁿ·Z₁` and `yʳ = mʳ + √Vʳ·(ρ·Z₁ + √(1−ρ²)·Z₂)` from independent standard
normals — the ρ-decomposition of the correlated two-rate driver, exactly the shape of
`MathFin.quantoForward_of_gaussian` — with means `mⁿ, mʳ`, variances `Vⁿ, Vʳ`,
correlation `ρ`, and Hull–White factors `Bⁿ, Bʳ` over `[S, T]`. -/
namespace MathFin.Inflation.Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The two-rate exponential moment (eq. 17.10's Gaussian core).** For independent
standard normals `Z₁, Z₂` and Gaussian rate deviations `yⁿ = mⁿ + √Vⁿ·Z₁` and
`yʳ = mʳ + √Vʳ·(ρ·Z₁ + √(1−ρ²)·Z₂)`, with `Vⁿ, Vʳ ≥ 0` and `ρ² ≤ 1` (their covariance is
`ρ·√(Vⁿ·Vʳ)`, an elementary fact not stated in Lean),

  `𝔼[exp(Bⁿ·yⁿ − Bʳ·yʳ)] = exp(Bⁿ·mⁿ − Bʳ·mʳ + ½(Bⁿ²Vⁿ + Bʳ²Vʳ − 2·Bⁿ·Bʳ·ρ·√(VⁿVʳ)))`.

The proof is the `quantoForward_of_gaussian` pattern: pointwise
factorization into `exp(const)·exp(a·Z₁)·exp(b·Z₂)` with `a = Bⁿ√Vⁿ − Bʳρ√Vʳ` and
`b = −Bʳ√(1−ρ²)√Vʳ`, independence factorization of the integral, and two applications
of the 1-D Gaussian MGF; the cross term `−2BⁿBʳρ√(VⁿVʳ)` is the `a²` algebra. -/
theorem yoyRatioExp_gaussian (mn mr Vn Vr ρ Bn Br : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1)
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, Real.exp (Bn * (mn + Real.sqrt Vn * Z1 ω)
        - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))) ∂μ
      = Real.exp (Bn * mn - Br * mr
          + (Bn ^ 2 * Vn + Br ^ 2 * Vr - 2 * Bn * Br * ρ * Real.sqrt (Vn * Vr)) / 2) := by
  have h1r2 : (0 : ℝ) ≤ 1 - ρ ^ 2 := by linarith
  set E : ℝ := Bn * mn - Br * mr
  set a : ℝ := Bn * Real.sqrt Vn - Br * ρ * Real.sqrt Vr with ha
  set b : ℝ := -(Br * Real.sqrt (1 - ρ ^ 2)) * Real.sqrt Vr with hb
  -- Pointwise: the integrand is the constant `exp E` times the two single-driver exponentials.
  have hpt : (fun ω ↦ Real.exp (Bn * (mn + Real.sqrt Vn * Z1 ω)
        - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))))
      = fun ω ↦ Real.exp E * (Real.exp (a * Z1 ω) * Real.exp (b * Z2 ω)) := by
    funext ω
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [E, a, b]
    ring
  -- Independence factorization of the two single-driver exponentials.
  have hindep_exp : IndepFun (fun ω ↦ Real.exp (a * Z1 ω)) (fun ω ↦ Real.exp (b * Z2 ω)) μ :=
    hindep.exp_mul a b
  have hprod : ∫ ω, Real.exp (a * Z1 ω) * Real.exp (b * Z2 ω) ∂μ
      = Real.exp (a ^ 2 / 2) * Real.exp (b ^ 2 / 2) := by
    rw [← integral_exp_mul_stdNormal hZ1 a, ← integral_exp_mul_stdNormal hZ2 b]
    exact hindep_exp.integral_mul_eq_mul_integral
      (by have := hZ1.aemeasurable; fun_prop) (by have := hZ2.aemeasurable; fun_prop)
  rw [hpt, integral_const_mul, hprod, ← Real.exp_add, ← Real.exp_add]
  -- The `a²` algebra: the cross term `−2·Bⁿ·Bʳ·ρ·√(VⁿVʳ)` emerges from `(Bⁿ√Vⁿ − Bʳρ√Vʳ)²`.
  have hcross : Bn * Real.sqrt Vn * (Br * ρ * Real.sqrt Vr)
      = Bn * Br * ρ * Real.sqrt (Vn * Vr) := by
    rw [show Bn * Real.sqrt Vn * (Br * ρ * Real.sqrt Vr)
        = (Bn * ρ * Br) * (Real.sqrt Vn * Real.sqrt Vr) from by ring,
      ← Real.sqrt_mul hVn Vr]
    ring
  have ha2 : a ^ 2 = Bn ^ 2 * Vn + Br ^ 2 * ρ ^ 2 * Vr
      - 2 * (Bn * Real.sqrt Vn * (Br * ρ * Real.sqrt Vr)) := by
    have h1 : (Bn * Real.sqrt Vn) ^ 2 = Bn ^ 2 * Vn := by
      rw [mul_pow, Real.sq_sqrt hVn]
    have h2 : (Br * ρ * Real.sqrt Vr) ^ 2 = Br ^ 2 * ρ ^ 2 * Vr := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hVr]
    rw [ha, sub_sq, h1, h2]
    ring
  have hb2 : b ^ 2 = Br ^ 2 * (1 - ρ ^ 2) * Vr := by
    have h1 : (Br * Real.sqrt (1 - ρ ^ 2)) ^ 2 = Br ^ 2 * (1 - ρ ^ 2) := by
      rw [mul_pow, Real.sq_sqrt h1r2]
    have h2 : (Real.sqrt Vr) ^ 2 = Vr := Real.sq_sqrt hVr
    rw [hb, show (-(Br * Real.sqrt (1 - ρ ^ 2)) * Real.sqrt Vr) ^ 2
        = (Br * Real.sqrt (1 - ρ ^ 2)) ^ 2 * (Real.sqrt Vr) ^ 2 from by ring,
      h1, h2]
  have hsum : E + (a ^ 2 / 2 + b ^ 2 / 2)
      = E + (Bn ^ 2 * Vn + Br ^ 2 * Vr - 2 * Bn * Br * ρ * Real.sqrt (Vn * Vr)) / 2 := by
    rw [ha2, hb2, hcross]
    ring
  rw [hsum]

/-- **Covariance form of the two-rate exponential moment.** The same conclusion with the
correlation slot replaced by `Cov`, fixed by hypothesis `hCov : Cov = ρ·√(Vⁿ·Vʳ)` (the
covariance of the two rate deviations; that identification is not a Lean statement), the
form in which eq. 17.10 is stated in the chapter. -/
theorem yoyRatioExp_gaussian_cov (mn mr Vn Vr ρ Bn Br Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, Real.exp (Bn * (mn + Real.sqrt Vn * Z1 ω)
        - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))) ∂μ
      = Real.exp (Bn * mn - Br * mr
          + (Bn ^ 2 * Vn + Br ^ 2 * Vr - 2 * Bn * Br * Cov) / 2) := by
  rw [hCov, yoyRatioExp_gaussian mn mr Vn Vr ρ Bn Br hVn hVr hρ hZ1 hZ2 hindep]
  congr 1
  ring

end MathFin.Inflation.Gaussian

/-! ## The YoY convexity closed form (eq. 17.10)

The Hull–White bond-reconstitution formula (chapter 8, quoted at p. 295) expresses the
real/nominal bond-price ratio `Pʳ(S,T)/Pⁿ(S,T)` as the naive ratio of forwards
`Pʳ(0,T)·Pⁿ(0,S)/(Pʳ(0,S)·Pⁿ(0,T))` times the stochastic factor
`e^{Dʳ−Dⁿ}·e^{−Bʳyʳ+Bⁿyⁿ}`, with deterministic parts `Dⁱ = −½Bⁱ²Vⁱ`. Composing
`yoyRatioExp_gaussian_cov` with those deterministics collapses the exponent — the
real-variance halves cancel, the nominal halves double — to the chapter's eq. (17.10).
The reconstitution formula is taken as the integrand of `yoyConvexity_eq`, not derived. What
is derived from the library's Hull–White model is the role of `Dⁱ` as the normaliser of the
reconstitution factor under the calibrated `S`-forward measure
(`integral_exp_hwD_forwardMeasure`). -/
namespace MathFin.Inflation.Convexity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The reconstitution deterministic** `Dⁱ = −½·Bⁱ²·Vⁱ` of the Hull–White bond
reconstitution formula: the deterministic part of bond `i`'s [S,T]-factor, with `Bⁱ`
the Hull–White factor and `Vⁱ` the integrated variance. That `Dʳ − Dⁿ = (Bⁿ²Vⁿ − Bʳ²Vʳ)/2`
exactly cancels the real variance's half and doubles the nominal variance's half in
`yoyRatioExp_gaussian_cov`'s exponent is the collapse mechanism of `yoyConvexity_eq`. -/
noncomputable def hwD (B V : ℝ) : ℝ := -(B ^ 2 * V) / 2

/-- **The year-on-year convexity closed form (eq. 17.10, exact chapter shape).** With
the reconstituted bond-ratio factor — the naive ratio of forwards
`Pʳ₀T·Pⁿ₀S/(Pʳ₀S·Pⁿ₀T)` times `e^{Dʳ−Dⁿ−Bʳyʳ+Bⁿyⁿ}` with `Dⁱ = −½Bⁱ²Vⁱ` (the `hwD`
below) — the Gaussian expectation collapses to the naive ratio times the correction

  `C = exp(Bⁿ·mⁿ − Bʳ·mʳ + Bⁿ²·Vⁿ − Bʳ·Bⁿ·Cov)`,

the chapter's eq. (17.10) verbatim, with `Cov = ρ·√(VⁿVʳ)` (hypothesis `hCov`) the
covariance of the two rate deviations. The exponent's composition is pure algebra on
`yoyRatioExp_gaussian_cov`: `(Dʳ−Dⁿ) = (Bⁿ²Vⁿ − Bʳ²Vʳ)/2` cancels the *real*
variance's half exactly and doubles the *nominal* variance's half. The means `mⁿ, mʳ`,
variances and `Cov` are inputs: where they come from (two correlated Hull–White fits, the
quanto parent `−ρ_{rI}σ_rσ_I` and the forward-measure parent `−ρ_{nr}σ_nσ_rBⁿ` inside
them) is chapter-sourced interpretation, not proved here. The exponent is affine in `mʳ`
with slope `−Bʳ`, so a quanto shift `Δ` of the real-rate mean moves it by exactly `−Bʳ·Δ`
(the chapter reads `Δ = 0` off `ρ_{rI} = 0`; that link is not modelled). -/
theorem yoyConvexity_eq (mn mr Vn Vr ρ Bn Br Pn0T Pn0S Pr0T Pr0S Cov : ℝ)
    (hVn : 0 ≤ Vn) (hVr : 0 ≤ Vr) (hρ : ρ ^ 2 ≤ 1) (hCov : Cov = ρ * Real.sqrt (Vn * Vr))
    {Z1 Z2 : Ω → ℝ}
    (hZ1 : HasLaw Z1 (gaussianReal 0 1) μ) (hZ2 : HasLaw Z2 (gaussianReal 0 1) μ)
    (hindep : IndepFun Z1 Z2 μ) :
    ∫ ω, (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (hwD Br Vr - hwD Bn Vn
        + (Bn * (mn + Real.sqrt Vn * Z1 ω)
          - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω)))) ∂μ
      = (Pr0T * Pn0S / (Pr0S * Pn0T))
        * Real.exp (Bn * mn - Br * mr + Bn ^ 2 * Vn - Br * Bn * Cov) := by
  have hkey := Gaussian.yoyRatioExp_gaussian_cov mn mr Vn Vr ρ Bn Br Cov hVn hVr hρ hCov
    hZ1 hZ2 hindep
  -- Pointwise: the naive ratio times the full factor = (ratio · e^{Dʳ−Dⁿ}) · e^{−Bʳyʳ+Bⁿyⁿ}.
  have hpt : (fun ω ↦ (Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (hwD Br Vr - hwD Bn Vn
          + (Bn * (mn + Real.sqrt Vn * Z1 ω)
            - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω)))))
      = fun ω ↦ ((Pr0T * Pn0S / (Pr0S * Pn0T)) * Real.exp (hwD Br Vr - hwD Bn Vn))
          * Real.exp (Bn * (mn + Real.sqrt Vn * Z1 ω)
            - Br * (mr + Real.sqrt Vr * (ρ * Z1 ω + Real.sqrt (1 - ρ ^ 2) * Z2 ω))) := by
    funext ω
    rw [mul_assoc, ← Real.exp_add]
  rw [hpt, integral_const_mul, hkey, mul_assoc, ← Real.exp_add]
  -- The `Dⁱ`-collapse: `Dʳ − Dⁿ = (Bⁿ²Vⁿ − Bʳ²Vʳ)/2` cancels the real halves, doubles the nominal.
  have hex : hwD Br Vr - hwD Bn Vn
      + (Bn * mn - Br * mr + (Bn ^ 2 * Vn + Br ^ 2 * Vr - 2 * Bn * Br * Cov) / 2)
      = Bn * mn - Br * mr + Bn ^ 2 * Vn - Br * Bn * Cov := by
    simp only [hwD]
    ring
  rw [hex]

/-- **The reconstitution deterministic is the forward-measure normaliser.** In the library's
Hull–White model calibrated to a `C¹` forward curve `f0` (`HullWhite.theta`, short rate started
at `f(0,0)`, `κ > 0`), let `V = σ²(1 − e^{−2κS})/(2κ)` be the variance of the short rate `r_S`
(`HullWhite.integratedRate_hasLaw_gaussian`). Then for every factor `b`, under the `S`-forward
measure `Q^S` (`MathFin.forwardMeasure` at the Hull–White bank account),

  `𝔼^{Q^S}[exp(hwD b V − b·(r_S − f(0, S)))] = 1`.

Under `Q^S` the deviation `r_S − f(0,S)` is `N(0, V)` (`HullWhite.shortRate_hasLaw_forwardMeasure`
and `HullWhite.calibMean`), so `D = −½b²V` cancels its exponential moment. This is the identity
that makes the reconstitution formula `P(S,T) = (P(0,T)/P(0,S))·exp(D − B(S,T)(r_S − f(0,S)))`
consistent with `𝔼^{Q^S}[P(S,T)] = P(0,T)/P(0,S)`. The formula itself is not derived, and the
short rate is the Hull–White Wiener representation (that it solves the SDE is cited, not proved). -/
theorem integral_exp_hwD_forwardMeasure [IsProbabilityMeasure μ] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) (f0 : ℝ → ℝ)
    (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ) (hκ : 0 < κ) (S : NNReal) (b : ℝ) :
    ∫ ω, Real.exp (hwD b (vasicekSDEVariance σ κ S)
        - b * (HullWhite.integratedRate hB (HullWhite.theta f0 κ σ) κ σ (f0 0) hκ S ω - f0 S))
      ∂forwardMeasure μ (fun ω ↦ Real.exp
        (HullWhite.bondRate hB (HullWhite.theta f0 κ σ) κ σ (f0 0) hκ S ω)) = 1 := by
  have hlaw := gaussianReal_sub_const
    (HullWhite.shortRate_hasLaw_forwardMeasure hB (HullWhite.theta f0 κ σ) κ σ (f0 0) hκ S) (f0 S)
  have hm := mgf_gaussianReal hlaw (-b)
  simp only [mgf] at hm
  have hfac (ω : Ω) : Real.exp (hwD b (vasicekSDEVariance σ κ S)
      - b * (HullWhite.integratedRate hB (HullWhite.theta f0 κ σ) κ σ (f0 0) hκ S ω - f0 S))
      = Real.exp (hwD b (vasicekSDEVariance σ κ S))
        * Real.exp (-b * (HullWhite.integratedRate hB (HullWhite.theta f0 κ σ) κ σ (f0 0) hκ S ω
          - f0 S)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hfac]
  rw [integral_const_mul, hm, ← Real.exp_add, Real.exp_eq_one_iff,
    Real.coe_toNNReal _ (vasicekSDEVariance_nonneg σ hκ S.coe_nonneg),
    HullWhite.calibMean f0 hf0 κ σ hκ S, hwD, vasicekBondB]
  ring

end MathFin.Inflation.Convexity
