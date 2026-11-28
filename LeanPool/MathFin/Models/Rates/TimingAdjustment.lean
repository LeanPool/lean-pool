/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.BrownianMartingale
public import LeanPool.MathFin.Pricing.ForwardMeasure
public import LeanPool.MathFin.Pricing.WienerIntegralForwardMeasure
public import LeanPool.MathFin.Models.Rates.HullWhiteCalibration

/-!
# The covariance-between-numéraires identity: timing adjustment and futures-forward basis

Two textbook corrections are the same identity. Let `Q^N` be the measure attached to a
numéraire whose relative weight against the reference numéraire is `e^{−Y}`. For a payoff
`V` with `(ln V, Y)` jointly Gaussian in the two-driver form below,

  `𝔼^{Q^N}[V] = 𝔼^Q[V] · exp(−Cov(ln V, Y))`.

The static step is `changeOfNumeraire` (`Pricing/Numeraire`): `𝔼^{Q^N}[V]` is
`𝔼^Q[V·e^{−Y}] / 𝔼^Q[e^{−Y}]`. The Gaussian step is the log-normal covariance identity
`𝔼[V·e^{−Y}] = 𝔼[V]·𝔼[e^{−Y}]·exp(−Cov(ln V, Y))`, proved here from the independent-driver
decomposition `Y = n + u(ρ Z₁ + √(1−ρ²) Z₂)`, `ln V = m + s Z₁`, so `Cov(ln V, Y) = ρ s u`.

* **Hull's timing adjustment** (Hull, *Options, Futures, and Other Derivatives*, the chapter
  on convexity, timing and quanto adjustments; the exact lognormal identity underlying its
  timing-adjustment formula): `Q` is the `T`-forward measure, `Q^N` the
  `T*`-forward measure, and `e^{−Y} = P(T,T*)`. A payoff fixed at `T` and paid at `T*` has
  `𝔼^{T*}[V] = 𝔼^T[V]·exp(−Cov(ln V, Y))`.
* **Bagaria's futures-forward basis** (Bagaria, §8.4, the unnumbered covariance identity
  preceding Worked case 8.5 — not the Ho–Lee basis approximation of eq. 8.9): `Q` is the
  risk-neutral measure, `Q^N` the `T`-forward measure, and `e^{Y}` the bank account
  `exp(∫₀ᵀ r)`. The futures price `𝔼^Q[V]` is the forward price `𝔼^T[V]` times
  `exp(Cov(ln V, ∫₀ᵀ r))`.

**Exact vs. linearized.** Both statements here are exact under the Gaussian hypothesis.
Hull's textbook presentation of the timing adjustment, with a `(1 + R_F/m)`-style
simple-compounding denominator, replaces the exact covariance `Cov(ln V, Y)` with its
first-order (bond-duration) approximation in the forward rate. That approximate form is
not proved here and is not exact.

**What the measures are.** In the two-driver theorems, `Q` is any measure `μ` carrying the two
independent standard normals, `Q^N` is `numeraireMeasure` with the stated normalisation, and `Y`
is the Gaussian variable `n + u(ρ Z₁ + √(1−ρ²) Z₂)`. "Risk-neutral", "`T`-forward", "bank
account `exp(∫₀ᵀ r)`" and "`P(T,T*)`" are readings of these; those theorems model no short rate
or bond. That the futures price is `𝔼^Q[V]` and the forward price is `𝔼^T[V]` are textbook
identifications, not proved here.

**The Hull–White instance.** The numéraire step does not depend on the two-driver form:
`futuresForwardBasis_of_integral_mul_exp_neg` (`Pricing/ForwardMeasure`) takes the covariance
identity as a hypothesis. `futuresForwardBasis_gaussian` is its two-driver instance. The last
section supplies a second instance in which the short rate and the bond are modelled: the
Hull–White short rate `r_S` and
bank account `exp(∫₀ˢ r)` of `Models/Rates/HullWhiteCalibration`, in their Wiener representations
(that they solve the SDE, and the time-order swap, are cited, not proved there). The covariance
identity is now `integral_exp_mul_exp_neg_wienerIntegralLp`, with
`Cov(r_S, ∫₀ˢ r) = σ²⟪e^{−κ(S−·)}, g⟫ = σ²B(S)²/2`. The `S`-forward measure
is `forwardMeasure μ (exp ∘ bondRate)` — the library's one
`T`-forward measure (`Pricing/ForwardMeasure`) at the bank account `exp(∫₀ˢ r)`; the law of a
Wiener-represented rate under it is `hasLaw_forwardMeasure_wienerIntegralLp`
(`Pricing/WienerIntegralForwardMeasure`).
Under it `r_S ~ N(α(S) − σ²B(S)²/2, var)` (`HullWhite.shortRate_hasLaw_forwardMeasure`), so the
futures–forward gap of the short rate is `𝔼[r_S] − 𝔼^S[r_S] = σ²B(S)²/2`
(`HullWhite.integral_shortRate_sub_forwardMeasure`). For the curve-calibrated model
`𝔼^S[r_S] = f(0, S)` (`HullWhite.forwardMeasure_shortRate_mean_eq_forwardCurve`). These are
statements about the instantaneous short rate `r_S`, not about a futures contract on a term rate.

## Main results

* `integral_mul_exp_neg_gaussian` — `𝔼[V·e^{−Y}] = 𝔼[V]·𝔼[e^{−Y}]·exp(−ρ s u)`.
* `timingAdjustment_gaussian` — the exact lognormal identity underlying Hull's timing
  adjustment.
* `futuresForwardBasis_gaussian` — Bagaria §8.4's covariance identity, exact Gaussian form.
* `HullWhite.shortRate_hasLaw_forwardMeasure`, `HullWhite.integral_shortRate_sub_forwardMeasure`,
  `HullWhite.forwardMeasure_shortRate_mean_eq_forwardCurve` — the Hull–White `S`-forward measure,
  the law of `r_S` under it (an instance of `hasLaw_forwardMeasure_wienerIntegralLp`), the
  futures–forward gap of the short rate, and the forward curve as the `S`-forward mean of the
  calibrated short rate.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull] (the chapter on convexity,
  timing and quanto adjustments).
* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 8.
* [H. Geman, N. El Karoui, J.-C. Rochet, *Changes of numéraire, changes of probability measure and
  option pricing*][GemanElKarouiRochet1995] (the forward measure; `𝔼^T[r_T] = f(0,T)`).
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  §3.3

## Tags

timing adjustment, futures–forward basis, convexity adjustment, change of numéraire,
forward measure, lognormal covariance, Hull–White, MSC 91G30, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The log-normal covariance identity.** With `ln V = m + s Z₁` and
`Y = n + u(ρ Z₁ + √(1−ρ²) Z₂)` for independent standard normals `Z₁, Z₂` (so
`Cov(ln V, Y) = ρ s u`). No bound on `ρ` is assumed: `√(1−ρ²)` enters the proof only through
its square, which cancels identically between the two sides, so the identity holds verbatim
even for `|ρ| > 1` (where `Real.sqrt` returns its junk value `0`).

  `𝔼[V·e^{−Y}] = 𝔼[V] · 𝔼[e^{−Y}] · exp(−ρ s u)`. -/
theorem integral_mul_exp_neg_gaussian (m s n u ρ : ℝ)
    {Z₁ Z₂ : Ω → ℝ}
    (h₁ : HasLaw Z₁ (gaussianReal 0 1) μ) (h₂ : HasLaw Z₂ (gaussianReal 0 1) μ)
    (hm₁ : Measurable Z₁) (hm₂ : Measurable Z₂) (hindep : IndepFun Z₁ Z₂ μ) :
    ∫ ω, Real.exp (m + s * Z₁ ω)
        * Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω))) ∂μ
      = (∫ ω, Real.exp (m + s * Z₁ ω) ∂μ)
        * (∫ ω, Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω))) ∂μ)
        * Real.exp (-(ρ * s * u)) := by
  set r := Real.sqrt (1 - ρ ^ 2)
  have eL : (fun ω ↦ Real.exp (m + s * Z₁ ω) * Real.exp (-(n + u * (ρ * Z₁ ω + r * Z₂ ω))))
      = fun ω ↦ Real.exp ((m - n) + (s - u * ρ) * Z₁ ω + (-(u * r)) * Z₂ ω) := by
    funext ω; rw [← Real.exp_add]; congr 1; ring
  have eV : (fun ω ↦ Real.exp (m + s * Z₁ ω))
      = fun ω ↦ Real.exp (m + s * Z₁ ω + 0 * Z₂ ω) := by
    funext ω; simp
  have eP : (fun ω ↦ Real.exp (-(n + u * (ρ * Z₁ ω + r * Z₂ ω))))
      = fun ω ↦ Real.exp (-n + (-(u * ρ)) * Z₁ ω + (-(u * r)) * Z₂ ω) := by
    funext ω; congr 1; ring
  rw [eL, eV, eP, integral_exp_affine_indep h₁ h₂ hm₁ hm₂ hindep,
    integral_exp_affine_indep h₁ h₂ hm₁ hm₂ hindep, integral_exp_affine_indep h₁ h₂ hm₁ hm₂ hindep,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- **Hull's timing adjustment** (the exact lognormal identity underlying Hull's formula).
Let `Q` be the
`T`-forward measure (reference numéraire `P(·,T)`, worth `1` at `T` and `B₀ = P(0,T)` today),
and let the `T*`-bond be worth `P(T,T*) = e^{−Y}` at `T` and `N₀ = P(0,T*)` today, with the
no-arbitrage normalization `N₀ = B₀·𝔼^T[P(T,T*)]` (hypothesis `hnorm`). These are readings
of `μ` and the two numéraires (see the module note). For a payoff `V` fixed at `T` and paid
at `T*`, with `ln V = m + s Z₁` and `Y = n + u(ρ Z₁ + √(1−ρ²) Z₂)` as in
`integral_mul_exp_neg_gaussian` (so `Cov(ln V, Y) = ρ s u`), the `T*`-forward expectation is

  `𝔼^{T*}[V] = 𝔼^T[V] · exp(−ρ s u)`.

This is exact; the textbook `(1 + R_F/m)`-style simple-compounding form replaces the exact
`Cov(ln V, Y)` with a first-order (bond-duration) approximation, not proved here. -/
theorem timingAdjustment_gaussian (m s n u ρ B₀ N₀ : ℝ)
    (hB₀ : 0 ≤ B₀) (hN₀ : 0 < N₀)
    {Z₁ Z₂ : Ω → ℝ}
    (h₁ : HasLaw Z₁ (gaussianReal 0 1) μ) (h₂ : HasLaw Z₂ (gaussianReal 0 1) μ)
    (hm₁ : Measurable Z₁) (hm₂ : Measurable Z₂) (hindep : IndepFun Z₁ Z₂ μ)
    (hnorm : N₀ = B₀ *
      ∫ ω, Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω))) ∂μ) :
    ∫ ω, Real.exp (m + s * Z₁ ω) ∂(numeraireMeasure μ (fun _ ↦ 1)
        (fun ω ↦ Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω)))) B₀ N₀)
      = (∫ ω, Real.exp (m + s * Z₁ ω) ∂μ) * Real.exp (-(ρ * s * u)) := by
  subst hnorm
  set P : Ω → ℝ := fun ω ↦ Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω)))
  set V : Ω → ℝ := fun ω ↦ Real.exp (m + s * Z₁ ω)
  have hPm : Measurable P := by fun_prop
  have h := changeOfNumeraire (Q := μ) (fun ω ↦ V ω * P ω) hPm measurable_const
    (fun ω ↦ Real.exp_pos _) (fun _ ↦ one_pos) hB₀ hN₀
  have hc : (fun ω ↦ V ω * P ω / P ω) = V := by
    funext ω; exact mul_div_cancel_right₀ _ (Real.exp_pos _).ne'
  simp only [hc, div_one] at h
  have hcore := integral_mul_exp_neg_gaussian (μ := μ) m s n u ρ h₁ h₂ hm₁ hm₂ hindep
  change ∫ ω, V ω * P ω ∂μ = (∫ ω, V ω ∂μ) * (∫ ω, P ω ∂μ) * _ at hcore
  rw [hcore] at h
  exact mul_left_cancel₀ hN₀.ne' (h.trans (by ring))

/-- **Bagaria's futures-forward basis** (Bagaria, §8.4, the unnumbered covariance identity
preceding Worked case 8.5 — not the Ho–Lee basis approximation of eq. 8.9), exact Gaussian
form. Read `μ` as the risk-neutral measure `Q` with bank account `e^{Y}`, `Y = ∫₀ᵀ r`, and pass
to the `T`-forward measure (numéraire `P(·,T)`, worth `1` at `T` and
`P(0,T) = 𝔼^Q[e^{−Y}]` today, positive by `hN₀`). These are readings: `μ` is any
measure carrying `Z₁, Z₂`, and this theorem models no short rate (see the module note). For an
underlying `V` with `ln V = m + s Z₁` and `Y = n + u(ρ Z₁ + √(1−ρ²) Z₂)` as in
`integral_mul_exp_neg_gaussian` (so `Cov(ln V, Y) = ρ s u`), the textbook futures price
`𝔼^Q[V]` and forward price `𝔼^T[V]` satisfy

  `𝔼^Q[V] = 𝔼^T[V] · exp(ρ s u)`.

The two-driver instance of `futuresForwardBasis_of_integral_mul_exp_neg`. -/
theorem futuresForwardBasis_gaussian (m s n u ρ : ℝ)
    {Z₁ Z₂ : Ω → ℝ}
    (h₁ : HasLaw Z₁ (gaussianReal 0 1) μ) (h₂ : HasLaw Z₂ (gaussianReal 0 1) μ)
    (hm₁ : Measurable Z₁) (hm₂ : Measurable Z₂) (hindep : IndepFun Z₁ Z₂ μ)
    (hN₀ : 0 <
      ∫ ω, Real.exp (-(n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω))) ∂μ) :
    ∫ ω, Real.exp (m + s * Z₁ ω) ∂μ
      = (∫ ω, Real.exp (m + s * Z₁ ω) ∂(forwardMeasure μ
          fun ω ↦ Real.exp (n + u * (ρ * Z₁ ω + Real.sqrt (1 - ρ ^ 2) * Z₂ ω))))
        * Real.exp (ρ * s * u) :=
  futuresForwardBasis_of_integral_mul_exp_neg (ρ * s * u) (by fun_prop) hN₀
    (integral_mul_exp_neg_gaussian m s n u ρ h₁ h₂ hm₁ hm₂ hindep)

/-! ## The Hull–White instance: the `S`-forward measure and the short rate

`r_S = α(S) + σ∫₀ˢ e^{−κ(S−u)} dB_u` (`HullWhite.integratedRate`) and
`∫₀ˢ r = ∫₀ˢ α + σ∫₀ˢ g dB` (`HullWhite.bondRate`) are both Wiener integrals against the same `B`,
so their covariance is `σ²⟪e^{−κ(S−·)}, g⟫ = σ²B(S)²/2`. -/

namespace HullWhite

open WienerIntegralL2
open scoped NNReal InnerProductSpace

/-- `∫₀ˢ e^{−κ(S−u)}·g(u) du = B(S)²/2` (`κ ≠ 0`), by the FTC with antiderivative
`e^{−κ(S−u)}/κ² − e^{−κ(S−u)}²/(2κ²)`. -/
lemma integral_vasicekKernel_mul_vasicekIntegratedKernel (κ S : ℝ) (hκ : κ ≠ 0) :
    ∫ u in (0 : ℝ)..S, vasicekKernel κ S u * vasicekIntegratedKernel κ S u
      = vasicekBondB κ S ^ 2 / 2 := by
  have hderiv (u : ℝ) : HasDerivAt
      (fun u : ℝ ↦ Real.exp (-(κ * (S - u))) / κ ^ 2
        - Real.exp (-(κ * (S - u))) * Real.exp (-(κ * (S - u))) / (2 * κ ^ 2))
      (vasicekKernel κ S u * vasicekIntegratedKernel κ S u) u := by
    have harg : HasDerivAt (fun u ↦ -(κ * (S - u))) κ u := by
      have h : HasDerivAt (fun u ↦ -(κ * (S - u))) (-(κ * (-1))) u := by
        apply HasDerivAt.neg; apply HasDerivAt.const_mul
        simpa using (hasDerivAt_id u).const_sub S
      simpa using h
    have he := harg.exp
    refine ((he.div_const (κ ^ 2)).sub ((he.mul he).div_const (2 * κ ^ 2))).congr_deriv ?_
    simp only [vasicekKernel, vasicekIntegratedKernel]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hderiv u)
    (by
      apply Continuous.intervalIntegrable
      simp only [vasicekKernel, vasicekIntegratedKernel]
      fun_prop)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, sub_zero, vasicekBondB]
  field_simp
  ring

/-- **The covariance of the HW short rate with its integral, per unit `σ²`**:
`⟪e^{−κ(S−·)}, g⟫_{L²((0,S])} = B(S)²/2`. -/
lemma inner_vasicekKernelLp_vasicekIntegratedKernelLp {κ : ℝ} (hκ : 0 < κ) (S : ℝ≥0) :
    ⟪vasicekKernelLp κ hκ.le S, vasicekIntegratedKernelLp hκ S⟫_ℝ = vasicekBondB κ S ^ 2 / 2 := by
  rw [L2.inner_def, ← integral_vasicekKernel_mul_vasicekIntegratedKernel κ S hκ.ne',
    intervalIntegral.integral_of_le S.coe_nonneg]
  refine integral_congr_ae ?_
  filter_upwards [(vasicekKernel_memLp κ hκ.le S).coeFn_toLp,
    (vasicekIntegratedKernel_memLp hκ S).coeFn_toLp] with u h₁ h₂
  simp only [vasicekKernelLp, vasicekIntegratedKernelLp, RCLike.inner_apply, conj_trivial, h₁, h₂]
  ring

variable [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- **The law of the Hull–White short rate under the `S`-forward measure**:

  `r_S ~ N(α(S) − σ²B(S)²/2, σ²(1 − e^{−2κS})/(2κ))`   under `Q^S`.

Under `μ` the law is `N(α(S), var)` (`integratedRate_hasLaw_gaussian`); the change to the
`S`-forward measure shifts the mean by `−Cov(r_S, ∫₀ˢ r) = −σ²B(S)²/2` and keeps the variance
(`hasLaw_forwardMeasure_wienerIntegralLp`, with `Cov = σ²⟪e^{−κ(S−·)}, g⟫`). -/
theorem shortRate_hasLaw_forwardMeasure (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ)
    (κ σ r₀ : ℝ) (hκ : 0 < κ) (S : ℝ≥0) :
    HasLaw (integratedRate hB θ κ σ r₀ hκ S)
      (gaussianReal (deterministic θ κ r₀ S - σ ^ 2 * vasicekBondB κ S ^ 2 / 2)
        (vasicekSDEVariance σ κ S).toNNReal)
      (forwardMeasure μ fun ω ↦ Real.exp (bondRate hB θ κ σ r₀ hκ S ω)) := by
  have h := hasLaw_forwardMeasure_wienerIntegralLp hB S (deterministic θ κ r₀ S)
    (integratedMean θ κ r₀ S) σ σ (deterministic θ κ r₀ S) (vasicekKernelLp κ hκ.le S)
    (vasicekIntegratedKernelLp hκ S) (integratedRate_hasLaw_gaussian hB θ κ σ r₀ hκ S)
  rwa [inner_vasicekKernelLp_vasicekIntegratedKernelLp hκ S,
    show σ * σ * (vasicekBondB κ S ^ 2 / 2) = σ ^ 2 * vasicekBondB κ S ^ 2 / 2 by ring] at h

/-- **The `S`-forward mean of the Hull–White short rate**:
`𝔼^S[r_S] = α(S) − σ²B(S)²/2`. -/
theorem integral_shortRate_forwardMeasure (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ)
    (κ σ r₀ : ℝ) (hκ : 0 < κ) (S : ℝ≥0) :
    ∫ ω, integratedRate hB θ κ σ r₀ hκ S ω
        ∂(forwardMeasure μ fun ω ↦ Real.exp (bondRate hB θ κ σ r₀ hκ S ω))
      = deterministic θ κ r₀ S - σ ^ 2 * vasicekBondB κ S ^ 2 / 2 := by
  rw [(shortRate_hasLaw_forwardMeasure hB θ κ σ r₀ hκ S).integral_eq, integral_id_gaussianReal]

/-- **The futures–forward gap of the Hull–White short rate**:

  `𝔼[r_S] − 𝔼^S[r_S] = σ²B(S)²/2 = (σ²/2κ²)(1 − e^{−κS})²`,

the mean of `r_S` under the measure `μ` carrying the driver minus its mean under the `S`-forward
measure. It holds for every deterministic forcing `θ`. -/
theorem integral_shortRate_sub_forwardMeasure (hB : IsPreBrownianReal B μ) (θ : ℝ → ℝ)
    (κ σ r₀ : ℝ) (hκ : 0 < κ) (S : ℝ≥0) :
    ∫ ω, integratedRate hB θ κ σ r₀ hκ S ω ∂μ
        - ∫ ω, integratedRate hB θ κ σ r₀ hκ S ω
            ∂(forwardMeasure μ fun ω ↦ Real.exp (bondRate hB θ κ σ r₀ hκ S ω))
      = σ ^ 2 * vasicekBondB κ S ^ 2 / 2 := by
  rw [integral_shortRate_forwardMeasure,
    (integratedRate_hasLaw_gaussian hB θ κ σ r₀ hκ S).integral_eq, integral_id_gaussianReal]
  ring

/-- **The forward curve is the `S`-forward mean of the calibrated short rate**: with the
calibrated forcing `θ = theta f0 κ σ`, the short rate started at `f(0,0)`, `f0 ∈ C¹` and `κ > 0`,

  `𝔼^S[r_S] = f(0, S)`.

The calibrated deterministic part is `f(0,S) + σ²B(S)²/2` (`calibMean`), and the forward measure
removes exactly `σ²B(S)²/2` (`integral_shortRate_forwardMeasure`). -/
theorem forwardMeasure_shortRate_mean_eq_forwardCurve (hB : IsPreBrownianReal B μ)
    (f0 : ℝ → ℝ) (hf0 : ContDiff ℝ 1 f0) (κ σ : ℝ) (hκ : 0 < κ) (S : ℝ≥0) :
    ∫ ω, integratedRate hB (theta f0 κ σ) κ σ (f0 0) hκ S ω
        ∂(forwardMeasure μ fun ω ↦ Real.exp (bondRate hB (theta f0 κ σ) κ σ (f0 0) hκ S ω))
      = f0 S := by
  rw [integral_shortRate_forwardMeasure, calibMean f0 hf0 κ σ hκ S, vasicekBondB]
  ring

end HullWhite

end MathFin
