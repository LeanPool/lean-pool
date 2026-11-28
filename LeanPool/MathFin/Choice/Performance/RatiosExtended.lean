/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Performance.Ratios
public import LeanPool.MathFin.Choice.Portfolio.CAPM
public import Mathlib.Probability.Moments.Variance

/-!
# Extended performance ratios: Sortino, Treynor, Information, gain-to-pain, upside capture

Standard quant performance metrics beyond the basic Sharpe ratio:

* **Sortino ratio** `S = (μ - target) / σ_down`, with `σ_down` the downside
  semi-deviation. Like Sharpe but penalises only downside variation.
* **Treynor ratio** `T = (μ - r_f) / β`, with `β = Cov(R, R_m) / Var(R_m)` the
  systematic risk. The market-model analogue of Sharpe.
* **Information ratio** `IR = (μ_p - μ_b) / σ_active`, with `σ_active` the
  tracking error (std-dev of `R_p − R_b`). Measures active management skill.
* **Tracking error squared** `trackingErrorSq := σ_p² − 2·cov + σ_b²` — the
  `Var(R_p − R_b)` expansion in terms of the input moments, tied to the variance of
  the active return by `trackingErrorSq_eq_variance_sub`.

Sortino, Treynor, and IR are all instances of `(a − b)/d`. Their
*scale-invariance* lemmas are one-line consequences of the algebraic master
`diff_div_scale_invariant` in `Choice.Performance.Ratios`. (The same master also
handles the Sharpe scale invariance — proving that the master is load-bearing
across all four ratios in the library.)

The last two are *realised* ratios: they aggregate a return path over a finite
period set rather than combining summary moments.

* **Gain-to-pain ratio** `(∑ r⁺) / (∑ r⁻)`, total gains over total losses
  (Schwager). Written with Mathlib's positive/negative parts `r⁺ = max r 0`,
  `r⁻ = max (-r) 0`, so `posPart_sub_negPart` supplies the decomposition
  `∑ r⁺ − ∑ r⁻ = ∑ r` that turns "ratio ≥ 1" into "the period was profitable".
* **Upside-capture ratio** `(∑_{up} p) / (∑_{up} b)`, portfolio gains over
  benchmark gains on the up-market periods (Morningstar).

Both are quotients, and in Lean `x / 0 = 0`; the nonnegativity and homogeneity
statements below therefore need **no** nonvanishing side condition — the
degenerate no-loss / flat-benchmark case is covered by the same statement. The
one place a hypothesis is genuinely load-bearing is
`one_le_gainToPain_iff`, where `0 < ∑ r⁻` is what makes the quotient
comparable to `1` at all.

## Main definitions

* `sortinoRatio`: `(μ − target) / σ_down`, with `σ_down` the downside semi-deviation.
* `treynorRatio`: `(μ − r_f) / β`.
* `informationRatio`: `(μ_p − μ_b) / σ_active`, with `σ_active` the tracking error.
* `trackingErrorSq`: `σ_p² − 2·cov + σ_b²`.
* `gainToPain`: over a finite period set, the total of the positive parts of the returns over the
  total of the negative parts.
* `upCapture`: over the up-market periods, the portfolio gains `∑ p` over the benchmark gains
  `∑ b`.

## Main results

* `sortinoRatio_scale_invariant`, `sortinoRatio_translation`.
* `treynorRatio_scale_invariant`, `treynorRatio_eq_sharpeRatio_mul` (Treynor
  is Sharpe rescaled by `σ / β`) and `treynorRatio_eq_of_jensenAlpha_eq_zero` (on the security
  market line every asset has the market's Treynor ratio).
* `informationRatio_scale_invariant`.
* `trackingErrorSq_self`, `trackingErrorSq_ge_diff_sq`,
  `trackingErrorSq_eq_variance_sub`.
* `gainToPain_nonneg`, `one_le_gainToPain_iff`.
* `upCapture_smul`.

## References

* [K. Bodie and Marcus, *Investments*][BodieKaneMarcus], Ch 10
* [Grinold and Kahn, *Active Portfolio Management*][GrinoldKahn1999]
* [Sortino and van der Meer (1991)][SortinoVanDerMeer1991]
* [Treynor (1965)][Treynor1965]

## Tags

Sortino ratio, Treynor ratio, information ratio, tracking error, gain-to-pain ratio, upside capture,
performance attribution, MSC 91G10, JEL G11
-/

@[expose] public section

namespace MathFin

open Real MeasureTheory ProbabilityTheory

/-- **Sortino ratio** `(μ - target) / σ_down`. Inputs are the mean, the target
return, and the downside semi-deviation. -/
noncomputable def sortinoRatio (μ target σ_down : ℝ) : ℝ :=
  (μ - target) / σ_down

/-- Sortino is invariant under uniform rescaling. One-line consequence of
`diff_div_scale_invariant`. -/
lemma sortinoRatio_scale_invariant {c : ℝ} (hc : c ≠ 0)
    (μ target σ_down : ℝ) :
    sortinoRatio (c * μ) (c * target) (c * σ_down) =
      sortinoRatio μ target σ_down := by
  unfold sortinoRatio
  exact diff_div_scale_invariant hc μ target σ_down

/-- Sortino is translation-invariant in the additive shift of both mean and
target. -/
lemma sortinoRatio_translation (μ target σ_down shift : ℝ) :
    sortinoRatio (μ + shift) (target + shift) σ_down =
      sortinoRatio μ target σ_down := by
  unfold sortinoRatio
  ring_nf

/-- **Treynor ratio** `(μ - r_f) / β`, with `β` the systematic-risk coefficient. -/
noncomputable def treynorRatio (μ r_f β : ℝ) : ℝ := (μ - r_f) / β

/-- Treynor is invariant under uniform rescaling. One-line consequence of
`diff_div_scale_invariant`. -/
lemma treynorRatio_scale_invariant {c : ℝ} (hc : c ≠ 0) (μ r_f β : ℝ) :
    treynorRatio (c * μ) (c * r_f) (c * β) = treynorRatio μ r_f β := by
  unfold treynorRatio
  exact diff_div_scale_invariant hc μ r_f β

/-- **Treynor is Sharpe rescaled**: for a nonzero beta and a nonzero volatility `σ`,
`T = S · σ / β`, with `S = sharpeRatio μ r_f σ`. With `β = Cov(R, R_m) / Var(R_m)`
(`MathFin.beta`) and `σ = √Var(R)` the factor `σ / β` is `σ_m / ρ`, the market volatility over
the correlation. -/
lemma treynorRatio_eq_sharpeRatio_mul {σ β : ℝ} (hσ : σ ≠ 0) (hβ : β ≠ 0) (μ r_f : ℝ) :
    treynorRatio μ r_f β = sharpeRatio μ r_f σ * (σ / β) := by
  unfold treynorRatio sharpeRatio
  field_simp

/-- **On the security market line every asset has the market's Treynor ratio**: if Jensen's alpha
vanishes (`MathFin.jensenAlpha`) and the beta is nonzero, the Treynor ratio of the asset is the
market risk premium `E[R_m] − r_f`. -/
lemma treynorRatio_eq_of_jensenAlpha_eq_zero {eR rf β eRm : ℝ}
    (h : jensenAlpha eR rf β eRm = 0) (hβ : β ≠ 0) : treynorRatio eR rf β = eRm - rf := by
  rw [jensenAlpha_eq_zero_iff] at h
  unfold treynorRatio
  rw [h, securityMarketLine]
  field_simp
  ring

/-- **Information ratio** `(μ_p - μ_b) / σ_active`, with `σ_active` the
tracking error. -/
noncomputable def informationRatio (μ_p μ_b σ_active : ℝ) : ℝ :=
  (μ_p - μ_b) / σ_active

/-- Information ratio is invariant under uniform rescaling. One-line
consequence of `diff_div_scale_invariant`. -/
lemma informationRatio_scale_invariant {c : ℝ} (hc : c ≠ 0)
    (μ_p μ_b σ_active : ℝ) :
    informationRatio (c * μ_p) (c * μ_b) (c * σ_active) =
      informationRatio μ_p μ_b σ_active := by
  unfold informationRatio
  exact diff_div_scale_invariant hc μ_p μ_b σ_active

/-- **Tracking error squared**, defined as `σ_p² − 2·cov + σ_b²` — the
familiar expansion of `Var(R_p − R_b)` in terms of the input moments. Its inputs are bare
reals; `trackingErrorSq_eq_variance_sub` ties it to the variance of the active return. -/
noncomputable def trackingErrorSq (σ_p σ_b cov : ℝ) : ℝ :=
  σ_p ^ 2 - 2 * cov + σ_b ^ 2

/-- **Tracking error squared is the variance of the active return**: for square-integrable
returns `R_p`, `R_b` of a portfolio and its benchmark, with `σ_p = √Var(R_p)`,
`σ_b = √Var(R_b)` and `cov = Cov(R_p, R_b)`, `trackingErrorSq σ_p σ_b cov = Var(R_p − R_b)`.
The tracking error `σ_active` of `informationRatio` is the square root of this. -/
theorem trackingErrorSq_eq_variance_sub {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {R_p R_b : Ω → ℝ} (hp : MemLp R_p 2 P) (hb : MemLp R_b 2 P) :
    trackingErrorSq √(Var[R_p; P]) √(Var[R_b; P]) cov[R_p, R_b; P]
      = Var[fun ω ↦ R_p ω - R_b ω; P] := by
  have h := variance_fun_add hp (hb.const_mul (-1))
  rw [variance_const_mul, covariance_const_mul_right] at h
  rw [show (fun ω ↦ R_p ω - R_b ω) = fun ω ↦ R_p ω + -1 * R_b ω by ext; ring, h,
    trackingErrorSq, Real.sq_sqrt (variance_nonneg _ _), Real.sq_sqrt (variance_nonneg _ _)]
  ring

/-- **Self-benchmark vanishing**: when the benchmark equals the portfolio
(`σ_p = σ_b` and `cov = σ_p²`), the tracking error vanishes. -/
lemma trackingErrorSq_self (σ_p : ℝ) :
    trackingErrorSq σ_p σ_p (σ_p ^ 2) = 0 := by
  unfold trackingErrorSq
  ring

/-- **Tracking error non-negativity** when `cov ≤ σ_p · σ_b` (Cauchy-Schwarz
bound): `σ_active² ≥ (σ_p - σ_b)²`. -/
lemma trackingErrorSq_ge_diff_sq (σ_p σ_b cov : ℝ) (h_cs : cov ≤ σ_p * σ_b) :
    (σ_p - σ_b) ^ 2 ≤ trackingErrorSq σ_p σ_b cov := by
  unfold trackingErrorSq
  nlinarith [h_cs]

variable {ι : Type*}

/-- **Gain-to-pain ratio** over a finite period set `s` with returns `r`: total
gains `∑ r⁺` over total losses `∑ r⁻` (Schwager). -/
noncomputable def gainToPain (s : Finset ι) (r : ι → ℝ) : ℝ :=
  (∑ i ∈ s, (r i)⁺) / (∑ i ∈ s, (r i)⁻)

/-- **Gain-to-pain is nonnegative**: both legs are sums of positive/negative
parts. Unconditionally — with no losses the denominator is `0` and the ratio is
`0`, which the statement already covers. -/
lemma gainToPain_nonneg (s : Finset ι) (r : ι → ℝ) : 0 ≤ gainToPain s r :=
  div_nonneg (Finset.sum_nonneg fun _ _ ↦ posPart_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ negPart_nonneg _)

/-- **Gain-to-pain exceeds one exactly on a profitable period set**: since
`r⁺ - r⁻ = r` summand-wise, `∑ r⁺ ≥ ∑ r⁻` says precisely `∑ r ≥ 0`. Here the
positive-pain hypothesis is load-bearing — it is what makes the quotient
comparable to `1`. -/
lemma one_le_gainToPain_iff (s : Finset ι) (r : ι → ℝ)
    (h : 0 < ∑ i ∈ s, (r i)⁻) :
    1 ≤ gainToPain s r ↔ 0 ≤ ∑ i ∈ s, r i := by
  rw [gainToPain, one_le_div h, ← sub_nonneg, ← Finset.sum_sub_distrib]
  simp [posPart_sub_negPart]

/-- **Upside-capture ratio** over the up-market periods `up`: portfolio gains
`∑ p` over benchmark gains `∑ b` (Morningstar). -/
noncomputable def upCapture (up : Finset ι) (p b : ι → ℝ) : ℝ :=
  (∑ i ∈ up, p i) / (∑ i ∈ up, b i)

/-- **Upside capture is homogeneous of degree one in the portfolio leg**: the
scalar factors out of the numerator sum, and `mul_div_assoc` carries it past the
benchmark leg with no nonvanishing condition. -/
lemma upCapture_smul (up : Finset ι) (p b : ι → ℝ) (c : ℝ) :
    upCapture up (c • p) b = c * upCapture up p b := by
  simp [upCapture, ← Finset.mul_sum, mul_div_assoc]

end MathFin
