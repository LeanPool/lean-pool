/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.CenteredIndicator
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.Numerics
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# BadEventCeiling

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the Markov-plus-`[0,1]`-ceiling engine of the bad-event sum

Nothing in this file mentions Section 3 carriers; the Section 3 instances live
in `BadEventIngredients.lean`.

## The two mechanisms

**(1) Indicator pricing against a two-summand tail bound.**  The proved
bad-event probability (`bad_event_estimate`) is a *sum of two* exponentials —
the oscillation lane `exp(-a)` and the doubly-exponential ellipticity lane
`exp(-b)` — records that the printed `e.badevent.indicator.propagate` wrongly
discards the second summand.  `isBigOWith_gammaSigma_indicator_of_two_exp`
keeps both:

```
    mu.real E <= exp(-a) + exp(-b)
      ==>  1_E <= O_{Gamma_rho}( (4/a)^{1/rho} + (4/b)^{1/rho} ) ,
```

with **no** lower bound on `a` or `b` beyond positivity.  The reason a bound
such as `min(a,b) >= log 2` is *not* needed is the deterministic ceiling `1_E
<= 1`: when the printed amplitude is already `>= 1` the conclusion is free, and
when it is `< 1` the exponent `x := A^{-rho}` is automatically `> 1`, which is
exactly the margin the union of the two lanes costs.  The union itself is the
proved `Provider.Percolation.exp_add_exp_le`
(`Provider/Percolation/Numerics.lean`), consumed at `4x <= a`, `4x <= b`, `1 <=
x`.

**(2) The `rho`-th power of a `[0,1]`-valued mean.** records that the
manuscript's *"crude application of the triangle inequality
`e.Gamma.sigma.triangle`"* is **not** the mechanism of the display

```
    ( avsum_z 1_{not Q(l,l-h,z)} )^rho  <=  O_{Gamma_1}( C rho^{-1} cstar^{-1} 3^{5h} cgamma ) :
```

the countable `Gamma_sigma` triangle costs `(1+|log s|)/s`, which the display's
own `eps^{-C}` cannot absorb.  What proves it is **Markov's inequality plus the
deterministic `[0,1]` ceiling**, applied to the normalized sum, followed by
CoarseGraining's free power rule `isBigOWith_gammaSigma_rpow` at `p = rho`
(which sends `Gamma_rho` to `Gamma_{rho/rho} = Gamma_1` and the scale `A` to
`A^rho`).  The printed `rho^{-1}` is the *join constant between the Markov
branch and the boundedness branch*, not a triangle cost; it is obtained here at
the explicit constant `4`.  No union bound, no `log |F|`, no grid cardinality,
and neither `gammaGrowthConst` nor `gammaTriangleConst` is invoked.

## Consumer fit: the `[0,1]` ceiling, never an Orlicz product

The display `e.local.bad.events.summed` multiplies `e.mathcalE.crude.bound`
against the bad-event factor

```
    W  =  max_l 3^{-s(m-l)/2} ( avsum_z 1_{not Q(l,l-h,z)} )^{s/d} .
```

(The `Gamma_1 x Gamma_1` lane fails separately, on amplitude: polynomially
small against an exponentially small rare budget.)

The mechanism that *does* work is `W`'s own pointwise `[0,1]` ceiling, exported
here as `indicatorAverage_mem_Icc` and `weightedIndicatorAverage_rpow_mem_Icc`.
At `0 <= W <= 1` and `Y >= 0` one has `Y . W <= Y` pointwise, so the crude
bound's `Gamma_1` lane and its `Gamma_{2/7}` lane both pass through
**unchanged** — the printed amplitudes verbatim, with no index loss — and only
the deterministic shift of `e.mathcalE.crude.bound` consumes the factor's own
`Gamma_1` smallness.  The output is exactly the printed `Gamma_1 + Gamma_{2/7}`
shape of `e.local.bad.events.summed`.

The `Y >= 0` in that pointwise step is not free, and the pass-through is at
unchanged amplitude only **after** the free witness clamp
`Provider.Tail.isBigOWith_max_zero` (`Provider/Tail/TailSqrt.lean`) has replaced
each of the two Orlicz witnesses by `max 0 (.)` at the *same* scale: the
witnesses of a two-term one-sided display are only known to be measurable and
dominating, never nonnegative.

## Main results

* `Algsuperdiff.Section3.Provider.MultiscaleEstimate.isBigOWith_gammaSigma_of_le_one`
* `Algsuperdiff.Section3.Provider.MultiscaleEstimate.boundedMean_isBigOWith_gammaSigma`
* `Algsuperdiff.Section3.Provider.MultiscaleEstimate.boundedMean_rpow_isBigOWith_gammaOne`
* `Algsuperdiff.Section3.Provider.MultiscaleEstimate.boundedMean_rpow_isBigOWith_gammaOne_of_two_exp`
* `Algsuperdiff.Section3.Provider.MultiscaleEstimate.indicatorAverage_mem_Icc`
* `Algsuperdiff.Section3.Provider.MultiscaleEstimate.weightedIndicatorAverage_rpow_mem_Icc`
* `Algsuperdiff.Section3.Provider.MultiscaleEstimate.indicatorAverage_rpow_isBigOWith_gammaOne_of_two_exp`

## In-repo consumed set

`Provider.Orlicz.isBigOWith_gammaSigma_indicator_of_le`,
`Provider.Percolation.exp_add_exp_le`; from CoarseGraining,
`Homogenization.IndependentSums.gammaSigma`, `isBigOWith_gammaSigma_iff`,
`isBigOWith_gammaSigma_rpow`, `upperTailEvent`, `mem_upperTailEvent`.  Nothing
else from this repository is used.

## References

* ABK26, proof of `p.multiscale.estimate`; `e.indc.O.sigma`;
  `e.Gamma.sigma.triangle`; `e.multGammasig`.
-/

namespace Algsuperdiff.Section3.Provider.MultiscaleEstimate

open _root_.MeasureTheory
open _root_.HCPolySupport.IndependentSums

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## 1. The deterministic `[0,1]` ceiling -/

/-- **The ceiling branch.**  An observable bounded above by `1` satisfies every
stretched-exponential upper-tail relation at every scale `A ≥ 1`, because the
tail event `{X > A t}` is empty for `t ≥ 1`.

This is one of the two branches of the manuscript's averaged-indicator display,
and it is also what makes the two-summand indicator bound below unconditional:
whenever the printed amplitude is already at least one, there is nothing to
prove. -/
theorem isBigOWith_gammaSigma_of_le_one {X : Ω → ℝ} {sigma A : ℝ}
    (h1 : ∀ omega, X omega ≤ 1) (hA : 1 ≤ A) :
    IsBigOWith μ (gammaSigma sigma) X A := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have hAt : (1 : ℝ) ≤ A * t := by nlinarith
  have hempty : upperTailEvent X (A * t) = (∅ : Set Ω) := by
    ext omega
    simp only [mem_upperTailEvent, Set.mem_empty_iff_false, iff_false, not_lt]
    exact (h1 omega).trans hAt
  rw [hempty, measureReal_empty]
  positivity

/-! ## 2. The two-lane exponential arithmetic

The union of the two lanes is the proved `Provider.Percolation.exp_add_exp_le`
(`Provider/Percolation/Numerics.lean`): at `1 ≤ x`, `4x ≤ a` and `4x ≤ b` one
has `-a + 1 ≤ -x` and `-b + 1 ≤ -x`, hence `exp(-a) + exp(-b) ≤ exp(-x)`. -/

/-- If `4 / c ≤ K` with `c, K > 0` then `4 K⁻¹ ≤ c`.  The elementary
rearrangement used to read both lanes' amplitudes off the joint scale. -/
private theorem four_mul_inv_le_of_le {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (h : 4 / c ≤ K) : 4 * K⁻¹ ≤ c := by
  have hmul : 4 / c * c = 4 := by field_simp
  have h1 : (4 : ℝ) ≤ K * c := by
    have hstep := mul_le_mul_of_nonneg_right h hc.le
    rwa [hmul] at hstep
  have h2 := mul_le_mul_of_nonneg_right h1 (inv_pos.2 hK).le
  rwa [mul_comm K c, mul_assoc, mul_inv_cancel₀ (ne_of_gt hK), mul_one] at h2

/-- A positive real below one has reciprocal at least one. -/
private theorem one_le_inv_of_lt_one {K : ℝ} (hK : 0 < K) (h : K < 1) :
    1 ≤ K⁻¹ := by
  have hmul : K * K⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hK)
  nlinarith [inv_pos.2 hK]

/-! ## 4. The arithmetic core of the Markov/ceiling join (abstract reals) -/

/-- `x - 1 ≤ x log x` for every `x > 0`: the `log y ≤ y - 1` bound at `y = x⁻¹`,
multiplied by `x`.  This is the crude form of `sup_{(0,1)} x|log x| = 1/e`, and
it is all the two-branch join of `boundedMean_isBigOWith_gammaSigma` needs. -/
private theorem sub_one_le_mul_log {x : ℝ} (hx : 0 < x) :
    x - 1 ≤ x * Real.log x := by
  have hinv : Real.log x⁻¹ ≤ x⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
  rw [Real.log_inv] at hinv
  have hlog : 1 - x⁻¹ ≤ Real.log x := by linarith
  have hmul : x * (1 - x⁻¹) ≤ x * Real.log x :=
    mul_le_mul_of_nonneg_left hlog hx.le
  have hcancel : x * (1 - x⁻¹) = x - 1 := by field_simp
  linarith [hcancel ▸ hmul]

/-- **The join inequality.**  For `0 < rho ≤ 2` and `K > 0`,

```
    (4 rho^{-1} K)^{-1} - K^{-1}  <=  rho^{-1} log (4 rho^{-1} K) .
```

The left side is the exponent `t^rho - 1/K` at its worst admissible value on
the Markov branch; the right side is `log A` at `A = (4 rho^{-1} K)^{1/rho}`.
Clearing the common denominator `4K` turns it into `rho - 4 ≤ x log x` at `x:=
4 rho^{-1} K`, which is `sub_one_le_mul_log` (`x - 1 ≤ x log x`) together with
`rho - 3 ≤ x`. -/
private theorem join_algebra {rho K : ℝ} (hrho : 0 < rho) (hrho2 : rho ≤ 2)
    (hK : 0 < K) :
    (4 * rho⁻¹ * K)⁻¹ - K⁻¹ ≤ rho⁻¹ * Real.log (4 * rho⁻¹ * K) := by
  have hx : (0 : ℝ) < 4 * rho⁻¹ * K := by positivity
  have h4K : (0 : ℝ) < 4 * K := by positivity
  have hcore : rho - 4 ≤ (4 * rho⁻¹ * K) * Real.log (4 * rho⁻¹ * K) := by
    have h := sub_one_le_mul_log hx
    linarith
  refine le_of_mul_le_mul_right ?_ h4K
  have key : ((4 * rho⁻¹ * K)⁻¹ - K⁻¹) * (4 * K) = rho - 4 := by
    field_simp
  have key2 : (rho⁻¹ * Real.log (4 * rho⁻¹ * K)) * (4 * K)
      = (4 * rho⁻¹ * K) * Real.log (4 * rho⁻¹ * K) := by
    field_simp
  rw [key, key2]
  exact hcore

/-! ## 5. Markov plus boundedness -/

/-- **The `Gamma_rho` bound of the Markov/ceiling join.**  A `[0,1]`-valued
observable whose mean is at most `e^{-1/K}` is `O_{Gamma_rho}` at scale
`(4 rho^{-1} K)^{1/rho}`, for every `rho ∈ (0,2]`.

Two branches on the tail height `A t`:

* `A t ≥ 1`: the event `{X > A t}` is **empty**, because `X ≤ 1`;
* `A t < 1`: Markov gives mass `≤ e^{-1/K}/(A t)`, and `join_algebra` says this
  is `≤ e^{-t^rho}` (using `t < A⁻¹`, hence `t^rho ≤ (A^rho)⁻¹ = rho/(4K)`).

The `rho^{-1}` in the scale is exactly what makes the two branches meet: it is
the join constant, and not a triangle-inequality cost. -/
theorem boundedMean_isBigOWith_gammaSigma [IsFiniteMeasure μ]
    {X : Ω → ℝ} {K rho : ℝ} (hrho : 0 < rho) (hrho2 : rho ≤ 2) (hK : 0 < K)
    (hmeas : AEStronglyMeasurable X μ)
    (h0 : ∀ omega, 0 ≤ X omega) (h1 : ∀ omega, X omega ≤ 1)
    (hmean : ∫ omega, X omega ∂μ ≤ Real.exp (-K⁻¹)) :
    IsBigOWith μ (gammaSigma rho) X ((4 * rho⁻¹ * K) ^ rho⁻¹) := by
  have hxpos : (0 : ℝ) < 4 * rho⁻¹ * K := by positivity
  set A : ℝ := (4 * rho⁻¹ * K) ^ rho⁻¹ with hAdef
  have hA0 : 0 < A := Real.rpow_pos_of_pos hxpos _
  have hApow : A ^ rho = 4 * rho⁻¹ * K := by
    rw [hAdef, ← Real.rpow_mul hxpos.le, inv_mul_cancel₀ (ne_of_gt hrho),
      Real.rpow_one]
  have hint : Integrable X μ := by
    refine (integrable_const (1 : ℝ)).mono' hmeas
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 omega)]
    exact h1 omega
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  rcases le_or_gt 1 (A * t) with hcase | hcase
  · have hempty : upperTailEvent X (A * t) = (∅ : Set Ω) := by
      ext omega
      simp only [mem_upperTailEvent, Set.mem_empty_iff_false, iff_false, not_lt]
      exact (h1 omega).trans hcase
    rw [hempty, measureReal_empty]
    positivity
  · have hAt0 : 0 < A * t := by positivity
    have htA : t < A⁻¹ := by
      have hAA : A * A⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hA0)
      have hstep : A * t < A * A⁻¹ := by rw [hAA]; exact hcase
      exact lt_of_mul_lt_mul_left hstep hA0.le
    have htpow : t ^ rho ≤ (4 * rho⁻¹ * K)⁻¹ := by
      have hstep : t ^ rho ≤ (A⁻¹) ^ rho := Real.rpow_le_rpow ht0.le htA.le hrho.le
      rwa [Real.inv_rpow hA0.le, hApow] at hstep
    have hmk := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall h0) hint (A * t)
    have hsub : upperTailEvent X (A * t) ⊆ {omega | A * t ≤ X omega} := by
      intro omega homega
      have hlt : A * t < X omega := homega
      exact hlt.le
    have hmass : (A * t) * μ.real (upperTailEvent X (A * t)) ≤ Real.exp (-K⁻¹) :=
      le_trans (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hAt0.le)
        (le_trans hmk hmean)
    have hcmp : Real.exp (-K⁻¹) ≤ (A * t) * Real.exp (-(t ^ rho)) := by
      have hlogA : Real.log A = rho⁻¹ * Real.log (4 * rho⁻¹ * K) := by
        rw [hAdef, Real.log_rpow hxpos]
      have hjoin : (4 * rho⁻¹ * K)⁻¹ - K⁻¹ ≤ Real.log A := by
        rw [hlogA]; exact join_algebra hrho hrho2 hK
      have hstep : t ^ rho - K⁻¹ ≤ Real.log A := by linarith
      have hexp : Real.exp (t ^ rho - K⁻¹) ≤ A :=
        le_trans (Real.exp_le_exp.2 hstep) (le_of_eq (Real.exp_log hA0))
      have hAt : Real.exp (t ^ rho - K⁻¹) ≤ A * t :=
        le_trans hexp (le_mul_of_one_le_right hA0.le ht)
      have hsplit : Real.exp (t ^ rho - K⁻¹) * Real.exp (-(t ^ rho))
          = Real.exp (-K⁻¹) := by
        rw [← Real.exp_add]
        ring_nf
      calc Real.exp (-K⁻¹)
          = Real.exp (t ^ rho - K⁻¹) * Real.exp (-(t ^ rho)) := hsplit.symm
        _ ≤ (A * t) * Real.exp (-(t ^ rho)) :=
            mul_le_mul_of_nonneg_right hAt (Real.exp_pos _).le
    refine le_of_mul_le_mul_left ?_ hAt0
    exact le_trans hmass hcmp

/-- **The `Gamma_1` bound after the free power conversion.**  A `[0,1]`-valued
observable with mean at most `e^{-1/K}` satisfies

```
    X^rho  <=  O_{Gamma_1}( 4 rho^{-1} K )      (0 < rho <= 2) .
```

This is `boundedMean_isBigOWith_gammaSigma` followed by CoarseGraining's power
rule `isBigOWith_gammaSigma_rpow` at `p = rho`, which is exact and free: it
sends `Gamma_rho` to `Gamma_{rho/rho} = Gamma_1` and the scale `A` to `A^rho =
4 rho^{-1} K`. -/
theorem boundedMean_rpow_isBigOWith_gammaOne [IsFiniteMeasure μ]
    {X : Ω → ℝ} {K rho : ℝ} (hrho : 0 < rho) (hrho2 : rho ≤ 2) (hK : 0 < K)
    (hmeas : AEStronglyMeasurable X μ)
    (h0 : ∀ omega, 0 ≤ X omega) (h1 : ∀ omega, X omega ≤ 1)
    (hmean : ∫ omega, X omega ∂μ ≤ Real.exp (-K⁻¹)) :
    IsBigOWith μ (gammaSigma 1) (fun omega => X omega ^ rho)
      (4 * rho⁻¹ * K) := by
  have hxpos : (0 : ℝ) < 4 * rho⁻¹ * K := by positivity
  have hbase := boundedMean_isBigOWith_gammaSigma hrho hrho2 hK hmeas h0 h1 hmean
  have hconv := isBigOWith_gammaSigma_rpow (μ := μ) (X := X) (σ := rho) (p := rho)
    (A := (4 * rho⁻¹ * K) ^ rho⁻¹) hrho (Real.rpow_nonneg hxpos.le _) h0 hbase
  have hApow : ((4 * rho⁻¹ * K) ^ rho⁻¹) ^ rho = 4 * rho⁻¹ * K := by
    rw [← Real.rpow_mul hxpos.le, inv_mul_cancel₀ (ne_of_gt hrho), Real.rpow_one]
  rwa [div_self (ne_of_gt hrho), hApow] at hconv

/-- **The two-lane form of the Markov/ceiling display.**  A `[0,1]`-valued
observable whose mean obeys the *two-summand* bound
`E[X] ≤ exp(-a) + exp(-b)` satisfies

```
    X^rho  <=  O_{Gamma_1}( 4 rho^{-1} (4/a + 4/b) )     (0 < rho <= 2) .
```

Both lanes survive at their own amplitude, as requires; the manuscript's
display keeps only the first.  As in
`isBigOWith_gammaSigma_indicator_of_two_exp`, no size hypothesis on `a` or `b`
is needed: if `K := 4/a + 4/b ≥ 1` the deterministic ceiling already gives the
conclusion (the amplitude is then `≥ 4 rho^{-1} ≥ 2`), and otherwise `K⁻¹ > 1`
with `4 K⁻¹ ≤ a` and `4 K⁻¹ ≤ b`, which is the input of
`Provider.Percolation.exp_add_exp_le`. -/
theorem boundedMean_rpow_isBigOWith_gammaOne_of_two_exp [IsFiniteMeasure μ]
    {X : Ω → ℝ} {a b rho : ℝ} (hrho : 0 < rho) (hrho2 : rho ≤ 2)
    (ha : 0 < a) (hb : 0 < b)
    (hmeas : AEStronglyMeasurable X μ)
    (h0 : ∀ omega, 0 ≤ X omega) (h1 : ∀ omega, X omega ≤ 1)
    (hmean : ∫ omega, X omega ∂μ ≤ Real.exp (-a) + Real.exp (-b)) :
    IsBigOWith μ (gammaSigma 1) (fun omega => X omega ^ rho)
      (4 * rho⁻¹ * (4 / a + 4 / b)) := by
  have hrinv : 0 < rho⁻¹ := inv_pos.2 hrho
  have hK : (0 : ℝ) < 4 / a + 4 / b := by positivity
  rcases le_or_gt 1 (4 / a + 4 / b) with hbig | hsmall
  · refine isBigOWith_gammaSigma_of_le_one (fun omega => ?_) ?_
    · exact Real.rpow_le_one (h0 omega) (h1 omega) hrho.le
    · have hrho' : (1 : ℝ) ≤ 4 * rho⁻¹ := by
        rw [le_mul_inv_iff₀ hrho]
        linarith
      nlinarith
  · have hinv : (1 : ℝ) ≤ (4 / a + 4 / b)⁻¹ := one_le_inv_of_lt_one hK hsmall
    have hKa : 4 * (4 / a + 4 / b)⁻¹ ≤ a :=
      four_mul_inv_le_of_le ha hK (by
        have := div_pos (show (0 : ℝ) < 4 by norm_num) hb
        linarith)
    have hKb : 4 * (4 / a + 4 / b)⁻¹ ≤ b :=
      four_mul_inv_le_of_le hb hK (by
        have := div_pos (show (0 : ℝ) < 4 by norm_num) ha
        linarith)
    have hunion : Real.exp (-a) + Real.exp (-b) ≤ Real.exp (-(4 / a + 4 / b)⁻¹) :=
      Provider.Percolation.exp_add_exp_le (by linarith) (by linarith)
    exact boundedMean_rpow_isBigOWith_gammaOne hrho hrho2 hK hmeas h0 h1
      (hmean.trans hunion)

/-! ## 6. The pointwise `[0,1]` ceiling of a weighted indicator average -/

omit [MeasurableSpace Ω] in
/-- **The pointwise ceiling.**  A volume-normalized average of indicators takes
values in `[0,1]` at every sample point, for an arbitrary finite index set — the
empty one included, where `(F.card : ℝ)⁻¹ = 0` makes the average `0`.

This is the deterministic fact behind the Markov/ceiling join below, and it is
also the *consumer mechanism* recorded: the bad-event factor of
`e.local.bad.events.summed` is built from this average, hence is `[0,1]`-valued
pointwise, hence multiplies the crude bound's lanes without touching their
Orlicz indices. -/
theorem indicatorAverage_mem_Icc {iota : Type*} (F : Finset iota)
    (B : iota → Set Ω) (omega : Ω) :
    (F.card : ℝ)⁻¹ * ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega ∈
      Set.Icc (0 : ℝ) 1 := by
  classical
  have hind0 : ∀ z : iota, 0 ≤ (B z).indicator (fun _ => (1 : ℝ)) omega :=
    fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) omega
  have hind1 : ∀ z : iota, (B z).indicator (fun _ => (1 : ℝ)) omega ≤ 1 := by
    intro z
    by_cases hz : omega ∈ B z
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  have hsum0 : 0 ≤ ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega :=
    Finset.sum_nonneg fun z _ => hind0 z
  have hsum : ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega ≤ (F.card : ℝ) := by
    calc ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega
        ≤ ∑ _z ∈ F, (1 : ℝ) := Finset.sum_le_sum fun z _ => hind1 z
      _ = (F.card : ℝ) := by simp
  rcases Nat.eq_zero_or_pos F.card with hcard | hcard
  · have hF : F = (∅ : Finset iota) := Finset.card_eq_zero.1 hcard
    subst hF
    simp
  · have hc : (0 : ℝ) < (F.card : ℝ) := by exact_mod_cast hcard
    refine Set.mem_Icc.2 ⟨mul_nonneg (inv_pos.2 hc).le hsum0, ?_⟩
    have hstep := mul_le_mul_of_nonneg_left hsum (inv_pos.2 hc).le
    rwa [inv_mul_cancel₀ (ne_of_gt hc)] at hstep

omit [MeasurableSpace Ω] in
/-- **The weighted `rho`-th power of the ceiling.**  For a weight `w ∈ [0,1]`
and any exponent `rho ≥ 0`,

```
    0  <=  w . ( avsum_{z in F} 1_{B z} )^rho  <=  1        pointwise.
```

Consequently the crude bound's `Gamma_1` lane and its `Gamma_{2/7}` lane pass
through the product **unchanged**, at their printed amplitudes and indices, and
only the deterministic shift consumes the factor's own smallness.  No Orlicz
product `e.multGammasig` is taken; that route is index-refuted (`2/9 < 1/4`). -/
theorem weightedIndicatorAverage_rpow_mem_Icc {iota : Type*} (F : Finset iota)
    (B : iota → Set Ω) {w rho : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hrho : 0 ≤ rho)
    (omega : Ω) :
    w * ((F.card : ℝ)⁻¹ * ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega) ^ rho ∈
      Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := Set.mem_Icc.1 (indicatorAverage_mem_Icc F B omega)
  have hp0 : (0 : ℝ) ≤
      ((F.card : ℝ)⁻¹ * ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega) ^ rho :=
    Real.rpow_nonneg h0 _
  have hp1 :
      ((F.card : ℝ)⁻¹ * ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega) ^ rho ≤ 1 :=
    Real.rpow_le_one h0 h1 hrho
  exact Set.mem_Icc.2 ⟨mul_nonneg hw0 hp0, by nlinarith⟩

/-! ## 7. The averaged-indicator instance -/

/-- **The volume-normalized average of indicators, at a two-summand per-event
tail bound.**  If every event of a finite nonempty family has mass at most
`exp(-a) + exp(-b)`, then for every `rho ∈ (0,2]`

```
    ( avsum_{z in F} 1_{B z} )^rho  <=  O_{Gamma_1}( 4 rho^{-1} (4/a + 4/b) ) .
```

The mean is computed by linearity — `E[ avsum_z 1_{B z} ] = avsum_z P[B z]` —
so **no union bound and no `log |F|` occurs**: means average, they do not add.
This is why the manuscript's display carries no grid-cardinality factor, and it
is the honest content of the sentence corrects. -/
theorem indicatorAverage_rpow_isBigOWith_gammaOne_of_two_exp [IsFiniteMeasure μ]
    {iota : Type*} {F : Finset iota} (hF : F.Nonempty) {B : iota → Set Ω}
    (hBmeas : ∀ z ∈ F, MeasurableSet (B z))
    {a b rho : ℝ} (hrho : 0 < rho) (hrho2 : rho ≤ 2) (ha : 0 < a) (hb : 0 < b)
    (hB : ∀ z ∈ F, μ.real (B z) ≤ Real.exp (-a) + Real.exp (-b)) :
    IsBigOWith μ (gammaSigma 1)
      (fun omega =>
        ((F.card : ℝ)⁻¹ * ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega) ^ rho)
      (4 * rho⁻¹ * (4 / a + 4 / b)) := by
  classical
  have hcard : (0 : ℝ) < (F.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hF
  have hind0 : ∀ (z : iota) (omega : Ω),
      0 ≤ (B z).indicator (fun _ => (1 : ℝ)) omega :=
    fun z omega => Set.indicator_nonneg (fun _ _ => zero_le_one) omega
  have hind1 : ∀ (z : iota) (omega : Ω),
      (B z).indicator (fun _ => (1 : ℝ)) omega ≤ 1 := by
    intro z omega
    by_cases homega : omega ∈ B z
    · simp [Set.indicator_of_mem homega]
    · simp [Set.indicator_of_notMem homega]
  have h0 : ∀ omega : Ω,
      0 ≤ (F.card : ℝ)⁻¹ * ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega :=
    fun omega => (Set.mem_Icc.1 (indicatorAverage_mem_Icc F B omega)).1
  have h1 : ∀ omega : Ω,
      (F.card : ℝ)⁻¹ * ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega ≤ 1 :=
    fun omega => (Set.mem_Icc.1 (indicatorAverage_mem_Icc F B omega)).2
  have hmS : Measurable
      (fun omega : Ω => ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega) :=
    Finset.measurable_sum F fun z hz => measurable_const.indicator (hBmeas z hz)
  have hmeasX : AEStronglyMeasurable
      (fun omega : Ω =>
        (F.card : ℝ)⁻¹ * ∑ z ∈ F, (B z).indicator (fun _ => (1 : ℝ)) omega) μ :=
    (hmS.const_mul _).aestronglyMeasurable
  have hintInd : ∀ z ∈ F, Integrable ((B z).indicator (fun _ => (1 : ℝ))) μ := by
    intro z hz
    refine (integrable_const (1 : ℝ)).mono'
      ((measurable_const.indicator (hBmeas z hz)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hind0 z omega)]
    exact hind1 z omega
  have hmean : ∫ omega, (F.card : ℝ)⁻¹ * ∑ z ∈ F,
      (B z).indicator (fun _ => (1 : ℝ)) omega ∂μ
      ≤ Real.exp (-a) + Real.exp (-b) := by
    have hsplit : ∫ omega, (F.card : ℝ)⁻¹ * ∑ z ∈ F,
        (B z).indicator (fun _ => (1 : ℝ)) omega ∂μ
        = (F.card : ℝ)⁻¹ * ∑ z ∈ F, μ.real (B z) := by
      rw [integral_const_mul, integral_finsetSum F hintInd]
      congr 1
      refine Finset.sum_congr rfl fun z hz => ?_
      rw [integral_indicator (hBmeas z hz), setIntegral_const, smul_eq_mul,
        mul_one, measureReal_def]
    rw [hsplit]
    have hsum : ∑ z ∈ F, μ.real (B z)
        ≤ (F.card : ℝ) * (Real.exp (-a) + Real.exp (-b)) := by
      calc ∑ z ∈ F, μ.real (B z)
          ≤ ∑ _z ∈ F, (Real.exp (-a) + Real.exp (-b)) :=
            Finset.sum_le_sum hB
        _ = (F.card : ℝ) * (Real.exp (-a) + Real.exp (-b)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hstep := mul_le_mul_of_nonneg_left hsum (inv_pos.2 hcard).le
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard), one_mul] at hstep
  exact boundedMean_rpow_isBigOWith_gammaOne_of_two_exp hrho hrho2 ha hb
    hmeasX h0 h1 hmean

end Algsuperdiff.Section3.Provider.MultiscaleEstimate
