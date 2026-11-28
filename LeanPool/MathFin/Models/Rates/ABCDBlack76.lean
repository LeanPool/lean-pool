/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralGaussian
public import LeanPool.MathFin.Models.Rates.ABCDVolatility
public import LeanPool.MathFin.Models.Forwards.Black76

/-!
# ABCD volatility prices through Black-76 at its root-mean-square

`Models/Rates/ABCDVolatility.lean` gives the ABCD instantaneous volatility
`f(τ) = (a + bτ)e^{−cτ} + d` of a forward rate as a function of its time to maturity `τ`, and
the closed form of its integrated variance `v(T) = ∫₀ᵀ f(τ)² dτ`. This file feeds that shape
to a forward and prices a call on it.

The forward fixing at `T` has, at calendar time `u`, the volatility `f(T − u)`. Driftless and
lognormal (as under its own forward measure), it is, in solved form,

  `F_T = F₀ · exp(−v(T)/2 + ∫₀ᵀ f(T − u) dB_u)`.

The stochastic integral is the Wiener integral of a deterministic integrand, so by
`wienerIntegralLp_hasLaw_gaussian` (`Probability/Brownian/Wiener/WienerIntegralGaussian.lean`) it is
centred Gaussian with variance `∫₀ᵀ f(T − u)² du = v(T)`, the ABCD closed form
(`abcdWienerIntegral_hasLaw`). Standardising it puts the forward in the Black–Scholes shape at
the volatility `σ_bar = √(v(T)/T)`, the root-mean-square of the instantaneous volatility over
`[0, T]`, and `black_futures_formula` (`Models/Forwards/Black76.lean`) prices the call: the
`e^{−rT}`-discounted call on `F_T` is the Black-76 price at `σ_bar`
(`abcdForward_call_eq_black76`). This is the computation behind quoting a caplet's Black
volatility as the root-mean-square of the instantaneous one (Rebonato); the caplet itself is not
modelled (see the scope note).

**Scope.** The forward is taken in its solved form; the SDE `dF = F f(T − u) dB` it solves is
cited, not proved, as for the Vasicek short rate (`Models/Rates/VasicekSDEGaussian.lean`). The
expectation is under the probability measure carrying the Brownian motion, read as the
forward measure; no change of measure is built. The discounting is the factor `e^{−rT}` of
`black_futures_formula`; the caplet's accrual `δ` and payment-date discount factor
`P(0, T + δ)` are not modelled.

## Main definitions

* `abcdKernel`: the integrand `u ↦ abcdVol a b c d (T - u)` of the forward fixing at `T`.
* `abcdKernelLp`: `abcdKernel` as an element of `L²((0, T])`.
* `abcdTotalVar`: the ABCD total variance `v(T)`, in the closed form of `abcdVol_sq_integral_zero`.
* `abcdForward`: the forward fixing `F₀ * exp (-v(T)/2 + ∫₀ᵀ f(T - u) dB_u)`, for a pre-Brownian
  motion `B`.
* `abcdRMSVol`: the root-mean-square volatility `√(v(T)/T)`.

## Main results

* `abcdKernel_integral_sq` — `∫_{(0,T]} f(T − u)² du = v(T)`, for `c ≠ 0`.
* `abcdWienerIntegral_hasLaw` — `∫₀ᵀ f(T − u) dB_u ~ N(0, v(T))`, for `c ≠ 0`.
* `abcdForward_call_eq_black76` — the discounted call on the ABCD forward is Black-76 at `σ_bar`.

## References

* [F. Black, *The pricing of commodity contracts*][Black1976]
* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006], ch.
  6
* [R. Rebonato, *Modern Pricing of Interest-Rate Derivatives: The LIBOR Market Model and
  Beyond*][Rebonato2002]

## Tags

ABCD volatility, Black-76, caplet volatility, Wiener integral, forward rate volatility, Rebonato,
MSC 91G30, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open WienerIntegralL2

/-- The ABCD integrand of the forward fixing at `T`: at calendar time `u` its volatility is the
ABCD shape at the time to maturity `T − u`. -/
noncomputable def abcdKernel (a b c d T : ℝ) : ℝ → ℝ := fun u ↦ abcdVol a b c d (T - u)

/-- The ABCD integrand is in `L²((0, T])`: it is continuous, hence bounded on `[0, T]`. -/
lemma abcdKernel_memLp (a b c d : ℝ) (T : ℝ≥0) :
    MemLp (abcdKernel a b c d T) 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
  have hcont : Continuous (abcdKernel a b c d T) := by
    unfold abcdKernel abcdVol
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (T : ℝ))).exists_bound_of_continuousOn
    hcont.continuousOn
  refine (memLp_top_of_bound hcont.aestronglyMeasurable C ?_).mono_exponent le_top
  exact (ae_restrict_iff' measurableSet_Ioc).mpr
    (ae_of_all _ fun u hu ↦ hC u (Ioc_subset_Icc_self hu))

/-- The ABCD integrand as an element of `L²((0, T])`. -/
noncomputable def abcdKernelLp (a b c d : ℝ) (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  (abcdKernel_memLp a b c d T).toLp _

/-- The total integrated variance `v(T) = ∫₀ᵀ f(τ)² dτ`, in the closed form of
`abcdVol_sq_integral_zero`. -/
noncomputable def abcdTotalVar (a b c d T : ℝ) : ℝ :=
  abcdIntegratedVarAntideriv a b c d T - abcdIntegratedVarAntideriv a b c d 0

/-- **The integrand's square integrates to the ABCD total variance**:
`∫_{(0,T]} f(T − u)² du = v(T)`, for `c ≠ 0`, by the substitution `τ = T − u` and
`abcdVol_sq_integral_zero`. -/
lemma abcdKernel_integral_sq (a b c d : ℝ) (hc : c ≠ 0) (T : ℝ≥0) :
    ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (abcdKernel a b c d T u) ^ 2 ∂volume
      = abcdTotalVar a b c d T := by
  rw [← intervalIntegral.integral_of_le (NNReal.coe_nonneg T)]
  simp only [abcdKernel]
  rw [intervalIntegral.integral_comp_sub_left (fun τ ↦ abcdVol a b c d τ ^ 2), sub_self,
    sub_zero]
  exact abcdVol_sq_integral_zero a b c d T hc

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The ABCD stochastic integral is Gaussian with the ABCD total variance**:
`∫₀ᵀ f(T − u) dB_u ~ N(0, v(T))`, for `c ≠ 0` — the Wiener integral of a deterministic
integrand (`wienerIntegralLp_hasLaw_gaussian`) with its variance in closed form. -/
theorem abcdWienerIntegral_hasLaw (hB : IsPreBrownianReal B μ) (a b c d : ℝ) (hc : c ≠ 0)
    (T : ℝ≥0) :
    HasLaw (fun ω ↦ wienerIntegralLp B hB T (abcdKernelLp a b c d T) ω)
      (gaussianReal 0 (abcdTotalVar a b c d T).toNNReal) μ :=
  wienerIntegralLp_hasLaw_gaussian_of_integral_sq hB T (abcdKernelLp a b c d T)
    ((abcdKernel_memLp a b c d T).integral_sq_toLp.trans (abcdKernel_integral_sq a b c d hc T))

/-- The forward fixing at `T` under ABCD volatility, in solved form:
`F_T = F₀ · exp(−v(T)/2 + ∫₀ᵀ f(T − u) dB_u)`. -/
noncomputable def abcdForward (hB : IsPreBrownianReal B μ) (F₀ a b c d : ℝ) (T : ℝ≥0)
    (ω : Ω) : ℝ :=
  F₀ * Real.exp (-(abcdTotalVar a b c d T / 2) + wienerIntegralLp B hB T (abcdKernelLp a b c d T) ω)

/-- The root-mean-square ABCD volatility over `[0, T]`: `σ_bar = √(v(T)/T)`. -/
noncomputable def abcdRMSVol (a b c d T : ℝ) : ℝ := Real.sqrt (abcdTotalVar a b c d T / T)

/-- **The discounted call on the ABCD forward is Black-76 at the root-mean-square volatility.**
For `F₀, K, T > 0`, `c ≠ 0` and a positive total variance `v(T)`,
`𝔼[e^{−rT}·(F_T − K)⁺] = e^{−rT}·(F₀Φ(d₁) − KΦ(d₂))` with `d₁, d₂` at `σ_bar = √(v(T)/T)`. The
standardised integral `(∫₀ᵀ f(T − u) dB_u)/√v(T)` is the standard normal of `BSCallHyp`, and
`black_futures_formula` prices the call. -/
theorem abcdForward_call_eq_black76 (hB : IsPreBrownianReal B μ) {F₀ K : ℝ} (r a b c d : ℝ)
    (hc : c ≠ 0) {T : ℝ≥0} (hF : 0 < F₀) (hK : 0 < K) (hT : 0 < (T : ℝ))
    (hv : 0 < abcdTotalVar a b c d T) :
    ∫ ω, Real.exp (-r * T) * max (abcdForward hB F₀ a b c d T ω - K) 0 ∂μ
      = Real.exp (-r * T) * (F₀ * Phi (bsd1 F₀ K 0 (abcdRMSVol a b c d T) T)
          - K * Phi (bsd2 F₀ K 0 (abcdRMSVol a b c d T) T)) := by
  have hsv : Real.sqrt (abcdTotalVar a b c d T) ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have hT0 : (T : ℝ) ≠ 0 := hT.ne'
  have hZ : HasLaw (fun ω ↦ wienerIntegralLp B hB T (abcdKernelLp a b c d T) ω
      / Real.sqrt (abcdTotalVar a b c d T)) (gaussianReal 0 1) μ := by
    have h := gaussianReal_div_const (abcdWienerIntegral_hasLaw hB a b c d hc T)
      (Real.sqrt (abcdTotalVar a b c d T))
    rw [zero_div] at h
    convert h using 2
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_one, NNReal.coe_div, NNReal.coe_mk, Real.sq_sqrt hv.le,
      Real.coe_toNNReal _ hv.le, div_self hv.ne']
  have hhyp : BSCallHyp μ F₀ K 0 (abcdRMSVol a b c d T) T
      (fun ω ↦ wienerIntegralLp B hB T (abcdKernelLp a b c d T) ω
        / Real.sqrt (abcdTotalVar a b c d T)) :=
    ⟨hF, hK, Real.sqrt_pos.mpr (div_pos hv hT), hT, hZ⟩
  have hsq : abcdRMSVol a b c d T ^ 2 = abcdTotalVar a b c d T / T :=
    Real.sq_sqrt (div_pos hv hT).le
  have hmul : abcdRMSVol a b c d T * Real.sqrt T = Real.sqrt (abcdTotalVar a b c d T) := by
    rw [abcdRMSVol, ← Real.sqrt_mul (div_pos hv hT).le, div_mul_cancel₀ _ hT.ne']
  have hterm (ω : Ω) : bsTerminal F₀ 0 (abcdRMSVol a b c d T) T
      (wienerIntegralLp B hB T (abcdKernelLp a b c d T) ω / Real.sqrt (abcdTotalVar a b c d T))
      = abcdForward hB F₀ a b c d T ω := by
    rw [bsTerminal, abcdForward, hmul, hsq]
    congr 2
    field_simp
    ring
  have h := black_futures_formula hhyp r
  simp only [hterm] at h
  exact h

end MathFin
