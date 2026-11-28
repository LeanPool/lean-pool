/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralGaussian
public import LeanPool.MathFin.Models.Rates.VasicekSDE

/-!
# Vasicek terminal distribution of the Ornstein–Uhlenbeck solution (Itô→pricing bridge)

`Models/Rates/VasicekSDE.lean` *posited* the terminal law of the Vasicek short
rate `r_t ~ N(mean, var)` as closed-form `def`s, in the `BSCallHyp` style.

This file **derives** that law for the short rate in its Wiener representation. The Vasicek
SDE `dr_t = κ(θ − r_t)dt + σ dB_t` has, as a textbook fact cited and not proved here, the
solution

  `r_t = r₀ e^{−κt} + θ(1 − e^{−κt}) + σ ∫₀ᵗ e^{−κ(t−s)} dB_s`,

whose stochastic term is the Wiener integral of the **deterministic** integrand
`e^{−κ(t−s)}`. By `wienerIntegralLp_hasLaw_gaussian`
(`Probability/Brownian/Wiener/WienerIntegralGaussian.lean`) that integral is Gaussian, centred,
with variance its `L²`-norm `∫₀ᵗ e^{−2κ(t−s)} ds = (1 − e^{−2κt})/(2κ)` — exactly
`vasicekSDEVariance σ κ t / σ²`. The affine map `x ↦ mean + σ x` then sends the
law to `gaussianReal (vasicekSDEMean) (vasicekSDEVariance)`.

This is the **first consumer of the deterministic-integrand Itô tower in the
FixedIncome layer** — the analytic Wiener/Itô machinery becomes load-bearing in
a pricing module, closing the two-tower gap for the Vasicek short rate.

## Main definitions

* `vasicekKernel`, `vasicekKernelLp`: the diffusion kernel `s ↦ e^{−κ(T−s)}`, and the same kernel
  as an element of `L²((0, T])`.
* `vasicekKernelSqAntideriv`: the antiderivative `u ↦ e^{−2κ(T−u)}/(2κ)` of the squared kernel.
* `vasicekDiffusionTerm`: the Vasicek diffusion term `σ ∫₀ᵀ e^{−κ(T−s)} dB_s`.

## Main results

* `vasicekKernel_integral_sq`: `∫₀ᵀ (e^{−κ(T−s)})² ds = (1 − e^{−2κT})/(2κ)`.
* `vasicekShortRate_hasLaw_gaussian`: the genuine terminal short rate
  `mean + σ ∫₀ᵀ e^{−κ(T−s)} dB_s` has law `N(vasicekSDEMean, vasicekSDEVariance)`.

## References

* [O. Vasicek, *An equilibrium characterization of the term structure*][Vasicek1977]

## Tags

Vasicek model, Ornstein–Uhlenbeck, Wiener integral, Gaussian law, short rate,
Itô integral of deterministic integrand, MSC 60H10, MSC 91G30, MSC 60G15
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The Vasicek diffusion kernel `e^{−κ(T−s)}` as an `L²` integrand -/

/-- The Vasicek diffusion kernel `s ↦ e^{−κ(T−s)}`. -/
noncomputable def vasicekKernel (κ T : ℝ) : ℝ → ℝ := fun s ↦ Real.exp (-(κ * (T - s)))

/-- The kernel is in `L²((0, T])` (continuous, bounded by `1` on the support
for `κ ≥ 0`). -/
lemma vasicekKernel_memLp (κ : ℝ) (hκ : 0 ≤ κ) (T : ℝ≥0) :
    MemLp (vasicekKernel κ T) 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
  refine (memLp_top_of_bound (by unfold vasicekKernel; fun_prop) 1 ?_).mono_exponent le_top
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ ?_)
  intro s hs
  rw [vasicekKernel, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_one_iff.mpr ?_
  have hTs : 0 ≤ (T : ℝ) - s := by linarith [hs.2]
  nlinarith [mul_nonneg hκ hTs]

/-- The kernel as an element of `L²((0, T])`. -/
noncomputable def vasicekKernelLp (κ : ℝ) (hκ : 0 ≤ κ) (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  (vasicekKernel_memLp κ hκ T).toLp _

/-! ### The kernel's `L²`-norm is the Vasicek variance (the deterministic integral) -/

/-- The antiderivative `u ↦ e^{−2κ(T−u)}/(2κ)` of the squared diffusion kernel
`(e^{−κ(T−u)})²`. -/
noncomputable def vasicekKernelSqAntideriv (κ T u : ℝ) : ℝ :=
  Real.exp (-(2 * κ * (T - u))) / (2 * κ)

/-- For `κ ≠ 0`, `vasicekKernelSqAntideriv` differentiates to the squared kernel
`(e^{−κ(T−u)})² = e^{−2κ(T−u)}`. -/
lemma hasDerivAt_vasicekKernelSqAntideriv (κ T u : ℝ) (hκ : κ ≠ 0) :
    HasDerivAt (vasicekKernelSqAntideriv κ T) ((vasicekKernel κ T u) ^ 2) u := by
  have hsq : (vasicekKernel κ T u) ^ 2 = Real.exp (-(2 * κ * (T - u))) := by
    rw [vasicekKernel, sq, ← Real.exp_add]
    congr 1
    ring
  have h1 : HasDerivAt (fun u ↦ -(2 * κ * (T - u))) (2 * κ) u := by
    have : HasDerivAt (fun u ↦ -(2 * κ * (T - u))) (-(2 * κ * (-1))) u := by
      apply HasDerivAt.neg
      apply HasDerivAt.const_mul
      simpa using (hasDerivAt_id u).const_sub T
    simpa using this
  have h3 := ((Real.hasDerivAt_exp _).comp u h1).div_const (2 * κ)
  rw [hsq]
  rwa [mul_div_assoc, div_self (mul_ne_zero two_ne_zero hκ), mul_one] at h3

/-- The FTC form over any interval, for `κ ≠ 0`:
`∫_A^B (e^{−κ(T−u)})² du = e^{−2κ(T−B)}/(2κ) − e^{−2κ(T−A)}/(2κ)`. -/
lemma integral_vasicekKernel_sq_eq_sub (κ T A B : ℝ) (hκ : κ ≠ 0) :
    ∫ u in A..B, (vasicekKernel κ T u) ^ 2
      = vasicekKernelSqAntideriv κ T B - vasicekKernelSqAntideriv κ T A :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ hasDerivAt_vasicekKernelSqAntideriv κ T u hκ)
    (Continuous.intervalIntegrable (by unfold vasicekKernel; fun_prop) _ _)

/-- **The Riemann integral fixing the variance**:
`∫₀ᵀ (e^{−κ(T−s)})² ds = (1 − e^{−2κT})/(2κ)`, by the FTC with antiderivative
`vasicekKernelSqAntideriv`. -/
lemma vasicekKernel_integral_sq (κ : ℝ) (hκ : κ ≠ 0) (T : ℝ≥0) :
    ∫ s in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekKernel κ T s) ^ 2 ∂volume
      = (1 - Real.exp (-(2 * κ * T))) / (2 * κ) := by
  rw [← intervalIntegral.integral_of_le T.coe_nonneg, integral_vasicekKernel_sq_eq_sub κ T 0 T hκ]
  simp only [vasicekKernelSqAntideriv, sub_self, sub_zero, mul_zero, neg_zero, Real.exp_zero]
  ring

/-! ### The genuine terminal short rate and its derived Gaussian law -/

/-- The genuine Vasicek diffusion term `σ ∫₀ᵀ e^{−κ(T−s)} dB_s`. -/
noncomputable def vasicekDiffusionTerm (hB : IsPreBrownianReal B μ) (κ σ : ℝ)
    (hκ : 0 ≤ κ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  σ * (wienerIntegralLp B hB T (vasicekKernelLp κ hκ T) ω)

/-- **Vasicek terminal law, derived.** The short rate in its Wiener representation
`r_T = vasicekSDEMean + σ ∫₀ᵀ e^{−κ(T−s)} dB_s` (the textbook solution of the Vasicek SDE;
that it solves the SDE is cited, not proved) has the
Gaussian law `N(vasicekSDEMean, vasicekSDEVariance)` — the closed form `VasicekSDE.lean`
posited is now a theorem. -/
theorem vasicekShortRate_hasLaw_gaussian (hB : IsPreBrownianReal B μ)
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    HasLaw (fun ω ↦ vasicekSDEMean r₀ θ κ (T : ℝ)
        + σ * (wienerIntegralLp B hB T (vasicekKernelLp κ hκ.le T) ω))
      (gaussianReal (vasicekSDEMean r₀ θ κ (T : ℝ)) (vasicekSDEVariance σ κ (T : ℝ)).toNNReal)
          μ := by
  -- The Wiener integral of the kernel is Gaussian, centred, variance = ∫ kernel².
  have hW := wienerIntegralLp_hasLaw_gaussian_of_integral_sq hB T (vasicekKernelLp κ hκ.le T)
    ((vasicekKernel_memLp κ hκ.le T).integral_sq_toLp.trans
      (vasicekKernel_integral_sq κ hκ.ne' T))
  -- Scale by σ then shift by the mean; the affine map sends N(0, ∫kernel²) to N(mean, σ²·∫kernel²).
  have hkernel_nonneg : (0 : ℝ) ≤ (1 - Real.exp (-(2 * κ * (T : ℝ)))) / (2 * κ) := by
    simpa [vasicekSDEVariance] using vasicekSDEVariance_nonneg 1 hκ (NNReal.coe_nonneg T)
  have hvar_nonneg : (0 : ℝ) ≤ vasicekSDEVariance σ κ (T : ℝ) :=
    vasicekSDEVariance_nonneg σ hκ (NNReal.coe_nonneg T)
  have hShift := gaussianReal_const_add (gaussianReal_const_mul hW σ)
    (vasicekSDEMean r₀ θ κ (T : ℝ))
  convert hShift using 2
  · ring
  · refine NNReal.coe_injective ?_
    rw [Real.coe_toNNReal _ hvar_nonneg, NNReal.coe_mul, NNReal.coe_mk,
      Real.coe_toNNReal _ hkernel_nonneg]
    unfold vasicekSDEVariance
    ring

end MathFin
