/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralExpMoment

/-!
# The Vasicek zero-coupon bond price — the affine term structure

`Models/Rates/VasicekSDEGaussian.lean` derives the terminal short-rate law
`r_T ~ N(mean, var)` from the Wiener representation of the Ornstein–Uhlenbeck
solution. This file takes the next step in the fixed-income layer: the
**zero-coupon bond price**

  `P(0, T) = 𝔼[exp(−∫₀ᵀ r_s ds)]`,

under the measure `μ` carrying `B`, read as the risk-neutral present value of one unit paid at
`T` (`vasicekBondPrice_girsanov` builds the change from a real-world `μ`). Under the Vasicek model
the *integrated* short rate is again Gaussian, so the bond price is a Gaussian
Laplace transform and collapses to the classical **affine term structure**

  `P(0, T) = exp(−B(T)·r₀ − θ·(T − B(T)) + σ²·V(T)/2)`,   `B(T) = (1 − e^{−κT})/κ`.

## The integrated short rate, in its Wiener representation

Integrating the OU solution `r_s = r₀e^{−κs} + θ(1 − e^{−κs}) + σ∫₀ˢ e^{−κ(s−u)}dB_u`
over `s ∈ [0, T]` and swapping the (deterministic-after-integration) time order
`∫₀ᵀ∫₀ˢ e^{−κ(s−u)} ds` sends the diffusion kernel `e^{−κ(s−u)}` to the
**integrated kernel**

  `g(u) = ∫_u^T e^{−κ(s−u)} ds = (1 − e^{−κ(T−u)})/κ`,

so `∫₀ᵀ r_s ds = M(T) + σ·∫₀ᵀ g(u) dB_u`, with deterministic mean
`M(T) = r₀·B(T) + θ·(T − B(T))`. This is the exact analogue, one integration up,
of the OU-solution model that `VasicekSDEGaussian` already takes as `full`: the
integrated rate is carried in its Wiener representation (the time-order swap is
the modelling bridge, cited, not the conclusion), and everything downstream is
derived. `∫₀ᵀ g(u) dB_u` is the Wiener integral of the *deterministic* integrand
`g`, hence centred Gaussian with variance its `L²`-norm

  `V(T) = ∫₀ᵀ g(u)² du = T/κ² − 2(1 − e^{−κT})/κ³ + (1 − e^{−2κT})/(2κ³)`.

## Main definitions

* `vasicekBondB`: the affine coefficient `B(T) = (1 − e^{−κT})/κ`.
* `vasicekIntegratedKernel`, `vasicekIntegratedKernelLp`: the integrated kernel
  `g(u) = (1 − e^{−κ(T−u)})/κ`, and the same kernel as an element of `L²((0, T])`.
* `vasicekIntegratedMean`: the deterministic mean of the integrated short rate,
  `M(T) = r₀·B(T) + θ·(T − B(T))`.
* `vasicekBondV`: the variance `V(T) = ∫₀ᵀ g²` of the diffusion part of the integrated short rate.
* `vasicekIntegratedKernelSqAntideriv`: the antiderivative of `g(u)²`.
* `vasicekIntegratedRate`: the integrated short rate in its Wiener representation,
  `∫₀ᵀ r_s ds = M(T) + σ·∫₀ᵀ g(u) dB_u`.
* `vasicekBondA`: the affine coefficient `A(T) = exp(−θ(T − B(T)) + σ²V(T)/2)`.

## Main results

* `vasicekIntegratedKernelSqAntideriv`, `hasDerivAt_vasicekIntegratedKernelSqAntideriv`,
  `integral_vasicekIntegratedKernel_sq_eq_sub` — the antiderivative of `g²` and its FTC form
  over any interval (also used by `Models/Rates/GSRPiecewiseVol`).
* `vasicekIntegratedKernel_integral_sq` — the variance integral `∫₀ᵀ g² = V(T)`, and
  `vasicekIntegratedKernelLp_integral_sq`, the same for the `L²` element.
* `integral_vasicekIntegratedKernel`, `integral_vasicekIntegratedKernelLp` — the kernel's mass
  `∫₀ᵀ g = (T − B(T))/κ`, the covariance of `∫₀ᵀ g dB` with `B_T`.
* `vasicekIntegratedRate_hasLaw_gaussian` — `∫₀ᵀ r_s ds ~ N(M(T), σ²V(T))`.
* `vasicekBondPrice_eq` — the bond price `𝔼[exp(−∫₀ᵀ r_s ds)] = exp(−M(T) + σ²V(T)/2)`, the
  instance `m = M(T)`, `c = σ`, `f = g` of the Wiener bond-price lemma
  `integral_exp_neg_add_mul_wienerIntegralLp`
  (`Probability/Brownian/Wiener/WienerIntegralExpMoment`).
* `vasicekBondPrice_affine` — the affine form `P(0,T) = A(T)·exp(−B(T)·r₀)`.

## References

* [O. Vasicek, *An equilibrium characterization of the term structure*][Vasicek1977]

## Tags

Vasicek model, affine term structure, zero-coupon bond price, integrated short rate,
Wiener integral, Gaussian Laplace transform, MSC 91G30, MSC 60H05, JEL E43
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The affine coefficient `B(T)` and the integrated kernel `g` -/

/-- The Vasicek affine coefficient `B(T) = (1 − e^{−κT})/κ` — the sensitivity of
the log bond price to the short rate, and the integral `∫₀ᵀ e^{−κs} ds`. -/
noncomputable def vasicekBondB (κ T : ℝ) : ℝ := (1 - Real.exp (-(κ * T))) / κ

/-- `B(τ) = (1 − e^{−κτ})/κ` is positive for `κ, τ > 0`. -/
theorem vasicekBondB_pos {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) : 0 < vasicekBondB κ τ :=
  div_pos (sub_pos.2 (Real.exp_lt_one_iff.2 (neg_neg_of_pos (mul_pos hκ hτ)))) hκ

/-- The **integrated Vasicek kernel** `g(u) = (1 − e^{−κ(T−u)})/κ = ∫_u^T e^{−κ(s−u)} ds`
— the deterministic integrand whose Wiener integral is the diffusion part of the
integrated short rate. -/
noncomputable def vasicekIntegratedKernel (κ T : ℝ) : ℝ → ℝ :=
  fun u ↦ (1 - Real.exp (-(κ * (T - u)))) / κ

/-- The deterministic mean of the integrated short rate,
`M(T) = ∫₀ᵀ (r₀e^{−κs} + θ(1 − e^{−κs})) ds = r₀·B(T) + θ·(T − B(T))`. -/
noncomputable def vasicekIntegratedMean (r₀ θ κ T : ℝ) : ℝ :=
  r₀ * vasicekBondB κ T + θ * (T - vasicekBondB κ T)

/-- The integrated mean `M(T)` is nonnegative (`κ > 0`, `v₀, θ, τ ≥ 0`):
`0 ≤ B(τ) ≤ τ`. -/
theorem vasicekIntegratedMean_nonneg {κ v₀ θ τ : ℝ} (hκ : 0 < κ) (hv : 0 ≤ v₀) (hθ : 0 ≤ θ)
    (hτ : 0 ≤ τ) : 0 ≤ vasicekIntegratedMean v₀ θ κ τ := by
  have hB0 : 0 ≤ vasicekBondB κ τ := by
    rw [vasicekBondB]
    refine div_nonneg ?_ hκ.le
    have : Real.exp (-(κ * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  have hBτ : vasicekBondB κ τ ≤ τ := by
    rw [vasicekBondB, div_le_iff₀ hκ]
    have := Real.add_one_le_exp (-(κ * τ))
    nlinarith
  rw [vasicekIntegratedMean]
  have := mul_nonneg hv hB0
  have := mul_nonneg hθ (sub_nonneg.mpr hBτ)
  linarith

/-- The variance of the integrated short rate's diffusion part (the `L²`-norm of
the integrated kernel `g`): `V(T) = ∫₀ᵀ g² = T/κ² − 2(1−e^{−κT})/κ³ + (1−e^{−2κT})/(2κ³)`. -/
noncomputable def vasicekBondV (κ T : ℝ) : ℝ :=
  T / κ ^ 2 - 2 * (1 - Real.exp (-(κ * T))) / κ ^ 3
    + (1 - Real.exp (-(2 * κ * T))) / (2 * κ ^ 3)

/-! ### The integrated kernel is an `L²` integrand -/

/-- The integrated kernel is in `L²((0, T])`: on the support it lies in
`[0, 1/κ]` (for `κ > 0`), hence is bounded. -/
lemma vasicekIntegratedKernel_memLp {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    MemLp (vasicekIntegratedKernel κ T) 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
  refine (memLp_top_of_bound (by unfold vasicekIntegratedKernel; fun_prop) (1 / κ) ?_).mono_exponent
    le_top
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ ?_)
  intro s hs
  rw [vasicekIntegratedKernel, Real.norm_eq_abs]
  have hexp_pos : 0 < Real.exp (-(κ * ((T : ℝ) - s))) := Real.exp_pos _
  have hTs : 0 ≤ (T : ℝ) - s := by linarith [hs.2]
  have hexp_le : Real.exp (-(κ * ((T : ℝ) - s))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hκ.le hTs])
  rw [abs_of_nonneg (div_nonneg (by linarith) hκ.le)]
  exact (div_le_div_iff_of_pos_right hκ).mpr (by linarith)

/-- The integrated kernel as an element of `L²((0, T])`. -/
noncomputable def vasicekIntegratedKernelLp {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  (vasicekIntegratedKernel_memLp hκ T).toLp _

/-! ### The variance integral `∫₀ᵀ g² = V(T)` -/

/-- The antiderivative `F(u) = u/κ² − 2e^{−κ(T−u)}/κ³ + e^{−2κ(T−u)}/(2κ³)` of the squared
integrated kernel `g(u)²`. -/
noncomputable def vasicekIntegratedKernelSqAntideriv (κ T u : ℝ) : ℝ :=
  u / κ ^ 2 - 2 * Real.exp (-(κ * (T - u))) / κ ^ 3 + Real.exp (-(2 * κ * (T - u))) / (2 * κ ^ 3)

/-- For `κ ≠ 0`, `F` differentiates to `g²`: its derivative expands the square
`g² = (1 − 2e^{−κ(T−u)} + e^{−2κ(T−u)})/κ²`. -/
lemma hasDerivAt_vasicekIntegratedKernelSqAntideriv (κ T u : ℝ) (hκ : κ ≠ 0) :
    HasDerivAt (vasicekIntegratedKernelSqAntideriv κ T)
      ((vasicekIntegratedKernel κ T u) ^ 2) u := by
  have he : Real.exp (-(2 * κ * (T - u)))
      = Real.exp (-(κ * (T - u))) * Real.exp (-(κ * (T - u))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hlin : HasDerivAt (fun u : ℝ ↦ u / κ ^ 2) (1 / κ ^ 2) u :=
    (hasDerivAt_id u).div_const (κ ^ 2)
  have harg1 : HasDerivAt (fun u ↦ -(κ * (T - u))) κ u := by
    have h : HasDerivAt (fun u ↦ -(κ * (T - u))) (-(κ * (-1))) u := by
      apply HasDerivAt.neg; apply HasDerivAt.const_mul
      simpa using (hasDerivAt_id u).const_sub T
    simpa using h
  have harg2 : HasDerivAt (fun u ↦ -(2 * κ * (T - u))) (2 * κ) u := by
    have h : HasDerivAt (fun u ↦ -(2 * κ * (T - u))) (-(2 * κ * (-1))) u := by
      apply HasDerivAt.neg; apply HasDerivAt.const_mul
      simpa using (hasDerivAt_id u).const_sub T
    simpa using h
  have hexp1 := harg1.exp
  have hexp2 := harg2.exp
  have h2 := (hexp1.const_mul (2 : ℝ)).div_const (κ ^ 3)
  have h3 := hexp2.div_const (2 * κ ^ 3)
  have hcomb := (hlin.sub h2).add h3
  refine hcomb.congr_deriv ?_
  unfold vasicekIntegratedKernel
  rw [he]
  field_simp
  ring

/-- The FTC form over any interval, for `κ ≠ 0`: `∫_A^B g(u)² du = F(B) − F(A)`. -/
lemma integral_vasicekIntegratedKernel_sq_eq_sub (κ T A B : ℝ) (hκ : κ ≠ 0) :
    ∫ u in A..B, (vasicekIntegratedKernel κ T u) ^ 2
      = vasicekIntegratedKernelSqAntideriv κ T B - vasicekIntegratedKernelSqAntideriv κ T A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ hasDerivAt_vasicekIntegratedKernelSqAntideriv κ T u hκ)
  apply Continuous.intervalIntegrable
  unfold vasicekIntegratedKernel; fun_prop

/-- **The variance-fixing integral**: `∫₀ᵀ g(u)² du = V(T)`, by the FTC with
antiderivative `vasicekIntegratedKernelSqAntideriv`. -/
lemma vasicekIntegratedKernel_integral_sq {κ : ℝ} (hκ : κ ≠ 0) (T : ℝ≥0) :
    ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekIntegratedKernel κ T u) ^ 2 ∂volume
      = vasicekBondV κ (T : ℝ) := by
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (T : ℝ)),
    integral_vasicekIntegratedKernel_sq_eq_sub κ (T : ℝ) 0 (T : ℝ) hκ]
  simp only [vasicekIntegratedKernelSqAntideriv, sub_self, mul_zero, neg_zero, Real.exp_zero,
    mul_one, sub_zero, zero_div]
  rw [vasicekBondV]
  field_simp
  ring

/-! ### The kernel's mass `∫₀ᵀ g = (T − B(T))/κ` -/

/-- **The mass of the integrated kernel**: `∫₀ᵀ g(u) du = (T − B(T))/κ`, by the FTC with
antiderivative `u/κ − e^{−κ(T−u)}/κ²` (`κ ≠ 0`). It is `⟪𝟙_{(0,T]}, g⟫`, the covariance of the
Wiener integral `∫₀ᵀ g dB` with `B_T`, and `−λσ` times it is the mean shift a constant market
price of risk `λ` gives the integrated rate under the Girsanov measure
(`vasicekBondPrice_girsanov`). -/
lemma integral_vasicekIntegratedKernel (κ T : ℝ) (hκ : κ ≠ 0) :
    ∫ u in (0 : ℝ)..T, vasicekIntegratedKernel κ T u = (T - vasicekBondB κ T) / κ := by
  have hderiv (u : ℝ) : HasDerivAt (fun u : ℝ ↦ u / κ - Real.exp (-(κ * (T - u))) / κ ^ 2)
      (vasicekIntegratedKernel κ T u) u := by
    have harg : HasDerivAt (fun u ↦ -(κ * (T - u))) κ u := by
      have h : HasDerivAt (fun u ↦ -(κ * (T - u))) (-(κ * (-1))) u := by
        apply HasDerivAt.neg; apply HasDerivAt.const_mul
        simpa using (hasDerivAt_id u).const_sub T
      simpa using h
    have hlin : HasDerivAt (fun u : ℝ ↦ u / κ) (1 / κ) u := (hasDerivAt_id u).div_const κ
    refine (hlin.sub (harg.exp.div_const (κ ^ 2))).congr_deriv ?_
    simp only [vasicekIntegratedKernel]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hderiv u)
    (by apply Continuous.intervalIntegrable; unfold vasicekIntegratedKernel; fun_prop)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, sub_zero, zero_div, vasicekBondB]
  field_simp
  ring

/-- `∫₀ᵀ g = (T − B(T))/κ` for the `L²` element of the integrated kernel. -/
lemma integral_vasicekIntegratedKernelLp {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), vasicekIntegratedKernelLp hκ T u
      = ((T : ℝ) - vasicekBondB κ T) / κ := by
  rw [← integral_vasicekIntegratedKernel κ T hκ.ne', intervalIntegral.integral_of_le T.coe_nonneg]
  refine integral_congr_ae ?_
  filter_upwards [(vasicekIntegratedKernel_memLp hκ T).coeFn_toLp] with u hu
  rw [vasicekIntegratedKernelLp, hu]

/-! ### The integrated short rate and the bond price -/

/-- The **integrated Vasicek short rate** in its Wiener representation:
`∫₀ᵀ r_s ds = M(T) + σ·∫₀ᵀ g(u) dB_u`. -/
noncomputable def vasicekIntegratedRate (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  vasicekIntegratedMean r₀ θ κ (T : ℝ)
    + σ * (wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω)

/-- `∫₀ᵀ g² = V(T)` for the `L²`-representative kernel (a.e. equal to the honest kernel). -/
lemma vasicekIntegratedKernelLp_integral_sq {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekIntegratedKernelLp hκ T u) ^ 2 ∂volume)
      = vasicekBondV κ (T : ℝ) := by
  exact (vasicekIntegratedKernel_memLp hκ T).integral_sq_toLp.trans
    (vasicekIntegratedKernel_integral_sq hκ.ne' T)

/-- `V(T) ≥ 0` (it is an integral of a square). -/
lemma vasicekBondV_nonneg {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    (0 : ℝ) ≤ vasicekBondV κ (T : ℝ) := by
  rw [← vasicekIntegratedKernelLp_integral_sq hκ T]
  exact integral_nonneg fun u ↦ sq_nonneg _

/-- **Integrated Vasicek short rate is Gaussian.** The integrated rate
`∫₀ᵀ r_s ds = M(T) + σ∫₀ᵀ g dB` has law `N(M(T), σ²V(T))` — the affine map
`x ↦ M(T) + σx` applied to the centred Wiener integral of the integrated
kernel `g`, whose variance is `V(T)`. -/
theorem vasicekIntegratedRate_hasLaw_gaussian (hB : IsPreBrownianReal B μ)
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    HasLaw (vasicekIntegratedRate hB r₀ θ σ hκ T)
      (gaussianReal (vasicekIntegratedMean r₀ θ κ (T : ℝ))
        (σ ^ 2 * vasicekBondV κ (T : ℝ)).toNNReal) μ := by
  have hW := wienerIntegralLp_hasLaw_gaussian_of_integral_sq hB T (vasicekIntegratedKernelLp hκ T)
    (vasicekIntegratedKernelLp_integral_sq hκ T)
  have hV_nonneg : (0 : ℝ) ≤ vasicekBondV κ (T : ℝ) := vasicekBondV_nonneg hκ T
  have hShift := gaussianReal_const_add (gaussianReal_const_mul hW σ)
    (vasicekIntegratedMean r₀ θ κ (T : ℝ))
  convert hShift using 2
  · rfl
  · ring
  · refine NNReal.coe_injective ?_
    rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) hV_nonneg), NNReal.coe_mul, NNReal.coe_mk,
      Real.coe_toNNReal _ hV_nonneg]

/-- **The Vasicek zero-coupon bond price.** The expectation under `μ` (read as the pricing
measure; no change of measure is built here) of one unit at `T`,

  `P(0, T) = 𝔼[exp(−∫₀ᵀ r_s ds)] = exp(−M(T) + σ²V(T)/2)`,

is the Gaussian Laplace transform of the integrated short rate: the Wiener bond-price lemma
`integral_exp_neg_add_mul_wienerIntegralLp` at `m = M(T)`, `c = σ` and the integrated kernel `g`,
whose squared `L²`-norm is `V(T)` (`vasicekIntegratedKernelLp_integral_sq`). -/
theorem vasicekBondPrice_eq (hB : IsPreBrownianReal B μ)
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(vasicekIntegratedRate hB r₀ θ σ hκ T ω)) ∂μ
      = Real.exp (-(vasicekIntegratedMean r₀ θ κ (T : ℝ)) + σ ^ 2 * vasicekBondV κ (T : ℝ) / 2) :=
  (integral_exp_neg_add_mul_wienerIntegralLp hB T (vasicekIntegratedMean r₀ θ κ (T : ℝ)) σ
    (vasicekIntegratedKernelLp hκ T)).trans <| by rw [vasicekIntegratedKernelLp_integral_sq hκ T]

/-- The Vasicek affine coefficient `A(T) = exp(−θ(T − B(T)) + σ²V(T)/2)`, so that
the bond price factors as `P(0,T) = A(T)·exp(−B(T)·r₀)`. -/
noncomputable def vasicekBondA (θ σ κ T : ℝ) : ℝ :=
  Real.exp (-(θ * (T - vasicekBondB κ T)) + σ ^ 2 * vasicekBondV κ T / 2)

/-- **The affine term structure**: the Vasicek bond price separates the initial
short rate into `P(0,T) = A(T)·exp(−B(T)·r₀)` — the defining shape of an affine
term-structure model, the exponential-affine dependence on `r₀`. -/
theorem vasicekBondPrice_affine (hB : IsPreBrownianReal B μ)
    (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(vasicekIntegratedRate hB r₀ θ σ hκ T ω)) ∂μ
      = vasicekBondA θ σ κ (T : ℝ) * Real.exp (-(vasicekBondB κ (T : ℝ) * r₀)) := by
  rw [vasicekBondPrice_eq hB r₀ θ σ hκ T, vasicekBondA, vasicekIntegratedMean, ← Real.exp_add]
  congr 1
  ring

end MathFin
