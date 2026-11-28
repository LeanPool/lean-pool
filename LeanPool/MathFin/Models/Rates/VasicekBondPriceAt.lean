/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.VasicekBondPrice
public import LeanPool.MathFin.Models.Rates.VasicekSDEGaussian
public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralFiltration

/-!
# The Vasicek bond price at a time `t > 0`

`Models/Rates/VasicekBondPrice.lean` prices the zero-coupon bond at time `0`,
`P(0, T) = 𝔼[exp(−∫₀ᵀ r_s ds)] = A(T)·exp(−B(T) r₀)`. This file prices it at a later time `t`,
given the information `𝓕_t = σ(B_s : s ≤ t)` of the driving Brownian motion:

  `𝔼[exp(−∫₀ᵀ r_s ds) | 𝓕_t] = exp(−∫₀ᵗ r_s ds)·A(T − t)·exp(−B(T − t)·r_t)`   almost surely,

so the price at `t` of one unit paid at `T`, the conditional mean of the discount over `[t, T]`, is
`A(T − t)·exp(−B(T − t)·r_t)`, with `A`, `B` the coefficients of the time-`0` price at the remaining
maturity `T − t`: the Vasicek model is time-homogeneous, so the price depends on `t` only through
`r_t` and `T − t`.

The integrated rate is carried in its Wiener representation (`vasicekIntegratedRate`), so
`∫₀ᵀ r` and `∫₀ᵗ r` are Wiener integrals over different horizons. Given the past
(`Probability/Brownian/Wiener/WienerIntegralFiltration.lean`, `condExp_exp_wienerIntegralLp`), the
integrated kernel `g_T(u) = (1 − e^{−κ(T−u)})/κ` of the horizon `T`, restricted to `(0, t]`, is
`g_t + B(T − t)·e^{−κ(t−u)}`: the past part of `∫₀ᵀ r` depends on the past through `∫₀ᵗ r` and the
Wiener integral `∫₀ᵗ e^{−κ(t−u)} dB_u`, which is `(r_t − mean)/σ`; and the remainder is
independent of the past, with the exponential moments of a centred Gaussian of variance
`∫_t^T g_T² = V(T − t)`. The bridge to
`bondPrice` is `Models/Rates/VasicekBond.lean`.

## Main results

* `kernelRestrict_vasicekIntegratedKernelLp` — `g_T|_{(0,t]} = g_t + B(T − t)·e^{−κ(t−·)}`.
* `integral_sq_vasicekIntegratedKernelLp_Ioc` — `∫_t^T g_T² = V(T − t)`.
* `vasicekIntegratedMean_sub` — the mean identity `M(t) − M(T) = −θ(τ − B(τ)) − B(τ) m_t`.
* `condExp_exp_neg_integratedRate` — the conditional discount factor of any Gaussian short rate
  with the integrated Vasicek kernel, from the mean identity `M(t) − M(T) = −c − B(T − t)·m`
  alone; the Hull–White bond price (`Models/Rates/HullWhiteBondPriceAt.lean`) is its other
  instance.
* `vasicekBondPrice_condExp` — the conditional discount factor, affine in `r_t`.

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  section 3.2.1
* [O. Vasicek, *An equilibrium characterization of the term structure*][Vasicek1977]

## Tags

Vasicek model, conditional bond price, time-homogeneous, affine term structure, short rate,
Markov property, MSC 91G30, MSC 60H05, JEL E43
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma vasicekIntegratedKernelLp_coeFn {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    vasicekIntegratedKernelLp hκ T =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)]
      vasicekIntegratedKernel κ T :=
  (vasicekIntegratedKernel_memLp hκ T).coeFn_toLp

lemma vasicekKernelLp_coeFn (κ : ℝ) (hκ : 0 ≤ κ) (T : ℝ≥0) :
    vasicekKernelLp κ hκ T =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)] vasicekKernel κ T :=
  (vasicekKernel_memLp κ hκ T).coeFn_toLp

/-- **The horizon-`T` kernel seen from time `t`.** On `(0, t]`, the integrated kernel
`g_T(u) = (1 − e^{−κ(T−u)})/κ` is `g_t(u) + B(T − t)·e^{−κ(t−u)}`, since
`e^{−κ(T−u)} = e^{−κ(t−u)} e^{−κ(T−t)}`. -/
lemma kernelRestrict_vasicekIntegratedKernelLp {κ : ℝ} (hκ : 0 < κ) {t T : ℝ≥0} (htT : t ≤ T) :
    kernelRestrict htT (vasicekIntegratedKernelLp hκ T)
      = vasicekIntegratedKernelLp hκ t
        + vasicekBondB κ ((T - t : ℝ≥0) : ℝ) • vasicekKernelLp κ hκ.le t := by
  refine Lp.ext ?_
  filter_upwards [kernelRestrict_coeFn htT (vasicekIntegratedKernelLp hκ T),
    (vasicekIntegratedKernelLp_coeFn hκ T).filter_mono (ae_mono (volume_restrict_Ioc_mono htT)),
    Lp.coeFn_add (vasicekIntegratedKernelLp hκ t)
      (vasicekBondB κ ((T - t : ℝ≥0) : ℝ) • vasicekKernelLp κ hκ.le t),
    Lp.coeFn_smul (vasicekBondB κ ((T - t : ℝ≥0) : ℝ)) (vasicekKernelLp κ hκ.le t),
    vasicekIntegratedKernelLp_coeFn hκ t, vasicekKernelLp_coeFn κ hκ.le t]
    with u h1 h2 h3 h4 h5 h6
  rw [h3, Pi.add_apply, h1, h4, Pi.smul_apply, h5, h6, h2]
  simp only [vasicekIntegratedKernel, vasicekKernel, vasicekBondB, smul_eq_mul, NNReal.coe_sub htT]
  have : Real.exp (-(κ * ((T : ℝ) - u)))
      = Real.exp (-(κ * ((t : ℝ) - u))) * Real.exp (-(κ * ((T : ℝ) - t))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]
  field_simp
  ring

/-- **The variance of the remainder.** `∫_t^T g_T(u)² du = V(T − t)`, the variance function at the
remaining maturity. -/
lemma integral_sq_vasicekIntegratedKernelLp_Ioc {κ : ℝ} (hκ : 0 < κ) {t T : ℝ≥0} (htT : t ≤ T) :
    ∫ s in Set.Ioc (t : ℝ) T, (vasicekIntegratedKernelLp hκ T s) ^ 2
      = vasicekBondV κ ((T - t : ℝ≥0) : ℝ) := by
  have ht : (t : ℝ) ≤ T := NNReal.coe_le_coe.2 htT
  rw [integral_congr_ae (g := fun s ↦ (vasicekIntegratedKernel κ T s) ^ 2)
    (((vasicekIntegratedKernelLp_coeFn hκ T).filter_mono (ae_mono
      (Measure.restrict_mono (Set.Ioc_subset_Ioc_left t.coe_nonneg) le_rfl))).mono
        fun u hu ↦ congrArg (· ^ 2) hu),
    ← intervalIntegral.integral_of_le ht,
    integral_vasicekIntegratedKernel_sq_eq_sub κ T t T hκ.ne']
  simp only [vasicekIntegratedKernelSqAntideriv, vasicekBondV, NNReal.coe_sub htT, sub_self,
    mul_zero, neg_zero, Real.exp_zero]
  field_simp
  ring

/-- The change in the integrated mean from `t` to `T`: the price coefficient at the remaining
maturity, less the mean sensitivity `B(T − t)` to the short-rate mean at `t`. -/
lemma vasicekIntegratedMean_sub (r₀ θ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) {t T : ℝ≥0} (htT : t ≤ T) :
    vasicekIntegratedMean r₀ θ κ t - vasicekIntegratedMean r₀ θ κ T
      = -(θ * (((T - t : ℝ≥0) : ℝ) - vasicekBondB κ ((T - t : ℝ≥0) : ℝ)))
        - vasicekBondB κ ((T - t : ℝ≥0) : ℝ) * vasicekSDEMean r₀ θ κ t := by
  have hT : Real.exp (-(κ * (T : ℝ)))
      = Real.exp (-(κ * (t : ℝ))) * Real.exp (-(κ * ((T : ℝ) - t))) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [vasicekIntegratedMean, vasicekBondB, vasicekSDEMean, NNReal.coe_sub htT, hT]
  field_simp
  ring

/-- **The conditional discount factor of a Gaussian short rate, from the kernel and mean
identities.** For any integrated rate `M_T + ∫₀ᵀ f dB` with a deterministic kernel `f ∈ L²((0, T])`
and deterministic part `M_T`, given the information `𝓕_t`,

  `𝔼[exp(−(M_T + ∫₀ᵀ f dB)) | 𝓕_t]
      = exp(−(M_t + ∫₀ᵗ f' dB))·exp(−c + v/2)·exp(−b(m + ∫₀ᵗ h dB))`

almost surely, as soon as the kernel seen from `t` splits as `f|_{(0,t]} = f' + b·h` (`hf`), the
remainder has variance `v = ∫_t^T f²` (`hv`), and the deterministic parts satisfy
`M_t − M_T = −c − b·m` (`hM`). The constant-volatility models are the instances
`f = σ·g_T` (`condExp_exp_neg_integratedRate`); the piecewise-volatility GSR model is another
(`Models/Rates/GSRBondPriceAt.lean`). -/
theorem condExp_exp_neg_wienerIntegralLp [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ)
    (hBm : ∀ s, Measurable (B s)) {t T : ℝ≥0} (htT : t ≤ T)
    (f : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) T)))
    (f' h : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) t))) {M_t M_T c m b v : ℝ}
    (hf : kernelRestrict htT f = f' + b • h) (hv : ∫ s in Set.Ioc (t : ℝ) T, f s ^ 2 = v)
    (hM : M_t - M_T = -c - b * m) :
    μ[fun ω ↦ Real.exp (-(M_T + wienerIntegralLp B hB T f ω))
        | Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable) t]
      =ᵐ[μ] fun ω ↦ Real.exp (-(M_t + wienerIntegralLp B hB t f' ω))
        * (Real.exp (-c + v / 2) * Real.exp (-(b * (m + wienerIntegralLp B hB t h ω)))) := by
  have hfun : (fun ω ↦ Real.exp (-(M_T + wienerIntegralLp B hB T f ω)))
      = fun ω ↦ Real.exp (-M_T + 0 * wienerIntegralLp B hB t 0 ω
          - 1 * wienerIntegralLp B hB T f ω) := by
    funext ω
    congr 1
    ring
  rw [hfun]
  refine (condExp_exp_wienerIntegralLp hB hBm htT 0 f _ 0 1).trans ?_
  rw [hf, map_add, map_smul, one_pow, one_mul, hv]
  filter_upwards [Lp.coeFn_add (wienerIntegralLp B hB t f') (b • wienerIntegralLp B hB t h),
    Lp.coeFn_smul b (wienerIntegralLp B hB t h)] with ω h1 h2
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  linear_combination hM

/-- **The conditional discount factor of a constant-volatility Gaussian short rate, from the mean
identity alone.** The instance of `condExp_exp_neg_wienerIntegralLp` at `f = σ·g_T`: for any
integrated rate `M_T + σ∫₀ᵀ g_T dB` (the integrated Vasicek kernel `g_T`, any deterministic part
`M_T`), given the information `𝓕_t`,

  `𝔼[exp(−(M_T + σ∫₀ᵀ g_T dB)) | 𝓕_t]
      = exp(−(M_t + σ∫₀ᵗ g_t dB))·exp(−c + σ²V(T − t)/2)·exp(−B(T − t)(m + σ∫₀ᵗ e^{−κ(t−·)} dB))`

almost surely, as soon as the deterministic parts satisfy `M_t − M_T = −c − B(T − t)·m`. The
Vasicek model (`c = θ(τ − B(τ))`, `m` the mean of `r_t`) and the Hull–White model
(`c = ∫_t^T θ B(T − ·)`, `m = α(t)`) are the two instances: they differ only in this identity. -/
theorem condExp_exp_neg_integratedRate [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ)
    (hBm : ∀ s, Measurable (B s)) (σ : ℝ) {κ : ℝ} (hκ : 0 < κ) {t T : ℝ≥0} (htT : t ≤ T)
    {M_t M_T c m : ℝ}
    (hM : M_t - M_T = -c - vasicekBondB κ ((T - t : ℝ≥0) : ℝ) * m) :
    μ[fun ω ↦ Real.exp (-(M_T + σ * wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω))
        | Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable) t]
      =ᵐ[μ] fun ω ↦
        Real.exp (-(M_t + σ * wienerIntegralLp B hB t (vasicekIntegratedKernelLp hκ t) ω))
        * (Real.exp (-c + σ ^ 2 * vasicekBondV κ ((T - t : ℝ≥0) : ℝ) / 2)
          * Real.exp (-(vasicekBondB κ ((T - t : ℝ≥0) : ℝ)
            * (m + σ * wienerIntegralLp B hB t (vasicekKernelLp κ hκ.le t) ω)))) := by
  have hsm (s : ℝ≥0) (g : Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) s))) :
      ∀ᵐ ω ∂μ, wienerIntegralLp B hB s (σ • g) ω = σ * wienerIntegralLp B hB s g ω :=
    wienerIntegralLp_smul_ae hB s σ g
  have hv : ∫ s in Set.Ioc (t : ℝ) T, (σ • vasicekIntegratedKernelLp hκ T) s ^ 2
      = σ ^ 2 * vasicekBondV κ ((T - t : ℝ≥0) : ℝ) := by
    rw [← integral_sq_vasicekIntegratedKernelLp_Ioc hκ htT, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [(Lp.coeFn_smul σ (vasicekIntegratedKernelLp hκ T)).filter_mono
      (ae_mono (Measure.restrict_mono (Set.Ioc_subset_Ioc_left t.coe_nonneg) le_rfl))] with u hu
    rw [hu, Pi.smul_apply, smul_eq_mul, mul_pow]
  have key := condExp_exp_neg_wienerIntegralLp hB hBm htT (σ • vasicekIntegratedKernelLp hκ T)
    (σ • vasicekIntegratedKernelLp hκ t) (σ • vasicekKernelLp κ hκ.le t)
    (b := vasicekBondB κ ((T - t : ℝ≥0) : ℝ)) (c := c) (m := m)
    (by rw [map_smul, kernelRestrict_vasicekIntegratedKernelLp hκ htT, smul_add, smul_comm]) hv hM
  refine (condExp_congr_ae ?_).trans (key.trans ?_)
  · filter_upwards [hsm T (vasicekIntegratedKernelLp hκ T)] with ω hω
    rw [hω]
  · filter_upwards [hsm t (vasicekIntegratedKernelLp hκ t), hsm t (vasicekKernelLp κ hκ.le t)]
      with ω h1 h2
    rw [h1, h2]

/-- **The Vasicek bond price at time `t`.** Given the information `𝓕_t` of the driving Brownian
motion, the discount factor `exp(−∫₀ᵀ r)` along the Vasicek integrated rate has conditional mean

  `𝔼[exp(−∫₀ᵀ r) | 𝓕_t] = exp(−∫₀ᵗ r)·A(T − t)·exp(−B(T − t)·r_t)`

almost surely, where `r_t = vasicekSDEMean + σ∫₀ᵗ e^{−κ(t−u)} dB_u` is the short rate in its Wiener
representation (`vasicekShortRate_hasLaw_gaussian`) and `A`, `B` are the coefficients of the
time-`0` price (`vasicekBondPrice_affine`), at the remaining maturity. Dividing by the discount
factor `exp(−∫₀ᵗ r)` known at `t`, the price at `t` of one unit paid at `T` is
`A(T − t)·exp(−B(T − t)·r_t)`. The measure is read as the pricing measure. -/
theorem vasicekBondPrice_condExp [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ)
    (hBm : ∀ s, Measurable (B s)) (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) {t T : ℝ≥0} (htT : t ≤ T) :
    μ[fun ω ↦ Real.exp (-vasicekIntegratedRate hB r₀ θ σ hκ T ω)
        | Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable) t]
      =ᵐ[μ] fun ω ↦ Real.exp (-vasicekIntegratedRate hB r₀ θ σ hκ t ω)
        * (vasicekBondA θ σ κ ((T - t : ℝ≥0) : ℝ)
          * Real.exp (-(vasicekBondB κ ((T - t : ℝ≥0) : ℝ)
            * (vasicekSDEMean r₀ θ κ t + vasicekDiffusionTerm hB κ σ hκ.le t ω)))) :=
  condExp_exp_neg_integratedRate hB hBm σ hκ htT (c := θ * (((T - t : ℝ≥0) : ℝ)
      - vasicekBondB κ ((T - t : ℝ≥0) : ℝ))) (m := vasicekSDEMean r₀ θ κ t)
    (vasicekIntegratedMean_sub r₀ θ hκ.ne' htT)

end MathFin
