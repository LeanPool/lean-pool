/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.GaussianGirsanov
public import LeanPool.MathFin.Models.Rates.VasicekBondPrice
public import LeanPool.MathFin.Models.Rates.VasicekSDEGaussian
public import LeanPool.MathFin.Probability.Brownian.Girsanov.WienerIntegralGirsanov
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Vasicek short rate under a constant market price of risk

Textbook background (the SDEs are not formalized): with a constant market price of risk `λ`, the
Vasicek short rate has real-world dynamics `dr = κ(θ − r)dt + σ dB` and, under the Girsanov
measure `Q_λ = μ.withDensity(exp(−λB_T − λ²T/2))`, dynamics `dr = κ(θ − λσ/κ − r)dt + σ dB^λ`
with `B^λ_t = B_t + λt`. The risk-adjusted long-run level is `θ − λσ/κ`. In the Lean, `r_T` and
`∫₀ᵀ r_s ds` are carried in their Wiener representations (`vasicekShortRate_hasLaw_gaussian`,
`vasicekIntegratedRate`), as elsewhere in the Vasicek layer.
That they solve the SDE, and the time-order swap behind the integrated rate, are cited, not proved.
`Q_λ` is the measure the library constructs: `isProbabilityMeasure_withDensity_girsanov` shows
it is a probability measure, and with a filtration `Btheta_isQBrownianMotion` shows that `B^λ`
has, on `[0, T]`, the increments of a `Q_λ`-Brownian motion.

## Main results

* `vasicekSDEMean_physical_eq_riskNeutral`: an algebraic identity of closed forms
  (`κ ≠ 0`): `vasicekSDEMean` at level `θ` equals `vasicekSDEMean` at the risk-adjusted level
  `θ − λσ/κ` plus `λσ·B(T)`; the analogue of `bsTerminal_physical_eq_riskNeutral`.
* `vasicekShortRate_hasLaw_girsanov`: under `Q_λ`, `r_T ~ N(mean_θ − λσ·B(T), var)`. By the
  identity above this is the law of the Vasicek short rate at level `θ − λσ/κ`.
* `vasicekBondPrice_girsanov`: the `Q_λ`-price of the zero-coupon bond,
  `𝔼_{Q_λ}[exp(−∫₀ᵀ r_s ds)]`, equals `𝔼_μ[exp(−∫₀ᵀ r_s ds)]` at level `θ − λσ/κ`, in
  closed form `exp(−M_{θ−λσ/κ}(T) + σ²V(T)/2)` (`vasicekBondPrice_eq`).
* `vasicekShortRate_hasLaw_esscherTilt`: a static Esscher tilt of `r_T`'s own normalised driver
  under which `r_T` has the same law `N(mean_θ − λσ·B(T), var)`. The tilt reproduces the
  terminal marginal only: it is `T`-dependent, does not make `B + λt` a Brownian motion, and
  prices nothing else. `vasicekShortRate_map_esscherTilt_eq_map_girsanov` records that it agrees
  with `Q_λ` on the law of `r_T`.

Both Girsanov results come from the Cameron–Martin shift `wienerIntegralLp_hasLaw_girsanov`:
under `Q_λ` every Wiener integral `∫₀ᵀ f dB` is `N(−λ∫₀ᵀ f, ∫₀ᵀ f²)`. The joint law of
`(B_T, ∫₀ᵀ e^{−κ(T−s)} dB_s)` is not needed. The mean shift is `−λσ∫₀ᵀ e^{−κ(T−s)} ds = −λσ·B(T)`
for `r_T`, and `−λσ∫₀ᵀ g = −λσ(T − B(T))/κ` for the integrated rate.

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  §3.2.1
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], Thm.
  5.2.3
* [O. Vasicek, *An equilibrium characterization of the term structure*][Vasicek1977]

## Tags

market price of risk, Vasicek model, risk-neutral measure, Cameron–Martin, Esscher transform,
risk-adjusted mean, MSC 91G30, MSC 60H30, JEL E43
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal
open WienerIntegralL2

/-- **Real-world vs. risk-neutral Vasicek mean.** An algebraic identity of the closed form
`vasicekSDEMean`, for `κ ≠ 0`: replacing the long-run level `θ` by the risk-neutral level
`θ − lamσ/κ` changes the terminal mean by `−lamσ·(1 − e^{−κT})/κ`. -/
theorem vasicekSDEMean_physical_eq_riskNeutral (r₀ θ κ σ lam T : ℝ) (hκ : κ ≠ 0) :
    vasicekSDEMean r₀ θ κ T
      = vasicekSDEMean r₀ (θ - lam * σ / κ) κ T
        + lam * σ * vasicekBondB κ T := by
  unfold vasicekSDEMean vasicekBondB
  field_simp
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### The kernel `e^{−κ(T−s)}`: mass and `L²`-norm -/

/-- **The mass of the Vasicek kernel**: `∫₀ᵀ e^{−κ(T−s)} ds = B(T)` (`κ ≠ 0`), by the FTC with
antiderivative `e^{−κ(T−s)}/κ`. It is the covariance of `∫₀ᵀ e^{−κ(T−s)} dB_s` with `B_T`. -/
lemma integral_vasicekKernel (κ T : ℝ) (hκ : κ ≠ 0) :
    ∫ u in (0 : ℝ)..T, vasicekKernel κ T u = vasicekBondB κ T := by
  have hderiv (u : ℝ) : HasDerivAt (fun u : ℝ ↦ Real.exp (-(κ * (T - u))) / κ)
      (vasicekKernel κ T u) u := by
    have harg : HasDerivAt (fun u ↦ -(κ * (T - u))) κ u := by
      have h : HasDerivAt (fun u ↦ -(κ * (T - u))) (-(κ * (-1))) u := by
        apply HasDerivAt.neg; apply HasDerivAt.const_mul
        simpa using (hasDerivAt_id u).const_sub T
      simpa using h
    refine (harg.exp.div_const κ).congr_deriv ?_
    simp only [vasicekKernel]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hderiv u)
    (by apply Continuous.intervalIntegrable; unfold vasicekKernel; fun_prop)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, sub_zero, vasicekBondB]
  ring

/-- `∫₀ᵀ e^{−κ(T−s)} ds = B(T)` for the `L²` element of the kernel. -/
lemma integral_vasicekKernelLp {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), vasicekKernelLp κ hκ.le T u = vasicekBondB κ T := by
  rw [← integral_vasicekKernel κ T hκ.ne', intervalIntegral.integral_of_le T.coe_nonneg]
  refine integral_congr_ae ?_
  filter_upwards [(vasicekKernel_memLp κ hκ.le T).coeFn_toLp] with u hu
  rw [vasicekKernelLp, hu]

/-- `∫₀ᵀ (e^{−κ(T−s)})² ds = vasicekSDEVariance 1 κ T` for the `L²` element of the kernel. -/
private lemma vasicekKernelLp_integral_sq {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (vasicekKernelLp κ hκ.le T u) ^ 2
      = vasicekSDEVariance 1 κ T := by
  rw [vasicekSDEVariance, one_pow, one_mul, ← vasicekKernel_integral_sq κ hκ.ne' T]
  exact (vasicekKernel_memLp κ hκ.le T).integral_sq_toLp

/-! ### The short rate and the bond under the Girsanov measure -/

/-- **The Vasicek terminal short rate under the Girsanov measure.** Under
`Q_λ = μ.withDensity(exp(−lam·B_T − lam²T/2))`, the terminal short rate in its Wiener
representation `r_T = mean_θ + σ∫₀ᵀ e^{−κ(T−s)} dB_s` has law

  `r_T ~ N(mean_θ − lam·σ·B(T), σ²(1 − e^{−2κT})/(2κ))`,   `B(T) = vasicekBondB κ T`:

the Cameron–Martin shift `wienerIntegralLp_hasLaw_girsanov` moves the mean of the Wiener integral
by `−lam·∫₀ᵀ e^{−κ(T−s)} ds = −lam·B(T)` and keeps its variance. By
`vasicekSDEMean_physical_eq_riskNeutral` the mean is `vasicekSDEMean r₀ (θ − lam·σ/κ) κ T`, the law
of the Vasicek short rate at the risk-adjusted level. That the representation solves the SDE is
cited, not proved. -/
theorem vasicekShortRate_hasLaw_girsanov (hB : IsPreBrownianReal B μ) (r₀ θ σ lam : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (T : ℝ≥0) :
    HasLaw (fun ω ↦ vasicekSDEMean r₀ θ κ T
        + σ * wienerIntegralLp B hB T (vasicekKernelLp κ hκ.le T) ω)
      (gaussianReal (vasicekSDEMean r₀ θ κ T - lam * σ * vasicekBondB κ T)
        (vasicekSDEVariance σ κ T).toNNReal)
      (μ.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-lam * B T ω - lam ^ 2 * (T : ℝ) / 2))) := by
  have hW := wienerIntegralLp_hasLaw_girsanov hB lam T (vasicekKernelLp κ hκ.le T)
  rw [integral_vasicekKernelLp hκ T, vasicekKernelLp_integral_sq hκ T] at hW
  have hv : (0 : ℝ) ≤ vasicekSDEVariance 1 κ T := vasicekSDEVariance_nonneg 1 hκ T.coe_nonneg
  convert gaussianReal_const_add (gaussianReal_const_mul hW σ) (vasicekSDEMean r₀ θ κ T) using 2
  · ring
  · refine NNReal.coe_injective ?_
    rw [Real.coe_toNNReal _ (vasicekSDEVariance_nonneg σ hκ T.coe_nonneg), NNReal.coe_mul,
      NNReal.coe_mk, Real.coe_toNNReal _ hv]
    unfold vasicekSDEVariance
    ring

/-- **The Vasicek bond under the Girsanov measure is the Vasicek bond at the risk-adjusted
level.** With `∫₀ᵀ r_s ds` in its Wiener representation `vasicekIntegratedRate`,

  `𝔼_{Q_λ}[exp(−∫₀ᵀ r_s ds)] = 𝔼_μ[exp(−∫₀ᵀ r^{θ − lam·σ/κ}_s ds)]`,

where the right side is the `μ`-expectation of `vasicekBondPrice_eq` at long-run level
`θ − lam·σ/κ`, in closed form `exp(−M_{θ−lam·σ/κ}(T) + σ²V(T)/2)` (`vasicekBondPrice_eq`). Under
`Q_λ` the Wiener integral of the integrated kernel `g` is shifted by
`−lam·∫₀ᵀ g = −lam·(T − B(T))/κ` (`wienerIntegralLp_hasLaw_girsanov`,
`integral_vasicekIntegratedKernelLp`), so `σ∫₀ᵀ g dB` shifts by `−lam·σ·(T − B(T))/κ`, exactly
the change of `M(T)` when `θ` drops by `lam·σ/κ`. -/
theorem vasicekBondPrice_girsanov (hB : IsPreBrownianReal B μ) (r₀ θ σ lam : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (-(vasicekIntegratedRate hB r₀ θ σ hκ T ω))
        ∂(μ.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-lam * B T ω - lam ^ 2 * (T : ℝ) / 2)))
      = ∫ ω, Real.exp (-(vasicekIntegratedRate hB r₀ (θ - lam * σ / κ) σ hκ T ω)) ∂μ := by
  have hW := wienerIntegralLp_hasLaw_girsanov hB lam T (vasicekIntegratedKernelLp hκ T)
  rw [integral_vasicekIntegratedKernelLp hκ T, vasicekIntegratedKernelLp_integral_sq hκ T] at hW
  have hm := mgf_gaussianReal hW (-σ)
  simp only [mgf] at hm
  have hfac (ω : Ω) : Real.exp (-(vasicekIntegratedRate hB r₀ θ σ hκ T ω))
      = Real.exp (-vasicekIntegratedMean r₀ θ κ T)
        * Real.exp (-σ * wienerIntegralLp B hB T (vasicekIntegratedKernelLp hκ T) ω) := by
    rw [vasicekIntegratedRate, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hfac]
  rw [integral_const_mul, hm, vasicekBondPrice_eq, Real.coe_toNNReal _ (vasicekBondV_nonneg hκ T),
    ← Real.exp_add]
  congr 1
  simp only [vasicekIntegratedMean]
  ring

/-- **Vasicek terminal law with the risk-adjusted mean, under a static Esscher tilt of the
terminal driver.** For `κ > 0` and `T > 0`, let `r_T = mean_θ + σ ∫₀ᵀ e^{−κ(T−s)} dB_s` be the
terminal short rate in its Wiener representation, and
`Z = (∫₀ᵀ e^{−κ(T−s)} dB_s)/√v` its standard-normal driver (`v = (1 − e^{−2κT})/(2κ)`).
Under the Esscher tilt `μ.withDensity(exp(cZ − c²/2))` with `c = −lam·B(T)/√v`, the same `r_T`
has law `N(mean_θ − lamσ·B(T), var)`.

This tilt is a terminal-marginal device, not the pricing measure. It is a `T`-dependent tilt of
`r_T`'s own normalised driver. Under it `B + lam·t` is not a Brownian motion, the rest of the path
(e.g. `∫₀ᵀ r_s ds`) does not have its risk-adjusted law, and it prices no other payoff. The
pricing statements are `vasicekShortRate_hasLaw_girsanov` and `vasicekBondPrice_girsanov`, under
the Girsanov measure `μ.withDensity(exp(−lam·B_T − lam²T/2))`. That measure gives `r_T` the same
law as this tilt (`vasicekShortRate_map_esscherTilt_eq_map_girsanov`). -/
theorem vasicekShortRate_hasLaw_esscherTilt (hB : IsPreBrownianReal B μ)
    (r₀ θ σ lam : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) (hT : 0 < T) :
    let I : Ω → ℝ := fun ω ↦ wienerIntegralLp B hB T (vasicekKernelLp κ hκ.le T) ω
    let s : ℝ := Real.sqrt (vasicekSDEVariance 1 κ T)
    let c : ℝ := -(lam * vasicekBondB κ T) / s
    HasLaw (fun ω ↦ vasicekSDEMean r₀ θ κ T + σ * I ω)
      (gaussianReal (vasicekSDEMean r₀ θ κ T - lam * σ * vasicekBondB κ T)
        (vasicekSDEVariance σ κ T).toNNReal)
      (μ.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (c * (I ω / s) - c ^ 2 / 2))) := by
  intro I s c
  -- `I ~ N(0, v)`: the σ = 1, zero-mean instance of the derived terminal law.
  have hI : HasLaw I (gaussianReal 0 (vasicekSDEVariance 1 κ T).toNNReal) μ := by
    have h := vasicekShortRate_hasLaw_gaussian hB 0 0 1 hκ T
    simp only [vasicekSDEMean, zero_mul, add_zero, one_mul, zero_add] at h
    exact h
  have hv : 0 < vasicekSDEVariance 1 κ T := vasicekSDE_variance_pos 1 κ T hκ hT one_ne_zero
  have hs : 0 < s := Real.sqrt_pos.mpr hv
  have hss : s ^ 2 = vasicekSDEVariance 1 κ T := Real.sq_sqrt hv.le
  have hImeas : Measurable I := (Lp.stronglyMeasurable _).measurable
  -- `Z = I/s ~ N(0, 1)`.
  have hZ : HasLaw (fun ω ↦ I ω / s) (gaussianReal 0 1) μ := by
    have h := gaussianReal_const_mul hI s⁻¹
    convert h using 2
    · rw [div_eq_inv_mul]
    · simp
    · ext
      simp [← hss, hs.ne', max_eq_left (sq_nonneg s)]
  have hZQ := hasLaw_esscher_tilt c (hImeas.div_const s) hZ
  have h := gaussianReal_const_add (gaussianReal_const_mul hZQ (σ * s)) (vasicekSDEMean r₀ θ κ T)
  convert h using 2
  · field_simp
  · simp only [c, vasicekBondB]; field_simp; ring
  · ext
    have hvσ : 0 ≤ vasicekSDEVariance σ κ T := vasicekSDEVariance_nonneg σ hκ T.2
    simp only [Real.coe_toNNReal _ hvσ, NNReal.coe_mk, mul_one]
    rw [mul_pow, hss]
    unfold vasicekSDEVariance
    ring

/-- **The terminal Esscher tilt and the Girsanov measure give `r_T` the same law**:
`N(mean_θ − lam·σ·B(T), var)` under both (`vasicekShortRate_hasLaw_esscherTilt`,
`vasicekShortRate_hasLaw_girsanov`). Only this terminal marginal is shared. The Girsanov measure
also prices the bond (`vasicekBondPrice_girsanov`); the tilt does not. -/
theorem vasicekShortRate_map_esscherTilt_eq_map_girsanov (hB : IsPreBrownianReal B μ)
    (r₀ θ σ lam : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) (hT : 0 < T) :
    let I : Ω → ℝ := fun ω ↦ wienerIntegralLp B hB T (vasicekKernelLp κ hκ.le T) ω
    let s : ℝ := Real.sqrt (vasicekSDEVariance 1 κ T)
    let c : ℝ := -(lam * vasicekBondB κ T) / s
    (μ.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (c * (I ω / s) - c ^ 2 / 2))).map
        (fun ω ↦ vasicekSDEMean r₀ θ κ T + σ * I ω)
      = (μ.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-lam * B T ω - lam ^ 2 * (T : ℝ) / 2))).map
        (fun ω ↦ vasicekSDEMean r₀ θ κ T + σ * I ω) :=
  (vasicekShortRate_hasLaw_esscherTilt hB r₀ θ σ lam hκ T hT).map_eq.trans
    (vasicekShortRate_hasLaw_girsanov hB r₀ θ σ lam hκ T).map_eq.symm

end MathFin
