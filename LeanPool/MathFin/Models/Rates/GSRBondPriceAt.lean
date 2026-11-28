/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.GSRPiecewiseVol
public import LeanPool.MathFin.Models.Rates.VasicekBondPriceAt
public import LeanPool.MathFin.Pricing.WienerIntegralForwardMeasure

/-!
# The GSR bond price at a time `t > 0`

`Models/Rates/GSRPiecewiseVol.lean` prices the zero-coupon bond at time `0` when the volatility is
`σ₁` up to the breakpoint `T*` and `σ₂` after it. This file prices it at a later time `t`, given
the information `𝓕_t = σ(B_s : s ≤ t)` of the driving Brownian motion:

  `𝔼[exp(−∫₀ᵀ r) | 𝓕_t] = exp(−∫₀ᵗ r)·A(t, T)·exp(−B(T − t)·r_t)`   almost surely,

with the Vasicek coefficient `B`, the short rate `r_t = m_t + ∫₀ᵗ σ(u) e^{−κ(t−u)} dB_u`
(`gsrShortRate`) and `A(t, T) = exp(−θ(τ − B(τ)) + Var_{(t,T]}/2)`, `τ = T − t`, where the
variance is that of the remainder `∫_t^T σ(u) g_T(u) dB_u` (`gsrBondVIoc`). Unlike the Vasicek and
Hull–White coefficients, `A` depends on `t` and `T` separately and not only on `T − t`, because
the volatility is not time-homogeneous.

It is the instance of `condExp_exp_neg_wienerIntegralLp` (`Models/Rates/VasicekBondPriceAt.lean`) at
the GSR kernel: the Vasicek mean identity is unchanged, and the kernel seen from `t` splits as
`σ(u) g_T(u) = σ(u) g_t(u) + B(T − t)·σ(u) e^{−κ(t−u)}` on `(0, t]`.

## Main definitions

* `gsrShortKernel`, `gsrShortKernelLp`: the GSR short-rate kernel `u ↦ σ(u)·e^{−κ(t−u)}`, and
  the same kernel as an element of `L²((0, t])`.
* `gsrShortRate`: the GSR short rate `r_t = m_t + ∫₀ᵗ σ(u) e^{−κ(t−u)} dB_u` in its Wiener
  representation.
* `gsrBondA`: the GSR affine coefficient `A(t, T) = exp(−θ(τ − B(τ)) + Var_{(t,T]}/2)` with
  `τ = T − t`.
* `gsrShortRateV`: the GSR short-rate variance `∫₀ᵗ σ(u)² e^{−2κ(t−u)} du` in closed form.

## Main results

* `kernelRestrict_gsrKernelLp` — the GSR kernel seen from `t`.
* `integral_sq_gsrKernelLp_Ioc` — the variance of the remainder.
* `gsrBondPrice_condExp` — the conditional discount factor, affine in `r_t`.
* `gsrShortRateV`, `gsrShortKernel_integral_sq_eq`, `gsrShortRateV_pos` — the variance
  `∫₀ᵗ σ(u)² e^{−2κ(t−u)} du` of the short rate in closed form, and its positivity.
* `gsrShortRate_hasLaw_gaussian`, `gsrShortRate_hasLaw_forwardMeasure` — the law of `r_t`, under
  the pricing measure and under the `t`-forward measure (the same variance, the mean shifted by
  minus the covariance with `∫₀ᵗ r`): the input of the bond put
  (`Models/Rates/Jamshidian.lean`).

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  section 3.3.1
* [J. Hull and A. White, *Pricing interest-rate-derivative securities*][HullWhite1990]
* [The QuantLib contributors, *QuantLib*][QuantLib], Gsr model

## Tags

Gaussian short rate, GSR model, conditional bond price, piecewise volatility, affine bond price,
forward measure, MSC 91G30, MSC 60G15, JEL E43
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
open WienerIntegralL2
open scoped InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### The short-rate kernel -/

/-- The **GSR short-rate kernel** `u ↦ σ(u)·e^{−κ(t−u)}`: the Vasicek kernel weighted by the
piecewise volatility, the integrand of the diffusion part of the short rate `r_t`. -/
noncomputable def gsrShortKernel (σ1 σ2 Tstar κ t : ℝ) : ℝ → ℝ :=
  fun u ↦ gsrSigma σ1 σ2 Tstar u * vasicekKernel κ t u

/-- The GSR short-rate kernel is in `L²((0, t])`: `|σ(u)| ≤ max |σ₁| |σ₂|` and
`0 < e^{−κ(t−u)} ≤ 1` on the window. -/
lemma gsrShortKernel_memLp {κ : ℝ} (hκ : 0 ≤ κ) (σ1 σ2 Tstar : ℝ) (t : ℝ≥0) :
    MemLp (gsrShortKernel σ1 σ2 Tstar κ t) 2 (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
  refine (memLp_top_of_bound
    (by unfold gsrShortKernel vasicekKernel
        exact ((gsrSigma_measurable σ1 σ2 Tstar).mul (by fun_prop)).aestronglyMeasurable)
    (max |σ1| |σ2|) ?_).mono_exponent le_top
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun u hu ↦ ?_)
  rw [gsrShortKernel, Real.norm_eq_abs, abs_mul, vasicekKernel,
    abs_of_pos (Real.exp_pos _)]
  have hσ : |gsrSigma σ1 σ2 Tstar u| ≤ max |σ1| |σ2| := by
    unfold gsrSigma; split
    · exact le_max_left _ _
    · exact le_max_right _ _
  have he : Real.exp (-(κ * ((t : ℝ) - u))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hκ (sub_nonneg.2 hu.2)])
  calc |gsrSigma σ1 σ2 Tstar u| * Real.exp (-(κ * ((t : ℝ) - u)))
      ≤ max |σ1| |σ2| * 1 :=
        mul_le_mul hσ he (Real.exp_pos _).le ((abs_nonneg _).trans hσ)
    _ = max |σ1| |σ2| := mul_one _

/-- The GSR short-rate kernel as an element of `L²((0, t])`. -/
noncomputable def gsrShortKernelLp {κ : ℝ} (hκ : 0 ≤ κ) (σ1 σ2 Tstar : ℝ) (t : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) :=
  (gsrShortKernel_memLp hκ σ1 σ2 Tstar t).toLp _

/-- **The GSR short rate** `r_t = m_t + ∫₀ᵗ σ(u) e^{−κ(t−u)} dB_u`, in its Wiener representation:
the Vasicek mean plus the Wiener integral of `gsrShortKernel`. That it is the solution of the GSR
short-rate SDE, and that `gsrIntegratedRate` is its integral, is the modelling bridge, cited, not
derived (as for `vasicekIntegratedRate`). -/
noncomputable def gsrShortRate (hB : IsPreBrownianReal B μ) (r₀ θ σ1 σ2 : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (Tstar t : ℝ≥0) (ω : Ω) : ℝ :=
  vasicekSDEMean r₀ θ κ (t : ℝ)
    + wienerIntegralLp B hB t (gsrShortKernelLp hκ.le σ1 σ2 (Tstar : ℝ) t) ω

/-! ### The kernel seen from `t` -/

lemma gsrKernelLp_coeFn {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 Tstar : ℝ) (T : ℝ≥0) :
    gsrKernelLp hκ σ1 σ2 Tstar T =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)]
      gsrKernel σ1 σ2 Tstar κ T :=
  (gsrKernel_memLp hκ σ1 σ2 Tstar T).coeFn_toLp

lemma gsrShortKernelLp_coeFn {κ : ℝ} (hκ : 0 ≤ κ) (σ1 σ2 Tstar : ℝ) (t : ℝ≥0) :
    gsrShortKernelLp hκ σ1 σ2 Tstar t =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) t)]
      gsrShortKernel σ1 σ2 Tstar κ t :=
  (gsrShortKernel_memLp hκ σ1 σ2 Tstar t).coeFn_toLp

/-- **The horizon-`T` GSR kernel seen from time `t`.** On `(0, t]`,
`σ(u) g_T(u) = σ(u) g_t(u) + B(T − t)·σ(u) e^{−κ(t−u)}`: the Vasicek splitting
(`kernelRestrict_vasicekIntegratedKernelLp`) weighted by the volatility. -/
lemma kernelRestrict_gsrKernelLp {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 Tstar : ℝ) {t T : ℝ≥0}
    (htT : t ≤ T) :
    kernelRestrict htT (gsrKernelLp hκ σ1 σ2 Tstar T)
      = gsrKernelLp hκ σ1 σ2 Tstar t
        + vasicekBondB κ ((T - t : ℝ≥0) : ℝ) • gsrShortKernelLp hκ.le σ1 σ2 Tstar t := by
  refine Lp.ext ?_
  filter_upwards [kernelRestrict_coeFn htT (gsrKernelLp hκ σ1 σ2 Tstar T),
    (gsrKernelLp_coeFn hκ σ1 σ2 Tstar T).filter_mono
      (ae_mono (volume_restrict_Ioc_mono htT)),
    Lp.coeFn_add (gsrKernelLp hκ σ1 σ2 Tstar t)
      (vasicekBondB κ ((T - t : ℝ≥0) : ℝ) • gsrShortKernelLp hκ.le σ1 σ2 Tstar t),
    Lp.coeFn_smul (vasicekBondB κ ((T - t : ℝ≥0) : ℝ)) (gsrShortKernelLp hκ.le σ1 σ2 Tstar t),
    gsrKernelLp_coeFn hκ σ1 σ2 Tstar t, gsrShortKernelLp_coeFn hκ.le σ1 σ2 Tstar t]
    with u h1 h2 h3 h4 h5 h6
  rw [h3, Pi.add_apply, h1, h4, Pi.smul_apply, h5, h6, h2]
  simp only [gsrKernel, gsrShortKernel, vasicekIntegratedKernel, vasicekKernel, vasicekBondB,
    smul_eq_mul, NNReal.coe_sub htT]
  have : Real.exp (-(κ * ((T : ℝ) - u)))
      = Real.exp (-(κ * ((t : ℝ) - u))) * Real.exp (-(κ * ((T : ℝ) - t))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]
  field_simp
  ring

/-- **The variance of the remainder.** `∫_t^T (σ g_T)(u)² du = gsrBondVIoc` (`T* ≤ T`). -/
lemma integral_sq_gsrKernelLp_Ioc {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 : ℝ) {Tstar t T : ℝ≥0}
    (htT : t ≤ T) (hTstarT : Tstar ≤ T) :
    ∫ s in Set.Ioc (t : ℝ) T, (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T s) ^ 2
      = gsrBondVIoc κ σ1 σ2 (Tstar : ℝ) t T := by
  rw [integral_congr_ae (g := fun s ↦ (gsrKernel σ1 σ2 (Tstar : ℝ) κ T s) ^ 2)
    (((gsrKernelLp_coeFn hκ σ1 σ2 (Tstar : ℝ) T).filter_mono (ae_mono
      (Measure.restrict_mono (Set.Ioc_subset_Ioc_left t.coe_nonneg) le_rfl))).mono
        fun u hu ↦ congrArg (· ^ 2) hu)]
  exact gsrKernel_integral_sq_Ioc_eq hκ σ1 σ2 (Tstar : ℝ) t T (NNReal.coe_le_coe.2 htT)
    (NNReal.coe_le_coe.2 hTstarT)

/-! ### The bond price at `t` -/

/-- The GSR affine coefficient at `t` for maturity `T`:
`A(t, T) = exp(−θ(τ − B(τ)) + Var_{(t,T]}/2)`, `τ = T − t`. -/
noncomputable def gsrBondA (θ κ σ1 σ2 Tstar t T : ℝ) : ℝ :=
  Real.exp (-(θ * ((T - t) - vasicekBondB κ (T - t))) + gsrBondVIoc κ σ1 σ2 Tstar t T / 2)

/-- **The GSR bond price at time `t`.** Given the information `𝓕_t` of the driving Brownian motion
and the breakpoint `T* ≤ T`, the discount factor `exp(−∫₀ᵀ r)` along the GSR integrated rate has
conditional mean

  `𝔼[exp(−∫₀ᵀ r) | 𝓕_t] = exp(−∫₀ᵗ r)·A(t, T)·exp(−B(T − t)·r_t)`

almost surely, with `r_t` the GSR short rate in its Wiener representation (`gsrShortRate`), `B`
Vasicek's coefficient and `A` as in `gsrBondA`. Dividing by the discount factor known at `t`, the
price at `t` of one unit paid at `T` is `A(t, T)·exp(−B(T − t)·r_t)`. The measure is read as the
pricing measure; mean reversion and the level `θ` are constant, only the volatility is piecewise. -/
theorem gsrBondPrice_condExp [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ)
    (hBm : ∀ s, Measurable (B s)) (r₀ θ σ1 σ2 : ℝ) {κ : ℝ} (hκ : 0 < κ) {Tstar t T : ℝ≥0}
    (htT : t ≤ T) (hTstarT : Tstar ≤ T) :
    μ[fun ω ↦ Real.exp (-gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar T ω)
        | Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable) t]
      =ᵐ[μ] fun ω ↦ Real.exp (-gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar t ω)
        * (gsrBondA θ κ σ1 σ2 (Tstar : ℝ) t T
          * Real.exp (-(vasicekBondB κ ((T : ℝ) - t)
            * gsrShortRate hB r₀ θ σ1 σ2 hκ Tstar t ω))) := by
  have key := condExp_exp_neg_wienerIntegralLp hB hBm htT (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T)
    (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) t) (gsrShortKernelLp hκ.le σ1 σ2 (Tstar : ℝ) t)
    (kernelRestrict_gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) htT)
    (integral_sq_gsrKernelLp_Ioc hκ σ1 σ2 htT hTstarT)
    (vasicekIntegratedMean_sub r₀ θ hκ.ne' htT)
  rw [NNReal.coe_sub htT] at key
  simp only [gsrIntegratedRate, gsrShortRate, gsrBondA]
  exact key

/-! ### The short rate under the forward measure -/

/-- **The GSR short-rate variance** `∫₀ᵗ σ(u)² e^{−2κ(t−u)} du`, in closed form
`σ₁²·(G(m) − G(0)) + σ₂²·(G(t) − G(m))`, with `G(u) = e^{−2κ(t−u)}/(2κ)` and `m = min(T*, t)` the
end of the part of `(0, t]` before the breakpoint. -/
noncomputable def gsrShortRateV (κ σ1 σ2 Tstar t : ℝ) : ℝ :=
  σ1 ^ 2 * (vasicekKernelSqAntideriv κ t (min Tstar t) - vasicekKernelSqAntideriv κ t 0)
    + σ2 ^ 2 * (vasicekKernelSqAntideriv κ t t - vasicekKernelSqAntideriv κ t (min Tstar t))

/-- **The squared `L²` norm of the GSR short-rate kernel**: splitting `(0, t]` at `min T* t`, where
`gsrSigma` is `σ₁` before and `σ₂` after, and applying `integral_vasicekKernel_sq_eq_sub` on each
piece. -/
theorem gsrShortKernel_integral_sq_eq {κ : ℝ} (hκ : κ ≠ 0) (σ1 σ2 : ℝ) {Tstar t : ℝ}
    (hTstar : 0 ≤ Tstar) (ht : 0 ≤ t) :
    ∫ u in Set.Ioc (0 : ℝ) t, (gsrShortKernel σ1 σ2 Tstar κ t u) ^ 2 ∂volume
      = gsrShortRateV κ σ1 σ2 Tstar t := by
  set m := min Tstar t with hm
  have hm0 : 0 ≤ m := le_min hTstar ht
  have hmt : m ≤ t := min_le_right _ _
  have heq1 : Set.EqOn (fun u ↦ (gsrShortKernel σ1 σ2 Tstar κ t u) ^ 2)
      (fun u ↦ σ1 ^ 2 * vasicekKernel κ t u ^ 2) (Set.Ioc 0 m) := fun u hu ↦ by
    simp only [gsrShortKernel, gsrSigma, ite_eq_left (hu.2.trans (min_le_left _ _))]
    ring
  have heq2 : Set.EqOn (fun u ↦ (gsrShortKernel σ1 σ2 Tstar κ t u) ^ 2)
      (fun u ↦ σ2 ^ 2 * vasicekKernel κ t u ^ 2) (Set.Ioc m t) := fun u hu ↦ by
    simp only [gsrShortKernel, gsrSigma, ite_eq_right fun h ↦ (not_le.2 hu.1) (le_min h hu.2)]
    ring
  have hcont (c : ℝ) {x y : ℝ} (hxy : x ≤ y) : IntegrableOn
      (fun u ↦ c * vasicekKernel κ t u ^ 2) (Set.Ioc x y) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mp
      (by apply Continuous.intervalIntegrable; unfold vasicekKernel; fun_prop)
  have hdisj : Disjoint (Set.Ioc 0 m) (Set.Ioc m t) :=
    Set.disjoint_left.mpr fun x hx1 hx2 ↦ absurd hx2.1 (not_lt.mpr hx1.2)
  rw [← Set.Ioc_union_Ioc_eq_Ioc hm0 hmt, setIntegral_union hdisj measurableSet_Ioc
      ((hcont (σ1 ^ 2) hm0).congr_fun heq1.symm measurableSet_Ioc)
      ((hcont (σ2 ^ 2) hmt).congr_fun heq2.symm measurableSet_Ioc),
    setIntegral_congr_fun measurableSet_Ioc heq1, setIntegral_congr_fun measurableSet_Ioc heq2,
    integral_const_mul, integral_const_mul, ← intervalIntegral.integral_of_le hm0,
    ← intervalIntegral.integral_of_le hmt, integral_vasicekKernel_sq_eq_sub κ t 0 m hκ,
    integral_vasicekKernel_sq_eq_sub κ t m t hκ, gsrShortRateV]

/-- **The GSR short-rate variance is positive** for `t > 0` and nonzero volatilities: the two
pieces of `(0, t]` are weighted by `σ₁², σ₂² > 0` and one of them is nonempty. -/
lemma gsrShortRateV_pos {κ : ℝ} (hκ : 0 < κ) {σ1 σ2 : ℝ} (hσ1 : σ1 ≠ 0) (hσ2 : σ2 ≠ 0)
    {Tstar t : ℝ} (hTstar : 0 ≤ Tstar) (ht : 0 < t) : 0 < gsrShortRateV κ σ1 σ2 Tstar t := by
  have hG {a b : ℝ} (hab : a < b) :
      vasicekKernelSqAntideriv κ t a < vasicekKernelSqAntideriv κ t b := by
    unfold vasicekKernelSqAntideriv
    exact div_lt_div_of_pos_right (Real.exp_lt_exp.2 (by nlinarith)) (by positivity)
  have hm0 : 0 ≤ min Tstar t := le_min hTstar ht.le
  have hmt : min Tstar t ≤ t := min_le_right _ _
  have h1 := pow_pos (abs_pos.2 hσ1) 2
  have h2 := pow_pos (abs_pos.2 hσ2) 2
  rw [sq_abs] at h1 h2
  unfold gsrShortRateV
  rcases hm0.eq_or_lt with h | h
  · rw [← h]
    linarith [mul_pos h2 (sub_pos.2 (hG ht))]
  · have hle : vasicekKernelSqAntideriv κ t (min Tstar t) ≤ vasicekKernelSqAntideriv κ t t := by
      rcases hmt.eq_or_lt with h | h
      · rw [h]
      · exact (hG h).le
    linarith [mul_pos h1 (sub_pos.2 (hG h)), mul_nonneg h2.le (sub_nonneg.2 hle)]

/-- **GSR with one volatility is Vasicek**: at `σ₁ = σ₂ = σ` the two pieces telescope and
`gsrShortRateV` is the Vasicek variance `σ²(1 − e^{−2κt})/(2κ)`. -/
lemma gsrShortRateV_self (κ σ Tstar t : ℝ) :
    gsrShortRateV κ σ σ Tstar t = vasicekSDEVariance σ κ t := by
  simp only [gsrShortRateV, vasicekKernelSqAntideriv, vasicekSDEVariance, sub_self, sub_zero,
    mul_zero, neg_zero, Real.exp_zero]
  ring

/-- **The GSR short rate is Gaussian**: `r_t ~ N(m_t, gsrShortRateV)`, `m_t` the Vasicek mean. -/
theorem gsrShortRate_hasLaw_gaussian [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ)
    (r₀ θ σ1 σ2 : ℝ) {κ : ℝ} (hκ : 0 < κ) (Tstar t : ℝ≥0) :
    HasLaw (gsrShortRate hB r₀ θ σ1 σ2 hκ Tstar t)
      (gaussianReal (vasicekSDEMean r₀ θ κ (t : ℝ))
        (gsrShortRateV κ σ1 σ2 (Tstar : ℝ) (t : ℝ)).toNNReal) μ := by
  have h := gaussianReal_const_add (wienerIntegralLp_hasLaw_gaussian_of_integral_sq hB t
    (gsrShortKernelLp hκ.le σ1 σ2 (Tstar : ℝ) t)
    ((gsrShortKernel_memLp hκ.le σ1 σ2 (Tstar : ℝ) t).integral_sq_toLp.trans
      (gsrShortKernel_integral_sq_eq hκ.ne' σ1 σ2 Tstar.coe_nonneg t.coe_nonneg)))
    (vasicekSDEMean r₀ θ κ (t : ℝ))
  rwa [zero_add] at h

/-- **The GSR short rate under the `t`-forward measure.** With the forward measure of the bank
account `exp(∫₀ᵗ r)` (`gsrIntegratedRate`), `r_t` stays Gaussian with the same variance and its
mean shifted by minus the covariance with `∫₀ᵗ r` (`hasLaw_forwardMeasure_wienerIntegralLp`):

  `r_t ~ N(m_t − ⟪σ(·)e^{−κ(t−·)}, σ(·)g_t⟫, gsrShortRateV)`   under `Q^t`. -/
theorem gsrShortRate_hasLaw_forwardMeasure [IsProbabilityMeasure μ] (hB : IsPreBrownianReal B μ)
    (r₀ θ σ1 σ2 : ℝ) {κ : ℝ} (hκ : 0 < κ) (Tstar t : ℝ≥0) :
    HasLaw (gsrShortRate hB r₀ θ σ1 σ2 hκ Tstar t)
      (gaussianReal (vasicekSDEMean r₀ θ κ (t : ℝ)
          - ⟪gsrShortKernelLp hκ.le σ1 σ2 (Tstar : ℝ) t, gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) t⟫_ℝ)
        (gsrShortRateV κ σ1 σ2 (Tstar : ℝ) (t : ℝ)).toNNReal)
      (forwardMeasure μ fun ω ↦ Real.exp (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar t ω)) := by
  have h := hasLaw_forwardMeasure_wienerIntegralLp hB t (vasicekSDEMean r₀ θ κ (t : ℝ))
    (vasicekIntegratedMean r₀ θ κ (t : ℝ)) 1 1 (vasicekSDEMean r₀ θ κ (t : ℝ))
    (gsrShortKernelLp hκ.le σ1 σ2 (Tstar : ℝ) t) (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) t)
    (by simp only [one_mul]; exact gsrShortRate_hasLaw_gaussian hB r₀ θ σ1 σ2 hκ Tstar t)
  simp only [one_mul, mul_one] at h
  exact h

end MathFin
