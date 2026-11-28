/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.VasicekBondPrice
public import Mathlib.Order.CompletePartialOrder

/-!
# GSR (Gaussian short rate) with two-piece piecewise-constant volatility

The **GSR model** (QuantLib's `GsrProcess`/one-factor `Gsr` model) generalizes Vasicek/
Hull-White by letting the diffusion coefficient be **piecewise constant in calendar
time** rather than a single scalar — the feature actually exercised in cap/swaption
calibration, where a term structure of volatility is bootstrapped bucket by bucket.
Mean reversion is kept constant here, matching common GSR calibration practice
(reversion is held fixed while volatility is bucketed); `θ` is likewise constant
(the time-varying-drift generalization is `Models/Rates/HullWhiteCalibration.lean`'s
separate contribution and composes with this one in principle, but is not combined
here).

**Scope note**: this file proves
the **two-piece** case — volatility `σ₁` on `(0, T*]`, `σ₂` on `(T*, T]`, for a fixed
breakpoint `T* ∈ [0, T]` — not the general finitely-many-pieces GSR. The obstruction to
full generality is not conceptual (the argument below is already piece-count-agnostic
in spirit: split, apply FTC on each piece, sum variances) but mechanical: each
additional piece needs its own disjoint-union / interval-additivity bookkeeping, which
is better done once as an induction over a list of breakpoints than hand-duplicated.
Two pieces is the smallest case that is genuinely new (distinct from the
constant-`σ` Vasicek bond price `vasicekBondPrice_eq`) and already demonstrates the
mechanism in full.

## Why this is still "the same Gaussian-moment substrate"

Even with `σ` piecewise constant, the integrated short rate's diffusion part
`∫₀ᵀ σ(u)·g(u) dB_u` (`g` the Vasicek integrated kernel of `VasicekBondPrice.lean`) is
still the Wiener integral of a single **deterministic** `L²` integrand `u ↦ σ(u)·g(u)` —
piecewise-constant `σ` times a bounded kernel is still bounded, hence `L²` on the
finite-measure window. No new stochastic-integral machinery is needed: only a new
(elementary) variance integral, computed by splitting the integration domain at `T*` and
evaluating the antiderivative `vasicekIntegratedKernelSqAntideriv` of `g²` at the three
points `0, T*, T` (`integral_vasicekIntegratedKernel_sq_eq_sub`).

As in `VasicekBondPrice`, the integrated short rate is *defined* by its Wiener
representation `M(T) + ∫₀ᵀ σ(u)·g(u) dB_u` (`gsrIntegratedRate`): that it is the integral
of the solution of the GSR short-rate SDE (the SDE solution plus the time-order swap) is the
modelling bridge, cited, not derived here. Everything downstream of the representation is
derived.

## Main definitions

* `gsrSigma`: the two-piece piecewise-constant volatility, `σ₁` on `(-∞, T*]` and `σ₂` on
  `(T*, ∞)`.
* `gsrKernel`, `gsrKernelLp`: the Vasicek integrated kernel weighted by the piecewise volatility,
  and the same kernel as an element of `L²((0, T])`.
* `gsrBondV`: the closed-form variance `σ₁²·(F(T*) - F(0)) + σ₂²·(F(T) - F(T*))`.
* `gsrBondVIoc`: the variance over a window `(a, T]`.
* `gsrIntegratedRate`: the integrated short rate, defined by its Wiener representation.

## Main results

* `gsrKernel_integral_sq_eq` — the core calculus fact: the kernel's squared `L²` norm
  over `(0,T]` equals `gsrBondV` (`κ > 0`, `0 ≤ T* ≤ T`).
* `gsrIntegratedRate_hasLaw_gaussian` — the integrated short rate, in its Wiener
  representation, is Gaussian with this variance.
* `gsrBondPrice_eq` — the exponential-Gaussian moment `𝔼_μ[exp(−∫₀ᵀ r_s ds)]`, the
  zero-coupon bond price when `μ` is read as the pricing measure: the Wiener bond-price lemma
  `integral_exp_neg_add_mul_wienerIntegralLp` at the GSR kernel.
* `gsrBondV_self`, `gsrIntegratedRate_self_ae` — **GSR with one volatility is Vasicek**: at
  `σ₁ = σ₂ = σ` the variance is `σ²·vasicekBondV` and the integrated GSR rate is almost surely
  the integrated Vasicek rate `vasicekIntegratedRate`.

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  §3.3
* [The QuantLib contributors, *QuantLib*][QuantLib], Gsr model

## Tags

Gaussian short rate, GSR model, piecewise-constant volatility, Hull–White, Vasicek model,
bond price, Wiener integral, MSC 91G30, MSC 60H05, JEL E43
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-! ### Two-piece piecewise-constant volatility -/

/-- **Two-piece piecewise-constant volatility**: `σ₁` on `(-∞, T*]`, `σ₂` on `(T*, ∞)`. -/
noncomputable def gsrSigma (σ1 σ2 Tstar u : ℝ) : ℝ := if u ≤ Tstar then σ1 else σ2

/-- `gsrSigma` is measurable: it is an `ite` on the measurable set `{u | u ≤ Tstar}` with
constant branches. -/
lemma gsrSigma_measurable (σ1 σ2 Tstar : ℝ) : Measurable (gsrSigma σ1 σ2 Tstar) := by
  unfold gsrSigma
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

/-- The **GSR kernel**: the Vasicek integrated kernel `g` weighted by the piecewise
volatility — the deterministic integrand of the diffusion part `∫₀ᵀ σ(u)g(u) dB_u`. -/
noncomputable def gsrKernel (σ1 σ2 Tstar κ T : ℝ) : ℝ → ℝ :=
  fun u ↦ gsrSigma σ1 σ2 Tstar u * vasicekIntegratedKernel κ T u

/-! ### The GSR kernel is an `L²` integrand -/

/-- The GSR kernel is in `L²((0, T])`: `|σ(u)| ≤ max |σ₁| |σ₂|` and `0 ≤ g(u) ≤ 1/κ`
(for `κ > 0`), so the product is bounded by `max |σ₁| |σ₂| / κ`. -/
lemma gsrKernel_memLp {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 Tstar : ℝ) (T : ℝ≥0) :
    MemLp (gsrKernel σ1 σ2 Tstar κ (T : ℝ)) 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
  have hg_meas : Measurable (vasicekIntegratedKernel κ (T : ℝ)) := by
    unfold vasicekIntegratedKernel; fun_prop
  refine (memLp_top_of_bound
    (by unfold gsrKernel
        exact ((gsrSigma_measurable σ1 σ2 Tstar).mul hg_meas).aestronglyMeasurable)
    (max |σ1| |σ2| / κ) ?_).mono_exponent le_top
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ ?_)
  intro u hu
  rw [gsrKernel, Real.norm_eq_abs, abs_mul]
  have hexp_pos : 0 < Real.exp (-(κ * ((T : ℝ) - u))) := Real.exp_pos _
  have hTu : 0 ≤ (T : ℝ) - u := by linarith [hu.2]
  have hexp_le : Real.exp (-(κ * ((T : ℝ) - u))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hκ.le hTu])
  have hg_nonneg : 0 ≤ vasicekIntegratedKernel κ (T : ℝ) u := by
    rw [vasicekIntegratedKernel]; exact div_nonneg (by linarith) hκ.le
  have hg_le : vasicekIntegratedKernel κ (T : ℝ) u ≤ 1 / κ := by
    rw [vasicekIntegratedKernel]
    exact (div_le_div_iff_of_pos_right hκ).mpr (by linarith)
  have hσ_le : |gsrSigma σ1 σ2 Tstar u| ≤ max |σ1| |σ2| := by
    unfold gsrSigma; split
    · exact le_max_left _ _
    · exact le_max_right _ _
  calc |gsrSigma σ1 σ2 Tstar u| * |vasicekIntegratedKernel κ (T : ℝ) u|
      ≤ max |σ1| |σ2| * (1 / κ) :=
        mul_le_mul hσ_le (by rw [abs_of_nonneg hg_nonneg]; exact hg_le) (abs_nonneg _)
          (le_trans (abs_nonneg _) hσ_le)
    _ = max |σ1| |σ2| / κ := by ring

/-- The GSR kernel as an element of `L²((0, T])`. -/
noncomputable def gsrKernelLp {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 Tstar : ℝ) (T : ℝ≥0) :
    Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
  (gsrKernel_memLp hκ σ1 σ2 Tstar T).toLp _

/-! ### The variance integral, by splitting at `T*` -/

/-- **The GSR closed-form variance**: `σ₁²·(F(T*) - F(0)) + σ₂²·(F(T) - F(T*))`,
`F = vasicekIntegratedKernelSqAntideriv κ T` (the antiderivative of `g²`). -/
noncomputable def gsrBondV (κ σ1 σ2 Tstar T : ℝ) : ℝ :=
  σ1 ^ 2 * (vasicekIntegratedKernelSqAntideriv κ T Tstar
      - vasicekIntegratedKernelSqAntideriv κ T 0)
    + σ2 ^ 2 * (vasicekIntegratedKernelSqAntideriv κ T T
      - vasicekIntegratedKernelSqAntideriv κ T Tstar)

/-- **The GSR variance over a window `(a, T]`**: `σ₁²·(F(m) − F(a)) + σ₂²·(F(T) − F(m))` with
`m = max a T*` the part of the window before the breakpoint ending at `m` (empty when `a ≥ T*`);
`gsrBondV` is the window `(0, T]`. -/
noncomputable def gsrBondVIoc (κ σ1 σ2 Tstar a T : ℝ) : ℝ :=
  σ1 ^ 2 * (vasicekIntegratedKernelSqAntideriv κ T (max a Tstar)
      - vasicekIntegratedKernelSqAntideriv κ T a)
    + σ2 ^ 2 * (vasicekIntegratedKernelSqAntideriv κ T T
      - vasicekIntegratedKernelSqAntideriv κ T (max a Tstar))

lemma gsrBondVIoc_zero {Tstar : ℝ} (hTstar0 : 0 ≤ Tstar) (κ σ1 σ2 T : ℝ) :
    gsrBondVIoc κ σ1 σ2 Tstar 0 T = gsrBondV κ σ1 σ2 Tstar T := by
  rw [gsrBondVIoc, gsrBondV, max_eq_right hTstar0]

/-- **The squared `L²` norm of the GSR kernel over a window `(a, T]`**, by splitting the window at
`max a T*` (`gsrKernel` is exactly `σ₁ · g` on the part before `T*` and `σ₂ · g` after it, a case
split on `gsrSigma`'s own definition) and applying `integral_vasicekIntegratedKernel_sq_eq_sub`
on each piece. -/
theorem gsrKernel_integral_sq_Ioc_eq {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 Tstar a T : ℝ)
    (haT : a ≤ T) (hTstarT : Tstar ≤ T) :
    ∫ u in Set.Ioc a T, (gsrKernel σ1 σ2 Tstar κ T u) ^ 2 ∂volume
      = gsrBondVIoc κ σ1 σ2 Tstar a T := by
  set m := max a Tstar with hm
  have ham : a ≤ m := le_max_left _ _
  have hmT : m ≤ T := max_le haT hTstarT
  have heq1 : Set.EqOn (fun u ↦ (gsrKernel σ1 σ2 Tstar κ T u) ^ 2)
      (fun u ↦ σ1 ^ 2 * vasicekIntegratedKernel κ T u ^ 2) (Set.Ioc a m) := by
    intro u hu
    have : u ≤ Tstar := by
      rcases le_total a Tstar with h | h
      · exact (hu.2.trans_eq (max_eq_right h))
      · exact absurd (hu.2.trans_eq (max_eq_left h)) (not_le.2 hu.1)
    simp only [gsrKernel, gsrSigma, ite_eq_left this]
    ring
  have heq2 : Set.EqOn (fun u ↦ (gsrKernel σ1 σ2 Tstar κ T u) ^ 2)
      (fun u ↦ σ2 ^ 2 * vasicekIntegratedKernel κ T u ^ 2) (Set.Ioc m T) := by
    intro u hu
    simp only [gsrKernel, gsrSigma,
      ite_eq_right (not_le.mpr (lt_of_le_of_lt (le_max_right _ _) hu.1))]
    ring
  have hcont (c : ℝ) {x y : ℝ} (hxy : x ≤ y) : IntegrableOn
      (fun u ↦ c * vasicekIntegratedKernel κ T u ^ 2) (Set.Ioc x y) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mp
      (by apply Continuous.intervalIntegrable; unfold vasicekIntegratedKernel; fun_prop)
  have hmeas1 := (hcont (σ1 ^ 2) ham).congr_fun heq1.symm measurableSet_Ioc
  have hmeas2 := (hcont (σ2 ^ 2) hmT).congr_fun heq2.symm measurableSet_Ioc
  have hdisj : Disjoint (Set.Ioc a m) (Set.Ioc m T) :=
    Set.disjoint_left.mpr (fun x hx1 hx2 ↦ absurd hx2.1 (not_lt.mpr hx1.2))
  rw [← Set.Ioc_union_Ioc_eq_Ioc ham hmT, setIntegral_union hdisj measurableSet_Ioc hmeas1 hmeas2,
    setIntegral_congr_fun measurableSet_Ioc heq1, setIntegral_congr_fun measurableSet_Ioc heq2,
    integral_const_mul, integral_const_mul, ← intervalIntegral.integral_of_le ham,
    ← intervalIntegral.integral_of_le hmT,
    integral_vasicekIntegratedKernel_sq_eq_sub κ T a m hκ.ne',
    integral_vasicekIntegratedKernel_sq_eq_sub κ T m T hκ.ne', gsrBondVIoc]

/-- **The core calculus fact**: the `(0,T]`-window squared `L²` norm of the GSR kernel is
the closed-form `gsrBondV` (`gsrKernel_integral_sq_Ioc_eq` on the window `(0, T]`). -/
theorem gsrKernel_integral_sq_eq {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 Tstar T : ℝ)
    (hTstar0 : 0 ≤ Tstar) (hTstarT : Tstar ≤ T) :
    ∫ u in Set.Ioc (0 : ℝ) T, (gsrKernel σ1 σ2 Tstar κ T u) ^ 2 ∂volume
      = gsrBondV κ σ1 σ2 Tstar T :=
  (gsrKernel_integral_sq_Ioc_eq hκ σ1 σ2 Tstar 0 T (hTstar0.trans hTstarT) hTstarT).trans
    (gsrBondVIoc_zero hTstar0 κ σ1 σ2 T)

/-! ### The GSR short rate and the bond price -/

/-- `∫₀ᵀ (gsrKernelLp)² = gsrBondV` for the `L²`-representative (a.e. equal to the
honest kernel). -/
private lemma gsrKernelLp_integral_sq {κ : ℝ} (hκ : 0 < κ) (σ1 σ2 : ℝ) (Tstar T : ℝ≥0)
    (hTstarT : (Tstar : ℝ) ≤ (T : ℝ)) :
    (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T u) ^ 2 ∂volume)
      = gsrBondV κ σ1 σ2 (Tstar : ℝ) (T : ℝ) := by
  exact (gsrKernel_memLp hκ σ1 σ2 (Tstar : ℝ) T).integral_sq_toLp.trans
    (gsrKernel_integral_sq_eq hκ σ1 σ2 (Tstar : ℝ) (T : ℝ) Tstar.2 hTstarT)

/-- **The GSR integrated short rate**, *defined* by its Wiener representation: deterministic
mean (the Vasicek mean, unchanged — only the volatility axis is piecewise here) plus the
Wiener integral of the piecewise-weighted kernel. That this is `∫₀ᵀ r_s ds` for the solution
of the GSR short-rate SDE is the modelling bridge (the SDE solution and the time-order swap),
cited, not derived, as for `vasicekIntegratedRate`. -/
noncomputable def gsrIntegratedRate (hB : IsPreBrownianReal B μ) (r₀ θ σ1 σ2 : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (Tstar T : ℝ≥0) (ω : Ω) : ℝ :=
  vasicekIntegratedMean r₀ θ κ (T : ℝ)
    + wienerIntegralLp B hB T (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T) ω

/-- **The GSR integrated short rate is Gaussian**: `N(M(T), gsrBondV κ σ₁ σ₂ T* T)`,
`M` the (unchanged) Vasicek mean. -/
theorem gsrIntegratedRate_hasLaw_gaussian (hB : IsPreBrownianReal B μ) (r₀ θ σ1 σ2 : ℝ)
    {κ : ℝ} (hκ : 0 < κ) (Tstar T : ℝ≥0) (hTstarT : (Tstar : ℝ) ≤ (T : ℝ)) :
    HasLaw (gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar T)
      (gaussianReal (vasicekIntegratedMean r₀ θ κ (T : ℝ))
        (gsrBondV κ σ1 σ2 (Tstar : ℝ) (T : ℝ)).toNNReal) μ := by
  have hW := wienerIntegralLp_hasLaw_gaussian_of_integral_sq hB T
    (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T) (gsrKernelLp_integral_sq hκ σ1 σ2 Tstar T hTstarT)
  have hShift := gaussianReal_const_add hW (vasicekIntegratedMean r₀ θ κ (T : ℝ))
  convert hShift using 2 <;> first | rfl | ring

/-- **The GSR zero-coupon bond price**: the exponential-Gaussian moment
`𝔼_μ[exp(−∫₀ᵀ r_s ds)] = exp(−M(T) + gsrBondV κ σ₁ σ₂ T* T / 2)`, with `∫₀ᵀ r_s ds` the
Wiener representation `gsrIntegratedRate`; it is `P(0,T)` when `μ` is read as the pricing
measure. The Wiener bond-price lemma `integral_exp_neg_add_mul_wienerIntegralLp` at `m = M(T)`,
`c = 1` and the GSR kernel, whose squared `L²`-norm is `gsrBondV` (`gsrKernel_integral_sq_eq`). -/
theorem gsrBondPrice_eq (hB : IsPreBrownianReal B μ) (r₀ θ σ1 σ2 : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (Tstar T : ℝ≥0) (hTstarT : (Tstar : ℝ) ≤ (T : ℝ)) :
    ∫ ω, Real.exp (-(gsrIntegratedRate hB r₀ θ σ1 σ2 hκ Tstar T ω)) ∂μ
      = Real.exp (-(vasicekIntegratedMean r₀ θ κ (T : ℝ))
          + gsrBondV κ σ1 σ2 (Tstar : ℝ) (T : ℝ) / 2) := by
  have h := integral_exp_neg_add_mul_wienerIntegralLp hB T (vasicekIntegratedMean r₀ θ κ (T : ℝ)) 1
    (gsrKernelLp hκ σ1 σ2 (Tstar : ℝ) T)
  simp only [one_mul, one_pow] at h
  rwa [gsrKernelLp_integral_sq hκ σ1 σ2 Tstar T hTstarT] at h

/-! ### One volatility: GSR is Vasicek -/

/-- **The one-volatility GSR variance is Vasicek's**: `gsrBondV κ σ σ T* T = σ²·vasicekBondV κ T`
— with `σ₁ = σ₂` the two antiderivative differences telescope to `F(T) − F(0) = V(T)`. -/
theorem gsrBondV_self (κ σ Tstar T : ℝ) :
    gsrBondV κ σ σ Tstar T = σ ^ 2 * vasicekBondV κ T := by
  simp only [gsrBondV, vasicekIntegratedKernelSqAntideriv, vasicekBondV, sub_self, mul_zero,
    neg_zero, Real.exp_zero, sub_zero]
  ring

omit [IsProbabilityMeasure μ] in
/-- **GSR with one volatility is Vasicek**: at `σ₁ = σ₂ = σ` the GSR kernel is `σ` times the
Vasicek integrated kernel, so by linearity of the Wiener integral the integrated GSR rate is
almost surely the integrated Vasicek rate `vasicekIntegratedRate` (whatever the breakpoint). -/
theorem gsrIntegratedRate_self_ae (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (Tstar T : ℝ≥0) :
    gsrIntegratedRate hB r₀ θ σ σ hκ Tstar T =ᵐ[μ] vasicekIntegratedRate hB r₀ θ σ hκ T := by
  have hk : gsrKernelLp hκ σ σ (Tstar : ℝ) T = σ • vasicekIntegratedKernelLp hκ T := by
    refine Lp.ext ?_
    filter_upwards [(gsrKernel_memLp hκ σ σ (Tstar : ℝ) T).coeFn_toLp,
      Lp.coeFn_smul σ (vasicekIntegratedKernelLp hκ T),
      (vasicekIntegratedKernel_memLp hκ T).coeFn_toLp] with u h₁ h₂ h₃
    rw [gsrKernelLp, h₁, h₂, Pi.smul_apply, vasicekIntegratedKernelLp, h₃]
    simp only [gsrKernel, gsrSigma, ite_self, smul_eq_mul]
  filter_upwards [wienerIntegralLp_smul_ae hB T σ (vasicekIntegratedKernelLp hκ T)] with ω hω
  rw [gsrIntegratedRate, vasicekIntegratedRate, hk, hω]

end MathFin
