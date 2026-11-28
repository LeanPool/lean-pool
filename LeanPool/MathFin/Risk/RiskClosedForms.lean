/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Risk.ValueAtRisk
public import Mathlib.Probability.Distributions.Pareto

/-!
# Closed forms for value-at-risk and expected shortfall: exponential and Pareto losses

The general value-at-risk and expected shortfall of `Risk/ValueAtRisk.lean` evaluated on
two textbook laws (McNeil–Frey–Embrechts, *Quantitative Risk Management*, Example 2.14; QRM
Exercise Book, Exercises 2.12 and 2.23):

* the **exponential** law `Exp(λ)` (Mathlib's `expMeasure`), a light tail:
  `VaR_α = −log(1 − α)/λ` and `ES_α = (1 − log(1 − α))/λ`;
* the **Pareto** law of Mathlib's `paretoMeasure t r` (type I, `F(x) = 1 − (t/x)^r` on `[t, ∞)`)
  and its shift to the origin, the **Lomax** (Pareto type II) law `Pa(θ, κ)` with
  `F(x) = 1 − (κ/(κ + x))^θ` on `[0, ∞)` (`lomaxMeasure`), heavy tails:
  `VaR_α = κ((1 − α)^{−1/θ} − 1)` and `ES_α = κ(θ/(θ − 1)·(1 − α)^{−1/θ} − 1)` for `θ > 1`.

The two tails separate in the **shortfall-to-quantile ratio** `ES_α/VaR_α` as `α → 1`: it tends
to `1` for the exponential law and to `θ/(θ − 1) > 1` for the Lomax law. For the type-I Pareto law
the ratio is `r/(r − 1)` at every level. A heavy tail makes the average loss beyond VaR a fixed
multiple of VaR, however far into the tail one looks.

The **median shortfall**, the median of the loss conditional on exceeding `VaR_α`, is itself a
value-at-risk, `MS_α = VaR_{(1+α)/2}`, whenever the distribution function is continuous
(`medianShortfall_eq_valueAtRisk`, QRM Exercise Book, Exercise 2.29 b)).

Every quantile below is read off the CDF through `quantile_eq_iff`: `quantile μ p = a` exactly
when `p ≤ F(a)` and `F(x) < p` for `x < a`. Mathlib records the Pareto CDF only as an integral of
its density; `cdf_paretoMeasure_of_le` evaluates it.

## Main definitions

* `lomaxMeasure`: the Lomax (Pareto type II) law `Pa(θ, κ)`, the type-I Pareto law of scale `κ`
  and shape `θ` shifted to the origin, with `F(x) = 1 − (κ/(κ + x))^θ` on `[0, ∞)`.
* `medianShortfall`: the median of the law of a loss `X` conditioned on exceeding its
  value-at-risk, `F⁻¹_{X | X > VaR_α(X)}(1/2)`.

## Main results

* `valueAtRisk_eq_iff`: a VaR is characterised by the CDF (from `quantile_eq_iff` in
  `Probability/Laws/Quantile.lean`).
* `valueAtRisk_of_hasLaw_expMeasure` (via `quantile_expMeasure` in
  `Probability/Laws/Quantile.lean`),
  `expectedShortfall_of_hasLaw_expMeasure`: the exponential closed forms.
* `tendsto_expectedShortfall_div_valueAtRisk_expMeasure`: `ES_α/VaR_α → 1` (light tail).
* `cdf_paretoMeasure_of_le`, `cdf_paretoMeasure_of_lt`, `quantile_paretoMeasure`: the type-I
  Pareto CDF and quantile.
* `expectedShortfall_of_hasLaw_paretoMeasure`: `ES_α = r/(r − 1)·VaR_α` for type-I Pareto with
  `r > 1`.
* `cdf_lomaxMeasure`, `valueAtRisk_of_hasLaw_lomaxMeasure`,
  `expectedShortfall_of_hasLaw_lomaxMeasure`: the Lomax CDF and closed forms.
* `tendsto_expectedShortfall_div_valueAtRisk_lomaxMeasure`: for `θ > 1`, `ES_α/VaR_α → θ/(θ − 1)`
  as `α → 1` (heavy tail).
* `medianShortfall_eq_valueAtRisk`: the median of the loss beyond `VaR_α` is `VaR_{(1+α)/2}` for a
  continuous distribution function.

## References

* [*QRM Exercise Book*][QRMExerciseBook], Ex. 2.12(a); Ex. 2.12(d); Ex. 2.23(a); Ex. 2.23(c); Ex.
  2.29(b)

## Tags

VaR closed form, exponential loss, Pareto loss, Lomax distribution, heavy tails, median shortfall,
light tail, tail risk, MSC 91G70, MSC 60E05, JEL G32
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Filter Topology Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ} {μ : Measure ℝ}
  {p α : ℝ}

/-! ### Reading a quantile off the CDF -/

/-- A VaR is pinned down by the distribution function of the loss:
`VaR_α(X) = a ↔ α ≤ P(X ≤ a) ∧ ∀ x < a, P(X ≤ x) < α`. -/
theorem valueAtRisk_eq_iff [IsProbabilityMeasure P] (hX : AEMeasurable X P) (hα : α ∈ Ioo 0 1)
    {a : ℝ} :
    valueAtRisk X P α = a ↔ α ≤ P.real {ω | X ω ≤ a} ∧ ∀ x < a, P.real {ω | X ω ≤ x} < α := by
  refine ⟨?_, fun ⟨ha, hlt⟩ ↦ le_antisymm ((valueAtRisk_le_iff hX hα).2 ha)
    (le_of_forall_lt fun x hx ↦ (lt_valueAtRisk_iff hX hα).2 (hlt x hx))⟩
  rintro rfl
  exact ⟨le_measureReal_le_valueAtRisk hX hα, fun _ hx ↦ (lt_valueAtRisk_iff hX hα).1 hx⟩

/-- The VaR curve is the quantile curve on `(α, 1)`, so ES is the average of any closed form for
it. -/
lemma expectedShortfall_eq_of_valueAtRisk_eq {f : ℝ → ℝ}
    (hf : ∀ u ∈ Ioo α 1, valueAtRisk X P u = f u) :
    expectedShortfall X P α = (1 - α)⁻¹ * ∫ u in Ioo α 1, f u := by
  rw [expectedShortfall, setIntegral_congr_fun measurableSet_Ioo hf]

/-! ### The exponential law -/

/-- **VaR of an exponential loss**: `VaR_α(X) = −log(1 − α)/λ` for `X ~ Exp(λ)`. -/
theorem valueAtRisk_of_hasLaw_expMeasure {r : ℝ} (hr : 0 < r) (hX : HasLaw X (expMeasure r) P)
    (hα : α ∈ Ioo 0 1) : valueAtRisk X P α = -log (1 - α) / r := by
  rw [valueAtRisk_eq_quantile hX, quantile_expMeasure hr hα]

/-- **ES of an exponential loss**: `ES_α(X) = (1 − log(1 − α))/λ` for `X ~ Exp(λ)`. -/
theorem expectedShortfall_of_hasLaw_expMeasure {r : ℝ} (hr : 0 < r)
    (hX : HasLaw X (expMeasure r) P) (hα : α ∈ Ioo 0 1) :
    expectedShortfall X P α = (1 - log (1 - α)) / r := by
  have h1α : 1 - α ≠ 0 := (sub_pos.2 hα.2).ne'
  have hr' : r ≠ 0 := hr.ne'
  rw [expectedShortfall_eq_of_valueAtRisk_eq fun u hu ↦
      valueAtRisk_of_hasLaw_expMeasure hr hX ⟨hα.1.trans hu.1, hu.2⟩,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hα.2.le,
    intervalIntegral.integral_div,
    intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left log 1,
    sub_self, integral_log]
  field_simp
  ring

/-- As the level `α` rises to `1`, the tail mass `1 − α` falls to `0` from above. -/
lemma tendsto_one_sub_nhdsLT_one : Tendsto (fun α : ℝ ↦ 1 - α) (𝓝[<] 1) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (eventually_nhdsWithin_of_forall fun _ hα ↦ show (0 : ℝ) < _ from sub_pos.2 hα)
  have h : Tendsto (fun α : ℝ ↦ 1 - α) (𝓝 1) (𝓝 (1 - 1)) :=
    (continuous_const.sub continuous_id).tendsto 1
  rw [sub_self] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **Light tail**: for an exponential loss the shortfall-to-quantile ratio tends to `1`,
`ES_α/VaR_α → 1` as `α → 1⁻` (QRM Exercise Book, Exercise 2.23 a)). -/
theorem tendsto_expectedShortfall_div_valueAtRisk_expMeasure {r : ℝ} (hr : 0 < r)
    (hX : HasLaw X (expMeasure r) P) :
    Tendsto (fun α ↦ expectedShortfall X P α / valueAtRisk X P α) (𝓝[<] 1) (𝓝 1) := by
  have hlim : Tendsto (fun α ↦ 1 + (-log (1 - α))⁻¹) (𝓝[<] 1) (𝓝 1) := by
    have h : Tendsto (fun α ↦ -log (1 - α)) (𝓝[<] 1) atTop :=
      tendsto_neg_atBot_atTop.comp (tendsto_log_nhdsGT_zero.comp tendsto_one_sub_nhdsLT_one)
    simpa using h.inv_tendsto_atTop.const_add 1
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with α hα
  have hlog : log (1 - α) ≠ 0 := (log_neg (sub_pos.2 hα.2) (by linarith [hα.1])).ne
  have hr' : r ≠ 0 := hr.ne'
  rw [expectedShortfall_of_hasLaw_expMeasure hr hX hα, valueAtRisk_of_hasLaw_expMeasure hr hX hα]
  field_simp
  ring

/-! ### The type-I Pareto law -/

section Pareto

variable {t r x : ℝ}

/-- Below its scale `t` the Pareto law puts no mass: `F(x) = 0` for `x < t`. -/
theorem cdf_paretoMeasure_of_lt (ht : 0 < t) (hr : 0 < r) (hx : x < t) :
    cdf (paretoMeasure t r) x = 0 := by
  have := isProbabilityMeasure_paretoMeasure ht hr
  rw [cdf_eq_real, paretoMeasure, measureReal_def, withDensity_apply _ measurableSet_Iic,
    setLIntegral_congr_fun measurableSet_Iic fun _ hy ↦ paretoPDF_of_lt (lt_of_le_of_lt hy hx),
    lintegral_zero, ENNReal.toReal_zero]

/-- **The Pareto CDF**: `F(x) = 1 − (t/x)^r` for `x ≥ t`. Mathlib states the CDF only as the
integral of the density; the tail integral `∫_x^∞ r t^r y^{−(r+1)} dy = (t/x)^r` evaluates it. -/
theorem cdf_paretoMeasure_of_le (ht : 0 < t) (hr : 0 < r) (hx : t ≤ x) :
    cdf (paretoMeasure t r) x = 1 - (t / x) ^ r := by
  have := isProbabilityMeasure_paretoMeasure ht hr
  have hx0 : 0 < x := ht.trans_le hx
  have hint : IntegrableOn (fun y ↦ r * t ^ r * y ^ (-(r + 1))) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hx0).const_mul _
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi x)] fun y ↦ r * t ^ r * y ^ (-(r + 1)) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun y hy ↦ by
      have : 0 < y := hx0.trans hy
      positivity
  rw [cdf_eq_real, ← compl_Ioi, probReal_compl_eq_one_sub measurableSet_Ioi, paretoMeasure,
    measureReal_def, withDensity_apply _ measurableSet_Ioi,
    setLIntegral_congr_fun measurableSet_Ioi fun _ hy ↦ paretoPDF_of_le (hx.trans (le_of_lt hy)),
    ← ofReal_integral_eq_lintegral_ofReal hint hnn,
        ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn),
    integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx0,
    div_rpow ht.le hx0.le, show -(r + 1) + 1 = -r by ring, rpow_neg hx0.le]
  field_simp

/-- **The Pareto quantile**: `F⁻¹(p) = t (1 − p)^{−1/r}`. -/
theorem quantile_paretoMeasure (ht : 0 < t) (hr : 0 < r) (hp : p ∈ Ioo 0 1) :
    quantile (paretoMeasure t r) p = t * (1 - p) ^ (-r⁻¹) := by
  have h1p : 0 < 1 - p := sub_pos.2 hp.2
  have hs : 1 ≤ (1 - p) ^ (-r⁻¹) :=
    one_le_rpow_of_pos_of_le_one_of_nonpos h1p (by linarith [hp.1]) (by simp [hr.le])
  have ha : t ≤ t * (1 - p) ^ (-r⁻¹) := le_mul_of_one_le_right ht.le hs
  -- the tail ratio at the candidate quantile is `(1 - p)^{1/r}`
  have hratio : t / (t * (1 - p) ^ (-r⁻¹)) = (1 - p) ^ r⁻¹ := by
    rw [rpow_neg h1p.le, div_mul_eq_div_div, div_self ht.ne', one_div, inv_inv]
  have hpow : ((1 - p) ^ r⁻¹) ^ r = 1 - p := by
    rw [← rpow_mul h1p.le, inv_mul_cancel₀ hr.ne', rpow_one]
  refine (quantile_eq_iff hp).2 ⟨?_, fun y hy ↦ ?_⟩
  · rw [cdf_paretoMeasure_of_le ht hr ha, hratio, hpow, sub_sub_cancel]
  · rcases lt_or_ge y t with hyt | hyt
    · rw [cdf_paretoMeasure_of_lt ht hr hyt]
      exact hp.1
    · have hy0 : 0 < y := ht.trans_le hyt
      rw [cdf_paretoMeasure_of_le ht hr hyt]
      have hlt : (1 - p) ^ r⁻¹ < t / y := by
        rw [← hratio]
        exact div_lt_div_of_pos_left ht hy0 hy
      have := rpow_lt_rpow (rpow_nonneg h1p.le _) hlt hr
      rw [hpow] at this
      linarith

/-- `∫_α^1 (1 − u)^{−1/r} du = r/(r − 1)·(1 − α)^{1 − 1/r}` for `r > 1`: the Pareto quantile is
integrable up to level `1` exactly when the mean is finite. -/
lemma integral_one_sub_rpow (hα : α < 1) (hr : 1 < r) :
    ∫ u in Ioo α 1, (1 - u) ^ (-r⁻¹) = r / (r - 1) * (1 - α) ^ (1 - r⁻¹) := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
  have hexp : -1 < -r⁻¹ := neg_lt_neg (inv_lt_one_of_one_lt₀ hr)
  have hne : -r⁻¹ + 1 ≠ 0 := by linarith
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hα.le,
    intervalIntegral.integral_comp_sub_left (fun x ↦ x ^ (-r⁻¹)) 1, sub_self,
    integral_rpow (Or.inl hexp), zero_rpow hne, sub_zero, show -r⁻¹ + 1 = 1 - r⁻¹ by ring]
  have hr1 : r - 1 ≠ 0 := by linarith
  field_simp

/-- **ES of a Pareto loss** (`r > 1`): `ES_α(X) = r/(r − 1)·VaR_α(X)`, a constant multiple of
`VaR_α` at every level. -/
theorem expectedShortfall_of_hasLaw_paretoMeasure (ht : 0 < t) (hr : 1 < r)
    (hX : HasLaw X (paretoMeasure t r) P) (hα : α ∈ Ioo 0 1) :
    expectedShortfall X P α = r / (r - 1) * (t * (1 - α) ^ (-r⁻¹)) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  have h1α' : 1 - α ≠ 0 := h1α.ne'
  have hr1 : r - 1 ≠ 0 := by linarith
  rw [expectedShortfall_eq_of_valueAtRisk_eq fun u hu ↦ by
      rw [valueAtRisk_eq_quantile hX, quantile_paretoMeasure ht hr0 ⟨hα.1.trans hu.1, hu.2⟩],
    integral_const_mul, integral_one_sub_rpow hα.2 hr, sub_eq_add_neg (1 : ℝ) r⁻¹,
    rpow_add h1α, rpow_one]
  field_simp

end Pareto

/-! ### The Lomax (Pareto type II) law -/

section Lomax

variable {θ κ : ℝ}

/-- The **Lomax** (Pareto type II) law `Pa(θ, κ)`: the type-I Pareto law of scale `κ` and shape
`θ`, shifted to start at `0`. Its CDF is `F(x) = 1 − (κ/(κ + x))^θ` on `[0, ∞)`
(`cdf_lomaxMeasure`); `Pa(θ, 1)` is the Pareto law of the QRM Exercise Book, Exercise 2.12 d). -/
noncomputable def lomaxMeasure (θ κ : ℝ) : Measure ℝ :=
  (paretoMeasure κ θ).map fun y ↦ y - κ

lemma isProbabilityMeasure_lomaxMeasure (hθ : 0 < θ) (hκ : 0 < κ) :
    IsProbabilityMeasure (lomaxMeasure θ κ) :=
  have := isProbabilityMeasure_paretoMeasure hκ hθ
  inferInstanceAs (IsProbabilityMeasure ((paretoMeasure κ θ).map (· - κ)))

/-- **The Lomax CDF**: `F(x) = 1 − (κ/(κ + x))^θ` for `x ≥ 0`. -/
theorem cdf_lomaxMeasure (hθ : 0 < θ) (hκ : 0 < κ) {x : ℝ} (hx : 0 ≤ x) :
    cdf (lomaxMeasure θ κ) x = 1 - (κ / (κ + x)) ^ θ := by
  have := isProbabilityMeasure_lomaxMeasure hθ hκ
  have := isProbabilityMeasure_paretoMeasure hκ hθ
  rw [cdf_eq_real, lomaxMeasure, map_measureReal_apply (measurable_sub_const κ) measurableSet_Iic,
    show (fun y ↦ y - κ) ⁻¹' Iic x = Iic (κ + x) by ext y; simp [add_comm],
    ← cdf_eq_real, cdf_paretoMeasure_of_le hκ hθ (le_add_of_nonneg_right hx)]

/-- **The Lomax quantile**: `F⁻¹(p) = κ((1 − p)^{−1/θ} − 1)`. -/
theorem quantile_lomaxMeasure (hθ : 0 < θ) (hκ : 0 < κ) (hp : p ∈ Ioo 0 1) :
    quantile (lomaxMeasure θ κ) p = κ * ((1 - p) ^ (-θ⁻¹) - 1) := by
  have := isProbabilityMeasure_paretoMeasure hκ hθ
  rw [lomaxMeasure, quantile_map (h := fun y ↦ y - κ) (fun _ _ h ↦ sub_le_sub_right h κ)
    (by fun_prop : Continuous fun y : ℝ ↦ y - κ).lowerSemicontinuous hp,
    quantile_paretoMeasure hκ hθ hp]
  ring

/-- **VaR of a Lomax loss**: `VaR_α(X) = κ((1 − α)^{−1/θ} − 1)` for `X ~ Pa(θ, κ)`
(QRM Exercise Book, Exercise 2.12 d)). -/
theorem valueAtRisk_of_hasLaw_lomaxMeasure (hθ : 0 < θ) (hκ : 0 < κ)
    (hX : HasLaw X (lomaxMeasure θ κ) P) (hα : α ∈ Ioo 0 1) :
    valueAtRisk X P α = κ * ((1 - α) ^ (-θ⁻¹) - 1) := by
  rw [valueAtRisk_eq_quantile hX, quantile_lomaxMeasure hθ hκ hα]

/-- **ES of a Lomax loss** (`θ > 1`, finite mean): `ES_α(X) = κ(θ/(θ − 1)·(1 − α)^{−1/θ} − 1)`
for `X ~ Pa(θ, κ)` (QRM Exercise Book, Exercise 2.12 d)). -/
theorem expectedShortfall_of_hasLaw_lomaxMeasure (hθ : 1 < θ) (hκ : 0 < κ)
    (hX : HasLaw X (lomaxMeasure θ κ) P) (hα : α ∈ Ioo 0 1) :
    expectedShortfall X P α = κ * (θ / (θ - 1) * (1 - α) ^ (-θ⁻¹) - 1) := by
  have hθ0 : 0 < θ := zero_lt_one.trans hθ
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  have h1α' : 1 - α ≠ 0 := h1α.ne'
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have hint : IntegrableOn (fun u ↦ (1 - u) ^ (-θ⁻¹)) (Ioo α 1) := by
    by_contra h
    have h0 := integral_one_sub_rpow hα.2 hθ
    rw [integral_undef h] at h0
    have : 0 < θ - 1 := by linarith
    have : 0 < θ / (θ - 1) * (1 - α) ^ (1 - θ⁻¹) := by positivity
    linarith
  rw [expectedShortfall_eq_of_valueAtRisk_eq fun u hu ↦
      valueAtRisk_of_hasLaw_lomaxMeasure hθ0 hκ hX ⟨hα.1.trans hu.1, hu.2⟩,
    integral_const_mul, integral_sub hint (integrableOn_const (by simp)), setIntegral_const,
    Real.volume_real_Ioo_of_le hα.2.le, smul_eq_mul, mul_one, integral_one_sub_rpow hα.2 hθ,
    sub_eq_add_neg (1 : ℝ) θ⁻¹, rpow_add h1α, rpow_one]
  field_simp

/-- **Heavy tail**: for a Lomax loss with `θ > 1` the shortfall-to-quantile ratio tends to
`θ/(θ − 1) > 1`, `ES_α/VaR_α → θ/(θ − 1)` as `α → 1⁻` (QRM Exercise Book, Exercise 2.23 c)). -/
theorem tendsto_expectedShortfall_div_valueAtRisk_lomaxMeasure (hθ : 1 < θ) (hκ : 0 < κ)
    (hX : HasLaw X (lomaxMeasure θ κ) P) :
    Tendsto (fun α ↦ expectedShortfall X P α / valueAtRisk X P α) (𝓝[<] 1)
      (𝓝 (θ / (θ - 1))) := by
  have hθ0 : 0 < θ := zero_lt_one.trans hθ
  -- `s = (1 − α)^{−1/θ} → ∞`, and the ratio is `(θ/(θ − 1)·s − 1)/(s − 1)`
  have hs : Tendsto (fun α : ℝ ↦ (1 - α) ^ (-θ⁻¹)) (𝓝[<] 1) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos (inv_pos.2 hθ0))).comp
      tendsto_one_sub_nhdsLT_one
  have hinv := hs.inv_tendsto_atTop
  have hlim : Tendsto (fun α ↦ (θ / (θ - 1) - ((1 - α) ^ (-θ⁻¹))⁻¹) / (1 - ((1 - α) ^ (-θ⁻¹))⁻¹))
      (𝓝[<] 1) (𝓝 (θ / (θ - 1))) := by
    have h := ((tendsto_const_nhds (x := θ / (θ - 1))).sub hinv).div
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hinv) (by norm_num)
    rw [sub_zero, sub_zero, div_one] at h
    exact h
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with α hα
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  have hs1 : 1 < (1 - α) ^ (-θ⁻¹) :=
    one_lt_rpow_of_pos_of_lt_one_of_neg h1α (by linarith [hα.1]) (neg_neg_of_pos (inv_pos.2 hθ0))
  have hne : (1 - α) ^ (-θ⁻¹) - 1 ≠ 0 := (sub_pos.2 hs1).ne'
  have hs0 : (1 - α) ^ (-θ⁻¹) ≠ 0 := (zero_lt_one.trans hs1).ne'
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have hκ' : κ ≠ 0 := hκ.ne'
  rw [expectedShortfall_of_hasLaw_lomaxMeasure hθ hκ hX hα,
    valueAtRisk_of_hasLaw_lomaxMeasure hθ0 hκ hX hα]
  field_simp

end Lomax

/-! ### Median shortfall -/

section MedianShortfall

/-- The **median shortfall** of a loss `X` at level `α`: the median of the law of `X`
conditioned on exceeding its value-at-risk, `MS_α(X) = F⁻¹_{X | X > VaR_α(X)}(1/2)`. -/
noncomputable def medianShortfall (X : Ω → ℝ) (P : Measure Ω) (α : ℝ) : ℝ :=
  quantile ((P.map X)[|Ioi (valueAtRisk X P α)]) (1 / 2)

/-- **Median shortfall is a value-at-risk** (QRM Exercise Book, Exercise 2.29 b)): for a loss
with a continuous distribution function, `MS_α(X) = VaR_{(1+α)/2}(X)`. Given that the loss
exceeds `VaR_α`, its conditional CDF is `(F − α)/(1 − α)`, which crosses `1/2` exactly where `F`
crosses `(1 + α)/2`. -/
theorem medianShortfall_eq_valueAtRisk [IsProbabilityMeasure P]
    (hF : Continuous (cdf (P.map X))) (hα : α ∈ Ioo 0 1) :
    medianShortfall X P α = valueAtRisk X P ((1 + α) / 2) := by
  have h1α : 0 < 1 - α := sub_pos.2 hα.2
  have hv : cdf (P.map X) (valueAtRisk X P α) = α := cdf_quantile hF hα
  -- the tail beyond `VaR_α` carries mass `1 − α`
  have hmass : (P.map X) (Ioi (valueAtRisk X P α)) = ENNReal.ofReal (1 - α) := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf, hv,
      ENNReal.ofReal_sub _ hα.1.le, ENNReal.ofReal_one]
  have hne : (P.map X) (Ioi (valueAtRisk X P α)) ≠ 0 := by
    rw [hmass]
    exact (ENNReal.ofReal_pos.2 h1α).ne'
  have := cond_isProbabilityMeasure (μ := P.map X) hne
  -- the distribution function of the tail law is `(F − α)/(1 − α)` beyond `VaR_α`
  have hcdf (x : ℝ) : cdf ((P.map X)[|Ioi (valueAtRisk X P α)]) x =
      if valueAtRisk X P α ≤ x then (cdf (P.map X) x - α) / (1 - α) else 0 := by
    rw [cdf_eq_real, measureReal_def, cond_apply measurableSet_Ioi, hmass, Ioi_inter_Iic]
    split_ifs with hvx
    · have hIoc := (cdf (P.map X)).measure_Ioc (valueAtRisk X P α) x
      rw [measure_cdf] at hIoc
      rw [hIoc, hv, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal h1α.le,
        ENNReal.toReal_ofReal (sub_nonneg.2 (hv ▸ monotone_cdf (P.map X) hvx))]
      ring
    · rw [Ioc_eq_empty_of_le (not_le.1 hvx).le, measure_empty, mul_zero, ENNReal.toReal_zero]
  change quantile _ (1 / 2) = quantile (P.map X) ((1 + α) / 2)
  unfold quantile
  congr 1
  ext x
  simp only [mem_ofPred_eq]
  rw [hcdf x]
  split_ifs with hvx
  · rw [le_div_iff₀ h1α]
    constructor <;> intro h <;> linarith
  · have hFx : cdf (P.map X) x ≤ α := hv ▸ monotone_cdf (P.map X) (not_le.1 hvx).le
    constructor <;> intro h <;> linarith [hα.2]

end MedianShortfall

end MathFin
