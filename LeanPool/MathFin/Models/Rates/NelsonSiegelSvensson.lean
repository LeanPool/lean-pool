/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Nelson-Siegel-Svensson yield-curve parametrization

The **Nelson-Siegel** (1987) and its **Svensson** (1994) four-term extension
are closed-form exponential-basis parametrizations of the zero-coupon yield
curve, fit by least squares to observed yields rather than recovered by
bootstrapping (`Models/Rates/YieldCurve.lean`, `Models/Rates/Bootstrapping.lean`)
from coupon-bond prices. The Svensson curve is

  `y(τ) = β₀ + β₁·s(τ/l₁) + β₂·(s(τ/l₁) - e^{-τ/l₁}) + β₃·(s(τ/l₂) - e^{-τ/l₂})`,

where `s(x) = (1 - e^{-x})/x` is the (normalized) slope factor shared by the
level/slope/curvature decomposition, and `l₁, l₂ > 0` are decay parameters
governing where the two curvature humps peak. Setting `β₃ = 0` recovers the
plain three-factor Nelson-Siegel curve.

This is a genuinely different object from bootstrapping: it is a closed form
in four (Nelson-Siegel) or six (Svensson) parameters, fit across the whole
curve at once, rather than a maturity-by-maturity recursive discount-factor
recovery. (Only continuity on `(0, ∞)` is proved here; at `τ = 0` the Lean
definition takes Lean's `x / 0 = 0` junk value, and the short end is stated
as a limit.)

## Main definitions

* `nssSlope`: the Nelson-Siegel slope factor `s(x) = (1 - e^{-x}) / x`.
* `nssYield`: the Nelson-Siegel-Svensson closed-form yield curve
  `y(τ) = β₀ + β₁·s(τ/l₁) + β₂·(s(τ/l₁) - e^{-τ/l₁}) + β₃·(s(τ/l₂) - e^{-τ/l₂})`.

## Main results

* `continuousOn_nssYield` — `y` is continuous on `(0, ∞)` (the economically
  meaningful domain: no coupon bond or discount factor is quoted at `τ = 0`).
* `tendsto_nssSlope_nhdsNE_zero` — the core calculus fact underlying the
  curve's short end: `s(x) → 1` as `x → 0 (through nonzero values)`, obtained from `HasDerivAt` of
  `x ↦ 1 - e^{-x}` at `0` (the slope factor is literally a difference
  quotient of that function through the origin).
* `tendsto_nssSlope_atTop` — the slope factor's long end: `s(x) → 0` as `x → ∞`.
* `tendsto_nssYield_nhdsNE_zero` — **short-end limit**:
  `y(τ) → β₀ + β₁` as `τ → 0 (through nonzero values)` (the two curvature terms vanish at the short
  end, leaving level plus slope).
* `tendsto_nssYield_atTop` — **long-end limit**: `y(τ) → β₀` as `τ → ∞`
  (all three non-level terms decay away, leaving the level factor as the
  asymptotic long rate).

The slope factor is also the Vasicek rate loading per unit maturity,
`s(κτ) = vasicekBondB κ τ / τ`; `Models/Rates/VasicekYieldNelsonSiegel.lean` writes the
Vasicek zero yield in these factors.

## References

* [C. R. Nelson, A. F. Siegel, *Parsimonious Modeling of Yield Curves*][NelsonSiegel1987].
* [L. E. O. Svensson, *Estimating and Interpreting Forward Interest Rates: Sweden
  1992–1994*][Svensson1994].

## Tags

Nelson–Siegel, Svensson, yield curve fitting, level slope curvature, parametric yield curve,
zero-coupon yield, MSC 91G30, JEL E43
-/

@[expose] public section

namespace MathFin

open Filter Topology

/-- The Nelson-Siegel **slope factor** `s(x) = (1 - e^{-x}) / x`, the
normalized exponential building block shared by the slope and curvature
terms of the Nelson-Siegel-Svensson curve. -/
noncomputable def nssSlope (x : ℝ) : ℝ := (1 - Real.exp (-x)) / x

/-- The **Nelson-Siegel-Svensson** closed-form yield curve:
`y(τ) = β₀ + β₁·s(τ/l₁) + β₂·(s(τ/l₁) - e^{-τ/l₁}) + β₃·(s(τ/l₂) - e^{-τ/l₂})`.
Setting `β₃ = 0` gives the plain three-factor Nelson-Siegel (1987) curve;
the fourth term is Svensson's (1994) extension adding a second curvature
hump at a distinct decay rate `l₂`. -/
noncomputable def nssYield (β₀ β₁ β₂ β₃ l₁ l₂ τ : ℝ) : ℝ :=
  β₀ + β₁ * nssSlope (τ / l₁)
    + β₂ * (nssSlope (τ / l₁) - Real.exp (-(τ / l₁)))
    + β₃ * (nssSlope (τ / l₂) - Real.exp (-(τ / l₂)))

/-- `nssSlope` is continuous away from `0` (an ordinary quotient of continuous
functions with nonvanishing denominator). -/
theorem continuousAt_nssSlope {x : ℝ} (hx : x ≠ 0) : ContinuousAt nssSlope x := by
  unfold nssSlope
  fun_prop (disch := assumption)

/-- **The curve is continuous on `(0, ∞)`**, the economically meaningful
domain for a yield curve (no instrument is quoted at `τ = 0`). -/
theorem continuousOn_nssYield (β₀ β₁ β₂ β₃ l₁ l₂ : ℝ)
    (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0) :
    ContinuousOn (nssYield β₀ β₁ β₂ β₃ l₁ l₂) (Set.Ioi 0) := by
  have h1 : ∀ τ ∈ Set.Ioi (0 : ℝ), τ / l₁ ≠ 0 := fun τ hτ ↦ div_ne_zero hτ.ne' hl₁
  have h2 : ∀ τ ∈ Set.Ioi (0 : ℝ), τ / l₂ ≠ 0 := fun τ hτ ↦ div_ne_zero hτ.ne' hl₂
  unfold nssYield nssSlope
  fun_prop (disch := first | apply h1 | apply h2 | assumption)

/-- **Core calculus fact**: the slope factor `s(x) = (1-e^{-x})/x` tends to
`1` as `x → 0` through nonzero values. This is the difference quotient of
`f(x) = 1 - e^{-x}` through the origin, so it is exactly `HasDerivAt f 1 0`
read via `hasDerivAt_iff_tendsto_slope`. -/
theorem tendsto_nssSlope_nhdsNE_zero :
    Tendsto nssSlope (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hf : HasDerivAt (fun x : ℝ ↦ 1 - Real.exp (-x)) 1 0 := by
    have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-x)) (-1) 0 := by
      simpa using (hasDerivAt_neg (0 : ℝ)).exp
    simpa using hexp.const_sub (1 : ℝ)
  have hcongr : slope (fun x : ℝ ↦ 1 - Real.exp (-x)) 0 = nssSlope := by
    funext x; simp [slope_def_field, nssSlope]
  simpa [hcongr] using hasDerivAt_iff_tendsto_slope.mp hf

/-- Dividing by a nonzero constant tends to `0` through nonzero values as the
numerator tends to `0` through nonzero values (used to transport the `𝓝[≠] 0`
short-end limit of `nssSlope` and `exp` along `τ ↦ τ/l`). -/
theorem tendsto_div_const_nhdsNE_zero {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun x : ℝ ↦ x / c) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hbase : Tendsto (fun x : ℝ ↦ x / c) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_id.div_const c).tendsto (0 : ℝ)
    exact hbase.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    exact div_ne_zero hx hc

/-- **Short-end limit**: as `τ → 0 (through nonzero values)`, the Svensson curve tends to `β₀ + β₁`.
The slope and level stay (`s(τ/lᵢ) → 1`), both curvature terms vanish
(`s(τ/lᵢ) - e^{-τ/lᵢ} → 1 - 1 = 0`), since `τ/lᵢ → 0` and `e^{-τ/lᵢ} → 1`. -/
theorem tendsto_nssYield_nhdsNE_zero (β₀ β₁ β₂ β₃ l₁ l₂ : ℝ)
    (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0) :
    Tendsto (nssYield β₀ β₁ β₂ β₃ l₁ l₂) (𝓝[≠] (0 : ℝ)) (𝓝 (β₀ + β₁)) := by
  have hdiv1 := tendsto_div_const_nhdsNE_zero hl₁
  have hdiv2 := tendsto_div_const_nhdsNE_zero hl₂
  have hs1 : Tendsto (fun τ : ℝ ↦ nssSlope (τ / l₁)) (𝓝[≠] (0 : ℝ)) (𝓝 1) :=
    tendsto_nssSlope_nhdsNE_zero.comp hdiv1
  have hs2 : Tendsto (fun τ : ℝ ↦ nssSlope (τ / l₂)) (𝓝[≠] (0 : ℝ)) (𝓝 1) :=
    tendsto_nssSlope_nhdsNE_zero.comp hdiv2
  have he (c : ℝ) : Tendsto (fun τ : ℝ ↦ Real.exp (-(τ / c))) (𝓝[≠] (0 : ℝ)) (𝓝 1) :=
    ((Real.continuous_exp.comp (continuous_id.div_const c).neg).tendsto' 0 1 (by simp)).mono_left
      nhdsWithin_le_nhds
  have he1 := he l₁
  have he2 := he l₂
  have h : Tendsto (nssYield β₀ β₁ β₂ β₃ l₁ l₂) (𝓝[≠] (0 : ℝ))
      (𝓝 (β₀ + β₁ * 1 + β₂ * (1 - 1) + β₃ * (1 - 1))) := by
    unfold nssYield
    exact
      (((tendsto_const_nhds.add (hs1.const_mul β₁)).add
            ((hs1.sub he1).const_mul β₂)).add
        ((hs2.sub he2).const_mul β₃))
  simpa using h

/-- **Long end of the slope factor**: `s(x) = (1 − e^{−x})/x → 0` as `x → ∞` (the numerator
tends to `1`, the denominator to `∞`). -/
theorem tendsto_nssSlope_atTop : Tendsto nssSlope atTop (𝓝 0) := by
  have hnum : Tendsto (fun x : ℝ ↦ 1 - Real.exp (-x)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
  exact hnum.div_atTop tendsto_id

/-- **Long-end limit**: as `τ → ∞`, the Svensson curve tends to `β₀`, the
level factor — the slope and both curvature terms decay to `0` since
`s(τ/lᵢ) → 0` and `e^{-τ/lᵢ} → 0`, given `l₁, l₂ > 0`. -/
theorem tendsto_nssYield_atTop (β₀ β₁ β₂ β₃ l₁ l₂ : ℝ)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) :
    Tendsto (nssYield β₀ β₁ β₂ β₃ l₁ l₂) atTop (𝓝 β₀) := by
  have hdiv1 : Tendsto (fun τ : ℝ ↦ τ / l₁) atTop atTop :=
    Filter.tendsto_id.atTop_div_const hl₁
  have hdiv2 : Tendsto (fun τ : ℝ ↦ τ / l₂) atTop atTop :=
    Filter.tendsto_id.atTop_div_const hl₂
  have he1 : Tendsto (fun τ : ℝ ↦ Real.exp (-(τ / l₁))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv1
  have he2 : Tendsto (fun τ : ℝ ↦ Real.exp (-(τ / l₂))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv2
  have hs1 : Tendsto (fun τ : ℝ ↦ nssSlope (τ / l₁)) atTop (𝓝 0) :=
    tendsto_nssSlope_atTop.comp hdiv1
  have hs2 : Tendsto (fun τ : ℝ ↦ nssSlope (τ / l₂)) atTop (𝓝 0) :=
    tendsto_nssSlope_atTop.comp hdiv2
  have h : Tendsto (nssYield β₀ β₁ β₂ β₃ l₁ l₂) atTop
      (𝓝 (β₀ + β₁ * 0 + β₂ * (0 - 0) + β₃ * (0 - 0))) := by
    unfold nssYield
    exact
      (((tendsto_const_nhds.add (hs1.const_mul β₁)).add
            ((hs1.sub he1).const_mul β₂)).add
        ((hs2.sub he2).const_mul β₃))
  simpa using h

end MathFin
