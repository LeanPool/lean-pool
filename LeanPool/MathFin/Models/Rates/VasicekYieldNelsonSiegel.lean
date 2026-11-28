/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.NelsonSiegelSvensson
public import LeanPool.MathFin.Models.Rates.VasicekBondPrice

/-!
# The Vasicek yield curve in Nelson–Siegel factors

The Nelson–Siegel slope factor `s(x) = (1 − e^{−x})/x` (`nssSlope`,
`Models/Rates/NelsonSiegelSvensson.lean`) is the Vasicek rate loading per unit maturity:
`s(κτ) = B(τ)/τ` with `B = vasicekBondB` (`vasicekBondB_div_eq_nssSlope`). This file takes the
Vasicek bond price `P(0,T) = 𝔼[exp(−∫₀ᵀ r_s ds)]` that `vasicekBondPrice_eq`
(`Models/Rates/VasicekBondPrice.lean`) derives, and writes its continuously compounded zero
yield `y(T) = −log P(0,T)/T` in slope factors:

  `y(T) = (θ − σ²/(2κ²)) + (r₀ − θ + σ²/κ²)·s(κT) − (σ²/(2κ²))·s(2κT)`.

So the Vasicek curve is a level plus slope factors at the two decay rates `κ` and `2κ`. With
`σ = 0` it is exactly a three-factor Nelson–Siegel curve (level `θ`, slope `r₀ − θ`, no
curvature, decay `1/κ`: `vasicekYield_zeroVol_eq_nssYield`). With `σ ≠ 0` the formula carries
a second slope factor `s(2κT)`, which is not one of the Svensson terms as written (a Svensson
curvature term is `s(τ/l₂) − e^{−τ/l₂}`); whether the curve can be rewritten in Svensson form
is not addressed here.

The slope factor's limits (`tendsto_nssSlope_nhdsNE_zero`, `tendsto_nssSlope_atTop`) then give
the two ends of the Vasicek curve: the yield tends to the short rate `r₀` as `T → 0⁺`, and to
the long rate `θ − σ²/(2κ²)` as `T → ∞`.

As in `vasicekBondPrice_eq`, the expectation is under the probability measure carrying the
Brownian motion, read as the pricing measure, and the integrated short rate is carried in its
Wiener representation.

## Main results

* `vasicekBondB_div_eq_nssSlope` — `vasicekBondB κ τ / τ = nssSlope (κ * τ)`.
* `vasicekBondV_div_eq_nssSlope` — `V(T)/T = (1 − 2 s(κT) + s(2κT))/κ²`.
* `vasicekYield_eq_nssSlope` — the Vasicek zero yield in slope factors, for `κ, T > 0`.
* `vasicekYield_zeroVol_eq_nssYield` — at `σ = 0`, the yield is the Nelson–Siegel curve
  `nssYield θ (r₀ − θ) 0 0 κ⁻¹ l₂`.
* `tendsto_vasicekYield_nhdsGT_zero` — `y(T) → r₀` as `T → 0⁺`.
* `tendsto_vasicekYield_atTop` — `y(T) → θ − σ²/(2κ²)` as `T → ∞`.

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  §3.2.1
* [C. R. Nelson and A. F. Siegel, *Parsimonious modeling of yield curves*][NelsonSiegel1987]
* [O. Vasicek, *An equilibrium characterization of the term structure*][Vasicek1977]

## Tags

Vasicek model, Nelson–Siegel curve, zero yield, term structure, slope factor, long rate, JEL E43,
MSC 91G30
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-- **The Nelson–Siegel slope factor is the Vasicek loading per unit maturity**:
`vasicekBondB κ τ / τ = nssSlope (κ τ)`, both being `(1 − e^{−κτ})/(κτ)`. The two definitions
were written independently, in `VasicekBondPrice` and `NelsonSiegelSvensson`. -/
theorem vasicekBondB_div_eq_nssSlope (κ τ : ℝ) : vasicekBondB κ τ / τ = nssSlope (κ * τ) := by
  rw [vasicekBondB, nssSlope, div_div]

/-- The Vasicek variance per unit maturity in slope factors:
`V(T)/T = (1 − 2 s(κT) + s(2κT))/κ²`, for `κ, T ≠ 0`. -/
theorem vasicekBondV_div_eq_nssSlope {κ T : ℝ} (hκ : κ ≠ 0) (hT : T ≠ 0) :
    vasicekBondV κ T / T = (1 - 2 * nssSlope (κ * T) + nssSlope (2 * κ * T)) / κ ^ 2 := by
  simp only [vasicekBondV, nssSlope]
  field_simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The Vasicek zero yield in Nelson–Siegel slope factors.** For `κ > 0` and maturity
`T > 0`, the continuously compounded yield of the Vasicek bond price
`P(0,T) = 𝔼[exp(−∫₀ᵀ r_s ds)]` (`vasicekBondPrice_eq`) is
`(θ − σ²/(2κ²)) + (r₀ − θ + σ²/κ²)·s(κT) − (σ²/(2κ²))·s(2κT)`, with `s = nssSlope`. -/
theorem vasicekYield_eq_nssSlope (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (T : ℝ≥0) (hT : 0 < (T : ℝ)) :
    -Real.log (∫ ω, Real.exp (-(vasicekIntegratedRate hB r₀ θ σ hκ T ω)) ∂μ) / T
      = θ - σ ^ 2 / (2 * κ ^ 2) + (r₀ - θ + σ ^ 2 / κ ^ 2) * nssSlope (κ * T)
        - σ ^ 2 / (2 * κ ^ 2) * nssSlope (2 * κ * T) := by
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hT0 : (T : ℝ) ≠ 0 := hT.ne'
  rw [vasicekBondPrice_eq hB r₀ θ σ hκ T, Real.log_exp]
  simp only [vasicekIntegratedMean, vasicekBondB, vasicekBondV, nssSlope]
  field_simp
  ring

/-- **With zero volatility the Vasicek curve is a Nelson–Siegel curve**: level `θ`, slope
`r₀ − θ`, no curvature, decay `κ⁻¹` (the Svensson decay `l₂` is unused, its loading being
zero). -/
theorem vasicekYield_zeroVol_eq_nssYield (hB : IsPreBrownianReal B μ) (r₀ θ : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (T : ℝ≥0) (hT : 0 < (T : ℝ)) (l₂ : ℝ) :
    -Real.log (∫ ω, Real.exp (-(vasicekIntegratedRate hB r₀ θ 0 hκ T ω)) ∂μ) / T
      = nssYield θ (r₀ - θ) 0 0 κ⁻¹ l₂ T := by
  rw [vasicekYield_eq_nssSlope hB r₀ θ 0 hκ T hT, nssYield, div_inv_eq_mul, mul_comm (T : ℝ) κ]
  ring

/-- `T ↦ c·T` sends `T → 0⁺` (in `ℝ≥0`) to `x → 0` through nonzero values, for `c ≠ 0`. -/
theorem tendsto_const_mul_coe_nhdsNE {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun T : ℝ≥0 ↦ c * (T : ℝ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Tendsto (fun T : ℝ≥0 ↦ c * (T : ℝ)) (𝓝 0) (𝓝 (c * ((0 : ℝ≥0) : ℝ))) :=
      (continuous_const.mul NNReal.continuous_coe).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with T hT
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact mul_ne_zero hc (NNReal.coe_pos.mpr hT).ne'

/-- **The short end of the Vasicek curve is the short rate**: `y(T) → r₀` as `T → 0⁺`, from
`s(x) → 1` as `x → 0`. -/
theorem tendsto_vasicekYield_nhdsGT_zero (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {κ : ℝ}
    (hκ : 0 < κ) :
    Tendsto (fun T : ℝ≥0 ↦
        -Real.log (∫ ω, Real.exp (-(vasicekIntegratedRate hB r₀ θ σ hκ T ω)) ∂μ) / T)
      (𝓝[>] 0) (𝓝 r₀) := by
  have hlim : Tendsto (fun T : ℝ≥0 ↦ θ - σ ^ 2 / (2 * κ ^ 2)
        + (r₀ - θ + σ ^ 2 / κ ^ 2) * nssSlope (κ * T) - σ ^ 2 / (2 * κ ^ 2) * nssSlope (2 * κ * T))
      (𝓝[>] 0)
      (𝓝 (θ - σ ^ 2 / (2 * κ ^ 2) + (r₀ - θ + σ ^ 2 / κ ^ 2) * 1 - σ ^ 2 / (2 * κ ^ 2) * 1)) :=
    (tendsto_const_nhds.add ((tendsto_nssSlope_nhdsNE_zero.comp
      (tendsto_const_mul_coe_nhdsNE hκ.ne')).const_mul _)).sub
      ((tendsto_nssSlope_nhdsNE_zero.comp
        (tendsto_const_mul_coe_nhdsNE (mul_ne_zero two_ne_zero hκ.ne'))).const_mul _)
  rw [show θ - σ ^ 2 / (2 * κ ^ 2) + (r₀ - θ + σ ^ 2 / κ ^ 2) * 1 - σ ^ 2 / (2 * κ ^ 2) * 1
    = r₀ by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with T hT
  exact (vasicekYield_eq_nssSlope hB r₀ θ σ hκ T (NNReal.coe_pos.mpr hT)).symm

/-- **The Vasicek long rate**: `y(T) → θ − σ²/(2κ²)` as `T → ∞`, from `s(x) → 0` as
`x → ∞`. -/
theorem tendsto_vasicekYield_atTop (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {κ : ℝ}
    (hκ : 0 < κ) :
    Tendsto (fun T : ℝ≥0 ↦
        -Real.log (∫ ω, Real.exp (-(vasicekIntegratedRate hB r₀ θ σ hκ T ω)) ∂μ) / T)
      atTop (𝓝 (θ - σ ^ 2 / (2 * κ ^ 2))) := by
  have hT : Tendsto (fun T : ℝ≥0 ↦ (T : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hlim : Tendsto (fun T : ℝ≥0 ↦ θ - σ ^ 2 / (2 * κ ^ 2)
        + (r₀ - θ + σ ^ 2 / κ ^ 2) * nssSlope (κ * T) - σ ^ 2 / (2 * κ ^ 2) * nssSlope (2 * κ * T))
      atTop
      (𝓝 (θ - σ ^ 2 / (2 * κ ^ 2) + (r₀ - θ + σ ^ 2 / κ ^ 2) * 0 - σ ^ 2 / (2 * κ ^ 2) * 0)) :=
    (tendsto_const_nhds.add ((tendsto_nssSlope_atTop.comp
      (hT.const_mul_atTop hκ)).const_mul _)).sub
      ((tendsto_nssSlope_atTop.comp (hT.const_mul_atTop (mul_pos two_pos hκ))).const_mul _)
  rw [mul_zero, mul_zero, add_zero, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT0
  exact (vasicekYield_eq_nssSlope hB r₀ θ σ hκ T (NNReal.coe_pos.mpr hT0)).symm

end MathFin
