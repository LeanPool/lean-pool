/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.HullWhiteCalibration
public import LeanPool.MathFin.Models.Rates.VasicekBondPriceAt

/-!
# The Hull–White bond price at a time `t > 0`

`Models/Rates/HullWhiteCalibration.lean` prices the zero-coupon bond at time `0`,
`P(0, T) = A(T)·exp(−B(T) r₀)` with the forcing `θ` in `A`. This file prices it at a later time
`t`, given the information `𝓕_t = σ(B_s : s ≤ t)` of the driving Brownian motion:

  `𝔼[exp(−∫₀ᵀ r) | 𝓕_t] = exp(−∫₀ᵗ r)·A_t(T − t)·exp(−B(T − t)·r_t)`   almost surely,

where `A_t = bondA (θ(t + ·))` is the time-`0` coefficient of the forcing seen from `t`. It is the
proof of `vasicekBondPrice_condExp` with a different mean identity: both are instances of
`condExp_exp_neg_integratedRate`, which takes the identity
`M(t) − M(T) = −c − B(T − t)·m` between the deterministic parts as its only model input. For the
Hull–White model it is `integratedMean_sub`:

  `∫₀ᵀ α − ∫₀ᵗ α = B(T − t)·α(t) + ∫_t^T θ(s) B(T − s) ds`,

from the splitting `B(T − s) = B(t − s) + e^{−κ(t−s)} B(T − t)` of the integrated kernel.

## Main results

* `integratedMean_sub` — the increment of the integrated deterministic part.
* `bondA_shift` — the coefficient `A_t` is `exp(−∫_t^T θ(s) B(T − s) ds + σ²V(T − t)/2)`.
* `bondRate_condExp` — the conditional discount factor, affine in `r_t`.

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  section 3.3.1
* [J. Hull and A. White, *Pricing interest-rate-derivative securities*][HullWhite1990]

## Tags

Hull–White model, conditional bond price, affine term structure, time-dependent drift, short rate,
zero-coupon bond, MSC 91G30, JEL E43
-/

@[expose] public section

namespace MathFin.HullWhite

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private lemma continuous_theta_bondB (θ : ℝ → ℝ) (hθ : Continuous θ) (κ T : ℝ) :
    Continuous fun s : ℝ ↦ θ s * vasicekBondB κ (T - s) := by
  unfold vasicekBondB; fun_prop

/-- **The increment of the integrated deterministic part.** From `t` to `T`, the integrated mean
grows by the mean sensitivity `B(T − t)` times the short-rate mean `α(t)` at `t`, plus the forcing
`θ` seen over `[t, T]`: `∫₀ᵀ α − ∫₀ᵗ α = B(T − t)·α(t) + ∫_t^T θ(s) B(T − s) ds`. -/
lemma integratedMean_sub (θ : ℝ → ℝ) (hθ : Continuous θ) (κ r₀ t T : ℝ) (hκ : κ ≠ 0) :
    integratedMean θ κ r₀ T - integratedMean θ κ r₀ t
      = vasicekBondB κ (T - t) * deterministic θ κ r₀ t
        + ∫ s in t..T, θ s * vasicekBondB κ (T - s) := by
  have hexp (s : ℝ) : Real.exp (-(κ * (T - s)))
      = Real.exp (-(κ * (t - s))) * Real.exp (-(κ * (T - t))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpt (s : ℝ) : θ s * vasicekBondB κ (T - s) = θ s * vasicekBondB κ (t - s)
      + (vasicekBondB κ (T - t) * Real.exp (-(κ * t))) * (Real.exp (κ * s) * θ s) := by
    have h2 : Real.exp (-(κ * (t - s))) = Real.exp (-(κ * t)) * Real.exp (κ * s) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [vasicekBondB, hexp s, h2]
    field_simp
    ring
  have hcont : Continuous fun s : ℝ ↦ Real.exp (κ * s) * θ s := by fun_prop
  have h0 : ∫ s in (0 : ℝ)..t, θ s * vasicekBondB κ (T - s)
      = (∫ s in (0 : ℝ)..t, θ s * vasicekBondB κ (t - s))
        + (vasicekBondB κ (T - t) * Real.exp (-(κ * t)))
          * ∫ s in (0 : ℝ)..t, Real.exp (κ * s) * θ s := by
    rw [intervalIntegral.integral_congr (fun s _ ↦ hpt s),
      intervalIntegral.integral_add ((continuous_theta_bondB θ hθ κ t).intervalIntegrable 0 t)
        ((hcont.const_mul _).intervalIntegrable 0 t),
      intervalIntegral.integral_const_mul]
  have hT : Real.exp (-(κ * T)) = Real.exp (-(κ * t)) * Real.exp (-(κ * (T - t))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hBT : vasicekBondB κ T - vasicekBondB κ t
      = Real.exp (-(κ * t)) * vasicekBondB κ (T - t) := by
    simp only [vasicekBondB, hT]; field_simp; ring
  rw [integratedMean_eq θ hθ κ r₀ T hκ, integratedMean_eq θ hθ κ r₀ t hκ,
    ← intervalIntegral.integral_add_adjacent_intervals
      ((continuous_theta_bondB θ hθ κ T).intervalIntegrable 0 t)
      ((continuous_theta_bondB θ hθ κ T).intervalIntegrable t T), h0]
  simp only [deterministic]
  linear_combination r₀ * hBT

/-- **The coefficient `A` seen from `t`.** The time-`0` coefficient `A` of the forcing shifted to
start at `t`, at the remaining maturity `T − t`, is the exponent of the forcing over `[t, T]`. -/
lemma bondA_shift (θ : ℝ → ℝ) (σ κ t T : ℝ) :
    bondA (fun s ↦ θ (t + s)) σ κ (T - t)
      = Real.exp (-(∫ s in t..T, θ s * vasicekBondB κ (T - s))
          + σ ^ 2 * vasicekBondV κ (T - t) / 2) := by
  have h := intervalIntegral.integral_comp_add_left (a := 0) (b := T - t)
    (fun s ↦ θ s * vasicekBondB κ (T - s)) t
  rw [add_zero, add_sub_cancel] at h
  rw [bondA]
  simp only [sub_sub]
  rw [h]

variable [IsProbabilityMeasure μ]

/-- **The Hull–White bond price at time `t`.** Given the information `𝓕_t` of the driving Brownian
motion, for continuous forcing `θ` the discount factor `exp(−∫₀ᵀ r)` along the integrated
Hull–White rate has conditional mean

  `𝔼[exp(−∫₀ᵀ r) | 𝓕_t] = exp(−∫₀ᵗ r)·A_t(T − t)·exp(−B(T − t)·r_t)`

almost surely, with `r_t` the short rate in its Wiener representation (`integratedRate`) and
`A_t = bondA (θ(t + ·))`, the coefficient of the time-`0` price (`bondPrice_affine`) of the forcing
shifted to `t`, at the remaining maturity. The measure is read as the pricing measure. -/
theorem bondRate_condExp (hB : IsPreBrownianReal B μ) (hBm : ∀ s, Measurable (B s))
    {θ : ℝ → ℝ} (hθ : Continuous θ) (κ σ r₀ : ℝ) (hκ : 0 < κ) {t T : ℝ≥0} (htT : t ≤ T) :
    μ[fun ω ↦ Real.exp (-bondRate hB θ κ σ r₀ hκ T ω)
        | Filtration.natural B (fun s ↦ (hBm s).stronglyMeasurable) t]
      =ᵐ[μ] fun ω ↦ Real.exp (-bondRate hB θ κ σ r₀ hκ t ω)
        * (bondA (fun s ↦ θ ((t : ℝ) + s)) σ κ (((T - t : ℝ≥0) : ℝ))
          * Real.exp (-(vasicekBondB κ ((T - t : ℝ≥0) : ℝ)
            * integratedRate hB θ κ σ r₀ hκ t ω))) := by
  have hm := integratedMean_sub θ hθ κ r₀ t T hκ.ne'
  have key := condExp_exp_neg_integratedRate hB hBm σ hκ htT
    (M_t := integratedMean θ κ r₀ t) (M_T := integratedMean θ κ r₀ T)
    (c := ∫ s in (t : ℝ)..T, θ s * vasicekBondB κ (T - s)) (m := deterministic θ κ r₀ t)
    (by rw [NNReal.coe_sub htT]; linear_combination -hm)
  rw [NNReal.coe_sub htT] at key ⊢
  rw [bondA_shift]
  exact key

/-- **The Hull–White coefficient at constant forcing is Vasicek's**: with `θ ≡ κ·θ_v` the affine
coefficient `A(τ) = exp(−∫₀^τ θ B(τ − s) ds + σ²V(τ)/2)` is `vasicekBondA θ_v σ κ τ`, since
`∫₀^τ B(τ − s) ds = (τ − B(τ))/κ` (`integral_vasicekIntegratedKernel`). -/
lemma bondA_const (θ σ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (τ : ℝ) :
    bondA (fun _ ↦ κ * θ) σ κ τ = vasicekBondA θ σ κ τ := by
  have hmass : ∫ s in (0 : ℝ)..τ, vasicekBondB κ (τ - s) = (τ - vasicekBondB κ τ) / κ :=
    integral_vasicekIntegratedKernel κ τ hκ
  rw [bondA, vasicekBondA, intervalIntegral.integral_const_mul, hmass]
  congr 2
  field_simp

omit [IsProbabilityMeasure μ] in
/-- **The Hull–White short rate at constant forcing is Vasicek's**: with `θ ≡ κ·θ_v` the short rate
`α(t) + σ∫₀ᵗ e^{−κ(t−u)} dB_u` is the Vasicek one, `vasicekSDEMean + vasicekDiffusionTerm`. -/
lemma integratedRate_const (hB : IsPreBrownianReal B μ) (r₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (t : ℝ≥0) (ω : Ω) :
    integratedRate hB (fun _ ↦ κ * θ) κ σ r₀ hκ t ω
      = vasicekSDEMean r₀ θ κ t + vasicekDiffusionTerm hB κ σ hκ.le t ω := by
  rw [integratedRate, vasicekDiffusionTerm, deterministic_const _ _ _ _ hκ.ne',
    mul_div_cancel_left₀ _ hκ.ne', vasicekSDEMean_eq_deterministic]

end MathFin.HullWhite
