/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Credit.CVA
public import LeanPool.MathFin.Risk.GaussianValueAtRisk

/-!
# Potential future exposure and netting subadditivity

Two risk measures of the CVA exposure process (`V : ℝ → Ω₁ → ℝ` an exposure process, `ν` its
measure): PFE, a quantile of the exposure (through `MathFin.valueAtRisk`), and netting
subadditivity. The expectations of the exposure that price the adjustments, EE and ENE, are with
the adjustments they price (`Models/Credit/CVA.lean`, `Models/Credit/DVA.lean`).

* `potentialFutureExposure`: `PFE_α(s) = VaR_α(V_s⁺)`, the `α`-quantile of the exposure `V_s⁺`.
  `potentialFutureExposure_eq_max` gives `PFE_α(s) = max (VaR_α(V_s)) 0`, since `x ↦ max x 0` is
  monotone and continuous (`valueAtRisk_comp`). `potentialFutureExposure_of_hasLaw_gaussianReal`
  is the closed form `max (m + √v Φ⁻¹(α)) 0` for `V_s ~ N(m, v)`, and
  `potentialFutureExposure_gaussian` its instance at the exposure model `V_s = m + σ√s Z` of
  `CVA.cva_gaussian`.
* `integral_posPart_finsetSum_le`: netting reduces exposure. For a finite family
  `V : ι → Ω → ℝ` of integrable exposures on a common measure, `E[(Σᵢ Vᵢ)⁺] ≤ Σᵢ E[Vᵢ⁺]`, from
  the pointwise subadditivity of `max (·) 0` (`max_add_add_le_max_add_max` with the second pair
  at `0`), summed by `le_sum_of_subadditive`, then integrated.

## Main definitions

* `potentialFutureExposure`: `PFE_α(s)`, the `α`-level value-at-risk of the exposure `V_s⁺`.

## Main results

* `potentialFutureExposure_eq_max`: `PFE_α(s) = max (VaR_α(V_s)) 0` for `α ∈ (0, 1)`.
* `potentialFutureExposure_gaussian`: for `V_s = m + σ√s Z` with `Z ~ N(0, 1)`, `σ ≥ 0` and
  `α ∈ (0, 1)`, `PFE_α(s) = max (gaussianVaR m (σ√s) (Φ⁻¹ α)) 0`.
* `integral_posPart_finsetSum_le`: netting reduces exposure, `E[(∑ᵢ Vᵢ)⁺] ≤ ∑ᵢ E[Vᵢ⁺]` for
  integrable `Vᵢ`.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull] (CVA/exposure chapter): EE, ENE,
  PFE.
* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management*][McNeilFreyEmbrechts]
  (netting of credit exposures).

## Tags

expected negative exposure, potential future exposure, netting, counterparty credit risk,
CVA exposure, expected exposure, MSC 91G40, MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin.CVA

open MeasureTheory Real ProbabilityTheory Set
open scoped NNReal

variable {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {ν : Measure Ω₁}

/-- **Potential future exposure**: the `α`-level value-at-risk of the exposure `V_s⁺` at time
`s`, `PFE_α(s) = VaR_α(V_s⁺)`. -/
noncomputable def potentialFutureExposure (V : ℝ → Ω₁ → ℝ) (ν : Measure Ω₁) (s α : ℝ) : ℝ :=
  MathFin.valueAtRisk (fun ω ↦ max (V s ω) 0) ν α

/-- **PFE is the positive part of the VaR of `V_s`**: `VaR_α(V_s⁺) = max (VaR_α(V_s)) 0`, since
`x ↦ max x 0` is monotone and continuous (`valueAtRisk_comp`). -/
theorem potentialFutureExposure_eq_max [IsProbabilityMeasure ν] {V : ℝ → Ω₁ → ℝ} {s α : ℝ}
    (hV : AEMeasurable (V s) ν) (hα : α ∈ Ioo 0 1) :
    potentialFutureExposure V ν s α = max (MathFin.valueAtRisk (V s) ν α) 0 :=
  MathFin.valueAtRisk_comp (h := fun x ↦ max x 0) hV (monotone_id.max monotone_const)
    (continuous_id.max continuous_const).lowerSemicontinuous hα

/-- **Gaussian PFE**: for `V_s ~ N(m, v)` and `α ∈ (0,1)`,
`PFE_α(s) = max (m + √v Φ⁻¹(α)) 0`, the positive part of the Gaussian value-at-risk. -/
theorem potentialFutureExposure_of_hasLaw_gaussianReal {V : ℝ → Ω₁ → ℝ} {s α m : ℝ} {v : ℝ≥0}
    (hV : HasLaw (V s) (gaussianReal m v) ν) (hα : α ∈ Ioo 0 1) :
    potentialFutureExposure V ν s α = max (gaussianVaR m √(v : ℝ) (PhiInv α)) 0 := by
  have := hV.isProbabilityMeasure_iff.2 inferInstance
  rw [potentialFutureExposure_eq_max hV.aemeasurable hα,
    MathFin.valueAtRisk_of_hasLaw_gaussianReal hV hα]

/-- **Gaussian PFE in the exposure model of `CVA.cva_gaussian`**: for `Z ~ N(0,1)`, `σ ≥ 0`,
`α ∈ (0,1)` and `V_s = m + σ√s Z`, `PFE_α(s) = max (m + σ√s Φ⁻¹(α)) 0`. -/
theorem potentialFutureExposure_gaussian {Z : Ω₁ → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) ν) (m σ s α : ℝ) (hσ : 0 ≤ σ)
    (hα : α ∈ Ioo 0 1) :
    potentialFutureExposure (fun s ω ↦ m + σ * √s * Z ω) ν s α
      = max (gaussianVaR m (σ * √s) (PhiInv α)) 0 := by
  have hL : HasLaw (fun ω ↦ m + σ * √s * Z ω)
      (gaussianReal m (NNReal.mk ((σ * √s) ^ 2) (sq_nonneg _))) ν := by
    simpa using gaussianReal_const_add (gaussianReal_const_mul hZ (σ * √s)) m
  rw [potentialFutureExposure_of_hasLaw_gaussianReal (V := fun s ω ↦ m + σ * √s * Z ω) hL hα,
    NNReal.coe_mk, Real.sqrt_sq (by positivity)]

/-- **Netting reduces exposure**: `E[(∑ᵢ Vᵢ)⁺] ≤ ∑ᵢ E[Vᵢ⁺]` for a finite family of integrable
real-valued exposures on a common measure. Proved via pointwise subadditivity of `max (·) 0`
(`max_add_add_le_max_add_max`), summed (`le_sum_of_subadditive`), then integrated
(`integral_mono`, `integral_finsetSum`, `Integrable.pos_part`). -/
theorem integral_posPart_finsetSum_le {ι : Type*} (s : Finset ι) {V : ι → Ω₁ → ℝ}
    (hV : ∀ i ∈ s, Integrable (V i) ν) :
    ∫ ω, max (∑ i ∈ s, V i ω) 0 ∂ν ≤ ∑ i ∈ s, ∫ ω, max (V i ω) 0 ∂ν :=
  (integral_mono (integrable_finsetSum s hV).pos_part
    (integrable_finsetSum s fun i hi ↦ (hV i hi).pos_part) fun ω ↦
      Finset.le_sum_of_subadditive (fun x ↦ max x 0) (max_self (0:ℝ)).le (fun a b ↦ by
        simpa using max_add_add_le_max_add_max (a := a) (b := b) (c := 0) (d := 0)) s
        fun i ↦ V i ω).trans_eq
    (integral_finsetSum s fun i hi ↦ (hV i hi).pos_part)

end MathFin.CVA
