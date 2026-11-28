/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Credit.CVA
public import LeanPool.MathFin.Probability.Gaussian.GaussianMoments

/-!
# Collateralized exposure under a Brownian-driven process

Collateral is the exposure process itself evaluated `Δ` earlier, `C t := V (t - Δ)`: a two-way
CSA with zero threshold and zero minimum transfer amount, posted with a lag `Δ` (the margin
period of risk).

* `collateralizedExposure V Δ t ω = max (V t ω - V (t - Δ) ω) 0`, time indexed by `ℝ≥0` to match
  `IsPreBrownianReal`. The lag `t - Δ` is `ℝ≥0` truncated subtraction, so for `Δ > t` it is `0`
  and `C_t` is `V_0`; the theorem below assumes `Δ ≤ t`.
* `collateralizedExposure_brownian_gaussian`: for `V t = m + σ B t` with `B` a pre-Brownian
  motion (`IsPreBrownianReal`), `0 < Δ ≤ t` and `σ > 0`, the expected collateralized exposure is
  `E[(V_t - V_{t-Δ})⁺] = σ√Δ · φ(0)`. The level `m` drops out of the increment
  `V_t - V_{t-Δ} = σ (B_t - B_{t-Δ})`, whose law comes from the Brownian finite-dimensional laws
  (`MathFin.hasLaw_increment`); standardized to `Z ~ N(0,1)` by `hasLaw_sub_div_of_gaussianReal`,
  it is `σ√Δ · Z`, and `CVA.expectedExposure_gaussian` at mean `0` gives the answer, the density
  `φ(0)` scaled by the volatility of the increment.

## Main definitions

* `collateralizedExposure`: the exposure `max (V t − V (t − Δ)) 0` at time `t` when the
  collateral is the process itself lagged by `Δ`, with `ℝ≥0` truncated subtraction in `t − Δ`.

## Main results

* `collateralizedExposure_brownian_gaussian`: for `V t = m + σ B t` with `B` a pre-Brownian
  motion, `σ > 0` and `0 < Δ ≤ t`, `E[(V_t − V_{t−Δ})⁺] = σ√Δ · φ(0)`, with `φ(0)` the standard
  Gaussian density at `0`. The level `m` drops out.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull] (collateralized exposure / CSAs).

## Tags

collateralized exposure, credit support annex, margin period of risk, counterparty credit risk,
Brownian exposure, CVA, MSC 91G40, MSC 60J65, JEL G32
-/

@[expose] public section

namespace MathFin.CVA

open MeasureTheory Real ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Collateralized exposure at time `t` with lag `Δ`: `max(V_t - C_t, 0)` with the lagged
collateral `C_t := V_{t-Δ}`, the same process `Δ` earlier. -/
noncomputable def collateralizedExposure (V : ℝ≥0 → Ω → ℝ) (Δ t : ℝ≥0) (ω : Ω) : ℝ :=
  max (V t ω - V (t - Δ) ω) 0

/-- **Collateralized exposure under a Brownian-driven process, in closed form**: for
`V_t = m + σ B_t` with `B` a pre-Brownian motion, `σ > 0` and `0 < Δ ≤ t`,
`E[(V_t - V_{t-Δ})⁺] = σ√Δ · φ(0)`; the level `m` drops out. The law of the increment comes from
`MathFin.hasLaw_increment`. -/
theorem collateralizedExposure_brownian_gaussian [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (m σ : ℝ) (hσ : 0 < σ) {Δ t : ℝ≥0} (hΔpos : 0 < Δ)
    (hΔt : Δ ≤ t) :
    ∫ ω, collateralizedExposure (fun t ω ↦ m + σ * B t ω) Δ t ω ∂P
      = σ * √(Δ : ℝ) * gaussianPDFReal 0 1 0 := by
  have hΔ : (0 : ℝ) < Δ := hΔpos
  have hinc : HasLaw (fun ω ↦ B t ω - B (t - Δ) ω) (gaussianReal 0 Δ) P := by
    simpa [tsub_tsub_cancel_of_le hΔt] using hasLaw_increment hB (tsub_le_self (a := t) (b := Δ))
  have hZ : HasLaw (fun ω ↦ (B t ω - B (t - Δ) ω) / √(Δ : ℝ)) (gaussianReal 0 1) P := by
    simpa using hasLaw_sub_div_of_gaussianReal hinc (Real.sqrt_pos.mpr hΔ) (Real.sq_sqrt hΔ.le).symm
  have hΔne : √(Δ : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hΔ).ne'
  have hpt (ω : Ω) : collateralizedExposure (fun t ω ↦ m + σ * B t ω) Δ t ω
      = max (0 + σ * √(Δ : ℝ) * ((B t ω - B (t - Δ) ω) / √(Δ : ℝ))) 0 := by
    rw [collateralizedExposure, zero_add, mul_assoc, mul_div_cancel₀ _ hΔne]
    congr 1
    ring
  simp_rw [hpt]
  rw [expectedExposure_gaussian hZ hσ hΔ]
  simp

end MathFin.CVA
