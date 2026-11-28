/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.SDE.SDEExistence
public import LeanPool.MathFin.Probability.Brownian.Ito.DriftProcessModification

/-! # The Picard fixed point, sliced into paths (SDE existence, the pathwise bridge)

`SDEExistence` produced the solution of `dX = b(X)dt + σ(X)dB` as the **abstract** fixed point
`picardSolution ∈ E = Lp ℝ 2 (trimMeasure T)` of the Picard map
`Φ(X) = η + driftProcessAssembled(b∘X) + itoProcessAssembled(σ∘X)`, under the short-horizon
contraction condition `T·L_b + √T·L_σ < 1`. That fixed point is an `L²` equivalence class on the
space–time product.

This file slices the fixed-point equation `X = Φ(X)`, which holds in `E`, into a decomposition of
representatives: `X(t, ω) = η(t, ω) + (drift limit)_t(ω) + (Itô modification)_t(ω)` for almost
every `(t, ω)` with respect to `trimMeasure T` (`sde_pathwise_decomposition`). The two analytic
terms are given by processes defined at every `(t, ω)`:
* the **drift** `driftProcessAssembled(b∘X)` has `coeFn` a.e. equal to the pointwise `limUnder`
  process `driftContinuousMod(b∘X)` (`driftProcessAssembled_coeFn`, `DriftProcessModification`);
* the **Itô term** `itoProcessAssembled(σ∘X)` is by construction the class of the continuous
  modification `itoContinuousMod(σ∘X)` (`ItoProcessPredictable`).

For each `t ≤ T`, the drift term is almost surely the time integral
`∫_{(0,t]} (b∘X)(s, ω) ds` of a representative of the class `b∘X = lipComp b X`
(`sde_pathwise_drift_eq_setIntegral`). A representative of a class is determined only up to a
null set of `(s, ω)`, and the per-path identity with `∫₀ᵗ b(X_s(ω)) ds` for a chosen
representative of `X` is not proved here. Nor is it proved that `X` has a representative that is
a continuous adapted process satisfying the integral equation at every `t` almost surely, which
is the textbook notion of a strong solution.

## Main results

* `sde_pathwise_decomposition`: the `E`-fixed point `picardSolution` decomposes, for almost every
  `(t, ω)` under `trimMeasure T`, as `η` plus the drift term plus the Itô modification term.
* `sde_pathwise_drift_eq_setIntegral`: for every `t ≤ T`, the drift term of that decomposition is
  the time integral of `b ∘ X` over `[0, t]`.

## References

* [B. Oksendal, *Stochastic Differential Equations*][Oksendal2003], Thm 5.2.1
* [Y. F. Saporito, *Stochastic Processes*][Saporito], Thm 8.2.5

## Tags

stochastic differential equation, strong solution, Picard fixed point, pathwise decomposition,
drift and Itô term, continuous modification, MSC 60H10, MSC 60H05
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace SDEExistence
open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral
  ItoIntegralProcessContinuousModification

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}

/-- **The Picard fixed point, sliced into paths.** The abstract `E`-fixed point `picardSolution`
decomposes, almost everywhere for `trimMeasure T` on the space–time product, into its initial
condition, a drift process and an Itô process:
`X(t, ω) = η(t, ω) + driftContinuousMod(b∘X)_t(ω) + itoContinuousMod(σ∘X)_t(ω)`.
The drift process is the pointwise `limUnder` of elementary drift integrals
(`driftProcessAssembled_coeFn`); the Itô process is the continuous modification of `(σ∘X) ● B`
(`itoProcessAssembled` is defined from `itoContinuousMod`). The fixed-point equation `X = Φ(X)`
holds in `E`; taking `coeFn` through `Lp.coeFn_add` and the two realization identities slices it
into this form. -/
theorem sde_pathwise_decomposition (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hc : (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ < 1) :
    ⇑(picardSolution hB T hBmeas hBcont hb hσ η_E hc)
      =ᵐ[trimMeasure (μ := μ) T hBmeas]
      fun z ↦ ⇑η_E z
        + Function.uncurry (driftContinuousMod T hBmeas
            (lipComp T hBmeas b Lb hb (picardSolution hB T hBmeas hBcont hb hσ η_E hc))) z
        + Function.uncurry (itoContinuousMod T hBmeas
            (lipComp T hBmeas σ Lσ hσ (picardSolution hB T hBmeas hBcont hb hσ η_E hc))) z := by
  set X := picardSolution hB T hBmeas hBcont hb hσ η_E hc
  -- X is a fixed point of the Picard map, which is definitionally the sum of the three terms
  have hfix : picardMap hB T hBmeas hBcont hb hσ η_E X = X :=
    (picardMap_contractingWith hB T hBmeas hBcont hb hσ η_E hc).fixedPoint_isFixedPt
  have hX : X = η_E + driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb X)
                    + itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ X) :=
    hfix.symm
  -- the two pathwise-realization identities
  have hdrift := driftProcessAssembled_coeFn (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb X)
  have hito : ⇑(itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ X))
      =ᵐ[trimMeasure (μ := μ) T hBmeas]
        Function.uncurry (itoContinuousMod T hBmeas (lipComp T hBmeas σ Lσ hσ X)) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ X)).coeFn_toLp
  -- slice the fixed-point equation through coeFn (rewrite only the standalone ⇑X, not the X in
  -- lipComp)
  filter_upwards [Lp.coeFn_add
      (η_E + driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb X))
      (itoProcessAssembled hB T hBmeas hBcont (lipComp T hBmeas σ Lσ hσ X)),
    Lp.coeFn_add η_E (driftProcessAssembled (μ := μ) T hBmeas (lipComp T hBmeas b Lb hb X)),
    hdrift, hito] with z h1 h2 hd hi
  conv_lhs => rw [hX]
  simp only [h1, h2, hd, hi, Pi.add_apply]

/-- **The drift term is a time integral.** For every `t ≤ T`, the drift term
`driftContinuousMod(b∘X)` of `sde_pathwise_decomposition` is, almost surely, the time integral
`∫_{(0,t]} (b∘X)(s, ω) ds` of the representative `⇑(lipComp b X)` of the class `b∘X`
(`driftContinuousMod_eq_setIntegral` applied to `lipComp b X`). The per-path identity with
`∫₀ᵗ b(X_s(ω)) ds` for a chosen representative of `X` is not stated. -/
theorem sde_pathwise_drift_eq_setIntegral (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    {b σ : ℝ → ℝ} {Lb Lσ : ℝ≥0} (hb : LipschitzWith Lb b) (hσ : LipschitzWith Lσ σ)
    (η_E : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas))
    (hc : (T : ℝ) * Lb + Real.sqrt (T : ℝ) * Lσ < 1) {t : ℝ≥0} (ht : t ≤ T) :
    ∀ᵐ ω ∂μ, driftContinuousMod T hBmeas
        (lipComp T hBmeas b Lb hb (picardSolution hB T hBmeas hBcont hb hσ η_E hc)) t ω
      = ∫ s in Set.Ioc (0 : ℝ≥0) t,
        ⇑(lipComp T hBmeas b Lb hb (picardSolution hB T hBmeas hBcont hb hσ η_E hc)) (s, ω)
            ∂timeMeasure :=
  driftContinuousMod_eq_setIntegral T hBmeas _ ht

end SDEExistence
end MathFin
