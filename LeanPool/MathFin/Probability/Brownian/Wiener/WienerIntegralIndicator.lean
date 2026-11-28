/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralL2

/-!
# The Wiener integral of a step indicator is the increment

The Wiener isometry `wienerIntegralLp B hB T : L²([0,T]) →L[ℝ] L²(μ)` is built as
`(wienerAssembly).extendOfNorm (stepAssembly)` — the norm-continuous extension of the
map that sends the step indicator `𝟙_{(s,t]}` to the Brownian increment `B_t − B_s`.
This file records the *defining* identity that the extension actually realizes on those
generators,

  `wienerIntegralLp B hB T (stepIndicatorLp T i) = wienerIncrementLp B hB i`,

i.e. `∫ 𝟙_{(s,t]} dB = B_t − B_s`. It is immediate from
`LinearMap.extendOfNorm_eq` (the extension agrees with the base map on the dense
subspace) applied to the single-basis coefficient `Finsupp.single i 1`, since both
assembly maps are `Finsupp.linearCombination` of their respective generators. This is
the piece that lets a finite sum of Brownian values `∑ᵢ B_{tᵢ}` be read as a single
Wiener integral of the deterministic step kernel `∑ᵢ 𝟙_{(0,tᵢ]}` — the route the
geometric-average Asian option (and any BM-value basket) takes to its Gaussian law.

## Main results

* `wienerIntegralLp_stepIndicator`: the Wiener integral of a step indicator is the Brownian
  increment, `∫ 𝟙_{(lo, hi]} dB = B_hi − B_lo`.

## Tags

Wiener integral, Brownian increment, step indicator, isometry extension, geometric Asian option,
step kernel, MSC 60H05, MSC 60J65
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal
open WienerIntegralL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The Wiener integral of a step indicator is the Brownian increment**:
`∫ 𝟙_{(lo,hi]} dB = B_hi − B_lo`. The extension `wienerIntegralLp` agrees with the base
assembly on the dense span of step indicators (`LinearMap.extendOfNorm_eq`), and on the
single-basis coefficient `stepAssembly (single i 1) = stepIndicatorLp i`,
`wienerAssembly (single i 1) = wienerIncrementLp i`. -/
lemma wienerIntegralLp_stepIndicator (hB : IsPreBrownianReal B μ) (T : ℝ≥0) (i : StepIndex T) :
    wienerIntegralLp B hB T (stepIndicatorLp T i) = wienerIncrementLp B hB i := by
  have hstep : stepIndicatorLp T i = stepAssembly T (Finsupp.single i (1 : ℝ)) := by
    rw [stepAssembly, Finsupp.linearCombination_single, one_smul]
  have hincr : wienerIncrementLp B hB i = wienerAssembly B hB T (Finsupp.single i (1 : ℝ)) := by
    rw [wienerAssembly, Finsupp.linearCombination_single, one_smul]
  rw [hstep, hincr, wienerIntegralLp]
  exact LinearMap.extendOfNorm_eq (stepAssembly_denseRange T)
    ⟨1, fun z ↦ by rw [one_mul]; exact (wiener_assembly_isometry hB T z).le⟩ _

end MathFin
