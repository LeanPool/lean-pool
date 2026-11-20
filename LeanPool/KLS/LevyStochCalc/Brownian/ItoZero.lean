/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoL2Completion

/-!
# The Itô integral of the zero integrand

The `L²`-isometry forces the Itô integral of the zero integrand to vanish almost surely, at
every time. This is what lets a coordinate of a vector Itô process carry no diffusion.

## Main statements

* `LevyStochCalc.Probability.progressivelyMeasurable_const` — a constant process is
  progressively measurable.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero` — the Itô integral of the zero
  integrand vanishes almost surely.
-/

@[expose] public section

namespace LevyStochCalc

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

/-- A constant process is progressively measurable for any filtration. -/
theorem Probability.progressivelyMeasurable_const {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [TopologicalSpace E] [Zero E] (ℱ : Filtration ℝ mΩ) (c : E) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => c) := fun _ =>
  stronglyMeasurable_const.indicator
    (measurableSet_preimage measurable_snd measurableSet_Iic)

/-- The zero process is progressively measurable for any filtration. -/
theorem Probability.progressivelyMeasurable_zero {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    [TopologicalSpace E] [Zero E] (ℱ : Filtration ℝ mΩ) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => (0 : E)) :=
  Probability.progressivelyMeasurable_const ℱ 0

namespace Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The Itô integral of the zero integrand vanishes almost surely.** -/
theorem stochasticIntegralBrownian_ae_zero
    (hm : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)))
    (hp : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ))
    (hq : ∀ T, 0 < T → ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
      (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (0 : ℝ)) hm hp hq t =ᵐ[P] 0 := by
  rcases le_or_gt t 0 with ht | ht
  · exact stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ _ hm hp hq ht
  · have hiso := isometry_stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (0 : ℝ)) hm hp hq ht
    have hrhs : ∫⁻ ω, ∫⁻ _s in Set.Icc (0 : ℝ) t,
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
      simp
    rw [hrhs] at hiso
    have hmeas : AEMeasurable (fun ω => (‖stochasticIntegralBrownian W ℱ hℱ
        (fun _ _ => (0 : ℝ)) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2) P :=
      ((((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ _ hm hp hq t).mono
        (ℱ.le t)).measurable.nnNorm.coe_nnreal_ennreal).pow_const 2).aemeasurable
    have hzero := (MeasureTheory.lintegral_eq_zero_iff' hmeas).mp hiso
    filter_upwards [hzero] with ω hω
    have : (‖stochasticIntegralBrownian W ℱ hℱ (fun _ _ => (0 : ℝ)) hm hp hq t ω‖₊ : ℝ≥0∞) = 0 := by
      simpa [pow_eq_zero_iff] using hω
    simpa using this

end Brownian.Ito

end LevyStochCalc
