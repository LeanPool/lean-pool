/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianPredictableMeasureTransform.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Brownian predictable measure transform

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `independent_past_measure_transform`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

/-- A measurable transformation chosen from independent past data preserves
both the fresh law and independence whenever each chosen transformation
preserves that law. This is the exact finite-step innovation identity. -/
theorem independent_past_measure_transform {Ω A E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure A) (μ : Measure E)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (Y : Ω → A) (X : Ω → E) (hY : HasLaw Y ν P) (hX : HasLaw X μ P)
    (hi : IndepFun Y X P) (T : A → E → E)
    (hT : Measurable (Function.uncurry T))
    (hpres : ∀ a, MeasurePreserving (T a) μ μ) :
    HasLaw (fun ω => T (Y ω) (X ω)) μ P ∧
      IndepFun Y (fun ω => T (Y ω) (X ω)) P := by
  have hp := (MeasurePreserving.id ν).skew_product hT
    (Filter.Eventually.of_forall (fun a => (hpres a).map_eq))
  have hj := hp.comp_hasLaw (hi.hasLaw_prod hY hX)
  have ht : HasLaw (fun ω => T (Y ω) (X ω)) μ P := by
    exact (measurePreserving_snd (μ := ν) (ν := μ)).comp_hasLaw hj
  refine ⟨ht, (indepFun_iff_hasLaw_prodMk_prod hY ht).mpr ?_⟩
  exact hj

end
end GinibrePoincare
