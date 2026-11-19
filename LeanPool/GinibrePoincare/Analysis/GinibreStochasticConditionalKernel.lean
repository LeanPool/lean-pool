/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticConditionalKernel.lean.
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

public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.HasLaw

/-! # Conditional probability kernel of a genuine independent innovation -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem ginibreIndependent_condDistrib {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : Ω → β) (Z : Ω → ℝ)
    (hR : Measurable R) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hZ : HasLaw Z ν P) (hind : IndepFun Z R P) :
    condDistrib Z R P =ᵐ[P.map R] Kernel.const β ν := by
  apply condDistrib_ae_eq_of_measure_eq_compProd hR.aemeasurable hZ.aemeasurable
  rw [Measure.compProd_const]
  rw [hind.symm.map_prod_eq_prod_map_map hR.aemeasurable hZ.aemeasurable, hZ.map_eq]

theorem ginibreIndependent_condDistrib_general {Ω β ζ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace ζ]
    [StandardBorelSpace ζ] [Nonempty ζ]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : Ω → β) (Z : Ω → ζ)
    (hR : Measurable R) (ν : Measure ζ) [IsProbabilityMeasure ν]
    (hZ : HasLaw Z ν P) (hind : IndepFun Z R P) :
    condDistrib Z R P =ᵐ[P.map R] Kernel.const β ν := by
  apply condDistrib_ae_eq_of_measure_eq_compProd hR.aemeasurable hZ.aemeasurable
  rw [Measure.compProd_const]
  rw [hind.symm.map_prod_eq_prod_map_map hR.aemeasurable hZ.aemeasurable, hZ.map_eq]

end
end GinibrePoincare
