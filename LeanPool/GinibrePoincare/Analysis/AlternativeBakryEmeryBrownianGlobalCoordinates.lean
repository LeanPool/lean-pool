/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryBrownianGlobalCoordinates.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGlobalGaussian
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianCompletedProductBrownian
/-!
# Alternative Bakry Emery Brownian global coordinates

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryBrownianCoordinate_isBrownian_of_scalar`,
`bakryBrownianCoordinate_independent`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
variable (ι : Type*) [Fintype ι]

/-- An `ι`-indexed family of global Brownian samples, with σ-algebra completed for the product
of copies of `bakryBrownianGlobalMeasure`. -/
abbrev BakryBrownianCoordinateSample :=
  NullMeasurableSpace (ι → BakryBrownianGlobalSample)
    (Measure.pi (fun _ : ι => bakryBrownianGlobalMeasure))

/-- The completion of the product of `ι` copies of `bakryBrownianGlobalMeasure`. -/
def bakryBrownianCoordinateMeasure : Measure (BakryBrownianCoordinateSample ι) :=
  (Measure.pi (fun _ : ι => bakryBrownianGlobalMeasure)).completion

instance : IsProbabilityMeasure (bakryBrownianCoordinateMeasure ι) :=
  ginibre_completion_isProbabilityMeasure _
instance : (bakryBrownianCoordinateMeasure ι).IsComplete :=
  Measure.completion.isComplete _

/-- The `i`-th coordinate Brownian process: `bakryBrownianGlobalProcess` evaluated on the
`i`-th sample. -/
def bakryBrownianCoordinateProcess (i : ι) (t : ℝ≥0)
    (ω : BakryBrownianCoordinateSample ι) : ℝ := bakryBrownianGlobalProcess t (ω i)

lemma bakryBrownianCoordinate_eval_preserving (i : ι) :
    MeasurePreserving (fun ω : BakryBrownianCoordinateSample ι => ω i)
      (bakryBrownianCoordinateMeasure ι) bakryBrownianGlobalMeasure := by
  refine ⟨(measurable_pi_apply i).nullMeasurable.measurable',?_⟩
  change (Measure.pi (fun _ : ι => bakryBrownianGlobalMeasure)).completion.map
    (fun ω => ω i) = _
  rw [ginibre_map_completion _ _ (measurable_pi_apply i)]
  exact (measurePreserving_eval (fun _ : ι => bakryBrownianGlobalMeasure) i).map_eq

lemma bakryBrownianCoordinate_isBrownian_of_scalar
    (hB : IsBrownianReal bakryBrownianGlobalProcess bakryBrownianGlobalMeasure) :
    ∀ i, IsBrownianReal (bakryBrownianCoordinateProcess ι i) (bakryBrownianCoordinateMeasure ι) :=
        by
  intro i
  exact ginibreBrownian_precompose_measurePreserving _ _ _
    (bakryBrownianCoordinate_eval_preserving ι i) _ hB

lemma bakryBrownianCoordinate_independent :
    iIndepFun (fun i ω t => bakryBrownianCoordinateProcess ι i t ω)
      (bakryBrownianCoordinateMeasure ι) := by
  let μ := Measure.pi (fun _ : ι => bakryBrownianGlobalMeasure)
  have hp : MeasurePreserving (fun ω : BakryBrownianCoordinateSample ι =>
      (fun i => ω i)) (bakryBrownianCoordinateMeasure ι) μ := by
    have hId : @Measurable (ι → BakryBrownianGlobalSample) (ι → BakryBrownianGlobalSample)
        MeasurableSpace.pi MeasurableSpace.pi id := measurable_id
    refine ⟨hId.nullMeasurable.measurable',?_⟩
    have he := ginibre_map_completion μ
      (fun ω : ι → BakryBrownianGlobalSample => fun i => ω i) measurable_id
    exact he.trans Measure.map_id'
  have hm : Measurable
      (fun ω : BakryBrownianGlobalSample => fun t => bakryBrownianGlobalProcess t ω) :=
    Measurable.of_eval (fun t => bakryBrownianGlobalPath_eval_measurable t)
  exact ginibre_iIndepFun_precompose_measurePreserving _ μ _ hp
    (fun i ω t => bakryBrownianGlobalProcess t (ω i))
    (fun i => hm.comp (measurable_pi_apply i))
    (iIndepFun_pi (X := fun _ ω t => bakryBrownianGlobalProcess t ω) (fun _ => hm.aemeasurable))

end
end GinibrePoincare
