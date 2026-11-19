/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityCoordinates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianFourierCoordinates
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import LeanPool.GinibrePoincare.Analysis.GaussianHermiteMoments
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import LeanPool.GinibrePoincare.Concrete.MeasureModel
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs

/-!
# Ginibre transition analytic local regularity coordinates

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_coordinate_integral`.
-/

@[expose] public section
open MeasureTheory Measure
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_coordinate_volume (n : ℕ) :
    ∃ c : ℝ≥0, 0 < c ∧
      (volume : Measure (Configuration n)).map (configurationEuclideanEquiv n) =
        c • (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  let e := configurationEuclideanEquiv n
  let μ := (volume : Measure (Configuration n)).map e
  let : IsAddHaarMeasure μ := e.isAddHaarMeasure_map volume
  refine ⟨addHaarScalarFactor μ volume, addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume,?_⟩
  exact isAddLeftInvariant_eq_smul μ volume

theorem ginibreLocalRegularity_coordinate_integral (n : ℕ) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ,
      (∫ z : Configuration n, f (configurationEuclideanEquiv n z)) =
        (c : ℝ) • (∫ x, f x) := by
  obtain ⟨c, hc, he⟩ := ginibreLocalRegularity_coordinate_volume n
  refine ⟨c, hc,?_⟩
  intro f
  have hm := integral_map_equiv (μ := (volume : Measure (Configuration n)))
    (configurationEuclideanEquiv n).toHomeomorph.toMeasurableEquiv f
  change (∫ x, f x ∂(volume : Measure (Configuration n)).map (configurationEuclideanEquiv n)) =
    (∫ z : Configuration n, f (configurationEuclideanEquiv n z)) at hm
  rw [he, integral_smul_nnreal_measure] at hm
  exact hm.symm

end
end GinibrePoincare
