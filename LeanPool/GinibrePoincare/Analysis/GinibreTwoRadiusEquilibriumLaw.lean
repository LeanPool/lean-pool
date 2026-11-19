/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTwoRadiusEquilibriumLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianBlockRadialLaw
public import LeanPool.GinibrePoincare.Analysis.PairwiseRadius

/-!
# Ginibre two radius equilibrium law

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `ginibreTwoRadius_equilibrium_gamma_product`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

/-- The literal squared norm of a standard complex Gaussian is Gamma(1,1). -/
theorem standardComplexGaussian_normSq_gamma :
    standardComplexGaussianMeasure.map Complex.normSq=gammaMeasure 1 1 := by
  have he : (gaussianBlockMeasure 1 1).map (fun z : Configuration 1 => z 0)=
      standardComplexGaussianMeasure := by
    exact (measurePreserving_eval (fun _ : Fin 1 =>
      (complexCoordinateGaussianProbability 1 : Measure ℂ)) 0).map_eq
  have hr : gaussianBlockRadius 1 1=(fun z : Configuration 1 => Complex.normSq (z 0)) := by
    funext z
    simp [gaussianBlockRadius, configurationNormSq]
  rw [← he, Measure.map_map Complex.continuous_normSq.measurable (measurable_pi_apply 0)]
  change (gaussianBlockMeasure 1 1).map (fun z : Configuration 1 => Complex.normSq (z
      0))=gammaMeasure 1 1
  rw [← hr]
  simpa using gaussianBlockRadius_gamma 1 1 (by decide) (by decide)

/-- Exact equilibrium law of the center CIR observable. -/
theorem ginibreCenterSquared_equilibrium_gamma (n : ℕ) (hn : 0 < n) :
    (ginibreMeasure n).map (ginibreCenterSquared n)=gammaMeasure 1 1 := by
  rw [← standardComplexGaussian_normSq_gamma,← coordinateSum_ginibre_gaussian n hn,
    Measure.map_map Complex.continuous_normSq.measurable (measurable_coordinateSum n)]
  rfl

/-- The actual two equilibrium CIR radii are independent. -/
theorem ginibreCenterSquared_pairwiseRadius_independent (n : ℕ) (hn : 0 < n) :
    IndepFun (ginibreCenterSquared n) (pairwiseRadius : Configuration n → ℝ)
      (ginibreMeasure n) := by
  exact (coordinateSum_pairwiseRadius_indepFun n hn).comp
    Complex.continuous_normSq.measurable measurable_id

/-- Exact joint Gamma product law of both concrete equilibrium radii. -/
theorem ginibreTwoRadius_equilibrium_gamma_product (n : ℕ) (hn : 2 ≤ n) :
    (ginibreMeasure n).map (fun z => (ginibreCenterSquared n z, pairwiseRadius z))=
      (gammaMeasure 1 1).prod (gammaMeasure (recenteredGammaShape n : ℝ) 1) := by
  let := ginibreMeasure_isProbabilityMeasure (by omega : 0<n)
  have hmS : Measurable (ginibreCenterSquared n) :=
    Complex.continuous_normSq.measurable.comp (measurable_coordinateSum n)
  have hmR : Measurable (pairwiseRadius : Configuration n → ℝ) := by
    unfold pairwiseRadius
    fun_prop
  rw [(ginibreCenterSquared_pairwiseRadius_independent n (by omega)).map_prod_eq_prod_map_map
    hmS.aemeasurable hmR.aemeasurable, ginibreCenterSquared_equilibrium_gamma n (by omega)]
  rw [recenteredGammaShape_eq n (by omega), pairwiseRadius_ginibre_gamma n hn]

end
end GinibrePoincare
