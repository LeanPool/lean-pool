/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryLiftProbability.lean.
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
public import LeanPool.GinibrePoincare.Analysis.BakryEmeryRegularizationVolume
/-!
# Alternative Bakry Emery lift probability

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryEuclideanLift_gibbs_probability`,
`bakryEmeryEuclideanLift_gibbs_absolutelyContinuous`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Gaussian confinement makes the actual unregularized lift density integrable. -/
theorem bakryEmeryEuclideanLift_density_integrable
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    Integrable (fun x : E => Real.exp (-bakryEmeryEuclideanLiftPotential n V x)) volume := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hG : Integrable (fun x : E => Real.exp (-((n : ℝ)*ρ)/2*‖x‖^2)) volume := by
    simpa only [neg_div] using bakryEmery_gaussian_majorant_integrable (E := E)
      ((n : ℝ)*ρ/2) (by positivity)
  have hcont : Continuous (bakryEmeryEuclideanLiftPotential (E := E) n V) :=
    continuous_const.mul (hV.comp (Complex.continuous_ofReal.comp continuous_norm))
  apply (hG.const_mul (Real.exp (-(n : ℝ)*V 0))).mono' hcont.neg.rexp.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hd := bakryEmeryRegularizedLift_density_domination n ρ 0 hρ.le hrot hc x
  simpa [bakryEmeryRegularizedLiftPotential, bakryEmeryEuclideanLiftPotential,
    Real.sqrt_sq (norm_nonneg x), Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hd

/-- The literal unregularized Euclidean Gibbs lift is a probability law. -/
theorem bakryEmeryEuclideanLift_gibbs_probability
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    IsProbabilityMeasure (bakryEmeryNormalizedGibbs (volume : Measure E)
      (bakryEmeryEuclideanLiftPotential n V)) := by
  exact bakryEmeryNormalizedGibbs_probability volume _
    (continuous_const.mul (hV.comp (Complex.continuous_ofReal.comp continuous_norm)))
    (bakryEmeryEuclideanLift_density_integrable n hn ρ hρ V hV hrot hc)

/-- Absolute continuity for the actual lift, used to transfer Rademacher limits. -/
theorem bakryEmeryEuclideanLift_gibbs_absolutelyContinuous (n : ℕ) (V : Potential) :
    bakryEmeryNormalizedGibbs (volume : Measure E) (bakryEmeryEuclideanLiftPotential n V) ≪ volume
        := by
  exact (withDensity_absolutelyContinuous _ _).smul_left _

end
end GinibrePoincare
