/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsMass.lean.
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

/-! The actual smooth radial Gibbs laws have finite positive mass in every
finite-dimensional real Hilbert space. Gaussian integrability is discharged
here rather than supplied as an analytic certificate. -/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem bakryEmeryRegularizedLift_density_integrable
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V)
    (hc : IsRhoConvexPotential ρ V) (ε : ℝ) :
    Integrable (fun x : E => Real.exp (-bakryEmeryRegularizedLiftPotential n V ε x)) volume := by
  have hG := bakryEmery_gaussian_majorant_integrable (E := E) ((n : ℝ)*ρ/2)
    (by positivity)
  have hm : Continuous (fun x : E => Real.exp (-bakryEmeryRegularizedLiftPotential n V ε x)) :=
    Real.continuous_exp.comp ((continuous_const.mul (hV.comp
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
        ((continuous_norm.pow 2).add continuous_const))))).neg)
  apply (hG.const_mul (Real.exp (-(n : ℝ)*V 0))).mono hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa only [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)),
    neg_div]
    using bakryEmeryRegularizedLift_density_domination n ρ ε hρ.le hrot hc x

theorem bakryEmeryRegularizedLift_gibbs_probability
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V)
    (hc : IsRhoConvexPotential ρ V) (ε : ℝ) :
    IsProbabilityMeasure (bakryEmeryNormalizedGibbs (volume : Measure E)
      (bakryEmeryRegularizedLiftPotential n V ε)) := by
  apply bakryEmeryNormalizedGibbs_probability
  · exact continuous_const.mul (hV.comp (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp ((continuous_norm.pow 2).add continuous_const))))
  · exact bakryEmeryRegularizedLift_density_integrable n hn ρ hρ V hV hrot hc ε

end
end GinibrePoincare
