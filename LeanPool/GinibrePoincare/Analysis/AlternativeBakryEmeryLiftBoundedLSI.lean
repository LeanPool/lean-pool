/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryLiftBoundedLSI.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLiftLSILimit
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryLiftProbability
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBoundedLSIClosure
/-!
# Alternative Bakry Emery lift bounded LSI

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryEuclideanLift_boundedLipschitz_square_lsi`.
-/

@[expose] public section
open MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The actual nonquadratic Euclidean lift satisfies the sharp curvature-bound
inequality on the bounded Lipschitz domain, with ordinary gradient energy. -/
theorem bakryEmeryEuclideanLift_boundedLipschitz_square_lsi
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (V : Potential) (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : EuclideanSpace ℝ (Fin d × Fin 2) → ℝ)
    {K : ℝ≥0} (hf : LipschitzWith K f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    squareEntropy (bakryEmeryNormalizedGibbs volume (bakryEmeryEuclideanLiftPotential n V)) f ≤
      (2/((n : ℝ)*ρ)) * ∫ x, ‖gradient f x‖^2 ∂bakryEmeryNormalizedGibbs volume
        (bakryEmeryEuclideanLiftPotential n V) := by
  let E := EuclideanSpace ℝ (Fin d × Fin 2)
  let μ := bakryEmeryNormalizedGibbs (volume : Measure E) (bakryEmeryEuclideanLiftPotential n V)
  let : IsProbabilityMeasure μ := bakryEmeryEuclideanLift_gibbs_probability n hn ρ hρ V
      hV.continuous hrot hc
  exact bakryEmery_boundedLipschitz_gradient_lsi_of_compact E volume μ
    (bakryEmeryEuclideanLift_gibbs_absolutelyContinuous n V) (2/((n : ℝ)*ρ))
    (fun g hg hgs => bakryEmeryEuclideanLift_square_lsi n d hn hd ρ hρ V hV hrot hc g hg hgs)
    f hf C hC

end
end GinibrePoincare
