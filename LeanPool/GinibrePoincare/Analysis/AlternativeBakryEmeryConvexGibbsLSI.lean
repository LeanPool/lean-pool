/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryConvexGibbsLSI.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGlobal
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsLSI
/-!
# Alternative Bakry Emery convex Gibbs LSI

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryConfigurationGibbs_square_lsi`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
namespace GinibrePoincare
noncomputable section

/-- Concrete strongly convex normalized Gibbs log-Sobolev inequality on real
Euclidean coordinates. Brownian noise, global Langevin flow, Gibbs invariance
and the entropy limit are all constructed internally. -/
theorem bakryEmeryConfigurationGibbs_square_lsi
    (n : ℕ) (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n×Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (f : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    squareEntropy (bakryEmeryNormalizedGibbs volume (W ∘ (configurationEuclideanEquiv n).symm)) f ≤
      (2/κ)*∫ x, ‖gradient f x‖^2 ∂bakryEmeryNormalizedGibbs volume
        (W ∘ (configurationEuclideanEquiv n).symm) := by
  exact bakryEmeryConfigurationGibbs_square_lsi_of_Brownian n hn W hW κ hκ hc
    (bakryBrownianCoordinateProcess (Fin n×Fin 2)) (bakryBrownianCoordinateMeasure (Fin n×Fin 2))
    (bakryBrownianCoordinate_isBrownian (Fin n×Fin 2))
    (bakryBrownianCoordinate_independent (Fin n×Fin 2)) f hf hs

end
end GinibrePoincare
