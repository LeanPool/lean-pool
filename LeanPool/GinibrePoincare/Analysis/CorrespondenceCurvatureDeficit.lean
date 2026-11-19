/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCurvatureDeficit.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceCurvatureHessian
/-!
# Correspondence curvature deficit

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondence_pointwise_interaction_deficit`.
-/

@[expose] public section
open Set Filter
open scoped ContDiff BigOperators ComplexConjugate Topology
namespace GinibrePoincare
noncomputable section

/-- Literal interaction-only pointwise deficit identity (1.43). -/
theorem correspondence_pointwise_interaction_deficit {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (z : Configuration n) (hz : CollisionFree z) :
    ginibrePointwiseGammaTwo n f z - 2*ginibrePointwiseGamma n f f z =
      (1/(n : ℝ)^2)*(ginibreBochnerHessianSquare f z +
        fderiv ℝ (fderiv ℝ (ginibreInteractionPotential n)) z
          (ginibreBochnerGradient f z) (ginibreBochnerGradient f z)) := by
  have hG := correspondenceGamma_gradient_normSq hn f hf z hz
  have hB := ginibrePointwiseGammaTwo_bochner_bilinear hn f hf z hz
  rw [correspondence_hamiltonian_interaction_hessian _ _ _ hz] at hB
  have hs : (∑ j, (conj (ginibreBochnerGradient f z j)*ginibreBochnerGradient f z j).re) =
      configurationNormSq (ginibreBochnerGradient f z) := by
    simp [configurationNormSq, Complex.mul_re, Complex.normSq_apply]
  rw [hs,← hG] at hB
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (mul_left_cancel₀ (pow_ne_zero 2 hn0))
  field_simp
  nlinarith [hB]

end
end GinibrePoincare
