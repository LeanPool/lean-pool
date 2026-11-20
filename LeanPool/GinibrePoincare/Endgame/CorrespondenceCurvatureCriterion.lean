/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Endgame/CorrespondenceCurvatureCriterion.lean.
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
public import LeanPool.GinibrePoincare.Endgame.FullTheoremOneNinePointwiseGamma

/-!
# Correspondence curvature criterion

Part of the paper assembly development of the
Ginibre Poincaré formalization.

Main results: `correspondence_poincare_iff_integrated_pointwise_curvature`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The literal integrated pointwise curvature criterion (1.42), with ordinary
gradient energy represented by its actual weighted L² class. -/
theorem correspondence_integrated_pointwise_curvature {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    2 * ginibreWeakEnergy n (ginibreFullCoreGradient hn f hf) ≤
      ∫ z, ginibrePointwiseGammaTwo n f z ∂ginibreMeasure n := by
  obtain ⟨g, hg, hfirst, hsecond⟩ := fullTheoremOneNinePointwiseGamma hn f hf
  have hgg : g = ginibreFullCoreGradient hn f hf :=
    ginibre_distributional_gradient_unique n hn _ _ _ hg
      (ginibreFullCorePair hn f hf).property.1
  subst g
  have htail := modeTail_nonneg
    (positiveHermiteModeMass hn
      (ginibreFullCenteredTransform n hn (ginibreFullCoreValue hn f hf)))
    (fun k => sq_nonneg _)
  nlinarith [sq_nonneg ‖ginibreFullCorePregenerator hn f hf + (2 : ℝ) •
    ginibreFullCenter n hn (ginibreFullCoreValue hn f hf)‖,
    sq_nonneg ‖ginibreFullHolomorphicRemainder n hn (ginibreFullCoreValue hn f hf)‖]

/-- The specific Ginibre Poincaré and integrated-curvature assertions are
equivalent. Both sides are established independently by concrete deficit
identities; this is not a universal external Bakry–Émery equivalence theorem. -/
theorem correspondence_poincare_iff_integrated_pointwise_curvature
    {n : ℕ} (hn : 0 < n) :
    (∀ (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n),
      IsGinibreDistributionalGradient n u g → IsGinibreSymmetricWeakPair (u, g) →
      ginibreL2Variance n hn u ≤ ginibreWeakEnergy n g / 2) ↔
    (∀ (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f),
      2 * ginibreWeakEnergy n (ginibreFullCoreGradient hn f hf) ≤
        ∫ z, ginibrePointwiseGammaTwo n f z ∂ginibreMeasure n) := by
  constructor
  · intro _ f hf
    exact correspondence_integrated_pointwise_curvature hn f hf
  · intro _ u g hg hs
    exact ginibre_symmetric_weak_poincare hn u g hg hs

end
end GinibrePoincare
