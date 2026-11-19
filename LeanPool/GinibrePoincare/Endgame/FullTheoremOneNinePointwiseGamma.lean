/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Endgame/FullTheoremOneNinePointwiseGamma.lean.
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
public import LeanPool.GinibrePoincare.Endgame.FullTheoremOneNine
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreIdentification
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorUnrestrictedGamma
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCenterEigenvectors
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConstants
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupDeficitConsequences
public import LeanPool.GinibrePoincare.Analysis.HolomorphicQuotientPhaseProjection

/-! # From the generator deficit to the pointwise Γ₂ integral

The compact smooth collision-free core lies in the symmetric generator graph.
Apply the graph-domain deficits first. The unrestricted integration-by-parts
identity identifies the integral of pointwise Γ₂ with the squared L² norm of
the pregenerator; the almost-everywhere representative lemma then identifies
this norm with the core generator value. This last bridge is needed to express
the second deficit in the paper's differential notation.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Both concrete Theorem 1.9 identities on the paper's literal smooth core,
with the second deficit expressed using actual pointwise Γ₂. -/
theorem fullTheoremOneNinePointwiseGamma {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n (ginibreFullCoreValue hn f hf) g ∧
      ginibreWeakEnergy n g - 2*ginibreL2Variance n hn (ginibreFullCoreValue hn f hf) =
        2*‖ginibreFullHolomorphicRemainder n hn (ginibreFullCoreValue hn f hf)‖^2 +
          4*modeTail (positiveHermiteModeMass hn
            (ginibreFullCenteredTransform n hn (ginibreFullCoreValue hn f hf))) ∧
      (∫ z, ginibrePointwiseGammaTwo n f z ∂ginibreMeasure n)-2*ginibreWeakEnergy n g =
        ‖ginibreFullCorePregenerator hn f hf+(2 : ℝ) •
          ginibreFullCenter n hn (ginibreFullCoreValue hn f hf)‖^2 +
          4*‖ginibreFullHolomorphicRemainder n hn (ginibreFullCoreValue hn f hf)‖^2 +
          8*modeTail (positiveHermiteModeMass hn
            (ginibreFullCenteredTransform n hn (ginibreFullCoreValue hn f hf))) := by
  obtain ⟨g, deficits⟩ := fullTheoremOneNine_named hn
    (ginibreFullCoreSymmetricValue hn f hf) (ginibreFullCoreSymmetricPregenerator hn f hf)
    (ginibreFullGenerator_core_graph hn f hf)
  have hcf : tsupport f⊆{z|CollisionFree z} := by
    intro z hz
    exact (collisionFree_iff_not_mem_collisionSet z).mpr (hf.2.2.1 hz)
  have hΓ := correspondenceOperator_integral_pointwiseGammaTwo_unrestricted hn f
    ⟨hf.1, hf.2.1, hcf⟩
  have hi : (∫ z, (ginibrePregenerator n f z)^2 ∂ginibreMeasure n) =
      ‖ginibreFullCorePregenerator hn f hf‖^2 := by
    rw [← integral_square_eq_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [ginibreFullCorePregenerator_ae hn f hf] with z hz
    rw [hz]
  refine ⟨g, deficits.distributional_gradient, deficits.poincare_deficit, ?_⟩
  rw [hΓ, hi]
  exact deficits.generator_deficit

end
end GinibrePoincare
