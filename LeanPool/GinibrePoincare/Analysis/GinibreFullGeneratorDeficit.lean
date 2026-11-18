/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-poincare.

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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakDeficit
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorVariational

/-! # Deficits from the variational generator graph

The graph characterization supplies a symmetric distributional gradient and
its variational pairing with every weak test pair. Test with the centered
value to identify Dirichlet energy with minus the generator pairing. The
weak-domain first deficit already supplies Hermite tail summability; expanding
the shifted generator norm and inserting the pairing gives the second deficit.
Graph membership supplies both weak differentiability and summability.
-/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory

/-- Full graph dissipation is the actual weak Dirichlet energy. -/
theorem ginibreFullGenerator_dissipation_eq_energy {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      ginibreWeakEnergy n g = -inner ℝ v.val (ginibreFullCenter n hn u.val) := by
  obtain ⟨g, hug, hsg, hvar⟩ := (ginibreFullGenerator_real_graph_iff_exists_gradient hn u v).mp
    hgraph
  obtain ⟨huc, hsc⟩ := ginibreFullCenter_weak_pair hn u.val g hug hsg
  refine ⟨g, hug, hsg, ?_⟩
  simpa only [ginibreWeakEnergy, real_inner_self_eq_norm_sq] using
    hvar (ginibreFullCenter n hn u.val) g huc hsc

/-- The centered dissipation and both exact deficits for the same graph-domain gradient. -/
theorem ginibreFullGenerator_deficit_identities_with_dissipation {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      ginibreWeakEnergy n g = -inner ℝ v.val (ginibreFullCenter n hn u.val) ∧
      Summable (fun k : ℕ => (k : ℝ) *
        positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val) k) ∧
      ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u.val =
        2 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          4 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) ∧
      ‖v.val‖ ^ 2 - 2 * ginibreWeakEnergy n g =
        ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖ ^ 2 +
          4 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          8 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) := by
  obtain ⟨g, hug, hsg, he⟩ := ginibreFullGenerator_dissipation_eq_energy hn u v hgraph
  obtain ⟨ht, hfirst⟩ := ginibreFullWeak_first_deficit_identity hn u.val g hug hsg
  refine ⟨g, hug, hsg, he, ht, hfirst, ?_⟩
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul]
  norm_num
  rw [mul_pow, ginibreFullCenter_variance]
  nlinarith [he, hfirst]

/-- Both exact deficit identities hold on the actual full real generator graph.
The gradient and convergent spectral tail are consequences of graph membership. -/
theorem ginibreFullGenerator_deficit_identities {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      Summable (fun k : ℕ => (k : ℝ) *
        positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val) k) ∧
      ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u.val =
        2 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          4 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) ∧
      ‖v.val‖ ^ 2 - 2 * ginibreWeakEnergy n g =
        ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖ ^ 2 +
          4 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          8 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) := by
  obtain ⟨g, hug, hsg, -, ht, hfirst, hsecond⟩ :=
    ginibreFullGenerator_deficit_identities_with_dissipation hn u v hgraph
  exact ⟨g, hug, hsg, ht, hfirst, hsecond⟩

end GinibrePoincare
