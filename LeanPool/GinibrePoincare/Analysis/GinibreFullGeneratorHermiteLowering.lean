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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakConstants
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakModes
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorDbarTransform

/-! # Weak derivatives and Hermite lowering -/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory Filter ComplexHermite
open scoped Topology BigOperators

/-- The actual ordinary weak gradient satisfies the exact Gaussian Hermite
lowering graph, obtained from simultaneous core approximation. -/
theorem ginibreFullTransformedDbar_weak_coefficient {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g))
    (j : Fin n) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (ginibreFullTransformedDbar n hn j g) pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn
          (normalizedVandermondeL2 n hn (ginibreFullComplexOfReal n u))
          (raiseHermiteIndex j pq) := by
  obtain ⟨q, hq, hlim⟩ := ginibreSymmetricWeakPair_exists_core_sequence hn u g hu hs
  let L : GinibreFullValueL2 n × GinibreFullGradientL2 n → ℂ :=
    fun p => gaussianHermiteCoefficient hn (ginibreFullTransformedDbar n hn j p.2) pq
  let R : GinibreFullValueL2 n × GinibreFullGradientL2 n → ℂ :=
    fun p => (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
      gaussianHermiteCoefficient hn
        (normalizedVandermondeL2 n hn (ginibreFullComplexOfReal n p.1))
        (raiseHermiteIndex j pq)
  have hL : Continuous L := by
    simp only [L, gaussianHermiteCoefficient_eq_inner]
    exact continuous_const.inner ((ginibreFullTransformedDbar n hn j).continuous.comp
      continuous_snd)
  have hR : Continuous R := by
    simp only [R, gaussianHermiteCoefficient_eq_inner]
    exact continuous_const.mul (continuous_const.inner
      ((normalizedVandermondeL2 n hn).continuous.comp
        ((ginibreFullComplexOfReal n).continuous.comp continuous_fst)))
  have hc : IsClosed {p | L p = R p} := isClosed_eq hL hR
  have hmem : ∀ m, q m ∈ {p | L p = R p} := by
    intro m
    obtain ⟨f, hf, hv, hg⟩ := hq m
    exact ginibreFullTransformedDbar_smooth_coefficient hn f hf.1 hf.2.1
      (q m).1 (q m).2 hv hg j pq
  have htarget : (u, g) ∈ {p | L p = R p} :=
    hc.mem_of_tendsto hlim (Eventually.of_forall hmem)
  exact htarget

/-- Centering preserves the actual symmetric ordinary weak gradient. -/
theorem ginibreFullCenter_weak_pair {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g)) :
    IsGinibreDistributionalGradient n (ginibreFullCenter n hn u) g ∧
      IsGinibreSymmetricWeakPair (ginibreFullCenter n hn u, g) := by
  let p : ginibreFullWeakSpace n hn := ⟨(u, g), hu, hs⟩
  let c : ginibreFullWeakSpace n hn :=
    ⟨(ginibreRealConstantL2 n hn (ginibreL2Mean n u), 0),
      ginibreRealConstantL2_weak n hn _, ginibreRealConstantL2_symmetric_pair n hn _⟩
  have hp := (p-c).property
  change IsGinibreDistributionalGradient n
    (u - ginibreRealConstantL2 n hn (ginibreL2Mean n u)) (g-0) ∧
    IsGinibreSymmetricWeakPair (u - ginibreRealConstantL2 n hn (ginibreL2Mean n u), g-0) at hp
  simpa only [ginibreFullCenter_apply, sub_zero] using hp

/-- Full weighted Hermite energy is an exact convergent series for every
actual symmetric weak pair. -/
theorem ginibreFullWeak_weighted_hermite_energy {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g)) :
    HasSum (fun k : ℕ => (k + 1) *
      positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u) k)
      (ginibreWeakEnergy n g / 4) := by
  obtain ⟨huc, hsc⟩ := ginibreFullCenter_weak_pair hn u g hu hs
  have he := hasSum_weighted_positiveHermiteModeMass_of_coefficient_raise hn
    (ginibreFullCenteredTransform n hn u) (ginibreFullTransformedDbar n hn · g)
    (ginibreFullTransformedDbar_weak_coefficient hn (ginibreFullCenter n hn u) g huc hsc)
  rw [ginibreFullTransformedDbar_norm_sum hn g] at he
  convert he using 1
  unfold ginibreWeakEnergy
  ring

end GinibrePoincare
