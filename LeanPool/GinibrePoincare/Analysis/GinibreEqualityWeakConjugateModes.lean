/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityWeakConjugateModes.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakHolomorphic

/-!
# Ginibre Equality Weak Conjugate Modes
-/


@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory ComplexHermite

/-- Ambient holomorphic Ginibre vectors transform into the actual Gaussian
antiholomorphic degree-zero subspace. -/
theorem ginibreEquality_holomorphic_transform_mem_zero {n : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n)) (hh : h ∈ ginibreHolomorphicAmbientClosedSpan n hn) :
    normalizedVandermondeL2 n hn h ∈ hermiteAntiDegreeClosedSpan n hn 0 := by
  obtain ⟨u, hu, rfl⟩ := hh
  have hmap : vandermondeSymmetricAlternatingEquiv n hn u ∈
      gaussianAlternatingZeroModeClosedSpan n hn := by
    change vandermondeSymmetricAlternatingEquiv n hn u ∈
      (gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule
    rw [← map_ginibreSymmetricHolomorphicPolynomialClosedSpan]
    exact ⟨u, hu, rfl⟩
  exact gaussianAlternatingZeroModeClosedSpan_le_hermiteZeroMode n hn hmap

/-- Orthogonal zero-mode vectors have no positive antiholomorphic component. -/
theorem ginibreEquality_zeroMode_higher_projection_zero {n : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (complexGaussianMeasure n)) (hh : h ∈ hermiteAntiDegreeClosedSpan n hn 0)
    (d : ℕ) (hd : 0 < d) : hermiteAntiDegreeProjection n hn d h = 0 := by
  have h0 : gaussianHermiteMode hn 0 h = h := by
    rw [gaussianHermiteMode_eq_antiDegreeProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hh
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.zero_mem _
  · intro w hw
    rw [sub_zero]
    have hw' : gaussianHermiteMode hn d w = w := by
      rw [gaussianHermiteMode_eq_antiDegreeProjection]
      exact Submodule.starProjection_eq_self_iff.mpr hw
    rw [← h0, ← hw']
    exact inner_gaussianHermiteMode_eq_zero hn (by omega) h w

/-- For a genuine full weak equality attainer, the conjugate of its actual
holomorphic part also has no transformed antiholomorphic modes beyond one. -/
theorem ginibreEquality_weak_conjugate_higher_modes_zero {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g))
    (heq : ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u)
    (k : ℕ) (hk : 0 < k) :
    hermiteAntiDegreeProjection n hn (k + 1)
      (normalizedVandermondeL2 n hn (star (ginibreFullHolomorphicPart n hn u))) = 0 := by
  have hr := (ginibreEquality_weak_holomorphic_reconstruction hn u g hu hs heq).1
  have hm : ginibreFullHolomorphicPart n hn u ∈ ginibreHolomorphicAmbientClosedSpan n hn :=
    Submodule.starProjection_apply_mem _ _
  have hz := ginibreEquality_zeroMode_higher_projection_zero hn _
    (ginibreEquality_holomorphic_transform_mem_zero hn _ hm) (k + 1) (by omega)
  have h := ginibreEquality_weak_higher_modes_vanish hn u g hu hs heq k hk
  unfold ginibreFullHigherMode ginibreFullCenteredTransform at h
  rw [hr, map_add, map_add, hz, zero_add] at h
  exact h

end GinibrePoincare
