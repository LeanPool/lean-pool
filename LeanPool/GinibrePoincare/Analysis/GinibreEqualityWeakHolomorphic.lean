/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityWeakHolomorphic.lean.
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


public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakModes

/-!
# Ginibre Equality Weak Holomorphic
-/


@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory Filter
open scoped Topology

/-- Pointwise conjugation on complex Ginibre L², viewed as a real-linear isometry. -/
def ginibreFullLpConjugationIsometry (n : ℕ) :
    Lp ℂ 2 (ginibreMeasure n) →ₗᵢ[ℝ] Lp ℂ 2 (ginibreMeasure n) where
  toLinearMap :=
    { toFun := star
      map_add' := by exact Lp_star_add
      map_smul' := by exact Lp_star_real_smul }
  norm_map' := by exact Lp_norm_star

/-- Centered residual after subtracting the holomorphic projection and its conjugate. -/
def ginibreFullHolomorphicRemainder (n : ℕ) (hn : 0 < n) (u : GinibreFullValueL2 n) :=
  let U := ginibreFullComplexOfReal n (ginibreFullCenter n hn u)
  let H := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection U
  U - H - star H

theorem ginibreFullHolomorphicRemainder_continuous (n : ℕ) (hn : 0 < n) :
    Continuous (ginibreFullHolomorphicRemainder n hn) := by
  let C := (ginibreFullComplexOfReal n).comp (ginibreFullCenter n hn)
  let P := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection.restrictScalars ℝ |>.comp C
  exact (C.continuous.sub P.continuous).sub
    ((ginibreFullLpConjugationIsometry n).continuous.comp P.continuous)

lemma ginibreEquality_core_pair_holomorphic_bound {n : ℕ} (hn : 0 < n)
    (p : GinibreFullValueL2 n × GinibreFullGradientL2 n)
    (hp : p ∈ ginibreTheoremOneNineCorePairs n) :
    2 * ‖ginibreFullHolomorphicRemainder n hn p.1‖ ^ 2 ≤
      ginibreWeakEnergy n p.2 - 2 * ginibreL2Variance n hn p.1 := by
  obtain ⟨f, hf, hv, hg⟩ := hp
  have he := ginibreWeakEnergy_eq_smoothGinibreEnergy p.2 f hg
  have hc : ginibreFullComplexOfReal n (ginibreFullCenter n hn p.1) =
      centeredObservableL2 hn f hf :=
    (normalizedVandermondeL2 n hn).injective (ginibreFullCenteredTransform_core hn f hf p.1 hv)
  have hvar := ginibreL2Variance_eq_smoothGinibreVariance hn p.1 f hv
  unfold ginibreFullHolomorphicRemainder
  rw [hc, he, hvar]
  have hid := (concrete_theoremOneNine hn f hf).1
  have htail := modeTail_nonneg (concretePositiveHermiteModeMass hn f hf)
    (fun k => sq_nonneg _)
  linarith

/-- The holomorphic/conjugate remainder is bounded by the exact Poincaré
 deficit on the entire actual symmetric weak domain. -/
theorem ginibreEquality_weak_holomorphic_bound {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g)) :
    2 * ‖ginibreFullHolomorphicRemainder n hn u‖ ^ 2 ≤
      ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u := by
  obtain ⟨q, hq, hlim⟩ := ginibreSymmetricWeakPair_exists_core_sequence hn u g hu hs
  let S : Set (GinibreFullValueL2 n × GinibreFullGradientL2 n) :=
    {p | 2 * ‖ginibreFullHolomorphicRemainder n hn p.1‖ ^ 2 ≤
      ginibreWeakEnergy n p.2 - 2 * ginibreL2Variance n hn p.1}
  have hclosed : IsClosed S := by
    have hleft : Continuous (fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
        2 * ‖ginibreFullHolomorphicRemainder n hn p.1‖ ^ 2) :=
      continuous_const.mul (((ginibreFullHolomorphicRemainder_continuous n hn).comp
        continuous_fst).norm.pow 2)
    have hright : Continuous (fun p : GinibreFullValueL2 n × GinibreFullGradientL2 n =>
        ginibreWeakEnergy n p.2 - 2 * ginibreL2Variance n hn p.1) :=
      ((ginibreWeakEnergy_continuous n).comp continuous_snd).sub
        (continuous_const.mul ((ginibreL2Variance_continuous n hn).comp continuous_fst))
    exact isClosed_le hleft hright
  have hqmem : ∀m, q m ∈ S := fun m => ginibreEquality_core_pair_holomorphic_bound hn (q m) (hq m)
  have hmem : (u, g) ∈ S := hclosed.mem_of_tendsto hlim (Eventually.of_forall hqmem)
  exact hmem

/-- Full weak equality has no holomorphic/conjugate remainder. -/
theorem ginibreEquality_weak_holomorphic_remainder_zero {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g))
    (heq : ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u) :
    ginibreFullHolomorphicRemainder n hn u = 0 := by
  have hb := ginibreEquality_weak_holomorphic_bound hn u g hu hs
  rw [heq, sub_self] at hb
  have hz : ‖ginibreFullHolomorphicRemainder n hn u‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg (‖ginibreFullHolomorphicRemainder n hn u‖)]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (ginibreFullHolomorphicRemainder n hn u)])

/-- Full weak-domain holomorphic projection, as an actual ambient L² class. -/
def ginibreFullHolomorphicPart (n : ℕ) (hn : 0 < n) (u : GinibreFullValueL2 n) :=
  (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
    (ginibreFullComplexOfReal n (ginibreFullCenter n hn u))

theorem ginibreFullHolomorphicPart_continuous (n : ℕ) (hn : 0 < n) :
    Continuous (ginibreFullHolomorphicPart n hn) :=
  (ginibreHolomorphicAmbientClosedSpan n hn).starProjection.continuous.comp
    ((ginibreFullComplexOfReal n).continuous.comp (ginibreFullCenter n hn).continuous)

/-- The centered holomorphic part of every genuine full symmetric weak-domain
observable lies in the strictly positive graded quotient closure. -/
theorem ginibreFullHolomorphicPart_mem_positive {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ginibreFullHolomorphicPart n hn u ∈ ginibrePositiveQuotientGradedClosedSpan n hn := by
  obtain ⟨q, hq, hlim⟩ := ginibreSymmetricWeakPair_exists_core_sequence hn u g hu hs
  have hqc : ∀m, ginibreFullHolomorphicPart n hn (q m).1 ∈
      ginibrePositiveQuotientGradedClosedSpan n hn := by
    intro m
    obtain ⟨f, hf, hv, _⟩ := hq m
    have he := ginibreFullCenteredTransform_core hn f hf (q m).1 hv
    have hc : ginibreFullComplexOfReal n (ginibreFullCenter n hn (q m).1) =
        centeredObservableL2 hn f hf := (normalizedVandermondeL2 n hn).injective he
    unfold ginibreFullHolomorphicPart
    rw [hc]
    exact holomorphicProjection_centeredObservable_mem_positive hn f hf
  have ht : Tendsto (fun m => ginibreFullHolomorphicPart n hn (q m).1) atTop
      (𝓝 (ginibreFullHolomorphicPart n hn u)) :=
    ((ginibreFullHolomorphicPart_continuous n hn).tendsto u).comp
      (continuous_fst.tendsto (u, g) |>.comp hlim)
  exact (ginibrePositiveQuotientGradedClosedSpan n hn).isClosed.mem_of_tendsto ht
    (Eventually.of_forall hqc)

/-- Exact holomorphic/conjugate reconstruction for arbitrary full weak sharp
attainers, including their genuine positive quotient-space membership. -/
theorem ginibreEquality_weak_holomorphic_reconstruction {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g))
    (heq : ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u) :
    ginibreFullComplexOfReal n (ginibreFullCenter n hn u) =
      ginibreFullHolomorphicPart n hn u + star (ginibreFullHolomorphicPart n hn u) ∧
    ginibreFullHolomorphicPart n hn u ∈ ginibrePositiveQuotientGradedClosedSpan n hn := by
  refine ⟨?_, ginibreFullHolomorphicPart_mem_positive hn u g hu hs⟩
  have h := ginibreEquality_weak_holomorphic_remainder_zero hn u g hu hs heq
  change ginibreFullComplexOfReal n (ginibreFullCenter n hn u) -
    ginibreFullHolomorphicPart n hn u - star (ginibreFullHolomorphicPart n hn u) = 0 at h
  exact (sub_eq_zero.mp h |> sub_eq_iff_eq_add.mp).trans (add_comm _ _)

end GinibrePoincare
