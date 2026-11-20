/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialQuotientNonnegativeClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialAlternatedPhaseClassification
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialNonnegativePhaseGeometry
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialQuotientAlternatingClosure
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialQuotientCentering
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticBottomGaugeConstant

/-!
# General potential quotient nonnegative closure

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialHolomorphicQuotient_centered_mem_positive`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem potentialInverseAlternatedVector_mem_nonnegative {n : ℕ} (hn : 0 < n)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (F : PlanarPiLebesgueL2 n)
    (hF : F ∈ planarPiAlternatedWeightedMonomialVectors n n V) :
    (potentialPiVandermondeL2Equiv n hn hV.continuous hfin).symm F ∈
      potentialNonnegativePhaseClosedSpan n hn hV.continuous hrot hfin := by
  rcases potentialInverseAlternatedVector_positive_or_bottom_or_zero hn hV hrot hfin F hF with
    hp | hb | hz
  · apply potentialPositivePhaseClosedSpan_le_nonnegative n hn hV.continuous hrot hfin
    exact (Submodule.span ℂ (potentialPositivePhaseVectors n hV.continuous
        hrot)).le_topologicalClosure
      (Submodule.subset_span hp)
  · obtain ⟨P, hh, ha, he⟩ := hb
    obtain ⟨c, hc⟩ := potentialInverseGauge_bottom_polynomial_constant hn hV hrot hfin P hh ha F he
    rw [hc]
    exact potentialConstantL2_mem_nonnegativePhaseClosedSpan n hn hV.continuous hrot hfin c
  · rw [hz, map_zero]
    exact Submodule.zero_mem _

theorem potentialInverseAlternatedClosure_mem_nonnegative {n : ℕ} (hn : 0 < n)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (F : PlanarPiLebesgueL2 n)
    (hF : F ∈ (Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors n n
        V)).topologicalClosure) :
    (potentialPiVandermondeL2Equiv n hn hV.continuous hfin).symm F ∈
      potentialNonnegativePhaseClosedSpan n hn hV.continuous hrot hfin := by
  let E := (potentialPiVandermondeL2Equiv n hn hV.continuous hfin).symm
  let K := potentialNonnegativePhaseClosedSpan n hn hV.continuous hrot hfin
  let A := K.toSubmodule.comap E.toLinearEquiv.toLinearMap
  have ha : IsClosed (A : Set (PlanarPiLebesgueL2 n)) := K.isClosed.preimage E.continuous
  have hs : Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors n n V) ≤ A := by
    apply Submodule.span_le.mpr
    intro G hG
    exact potentialInverseAlternatedVector_mem_nonnegative hn hV hrot hfin G hG
  exact (Submodule.topologicalClosure_minimal _ hs ha) hF

theorem potentialHolomorphicQuotient_centered_mem_positive {d : ℕ}
    (hn : 0 < d + 1) {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition (d + 1) V < ⊤)
    (f : Configuration (d + 1) → ℝ) (hf : MemLp f 2 (potentialMeasure (d + 1) V))
    (hs : IsSymmetric f) :
    potentialHolomorphicQuotientProjection hn hV hfin
      (potentialCenteredL2 (d+1) hn hV.continuous hfin f hf) ∈
        potentialPositivePhaseClosedSpan (d+1) hV.continuous hrot := by
  apply potentialNonnegativePhase_mem_positive_of_orthogonal_constant
    (d+1) hn hV.continuous hrot hfin
  · have he := potentialInverseAlternatedClosure_mem_nonnegative hn hV hrot hfin _
      (potentialHolomorphicQuotient_centered_gauge_mem_alternated_closure hn hV hrot hfin f hf hs)
    simpa only [LinearIsometryEquiv.symm_apply_apply] using he
  · exact potentialHolomorphicQuotientProjection_centered_orthogonal_constant hn hV hrot hfin f hf 1

end
end GinibrePoincare
