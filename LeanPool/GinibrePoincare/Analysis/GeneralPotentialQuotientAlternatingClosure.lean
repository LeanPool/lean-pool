/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialQuotientAlternatingClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialQuotientProjection
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialProjectionGeometry
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticAlternatingMonomialClosure

/-!
# General potential quotient alternating closure

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialHolomorphicQuotient_centered_gauge_mem_alternated_closure`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem potentialHolomorphicQuotient_centered_gauge_mem_alternated_closure {d : ℕ}
    (hn : 0 < d + 1) {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition (d + 1) V < ⊤)
    (f : Configuration (d + 1) → ℝ) (hf : MemLp f 2 (potentialMeasure (d + 1) V))
    (hs : IsSymmetric f) :
    potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin
      (potentialHolomorphicQuotientProjection hn hV hfin
        (potentialCenteredL2 (d+1) hn hV.continuous hfin f hf)) ∈
      (Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors (d+1) (d+1)
          V)).topologicalClosure := by
  rw [potentialHolomorphicQuotientProjection_gauge]
  apply planarPiBergman_alternating_mem_alternated_monomial_closure
    (d+1) V hV (fun a ha z => hrot a z ha)
  intro e
  exact potentialVandermondeCentered_alternating (d+1) hn hV.continuous hfin f hf hs e

end
end GinibrePoincare
