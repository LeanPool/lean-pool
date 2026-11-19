/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialQuotientVariance.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialProjectionRealVariance
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialPositivePhaseClosure

/-!
# General potential quotient variance

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialVariance_le_two_quotient_residual_of_positive`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Hilbert geometry for an actual centered observable whose projected vector
lies in the genuine closed positive-character space. -/
theorem potentialVariance_le_two_quotient_residual_of_positive {d : ℕ}
    (hn : 0 < d + 1) {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition (d + 1) V < ⊤)
    (f : Configuration (d + 1) → ℝ) (hf : MemLp f 2 (potentialMeasure (d + 1) V))
    (hp : potentialHolomorphicQuotientProjection hn hV hfin
      (potentialCenteredL2 (d + 1) hn hV.continuous hfin f hf) ∈
        potentialPositivePhaseClosedSpan (d + 1) hV.continuous hrot) :
    potentialVariance (d+1) V f ≤ 2 *
      ‖potentialCenteredL2 (d+1) hn hV.continuous hfin f hf -
        potentialHolomorphicQuotientProjection hn hV hfin
          (potentialCenteredL2 (d+1) hn hV.continuous hfin f hf)‖ ^ 2 := by
  rw [← potentialCenteredL2_norm_sq (d+1) hn hV.continuous hfin f hf]
  apply real_Lp_projection_norm_sq_le_two_residual
    (potentialMeasure (d+1) V) (potentialHolomorphicQuotientProjection hn hV hfin)
    (potentialHolomorphicQuotientProjection_adjoint hn hV hfin)
    (potentialHolomorphicQuotientProjection_idempotent hn hV hfin)
    _ (potentialCenteredL2_star (d+1) hn hV.continuous hfin f hf)
  exact potentialPositivePhaseClosedSpan_inner_star_zero hV.continuous hrot _ _ hp hp

end
end GinibrePoincare
