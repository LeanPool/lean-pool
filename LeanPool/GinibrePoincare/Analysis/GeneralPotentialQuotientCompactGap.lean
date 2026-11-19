/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialQuotientCompactGap.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialCompactLift
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialQuotientProjection

/-!
# General potential quotient compact gap

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialHolomorphicQuotientProjection_compact_gap`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Actual source-space quotient-projection residual bound, with the exact
subharmonic constant and the genuine compact observable lift. -/
theorem potentialHolomorphicQuotientProjection_compact_gap {d : ℕ}
    (hn : 0 < d + 1) (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hsub : IsRhoSubharmonicPotential ρ V) (hfin : potentialPartition (d + 1) V < ⊤)
    (f : Configuration (d + 1) → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let hmem := potentialSmoothCompact_memLp (d+1) hn hV.continuous hfin f hf.continuous hc
    let u := hmem.ofReal.toLp (fun z => (f z : ℂ))
    ‖u - potentialHolomorphicQuotientProjection hn hV hfin u‖ ^ 2 ≤
      (1 / (2 * ((d+1 : ℕ) : ℝ) * ρ)) * potentialGradientEnergy (d+1) V f := by
  dsimp only
  rw [potentialHolomorphicQuotientProjection_residual_norm]
  have hg := potentialVandermonde_compact_projection_gap ρ hρ hV hsub hfin f hf hc
  have he := potentialVandermonde_compact_graph_value hn hV hfin f hf hc
  dsimp only at hg he
  change _ = potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin
    ((potentialSmoothCompact_memLp (d+1) hn hV.continuous hfin f hf.continuous hc).ofReal.toLp
      (fun z => (f z : ℂ))) at he
  rw [he] at hg
  exact hg

end
end GinibrePoincare
