/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianInitialDensityCancellation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInteractionPotential

/-!
# Ginibre Hamiltonian initial density cancellation

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreInteraction_initial_action_cancellation`.
-/

@[expose] public section

namespace GinibrePoincare
noncomputable section

/-- The genuine interaction likelihood initial factor cancels the
Vandermonde density of Ginibre relative to its Gaussian reference. -/
theorem ginibreInteraction_initial_density_cancellation {n : ℕ}
    (z : Configuration n) (hz : CollisionFree z) :
    vandermondeWeight z * Real.exp (ginibreInteractionPotential n z) = 1 := by
  rw [ginibreInteractionPotential, Real.exp_neg,
    Real.exp_log (vandermondeWeight_pos_of_collisionFree z hz)]
  exact mul_inv_cancel₀ (ne_of_gt (vandermondeWeight_pos_of_collisionFree z hz))

theorem ginibreInteraction_initial_action_cancellation {n : ℕ}
    (z : Configuration n) (hz : CollisionFree z) (action : ℝ) :
    vandermondeWeight z * (Real.exp (ginibreInteractionPotential n z) * action) = action := by
  rw [← mul_assoc, ginibreInteraction_initial_density_cancellation z hz, one_mul]

end
end GinibrePoincare
