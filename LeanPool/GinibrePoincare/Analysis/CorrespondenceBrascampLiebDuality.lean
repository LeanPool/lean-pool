/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceBrascampLiebDuality.lean.
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
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.MetricSpace.Isometry
/-!
# Correspondence Brascamp Lieb duality

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `correspondenceBrascampLieb_duality`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section

/-- Hilbert-space duality used after the concrete Gibbs compact-generator
range has been proved dense in the centered subspace. -/
theorem correspondenceBrascampLieb_duality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : H) (D : Set H) (energy : ℝ) (henergy : 0 ≤ energy) (hu : u ∈ closure D)
    (hbound : ∀ v ∈ D, (inner ℝ u v) ^ 2 ≤ energy * ‖v‖ ^ 2) :
    ‖u‖^2 ≤ energy := by
  let K : Set H := {v | (inner ℝ u v)^2 ≤ energy * ‖v‖^2}
  have hK : IsClosed K := by
    exact isClosed_le ((continuous_const.inner continuous_id).pow 2)
      (continuous_const.mul (continuous_norm.pow 2))
  have hDK : D ⊆ K := fun v hv => hbound v hv
  have hUK : u ∈ K := (closure_minimal hDK hK) hu
  change (inner ℝ u u)^2 ≤ energy * ‖u‖^2 at hUK
  rw [real_inner_self_eq_norm_sq] at hUK
  by_cases hz : ‖u‖^2 = 0
  · simpa [hz] using henergy
  · have hp : 0 < ‖u‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    nlinarith
end
end GinibrePoincare
