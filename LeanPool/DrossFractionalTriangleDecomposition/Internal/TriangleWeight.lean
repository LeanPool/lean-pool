/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.FlowSaturation

/-!
# Triangle weights reconstructed from Dross's flow

Each rooted K₄ transfer adjusts the common initial triangle weight. Subsequent
lemmas show that the weights are nonnegative and cover every graph edge.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weight of a triangle after all rooted-K₄ transfers in the auxiliary flow. -/
@[expose] public noncomputable def triWeight (G : SimpleGraph V) [DecidableRel G.Adj]
    (wΔ : ℝ) (F : Contrib.MaxFlowMinCut.Flow (drossNet G wΔ)) (t : Finset V) : ℝ :=
  if t ∈ G.cliqueFinset 3 then
    wΔ - (1 / 2) * ∑ e ∈ triEdges t, ∑ e' : Sym2 V,
      (if K4pair G e e' ∧ ∃ v, v ∈ t ∧ v ∈ e' ∧ v ∉ e then
        F.f (Ghat.edge e) (Ghat.edge e') else 0)
  else 0

end LeanPool.DrossFractionalTriangleDecomposition
