/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.PeelingLift

/-!
# Dross's fractional triangle decomposition theorem

If a finite graph has minimum degree at least nine tenths of its order, its
edges admit an exact fractional decomposition into triangles. The proof
peels high-degree triangles until the exact flow argument applies.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Dross's theorem at the exact `9/10` minimum-degree threshold. -/
public theorem dross_fractional_flow_exact (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) :
    FractionalTriangleDecomp G := by
  classical
  induction m : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hNoHDT : ∀ u v w : V, G.Adj u v → G.Adj u w → G.Adj v w →
        G.minDegree + 2 ≤ G.degree u → G.minDegree + 2 ≤ G.degree v →
        G.minDegree + 2 ≤ G.degree w → False
    · exact dross_fractional_flow_noHDT_exact G h hNoHDT
    · push Not at hNoHDT
      obtain ⟨u, v, w, huv, huw, hvw, hu, hv, hw, _⟩ := hNoHDT
      let G' := G.deleteEdges (triEdges {u, v, w})
      have hmin : G'.minDegree = G.minDegree :=
        peeled_heavy_triangle_minDegree G hu hv hw
      have hlt : G'.edgeFinset.card < G.edgeFinset.card :=
        peeled_heavy_triangle_fewer_edges G huv huw hvw
      have hdec : FractionalTriangleDecomp G' := by
        apply ih G'.edgeFinset.card (by omega) G'
        · simpa [hmin] using h
        · rfl
      exact lift_fractional_decomp_triangle G huv huw hvw hdec

end LeanPool.DrossFractionalTriangleDecomposition
