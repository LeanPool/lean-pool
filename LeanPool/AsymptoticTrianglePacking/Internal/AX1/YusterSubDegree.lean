/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Yuster (edge-based) — cardinality and degree-sum of `triangleHypergraphSub`

Standalone, Mathlib-only. Foundation of the edge-based near-regularity (②a). The edge-vertex-type
triangle hypergraph `triangleHypergraphSub G` has exactly `|cliqueFinset 3|` = `#triangles` hyperedges
(the powerset-subtype map is injective on 3-cliques), and — being `3`-uniform — its degree sum over the
edge vertices is `3·#triangles` (handshake). This pins the AVERAGE edge triangle-degree at
`3·#triangles / |E(G)|`, the anchor for "most edges are near-regular".

* `triangleHypergraphSub_card` — `|triangleHypergraphSub G| = |cliqueFinset 3 G|`.
* `sum_degree_triangleHypergraphSub` — `∑_E deg_E = 3·|cliqueFinset 3 G|`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdge
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterEdgeType
public import Mathlib.Algebra.Order.Ring.Star

/-! # YusterSubDegree -/

@[expose] public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **`|triangleHypergraphSub| = #triangles`.** The powerset-subtype map is injective on 3-cliques
(distinct triangles have distinct edge-sets), so the image has the same cardinality. -/
theorem triangleHypergraphSub_card :
    (triangleHypergraphSub G).card = (G.cliqueFinset 3).card := by
  rw [triangleHypergraphSub, Finset.card_image_of_injOn]
  intro t ht t' ht' heq
  rw [Finset.mem_coe, SimpleGraph.mem_cliqueFinset_iff] at ht ht'
  have h1 : t.powersetCard 2 = t'.powersetCard 2 := by
    have e1 := Finset.subtype_map_of_mem (powersetCard_two_subset_cliqueFinset G ht)
    have e2 := Finset.subtype_map_of_mem (powersetCard_two_subset_cliqueFinset G ht')
    rw [← e1, ← e2]
    exact congrArg (Finset.map _) heq
  exact powersetCard_two_inj (by rw [ht.card_eq]; norm_num) (by rw [ht'.card_eq]; norm_num) h1

/-- **Degree-sum (handshake) for the edge-based triangle hypergraph.** As `triangleHypergraphSub G`
is `3`-uniform, `∑_{E} deg_E = 3·|triangleHypergraphSub| = 3·#triangles`. The average edge
triangle-degree is `3·#triangles / |E(G)|`. -/
theorem sum_degree_triangleHypergraphSub :
    ∑ E : EdgeV G, degree (triangleHypergraphSub G) E = 3 * (G.cliqueFinset 3).card := by
  rw [Hypergraph.sum_degree (triangleHypergraphSub G) (triangleHypergraphSub_uniform G),
    triangleHypergraphSub_card]

end Nibble.YusterE
