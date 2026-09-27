/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — splitting the LP value along cluster triples

Second half of the `ν₃*` bookkeeping of the AX1 residual (`RESIDUAL.md`, §2, (R2)).  In a
regularity-reduced graph every triangle has its three vertices in three *distinct* parts
(`Nibble.AX1.regularityReduced_triangle_parts`), so the triangles are classified by the triple of
parts they live on.  This file records the two facts about that classification that the assembly of
`ReducedFamilyResidual` needs.

* `Nibble.AX1.partClass` — the triple of parts of a triangle.
* `Nibble.AX1.sum_split_partClass` — **the value splits**: the objective of a fractional packing is
  the sum, over triples of parts, of the weight it puts on that triple.
* `Nibble.AX1.sum_pair_classes_le` — **the per-pair constraint**: for two distinct parts `U`, `W`,
  the total weight put on the triples containing both is at most the number of `U–W` edges.  This is
  what makes the allocation of a pair among its triples feasible.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapPackingEdges
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterBridgeFrac
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRegularCover

/-! # CoreGapPackingSplit -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The set of parts of `P` met by `t`.  For a triangle of a regularity-reduced graph this is a
triple of distinct parts. -/
def partClass (P : Finpartition (univ : Finset V)) (t : Finset V) : Finset (Finset V) :=
  t.image P.part

theorem mem_partClass_iff (P : Finpartition (univ : Finset V)) (t : Finset V) (U : Finset V) :
    U ∈ partClass P t ↔ ∃ x ∈ t, P.part x = U := by
  simp [partClass]

theorem partClass_subset_parts (P : Finpartition (univ : Finset V)) (t : Finset V) :
    partClass P t ⊆ P.parts := by
  intro U hU
  obtain ⟨x, -, rfl⟩ := (mem_partClass_iff P t U).mp hU
  exact P.part_mem.mpr (mem_univ x)

theorem partClass_mem_powersetCard_three (P : Finpartition (univ : Finset V)) {t : Finset V}
    (h3 : #(partClass P t) = 3) : partClass P t ∈ P.parts.powersetCard 3 :=
  Finset.mem_powersetCard.mpr ⟨partClass_subset_parts P t, h3⟩

/-- In a regularity-reduced graph every triangle meets exactly three parts: this is the hypothesis
of `Nibble.AX1.sum_split_partClass`, discharged. -/
theorem partClass_card_three_of_isNClique (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {t : Finset V}
    (ht : (G.regularityReduced P ep de).IsNClique 3 t) : #(partClass P t) = 3 := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  have haxy : (G.regularityReduced P ep de).Adj x y := ht.1 (by simp) (by simp) hxy
  have haxz : (G.regularityReduced P ep de).Adj x z := ht.1 (by simp) (by simp) hxz
  have hayz : (G.regularityReduced P ep de).Adj y z := ht.1 (by simp) (by simp) hyz
  obtain ⟨U, W, X, hgood, hxU, hyW, hzX⟩ :=
    regularityReduced_triangle_parts G P ep de haxy haxz hayz
  obtain ⟨hUp, hWp, hXp, hUW, hUX, hWX, -⟩ := hgood
  have h1 : P.part x = U := P.part_eq_of_mem hUp hxU
  have h2 : P.part y = W := P.part_eq_of_mem hWp hyW
  have h3 : P.part z = X := P.part_eq_of_mem hXp hzX
  have himg : partClass P {x, y, z} = {U, W, X} := by
    simp [partClass, Finset.image_insert, h1, h2, h3]
  rw [himg, Finset.card_insert_of_notMem (by simp [hUW, hUX]),
    Finset.card_insert_of_notMem (by simp [hWX]), Finset.card_singleton]

/-- **The objective splits along the triples of parts.**  If every triangle of `G` meets three
distinct parts of `P` — which is the case for a regularity-reduced graph, by
`Nibble.AX1.regularityReduced_triangle_parts` — then the sum of any weight function over the
triangles is the sum, over triples of parts, of its weight on that triple. -/
theorem sum_split_partClass (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (f : Finset V → ℝ)
    (hdist : ∀ t ∈ G.cliqueFinset 3, #(partClass P t) = 3) :
    ∑ S ∈ P.parts.powersetCard 3,
        ∑ t ∈ (G.cliqueFinset 3).filter (fun t => partClass P t = S), f t
      = ∑ t ∈ G.cliqueFinset 3, f t :=
  Finset.sum_fiberwise_of_maps_to
    (fun t ht => partClass_mem_powersetCard_three P (hdist t ht)) f

/-- **The per-pair LP constraint.**  For two distinct parts `U ≠ W`, a fractional triangle packing
puts total weight at most `e(U, W)` on the triangles whose triple of parts contains both `U`
and `W`. -/
theorem sum_pair_classes_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {w : Finset (Finset V) → ℝ} (hw : IsFracPacking G w)
    (hdist : ∀ t ∈ G.cliqueFinset 3, #(partClass P t) = 3) {U W : Finset V} (hUW : U ≠ W) :
    ∑ S ∈ (P.parts.powersetCard 3).filter (fun S => U ∈ S ∧ W ∈ S),
        ∑ t ∈ (G.cliqueFinset 3).filter (fun t => partClass P t = S), w (t.powersetCard 2)
      ≤ (#(G.interedges U W) : ℝ) := by
  classical
  have hnn : ∀ T, 0 ≤ w T := hw.1
  set s' := (G.cliqueFinset 3).filter (fun t => U ∈ partClass P t ∧ W ∈ partClass P t) with hs'
  -- the inner sums only ever see triangles of `s'`
  have hfib : ∑ S ∈ (P.parts.powersetCard 3).filter (fun S => U ∈ S ∧ W ∈ S),
      ∑ t ∈ (G.cliqueFinset 3).filter (fun t => partClass P t = S), w (t.powersetCard 2)
      = ∑ t ∈ s', w (t.powersetCard 2) := by
    have hcongr : ∀ S ∈ (P.parts.powersetCard 3).filter (fun S => U ∈ S ∧ W ∈ S),
        (G.cliqueFinset 3).filter (fun t => partClass P t = S)
          = s'.filter (fun t => partClass P t = S) := by
      intro S hS
      rw [Finset.mem_filter] at hS
      ext t
      simp only [hs', Finset.mem_filter]
      constructor
      · rintro ⟨ht, rfl⟩; exact ⟨⟨ht, hS.2.1, hS.2.2⟩, rfl⟩
      · rintro ⟨⟨ht, -, -⟩, hEq⟩; exact ⟨ht, hEq⟩
    rw [Finset.sum_congr rfl (fun S hS => by rw [hcongr S hS])]
    refine Finset.sum_fiberwise_of_maps_to (fun t ht => ?_) _
    rw [Finset.mem_filter]
    refine ⟨partClass_mem_powersetCard_three P (hdist t (Finset.mem_filter.mp (hs' ▸ ht)).1), ?_⟩
    exact ⟨(Finset.mem_filter.mp (hs' ▸ ht)).2.1, (Finset.mem_filter.mp (hs' ▸ ht)).2.2⟩
  rw [hfib]
  -- pass to the edge-set picture and use the packing constraint on the `U–W` edges
  set E : Finset (Finset V) :=
    (G.interedges U W).image (fun p : V × V => ({p.1, p.2} : Finset V)) with hE
  have hinj : Set.InjOn (fun t : Finset V => t.powersetCard 2) (s' : Set (Finset V)) := by
    refine (triangle_powersetCard_two_injOn G).mono ?_
    intro t ht
    exact Finset.mem_coe.mpr (Finset.mem_filter.mp (hs' ▸ Finset.mem_coe.mp ht)).1
  have himg : ∑ t ∈ s', w (t.powersetCard 2)
      = ∑ T ∈ s'.image (fun t => t.powersetCard 2), w T := (Finset.sum_image hinj).symm
  have hsub : s'.image (fun t => t.powersetCard 2)
      ⊆ (triangleHypergraphE G).filter (fun T => ∃ e ∈ E, e ∈ T) := by
    intro T hT
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hT
    have ht3 : t ∈ G.cliqueFinset 3 := (Finset.mem_filter.mp (hs' ▸ ht)).1
    have hclique : G.IsNClique 3 t := SimpleGraph.mem_cliqueFinset_iff.mp ht3
    obtain ⟨x, hxt, hxU⟩ := (mem_partClass_iff P t U).mp (Finset.mem_filter.mp (hs' ▸ ht)).2.1
    obtain ⟨y, hyt, hyW⟩ := (mem_partClass_iff P t W).mp (Finset.mem_filter.mp (hs' ▸ ht)).2.2
    have hxU' : x ∈ U := hxU ▸ P.mem_part (mem_univ x)
    have hyW' : y ∈ W := hyW ▸ P.mem_part (mem_univ y)
    have hxy : x ≠ y := by
      rintro rfl
      exact hUW (hxU ▸ hyW ▸ rfl)
    have hadj : G.Adj x y := hclique.1 hxt hyt hxy
    refine Finset.mem_filter.mpr ⟨?_, ⟨({x, y} : Finset V), ?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨t, ht3, rfl⟩
    · refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
      rw [SimpleGraph.mem_interedges_iff]
      exact ⟨hxU', hyW', hadj⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair hxy⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact hxt
      · rw [Finset.mem_singleton] at hz'; exact hz' ▸ hyt
  calc ∑ t ∈ s', w (t.powersetCard 2)
      = ∑ T ∈ s'.image (fun t => t.powersetCard 2), w T := himg
    _ ≤ ∑ T ∈ (triangleHypergraphE G).filter (fun T => ∃ e ∈ E, e ∈ T), w T :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ => hnn T)
    _ ≤ (#E : ℝ) := sum_fracPacking_over_edges_le G hw E
    _ ≤ (#(G.interedges U W) : ℝ) := by
        exact_mod_cast Finset.card_image_le

end Nibble.AX1
