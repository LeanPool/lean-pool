/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **cluster (host) graph** and the aggregation of the LP along it

The block-allocation route needs the fractional triangle packing LP of the regularity-reduced graph
`R = G.regularityReduced P ep de` to be compared with the LP of the *cluster* graph: the graph whose
vertices are the parts of `P` and whose edges are the uniform, dense cluster pairs.

* `Nibble.AX1.hostGraph` — the cluster graph, on the subtype of the parts of `P` (so that its vertex
  count is the number of clusters, not `2^|V|`);
* `Nibble.AX1.hostTri` — the cluster triple of a triangle;
* `Nibble.AX1.nu3star_regularityReduced_le_host` — **the aggregation**: if every cluster pair
  carries at most `c` edges then `ν₃*(R) ≤ c·ν₃*(cluster graph)`.  The proof aggregates a fractional
  packing of `R` along cluster triples; the per-cluster-pair capacity constraint
  (`Nibble.AX1.sum_fracPacking_cluster_pair_le`) is exactly the edge constraint of the aggregated
  weighting.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapPackingSplit
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterLP
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapBlowUp

/-! # CoreGapClusterHost -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### The cluster graph -/

/-- **The cluster graph** of `G` along `P` at scales `ep`, `de`: the vertices are the parts of `P`
and two distinct parts are joined when the pair is `ep`-uniform of density at least `de`. -/
def hostGraph (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finpartition (univ : Finset V))
    (ep de : ℝ) : SimpleGraph {S : Finset V // S ∈ P.parts} where
  Adj S T := (S : Finset V) ≠ (T : Finset V) ∧ G.IsUniform ep (S : Finset V) (T : Finset V) ∧
    de ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ)
  symm := ⟨by
    rintro S T ⟨h1, h2, h3⟩
    refine ⟨h1.symm, h2.symm, ?_⟩
    rwa [SimpleGraph.edgeDensity_comm]⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance hostGraph.instDecidableRelAdj (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) : DecidableRel (hostGraph G P ep de).Adj :=
  Classical.decRel _

theorem hostGraph_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finpartition (univ : Finset V)} {ep de : ℝ} {S T : {S : Finset V // S ∈ P.parts}} :
    (hostGraph G P ep de).Adj S T ↔ (S : Finset V) ≠ (T : Finset V) ∧
      G.IsUniform ep (S : Finset V) (T : Finset V) ∧
      de ≤ (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) := Iff.rfl

/-- The number of vertices of the cluster graph is the number of clusters. -/
theorem card_hostGraph_vertices (P : Finpartition (univ : Finset V)) :
    Fintype.card {S : Finset V // S ∈ P.parts} = #P.parts := Fintype.card_coe _

/-- The cluster of a vertex, as a vertex of the cluster graph. -/
def clusterOf (P : Finpartition (univ : Finset V)) (v : V) : {S : Finset V // S ∈ P.parts} :=
  ⟨P.part v, P.part_mem.mpr (mem_univ v)⟩

/-- **The cluster triple of a triangle**. -/
def hostTri (P : Finpartition (univ : Finset V)) (t : Finset V) :
    Finset {S : Finset V // S ∈ P.parts} := t.image (clusterOf P)

theorem image_hostTri (P : Finpartition (univ : Finset V)) (t : Finset V) :
    (hostTri P t).image Subtype.val = partClass P t := by
  classical
  rw [hostTri, partClass, Finset.image_image]
  rfl

/-- A triangle of a regularity-reduced graph has a cluster triple that is a triangle of the cluster
graph at the same scales. -/
theorem hostTri_mem_cliqueFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {t : Finset V}
    (ht : t ∈ (G.regularityReduced P ep de).cliqueFinset 3) :
    hostTri P t ∈ (hostGraph G P ep de).cliqueFinset 3 := by
  classical
  have htc : (G.regularityReduced P ep de).IsNClique 3 t :=
    SimpleGraph.mem_cliqueFinset_iff.mp ht
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp htc.card_eq
  have haxy : (G.regularityReduced P ep de).Adj x y := htc.1 (by simp) (by simp) hxy
  have haxz : (G.regularityReduced P ep de).Adj x z := htc.1 (by simp) (by simp) hxz
  have hayz : (G.regularityReduced P ep de).Adj y z := htc.1 (by simp) (by simp) hyz
  obtain ⟨U, W, X, hgood, hxU, hyW, hzX⟩ :=
    regularityReduced_triangle_parts G P ep de haxy haxz hayz
  obtain ⟨hUp, hWp, hXp, hUW, hUX, hWX, huUW, hdUW, huUX, hdUX, huWX, hdWX⟩ := hgood
  have h1 : P.part x = U := P.part_eq_of_mem hUp hxU
  have h2 : P.part y = W := P.part_eq_of_mem hWp hyW
  have h3 : P.part z = X := P.part_eq_of_mem hXp hzX
  have himg : hostTri P {x, y, z}
      = {(⟨U, hUp⟩ : {S : Finset V // S ∈ P.parts}), ⟨W, hWp⟩, ⟨X, hXp⟩} := by
    simp only [hostTri, Finset.image_insert, Finset.image_singleton]
    congr 1
    · exact Subtype.ext (by simp [clusterOf, h1])
    · congr 1
      · exact Subtype.ext (by simp [clusterOf, h2])
      · congr 1
        exact Subtype.ext (by simp [clusterOf, h3])
  rw [himg, SimpleGraph.mem_cliqueFinset_iff]
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab
        | exact ⟨hUW, huUW, hdUW⟩
        | exact ⟨hUX, huUX, hdUX⟩
        | exact ⟨hWX, huWX, hdWX⟩
        | exact ⟨hUW.symm, huUW.symm, by rwa [SimpleGraph.edgeDensity_comm]⟩
        | exact ⟨hUX.symm, huUX.symm, by rwa [SimpleGraph.edgeDensity_comm]⟩
        | exact ⟨hWX.symm, huWX.symm, by rwa [SimpleGraph.edgeDensity_comm]⟩
  · rw [Finset.card_insert_of_notMem (by simp [Subtype.ext_iff, hUW, hUX]),
      Finset.card_insert_of_notMem (by simp [Subtype.ext_iff, hWX]), Finset.card_singleton]

/-- Two clusters of the cluster triple of a triangle are joined by an edge of the triangle. -/
theorem exists_edge_of_mem_hostTri (P : Finpartition (univ : Finset V)) {t : Finset V}
    {S T : {S : Finset V // S ∈ P.parts}} (hST : S ≠ T)
    (hS : S ∈ hostTri P t) (hT : T ∈ hostTri P t) :
    ∃ x ∈ (S : Finset V), ∃ y ∈ (T : Finset V), ({x, y} : Finset V) ∈ t.powersetCard 2 := by
  classical
  rw [hostTri, Finset.mem_image] at hS hT
  obtain ⟨x, hx, hxS⟩ := hS
  obtain ⟨y, hy, hyT⟩ := hT
  have hxy : x ≠ y := by
    rintro rfl
    exact hST (hxS ▸ hyT ▸ rfl)
  refine ⟨x, ?_, y, ?_, ?_⟩
  · rw [← hxS]; exact P.mem_part (mem_univ x)
  · rw [← hyT]; exact P.mem_part (mem_univ y)
  · rw [Finset.mem_powersetCard]
    refine ⟨?_, by rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]⟩
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption

/-! ### The aggregation -/

/-- **Aggregating the LP along the cluster triples.**  If every cluster pair of `P` carries at most
`c` edges of `G`, then the fractional triangle packing number of the regularity-reduced graph is at
most `c` times that of the cluster graph.

The aggregated weighting gives a cluster triple the total weight of the triangles lying on it,
scaled by `1/c`; the capacity constraint of a cluster pair
(`Nibble.AX1.sum_fracPacking_cluster_pair_le`) is exactly the edge constraint of the aggregate. -/
theorem nu3star_regularityReduced_le_host (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {c : ℝ} (hc : 0 < c)
    (hcap : ∀ S ∈ P.parts, ∀ T ∈ P.parts, S ≠ T → (#(G.interedges S T) : ℝ) ≤ c) :
    nu3star (G.regularityReduced P ep de) ≤ c * nu3star (hostGraph G P ep de) := by
  classical
  set R : SimpleGraph V := G.regularityReduced P ep de with hR
  set Hst : SimpleGraph {S : Finset V // S ∈ P.parts} := hostGraph G P ep de with hHst
  refine csSup_le ⟨0, ⟨fun _ => 0, isFracPacking_zero R, by simp⟩⟩ ?_
  rintro x ⟨w, hw, rfl⟩
  -- the aggregate weighting of the cluster triples
  set val : Finset {S : Finset V // S ∈ P.parts} → ℝ := fun th =>
    (∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t = th), w (t.powersetCard 2)) / c
    with hvaldef
  set wH : Finset (Finset {S : Finset V // S ∈ P.parts}) → ℝ := fun T =>
    if T ∈ triangleHypergraphE Hst then val (vtxSet T) else 0 with hwHdef
  have hval0 : ∀ th, 0 ≤ val th := fun th =>
    div_nonneg (Finset.sum_nonneg fun t _ => hw.1 _) hc.le
  -- the sum over a set of cluster triples is a sum over the triangles lying on them
  have hfiber : ∀ A : Finset (Finset {S : Finset V // S ∈ P.parts}),
      A ⊆ Hst.cliqueFinset 3 →
      ∑ th ∈ A, (∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t = th),
            w (t.powersetCard 2))
        = ∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t ∈ A), w (t.powersetCard 2) := by
    intro A hA
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := hostTri P) (s := (R.cliqueFinset 3).filter (fun t => hostTri P t ∈ A)) (t := A)
      (fun t ht => (Finset.mem_filter.mp ht).2) (fun t => w (t.powersetCard 2))]
    refine Finset.sum_congr rfl fun th hth => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, rfl⟩; exact ⟨⟨ht, hth⟩, rfl⟩
    · rintro ⟨⟨ht, -⟩, hEq⟩; exact ⟨ht, hEq⟩
  -- the capacity constraint of a cluster pair
  have hpair : ∀ Sv Tv : {S : Finset V // S ∈ P.parts}, Sv ≠ Tv →
      ∑ t ∈ (R.cliqueFinset 3).filter (fun t => Sv ∈ hostTri P t ∧ Tv ∈ hostTri P t),
        w (t.powersetCard 2) ≤ c := by
    intro Sv Tv hST
    set C := (R.cliqueFinset 3).filter (fun t => Sv ∈ hostTri P t ∧ Tv ∈ hostTri P t) with hC
    have hinj : Set.InjOn (fun t : Finset V => t.powersetCard 2) (C : Set (Finset V)) :=
      (triangle_powersetCard_two_injOn R).mono (by
        intro t ht
        exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1)
    have himg : ∑ t ∈ C, w (t.powersetCard 2)
        = ∑ T ∈ C.image (fun t => t.powersetCard 2), w T := (Finset.sum_image hinj).symm
    have hsub : C.image (fun t => t.powersetCard 2)
        ⊆ (triangleHypergraphE R).filter
          (fun T => ∃ x ∈ (Sv : Finset V), ∃ y ∈ (Tv : Finset V), ({x, y} : Finset V) ∈ T) := by
      intro T hT
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hT
      rw [Finset.mem_filter] at ht
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_image_of_mem _ ht.1, ?_⟩
      exact exists_edge_of_mem_hostTri P hST ht.2.1 ht.2.2
    have hmono : ∑ T ∈ C.image (fun t => t.powersetCard 2), w T
        ≤ ∑ T ∈ (triangleHypergraphE R).filter
            (fun T => ∃ x ∈ (Sv : Finset V), ∃ y ∈ (Tv : Finset V), ({x, y} : Finset V) ∈ T), w T :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun T _ _ => hw.1 T
    have hcapR := sum_fracPacking_cluster_pair_le R hw (Sv : Finset V) (Tv : Finset V)
    have hmono2 : (#(R.interedges (Sv : Finset V) (Tv : Finset V)) : ℝ)
        ≤ (#(G.interedges (Sv : Finset V) (Tv : Finset V)) : ℝ) := by
      exact_mod_cast card_interedges_mono (G := G) (H := R)
        (hR ▸ SimpleGraph.regularityReduced_le) (Sv : Finset V) (Tv : Finset V)
    have hcapG := hcap (Sv : Finset V) Sv.2 (Tv : Finset V) Tv.2 fun h => hST (Subtype.ext h)
    rw [himg]
    linarith
  -- the aggregate is a fractional packing of the cluster graph
  have hpack : IsFracPacking Hst wH := by
    refine ⟨fun T => ?_, fun T hT => ?_, fun e => ?_⟩
    · rw [hwHdef]; dsimp only; split_ifs
      · exact hval0 _
      · exact le_rfl
    · rw [hwHdef]; dsimp only; rw [ite_eq_right hT]
    · by_cases he2 : #e = 2
      swap
      · have hemp : (triangleHypergraphE Hst).filter (fun T => e ∈ T) = ∅ := by
          ext T
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hT heT
          rw [triangleHypergraphE, Finset.mem_image] at hT
          obtain ⟨th, hth, rfl⟩ := hT
          rw [Finset.mem_powersetCard] at heT
          exact he2 heT.2
        rw [hemp, Finset.sum_empty]; norm_num
      obtain ⟨Sv, Tv, hST, rfl⟩ := Finset.card_eq_two.mp he2
      rw [sum_triangleHypergraphE_filter Hst he2 wH]
      have hstep : ∀ th ∈ (Hst.cliqueFinset 3).filter
          (fun th => ({Sv, Tv} : Finset {S : Finset V // S ∈ P.parts}) ⊆ th),
          wH (th.powersetCard 2) = val th := by
        intro th hth
        rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hth
        have hmem : th.powersetCard 2 ∈ triangleHypergraphE Hst := by
          rw [triangleHypergraphE, Finset.mem_image]
          exact ⟨th, SimpleGraph.mem_cliqueFinset_iff.mpr hth.1, rfl⟩
        rw [hwHdef]
        dsimp only
        rw [ite_eq_left hmem, vtxSet_powersetCard_two (by rw [hth.1.card_eq]; norm_num)]
      rw [Finset.sum_congr rfl hstep]
      have hAsub : (Hst.cliqueFinset 3).filter
          (fun th => ({Sv, Tv} : Finset {S : Finset V // S ∈ P.parts}) ⊆ th)
          ⊆ Hst.cliqueFinset 3 := Finset.filter_subset _ _
      have hsum : ∑ th ∈ (Hst.cliqueFinset 3).filter
            (fun th => ({Sv, Tv} : Finset {S : Finset V // S ∈ P.parts}) ⊆ th), val th
          = (∑ t ∈ (R.cliqueFinset 3).filter (fun t => hostTri P t ∈
              (Hst.cliqueFinset 3).filter
                (fun th => ({Sv, Tv} : Finset {S : Finset V // S ∈ P.parts}) ⊆ th)),
              w (t.powersetCard 2)) / c := by
        rw [← hfiber _ hAsub, hvaldef, ← Finset.sum_div]
      rw [hsum, div_le_one hc]
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun t _ _ => hw.1 _))
        (hpair Sv Tv hST)
      intro t ht
      rw [Finset.mem_filter] at ht ⊢
      refine ⟨ht.1, ?_, ?_⟩
      · exact (Finset.mem_filter.mp ht.2).2 (by simp)
      · exact (Finset.mem_filter.mp ht.2).2 (by simp)
  -- the value of the aggregate
  have htot : ∑ T ∈ triangleHypergraphE Hst, wH T
      = (∑ T ∈ triangleHypergraphE R, w T) / c := by
    rw [sum_triangleHypergraphE Hst wH, sum_triangleHypergraphE R w]
    have hstep : ∀ th ∈ Hst.cliqueFinset 3, wH (th.powersetCard 2) = val th := by
      intro th hth
      rw [SimpleGraph.mem_cliqueFinset_iff] at hth
      have hmem : th.powersetCard 2 ∈ triangleHypergraphE Hst := by
        rw [triangleHypergraphE, Finset.mem_image]
        exact ⟨th, SimpleGraph.mem_cliqueFinset_iff.mpr hth, rfl⟩
      rw [hwHdef]
      dsimp only
      rw [ite_eq_left hmem, vtxSet_powersetCard_two (by rw [hth.card_eq]; norm_num)]
    rw [Finset.sum_congr rfl hstep, hvaldef, ← Finset.sum_div]
    congr 1
    rw [hfiber (Hst.cliqueFinset 3) (Finset.Subset.refl _)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    refine Finset.filter_true_of_mem fun t ht => ?_
    exact hostTri_mem_cliqueFinset G P ep de ht
  have hle : ∑ T ∈ triangleHypergraphE Hst, wH T ≤ nu3star Hst :=
    le_csSup (nu3star_bddAbove Hst) ⟨wH, hpack, rfl⟩
  rw [htot, div_le_iff₀ hc] at hle
  linarith only [hle]

/-! ### Axiom check -/

section AxCheck




end AxCheck

end Nibble.AX1
