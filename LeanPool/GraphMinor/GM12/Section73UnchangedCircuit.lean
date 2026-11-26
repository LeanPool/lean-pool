/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CommonCircuitInside
public import LeanPool.GraphMinor.GM12.Section73EdgeWalkLift
import LeanPool.GraphMinor.GM11.CircuitRegions
import LeanPool.GraphMinor.GM11.RadialRegions

/-!
# Circuits that avoid the merged hub

For the first case of XII (7.3), Claim (1), page 262, a circuit
avoiding the merged hub misses the merged region altogether.
Its edges are unchanged old edges. Equality of the two walk point
sets outside that region then places the circuit in the lifted
walk. Its selected inside is unchanged, as proved by the disc
separation argument.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 Hypergraph

/-- A radial subdrawing omitting a region's hub misses that whole
region. This is the geometric reason that the unchanged-circuit
case of XII (7.3), Claim (1), lies outside the merged region. -/
theorem subdrawing_disjoint_region_of_notMem_hub
    {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Γ J C : Drawing S}
    (hJ : PreRad (PaintingOrDrawing.drawing Γ) J)
    {r : Set S} (hr : r ∈ Γ.R) {v : S} (hvr : v ∈ r) (hvJ : v ∈ J.V)
    (hCJ : C.IsSubdrawing J) (hvC : v ∉ C.V) : Disjoint C.U r := by
  apply disjoint_left.mpr
  intro x hxC hxr
  by_cases hxV : x ∈ C.V
  · have hxv := hub_unique hJ hr hvr hvJ hxr (hCJ.1 hxV)
    exact hvC (hxv ▸ hxV)
  · obtain ⟨e, he, hxe⟩ := C.exists_edge_of_mem hxC hxV
    obtain ⟨u, _, q, hq, w, hwq, hwJ, hcap, heq⟩ := spoke_ends hJ hS (hCJ.2 he)
    have hqr : q = r := region_eq_of_mem hq hr (heq hxe) hxr
    have hwv := hub_unique hJ hr hvr hvJ (hqr ▸ hwq) hwJ
    have hwC : w ∈ C.V := by
      have hw : w ∈ closure e ∩ J.V := hcap.superset (Or.inr rfl)
      rw [← hCJ.closure_inter_V he] at hw
      exact hw.2
    exact hvC (hwv ▸ hwC)

/-- Inside one drawing, inclusion of underlying point sets implies
inclusion of subdrawings. Vertices are recovered by intersecting
with the ambient vertices; an absent edge misses the smaller
underlying point set. -/
theorem isSubdrawing_of_U_subset_common
    {S : Type*} [TopologicalSpace S] {K C N : Drawing S}
    (hCK : C.IsSubdrawing K) (hNK : N.IsSubdrawing K) (hU : C.U ⊆ N.U) :
    C.IsSubdrawing N := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact (isSubdrawing_U_inter_V hNK).subset ⟨hU (C.V_subset_U hx), hCK.1 hx⟩
  · intro e he
    by_contra hen
    obtain ⟨x, hxe⟩ := he.1
    exact disjoint_left.mp (edge_disjoint_U hNK (hCK.2 he) hen) hxe
      (hU ((he.2.1 hxe).1))

/-- A subdrawing omitting the contracted vertex is an old
subdrawing whenever all its incident edge replacements have length
one. This identifies the unchanged circuits in XII (7.3). -/
theorem isSubdrawing_of_retained_edges
    {S : Type*} [TopologicalSpace S] {K J C : Drawing S} {v : S}
    (hV : J.V ⊆ K.V)
    (hretain : ∀ e x y, J.toGraph.IsLink e x y → x ≠ v → y ≠ v → e ∈ K.E)
    (hCJ : C.IsSubdrawing J) (hvC : v ∉ C.V) : C.IsSubdrawing K := by
  refine ⟨hCJ.1.trans hV, ?_⟩
  intro e he
  obtain ⟨x, y, hxy⟩ := (C.toGraph.edge_mem_iff_exists_isLink e).mp he
  exact hretain e x y ((hCJ.isLink_iff he).mp hxy)
    (fun hxv => hvC (hxv ▸ hxy.2.1)) (fun hyv => hvC (hyv ▸ hxy.2.2.1))

/-- A path avoiding the merged hub lifts with the same vertex and
edge lists, and all its vertices lie outside the merged region.
This lifts the retained part of the circuit in XII (7.3),
Claim (1), page 262. -/
theorem exists_unchanged_path_lift
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ J K : Drawing S}
    (hJ : PreRad (PaintingOrDrawing.drawing Γ) J)
    {r : Set S} (hr : r ∈ Γ.R) {v : S} (hvr : v ∈ r) (hvJ : v ∈ J.V)
    (hV : J.V ⊆ K.V)
    (hretain : ∀ e x y, J.toGraph.IsLink e x y → x ≠ v → y ≠ v → e ∈ K.E)
    {x y : S} (P : GraphWalk J.toGraph x y) (hvP : v ∉ P.support) :
    ∃ Q : GraphWalk K.toGraph x y, Q.support = P.support ∧ Q.edges = P.edges ∧
      ∀ z ∈ Q.support, z ∉ r := by
  have hPJ := walkDrawing_isSubdrawing J P
  have hvDraw : v ∉ (walkDrawing J P).V := by
    rw [walkDrawing_V]
    exact hvP
  have hPK := isSubdrawing_of_retained_edges hV hretain hPJ hvDraw
  obtain ⟨P₀, hS₀, hE₀⟩ := hPJ.exists_walk_down P
    (by rw [walkDrawing_V]; exact fun _ hz => hz)
    (by rw [walkDrawing_E]; exact fun _ he => he)
  obtain ⟨Q, hSQ, hEQ⟩ := hPK.exists_walk_up P₀
  have hdis := subdrawing_disjoint_region_of_notMem_hub hS hJ hr hvr hvJ hPJ hvDraw
  refine ⟨Q, hSQ.trans hS₀, hEQ.trans hE₀, ?_⟩
  intro z hz hzr
  have hzP : z ∈ P.support := hS₀ ▸ hSQ ▸ hz
  have hzV : z ∈ (walkDrawing J P).V := by rw [walkDrawing_V]; exact hzP
  exact disjoint_left.mp hdis ((walkDrawing J P).V_subset_U hzV) hzr

/-- The inside of a short circuit avoiding the merged hub lies
in the inside of the lifted walk. This proves the first circuit
case of XII (7.3), Claim (1), page 262. The retained-edge and
outside-point-set assumptions are the geometric properties of
the constructed spoke replacements. -/
theorem circuit_inside_subset_lifted_walk_of_notMem_hub
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K J C : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsTangle Γ.toHypergraph θ T)
    {v : S} (hv : v ∈ Γ.V)
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    (hJ : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsRadialDrawing J)
    {r : Set S} (hr : r ∈ (deleteVertices Γ {v}).R) (hvr : v ∈ r) (hvJ : v ∈ J.V)
    (hV : J.V ⊆ K.V)
    (hretain : ∀ e x y, J.toGraph.IsLink e x y → x ≠ v → y ≠ v → e ∈ K.E)
    {ins ins' : Drawing S → Set S}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hins' : IsDerivedSlope (PaintingOrDrawing.drawing (deleteVertices Γ {v})) J (θ - 1)
      (deleteVerticesTangle Γ.toHypergraph {v} T θ) ins')
    {a b : S} (W : GraphWalk J.toGraph a a) (W' : GraphWalk K.toGraph b b)
    (hpoints : (walkDrawing K W').U \ r = (walkDrawing J W).U \ r)
    (hC : C.IsCircuit) (hCW : C.IsSubdrawing (walkDrawing J W))
    (hvC : v ∉ C.V) (hshort : C.length + 2 < 2 * θ) :
    ins' C ⊆ insWalk ins K W' := by
  have hCJ : C.IsSubdrawing J := hCW.trans (walkDrawing_isSubdrawing J W)
  have hCK := isSubdrawing_of_retained_edges hV hretain hCJ hvC
  have hdis := subdrawing_disjoint_region_of_notMem_hub hS ⟨hJ.1, hJ.2.1⟩ hr hvr hvJ hCJ hvC
  have hU : C.U ⊆ (walkDrawing K W').U := by
    intro x hx
    have hxout : x ∉ r := fun hxr => disjoint_left.mp hdis hx hxr
    have hmem : x ∈ (walkDrawing J W).U \ r := ⟨hCW.U_subset hx, hxout⟩
    rw [← hpoints] at hmem
    exact hmem.1
  have hCW' := isSubdrawing_of_U_subset_common hCK (walkDrawing_isSubdrawing K W') hU
  have heq := common_circuit_inside_eq_after_vertex_deletion hS hθ hT hv hK hJ.2.1
    hins hins' hC hCK hCJ hshort
  intro x hx
  change x ∈ insOf ins (walkDrawing K W')
  exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCW'⟩, heq.symm ▸ hx⟩)

end GraphMinor.GM12
