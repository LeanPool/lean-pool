/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72Trace
public import LeanPool.GraphMinor.GM12.Section72BoundaryCompare
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section91

/-!
# The radial boundary circuit for XII (7.2)

On page 260 the boundary circle is replaced by two radial spokes.
The two-edge deformation supplies its embedded circle. Extract its
circuit from the trace drawing and compare the selected insides by
the region homotopy. Thus deleting the original selected inside
removes exactly the same original drawing points as deleting the
inside of the radial circuit.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM07

private theorem circuit_length_eq_two_of_le
    {S : Type*} [TopologicalSpace S]
    {Γ K C : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    (hC : C.IsCircuit) (hCK : C.IsSubdrawing K) (hle : C.length ≤ 2) :
    C.length = 2 := by
  classical
  obtain ⟨u, W, ⟨_, hnd⟩, hpos, _, hCE⟩ := hC
  have hl : C.length = W.length := by
    rw [Drawing.length, hCE]
    have he : {e | e ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by
      ext x
      simp
    rw [he, ncard_coe_finset, List.toFinset_card_of_nodup hnd]
    rfl
  obtain ⟨X, _, hXE⟩ := hCK.exists_walk_up W
  have hlen : X.length = W.length := congrArg List.length hXE
  obtain ⟨n, hn⟩ := even_length_of_closed hK X
  omega

/-- The two edges of a radial boundary in a region with one old
vertex are parallel spokes from that vertex to the region's hub.
This spells out the edges `e, f` used in XII (7.2), page 260. -/
theorem two_spokes_of_radial_boundary
    {S : Type*} [TopologicalSpace S]
    {Γ K C : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    (hCK : C.IsSubdrawing K) (hlen : C.length = 2)
    {r : Set S} {v : S} (hr : r ∈ Γ.R)
    (hCZ : C.U ⊆ r ∪ {v}) (hmeet : Γ.U ∩ C.U = {v}) :
    ∃ (u : S) (e f : Set S), u ∈ r ∩ K.V ∧ e ≠ f ∧ C.E = {e, f} ∧
      K.toGraph.IsLink e v u ∧ K.toGraph.IsLink f v u := by
  obtain ⟨u, hu, huniq⟩ := hK.2.2.1 r hr
  have hend : ∀ e ∈ C.E, K.toGraph.IsLink e v u := by
    intro e he
    obtain ⟨z, hzΓ, w, hw, hcap⟩ := hK.2.2.2.2.1 e (hCK.2 he)
    have hzcl : z ∈ closure e := by
      have hz : z ∈ closure e ∩ K.V := by rw [hcap]; exact Or.inl rfl
      exact hz.1
    have hwcl : w ∈ closure e := by
      have hw' : w ∈ closure e ∩ K.V := by rw [hcap]; exact Or.inr rfl
      exact hw'.1
    have hzv : z = v := mem_singleton_iff.mp
      (hmeet.subset ⟨Γ.V_subset_U hzΓ, C.closure_subset_U he hzcl⟩)
    have hwr : w ∈ r := by
      rcases hCZ (C.closure_subset_U he hwcl) with hwr | hwv
      · exact hwr
      · exact (hw.2 (mem_singleton_iff.mp hwv ▸ hzv ▸ hzΓ)).elim
    have hwu : w = u := huniq w ⟨hwr, hw.1⟩
    subst z
    subst w
    exact ⟨hCK.2 he, hK.2.1 hzΓ, hw.1, hcap⟩
  obtain ⟨e, f, hef, hCE⟩ := ncard_eq_two.mp hlen
  exact ⟨u, e, f, hu, hef, hCE,
    hend e (hCE.symm ▸ Or.inl rfl), hend f (hCE.symm ▸ Or.inr rfl)⟩

/-- The boundary of a two-spoke circuit has exactly its two common
ends as vertices. Its whole point set is the union of the spokes'
closures, as used in the radial deletion of XII (7.2), page 260. -/
theorem two_spoke_circuit_point_sets
    {S : Type*} [TopologicalSpace S] {K C : Drawing S}
    (hC : C.IsCircuit) (hCK : C.IsSubdrawing K)
    {e f : Set S} {v u : S} (hCE : C.E = {e, f})
    (he : K.toGraph.IsLink e v u) (hf : K.toGraph.IsLink f v u) :
    C.V = {v, u} ∧ C.U = closure e ∪ closure f := by
  have heC : e ∈ C.E := hCE.symm ▸ Or.inl rfl
  have hcap : ∀ g ∈ C.E, closure g ∩ C.V = {v, u} := by
    intro g hg
    rw [hCK.closure_inter_V hg]
    rcases hCE.subset hg with rfl | rfl
    · exact he.2.2.2
    · exact hf.2.2.2
  have hCV : C.V = {v, u} := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨W, _, hpos, _, _⟩ := exists_walk_at hC hx
      cases W with
      | nil hv => exact (Nat.lt_irrefl 0 hpos).elim
      | @cons _ y _ g hlink rest =>
        have hxcl : x ∈ closure g ∩ C.V := by
          rw [hlink.2.2.2]
          exact Or.inl rfl
        exact (hcap _ hlink.1).subset hxcl
    · intro x hx
      exact ((hcap e heC).superset hx).2
  refine ⟨hCV, ?_⟩
  rw [C.U_eq, hCE]
  simp only [mem_insert_iff, mem_singleton_iff, iUnion_iUnion_eq_or_left, iUnion_iUnion_eq_left]
  apply union_eq_right.mpr
  intro x hx
  exact Or.inl (((hcap e heC).superset (hCV ▸ hx)).1)

/-- The two-spoke or backtracking alternative in XII (7.2), page 260.
In the backtracking case the selected disc lies in the region with
its boundary vertex restored. Otherwise the radial circuit inside
meets the original drawing in exactly the same points as the given
selected disc, and its boundary uses only the old region and vertex. -/
theorem exists_radial_boundary_circuit_or_disc_subset_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T) (hθ : 2 ≤ θ)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hE : Γ.E.Nonempty)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {F r D : Set S} {v : S} (hF : IsOArc F) (hvF : v ∈ F)
    (hv : v ∈ Γ.V) (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r)
    (hn : Γ.IsNormal F) (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    :
    D ⊆ r ∪ {v} ∨ ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length = 2 ∧
      Γ.U ∩ D = Γ.U ∩ ins C ∧
      (PaintingOrDrawing.drawing Γ).inter D = (PaintingOrDrawing.drawing Γ).inter (ins C) ∧
      (PaintingOrDrawing.drawing Γ).interOutside D = (PaintingOrDrawing.drawing Γ).interOutside
        (ins C) ∧
      C.U ⊆ r ∪ {v} ∧ Γ.U ∩ C.U = {v} := by
  obtain ⟨φ, ψ, W, hφ, hφF, hlen, hψU, hh, halt⟩ :=
    exists_two_spoke_deformation hS hK hE hF hvF hv hr hFr
  rcases halt with hψ | ⟨L, hL, hψL, hLZ⟩
  · right
    obtain ⟨C, hC, hCW, hCU⟩ := exists_circuit_of_oArc
      (show IsOArc (range ψ) from ⟨hψ.toHomeomorph⟩) hψU.subset
    have hCK := hCW.trans (walkDrawing_isSubdrawing K W)
    have hCl : C.length ≤ 2 := by
      have hle : C.E.ncard ≤ W.edges.length :=
        (ncard_le_ncard (fun e he => by
          have hw := hCW.2 he
          rwa [walkDrawing_E] at hw) W.edges.finite_toSet).trans (ncard_mem_list_le W.edges)
      exact hle.trans (by simpa only [GraphWalk.length] using hlen.le)
    obtain ⟨hE, hbdE, hmE⟩ := hd C hC hCK (by omega)
    have hvψ : v ∈ range ψ := by
      rw [hψU]
      apply (walkDrawing K W).V_subset_U
      rw [walkDrawing_V]
      exact W.start_mem_support
    have hψZ : range ψ ⊆ r ∪ {v} := by
      obtain ⟨H, hHZ, _, hH1⟩ := hh
      rintro x ⟨z, rfl⟩
      exact hH1 z ▸ hHZ (z, 1)
    have hmeet : Γ.U ∩ range ψ = {v} := by
      apply Subset.antisymm
      · rintro x ⟨hxΓ, hxψ⟩
        rcases hψZ hxψ with hxr | hxv
        · exact (region_subset hr hxr hxΓ).elim
        · exact hxv
      · intro x hx
        have hxv := mem_singleton_iff.mp hx
        subst x
        exact ⟨Γ.V_subset_U hv, hvψ⟩
    have hnψ : Γ.IsNormal (range ψ) := by
      rintro x ⟨hxψ, hxΓ⟩
      have hxv := mem_singleton_iff.mp (hmeet.subset ⟨hxΓ, hxψ⟩)
      exact hxv ▸ hv
    have heq := drawing_inter_disc_eq_of_region_deformation hS hT hφ hψ hr
      (hφF.symm ▸ hvF) hvψ hD hE (hbd.trans hφF.symm) (hbdE.trans hCU)
      (hφF.symm ▸ hn) hnψ hm hmE hh
    have hΓF : Γ.U ∩ F = {v} := by
      apply Subset.antisymm
      · rintro x ⟨hxΓ, hxF⟩
        by_cases hxv : x = v
        · exact hxv
        · exact (region_subset hr (hFr ⟨hxF, hxv⟩) hxΓ).elim
      · rintro x hx
        have hxv := mem_singleton_iff.mp hx
        subst x
        exact ⟨Γ.V_subset_U hv, hvF⟩
    have hboundary : Γ.U ∩ frontier D = Γ.U ∩ frontier (ins C) := by
      rw [← subBd_eq_frontier, hbd, hΓF, ← subBd_eq_frontier, hbdE, hCU, hmeet]
    have hout := drawing_inter_outside_eq_of_boundary_eq heq hboundary
    exact ⟨C, hC, hCK, circuit_length_eq_two_of_le hK.2.1 hC hCK hCl, heq,
      inter_eq_of_drawing_inter_eq heq, inter_eq_of_drawing_inter_eq hout,
      hCU ▸ hψZ, hCU ▸ hmeet⟩
  · left
    exact selected_disc_subset_region_vertex_of_line_deformation hS hT hφ
      (hφF.symm ▸ hn) hr (hφF.symm ▸ hvF) hD (hbd.trans hφF.symm)
      hm hL hLZ hψL.subset hh

/-- The radial boundary circuit in XII (7.2), page 260. Its inside
meets the original drawing in exactly the same points as the given
selected disc, and its boundary uses only the old region and vertex. -/
theorem exists_radial_boundary_circuit
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T) (hθ : 2 ≤ θ)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    {F r D : Set S} {v : S} (hF : IsOArc F) (hvF : v ∈ F)
    (hv : v ∈ Γ.V) (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r)
    (hn : Γ.IsNormal F) (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T)
    (hED : ∃ e ∈ Γ.E, e ⊆ D) :
    ∃ C : Drawing S, C.IsCircuit ∧ C.IsSubdrawing K ∧ C.length = 2 ∧
      Γ.U ∩ D = Γ.U ∩ ins C ∧
      (PaintingOrDrawing.drawing Γ).inter D = (PaintingOrDrawing.drawing Γ).inter (ins C) ∧
      (PaintingOrDrawing.drawing Γ).interOutside D = (PaintingOrDrawing.drawing Γ).interOutside
        (ins C) ∧
      C.U ⊆ r ∪ {v} ∧ Γ.U ∩ C.U = {v} := by
  obtain ⟨e, he, heD⟩ := hED
  rcases exists_radial_boundary_circuit_or_disc_subset_region hS hT hθ hK ⟨e, he⟩ hd
      hF hvF hv hr hFr hn hD hbd hm with hDZ | hC
  · obtain ⟨x, hxe⟩ := he.1
    rcases hDZ (heD hxe) with hxr | hxv
    · exact (region_subset hr hxr (he.2.1 hxe).1).elim
    · exact ((he.2.1 hxe).2 (mem_singleton_iff.mp hxv ▸ hv)).elim
  · exact hC

end GraphMinor.GM12
