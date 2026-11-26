/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CellPartitionArc
public import LeanPool.GraphMinor.GM17.CellPartitionCount

/-!
# Faces of a painting

The proof of (11.1) of Graph Minors XVII, page 190, draws a graph `H` with a vertex for each node
and each region of the painting in the capped surface, where the caps are regions too.
We keep only what is on the boundary of these regions. A *face* is the frontier of a region or a
cuff, and each is an `O`-arc. The gaps of cells are the arcs of `H` between nodes on a face: each
gap
lies on exactly one face (`exists_face`, `face_unique`), and the arcs of a face are gaps
(`arc_face_gap`). Painted regions are finite in number (`finite_regions`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface Painting

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-- The hypotheses of (11.1) on regions, cells and nodes. -/
structure CellHyps (Γ : Painting S) : Prop where
  hreg : ∀ R ∈ Γ.regions, IsOpenDisc R ∧ IsOArc (closure R \ R)
  h2 : ∀ c ∈ Γ.C, 2 ≤ (tilde c).ncard
  hn : ∀ n ∈ Γ.N, ∃ c ∈ Γ.C, n ∈ tilde c

/-- A face is the frontier of a region or a cuff. -/
def Painting.IsFace (Γ : Painting S) (O : Set S) : Prop := (∃ r ∈ Γ.regions, O = closure r \ r)
  ∨ O ∈ cuffs S

variable {Γ : Painting S}

omit [T2Space S] in
theorem CellHyps.hopen (h : CellHyps Γ) : ∀ r ∈ Γ.regions, IsOpen r := fun r hr => (h.hreg r hr).1.1

omit [T2Space S] in
theorem CellHyps.two (h : CellHyps Γ) : ∀ c ∈ Γ.C, ∃ a ∈ tilde c, ∃ b ∈ tilde c, a ≠ b := fun c hc
  => by
  have hfin := Γ.finite_tilde_cell hc
  have h1 : 1 < (tilde c).ncard := h.h2 c hc
  exact (one_lt_ncard hfin).mp h1

theorem side_of_frontier [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) {r L c : Set S} {u
  v : S} (hr : r ∈ Γ.regions) (hL : Γ.IsGap c L u v) (hsub : L ⊆ closure r \ r) : Γ.SideOf r L := by
  have hcS : CompactSpace S := hS.1
  obtain ⟨z, hz⟩ := line_inner_nonempty hL.2.1
  have hzN : z ∉ Γ.N := hL.not_mem_N hz.1 (fun e => hz.2 (.inl e)) (fun e => hz.2 (.inr e))
  obtain ⟨L', hs, hz'⟩ := frontier_region hS h.hopen h.two hr (hsub hz.1).1 (hsub hz.1).2 hzN
  obtain ⟨c', u', v', hs', hcl⟩ := id hs
  obtain ⟨-, rfl⟩ := hL.unique hs'.1 hz.1 hz' hzN
  exact hs

/-- The boundary line of a border cell is a gap. -/
theorem border_gap (hS : IsSurface S) {c : Set S} (hc : c ∈ Γ.C) (hbd :
  (c ∩ bd S).Nonempty) : ∃ u v, Γ.IsGap c (closure c ∩ bd S) u v := by
  obtain ⟨u, v, O, ht, hB, -, hd, -, -, -, -⟩ := border_side hS hc hbd
  refine ⟨u, v, hc, hB, hd ▸ subset_union_left, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hxN⟩
    have : x ∈ tilde c := ⟨hx.1, fun h => disjoint_left.mp (Γ.cell_disjoint_N hc) h hxN⟩
    exact ht ▸ this
  · rintro (rfl | rfl)
    · exact ⟨hB.left_mem, Γ.tilde_subset_N hc (ht ▸ .inl rfl)⟩
    · exact ⟨hB.right_mem, Γ.tilde_subset_N hc (ht ▸ .inr rfl)⟩

theorem gap_or_border (hS : IsSurface S) {c L : Set S} {u v : S} (hL : Γ.IsGap c L u v) : Γ.IsSide
  c L u v ∨ L = closure c ∩ bd S := by
  by_cases hd : Disjoint (L \ {u, v}) (bd S)
  · exact .inl ⟨hL, hd⟩
  · obtain ⟨x, hx, hxb⟩ := not_disjoint_iff.mp hd
    have hxN : x ∉ Γ.N := hL.not_mem_N hx.1 (fun e => hx.2 (.inl e)) (fun e => hx.2 (.inr e))
    have hxc : x ∈ c := hL.mem_cell hx.1 (fun e => hx.2 (.inl e)) (fun e => hx.2 (.inr e))
    obtain ⟨u', v', hB⟩ := border_gap hS hL.1 ⟨x, hxc, hxb⟩
    exact .inr (hL.unique hB hx.1 ⟨subset_closure hxc, hxb⟩ hxN).2

omit [T2Space S] in
theorem cuff_eq {Θ Θ' : Set S} (hΘ : Θ ∈ cuffs S) (hΘ' : Θ' ∈ cuffs S) {x : S} (hx : x ∈ Θ)
  (hx' : x ∈ Θ') : Θ = Θ' := by
  obtain ⟨a, -, rfl⟩ := hΘ
  obtain ⟨b, -, rfl⟩ := hΘ'
  rw [connectedComponentIn_eq hx, connectedComponentIn_eq hx']

omit [T2Space S] in
theorem cuff_subset {Θ : Set S} (hΘ : Θ ∈ cuffs S) : Θ ⊆ bd S := by
  obtain ⟨a, -, rfl⟩ := hΘ
  exact connectedComponentIn_subset _ _

/-- Each gap lies on a face. -/
theorem exists_face [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) {c L : Set S} {u v : S}
  (hL : Γ.IsGap c L u v) : ∃ O, Γ.IsFace O ∧ L ⊆ O := by
  have hcS : CompactSpace S := hS.1
  rcases gap_or_border hS hL with hs | rfl
  · obtain ⟨-, -, r, -, -, -, -, -, -, -, hr, -, hLr, -⟩ :=
      side_strip hS h.hopen hs isClosed_empty (by simp)
    refine ⟨closure r \ r, .inl ⟨r, hr, rfl⟩, fun x hx => ⟨hLr hx, fun hxr => ?_⟩⟩
    exact (arcComponentsIn_subset hr hxr).2 (hL.subset_U hx)
  · refine ⟨connectedComponentIn (bd S) u, .inr ⟨u, ?_, rfl⟩, ?_⟩
    · exact (hL.2.1.left_mem).2
    · exact (line_preconnected hL.2.1).subset_connectedComponentIn hL.2.1.left_mem
        inter_subset_right

omit [T2Space S] in
theorem side_off_bd {c L : Set S} {u v z : S} (hs : Γ.IsSide c L u v) (hz : z ∈ L)
  (hzN : z ∉ Γ.N) : z ∉ bd S := fun hb => by
  refine disjoint_left.mp hs.2 ⟨hz, ?_⟩ hb
  rintro (rfl | rfl)
  · exact hzN hs.1.left_mem_N
  · exact hzN hs.1.right_mem_N

/-- A gap lies on just one face. -/
theorem face_unique [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) {c L O O' : Set S} {u
  v
  : S} (hL : Γ.IsGap c L u v) (hO : Γ.IsFace O) (hO' : Γ.IsFace O') (hs : L ⊆ O) (hs' : L ⊆ O') : O
    = O' := by
  have hcS : CompactSpace S := hS.1
  obtain ⟨z, hz⟩ := line_inner_nonempty hL.2.1
  have hzN : z ∉ Γ.N := hL.not_mem_N hz.1 (fun e => hz.2 (.inl e)) (fun e => hz.2 (.inr e))
  have hcross : ∀ {r Θ : Set S}, r ∈ Γ.regions → L ⊆ closure r \ r → Θ ∈ cuffs S → L ⊆ Θ → False
    := fun {r Θ} hr hsub hΘ hsub' => by
    obtain ⟨c', u', v', hsd, -⟩ := side_of_frontier hS h hr hL hsub
    have hzL : z ∈ L := hz.1
    exact side_off_bd hsd hzL hzN (cuff_subset hΘ (hsub' hz.1))
  rcases hO with ⟨r, hr, rfl⟩ | hO <;> rcases hO' with ⟨r', hr', rfl⟩ | hO'
  · rw [SideOf.unique hS h.hopen hr hr' (side_of_frontier hS h hr hL hs)
    (side_of_frontier hS h hr' hL hs')]
  · exact (hcross hr hs hO' hs').elim
  · exact (hcross hr' hs' hO hs).elim
  · exact cuff_eq hO hO' (hs hz.1) (hs' hz.1)

omit [T2Space S] in
/-- A face is an `O`-arc. -/
theorem face_oarc (hS : IsSurface S) (h : CellHyps Γ) {O : Set S} (hO : Γ.IsFace O) : IsOArc O := by
  rcases hO with ⟨r, hr, rfl⟩ | hO
  · exact (h.hreg r hr).2
  · exact (cuff_statement S hS).2.2 O hO

omit [T2Space S] in
/-- A gap is an arc of the boundary of its cell, marked by the nodes of the cell. -/
theorem gap_arc_cell {c L : Set S} {u v : S} (hL : Γ.IsGap c L u v) : IsArcOf (discBd (closure c))
  (tilde c) L := by
  refine ⟨u, v, hL.2.1, hL.2.2.1, ?_⟩
  rw [← hL.2.2.2, ← Γ.closure_cell_inter_N hL.1]
  ext z
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hL.subset_closure h.1, h.2⟩⟩

omit [T2Space S] in
theorem arc_cell_gap {c L : Set S} (hc : c ∈ Γ.C) (hL : IsArcOf (discBd (closure c))
  (tilde c) L) : ∃ u v, Γ.IsGap c L u v := by
  obtain ⟨u, v, h1, h2, h3⟩ := hL
  refine ⟨u, v, hc, h1, h2, ?_⟩
  rw [← h3, ← Γ.closure_cell_inter_N hc]
  ext z
  exact ⟨fun h => ⟨h.1, discBd_subset _ (h2 h.1), h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

omit [T2Space S] in
/-- A gap on a face is an arc of the face, marked by the nodes on the face. -/
theorem gap_arc_face {c L O : Set S} {u v : S} (hL : Γ.IsGap c L u v) (hs : L ⊆ O) : IsArcOf O
  (Γ.N ∩ O) L := by
  refine ⟨u, v, hL.2.1, hs, ?_⟩
  rw [← hL.2.2.2]
  ext z
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hs h.1⟩⟩

/-- An arc of a face is a gap. For a region this is `frontier_region`. For a cuff, a point of the
arc off the nodes lies on a border cell, whose boundary line is a gap on the same cuff. -/
theorem arc_face_gap [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) {O L : Set S}
  (hO : Γ.IsFace O) (hL : IsArcOf O (Γ.N ∩ O) L) : ∃ c u v, Γ.IsGap c L u v := by
  have hcS : CompactSpace S := hS.1
  have hOA := face_oarc hS h hO
  obtain ⟨u, v, h1, h2, h3⟩ := id hL
  obtain ⟨z, hz⟩ := line_inner_nonempty h1
  have hzN : z ∉ Γ.N := fun hN => hz.2 (h3.subset ⟨hz.1, hN, h2 hz.1⟩)
  have hzA : z ∉ Γ.N ∩ O := fun e => hzN e.1
  rcases hO with ⟨r, hr, rfl⟩ | hO
  · obtain ⟨L', ⟨c', u', v', hs, hcl⟩, hz'⟩ :=
      frontier_region hS h.hopen h.two hr (h2 hz.1).1 (h2 hz.1).2 hzN
    have hsub : L' ⊆ closure r \ r := fun x hx => ⟨hcl hx, fun hxr =>
      (arcComponentsIn_subset hr hxr).2 (hs.1.subset_U hx)⟩
    rw [arcOf_eq hOA hL (gap_arc_face hs.1 hsub) hz.1 hz' hzA]
    exact ⟨c', u', v', hs.1⟩
  · have hzb := cuff_subset hO (h2 hz.1)
    have hzU : z ∈ Γ.U := Γ.bd_subset hzb
    obtain ⟨c, hc, hzc⟩ : ∃ c ∈ Γ.C, z ∈ c := by
      have := Γ.U_eq_N_union_cells ▸ hzU
      rcases this with h4 | h4
      · exact absurd h4 hzN
      · exact h4
    obtain ⟨u', v', hB⟩ := border_gap hS hc ⟨z, hzc, hzb⟩
    have hsub : closure c ∩ bd S ⊆ O := by
      obtain ⟨a, -, rfl⟩ := id hO
      have hzC : z ∈ connectedComponentIn (bd S) a := h2 hz.1
      rw [connectedComponentIn_eq hzC]
      exact (line_preconnected hB.2.1).subset_connectedComponentIn ⟨subset_closure hzc,
        hzb⟩ inter_subset_right
    rw [arcOf_eq hOA hL (gap_arc_face hB hsub) hz.1 ⟨subset_closure hzc, hzb⟩ hzA]
    exact ⟨c, u', v', hB⟩

/-- Every region has a side, since its frontier is an `O`-arc, which is infinite. -/
theorem region_side [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) {r : Set S}
  (hr : r ∈ Γ.regions) : ∃ L, Γ.SideOf r L := by
  have hcS : CompactSpace S := hS.1
  obtain ⟨y, hy, hyN⟩ := ((infinite_of_isOArc (h.hreg r hr).2).sdiff Γ.finite_N).nonempty
  obtain ⟨L, hL, -⟩ := frontier_region hS h.hopen h.two hr hy.1 hy.2 hyN
  exact ⟨L, hL⟩

theorem finite_regions [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) : Γ.regions.Finite
  := by
  have hcS : CompactSpace S := hS.1
  have hsub : Γ.regions ⊆ ⋃ L ∈ {L | ∃ c u v, Γ.IsGap c L u v}, {r | r ∈ Γ.regions ∧ Γ.SideOf r L}
    := fun r hr => by
    obtain ⟨L, hL⟩ := region_side hS h hr
    obtain ⟨c, u, v, hs, -⟩ := id hL
    exact mem_biUnion (x := L) ⟨c, u, v, hs.1⟩ ⟨hr, hL⟩
  refine (Γ.finite_gaps.biUnion fun L _ => ?_).subset hsub
  exact Set.Subsingleton.finite fun r hr r' hr' => SideOf.unique hS h.hopen hr.1 hr'.1 hr.2 hr'.2

end GraphMinor.GM17
