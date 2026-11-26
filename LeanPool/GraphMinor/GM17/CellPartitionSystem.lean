/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CellPartitionChord

/-!
# The arc system of a painting

We put the gaps of a painting into the frame of `GraphMinor/GM17/CellPartitionCount.lean`. An arc is
a gap, its cell is the cell of the gap, its face is the face of `exists_face`, and its ends are its
two nodes. `arcSystem` proves the facts of `ArcSystem`. Each node of a cell lies on two gaps of the
cell, and each node of a face lies on two gaps on the face, by `arcs_at_mark`. Two faces with two
common nodes come from `par_faces`.

If the sides of each region lie in one class of cells, then this class or its complement is empty
(`trivial_of_regions`). This is the statement `E(δ(I)) ≠ ∅` of Claim (3) of the proof of (11.1) of
Graph Minors XVII, page 191. The closed cells and the closed regions of the class and those of its
complement
are two closed sets that cover the surface and meet only in nodes, so one of them is everything, as
the surface stays connected after removing finitely many points.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface Painting

variable {S : Type} [TopologicalSpace S] [T2Space S] (Γ : Painting S)

/-- The gaps of a painting, as a type. -/
abbrev GapT : Type := {L : Set S // ∃ c u v, Γ.IsGap c L u v}

/-- The cells of a painting, as a type. -/
abbrev CellT : Type := {c : Set S // c ∈ Γ.C}

noncomputable instance : Fintype (GapT Γ) :=
  have : Finite (GapT Γ) := Γ.finite_gaps.to_subtype
  Fintype.ofFinite _

noncomputable instance : Fintype (CellT Γ) :=
  have : Finite (CellT Γ) := Set.Finite.to_subtype Γ.finite_cells
  Fintype.ofFinite _

variable {Γ}

/-- The cell of a gap. -/
noncomputable def cellOf (L : GapT Γ) : CellT Γ := ⟨L.2.choose, by
  obtain ⟨u, v, h⟩ := L.2.choose_spec
  exact h.1⟩

omit [T2Space S] in
theorem cellOf_spec (L : GapT Γ) : ∃ u v, Γ.IsGap (cellOf L).1 L.1 u v := L.2.choose_spec

open Classical in
/-- The face of a gap. -/
noncomputable def faceOf (L : GapT Γ) : Set S := if h : ∃ O, Γ.IsFace O
  ∧ L.1 ⊆ O then h.choose else ∅

open Classical in
/-- The two ends of a gap. -/
noncomputable def gapEnds (L : GapT Γ) : Finset S := Γ.finite_N.toFinset.filter (· ∈ L.1)

open Classical in
/-- The nodes of a cell. -/
noncomputable def cellNodes (c : CellT Γ) : Finset S := Γ.finite_N.toFinset.filter (· ∈ tilde c.1)

omit [T2Space S] in
theorem mem_gapEnds {L : GapT Γ} {n : S} : n ∈ gapEnds L ↔ n ∈ Γ.N ∧ n ∈ L.1 := by simp [gapEnds]

omit [T2Space S] in
theorem mem_cellNodes {c : CellT Γ} {n : S} : n ∈ cellNodes c ↔ n ∈ tilde c.1 := by
  simp only [cellNodes, Finset.mem_filter, Set.Finite.mem_toFinset, and_iff_right_iff_imp]
  exact fun h => Γ.tilde_subset_N c.2 h

omit [T2Space S] in
open Classical in
theorem gapEnds_eq {L : GapT Γ} {c : Set S} {u v : S} (h : Γ.IsGap c L.1 u v) : gapEnds L = {u, v}
  := by
  ext n
  rw [mem_gapEnds, Finset.mem_insert, Finset.mem_singleton]
  have := Set.ext_iff.mp h.2.2.2 n
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at this
  rw [← this, and_comm]

theorem cellOf_eq {L : GapT Γ} {c : Set S} {u v : S} (h : Γ.IsGap c L.1 u v) : (cellOf L).1 = c
  := by
  obtain ⟨u', v', h'⟩ := cellOf_spec L
  obtain ⟨z, hz⟩ := line_inner_nonempty h.2.1
  exact (h'.unique h hz.1 hz.1 (h.not_mem_N hz.1 (fun e => hz.2 (.inl e)) (fun e => hz.2
    (.inr e)))).1

variable [ConnectedSpace S]

theorem faceOf_spec (hS : IsSurface S) (h : CellHyps Γ) (L : GapT Γ) : Γ.IsFace (faceOf L)
  ∧ L.1 ⊆ faceOf L := by
  obtain ⟨c, u, v, hL⟩ := L.2
  have hex : ∃ O, Γ.IsFace O ∧ L.1 ⊆ O := exists_face hS h hL
  rw [faceOf, dite_eq_left hex]
  exact hex.choose_spec

theorem faceOf_eq (hS : IsSurface S) (h : CellHyps Γ) {L : GapT Γ} {O : Set S} (hO : Γ.IsFace O)
  (hs : L.1 ⊆ O) : faceOf L = O := by
  obtain ⟨c, u, v, hL⟩ := L.2
  obtain ⟨h1, h2⟩ := faceOf_spec hS h L
  exact face_unique hS h hL h1 hO h2 hs

omit [T2Space S] [ConnectedSpace S] in
theorem card_gapset (T : Finset (GapT Γ)) (A : Set (Set S)) (h : ∀ L : Set S, L ∈ A ↔ ∃ hL,
  (⟨L, hL⟩ : GapT Γ) ∈ T) : T.card = A.ncard := by
  classical
  have hA : A = ↑(T.image Subtype.val) := by
    ext L
    rw [h L]
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨hL, hm⟩
      exact ⟨_, hm, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
  rw [hA, Set.ncard_coe_finset, Finset.card_image_of_injective _ Subtype.val_injective]

open Classical in
omit [ConnectedSpace S] in
theorem cell_two_gaps (h : CellHyps Γ) (c : CellT Γ) {n : S}
  (hn : n ∈ cellNodes c) : ({a | cellOf a = c ∧ n ∈ gapEnds a} : Finset (GapT Γ)).card = 2 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.two c.1 c.2
  rw [card_gapset _ {L | IsArcOf (discBd (closure c.1)) (tilde c.1) L ∧ n ∈ L}]
  · exact arcs_at_mark (Γ.isClosedDisc_closure_cell c.2).isOArc_discBd (Γ.finite_tilde_cell c.2)
      (Γ.tilde_subset_discBd c.2) hx hy hxy (mem_cellNodes.mp hn)
  · intro L
    have hnN : n ∈ Γ.N := Γ.tilde_subset_N c.2 (mem_cellNodes.mp hn)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_gapEnds]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨u, v, hG⟩ := arc_cell_gap c.2 h1
      have hL : ∃ c u v, Γ.IsGap c L u v := ⟨c.1, u, v, hG⟩
      refine ⟨hL, Subtype.ext ?_, hnN, h2⟩
      exact cellOf_eq (L := ⟨L, hL⟩) hG
    · rintro ⟨hL, h1, -, h3⟩
      obtain ⟨u, v, hG⟩ := cellOf_spec (⟨L, hL⟩ : GapT Γ)
      rw [h1] at hG
      exact ⟨gap_arc_cell hG, h3⟩

open Classical in
theorem face_two_gaps (hS : IsSurface S) (h : CellHyps Γ) (a : GapT Γ) {n : S}
  (hn : n ∈ gapEnds a) : ({b | faceOf b = faceOf a ∧ n ∈ gapEnds b} : Finset (GapT Γ)).card = 2
    := by
  obtain ⟨hO, hsub⟩ := faceOf_spec hS h a
  obtain ⟨c, u, v, hG⟩ := id a.2
  rw [card_gapset _ {L | IsArcOf (faceOf a) (Γ.N ∩ faceOf a) L ∧ n ∈ L}]
  · have hu : u ∈ Γ.N ∩ faceOf a := ⟨hG.left_mem_N, hsub hG.2.1.left_mem⟩
    have hv : v ∈ Γ.N ∩ faceOf a := ⟨hG.right_mem_N, hsub hG.2.1.right_mem⟩
    have hna := mem_gapEnds.mp hn
    exact arcs_at_mark (face_oarc hS h hO) (Γ.finite_N.subset inter_subset_left) inter_subset_right
      hu hv hG.2.1.ne' ⟨hna.1, hsub hna.2⟩
  · intro L
    have hnN : n ∈ Γ.N := (mem_gapEnds.mp hn).1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_gapEnds]
    constructor
    · rintro ⟨h1, h2⟩
      have hL := arc_face_gap hS h hO h1
      exact ⟨hL, faceOf_eq hS h hO h1.subset, hnN, h2⟩
    · rintro ⟨hL, h1, -, h3⟩
      obtain ⟨c', u', v', hG'⟩ := id hL
      have hsub' := (faceOf_spec hS h (⟨L, hL⟩ : GapT Γ)).2
      rw [h1] at hsub'
      exact ⟨gap_arc_face hG' hsub', h3⟩

/-- **`E(δ(I)) ≠ ∅`, on regions.** If the sides of each region have their cells on one side of the
class `K`, then `K` is empty or all cells. -/
theorem trivial_of_regions (hS : IsSurface S) (h : CellHyps Γ) (K : Set (CellT Γ))
    (hno : ∀ r ∈ Γ.regions, ∀ L L' : GapT Γ, Γ.SideOf r L.1 → Γ.SideOf r L'.1 →
      (cellOf L ∈ K ↔ cellOf L' ∈ K)) : K = ∅ ∨ K = univ := by
  classical
  have hcS : CompactSpace S := hS.1
  have hman := hS.2.2
  by_contra hne
  push Not at hne
  obtain ⟨hK, hK'⟩ := hne
  obtain ⟨c, hc⟩ := hK
  obtain ⟨c', hc'⟩ := (ne_univ_iff_exists_notMem _).mp hK'
  have hfr := finite_regions hS h
  let cellsOf : Set (CellT Γ) → Set (Set S) := fun T => (fun d : CellT Γ => closure d.1) '' T
  let regOf : Prop → Set (Set S) := fun p => {r | r ∈ Γ.regions ∧ ∃ L : GapT Γ, Γ.SideOf r L.1 ∧
    (cellOf L ∈ K ↔ p)}
  let W : Set S := ⋃₀ (cellsOf K ∪ (fun r => closure r) '' regOf True)
  let W' : Set S := ⋃₀ (cellsOf Kᶜ ∪ (fun r => closure r) '' regOf False)
  have hcl : ∀ (T : Set (CellT Γ)) (p : Prop), IsClosed (⋃₀ (cellsOf T ∪ (fun r
    => closure r) '' regOf p)) := fun T p => by
    have hreg : (regOf p).Finite := hfr.subset fun _ h => h.1
    refine ((Set.toFinite (cellsOf T)).union (hreg.image _)).isClosed_sUnion ?_
    rintro _ (⟨d, -, rfl⟩ | ⟨r, -, rfl⟩) <;> exact isClosed_closure
  have hcover : ∀ y, y ∈ W ∨ y ∈ W' := fun y => by
    by_cases hyU : y ∈ Γ.U
    · obtain ⟨d, hd, hyd⟩ : ∃ d ∈ Γ.C, y ∈ closure d := by
        rcases mem_U_iff.mp hyU with hN | hd
        · obtain ⟨d, hd, hyd⟩ := h.hn y hN
          exact ⟨d, hd, hyd.1⟩
        · exact hd
      by_cases hdK : (⟨d, hd⟩ : CellT Γ) ∈ K
      · exact .inl ⟨closure d, .inl ⟨⟨d, hd⟩, hdK, rfl⟩, hyd⟩
      · exact .inr ⟨closure d, .inl ⟨⟨d, hd⟩, hdK, rfl⟩, hyd⟩
    · obtain ⟨r, hr, hyr⟩ := exists_region hyU
      obtain ⟨L, hL⟩ := region_side hS h hr
      obtain ⟨d, u, v, hs, -⟩ := id hL
      let L' : GapT Γ := ⟨L, d, u, v, hs.1⟩
      by_cases hk : cellOf L' ∈ K
      · exact .inl ⟨closure r, .inr ⟨r, ⟨hr, L', hL, by simpa using hk⟩, rfl⟩, subset_closure hyr⟩
      · exact .inr ⟨closure r, .inr ⟨r, ⟨hr, L', hL, by simpa using hk⟩, rfl⟩, subset_closure hyr⟩
  have hsame : ∀ {p r}, r ∈ regOf p → ∀ L : GapT Γ, Γ.SideOf r L.1 → (cellOf L ∈ K ↔ p)
    := fun {p r} hr L hL => by
    obtain ⟨hr1, L₀, hL₀, he⟩ := hr
    exact (hno r hr1 L L₀ hL hL₀).trans he
  have hcr : ∀ {d r : Set S} (hd : d ∈ Γ.C) {y : S}, r ∈ Γ.regions → y ∈ closure d → y ∈ closure r
    → y ∉ Γ.N → ∃ L : GapT Γ, Γ.SideOf r L.1 ∧ (cellOf L).1 = d := fun {d r} hd {y} hr h1 h2 hyN
      => by
    have hyr : y ∉ r := fun h3 => disjoint_left.mp (region_disjoint_closure hr hd) h3 h1
    obtain ⟨L, hL, hyL⟩ := frontier_region hS h.hopen h.two hr h2 hyr hyN
    obtain ⟨c₀, u, v, hs, hcl⟩ := id hL
    have hyu : y ≠ u := fun e => hyN (e ▸ hs.1.left_mem_N)
    have hyv : y ≠ v := fun e => hyN (e ▸ hs.1.right_mem_N)
    refine ⟨⟨L, c₀, u, v, hs.1⟩, hL, ?_⟩
    rw [cellOf_eq (L := ⟨L, c₀, u, v, hs.1⟩) hs.1]
    exact Γ.cell_eq_of_mem hs.1.1 hd (hs.1.mem_cell hyL hyu hyv) (closure_eq_cell hd h1 hyN)
  have hinter : ∀ y, y ∈ W → y ∈ W' → y ∈ Γ.N := by
    rintro y ⟨_, h1, hy⟩ ⟨_, h2, hy'⟩
    by_contra hyN
    rcases h1 with ⟨d, hd, rfl⟩ | ⟨r, hr, rfl⟩ <;> rcases h2 with ⟨d', hd', rfl⟩ | ⟨r', hr', rfl⟩
    · have he : d.1 = d'.1 := Γ.cell_eq_of_mem d.2 d'.2 (closure_eq_cell d.2 hy hyN)
        (closure_eq_cell d'.2 hy' hyN)
      exact hd' ((Subtype.ext he : d = d') ▸ hd)
    · obtain ⟨L, hL, he⟩ := hcr d.2 hr'.1 hy hy' hyN
      have h3 := hsame hr' L hL
      rw [Subtype.ext he] at h3
      exact h3.mp hd
    · obtain ⟨L, hL, he⟩ := hcr d'.2 hr.1 hy' hy hyN
      have h3 := hsame hr L hL
      rw [Subtype.ext he] at h3
      exact hd' (h3.mpr trivial)
    · have hrr : r ≠ r' := by
        rintro rfl
        obtain ⟨L, hL⟩ := region_side hS h hr.1
        obtain ⟨d, u, v, hs, -⟩ := id hL
        exact (hsame hr' ⟨L, d, u, v, hs.1⟩ hL).mp ((hsame hr ⟨L, d, u, v, hs.1⟩ hL).mpr trivial)
      have hyr : y ∉ r := fun h3 => by
        obtain ⟨w, hw, hw'⟩ := mem_closure_iff.mp hy' r (h.hopen r hr.1) h3
        exact hrr (region_eq hr.1 hr'.1 hw hw')
      have hyr' : y ∉ r' := fun h3 => by
        obtain ⟨w, hw, hw'⟩ := mem_closure_iff.mp hy r' (h.hopen r' hr'.1) h3
        exact hrr (region_eq hr.1 hr'.1 hw' hw)
      obtain ⟨L, hL, hyL⟩ := frontier_region hS h.hopen h.two hr.1 hy hyr hyN
      obtain ⟨L', hL', hyL'⟩ := frontier_region hS h.hopen h.two hr'.1 hy' hyr' hyN
      obtain ⟨c₁, u, v, hs, hcl⟩ := id hL
      obtain ⟨c₂, u', v', hs', hcl'⟩ := id hL'
      obtain ⟨-, rfl⟩ := hs.1.unique hs'.1 hyL hyL' hyN
      exact hrr (SideOf.unique hS h.hopen hr.1 hr'.1 hL hL')
  have hwc : IsClosed W := hcl K True
  have hwc' : IsClosed W' := hcl Kᶜ False
  obtain ⟨x, hx⟩ := arcComponentsIn_nonempty c.2
  have hxN : x ∉ Γ.N := disjoint_left.mp (Γ.cell_disjoint_N c.2) hx
  obtain ⟨y, hy⟩ := arcComponentsIn_nonempty c'.2
  have hyN : y ∉ Γ.N := disjoint_left.mp (Γ.cell_disjoint_N c'.2) hy
  have hxW : x ∈ W := ⟨closure c.1, .inl ⟨c, hc, rfl⟩, subset_closure hx⟩
  have hyW' : y ∈ W' := ⟨closure c'.1, .inl ⟨c', hc', rfl⟩, subset_closure hy⟩
  have hnb : ∀ z ∈ W, z ∉ Γ.N → W ∈ 𝓝 z := fun z hz hzN =>
    Filter.mem_of_superset (hwc'.isOpen_compl.mem_nhds fun h3 => hzN (hinter z hz h3)) fun w hw =>
      (hcover w).resolve_right hw
  exact hyN (hinter y (cover_off hman hwc Γ.finite_N ⟨x, hxW, hxN⟩ hnb hyN) hyW')

theorem side_faceOf (hS : IsSurface S) (h : CellHyps Γ) {r : Set S} (hr : r ∈ Γ.regions) {L : GapT
  Γ} (hL : Γ.SideOf r L.1) : faceOf L = closure r \ r := by
  obtain ⟨c, u, v, hs, hcl⟩ := hL
  exact faceOf_eq hS h (.inl ⟨r, hr, rfl⟩) fun x hx => ⟨hcl hx, fun hxr =>
    (arcComponentsIn_subset hr hxr).2 (hs.1.subset_U hx)⟩

theorem face_side (hS : IsSurface S) (h : CellHyps Γ) {r : Set S} (hr : r ∈ Γ.regions) {L : GapT Γ}
  (hL : faceOf L = closure r \ r) : Γ.SideOf r L.1 := by
  obtain ⟨c, u, v, hG⟩ := L.2
  exact side_of_frontier hS h hr hG (hL ▸ (faceOf_spec hS h L).2)

/-- Two gaps on the same face at a node are in the same class if the node is not a change. -/
theorem same_of_no_chg (hS : IsSurface S) (h : CellHyps Γ) {K : Finset
  (CellT Γ)} {a b : GapT Γ} {n : S} (he : faceOf b = faceOf a) (hn : ¬ Chg cellOf faceOf gapEnds K
    (faceOf a) n)
    (han : n ∈ gapEnds a) (hbn : n ∈ gapEnds b) (hab : a ≠ b) : cellOf a ∈ K ↔ cellOf b ∈ K := by
  by_contra hd
  exact hn (chg_of_differ (fun a n hn => face_two_gaps hS h a hn) rfl he han hbn hab hd)

/-- A class with no changes at a face is constant on the face. -/
theorem class_const (hS : IsSurface S) (h : CellHyps Γ) {K : Finset (CellT Γ)} {O : Set S}
  (hno : ∀ n, ¬ Chg cellOf faceOf gapEnds K O n) {a b : GapT Γ} (ha : faceOf a = O) (hb : faceOf b
    = O) : cellOf a ∈ K ↔ cellOf b ∈ K := by
  obtain ⟨hO, hsa⟩ := faceOf_spec hS h a
  rw [ha] at hO hsa
  have hsb := (faceOf_spec hS h b).2
  rw [hb] at hsb
  have hOa := face_oarc hS h hO
  obtain ⟨c, u, v, hG⟩ := id a.2
  have hu : u ∈ Γ.N ∩ O := ⟨hG.left_mem_N, hsa hG.2.1.left_mem⟩
  have hv : v ∈ Γ.N ∩ O := ⟨hG.right_mem_N, hsa hG.2.1.right_mem⟩
  have hfin : (Γ.N ∩ O).Finite := Γ.finite_N.subset inter_subset_left
  obtain ⟨hf, hcov⟩ := arcOf_family hOa hfin inter_subset_right hu hv hG.2.1.ne'
  let p : Set S → Prop := fun L => ∃ g : GapT Γ, g.1 = L ∧ cellOf g ∈ K
  have hp : ∀ g : GapT Γ, p g.1 ↔ cellOf g ∈ K := fun g => ⟨fun ⟨g', e, h'⟩ => (Subtype.ext e : g'
    = g) ▸ h', fun h' => ⟨g, rfl, h'⟩⟩
  have harc : ∀ {g : GapT Γ}, faceOf g = O → IsArcOf O (Γ.N ∩ O) g.1 := fun {g} hg => by
    obtain ⟨c', u', v', hG'⟩ := id g.2
    exact gap_arc_face hG' (hg ▸ (faceOf_spec hS h g).2)
  have hne : ∀ {L}, IsArcOf O (Γ.N ∩ O) L → L.Nonempty := fun {L} hL => by
    obtain ⟨s, t, hl, -, -⟩ := hL
    exact ⟨s, hl.left_mem⟩
  have hag : ∀ L ∈ {L | IsArcOf O (Γ.N ∩ O) L}, ∀ L' ∈ {L | IsArcOf O (Γ.N ∩ O) L},
    (L ∩ L').Nonempty → (p L ↔ p L') := by
    intro L hL L' hL' ⟨x, hx, hx'⟩
    by_cases heq : L = L'
    · rw [heq]
    have hxA : x ∈ Γ.N ∩ O := by
      by_contra hxA
      exact heq (arcOf_eq hOa hL hL' hx hx' hxA)
    obtain ⟨g, rfl⟩ : ∃ g : GapT Γ, g.1 = L := ⟨⟨L, arc_face_gap hS h hO hL⟩, rfl⟩
    obtain ⟨g', rfl⟩ : ∃ g : GapT Γ, g.1 = L' := ⟨⟨L', arc_face_gap hS h hO hL'⟩, rfl⟩
    have hg : faceOf g = O := faceOf_eq hS h hO hL.subset
    have hg' : faceOf g' = O := faceOf_eq hS h hO hL'.subset
    rw [hp, hp]
    exact same_of_no_chg hS h (hg'.trans hg.symm) (hg ▸ hno x) (mem_gapEnds.mpr ⟨hxA.1,
      hx⟩) (mem_gapEnds.mpr ⟨hxA.1, hx'⟩) fun e => heq (congrArg Subtype.val e)
  have := arcs_agree (𝓑 := {L | IsArcOf O (Γ.N ∩ O) L}) (p := p) hf (by rw [hcov]; exact
    hOa.isPreconnected) (fun L hL => IsArcOf.isClosed hL) hag (harc ha) (harc hb) (hne (harc ha))
      (hne (harc hb))
  rwa [hp, hp] at this

/-- **`E(δ(I)) ≠ ∅`.** A class of cells with no changes is empty or all cells. -/
theorem no_changes_trivial (hS : IsSurface S) (h : CellHyps Γ) (K : Finset (CellT Γ))
  (hno : ∀ f n, ¬ Chg cellOf faceOf gapEnds K f n) : K = ∅ ∨ K = Finset.univ := by
  classical
  have := trivial_of_regions hS h (K : Set (CellT Γ)) fun r hr L L' hL hL' => by
    simp only [Finset.mem_coe]
    exact class_const hS h (hno _) (side_faceOf hS h hr hL) (side_faceOf hS h hr hL')
  rcases this with h1 | h1
  · exact .inl (Finset.coe_eq_empty.mp h1)
  · exact .inr (Finset.coe_eq_univ.mp h1)

/-- The gaps of a painting satisfy the facts of `ArcSystem`. -/
theorem arcSystem (hS : IsSurface S) (h : CellHyps Γ) (h83 : Hyp83 Γ)
  (h85 : Hyp85 Γ) : ArcSystem cellOf faceOf gapEnds (cellNodes (Γ := Γ)) Γ.finite_N.toFinset where
  ends_card a := by
    classical
    obtain ⟨c, u, v, hG⟩ := a.2
    rw [gapEnds_eq (L := a) hG, Finset.card_pair hG.2.1.ne']
  ends_sub a n hn := by
    obtain ⟨u, v, hG⟩ := cellOf_spec a
    have hna := mem_gapEnds.mp hn
    exact mem_cellNodes.mpr ⟨hG.subset_closure hna.2, fun hx => disjoint_left.mp (Γ.cell_disjoint_N
      (cellOf a).2) hx hna.1⟩
  ti_sub c n hn := by
    simpa using Γ.tilde_subset_N c.2 (mem_cellNodes.mp hn)
  cover n hn := by
    obtain ⟨c, hc, hnc⟩ := h.hn n (by simpa using hn)
    exact ⟨⟨c, hc⟩, mem_cellNodes.mpr hnc⟩
  cell_two c n hn := by convert cell_two_gaps h c hn
  face_two a n hn := by convert face_two_gaps hS h a hn
  empty K hno := no_changes_trivial hS h K hno
  par f g u v hfg huv := by
    classical
    rintro ⟨a, rfl, hau⟩ ⟨a', ha', hav⟩ ⟨b, rfl, hbu⟩ ⟨b', hb', hbv⟩
    obtain ⟨hOf, hsf⟩ := faceOf_spec hS h a
    obtain ⟨hOg, hsg⟩ := faceOf_spec hS h b
    have hsf' := (faceOf_spec hS h a').2
    have hsg' := (faceOf_spec hS h b').2
    rw [ha'] at hsf'
    rw [hb'] at hsg'
    have hu := mem_gapEnds.mp hau
    have hv := mem_gapEnds.mp hav
    have hu' := mem_gapEnds.mp hbu
    have hv' := mem_gapEnds.mp hbv
    obtain ⟨c, L, L', hG, hG', hL, hL', ht⟩ := par_faces hS h h83 h85 hOf hOg hfg (hsf hu.2)
      (hsf' hv.2) (hsg hu'.2) (hsg' hv'.2) hu.1 hv.1 huv
    have hcC : c ∈ Γ.C := hG.1
    refine ⟨⟨c, hcC⟩, ⟨L, c, u, v, hG⟩, ⟨L', c, u, v, hG'⟩, ?_, Subtype.ext (cellOf_eq (L
      := ⟨L, c, u, v, hG⟩) hG), Subtype.ext (cellOf_eq (L := ⟨L', c, u, v, hG'⟩) hG'), faceOf_eq hS
        h hOf hL, faceOf_eq hS h hOg hL', gapEnds_eq (L := ⟨L, c, u, v, hG⟩) hG, gapEnds_eq (L
          := ⟨L', c, u, v, hG'⟩) hG'⟩
    ext n
    rw [mem_cellNodes, Finset.mem_insert, Finset.mem_singleton]
    change n ∈ tilde c ↔ _
    rw [ht]
    rfl

end GraphMinor.GM17
