/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CellPartitionSystem
public import LeanPool.GraphMinor.GM17.ReplaceDisc

/-!
# The two sides of a curve through three nodes

This is the last step of the proof of (11.1) of Graph Minors XVII, page 191. The curve `F` is made
of chords of the faces of the circuit `δ(I)`. We show that the cells inside a disc `Δ` bounded by
`F`, or by `F` and a part of `bd(Σ)`, are the class `I` or its complement.
The paper gets this from `U(D)` partitioning the cells. We say it with changes. The class `inside Δ`
of cells in `Δ` has changes at a region exactly where the curve `F` passes through the region: a
chord cuts the frontier into two lines, one in `Δ` and one out of `Δ` (`chord_chg`), and a region
off `F` lies on one side of it (`off_chord_no_chg`). So `I` and `inside Δ` have the same changes at
each region, and their symmetric difference has none. By `trivial_of_region_chg` the two classes are
equal or complementary (`match_of_chg`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface Painting

attribute [local instance 2000] Classical.decEq Classical.propDecidable

variable {S : Type} [TopologicalSpace S] [T2Space S] {Γ : Painting S}

/-- A curve `F` on the boundary of a disc `Δ`, with the rest of the boundary on `bd(Σ)`. -/
structure DiscData (Γ : Painting S) (F Δ : Set S) : Prop where
  disc : IsClosedDisc Δ
  closed : IsClosed F
  normal : F ∩ Γ.U ⊆ Γ.N
  nbhd : ∀ x ∈ Δ \ F, Δ ∈ 𝓝 x
  sub : F ⊆ discBd Δ
  bdry : discBd Δ ⊆ F ∪ bd S

/-- A chord of the closure of a region between the nodes `u` and `v`, with the two lines of the
frontier and the two discs. -/
structure ChordData (Γ : Painting S) (r : Set S) (u v : S) (F C₁ C₂ Δ₁ Δ₂ : Set S) : Prop where
  line₁ : IsLineWithEnds C₁ u v
  line₂ : IsLineWithEnds C₂ u v
  union : C₁ ∪ C₂ = closure r \ r
  inter : C₁ ∩ C₂ = {u, v}
  chord : IsLineWithEnds F u v
  inner : F \ {u, v} ⊆ r
  nodes : F ∩ Γ.N = {u, v}
  paint : F ∩ Γ.U ⊆ {u, v}
  edge : F ∩ bd S ⊆ {u, v}
  disc₁ : IsClosedDisc Δ₁
  disc₂ : IsClosedDisc Δ₂
  discs : Δ₁ ∪ Δ₂ = closure r
  meet : Δ₁ ∩ Δ₂ = F
  bd₁ : discBd Δ₁ = C₁ ∪ F
  bd₂ : discBd Δ₂ = C₂ ∪ F

/-- The class of cells inside a set. -/
noncomputable def inside (Γ : Painting S) (Δ : Set S) : Finset (CellT Γ)
  := open Classical in Finset.univ.filter fun c => c.1 ⊆ Δ

omit [T2Space S] in
theorem mem_inside {Δ : Set S} {c : CellT Γ} : c ∈ inside Γ Δ ↔ c.1 ⊆ Δ := by simp [inside]

theorem exists_chordData [ConnectedSpace S] (hS : IsSurface S) (h : CellHyps Γ) {r : Set S} {u v :
  S} (hr : r ∈ Γ.regions) (hu : u ∈ closure r \ r) (hv : v ∈ closure r \ r) (huN : u ∈ Γ.N)
    (hvN : v ∈ Γ.N) (huv : u ≠ v) :
    ∃ F C₁ C₂ Δ₁ Δ₂, ChordData Γ r u v F C₁ C₂ Δ₁ Δ₂ := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hun, hin⟩ := (h.hreg r hr).2.lines hu hv huv
  obtain ⟨F, Δ₁, Δ₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := chord_of_region hS h hr hC₁
    hC₂ hun hin huN hvN huv
  exact ⟨F, C₁, C₂, Δ₁, Δ₂, hC₁, hC₂, hun, hin, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

omit [T2Space S] in
theorem region_off_paint {r : Set S} (hr : r ∈ Γ.regions) {x : S} (hx : x ∈ r) : x ∉ Γ.U :=
  (arcComponentsIn_subset hr hx).2

omit [T2Space S] in
theorem region_off_bd {r : Set S} (hr : r ∈ Γ.regions) {x : S} (hx : x ∈ r) : x ∉ bd S := fun h
  => region_off_paint hr hx (Γ.bd_subset h)

/-- A cell of a gap is in the disc when a point of the gap off the nodes is. -/
theorem cell_test {F Δ c L : Set S} {u v z : S} (D : DiscData Γ F Δ) (hG : Γ.IsGap c L u v)
  (hz : z ∈ L) (hzN : z ∉ Γ.N) : c ⊆ Δ ↔ z ∈ Δ := by
  have hzu : z ≠ u := fun e => hzN (e ▸ hG.left_mem_N)
  have hzv : z ≠ v := fun e => hzN (e ▸ hG.right_mem_N)
  have hzc := hG.mem_cell hz hzu hzv
  have hcF : Disjoint c F := disjoint_left.mpr fun x hx hxF => disjoint_left.mp
    (Γ.cell_disjoint_N hG.1) hx (D.normal ⟨hxF, Γ.cell_subset_U hG.1 hx⟩)
  exact ⟨fun h => h hzc, fun h => cell_in_disc D.disc.isClosed D.closed D.nbhd hG.1 hcF hzc h⟩

omit [T2Space S] in
theorem off_curve {F Δ c L : Set S} {u v z : S} (D : DiscData Γ F Δ) (hG : Γ.IsGap c L u v)
  (hz : z ∈ L) (hzN : z ∉ Γ.N) : z ∉ F := fun h => hzN (D.normal ⟨h, hG.subset_U hz⟩)

variable [ConnectedSpace S]

theorem trivial_of_region_chg (hS : IsSurface S) (h : CellHyps Γ) (K : Finset (CellT Γ))
  (hno : ∀ r ∈ Γ.regions, ∀ n, ¬ Chg cellOf faceOf gapEnds K (closure r \ r) n) : K = ∅ ∨ K
    = Finset.univ := by
  have := trivial_of_regions hS h (K : Set (CellT Γ)) fun r hr L L' hL hL' => by
    simp only [Finset.mem_coe]
    exact class_const hS h (hno r hr) (side_faceOf hS h hr hL) (side_faceOf hS h hr hL')
  rcases this with h1 | h1
  · exact .inl (Finset.coe_eq_empty.mp h1)
  · exact .inr (Finset.coe_eq_univ.mp h1)

open Classical in
/-- Two classes with the same changes at each region are equal or complementary. -/
theorem match_of_chg (hS : IsSurface S) (h : CellHyps Γ) (I I₀ : Finset (CellT Γ))
    (hm : ∀ r ∈ Γ.regions, ∀ n, Chg cellOf faceOf gapEnds I (closure r \ r) n ↔ Chg cellOf faceOf
      gapEnds I₀ (closure r \ r) n) : I₀ = I ∨ I₀ = Iᶜ := by
  rcases trivial_of_region_chg hS h (symmDiff I I₀) fun r hr n hc => by
    exact (chg_symmDiff cellOf faceOf gapEnds I I₀ _ n).mp (by convert hc) (hm r hr n) with h1 | h1
  · left
    ext c
    have := Finset.ext_iff.mp h1 c
    simp only [Finset.mem_symmDiff, Finset.notMem_empty, iff_false] at this
    tauto
  · right
    ext c
    have := Finset.ext_iff.mp h1 c
    simp only [Finset.mem_symmDiff, Finset.mem_univ, iff_true, Finset.mem_compl] at this ⊢
    tauto

/-- A region off the curve lies on one side of it, so `inside Δ` has no changes there. -/
theorem off_chord_no_chg (hS : IsSurface S) (h : CellHyps Γ) (sys : ArcSystem cellOf faceOf gapEnds
  (cellNodes (Γ := Γ)) Γ.finite_N.toFinset) {r F Δ : Set S} (hr : r ∈ Γ.regions)
    (D : DiscData Γ F Δ) (hd : Disjoint r F) (n : S) :
    ¬ Chg cellOf faceOf gapEnds (inside Γ Δ) (closure r \ r) n := by
  have hW : IsOpen (Δ \ F) := by
    rw [isOpen_iff_mem_nhds]
    exact fun y hy => Filter.inter_mem (D.nbhd y hy) (D.closed.isOpen_compl.mem_nhds hy.2)
  have hpc : IsPreconnected r := (arcComponentsIn_isPathConnected hr).isConnected.isPreconnected
  have hcase : ∀ t ∈ r, t ∈ Δ → r ⊆ Δ := fun t ht htΔ => by
    have hsub : r ⊆ (Δ \ F) ∪ Δᶜ := fun y hy => by
      by_cases h3 : y ∈ Δ
      · exact .inl ⟨h3, disjoint_left.mp hd hy⟩
      · exact .inr h3
    exact (hpc.subset_left_of_subset_union hW D.disc.isClosed.isOpen_compl
      (disjoint_left.mpr fun y hy hy' => hy' hy.1) hsub ⟨t, ht, htΔ, disjoint_left.mp hd ht⟩).trans
        sdiff_subset
  have hkey : ∀ g : GapT Γ, faceOf g = closure r \ r → (cellOf g ∈ inside Γ Δ ↔ r ⊆ Δ) := fun g hg
    => by
    obtain ⟨c, u, v, hs, hcl⟩ := face_side hS h hr hg
    obtain ⟨z, hz⟩ := line_inner_nonempty hs.1.2.1
    have hzN : z ∉ Γ.N := hs.1.not_mem_N hz.1 (fun e => hz.2 (.inl e)) (fun e => hz.2 (.inr e))
    rw [mem_inside, cellOf_eq hs.1, cell_test D hs.1 hz.1 hzN]
    constructor
    · intro hzΔ
      obtain ⟨w, hw, hw'⟩ := mem_closure_iff_nhds.mp (hcl hz.1) Δ (D.nbhd z ⟨hzΔ, off_curve D hs.1
        hz.1 hzN⟩)
      exact hcase w hw' hw
    · exact fun h3 => closure_minimal h3 D.disc.isClosed (hcl hz.1)
  intro hc
  obtain ⟨a, b, ha, hb, -, -, hI, hJ⟩ := chg_arcs sys hc
  exact hJ ((hkey b hb).mpr ((hkey a ha).mp hI))

/-- The class `inside Δ` changes at a region cut by a chord of the curve exactly at the two ends of
the chord. The two parts of the region lie on opposite sides of the curve. -/
theorem chord_chg (hS : IsSurface S) (h : CellHyps Γ) (sys : ArcSystem cellOf faceOf gapEnds
  (cellNodes (Γ := Γ)) Γ.finite_N.toFinset) {r F₀ C₁ C₂ Δ₁ Δ₂ F Δ : Set S} {u v : S}
    (hr : r ∈ Γ.regions)
    (C : ChordData Γ r u v F₀ C₁ C₂ Δ₁ Δ₂) (D : DiscData Γ F Δ) (hsub : F₀ ⊆ F)
      (hrF : ∀ x ∈ F, x ∈ r → x ∈ F₀) (huN : u ∈ Γ.N) (hvN : v ∈ Γ.N) (huv : u ≠ v) (n : S) :
    Chg cellOf faceOf gapEnds (inside Γ Δ) (closure r \ r) n ↔ n = u ∨ n = v := by
  have h2 : discBd Δ ∩ r ⊆ F₀ := fun x hx => (D.bdry hx.1).elim (fun h3 => hrF x h3 hx.2) fun hb =>
    (region_off_bd hr hx.2 hb).elim
  have hside := chord_side hS (h.hopen r hr) C.union.symm C.chord C.inner C.disc₁ C.disc₂ C.discs
    C.meet C.bd₁ C.bd₂ D.disc (hsub.trans D.sub) h2
  have hC₁₁ : C₁ ⊆ Δ₁ := fun x hx => discBd_subset _ (C.bd₁ ▸ .inl hx)
  have hC₂₂ : C₂ ⊆ Δ₂ := fun x hx => discBd_subset _ (C.bd₂ ▸ .inl hx)
  have hnot : ¬ (Δ₁ ⊆ Δ ∧ Δ₂ ⊆ Δ) := by
    rintro ⟨h3, h4⟩
    obtain ⟨t, ht⟩ := line_inner_nonempty C.chord
    have htr : t ∈ r := C.inner ht
    have hi : IsInteriorPoint t := not_not.mp (region_off_bd hr htr)
    obtain ⟨w, hw, hw'⟩ := mem_closure_iff.mp (mem_closure_compl (D.sub (hsub ht.1)) hi) r
      (h.hopen r hr) htr
    have hwc : w ∈ Δ₁ ∪ Δ₂ := C.discs ▸ subset_closure hw
    exact hw' (hwc.elim (fun h5 => h3 h5) fun h5 => h4 h5)
  have hoff : ∀ {X X' Cx Cx' : Set S}, IsClosedDisc X → X ∪ X' = closure r → X ∩ X' = F₀ → discBd X
    = Cx ∪ F₀ → Cx' ⊆ X' → closure r \ r = Cx ∪ Cx' → ∀ z ∈ Cx, z ∉ F → z ∈ Δ → X ⊆ Δ := by
    intro X X' Cx Cx' hX hXu hXi hXb hCx' hC z hz hzF hzΔ
    have hin : discInt X ⊆ r := fun x hx => by
      by_contra h3
      have hx' : x ∈ closure r \ r := ⟨hXu ▸ .inl hx.1, h3⟩
      rw [hC] at hx'
      rcases hx' with h4 | h4
      · exact hx.2 (hXb ▸ .inl h4)
      · exact hx.2 (hXb ▸ .inr (hXi ▸ ⟨hx.1, hCx' h4⟩))
    have hV : Δ ∩ Fᶜ ∈ 𝓝 z := Filter.inter_mem (D.nbhd z ⟨hzΔ, hzF⟩)
      (D.closed.isOpen_compl.mem_nhds hzF)
    obtain ⟨w, ⟨hwΔ, hwF⟩, hw⟩ := mem_closure_iff_nhds.mp (hX.subset_closure_discInt
      (discBd_subset _ (hXb ▸ .inl hz))) _ hV
    have hwr := hin hw
    refine chord_part hS D.disc h2 hX hXu hXi hXb hCx' hC hwr (fun h3 => hwF
      (hsub h3)) hw.1 ⟨hwΔ, fun h3 => ?_⟩
    exact (D.bdry h3).elim hwF fun hb => region_off_bd hr hwr hb
  have hgap : ∀ g : GapT Γ, (g.1 ⊆ C₁ → (cellOf g ∈ inside Γ Δ ↔ Δ₁ ⊆ Δ)) ∧ (g.1 ⊆ C₂ →
    (cellOf g ∈ inside Γ Δ ↔ Δ₂ ⊆ Δ)) := fun g => by
    obtain ⟨c, a, b, hG⟩ := id g.2
    obtain ⟨z, hz⟩ := line_inner_nonempty hG.2.1
    have hzN : z ∉ Γ.N := hG.not_mem_N hz.1 (fun e => hz.2 (.inl e)) (fun e => hz.2 (.inr e))
    have hzF := off_curve D hG hz.1 hzN
    rw [mem_inside, cellOf_eq hG, cell_test D hG hz.1 hzN]
    constructor
    · intro hs
      exact ⟨fun h3 => hoff C.disc₁ C.discs C.meet C.bd₁ hC₂₂ C.union.symm z (hs hz.1) hzF h3,
        fun h3 => h3 (hC₁₁ (hs hz.1))⟩
    · intro hs
      refine ⟨fun h3 => hoff C.disc₂ (by rw [union_comm, C.discs]) (by rw [inter_comm, C.meet])
        C.bd₂ hC₁₁ (by rw [← C.union, union_comm]) z (hs hz.1) hzF h3, fun h3 => h3 (hC₂₂
          (hs hz.1))⟩
  have hO : Γ.IsFace (closure r \ r) := .inl ⟨r, hr, rfl⟩
  have hOa := (h.hreg r hr).2
  have hsub₁ : C₁ ⊆ closure r \ r := C.union ▸ subset_union_left
  have hsub₂ : C₂ ⊆ closure r \ r := C.union ▸ subset_union_right
  have huA : u ∈ Γ.N ∩ (closure r \ r) := ⟨huN, hsub₁ C.line₁.left_mem⟩
  have hvA : v ∈ Γ.N ∩ (closure r \ r) := ⟨hvN, hsub₁ C.line₁.right_mem⟩
  have hfin : (Γ.N ∩ (closure r \ r)).Finite := Γ.finite_N.subset inter_subset_left
  have harc : ∀ {g : GapT Γ}, faceOf g = closure r \ r → IsArcOf (closure r \ r) (Γ.N ∩
    (closure r \ r)) g.1 := fun {g} hg => by
    obtain ⟨c', u', v', hG'⟩ := id g.2
    exact gap_arc_face hG' (hg ▸ (faceOf_spec hS h g).2)
  constructor
  · intro hc
    obtain ⟨a, b, ha, hb, han, hbn, hI, hJ⟩ := chg_arcs sys hc
    have hna := (mem_gapEnds.mp han).2
    have hnb := (mem_gapEnds.mp hbn).2
    rcases arc_sub_line hOa huA hvA C.line₁ C.line₂ C.union (harc ha) with h3 | h3
      <;> rcases arc_sub_line hOa huA hvA C.line₁ C.line₂ C.union (harc hb) with h4 | h4
    · exact (hJ (((hgap b).1 h4).mpr (((hgap a).1 h3).mp hI))).elim
    · exact C.inter.subset ⟨h3 hna, h4 hnb⟩
    · exact C.inter.subset ⟨h4 hnb, h3 hna⟩
    · exact (hJ (((hgap b).2 h4).mpr (((hgap a).2 h3).mp hI))).elim
  · intro hn
    have hn₁ : n ∈ C₁ := hn.elim (fun e => e ▸ C.line₁.left_mem) fun e => e ▸ C.line₁.right_mem
    have hn₂ : n ∈ C₂ := hn.elim (fun e => e ▸ C.line₂.left_mem) fun e => e ▸ C.line₂.right_mem
    have hnN : n ∈ Γ.N := hn.elim (fun e => e ▸ huN) fun e => e ▸ hvN
    obtain ⟨L₁, ⟨h3, h4⟩, h5⟩ : n ∈ ⋃₀ {L | IsArcOf (closure r \ r) (Γ.N ∩ (closure r \ r)) L
      ∧ L ⊆ C₁} := by
      rw [arcs_cover_line hOa hfin inter_subset_right huA hvA huv C.line₁ C.line₂ C.union C.inter]
      exact hn₁
    obtain ⟨L₂, ⟨h6, h7⟩, h8⟩ : n ∈ ⋃₀ {L | IsArcOf (closure r \ r) (Γ.N ∩ (closure r \ r)) L
      ∧ L ⊆ C₂} := by
      rw [arcs_cover_line hOa hfin inter_subset_right huA hvA huv C.line₂ C.line₁
        (by rw [union_comm, C.union]) (by rw [inter_comm, C.inter])]
      exact hn₂
    let a : GapT Γ := ⟨L₁, arc_face_gap hS h hO h3⟩
    let b : GapT Γ := ⟨L₂, arc_face_gap hS h hO h6⟩
    have ha : faceOf a = closure r \ r := faceOf_eq hS h hO h3.subset
    have hb : faceOf b = closure r \ r := faceOf_eq hS h hO h6.subset
    have hab : a ≠ b := by
      intro e
      have e' : L₁ = L₂ := congrArg Subtype.val e
      obtain ⟨c', s, t, hG'⟩ := a.2
      obtain ⟨z, hz⟩ := line_inner_nonempty hG'.2.1
      have hzN : z ∉ Γ.N := hG'.not_mem_N hz.1 (fun e => hz.2 (.inl e)) (fun e => hz.2 (.inr e))
      have hzu : z ∈ ({u, v} : Set S) := C.inter.subset ⟨h4 hz.1, h7 (e' ▸ hz.1)⟩
      exact hzN (hzu.elim (fun e => e ▸ huN) fun e => e ▸ hvN)
    refine chg_of_differ (fun a n hn => face_two_gaps hS h a hn) ha hb (mem_gapEnds.mpr ⟨hnN,
      h5⟩) (mem_gapEnds.mpr ⟨hnN, h8⟩) hab ?_
    rw [(hgap a).1 h4, (hgap b).2 h7]
    tauto

end GraphMinor.GM17
