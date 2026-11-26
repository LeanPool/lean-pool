/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.CircleCut

/-!
# The park of a clean presentation

We build the park `(G*, Ω*, Ω₀)` of Graph Minors IX, page 68, and prove the two facts about it that
the proof of (11.4) uses. The first is the fence `(A, B)` of `Ω₀` and the set `Z` that the paper
states with the remark "it follows easily". The second is that a path of `G*` between the two
boundaries is drawn in one lawn. We also show that the part outside the wall is rural.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v}

/-- A short path has a vertex joined to all the others by edges of the path: its middle vertex, or
one end if it has a single edge. The other vertices are in `ΩBar₀`. -/
theorem IsShortPath.exists_rep {N : Neighborhood α β} {P : Graph α β} {a b : α}
    (hS : IsShortPath N P a b) :
    ∃ r ∈ V(P), ∀ v ∈ V(P), v ≠ r → v ∈ N.Ω₀.bar ∧ ∃ e ∈ E(P), N.G.IsLink e r v := by
  rcases hS.cases with ⟨hV, e, hE, hl⟩ | ⟨m, -, -, -, hV, e₁, e₂, -, hE, hl₁, hl₂⟩
  · refine ⟨a, hS.path.left_mem, fun v hv hne => ?_⟩
    rw [hV] at hv
    rcases hv with rfl | rfl
    · exact (hne rfl).elim
    · exact ⟨hS.right_mem, e, by rw [hE]; rfl, hl⟩
  · refine ⟨m, by rw [hV]; exact Or.inr (Or.inl rfl), fun v hv hne => ?_⟩
    rw [hV] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨hS.left_mem, e₁, by rw [hE]; exact Or.inl rfl, hl₁⟩
    · exact (hne rfl).elim
    · exact ⟨hS.right_mem, e₂, by rw [hE]; exact Or.inr rfl, hl₂⟩

/-- A compact connected set `K` outside the interior of `Δ₀`, joining a vertex `v` to a vertex `r`
of the wall. It meets the wall only in `r`, and the rest of it lies in a lawn with `r` as chosen
vertex. -/
structure IsChord {N : Neighborhood α β} (P_pres : Presentation N)
    (r : {L // IsLawn P_pres L} → α) (K : Set EuclideanPlane) (v r' : α) : Prop where
  compact : IsCompact K
  conn : IsConnected K
  mem_v : vertexPt P_pres.Γ v ∈ K
  mem_r : vertexPt P_pres.Γ r' ∈ K
  avoid : K ⊆ (interior P_pres.Δ₀)ᶜ
  wall_eq : ∀ y ∈ K, y ∈ wall P_pres → y = vertexPt P_pres.Γ r'
  off : ∀ y ∈ K, y ∉ wall P_pres → ∃ i : {L // IsLawn P_pres L}, y ∈ i.1 ∧ r i = r'

namespace IsCleanPresentation

variable {N : Neighborhood α β} {P_pres : Presentation N} (C : IsCleanPresentation P_pres)
include C

omit C in
theorem not_mem_wall_of_interior {x : EuclideanPlane} (hx : x ∈ interior (wallDisc P_pres)) :
    x ∉ wall P_pres := fun h =>
  disjoint_left.mp (disjoint_interior_subBd (wallDisc P_pres)) hx h

omit C in
theorem Δ₀_subset_wallDisc : P_pres.Δ₀ ⊆ wallDisc P_pres := subset_union_left

omit C in
theorem interior_Δ₀_disjoint_wall {x : EuclideanPlane} (hx : x ∈ interior P_pres.Δ₀) :
    x ∉ wall P_pres :=
  not_mem_wall_of_interior (interior_mono Δ₀_subset_wallDisc hx)

omit C in
theorem vertexSet_subset_iff {v : α} (hv : v ∈ V(N.G)) {X : Set EuclideanPlane} :
    graphDrawingVertexSet P_pres.Γ v ⊆ X ↔ vertexPt P_pres.Γ v ∈ X := by
  rw [vertexSet_eq_vertexPt P_pres.Γ hv, singleton_subset_iff]

/-- A vertex drawn in `bd(L)` is in the prominence, or it is in `ΩBar₀` and off the wall. -/
theorem mem_bd_lawn_cases {Q : Graph α β} {L : Set EuclideanPlane}
    (hL : IsProminenceWithDisc P_pres Q L) {v : α} (hv : v ∈ V(N.G))
    (hb : vertexPt P_pres.Γ v ∈ discBd L) :
    v ∈ V(Q) ∨ (v ∈ N.Ω₀.bar ∧ vertexPt P_pres.Γ v ∉ wall P_pres) := by
  obtain ⟨a, b, A, B, hS, E⟩ := C.exists_ear_of_prominence hL
  by_cases hc : vertexPt P_pres.Γ v ∈ graphDrawingSubgraphU P_pres.Γ Q
  · exact Or.inl (mem_vertexSet_of_vertexPt_mem P_pres.Γ hS.path.le hv hc)
  right
  rw [E.bdL] at hb
  have hA : vertexPt P_pres.Γ v ∈ A := hb.resolve_right hc
  obtain ⟨w, hw, hx⟩ := C.exists_bar_of_mem (vertexPt_mem_U P_pres.Γ hv)
    (Surface.discBd_subset _ (E.A_subset hA))
  have hvw : v = w := vertexPt_injOn P_pres.Γ hv (N.bar₀_subset hw) hx
  subst hvw
  exact ⟨hw, fun h => hc ((C.prominence_U_subset_wall hL).2 ⟨E.A_subset_L hA, h⟩)⟩

/-- A vertex of `ΩBar₀` off the wall lies in a lawn. -/
theorem exists_lawn_of_off_wall {v : α} (hv : v ∈ N.Ω₀.bar)
    (hw : vertexPt P_pres.Γ v ∉ wall P_pres) :
    ∃ L, IsLawn P_pres L ∧ vertexPt P_pres.Γ v ∈ L := by
  obtain ⟨Q, a, b, A, B, F, hF⟩ := C.exists_earFamily
  by_contra hn
  push Not at hn
  have hv₀ : vertexPt P_pres.Γ v ∈ P_pres.Δ₀ :=
    subBd_subset_of_isClosed C.disc₀.isCompact.isClosed (IsCleanPresentation.vertexPt_mem_subBd hv)
  have hY : IsClosed (⋃ i ∈ (univ : Set {L // IsLawn P_pres L}), i.1) :=
    F.finite.isClosed_biUnion fun i hi => (F.ear i hi).disc.isCompact.isClosed
  have hvY : vertexPt P_pres.Γ v ∉ ⋃ i ∈ (univ : Set {L // IsLawn P_pres L}), i.1 := by
    intro h
    obtain ⟨i, -, hi⟩ := mem_iUnion₂.mp h
    exact hn i.1 i.2 hi
  have hint : vertexPt P_pres.Γ v ∈ interior (wallDisc P_pres) := by
    rw [interior_eq_discInt_plane C.isClosedDisc_wallDisc]
    exact ⟨Δ₀_subset_wallDisc hv₀, fun h => hw (C.wall_eq ▸ h)⟩
  have hi₀ : vertexPt P_pres.Γ v ∈ interior P_pres.Δ₀ := by
    refine mem_interior.mpr ⟨interior (wallDisc P_pres) ∩ (⋃ i ∈ (univ : Set {L // IsLawn P_pres
      L}), i.1)ᶜ,
      ?_, isOpen_interior.inter hY.isOpen_compl, hint, hvY⟩
    rintro y ⟨hy, hyn⟩
    have hy' := interior_subset hy
    rw [wallDisc_eq] at hy'
    exact hy'.resolve_right hyn
  exact (P_pres.U_subset (vertexPt_mem_U P_pres.Γ (N.bar₀_subset hv))).2 hi₀

/-- A point off the wall lies in at most one lawn. -/
theorem lawn_eq_of_off_wall {Q Q' : Graph α β} {L L' : Set EuclideanPlane}
    (hL : IsProminenceWithDisc P_pres Q L) (hL' : IsProminenceWithDisc P_pres Q' L')
    {x : EuclideanPlane} (hx : x ∈ L) (hx' : x ∈ L') (hw : x ∉ wall P_pres) : L = L' := by
  by_contra hne
  obtain ⟨v, ⟨hv, -⟩, hxv⟩ := C.lawn_inter_subset hL hL' hne ⟨hx, hx'⟩
  obtain ⟨a, b, A, B, hS, E⟩ := C.exists_ear_of_prominence hL
  rw [hS.path.pathEnds_eq] at hv
  have hvV : v ∈ V(Q) := by
    rcases hv with rfl | rfl
    · exact hS.path.left_mem
    · exact hS.path.right_mem
  exact hw ((C.prominence_U_subset_wall hL).1
    (graphDrawingVertexSet_subset_subgraphU_of_mem P_pres.Γ hvV hxv))

/-- A wall vertex or a vertex of `ΩBar₀` off the wall has a chord. -/
theorem exists_chord_of_lawn {r : {L // IsLawn P_pres L} → α} {Q : Graph α β}
    {i : {L // IsLawn P_pres L}} (hL : IsProminenceWithDisc P_pres Q i.1) (hr : r i ∈ V(Q)) {v : α}
    (hv : v ∈ N.Ω₀.bar) (hw : vertexPt P_pres.Γ v ∉ wall P_pres)
    (hvi : vertexPt P_pres.Γ v ∈ i.1) :
    ∃ K, IsChord P_pres r K v (r i) := by
  obtain ⟨a, b, A, B, hS, E⟩ := C.exists_ear_of_prominence hL
  have hv₀ : vertexPt P_pres.Γ v ∈ P_pres.Δ₀ :=
    subBd_subset_of_isClosed C.disc₀.isCompact.isClosed (IsCleanPresentation.vertexPt_mem_subBd hv)
  have hvA : vertexPt P_pres.Γ v ∈ A := E.L_inter ▸ ⟨hvi, hv₀⟩
  have hvb : vertexPt P_pres.Γ v ∈ discBd i.1 := E.bdL ▸ Or.inl hvA
  have hrU : vertexPt P_pres.Γ (r i) ∈ graphDrawingSubgraphU P_pres.Γ Q :=
    vertexPt_mem_subgraphU P_pres.Γ hr hS.path.le
  have hrb : vertexPt P_pres.Γ (r i) ∈ discBd i.1 := E.bdL ▸ Or.inr hrU
  have hne : vertexPt P_pres.Γ v ≠ vertexPt P_pres.Γ (r i) := fun h =>
    hw (h ▸ (C.prominence_U_subset_wall hL).1 hrU)
  obtain ⟨F, hF, hFs, hFb⟩ := Surface.exists_chord E.disc hvb hrb hne
  refine ⟨F, hF.isCompact, ?_, hF.left_mem, hF.right_mem, ?_, ?_, ?_⟩
  · exact ⟨⟨_, hF.left_mem⟩, hF.isPreconnected_diff.subset_closure sdiff_subset
    hF.subset_closure_diff⟩
  · intro y hy hyi
    have hyL := hFs hy
    have hyΔ : y ∈ P_pres.Δ₀ := interior_subset hyi
    have hyA : y ∈ A := E.L_inter ▸ ⟨hyL, hyΔ⟩
    rw [interior_eq_discInt_plane C.disc₀] at hyi
    exact hyi.2 (E.A_subset hyA)
  · intro y hy hyw
    have hyc := (C.prominence_U_subset_wall hL).2 ⟨hFs hy, hyw⟩
    have hyb : y ∈ F ∩ discBd i.1 := ⟨hy, E.bdL ▸ Or.inr hyc⟩
    rw [hFb] at hyb
    rcases hyb with h | h
    · exact (hw (h ▸ hyw)).elim
    · exact h
  · intro y hy _
    exact ⟨i, hFs hy, rfl⟩

omit C in
/-- The chord of a wall vertex is just that vertex. -/
theorem exists_chord_of_wall (r : {L // IsLawn P_pres L} → α) {v : α}
    (_hv : v ∈ N.Ω₀.bar) (hw : vertexPt P_pres.Γ v ∈ wall P_pres) :
    IsChord P_pres r {vertexPt P_pres.Γ v} v v := by
  refine ⟨isCompact_singleton, isConnected_singleton, rfl, rfl, ?_, fun y hy _ => hy, ?_⟩
  · rintro y rfl hi
    exact interior_Δ₀_disjoint_wall hi hw
  · rintro y rfl hn
    exact (hn hw).elim

theorem chord_disjoint {r : {L // IsLawn P_pres L} → α} {K K' : Set EuclideanPlane} {v v' s s' : α}
    (hF : ∀ i : {L // IsLawn P_pres L}, ∃ Q, IsProminenceWithDisc P_pres Q i.1)
    (h : IsChord P_pres r K v s) (h' : IsChord P_pres r K' v' s') (hne : s ≠ s')
    (hinj : vertexPt P_pres.Γ s ≠ vertexPt P_pres.Γ s') : Disjoint K K' := by
  rw [disjoint_left]
  intro y hy hy'
  by_cases hw : y ∈ wall P_pres
  · exact hinj ((h.wall_eq y hy hw).symm.trans (h'.wall_eq y hy' hw))
  · obtain ⟨i, hyi, hri⟩ := h.off y hy hw
    obtain ⟨j, hyj, hrj⟩ := h'.off y hy' hw
    obtain ⟨Q, hQ⟩ := hF i
    obtain ⟨Q', hQ'⟩ := hF j
    have hij : i = j := Subtype.ext (C.lawn_eq_of_off_wall hQ hQ' hyi hyj hw)
    exact hne (hri.symm.trans ((congrArg r hij).trans hrj))

omit C in
private theorem ncard_union_le_two {A B : Set α} (hA : A.Subsingleton) (hB : B.Subsingleton) :
    (A ∪ B).ncard ≤ 2 := by
  let := hA.finite.to_subtype
  let := hB.finite.to_subtype
  have ha := Set.ncard_le_one_iff_subsingleton.mpr hA
  have hb := Set.ncard_le_one_iff_subsingleton.mpr hB
  have hu := Set.ncard_union_le A B
  omega

omit C in
private theorem edge_meets_wall_cut {X Y : Set EuclideanPlane} {p q : EuclideanPlane}
    (cut : IsCircleCut (wall P_pres) X Y p q) {e : β} {r v : α} (hl : N.G.IsLink e r v)
    (hsubw : closure (graphDrawingEdgeSet P_pres.Γ e) ⊆ wall P_pres)
    (hlabel : (vertexPt P_pres.Γ r ∈ X ∧ vertexPt P_pres.Γ v ∈ Y) ∨
      (vertexPt P_pres.Γ r ∈ Y ∧ vertexPt P_pres.Γ v ∈ X))
    (hp : p ∉ P_pres.Γ.drawing.V) (hq : q ∉ P_pres.Γ.drawing.V) :
    p ∈ graphDrawingEdgeSet P_pres.Γ e ∨ q ∈ graphDrawingEdgeSet P_pres.Γ e := by
  have hrmem := graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl
    ((mem_vertexSet_iff P_pres.Γ hl.left_mem).mpr rfl)
  have hvmem := graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl.symm
    ((mem_vertexSet_iff P_pres.Γ hl.right_mem).mpr rfl)
  have hcon : IsPreconnected (closure (graphDrawingEdgeSet P_pres.Γ e)) :=
    (isPreconnected_edgeSet hl.edge_mem).closure
  have hin : p ∈ closure (graphDrawingEdgeSet P_pres.Γ e) ∨
      q ∈ closure (graphDrawingEdgeSet P_pres.Γ e) := by
    by_contra hn
    push Not at hn
    rcases hlabel with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact cut.sep _ hcon hsubw hn.1 hn.2 ⟨_, hrmem, h₁⟩ ⟨_, hvmem, h₂⟩
    · exact cut.sep _ hcon hsubw hn.1 hn.2 ⟨_, hvmem, h₂⟩ ⟨_, hrmem, h₁⟩
  have hmemE := graphDrawingEdgeSet_mem P_pres.Γ hl.edge_mem
  rcases hin with h | h
  · left
    rw [← P_pres.Γ.drawing.closure_diff_V hmemE]
    exact ⟨h, hp⟩
  · right
    rw [← P_pres.Γ.drawing.closure_diff_V hmemE]
    exact ⟨h, hq⟩

/-- The fence `(A, B)` of `Ω₀` and the set `Z` of Graph Minors IX, page 68, when both sides of the
fence of `Ω*` are nonempty. -/
theorem exists_fence_and_Z_of_cut {Ωs : CyclicPerm α} {As Bs : Set α}
    (hbar : ∀ v ∈ V(N.G), v ∈ Ωs.bar ↔ vertexPt P_pres.Γ v ∈ wall P_pres)
    (hdisj : Disjoint As Bs) (hun : As ∪ Bs = Ωs.bar)
    {X Y : Set EuclideanPlane} {p q : EuclideanPlane} (cut : IsCircleCut (wall P_pres) X Y p q)
    (hX : ∀ a ∈ As, vertexPt P_pres.Γ a ∈ X) (hY : ∀ b ∈ Bs, vertexPt P_pres.Γ b ∈ Y) :
    ∃ A B Z : Set α, N.Ω₀.IsFence A B ∧ Z ⊆ N.Ω₀.bar ∧ Z.ncard ≤ 2 ∧
      As ∩ N.Ω₀.bar ⊆ A ∧ Bs ∩ N.Ω₀.bar ⊆ B ∧
      ∀ L, IsLawn P_pres L →
        {v ∈ V(N.G) | graphDrawingVertexSet P_pres.Γ v ⊆ subBd L} ⊆ A ∪ As ∪ Z ∨
          {v ∈ V(N.G) | graphDrawingVertexSet P_pres.Γ v ⊆ subBd L} ⊆ B ∪ Bs ∪ Z := by
  classical
  obtain ⟨Q, a, b, Af, Bf, F, hF⟩ := C.exists_earFamily
  have hrep := fun i => (hF i).2.exists_rep
  choose r hr₁ hr₂ using hrep
  have hprom : ∀ i : {L // IsLawn P_pres L}, ∃ Q, IsProminenceWithDisc P_pres Q i.1 :=
    fun i => ⟨Q i, (hF i).1⟩
  have hUw : ∀ i, graphDrawingSubgraphU P_pres.Γ (Q i) ⊆ wall P_pres := fun i =>
    (C.prominence_U_subset_wall (hF i).1).1
  have hleG : ∀ i, Q i ≤ N.G := fun i => (hF i).2.path.le
  have hVG : ∀ i, ∀ v ∈ V(Q i), v ∈ V(N.G) := fun i v hv => (hleG i).vertexSet_mono hv
  have hwall : ∀ i, ∀ v ∈ V(Q i), vertexPt P_pres.Γ v ∈ wall P_pres := fun i v hv =>
    hUw i (vertexPt_mem_subgraphU P_pres.Γ hv (hleG i))
  have hsplit : ∀ v ∈ V(N.G), vertexPt P_pres.Γ v ∈ wall P_pres → v ∈ As ∨ v ∈ Bs := by
    intro v hv hw
    have : v ∈ As ∪ Bs := hun ▸ (hbar v hv).mpr hw
    exact this
  have hrs : ∀ i, r i ∈ As ∨ r i ∈ Bs := fun i =>
    hsplit _ (hVG i _ (hr₁ i)) (hwall i _ (hr₁ i))
  let inS : Set α → Set α := fun S => {v | v ∈ N.Ω₀.bar ∧
    ((vertexPt P_pres.Γ v ∈ wall P_pres ∧ v ∈ S) ∨
      (vertexPt P_pres.Γ v ∉ wall P_pres ∧ ∃ i, vertexPt P_pres.Γ v ∈ i.1 ∧ r i ∈ S))}
  have hchord : ∀ S, ∀ v ∈ inS S, ∃ K s, IsChord P_pres r K v s ∧ s ∈ S := by
    rintro S v ⟨hv, ⟨hw, hS⟩ | ⟨hw, i, hi, hS⟩⟩
    · exact ⟨_, v, exists_chord_of_wall r hv hw, hS⟩
    · obtain ⟨K, hK⟩ := C.exists_chord_of_lawn (hF i).1 (hr₁ i) hv hw hi
      exact ⟨K, r i, hK, hS⟩
  have hABd : Disjoint (inS As) (inS Bs) := by
    rw [disjoint_left]
    rintro v ⟨hv, ⟨hw, hS⟩ | ⟨hw, i, hi, hS⟩⟩ ⟨-, ⟨hw', hS'⟩ | ⟨hw', i', hi', hS'⟩⟩
    · exact disjoint_left.mp hdisj hS hS'
    · exact hw' hw
    · exact hw hw'
    · have : i = i' := Subtype.ext (C.lawn_eq_of_off_wall (hF i).1 (hF i').1 hi hi' hw)
      subst this
      exact disjoint_left.mp hdisj hS hS'
  have hABu : inS As ∪ inS Bs = N.Ω₀.bar := by
    apply Subset.antisymm
    · rintro v (h | h)
      · exact h.1
      · exact h.1
    · intro v hv
      by_cases hw : vertexPt P_pres.Γ v ∈ wall P_pres
      · rcases hsplit v (N.bar₀_subset hv) hw with h | h
        · exact Or.inl ⟨hv, Or.inl ⟨hw, h⟩⟩
        · exact Or.inr ⟨hv, Or.inl ⟨hw, h⟩⟩
      · obtain ⟨L, hL, hvL⟩ := C.exists_lawn_of_off_wall hv hw
        rcases hrs ⟨L, hL⟩ with h | h
        · exact Or.inl ⟨hv, Or.inr ⟨hw, ⟨L, hL⟩, hvL, h⟩⟩
        · exact Or.inr ⟨hv, Or.inr ⟨hw, ⟨L, hL⟩, hvL, h⟩⟩
  have hsep : ∀ s t, s ∈ As → t ∈ Bs → s ≠ t ∧ vertexPt P_pres.Γ s ≠ vertexPt P_pres.Γ t := by
    intro s t hs ht
    refine ⟨fun h => disjoint_left.mp hdisj hs (h ▸ ht), fun h => ?_⟩
    exact disjoint_left.mp cut.disj (hX s hs) (h ▸ hY t ht)
  have hag₀ : ∃ φ₀ : Circle ≃ₜ subBd P_pres.Δ₀, DrawingAgreesWithOArcHomeo P_pres.Γ N.Ω₀
    (subBd P_pres.Δ₀) φ₀ := by
    rcases P_pres.agrees_Δ₀ with ⟨h, -⟩ | ⟨-, φ₀, _, h⟩
    · exfalso
      obtain ⟨x, hx⟩ := C.disc₀.nonempty_discInt
      rw [h] at hx
      exact hx.1
    · exact ⟨φ₀, h⟩
  obtain ⟨φ₀, hφ₀⟩ := hag₀
  have hfence : N.Ω₀.IsFence (inS As) (inS Bs) := by
    refine ⟨fun v h => h.1, fun v h => h.1, hABd, hABu, ?_⟩
    intro a₁ ha₁ a₂ ha₂ _ b₁ hb₁ b₂ hb₂ _ hcr
    obtain ⟨K₁, s₁, hK₁, hs₁⟩ := hchord As a₁ ha₁
    obtain ⟨K₂, s₂, hK₂, hs₂⟩ := hchord As a₂ ha₂
    obtain ⟨K₃, s₃, hK₃, hs₃⟩ := hchord Bs b₁ hb₁
    obtain ⟨K₄, s₄, hK₄, hs₄⟩ := hchord Bs b₂ hb₂
    have hconn : ∀ {Z K W : Set EuclideanPlane} {s₁ s₂ : EuclideanPlane},
        IsConnected Z → IsConnected K → IsConnected W → s₁ ∈ Z → s₁ ∈ K → s₂ ∈ Z → s₂ ∈ W →
        IsConnected (Z ∪ K ∪ W) := by
      intro Z K W s₁ s₂ hZ hK hW h₁ h₂ h₃ h₄
      exact (hZ.union ⟨s₁, h₁, h₂⟩ hK).union ⟨s₂, Or.inl h₃, h₄⟩ hW
    have hXav : X ⊆ (interior P_pres.Δ₀)ᶜ := fun y hy hi =>
      interior_Δ₀_disjoint_wall hi (cut.X_sub hy)
    have hYav : Y ⊆ (interior P_pres.Δ₀)ᶜ := fun y hy hi =>
      interior_Δ₀_disjoint_wall hi (cut.Y_sub hy)
    have hch : ∀ {K : Set EuclideanPlane} {v s : α} {Z' : Set EuclideanPlane},
        IsChord P_pres r K v s → Z' ⊆ wall P_pres → vertexPt P_pres.Γ s ∉ Z' → Disjoint K Z' := by
      intro K v s Z' hK hZ' hs
      rw [disjoint_left]
      intro y hy hy'
      exact hs (hK.wall_eq y hy (hZ' hy') ▸ hy')
    obtain ⟨y, h₁, h₂⟩ := nonempty_inter_of_crosses_on_inner_bd C.disc₀ hφ₀ hcr
      ((mem_vertexSet_iff P_pres.Γ (N.bar₀_subset ha₁.1)).mpr rfl)
      ((mem_vertexSet_iff P_pres.Γ (N.bar₀_subset ha₂.1)).mpr rfl)
      ((mem_vertexSet_iff P_pres.Γ (N.bar₀_subset hb₁.1)).mpr rfl)
      ((mem_vertexSet_iff P_pres.Γ (N.bar₀_subset hb₂.1)).mpr rfl)
      ((cut.compact_X.union hK₁.compact).union hK₂.compact)
      ((cut.compact_Y.union hK₃.compact).union hK₄.compact)
      (hconn cut.conn_X hK₁.conn hK₂.conn (hX _ hs₁) hK₁.mem_r (hX _ hs₂) hK₂.mem_r)
      (hconn cut.conn_Y hK₃.conn hK₄.conn (hY _ hs₃) hK₃.mem_r (hY _ hs₄) hK₄.mem_r)
      (union_subset (union_subset hXav hK₁.avoid) hK₂.avoid)
      (union_subset (union_subset hYav hK₃.avoid) hK₄.avoid)
      (Or.inl (Or.inr hK₁.mem_v)) (Or.inr hK₂.mem_v)
      (Or.inl (Or.inr hK₃.mem_v)) (Or.inr hK₄.mem_v)
    have hdXY := cut.disj
    have hA_not : ∀ {K : Set EuclideanPlane} {v s : α}, IsChord P_pres r K v s → s ∈ As →
        Disjoint K Y := fun hK hs => hch hK cut.Y_sub fun h =>
      disjoint_left.mp hdXY (hX _ hs) h
    have hB_not : ∀ {K : Set EuclideanPlane} {v s : α}, IsChord P_pres r K v s → s ∈ Bs →
        Disjoint K X := fun hK hs => hch hK cut.X_sub fun h =>
      disjoint_left.mp hdXY h (hY _ hs)
    have hcc : ∀ {K K' : Set EuclideanPlane} {v v' s s' : α}, IsChord P_pres r K v s →
        IsChord P_pres r K' v' s' → s ∈ As → s' ∈ Bs → Disjoint K K' := fun hK hK' hs hs' =>
      C.chord_disjoint hprom hK hK' (hsep _ _ hs hs').1 (hsep _ _ hs hs').2
    rcases h₁ with (h₁ | h₁) | h₁ <;> rcases h₂ with (h₂ | h₂) | h₂
    · exact disjoint_left.mp hdXY h₁ h₂
    · exact disjoint_left.mp (hB_not hK₃ hs₃) h₂ h₁
    · exact disjoint_left.mp (hB_not hK₄ hs₄) h₂ h₁
    · exact disjoint_left.mp (hA_not hK₁ hs₁) h₁ h₂
    · exact disjoint_left.mp (hcc hK₁ hK₃ hs₁ hs₃) h₁ h₂
    · exact disjoint_left.mp (hcc hK₁ hK₄ hs₁ hs₄) h₁ h₂
    · exact disjoint_left.mp (hA_not hK₂ hs₂) h₁ h₂
    · exact disjoint_left.mp (hcc hK₂ hK₃ hs₂ hs₃) h₁ h₂
    · exact disjoint_left.mp (hcc hK₂ hK₄ hs₂ hs₄) h₁ h₂
  -- The set `Z`: the ends of the wall edges through the two cut points.
  let Zw : EuclideanPlane → Set α := fun w => {z | z ∈ N.Ω₀.bar ∧ ∃ e i, e ∈ E(Q i) ∧
    w ∈ graphDrawingEdgeSet P_pres.Γ e ∧ N.G.IsLink e (r i) z}
  have hnotV : ∀ w ∈ wall P_pres, w ∉ X → w ∉ Y → w ∉ P_pres.Γ.drawing.V := by
    intro w hw hwX hwY hV
    obtain ⟨v, hv, rfl⟩ := exists_vertexPt_of_mem_V P_pres.Γ hV
    rcases hsplit v hv hw with h | h
    · exact hwX (hX v h)
    · exact hwY (hY v h)
  have hsub : ∀ w ∈ wall P_pres, w ∉ X → w ∉ Y → (Zw w).Subsingleton := by
    rintro w hw hwX hwY z ⟨-, e, i, he, hwe, hl⟩ z' ⟨-, e', i', he', hwe', hl'⟩
    have hee : e = e' := eq_of_mem_edgeSet P_pres.Γ hl.edge_mem hl'.edge_mem hwe hwe'
    subst hee
    have hwi : w ∈ i.1 := by
      obtain ⟨c₁, c₂, A', B', hS, E⟩ := C.exists_ear_of_prominence (hF i).1
      exact E.c_subset_L (graphDrawingEdgeSet_subset_subgraphU_of_mem P_pres.Γ he hwe)
    have hwi' : w ∈ i'.1 := by
      obtain ⟨c₁, c₂, A', B', hS, E⟩ := C.exists_ear_of_prominence (hF i').1
      exact E.c_subset_L (graphDrawingEdgeSet_subset_subgraphU_of_mem P_pres.Γ he' hwe')
    have hii : i = i' := by
      apply Subtype.ext
      by_contra hne
      obtain ⟨v, ⟨hv, -⟩, hxv⟩ := C.lawn_inter_subset (hF i).1 (hF i').1 hne ⟨hwi, hwi'⟩
      rw [(hF i).2.path.pathEnds_eq] at hv
      have hvG : v ∈ V(N.G) := by
        rcases hv with rfl | rfl
        · exact N.bar₀_subset (hF i).2.left_mem
        · exact N.bar₀_subset (hF i).2.right_mem
      rw [mem_vertexSet_iff P_pres.Γ hvG] at hxv
      exact hnotV w hw hwX hwY (hxv ▸ vertexPt_mem_V P_pres.Γ hvG)
    subst hii
    exact hl.right_unique hl'
  have hZcard := ncard_union_le_two (hsub p cut.p_mem cut.p_X cut.p_Y)
    (hsub q cut.q_mem cut.q_X cut.q_Y)
  -- A vertex of the prominence with the other label is in `Z`.
  have hodd : ∀ i, ∀ v ∈ V(Q i), v ≠ r i →
      (((r i ∈ As ∧ v ∈ Bs) ∨ (r i ∈ Bs ∧ v ∈ As)) → v ∈ Zw p ∪ Zw q) := by
    intro i v hv hne hlabel
    obtain ⟨hvb, e, heQ, hl⟩ := hr₂ i v hv hne
    have hsubw : closure (graphDrawingEdgeSet P_pres.Γ e) ⊆ wall P_pres := by
      intro x hx
      exact hUw i (Or.inr (mem_iUnion₂.mpr ⟨e, heQ, hx⟩))
    obtain h | h := edge_meets_wall_cut cut hl hsubw
      (hlabel.imp (fun h => ⟨hX _ h.1, hY _ h.2⟩) fun h => ⟨hY _ h.1, hX _ h.2⟩)
      (hnotV p cut.p_mem cut.p_X cut.p_Y) (hnotV q cut.q_mem cut.q_X cut.q_Y)
    · exact Or.inl ⟨hvb, e, i, heQ, h, hl⟩
    · exact Or.inr ⟨hvb, e, i, heQ, h, hl⟩
  refine ⟨inS As, inS Bs, Zw p ∪ Zw q, hfence, ?_, hZcard, ?_, ?_, ?_⟩
  · rintro z (h | h)
    · exact h.1
    · exact h.1
  · rintro v ⟨hv, hv₀⟩
    refine ⟨hv₀, Or.inl ⟨?_, hv⟩⟩
    exact cut.X_sub (hX v hv)
  · rintro v ⟨hv, hv₀⟩
    refine ⟨hv₀, Or.inl ⟨?_, hv⟩⟩
    exact cut.Y_sub (hY v hv)
  · intro L hL
    let i : {L // IsLawn P_pres L} := ⟨L, hL⟩
    have hmem : ∀ {S T : Set α}, r i ∈ S →
        (∀ v ∈ V(Q i), v ≠ r i → v ∈ T → v ∈ Zw p ∪ Zw q) →
        (∀ v ∈ V(Q i), v ∈ S ∨ v ∈ T) →
        {v ∈ V(N.G) | graphDrawingVertexSet P_pres.Γ v ⊆ subBd L} ⊆ inS S ∪ S ∪ (Zw p ∪ Zw q) := by
      rintro S T hrS hT hST v ⟨hv, hsubv⟩
      have hd := (hF i).1.1.2.1
      have hb : vertexPt P_pres.Γ v ∈ discBd L := by
        rw [← subBd_eq_discBd_plane hd]
        exact (vertexSet_subset_iff hv).mp hsubv
      rcases C.mem_bd_lawn_cases (hF i).1 hv hb with h | ⟨h₁, h₂⟩
      · rcases hST v h with h' | h'
        · exact Or.inl (Or.inr h')
        · by_cases hne : v = r i
          · exact Or.inl (Or.inr (hne ▸ hrS))
          · exact Or.inr (hT v h hne h')
      · exact Or.inl (Or.inl ⟨h₁, Or.inr ⟨h₂, i, Surface.discBd_subset _ hb, hrS⟩⟩)
    have hVsplit : ∀ v ∈ V(Q i), v ∈ As ∨ v ∈ Bs := fun v hv => hsplit v (hVG i v hv) (hwall i v hv)
    rcases hrs i with h | h
    · left
      exact hmem h (fun v hv hne hb => hodd i v hv hne (Or.inl ⟨h, hb⟩)) hVsplit
    · right
      exact hmem h (fun v hv hne ha => hodd i v hv hne (Or.inr ⟨h, ha⟩))
        (fun v hv => (hVsplit v hv).symm)

/-- A vertex drawn in the boundary of a lawn is in `ΩBar₀` or on the wall. -/
theorem bd_lawn_cases {L : Set EuclideanPlane} (hL : IsLawn P_pres L) {v : α}
    (hv : v ∈ V(N.G)) (hb : graphDrawingVertexSet P_pres.Γ v ⊆ subBd L) :
    v ∈ N.Ω₀.bar ∨ vertexPt P_pres.Γ v ∈ wall P_pres := by
  obtain ⟨Q, hQ⟩ := hL
  have hb' : vertexPt P_pres.Γ v ∈ discBd L := by
    rw [← subBd_eq_discBd_plane hQ.1.2.1]
    exact (vertexSet_subset_iff hv).mp hb
  rcases C.mem_bd_lawn_cases hQ hv hb' with h | h
  · right
    obtain ⟨a, b, A, B, hS, E⟩ := C.exists_ear_of_prominence hQ
    exact (C.prominence_U_subset_wall hQ).1 (vertexPt_mem_subgraphU P_pres.Γ h hS.path.le)
  · exact Or.inl h.1

/-- The fence `(A, B)` of `Ω₀` and the set `Z` of Graph Minors IX, page 68. -/
theorem exists_fence_and_Z {N_star : Neighborhood α β} (hpark : IsParkOf P_pres N_star)
    (hcut : ∀ A B : Set α, N_star.Ω.IsFence A B → A.Nonempty → B.Nonempty →
      ∃ X Y p q, IsCircleCut (wall P_pres) X Y p q ∧ (∀ a ∈ A, vertexPt P_pres.Γ a ∈ X) ∧
        (∀ b ∈ B, vertexPt P_pres.Γ b ∈ Y))
    ⦃As Bs : Set α⦄ (hF : N_star.Ω.IsFence As Bs) :
    ∃ A B Z : Set α, N_star.Ω₀.IsFence A B ∧ Z ⊆ N_star.Ω₀.bar ∧ Z.ncard ≤ 2 ∧
      As ∩ N_star.Ω₀.bar ⊆ A ∧ Bs ∩ N_star.Ω₀.bar ⊆ B ∧
      ∀ L, IsLawn P_pres L →
        {v ∈ V(N_star.G) | graphDrawingVertexSet P_pres.Γ v ⊆ subBd L} ⊆ A ∪ As ∪ Z ∨
          {v ∈ V(N_star.G) | graphDrawingVertexSet P_pres.Γ v ⊆ subBd L} ⊆ B ∪ Bs ∪ Z := by
  rw [hpark.2.1]
  have hVs : ∀ v ∈ V(N_star.G), v ∈ V(N.G) := fun v hv => hpark.2.2.2.2.1.vertexSet_mono hv
  have hbar : ∀ v ∈ V(N.G), v ∈ N_star.Ω.bar ↔ vertexPt P_pres.Γ v ∈ wall P_pres := by
    intro v hv
    rw [hpark.2.2.2.2.2.1]
    exact ⟨fun h => (vertexSet_subset_iff hv).mp h.2, fun h => ⟨hv,
      (vertexSet_subset_iff hv).mpr h⟩⟩
  obtain ⟨-, -, hd, hun, -⟩ := id hF
  have hsplit : ∀ v ∈ V(N.G), vertexPt P_pres.Γ v ∈ wall P_pres → v ∈ As ∨ v ∈ Bs := by
    intro v hv hw
    have : v ∈ As ∪ Bs := hun ▸ (hbar v hv).mpr hw
    exact this
  rcases As.eq_empty_or_nonempty with rfl | hA
  · refine ⟨∅, N.Ω₀.bar, ∅, ⟨empty_subset _, Subset.rfl, Set.empty_disjoint _, empty_union _,
      fun _ h => h.elim⟩, empty_subset _, by simp, by simp, inter_subset_right, fun L hL
        => Or.inr ?_⟩
    rintro v ⟨hv, hb⟩
    rcases C.bd_lawn_cases hL (hVs v hv) hb with h | h
    · exact Or.inl (Or.inl h)
    · rcases hsplit v (hVs v hv) h with h' | h'
      · exact h'.elim
      · exact Or.inl (Or.inr h')
  rcases Bs.eq_empty_or_nonempty with rfl | hB
  · refine ⟨N.Ω₀.bar, ∅, ∅, ⟨Subset.rfl, empty_subset _, Set.disjoint_empty _, union_empty _,
      fun _ _ _ _ _ _ h => h.elim⟩, empty_subset _, by simp, inter_subset_right, by simp,
      fun L hL => Or.inl ?_⟩
    rintro v ⟨hv, hb⟩
    rcases C.bd_lawn_cases hL (hVs v hv) hb with h | h
    · exact Or.inl (Or.inl h)
    · rcases hsplit v (hVs v hv) h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact h'.elim
  obtain ⟨X, Y, p, q, cut, hX, hY⟩ := hcut As Bs hF hA hB
  obtain ⟨A, B, Z, h₁, h₂, h₃, h₄, h₅, h₆⟩ := C.exists_fence_and_Z_of_cut hbar hd hun cut hX hY
  refine ⟨A, B, Z, h₁, h₂, h₃, h₄, h₅, fun L hL => ?_⟩
  rcases h₆ L hL with h | h
  · exact Or.inl (fun v hv => h ⟨hVs v hv.1, hv.2⟩)
  · exact Or.inr (fun v hv => h ⟨hVs v hv.1, hv.2⟩)

/-- A path of `G*` is drawn in the union of `Δ₀` with the lawns. -/
theorem subgraphU_subset_wallDisc {N_star : Neighborhood α β} (hpark : IsParkOf P_pres N_star)
    {P : Graph α β} (hP : P ≤ N_star.G) :
    graphDrawingSubgraphU P_pres.Γ P ⊆ wallDisc P_pres := by
  have hle : N_star.G ≤ N.G := hpark.2.2.2.2.1
  rintro x (hx | hx)
  · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    have hv' := hP.vertexSet_mono hv
    rw [hpark.2.2.1] at hv'
    exact hv'.2 hxv
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    have he' := hP.edgeSet_mono he
    rw [hpark.2.2.2.1] at he'
    exact closure_minimal he'.2 C.isClosedDisc_wallDisc.isCompact.isClosed hxe

/-- A path of `G*` with distinct ends in `ΩBar₀ ∪ ΩBar*`, and no internal vertex there, is drawn in
one
lawn, so both of its ends are drawn in the boundary of that lawn. -/
theorem exists_lawn_of_park_path {N_star : Neighborhood α β} (hpark : IsParkOf P_pres N_star)
    ⦃P' : Graph α β⦄ ⦃x y : α⦄ (hP : IsGraphPathWithEnds N_star.G P' x y) (hxy : x ≠ y)
    (hx : x ∈ N_star.Ω₀.bar ∪ N_star.Ω.bar) (hy : y ∈ N_star.Ω₀.bar ∪ N_star.Ω.bar)
    (hd : Disjoint (V(P') \ {x, y}) (N_star.Ω₀.bar ∪ N_star.Ω.bar)) :
    ∃ L, IsLawn P_pres L ∧ graphDrawingVertexSet P_pres.Γ x ⊆ subBd L ∧
      graphDrawingVertexSet P_pres.Γ y ⊆ subBd L := by
  have hle : N_star.G ≤ N.G := hpark.2.2.2.2.1
  have hP' := hP.mono hle
  have hbar : ∀ v ∈ V(N.G), v ∈ N_star.Ω.bar ↔ vertexPt P_pres.Γ v ∈ wall P_pres := by
    intro v hv
    rw [hpark.2.2.2.2.2.1]
    exact ⟨fun h => (vertexSet_subset_iff hv).mp h.2, fun h => ⟨hv,
      (vertexSet_subset_iff hv).mpr h⟩⟩
  have hΩ₀ := hpark.2.1
  obtain ⟨hl, hne⟩ := isLineWithEnds_graphDrawingSubgraphU P_pres.Γ hP' hxy
  rw [vertexEquiv_eq_vertexPt, vertexEquiv_eq_vertexPt] at hl hne
  have hxG : x ∈ V(N.G) := hP'.le.vertexSet_mono hP'.left_mem
  have hyG : y ∈ V(N.G) := hP'.le.vertexSet_mono hP'.right_mem
  have hconv : ∀ {L : Set EuclideanPlane} {v : α}, IsClosedDisc L → v ∈ V(N.G) →
      vertexPt P_pres.Γ v ∈ discBd L → graphDrawingVertexSet P_pres.Γ v ⊆ subBd L := by
    intro L v hL hv h
    rw [vertexSet_subset_iff hv, subBd_eq_discBd_plane hL]
    exact h
  set T := graphDrawingSubgraphU P_pres.Γ P' \ {vertexPt P_pres.Γ x, vertexPt P_pres.Γ y} with hT
  have hT₀ : ∀ t ∈ T, t ∉ P_pres.Δ₀ := by
    intro t ht ht₀
    obtain ⟨v, hv, rfl⟩ := C.exists_bar_of_mem (subgraphU_subset_U P_pres.Γ hP'.le ht.1) ht₀
    have hvP := mem_vertexSet_of_vertexPt_mem P_pres.Γ hP'.le (N.bar₀_subset hv) ht.1
    refine disjoint_left.mp hd ⟨hvP, ?_⟩ (Or.inl (hΩ₀ ▸ hv))
    rintro (rfl | rfl)
    · exact ht.2 (Or.inl rfl)
    · exact ht.2 (Or.inr rfl)
  by_cases hcase : ∃ t ∈ T, t ∈ wall P_pres
  · obtain ⟨t, ht, htw⟩ := hcase
    have hnt : ∀ v ∈ V(P'), vertexPt P_pres.Γ v ∈ wall P_pres → v = x ∨ v = y := by
      intro v hv hw
      by_contra hn
      push Not at hn
      exact disjoint_left.mp hd ⟨hv, by rintro (h | h); exacts [hn.1 h, hn.2 h]⟩
        (Or.inr ((hbar v (hP'.le.vertexSet_mono hv)).mpr hw))
    rcases mem_subgraphU_cases P_pres.Γ hP'.le ht.1 with ⟨v, hv, rfl⟩ | ⟨e, he, hte, htV⟩
    · rcases hnt v hv htw with rfl | rfl
      · exact (ht.2 (Or.inl rfl)).elim
      · exact (ht.2 (Or.inr rfl)).elim
    rcases C.wall_subset htw with h | h
    · exact (hT₀ t ht (subBd_subset_of_isClosed C.disc₀.isCompact.isClosed h)).elim
    obtain ⟨Q, ⟨L, hL⟩, htQ⟩ := mem_iUnion₂.mp h
    obtain ⟨a, b, A, B, hS, E⟩ := C.exists_ear_of_prominence hL
    rcases mem_subgraphU_cases P_pres.Γ hS.path.le htQ with ⟨v, hv, rfl⟩ | ⟨f, hf, htf, -⟩
    · exact (htV (vertexPt_mem_V P_pres.Γ (hS.path.le.vertexSet_mono hv))).elim
    have hef : e = f := eq_of_mem_edgeSet P_pres.Γ (hP'.le.edgeSet_mono he)
      (hS.path.le.edgeSet_mono hf) hte htf
    subst hef
    obtain ⟨u, w, hlP⟩ := P'.exists_isLink_of_mem_edgeSet he
    have hlG := hlP.mono hP'.le
    have hlQ : Q.IsLink e u w := (hS.path.le.isLink_iff hf).mpr hlG
    have huw : u ≠ w := by
      rintro rfl
      exact C.simple.1 e hlG.edge_mem u hlG
    have hUw := (C.prominence_U_subset_wall hL).1
    have hu := hnt u hlP.left_mem (hUw (vertexPt_mem_subgraphU P_pres.Γ hlQ.left_mem hS.path.le))
    have hw := hnt w hlP.right_mem (hUw (vertexPt_mem_subgraphU P_pres.Γ hlQ.right_mem hS.path.le))
    have hbd : ∀ v ∈ V(Q), v ∈ V(N.G) → graphDrawingVertexSet P_pres.Γ v ⊆ subBd L := by
      intro v hv hvG
      refine hconv hL.1.2.1 hvG ?_
      exact E.bdL ▸ Or.inr (vertexPt_mem_subgraphU P_pres.Γ hv hS.path.le)
    refine ⟨L, ⟨Q, hL⟩, ?_⟩
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact (huw rfl).elim
    · exact ⟨hbd _ hlQ.left_mem hxG, hbd _ hlQ.right_mem hyG⟩
    · exact ⟨hbd _ hlQ.right_mem hxG, hbd _ hlQ.left_mem hyG⟩
    · exact (huw rfl).elim
  · push Not at hcase
    obtain ⟨t, ht⟩ : T.Nonempty := hl.nonempty_sdiff
    have htW : t ∈ wallDisc P_pres := C.subgraphU_subset_wallDisc hpark hP.le ht.1
    have htL : ∃ L, IsLawn P_pres L ∧ t ∈ L := by
      rcases htW with h | h
      · exact (hT₀ t ht h).elim
      · obtain ⟨L, hL, htL⟩ := mem_iUnion₂.mp h
        exact ⟨L, hL, htL⟩
    obtain ⟨L, hL, htL⟩ := htL
    obtain ⟨Q, hQ⟩ := id hL
    obtain ⟨a, b, A, B, hS, E⟩ := C.exists_ear_of_prominence hQ
    have hdT : Disjoint T (discBd L) := by
      rw [disjoint_left, E.bdL]
      rintro y' hy' (h | h)
      · exact hT₀ y' hy' (Surface.discBd_subset _ (E.A_subset h))
      · exact hcase y' hy' ((C.prominence_U_subset_wall hQ).1 h)
    have hsubL : T ⊆ L := by
      rcases subset_interior_or_compl E.disc hl.isPreconnected_diff hdT with h | h
      · exact h.trans interior_subset
      · exact (h ht htL).elim
    have hcl : graphDrawingSubgraphU P_pres.Γ P' ⊆ L :=
      hl.subset_closure_diff.trans (closure_minimal hsubL E.disc.isCompact.isClosed)
    have hend : ∀ {v : α}, v ∈ V(P') → v ∈ N_star.Ω₀.bar ∪ N_star.Ω.bar →
        graphDrawingVertexSet P_pres.Γ v ⊆ subBd L := by
      intro v hv hb
      have hvG := hP'.le.vertexSet_mono hv
      have hvL := hcl (vertexPt_mem_subgraphU P_pres.Γ hv hP'.le)
      refine hconv E.disc hvG ?_
      rcases hb with h | h
      · have hv₀ : vertexPt P_pres.Γ v ∈ P_pres.Δ₀ :=
          subBd_subset_of_isClosed C.disc₀.isCompact.isClosed
            (IsCleanPresentation.vertexPt_mem_subBd (hΩ₀ ▸ h))
        exact E.bdL ▸ Or.inl (E.L_inter ▸ ⟨hvL, hv₀⟩)
      · exact E.bdL ▸ Or.inr ((C.prominence_U_subset_wall hQ).2 ⟨hvL, (hbar v hvG).mp h⟩)
    exact ⟨L, hL, hend hP'.left_mem hx, hend hP'.right_mem hy⟩

/-- The park of a clean presentation exists. It is a regular park, and the neighborhood outside the
wall is rural. -/
theorem exists_regular_park :
    ∃ (N_star : Neighborhood α β) (hreg : IsRegularParkOf P_pres N_star),
      (outerParkNeighborhood P_pres hreg.isParkOf).IsRural := by
  classical
  have hdW := C.isClosedDisc_wallDisc
  obtain ⟨φ, hφ_cw⟩ := exists_isClockwiseDiscHomeo hdW
  let Vs : Set α := {v ∈ V(N.G) | graphDrawingVertexSet P_pres.Γ v ⊆ wallDisc P_pres}
  let Es : Set β := {e ∈ E(N.G) | graphDrawingEdgeSet P_pres.Γ e ⊆ wallDisc P_pres}
  let K : Set α := {v ∈ V(N.G) | graphDrawingVertexSet P_pres.Γ v ⊆ wall P_pres}
  have hwW : wall P_pres ⊆ wallDisc P_pres :=
    subBd_subset_of_isClosed hdW.isCompact.isClosed
  have hKV : K ⊆ Vs := fun v hv => ⟨hv.1, hv.2.trans hwW⟩
  obtain ⟨Ωs, hbar, hag, hcut⟩ := exists_cyclicPerm_of_oArc P_pres.Γ φ (K := K)
    (fun v hv => hv.1) (N.finite_V.subset fun v hv => hv.1)
    (fun v hv => (vertexSet_subset_iff hv.1).mp hv.2)
  let Gs : Graph α β := (N.G.induce Vs).restrict Es
  have hle : Gs ≤ N.G := restrict_le.trans (N.G.induce_le fun _ hv => hv.1)
  have hends : ∀ {e : β} {u w : α}, e ∈ Es → N.G.IsLink e u w → u ∈ Vs := by
    intro e u w he hl
    refine ⟨hl.left_mem, (graphDrawingVertexSet_subset_closure_edge P_pres.Γ hl).trans ?_⟩
    exact closure_minimal he.2 hdW.isCompact.isClosed
  have hE : E(Gs) = Es := by
    change E((N.G.induce Vs).restrict Es) = Es
    rw [edgeSet_restrict, inter_eq_right]
    intro e he
    obtain ⟨u, w, hl⟩ := N.G.exists_isLink_of_mem_edgeSet he.1
    exact ⟨u, w, hl, hends he hl, hends he hl.symm⟩
  have hV₀ : N.Ω₀.bar ⊆ Vs := by
    intro v hv
    refine ⟨N.bar₀_subset hv, (vertexSet_subset_iff (N.bar₀_subset hv)).mpr ?_⟩
    exact Δ₀_subset_wallDisc (subBd_subset_of_isClosed C.disc₀.isCompact.isClosed
      (IsCleanPresentation.vertexPt_mem_subBd hv))
  let N_star : Neighborhood α β :=
    { G := Gs
      Ω := Ωs
      Ω₀ := N.Ω₀
      finite_V := N.finite_V.subset hle.vertexSet_mono
      finite_E := N.finite_E.subset hle.edgeSet_mono
      bar_subset := hbar ▸ hKV
      bar₀_subset := hV₀ }
  have hpark : IsParkOf P_pres N_star :=
    ⟨C.simple, rfl, rfl, hE, hle, hbar, hdW, φ, hφ_cw, hag⟩
  have hreg : IsRegularParkOf P_pres N_star :=
    { isRegularPresentation := C.isRegularPresentation
      isParkOf := hpark
      exists_fence_and_Z := C.exists_fence_and_Z hpark hcut
      exists_lawn_of_park_path := C.exists_lawn_of_park_path hpark }
  refine ⟨N_star, hreg, ?_⟩
  have hint : ∀ x, x ∈ wall P_pres → x ∉ interior (wallDisc P_pres) := fun x hx hi =>
    not_mem_wall_of_interior hi hx
  have hwΔ : wall P_pres ⊆ P_pres.Δ := hwW.trans (wallDisc_subset_Δ P_pres)
  obtain ⟨P', -, -, -, -⟩ := Presentation.exists_of_le (N' := outerParkNeighborhood P_pres hpark)
    P_pres (outerParkGraph_le P_pres) (Δ' := P_pres.Δ) (Δ₀' := wallDisc P_pres)
    P_pres.isClosedDisc_Δ (wallDisc_subset_Δ P_pres) (by
      intro x hx
      change x ∈ graphDrawingSubgraphU P_pres.Γ (outerParkGraph P_pres) at hx
      rcases mem_subgraphU_cases P_pres.Γ (outerParkGraph_le P_pres) hx with ⟨v, hv, rfl⟩ | ⟨e, he,
        hxe, -⟩
      · have hvG := (outerParkGraph_le P_pres).vertexSet_mono hv
        have h := (vertexSet_subset_iff hvG).mp (hv : v ∈ outerParkVerts P_pres).2
        rcases h with h | h
        · exact ⟨hwΔ h, hint _ h⟩
        · exact ⟨h.1, fun hi => h.2 (interior_subset hi)⟩
      · have he' : e ∈ outerParkEdges P_pres := by
          rw [← edgeSet_outerParkGraph]
          exact he
        rcases he'.2 with h | h
        · exact ⟨hwΔ (h.2 hxe), hint _ (h.2 hxe)⟩
        · exact ⟨(h.2 hxe).1, fun hi => (h.2 hxe).2 (interior_subset hi)⟩)
    (fun v hv => P_pres.mem_bd_Δ_iff v hv.1)
    (fun v hv => by
      change _ ↔ v ∈ Ωs.bar
      rw [hbar]
      exact ⟨fun h => ⟨hv.1, h⟩, fun h => h.2⟩)
    P_pres.agrees_Δ (Or.inr ⟨hdW, φ, hφ_cw, hag⟩)
  exact ⟨P'.Γ, P'.Δ, P'.Δ₀, P'.isClosedDisc_Δ, P'.Δ₀_subset_Δ, P'.U_subset, P'.mem_bd_Δ_iff,
    P'.mem_bd_Δ₀_iff, P'.agrees_Δ, P'.agrees_Δ₀⟩

end IsCleanPresentation

/-- If the two sides of a composition have no common vertex, every triangle lies on one side. -/
theorem triangle_le_of_disjoint {G H₁ H₂ T : Graph α β} (hsep : IsGraphSeparation G H₁ H₂)
    (hd : V(H₁) ∩ V(H₂) = ∅) (hT : IsTriangle G T) : T ≤ H₁ ∨ T ≤ H₂ := by
  obtain ⟨v₁, v₂, v₃, e₁, e₂, e₃, -, -, -, -, -, -, hVT, hET, hl₁, hl₂, hl₃⟩ :=
    hT.exists_verts_and_edges
  have hle : T ≤ G := hT.1.1
  have hl₁' := hl₁.mono hle
  have hl₂' := hl₂.mono hle
  have hl₃' := hl₃.mono hle
  have hside : ∀ {e : β} {u w : α}, G.IsLink e u w →
      (H₁.IsLink e u w ∨ H₂.IsLink e u w) := by
    intro e u w hl
    have he : e ∈ E(H₁) ∪ E(H₂) := hsep.2.2.2.1 ▸ hl.edge_mem
    rcases he with h | h
    · exact Or.inl ((hsep.1.isLink_iff h).mpr hl)
    · exact Or.inr ((hsep.2.1.isLink_iff h).mpr hl)
  have hno : ∀ {v : α}, v ∈ V(H₁) → v ∈ V(H₂) → False := fun h₁ h₂ =>
    Set.eq_empty_iff_forall_notMem.mp hd _ ⟨h₁, h₂⟩
  have hle_of : ∀ H : Graph α β, H ≤ G → H.IsLink e₁ v₂ v₃ → H.IsLink e₂ v₁ v₃ →
      H.IsLink e₃ v₁ v₂ → T ≤ H := by
    intro H hH h₁ h₂ h₃
    rw [(Compatible.of_le_le hle hH).le_iff]
    constructor
    · rw [hVT]
      rintro v (rfl | rfl | rfl)
      exacts [h₂.left_mem, h₁.left_mem, h₁.right_mem]
    · rw [hET]
      rintro e (rfl | rfl | rfl)
      exacts [h₁.edge_mem, h₂.edge_mem, h₃.edge_mem]
  rcases hside hl₁' with h₁ | h₁ <;> rcases hside hl₂' with h₂ | h₂ <;>
    rcases hside hl₃' with h₃ | h₃
  · exact Or.inl (hle_of _ hsep.1 h₁ h₂ h₃)
  · exact (hno h₂.left_mem h₃.left_mem).elim
  · exact (hno h₁.right_mem h₂.right_mem).elim
  · exact (hno h₁.left_mem h₃.right_mem).elim
  · exact (hno h₂.right_mem h₁.right_mem).elim
  · exact (hno h₂.right_mem h₁.right_mem).elim
  · exact (hno h₃.left_mem h₂.left_mem).elim
  · exact Or.inr (hle_of _ hsep.2.1 h₁ h₂ h₃)

/-- **Graph Minors IX, (11.5)** (pages 69–70):
"Let $G$ be simple, and let $(G, \Omega)$ have sophistication $\le p$. Then there is a
society $(G_1, \Omega_1)$ and a rural neighborhood $(G_2, \Omega, \Omega_1)$ such that* (i)
$G_1, G_2 \subseteq G$, $G_1 \cup G_2 = G$ *and* $V(G_1 \cap G_2) = \bar{\Omega}_1$, (ii)
$(G_1, \Omega_1)$ *has no transaction of cardinality* $> p + 2$ (iii) *for every triangle
$T$ of $G$, either $T \subseteq G_1$ or $T \subseteq G_2$." -/
theorem theorem_11_5_proof (S : Society α β) (hsimple : IsSimpleGraph S.G) {p : ℕ}
    (hsoph : S.HasSophisticationLE p) :
    ∃ (S₁ : Society α β) (N₂ : Neighborhood α β),
      N₂.IsRural ∧
      N₂.Ω = S.Ω ∧
      N₂.Ω₀ = S₁.Ω ∧
      S₁.G ≤ S.G ∧
      N₂.G ≤ S.G ∧
      subgraphUnion S.G S₁.G N₂.G = S.G ∧
      V(subgraphInter S.G S₁.G N₂.G) = S₁.Ω.bar ∧
      (∀ Q_set : Set (Graph α β), S₁.IsTransaction Q_set → Q_set.ncard ≤ p + 2) ∧
      (∀ T : Graph α β, IsTriangle S.G T → T ≤ S₁.G ∨ T ≤ N₂.G) := by
  obtain ⟨H₁, H₂, hcomp, hH₂_rural, hH₁_no⟩ := hsoph
  have hsep := hcomp.1.1
  obtain ⟨P, -, -, hclean⟩ := hH₂_rural.exists_clean
  rcases P.agrees_Δ₀ with ⟨-, hemp⟩ | ⟨hd, -⟩
  · have hbar : H₁.Ω.bar = ∅ := by rw [← hcomp.2.2.1]; exact hemp
    have hV : V(H₁.G) ∩ V(H₂.G) = ∅ := by rw [← hcomp.2.2.2, hbar]
    refine ⟨H₁, H₂, hH₂_rural, hcomp.2.1, hcomp.2.2.1, hsep.1, hsep.2.1, ?_, ?_,
      fun Q hQ => (hH₁_no Q hQ).trans (Nat.le_add_right _ _),
      fun T hT => triangle_le_of_disjoint hsep hV hT⟩
    · exact (Compatible.of_le_le (subgraphUnion_le hsep.1 hsep.2.1) le_rfl).ext
        (by rw [vertexSet_subgraphUnion, hsep.2.2.1])
        (by rw [edgeSet_subgraphUnion hsep.1 hsep.2.1, hsep.2.2.2.1])
    · change V(H₁.G) ∩ V(H₂.G) = H₁.Ω.bar
      rw [hV, hbar]
  · have C : IsCleanPresentation P := ⟨hd, hclean, hsimple.mono hsep.2.1⟩
    obtain ⟨N_star, hreg, hrural⟩ := C.exists_regular_park
    exact composition_of_regular_park S hsimple hcomp hH₁_no hreg hrural

end GraphMinor.GM09
