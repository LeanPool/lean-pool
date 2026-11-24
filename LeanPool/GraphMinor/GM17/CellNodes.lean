/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.RegionFrontier

/-!
# Cells have two nodes and nodes lie on cells

We collect the hypotheses of `RegionBoundaryOArcCriterionStatement` in `Painting.Tame`: there are at
least six nodes, all regions are open discs, and every normal `O`-arc
with at most one node bounds a disc that meets the paint only in the arc. Then every cell has at
least two nodes (`two_nodes`), which is the last part of (8.2) of
Graph Minors XVII (page 182), and every node lies on a cell (`node_on_cell`). To prove them we take
a curve around a cell or around a node. The curve bounds a disc on its other
side, so the surface is covered by two discs, which leaves room for too few nodes.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology Metric GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- Two closed discs with the same boundary in a connected surface are equal, or else they cover the
surface and meet exactly in the boundary. -/
theorem two_discs [ConnectedSpace S] (hS : IsSurface S) {Δ Δ' : Set S} (h : IsClosedDisc Δ)
  (h' : IsClosedDisc Δ') (hb : discBd Δ = discBd Δ') :
    Δ = Δ' ∨ (Δ ∪ Δ' = univ ∧ Δ ∩ Δ' = discBd Δ) := by
  have ht2 : T2Space S := hS.2.1
  obtain ⟨T, tT, j, cap, hT, hTc, hj, -, -⟩ := exists_cap_discs _ S hS rfl
  have hb' : discBd (j '' Δ) = discBd (j '' Δ') := by
    rw [discBd_image hj.isEmbedding, discBd_image hj.isEmbedding, hb]
  rcases two_discs_closed hT (image_emb_disc hj.isEmbedding h) (image_emb_disc hj.isEmbedding h')
    hb' with h1 | ⟨h1, h2⟩
  · exact .inl (hj.injective.image_injective h1)
  · right
    constructor
    · rw [eq_univ_iff_forall]
      intro x
      rcases (h1 ▸ mem_univ (j x) : j x ∈ j '' Δ ∪ j '' Δ') with h3 | h3
      · exact .inl (hj.injective.mem_set_image.mp h3)
      · exact .inr (hj.injective.mem_set_image.mp h3)
    · rw [discBd_image hj.isEmbedding] at h2
      ext x
      have h3 := Set.ext_iff.mp h2 (j x)
      simp only [mem_inter_iff, hj.injective.mem_set_image] at h3
      simpa using h3

/-- A closed disc around a closed disc in a surface that meets a closed set only where the small
disc does. -/
theorem exists_ring_sub [ConnectedSpace S] (hS : IsSurface S) {E Z : Set S} (hE : IsClosedDisc E)
  (hZ : IsClosed Z) (hZb : Z ∩ E ⊆ discBd E) (hEb : E ∩ bd S ⊆ Z) :
    ∃ Δ, IsClosedDisc Δ ∧ E ⊆ Δ ∧ Δ ∩ Z = E ∩ Z ∧ discBd Δ ∩ E = E ∩ Z ∧ Δ ∩ bd S = E ∩ bd S := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  obtain ⟨T, tT, j, cap, hT, hTc, hj, hcap, hcov⟩ := exists_cap_discs _ S hS rfl
  have hTs : IsSurface T := ⟨hT.1, hT.2.1, fun x => (hT.2.2 x).isManifoldPoint⟩
  have ht2T : T2Space T := hT.2.1
  have hfinC := (cuff_statement.{0} S hS).2.1
  let Z' : Set T := j '' Z ∪ ⋃ C ∈ cuffs S, cap C
  have hZ' : IsClosed Z' := (hj.isClosedMap _ hZ).union (hfinC.isClosed_biUnion fun C hC =>
    (hcap C hC).1.isClosed)
  have hbC : ∀ {C : Set S}, C ∈ cuffs S → C ⊆ bd S := fun {C} hC => by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hcapj : ∀ {x : S}, j x ∈ ⋃ C ∈ cuffs S, cap C → x ∈ bd S := fun {x} hx => by
    obtain ⟨C, hC, hw⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hy, he⟩ := ((hcap C hC).2.2 ▸ ⟨⟨x, rfl⟩, hw⟩ : j x ∈ j '' C)
    obtain rfl := hj.injective he
    exact hbC hC hy
  have hjbd : ∀ {x : S}, x ∈ bd S → j x ∈ ⋃ C ∈ cuffs S, cap C := fun {x} hx => by
    have hC : connectedComponentIn (bd S) x ∈ cuffs S := ⟨x, hx, rfl⟩
    refine mem_iUnion₂.mpr ⟨_, hC, ?_⟩
    have h1 : j x ∈ discBd (cap (connectedComponentIn (bd S) x)) := by
      rw [(hcap _ hC).2.1]
      exact mem_image_of_mem _ (mem_connectedComponentIn hx)
    exact discBd_subset _ h1
  have hjZ : ∀ {x : S}, x ∈ E → j x ∈ Z' → x ∈ Z := fun {x} hxE hx => by
    rcases hx with ⟨y, hy, he⟩ | hx
    · exact hj.injective he ▸ hy
    · exact hEb ⟨hxE, hcapj hx⟩
  have hB : IsClosedDisc (j '' E) := image_emb_disc hj.isEmbedding hE
  have hbB : discBd (j '' E) = j '' discBd E := discBd_image hj.isEmbedding _
  have hZB : Z' ∩ j '' E ⊆ discBd (j '' E) := by
    rintro _ ⟨hz, x, hx, rfl⟩
    rw [hbB]
    exact mem_image_of_mem _ (hZb ⟨hjZ hx hz, hx⟩)
  obtain ⟨Δ, hΔ, hsub, hin, hbd⟩ := exists_ring hTs hB (fun x _ => hT.2.2 x) hZ' hZB
  have hΔr : Δ ⊆ range j := by
    intro z hz
    rcases (hcov ▸ mem_univ z : z ∈ range j ∪ ⋃ C ∈ cuffs S, cap C) with h | h
    · exact h
    · have h1 : z ∈ j '' E ∩ Z' := hin ▸ ⟨hz, .inr h⟩
      obtain ⟨y, -, rfl⟩ := h1.1
      exact mem_range_self _
  obtain ⟨hD, hDb⟩ := isClosedDisc_preimage hj hΔ hΔr
  refine ⟨_, hD, fun x hx => hsub (mem_image_of_mem _ hx), ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hx, hxZ⟩
      obtain ⟨y, hy, he⟩ := (hin ▸ ⟨hx, .inl (mem_image_of_mem _ hxZ)⟩ : j x ∈ j '' E ∩ Z').1
      obtain rfl := hj.injective he
      exact ⟨hy, hxZ⟩
    · rintro ⟨hx, hxZ⟩
      exact ⟨hsub (mem_image_of_mem _ hx), hxZ⟩
  · ext x
    constructor
    · rw [hDb]
      rintro ⟨hx, hxE⟩
      have h1 : j x ∈ j '' E ∩ Z' := by
        rw [← hbd]
        exact ⟨hx, mem_image_of_mem _ hxE⟩
      exact ⟨hxE, hjZ hxE h1.2⟩
    · rintro ⟨hx, hxZ⟩
      have h1 : j x ∈ discBd Δ ∩ j '' E := by
        rw [hbd]
        exact ⟨mem_image_of_mem _ hx, .inl (mem_image_of_mem _ hxZ)⟩
      rw [hDb]
      exact ⟨h1.1, hx⟩
  · ext x
    constructor
    · rintro ⟨hx, hxb⟩
      obtain ⟨y, hy, he⟩ := (hin ▸ ⟨hx, .inr (hjbd hxb)⟩ : j x ∈ j '' E ∩ Z').1
      obtain rfl := hj.injective he
      exact ⟨hy, hxb⟩
    · rintro ⟨hx, hxb⟩
      exact ⟨hsub (mem_image_of_mem _ hx), hxb⟩

namespace Painting

/-- The hypotheses of the statement on boundaries of regions. -/
structure Tame (Γ : Painting S) : Prop where
  six : 6 ≤ Γ.N.ncard
  open_disc : ∀ r ∈ Γ.regions, IsOpenDisc r
  curve : ∀ F : Set S, IsOArc F → Γ.IsNormal F → (F ∩ Γ.N).ncard ≤ 1 → ∃ Δ : Set S, IsClosedDisc Δ
    ∧ discBd Δ = F ∧ Δ ∩ Γ.U ⊆ F

variable {Γ : Painting S}

theorem Tame.isOpen (h : Γ.Tame) : ∀ r ∈ Γ.regions, IsOpen r := fun r hr => (h.open_disc r hr).1

/-- The nodes of a cover by two sets are few if each set has few nodes. -/
theorem Tame.not_covered (h : Γ.Tame) {A : Set S} (hA : A.Finite) (hcard : A.ncard ≤ 5)
  (hN : Γ.N ⊆ A) : False := by
  have := Set.ncard_le_ncard hN hA
  have := h.six
  omega

variable [T2Space S]

/-- The closure of a cell without the nodes is off all other closures. -/
theorem others_closed (Γ : Painting S) (G : Set (Set S)) : IsClosed (Γ.N ∪ ⋃ d ∈ Γ.C \ G, closure
  d) :=
  Γ.finite_N.isClosed.union ((Γ.finite_cells.subset sdiff_subset).isClosed_biUnion fun _ _
    => isClosed_closure)

omit [T2Space S] in
theorem mem_U_iff {x : S} : x ∈ Γ.U ↔ x ∈ Γ.N ∨ ∃ d ∈ Γ.C, x ∈ closure d := by
  rw [Γ.U_eq_N_union_biUnion_closure]
  simp

/-- Every cell has two nodes. -/
theorem two_nodes [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {c : Set S}
  (hc : c ∈ Γ.C) : ∃ a ∈ tilde c, ∃ b ∈ tilde c, a ≠ b := by
  classical
  by_contra hne
  push Not at hne
  have hsmall : (tilde c).ncard ≤ 1 := by
    rw [Set.ncard_le_one (Γ.finite_tilde_cell hc)]
    exact hne
  have hbd : ¬ (c ∩ bd S).Nonempty := fun h => by
    obtain ⟨u, v, huv, ht, -⟩ := Γ.border_cell_exists_ends hc h
    exact huv (hne u (ht ▸ .inl rfl) v (ht ▸ .inr rfl))
  have hdisc := Γ.isClosedDisc_closure_cell hc
  let Z : Set S := Γ.N ∪ ⋃ d ∈ Γ.C \ {c}, closure d
  have hZE : closure c ∩ Z ⊆ tilde c := by
    rintro x ⟨hx, h | h⟩
    · rw [← Γ.closure_cell_inter_N hc]
      exact ⟨hx, h⟩
    · obtain ⟨d, hd, hxd⟩ := mem_iUnion₂.mp h
      rw [← Γ.closure_cell_inter_N hc]
      exact ⟨hx, closure_inter_closure hc hd.1 (Ne.symm hd.2) ⟨hx, hxd⟩⟩
  have hEb : closure c ∩ bd S ⊆ Z := fun x hx => by
    refine .inl (Γ.tilde_subset_N hc ⟨hx.1, fun h => hbd ⟨x, h, hx.2⟩⟩)
  obtain ⟨Δ, hΔ, hsub, hin, hbdΔ, -⟩ := exists_ring_sub hS hdisc (others_closed Γ {c}) (fun x hx
    => Γ.tilde_subset_discBd hc (hZE ⟨hx.2, hx.1⟩)) hEb
  have hUZ : ∀ {x}, x ∈ Γ.U → x ∈ discBd Δ → x ∈ tilde c := fun {x} hxU hx => by
    obtain h | ⟨d, hd, hxd⟩ := mem_U_iff.mp hxU
    · exact hZE (hin ▸ ⟨discBd_subset _ hx, .inl h⟩)
    · by_cases hdc : d = c
      · subst hdc
        exact hZE (hbdΔ ▸ ⟨hx, hxd⟩)
      · exact hZE (hin ▸ ⟨discBd_subset _ hx, .inr (mem_iUnion₂.mpr ⟨d, ⟨hd, hdc⟩, hxd⟩)⟩)
  have hnorm : Γ.IsNormal (discBd Δ) := fun x hx => Γ.tilde_subset_N hc (hUZ hx.2 hx.1)
  have hc1 : (discBd Δ ∩ Γ.N).ncard ≤ 1 := by
    refine (Set.ncard_le_ncard
      (fun x (hx : x ∈ discBd Δ ∩ Γ.N) => hUZ (Γ.N_subset hx.2) hx.1)
      (Γ.finite_tilde_cell hc)).trans hsmall
  obtain ⟨Δ', hΔ', hb', hU'⟩ := hΓ.curve _ hΔ.isOArc_discBd hnorm hc1
  obtain ⟨x, hx⟩ := (arcComponentsIn_nonempty hc)
  rcases two_discs hS hΔ hΔ' hb'.symm with he | ⟨hcov, -⟩
  · subst he
    have h1 := hU' ⟨hsub (subset_closure hx), Γ.cell_subset_U hc hx⟩
    exact disjoint_left.mp (Γ.cell_disjoint_N hc) hx (hnorm ⟨h1, Γ.cell_subset_U hc hx⟩)
  · refine hΓ.not_covered (Γ.finite_tilde_cell hc) (by omega) fun n hn => ?_
    rcases (hcov ▸ mem_univ n : n ∈ Δ ∪ Δ') with h | h
    · exact hZE (hin ▸ ⟨h, .inl hn⟩)
    · exact hUZ (Γ.N_subset hn) (hU' ⟨h, Γ.N_subset hn⟩)

/-- A closed disc around an inner point of a surface inside a given open set, with the point in its
inside. -/
theorem exists_small_disc {y : S} (hy : IsInteriorPoint y) {W : Set S} (hW : IsOpen W)
  (hyW : y ∈ W) : ∃ E, IsClosedDisc E ∧ y ∈ E ∧ y ∉ discBd E ∧ E ⊆ W := by
  obtain ⟨U₀, h, g, hc, hU₀, h0⟩ := hy.exists_ballChart hW hyW (R := 2) (by norm_num)
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
  obtain ⟨hD, hbd⟩ := isClosedDisc_closedBall
  obtain ⟨hE, hEb⟩ := isClosedDisc_image_injOn hD (isCompact_closedBall _ _) (hc.gc.mono hsub)
    (fun a ha b hb he => by
    rw [← hc.hg (hsub ha), ← hc.hg (hsub hb), he])
  refine ⟨_, hE, ⟨0, by simp, h0⟩, ?_, ?_⟩
  · rw [hEb, hbd]
    rintro ⟨z, hz, he⟩
    have h1 : z = 0 := by
      rw [← hc.hg (hsub (sphere_subset_closedBall hz)), he, ← h0, hc.hg (by simp)]
    subst h1
    simp at hz
  · rintro _ ⟨z, hz, rfl⟩
    exact hU₀ (hc.gm (hsub hz))

/-- Every node lies on a cell. -/
theorem node_on_cell [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {n : S}
  (hn : n ∈ Γ.N) : ∃ c ∈ Γ.C, n ∈ tilde c := by
  classical
  by_contra hno
  push Not at hno
  by_cases hb : n ∈ bd S
  · have hC : connectedComponentIn (bd S) n ∈ cuffs S := ⟨n, hb, rfl⟩
    have hO : IsOArc (connectedComponentIn (bd S) n) := (cuff_statement.{0} S hS).2.2 _ hC
    obtain ⟨φ⟩ := id hO
    obtain ⟨y, hy, hyn⟩ : ∃ y ∈ connectedComponentIn (bd S) n, y ≠ n := by
      by_cases h1 : (φ 1).1 = n
      · refine ⟨(φ (Circle.exp Real.pi)).1, (φ _).2, fun h2 => ?_⟩
        have h3 : φ (Circle.exp Real.pi) = φ 1 := Subtype.ext (h2.trans h1.symm)
        have h4 := φ.injective h3
        have h5 := congrArg (fun z : Circle => (z : ℂ)) h4
        simp [Circle.coe_exp] at h5
        norm_num at h5
      · exact ⟨_, (φ 1).2, h1⟩
    obtain ⟨I, B, hI, -, hu, -⟩ := hO.lines (mem_connectedComponentIn hb) hy (Ne.symm hyn)
    have hIb : I ⊆ bd S := (hu ▸ subset_union_left : I ⊆ _).trans (connectedComponentIn_subset _ _)
    obtain ⟨c, hc, -, -, hnc, -⟩ := exists_border_cell (Δ := univ) hI hIb (subset_univ _) hn
      (fun c _ => .inl (subset_univ _))
    exact hno c hc hnc
  · have hiso : ∀ d ∈ Γ.C, n ∉ closure d := fun d hd h => hno d hd ⟨h, fun h' => disjoint_left.mp
      (Γ.cell_disjoint_N hd) h' hn⟩
    have hZ : IsClosed ((Γ.N \ {n}) ∪ ⋃ d ∈ Γ.C, closure d) :=
      (Γ.finite_N.subset sdiff_subset).isClosed.union (Γ.finite_cells.isClosed_biUnion fun _ _
        => isClosed_closure)
    obtain ⟨E, hE, hnE, hnb, hEW⟩ := exists_small_disc (by_contra hb : IsInteriorPoint n)
      hZ.isOpen_compl (by
      rintro (h | h)
      · exact h.2 rfl
      · obtain ⟨d, hd, h⟩ := mem_iUnion₂.mp h
        exact hiso d hd h)
    have hEU : E ∩ Γ.U ⊆ {n} := by
      rintro x ⟨hx, hxU⟩
      obtain h | ⟨d, hd, hxd⟩ := mem_U_iff.mp hxU
      · by_contra hne
        exact hEW hx (.inl ⟨h, hne⟩)
      · exact absurd (.inr (mem_iUnion₂.mpr ⟨d, hd, hxd⟩)) (hEW hx)
    have hFU : discBd E ∩ Γ.U = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨hx, hxU⟩
      have h1 := hEU ⟨discBd_subset _ hx, hxU⟩
      exact hnb (h1 ▸ hx)
    have hnorm : Γ.IsNormal (discBd E) := by
      intro x hx
      exact absurd hx (by rw [hFU]; exact notMem_empty _)
    have hF0 : discBd E ∩ Γ.N = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨hx, hxN⟩
      exact (eq_empty_iff_forall_notMem.mp hFU x) ⟨hx, Γ.N_subset hxN⟩
    obtain ⟨Δ', hΔ', hb', hU'⟩ := hΓ.curve _ hE.isOArc_discBd hnorm (by rw [hF0]; simp)
    rcases two_discs hS hE hΔ' hb'.symm with he | ⟨hcov, -⟩
    · subst he
      have h1 := hU' ⟨hnE, Γ.N_subset hn⟩
      exact hnb h1
    · refine hΓ.not_covered (finite_singleton n) (by simp) fun x hx => ?_
      rcases (hcov ▸ mem_univ x : x ∈ E ∪ Δ') with h | h
      · exact hEU ⟨h, Γ.N_subset hx⟩
      · exact ((eq_empty_iff_forall_notMem.mp hF0 x) ⟨hb' ▸ hU' ⟨h, Γ.N_subset hx⟩, hx⟩).elim

end Painting

end GraphMinor.GM17
