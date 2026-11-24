/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Theta

/-!
# The frontier of a region at a node

Let `Γ` be a tame painting. A node on the frontier of a region `r` is an end of exactly two sides of
`r`. There are at least two, because just beyond a side of a cell at a node
there is more of the frontier (`near_region`, `other_side`). There are at most two (`three_sides`):
for three sides at a node, we close up curves through `r` and the node. The
hypothesis on curves with one node gives three discs, and these cover the surface by `theta_cover`,
which is impossible. This is the content of the proof of (8.2) of
Graph Minors XVII (page 182).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

namespace Painting

variable {Γ : Painting S} [T2Space S]

omit [T2Space S] in
/-- Near a point of the boundary of a cell in the closure of a region, there is more of the frontier
off a given line of the boundary of the cell. -/
theorem near_region [ConnectedSpace S] (hS : IsSurface S) (hreg : ∀ r ∈ Γ.regions, IsOpen r) {r c L
  : Set S} {a b : S} (hr : r ∈ Γ.regions) (hc : c ∈ Γ.C) (ha : a ∈ closure r)
    (hL : IsLineWithEnds L a b) (hLc : L ⊆ discBd (closure c)) : a ∈ closure ((closure r \ r) \ L)
      := by
  obtain ⟨T, tT, j, cap, hT, hTc, hj, hcap, hcov⟩ := exists_cap_discs _ S hS rfl
  have hTs : IsSurface T := ⟨hT.1, hT.2.1, fun x => (hT.2.2 x).isManifoldPoint⟩
  have ht2T : T2Space T := hT.2.1
  have hfinC := (cuff_statement.{0} S hS).2.1
  have hbC : ∀ {C : Set S}, C ∈ cuffs S → C ⊆ bd S := fun {C} hC => by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hrb : Disjoint r (bd S) := disjoint_left.mpr fun x hx hb => region_subset hr hx
    (Γ.bd_subset hb)
  have hW : IsOpen (j '' r) := by
    have h1 : (j '' r)ᶜ = j '' rᶜ ∪ ⋃ C ∈ cuffs S, cap C := by
      ext y
      constructor
      · intro hy
        rcases (hcov ▸ mem_univ y : y ∈ range j ∪ ⋃ C ∈ cuffs S, cap C) with ⟨x, rfl⟩ | h
        · exact .inl ⟨x, fun hx => hy (mem_image_of_mem _ hx), rfl⟩
        · exact .inr h
      · rintro (⟨x, hx, rfl⟩ | h) hm
        · exact hx (hj.injective.mem_set_image.mp hm)
        · obtain ⟨C, hC, hw⟩ := mem_iUnion₂.mp h
          obtain ⟨x, hx, rfl⟩ := hm
          obtain ⟨y, hy, he⟩ := ((hcap C hC).2.2 ▸ ⟨⟨x, rfl⟩, hw⟩ : j x ∈ j '' C)
          obtain rfl := hj.injective he
          exact disjoint_left.mp hrb hx (hbC hC hy)
    rw [← isClosed_compl_iff, h1]
    exact (hj.isClosedMap _ (hreg r hr).isClosed_compl).union (hfinC.isClosed_biUnion fun C hC =>
      (hcap C hC).1.isClosed)
  have hdisc := Γ.isClosedDisc_closure_cell hc
  have hB := image_emb_disc hj.isEmbedding hdisc
  have hd : Disjoint (j '' r) (j '' closure c) := (disjoint_image_iff hj.injective).mpr
    (region_disjoint_closure hr hc)
  have hcl : closure (j '' r) = j '' closure r := hj.closure_image_eq r
  have h1 := frontier_near hTs hB (fun x _ => hT.2.2 x) hW hd (hcl ▸ mem_image_of_mem _ ha)
    (hL.map_of_embedding hj.isEmbedding) (by
    rw [discBd_image hj.isEmbedding]
    exact image_mono hLc)
  have hfr : frontier (j '' r) \ j '' L = j '' ((closure r \ r) \ L) := by
    rw [hW.frontier_eq, hcl]
    ext y
    constructor
    · rintro ⟨⟨⟨x, hx, rfl⟩, h1⟩, h2⟩
      exact ⟨x, ⟨⟨hx, fun h => h1 (mem_image_of_mem _ h)⟩, fun h => h2 (mem_image_of_mem _ h)⟩, rfl⟩
    · rintro ⟨x, ⟨⟨hx, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨mem_image_of_mem _ hx, fun h => h1 (hj.injective.mem_set_image.mp h)⟩,
        fun h => h2 (hj.injective.mem_set_image.mp h)⟩
  rw [hfr, hj.closure_image_eq] at h1
  exact hj.injective.mem_set_image.mp h1

theorem finite_sideOf (r : Set S) : {L | Γ.SideOf r L}.Finite :=
  finite_gaps.subset fun _ ⟨c, u, v, hL, _⟩ => ⟨c, u, v, hL.1⟩

/-- At a point in the closure of a region near which there is more of its frontier off a line, there
is a side of the region off the line. -/
theorem exists_side_near [CompactSpace S] [ConnectedSpace S] (hS : IsSurface S)
  (hreg : ∀ r ∈ Γ.regions, IsOpen r) (h2 : ∀ c ∈ Γ.C, ∃ a ∈ tilde c, ∃ b ∈ tilde c, a ≠ b)
    {r L : Set S} {a : S} (hr : r ∈ Γ.regions) (haL : a ∈ L)
    (h : a ∈ closure ((closure r \ r) \ L)) : ∃ L', Γ.SideOf r L' ∧ a ∈ L' ∧ (L' \ L).Nonempty := by
  classical
  have hsub : (closure r \ r) \ L ⊆ (Γ.N \ {a}) ∪ ⋃ L' ∈ {L' | Γ.SideOf r L'}, L' \ L := by
    rintro y ⟨⟨hy, hyr⟩, hyL⟩
    by_cases hyN : y ∈ Γ.N
    · exact .inl ⟨hyN, fun e => hyL ((show y = a from e) ▸ haL)⟩
    · obtain ⟨L', hL', hyL'⟩ := frontier_region hS hreg h2 hr hy hyr hyN
      exact .inr (mem_iUnion₂.mpr ⟨L', hL', hyL', hyL⟩)
  have h3 := closure_mono hsub h
  rw [closure_union, (finite_sideOf r).closure_biUnion, (Γ.finite_N.subset
    sdiff_subset).isClosed.closure_eq] at h3
  rcases h3 with h3 | h3
  · exact absurd rfl h3.2
  · obtain ⟨L', hL', ha'⟩ := mem_iUnion₂.mp h3
    obtain ⟨c, u, v, hs, -⟩ := id hL'
    exact ⟨L', hL', closure_minimal sdiff_subset hs.1.2.1.isCompact.isClosed ha',
      closure_nonempty_iff.mp ⟨_, ha'⟩⟩

omit [T2Space S] in
theorem IsSide.exists_end {c L : Set S} {u v a : S} (h : Γ.IsSide c L u v) (ha : a ∈ L)
  (haN : a ∈ Γ.N) : ∃ b, Γ.IsSide c L a b := by
  rcases (h.1.2.2.2.le ⟨ha, haN⟩ : a ∈ ({u, v} : Set S)) with rfl | rfl
  · exact ⟨v, h⟩
  · exact ⟨u, h.symm⟩

/-- A second side of a region at a node of a side. -/
theorem other_side [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {r L : Set S} {a : S}
  (hr : r ∈ Γ.regions) (hL : Γ.SideOf r L) (ha : a ∈ L) (haN : a ∈ Γ.N) :
    ∃ L', Γ.SideOf r L' ∧ a ∈ L' ∧ L' ≠ L := by
  have hcS : CompactSpace S := hS.1
  obtain ⟨c, u, v, hs, hcl⟩ := hL
  obtain ⟨b, hs'⟩ := hs.exists_end ha haN
  have h1 := near_region hS hΓ.isOpen hr hs.1.1 (hcl ha) hs'.1.2.1 hs'.1.2.2.1
  obtain ⟨L', h2, h3, h4⟩ := exists_side_near hS hΓ.isOpen (fun c hc => two_nodes hS hΓ hc) hr ha h1
  refine ⟨L', h2, h3, ?_⟩
  rintro rfl
  obtain ⟨z, hz⟩ := h4
  exact hz.2 hz.1

/-- A node in the closure of a region lies on a side of the region. -/
theorem first_side [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {r : Set S} {a : S}
  (hr : r ∈ Γ.regions) (ha : a ∈ closure r) (haN : a ∈ Γ.N) : ∃ L, Γ.SideOf r L ∧ a ∈ L := by
  have hcS : CompactSpace S := hS.1
  obtain ⟨c, hc, hac⟩ := node_on_cell hS hΓ haN
  obtain ⟨x, hx, y, hy, hxy⟩ := two_nodes hS hΓ hc
  obtain ⟨b, hb, hba⟩ : ∃ b ∈ tilde c, a ≠ b := by
    by_cases h : a = x
    · exact ⟨y, hy, h ▸ hxy⟩
    · exact ⟨x, hx, h⟩
  have hO := (Γ.isClosedDisc_closure_cell hc).isOArc_discBd
  obtain ⟨L₀, B, hL₀, -, hu, -⟩ := hO.lines (Γ.tilde_subset_discBd hc hac)
    (Γ.tilde_subset_discBd hc hb) hba
  have h1 := near_region hS hΓ.isOpen hr hc ha hL₀ (hu ▸ subset_union_left)
  obtain ⟨L', h2, h3, -⟩ := exists_side_near hS hΓ.isOpen (fun c hc => two_nodes hS hΓ hc) hr
    hL₀.left_mem h1
  exact ⟨L', h2, h3⟩

/-- A strip along a side of a region. -/
theorem side_strip' [CompactSpace S] [ConnectedSpace S] (hS : IsSurface S)
  (hΓ : Γ.Tame) {c L A r : Set S} {a b : S} (hr : r ∈ Γ.regions) (hL : Γ.IsSide c L a b)
    (hcl : L ⊆ closure r) (hA : IsClosed A) (hAL : A ∩ L ⊆ {a, b}) :
    ∃ St γ, IsClosedDisc St ∧ IsLineWithEnds γ a b ∧ discBd St = L ∪ γ ∧ L ∩ γ = {a, b}
      ∧ St ∩ closure c = L ∧ St ∩ A ⊆ {a, b} ∧ St ∩ Γ.U ⊆ L ∧ St \ L ⊆ r ∧
      ∀ x ∈ L, x ≠ a → x ≠ b → closure c ∪ St ∈ 𝓝 x := by
  obtain ⟨St, γ, r₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := side_strip hS hΓ.isOpen hL hA
    hAL
  obtain rfl : r = r₀ := SideOf.unique hS hΓ.isOpen hr h8 ⟨c, a, b, hL, hcl⟩ ⟨c, a, b, hL, h10⟩
  exact ⟨St, γ, h1, h2, h3, h4, h5, h6, h7, h9, h11⟩

omit [T2Space S] in
/-- A line that leaves a strip at its end leaves it through the far side. -/
theorem bridge_end {St L γ β : Set S} {x y : S} (hman : ∀ x : S, IsManifoldPoint x)
  (hSt : IsClosedDisc St) (hb : discBd St = L ∪ γ) (hβ : IsLineWithEnds β x y)
    (hi : β ∩ St = {x}) (hx : x ∉ L) : x ∈ γ := by
  have hxSt : x ∈ St := (hi.ge rfl : x ∈ β ∩ St).2
  have hxb : x ∈ discBd St := by
    by_contra hn
    have h1 : x ∈ closure (β \ {x, y}) := hβ.subset_closure_diff hβ.left_mem
    obtain ⟨z, hz, hz'⟩ := mem_closure_iff.mp h1 _ (hSt.isOpen_discInt hman) ⟨hxSt, hn⟩
    have h2 : z ∈ β ∩ St := ⟨hz'.1, hz.1⟩
    rw [hi] at h2
    exact hz'.2 (.inl h2)
  exact (hb ▸ hxb : x ∈ L ∪ γ).resolve_left hx

omit [T2Space S] in
theorem not_mem_closure_union {A B : Set S} {a : S} (h : a ∉ closure A)
  (h' : a ∉ closure B) : a ∉ closure (A ∪ B) := by
  rw [closure_union]
  rintro (h1 | h1)
  · exact h h1
  · exact h' h1

omit [T2Space S] in
/-- A curve through a node with the rest in a region bounds a disc that misses the rest of the
paint. -/
theorem curve_disc (hΓ : Γ.Tame) {r F : Set S} {a : S} (hr : r ∈ Γ.regions) (haN : a ∈ Γ.N)
  (hF : IsOArc F) (hFr : ∀ x ∈ F, x ≠ a → x ∈ r) :
    ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F ∧ ∀ x ∈ Γ.U, x ≠ a → x ∉ Δ := by
  have hU : ∀ {x}, x ∈ F → x ∈ Γ.U → x = a := fun {x} hx hxU => by
    by_contra hne
    exact region_subset hr (hFr x hx hne) hxU
  obtain ⟨Δ, hΔ, hb, hsub⟩ := hΓ.curve F hF (fun x hx => by
    rw [hU hx.1 hx.2]
    exact haN) (by
    have hsub : F ∩ Γ.N ⊆ {a} := fun _ hx => hU hx.1 (Γ.N_subset hx.2)
    exact (Set.ncard_le_ncard hsub (finite_singleton a)).trans (by simp))
  exact ⟨Δ, hΔ, hb, fun x hxU hne hxΔ => hne (hU (hsub ⟨hxΔ, hxU⟩) hxU)⟩

/-- Two lines at a node along the far sides of two strips, closed up inside the region. -/
theorem exists_loop {r St₁ St₂ L₁ L₂ γ₁ γ₂ : Set S} {a b₁ b₂ : S} (hS : IsSurface S) (_ : Γ.Tame)
    (hr : r ∈ Γ.regions) (haN : a ∈ Γ.N) (hb₁N : b₁ ∈ Γ.N) (hb₂N : b₂ ∈ Γ.N)
    (h₁ : IsClosedDisc St₁) (h₂ : IsClosedDisc St₂)
    (hγ₁ : IsLineWithEnds γ₁ a b₁) (hγ₂ : IsLineWithEnds γ₂ a b₂) (hb₁ : discBd St₁ = L₁ ∪ γ₁)
      (hb₂ : discBd St₂ = L₂ ∪ γ₂) (hr₁ : St₁ \ L₁ ⊆ r) (hr₂ : St₂ \ L₂ ⊆ r)
    (hd₁ : Disjoint L₁ r) (hd₂ : Disjoint L₂ r)
    (hi₁ : L₁ ∩ γ₁ = {a, b₁}) (hi₂ : L₂ ∩ γ₂ = {a, b₂}) (hin : St₂ ∩ St₁ ⊆ {a, b₂}) :
    ∃ A₁ A₂ x y β, IsLineWithEnds A₁ a x ∧ IsLineWithEnds A₂ a x ∧ A₁ ∩ A₂ = {a, x} ∧ x ∈ r
      ∧ A₁ ⊆ γ₁ ∧ IsLineWithEnds β y x ∧ β ⊆ r ∧ β ⊆ A₂ ∧ y ∈ γ₂ ∧
      β ∩ St₂ = {y} ∧ β ∩ St₁ = {x} ∧
      (∃ A' R₁ R₂, IsLineWithEnds A' a y ∧ A' ⊆ γ₂ ∧
        A₂ = A' ∪ β ∧ IsLineWithEnds R₁ x b₁ ∧ IsLineWithEnds R₂ y b₂ ∧
        A₁ ∪ R₁ = γ₁ ∧ A₁ ∩ R₁ = {x} ∧ A' ∪ R₂ = γ₂ ∧ A' ∩ R₂ = {y}) ∧
      (∀ z ∈ A₁, z ≠ a → z ∈ r) ∧ (∀ z ∈ A₂, z ≠ a → z ∈ r) := by
  have hman := hS.2.2
  have hNr : ∀ {z}, z ∈ Γ.N → z ∉ r := fun {z} hz h => region_subset hr h (Γ.N_subset hz)
  have hinner : ∀ {L γ St : Set S} {b : S}, discBd St = L ∪ γ → IsLineWithEnds γ a b → L ∩ γ
    = {a, b} → St \ L ⊆ r → ∃ e ∈ γ, e ∈ St ∧ e ∈ r := fun {L γ St b} hb hγ hi hsub => by
    obtain ⟨e, he, h1, h2, -⟩ := exists_inner hγ (finite_empty (α := S))
    have h3 : e ∉ L := fun h => by
      rcases (hi ▸ ⟨h, he⟩ : e ∈ ({a, b} : Set S)) with h4 | h4
      · exact h1 h4
      · exact h2 h4
    have h4 : e ∈ St := discBd_subset St (hb ▸ .inr he)
    exact ⟨e, he, h4, hsub ⟨h4, h3⟩⟩
  obtain ⟨e₁, -, he₁, he₁r⟩ := hinner hb₁ hγ₁ hi₁ hr₁
  obtain ⟨e₂, -, he₂, he₂r⟩ := hinner hb₂ hγ₂ hi₂ hr₂
  have hsep : ∀ z ∈ r, z ∈ St₁ → z ∉ St₂ := fun z hz h1 h2 => by
    rcases hin ⟨h2, h1⟩ with rfl | rfl
    · exact hNr haN hz
    · exact hNr hb₂N hz
  obtain ⟨β, x, y, hβ, hβr, hx, hy, hβ₁, hβ₂⟩ := exists_bridge (arcComponentsIn_isPathConnected hr)
    h₁.isClosed h₂.isClosed he₁ he₁r he₂ he₂r hsep
  have hxr : x ∈ r := hβr hβ.left_mem
  have hyr : y ∈ r := hβr hβ.right_mem
  have hxγ : x ∈ γ₁ := bridge_end hman h₁ hb₁ hβ hβ₁ (fun h => disjoint_left.mp hd₁ h hxr)
  have hyγ : y ∈ γ₂ := bridge_end hman h₂ hb₂ hβ.symm hβ₂ (fun h => disjoint_left.mp hd₂ h hyr)
  have hxa : x ≠ a := fun e => hNr haN (e ▸ hxr)
  have hya : y ≠ a := fun e => hNr haN (e ▸ hyr)
  have hxb : x ≠ b₁ := fun e => hNr hb₁N (e ▸ hxr)
  have hyb : y ≠ b₂ := fun e => hNr hb₂N (e ▸ hyr)
  obtain ⟨A₁, R₁, hA₁, hR₁, hu₁, hi'₁⟩ := hγ₁.split hxγ hxa hxb
  obtain ⟨A', R₂, hA', hR₂, hu₂, hi'₂⟩ := hγ₂.split hyγ hya hyb
  have hA₁s : A₁ ⊆ γ₁ := hu₁ ▸ subset_union_left
  have hA's : A' ⊆ γ₂ := hu₂ ▸ subset_union_left
  have hA₁b : x ≠ b₁ → b₁ ∉ A₁ := fun h h' => h (hi'₁.le ⟨h', hR₁.right_mem⟩).symm
  have hA'b : y ≠ b₂ → b₂ ∉ A' := fun h h' => h (hi'₂.le ⟨h', hR₂.right_mem⟩).symm
  have hγ₁St : γ₁ ⊆ St₁ := (hb₁ ▸ subset_union_right).trans (discBd_subset St₁)
  have hγ₂St : γ₂ ⊆ St₂ := (hb₂ ▸ subset_union_right).trans (discBd_subset St₂)
  have hA'β : A' ∩ β = {y} := by
    apply subset_antisymm
    · rintro z ⟨h1, h2⟩
      rw [← hβ₂]
      exact ⟨h2, hγ₂St (hA's h1)⟩
    · rintro _ rfl
      exact ⟨hA'.right_mem, hβ.right_mem⟩
  have hA₂ := hA'.union hβ.symm hA'β
  have hA₁r : ∀ z ∈ A₁, z ≠ a → z ∈ r := fun z hz hne => by
    refine hr₁ ⟨hγ₁St (hA₁s hz), fun hL => ?_⟩
    rcases (hi₁ ▸ ⟨hL, hA₁s hz⟩ : z ∈ ({a, b₁} : Set S)) with h | h
    · exact hne h
    · exact hA₁b hxb (h ▸ hz)
  have hA'r : ∀ z ∈ A', z ≠ a → z ∈ r := fun z hz hne => by
    refine hr₂ ⟨hγ₂St (hA's hz), fun hL => ?_⟩
    rcases (hi₂ ▸ ⟨hL, hA's hz⟩ : z ∈ ({a, b₂} : Set S)) with h | h
    · exact hne h
    · exact hA'b hyb (h ▸ hz)
  refine ⟨A₁, A' ∪ β, x, y, β, hA₁, hA₂, ?_, hxr, hA₁s, hβ.symm, hβr, subset_union_right, hyγ,
    hβ₂, hβ₁, ⟨A', R₁, R₂, hA', hA's, rfl, hR₁, hR₂, hu₁, hi'₁, hu₂, hi'₂⟩, hA₁r, ?_⟩
  · apply subset_antisymm
    · rintro z ⟨h1, h2 | h2⟩
      · by_cases hza : z = a
        · exact .inl hza
        · exact absurd (hsep z (hA₁r z h1 hza) (hγ₁St (hA₁s h1))) (not_not.mpr (hγ₂St (hA's h2)))
      · have h3 : z ∈ β ∩ St₁ := ⟨h2, hγ₁St (hA₁s h1)⟩
        rw [hβ₁] at h3
        exact .inr h3
    · rintro z (rfl | rfl)
      · exact ⟨hA₁.left_mem, .inl hA'.left_mem⟩
      · exact ⟨hA₁.right_mem, .inr hβ.left_mem⟩
  · rintro z (h | h) hne
    · exact hA'r z h hne
    · exact hβr h

/-- Two different sides of a region meet at most in nodes. -/
theorem sides_inter {r L L' : Set S} (h : Γ.SideOf r L) (h' : Γ.SideOf r L') (hne : L ≠ L') {z : S}
  (hz : z ∈ L) (hz' : z ∈ L') : z ∈ Γ.N := by
  obtain ⟨c, u, v, hs, -⟩ := h
  obtain ⟨c', u', v', hs', -⟩ := h'
  by_contra hn
  exact hne (hs.1.unique hs'.1 hz hz' hn).2

/-- A region has at most two sides at a node. -/
theorem three_sides [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {r L₁ L₂ L₃ : Set S} {a :
  S} (hr : r ∈ Γ.regions) (h₁ : Γ.SideOf r L₁) (h₂ : Γ.SideOf r L₂) (h₃ : Γ.SideOf r L₃)
    (ha₁ : a ∈ L₁) (ha₂ : a ∈ L₂) (ha₃ : a ∈ L₃) (haN : a ∈ Γ.N) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃)
      (h23 : L₂ ≠ L₃) : False := by
  classical
  have hcS : CompactSpace S := hS.1
  have hman := hS.2.2
  have hNr : ∀ {z}, z ∈ Γ.N → z ∉ r := fun {z} hz h => region_subset hr h (Γ.N_subset hz)
  obtain ⟨c₁, u₁, v₁, hs₁', hcl₁⟩ := id h₁
  obtain ⟨c₂, u₂, v₂, hs₂', hcl₂⟩ := id h₂
  obtain ⟨c₃, u₃, v₃, hs₃', hcl₃⟩ := id h₃
  obtain ⟨b₁, hs₁⟩ := hs₁'.exists_end ha₁ haN
  obtain ⟨b₂, hs₂⟩ := hs₂'.exists_end ha₂ haN
  obtain ⟨b₃, hs₃⟩ := hs₃'.exists_end ha₃ haN
  have hU₁ := hs₁.1.subset_U
  have hU₂ := hs₂.1.subset_U
  have hU₃ := hs₃.1.subset_U
  have hdr : ∀ {L : Set S}, L ⊆ Γ.U → Disjoint L r := fun {L} hL => disjoint_left.mpr fun x hx hx'
    => region_subset hr hx' (hL hx)
  obtain ⟨St₁, γ₁, hSt₁, hγ₁, hb₁, hi₁, -, -, hU'₁, hr₁, -⟩ := side_strip' hS hΓ hr hs₁ hcl₁
    (isClosed_empty (X := S)) (by simp)
  have hAL₂ : St₁ ∩ L₂ ⊆ {a, b₂} := fun z hz => by
    have h1 := hU'₁ ⟨hz.1, hU₂ hz.2⟩
    exact hs₂.1.2.2.2.le ⟨hz.2, sides_inter h₁ h₂ h12 h1 hz.2⟩
  obtain ⟨St₂, γ₂, hSt₂, hγ₂, hb₂, hi₂, -, hA₂', hU'₂, hr₂, -⟩ := side_strip' hS hΓ hr hs₂ hcl₂
    hSt₁.isClosed hAL₂
  obtain ⟨A₁, A₂, x, y, β, hA₁, hA₂, hi, hxr, hA₁s, hβ, hβr, hβA, hyγ, hβ₂, hβ₁, ⟨A', -, -, hA',
    hA's, rfl, -⟩, hA₁r, hA₂r⟩ :=
    exists_loop hS hΓ hr haN hs₁.1.right_mem_N hs₂.1.right_mem_N hSt₁ hSt₂ hγ₁ hγ₂ hb₁ hb₂
      hr₁ hr₂ (hdr hU₁) (hdr hU₂) hi₁ hi₂ hA₂'
  set A₂ := A' ∪ β with hA₂def
  let F := A₁ ∪ A₂
  have hFO : IsOArc F := oArc_of_lines hA₁ hA₂ hi
  have hFr : ∀ z ∈ F, z ≠ a → z ∈ r := fun z hz hne => hz.elim (fun h => hA₁r z h hne) (fun h
    => hA₂r z h hne)
  have hFc : IsClosed F := hA₁.isCompact.isClosed.union hA₂.isCompact.isClosed
  have hAL₃ : (F ∪ St₁ ∪ St₂) ∩ L₃ ⊆ {a, b₃} := by
    rintro z ⟨h, hz⟩
    refine hs₃.1.2.2.2.le ⟨hz, ?_⟩
    rcases h with (h | h) | h
    · by_cases hza : z = a
      · exact hza ▸ haN
      · exact absurd (hU₃ hz) (region_subset hr (hFr z h hza))
    · exact sides_inter h₁ h₃ h13 (hU'₁ ⟨h, hU₃ hz⟩) hz
    · exact sides_inter h₂ h₃ h23 (hU'₂ ⟨h, hU₃ hz⟩) hz
  obtain ⟨St₃, γ₃, hSt₃, hγ₃, hb₃, hi₃, -, hA₃', hU'₃, hr₃, -⟩ := side_strip' hS hΓ hr hs₃ hcl₃
    ((hFc.union hSt₁.isClosed).union hSt₂.isClosed) hAL₃
  have hb₃N := hs₃.1.right_mem_N
  obtain ⟨e₃, he₃, he₃a, he₃b, -⟩ := exists_inner hγ₃ (finite_empty (α := S))
  have hγ₃St : γ₃ ⊆ St₃ := (hb₃ ▸ subset_union_right).trans (discBd_subset St₃)
  have he₃r : e₃ ∈ r := hr₃ ⟨hγ₃St he₃, fun h => by
    rcases (hi₃ ▸ ⟨h, he₃⟩ : e₃ ∈ ({a, b₃} : Set S)) with h1 | h1
    · exact he₃a h1
    · exact he₃b h1⟩
  have hF3 : ∀ z, z ∈ F → z ∈ St₃ → z = a ∨ z = b₃ := fun z h h' => hA₃' ⟨h', .inl (.inl h)⟩
  obtain ⟨β₃, q, q₃, hβ₃, hβ₃r, hqF, hq₃, hβF, hβ₃St⟩ := exists_bridge
    (arcComponentsIn_isPathConnected hr) hFc hSt₃.isClosed (Or.inl hA₁.right_mem) hxr
      (hγ₃St he₃) he₃r
    (fun z hz h1 h2 => by
      rcases hF3 z h1 h2 with rfl | rfl
      · exact hNr haN hz
      · exact hNr hb₃N hz)
  have hqr : q ∈ r := hβ₃r hβ₃.left_mem
  have hq₃r : q₃ ∈ r := hβ₃r hβ₃.right_mem
  have hq₃γ : q₃ ∈ γ₃ := bridge_end hman hSt₃ hb₃ hβ₃.symm hβ₃St (fun h => disjoint_left.mp
    (hdr hU₃) h hq₃r)
  have hqa : q ≠ a := fun e => hNr haN (e ▸ hqr)
  have hq₃a : q₃ ≠ a := fun e => hNr haN (e ▸ hq₃r)
  have hq₃b : q₃ ≠ b₃ := fun e => hNr hb₃N (e ▸ hq₃r)
  obtain ⟨A₃, hA₃, hA₃s, hA₃b⟩ := sub_line hγ₃ hq₃γ hq₃a
  have hA₃β : A₃ ∩ β₃ = {q₃} := by
    apply subset_antisymm
    · rintro z ⟨h1, h2⟩
      rw [← hβ₃St]
      exact ⟨h2, hγ₃St (hA₃s h1)⟩
    · rintro _ rfl
      exact ⟨hA₃.right_mem, hβ₃.right_mem⟩
  have hP₃ : IsLineWithEnds (A₃ ∪ β₃) a q := hA₃.union hβ₃.symm hA₃β
  obtain ⟨P₁, P₂, hP₁, hP₂, hun, hin, hg₁, hg₂⟩ := split_oarc hA₁ hA₂ hi hqF hqa
  set P₃ := A₃ ∪ β₃ with hP₃def
  have hP₃F : P₃ ∩ F = {a, q} := by
    apply subset_antisymm
    · rintro z ⟨h1 | h1, h2⟩
      · rcases hF3 z h2 (hγ₃St (hA₃s h1)) with h | h
        · exact .inl h
        · exact absurd (h ▸ h1) (hA₃b hq₃b)
      · have h3 : z ∈ β₃ ∩ F := ⟨h1, h2⟩
        rw [hβF] at h3
        exact .inr h3
    · rintro z (rfl | rfl)
      · exact ⟨hP₃.left_mem, .inl hA₁.left_mem⟩
      · exact ⟨hP₃.right_mem, hqF⟩
  have hP₁F : P₁ ⊆ F := subset_union_left.trans hun.subset
  have hP₂F : P₂ ⊆ F := subset_union_right.trans hun.subset
  have hP₁₃ : P₁ ∩ P₃ = {a, q} := by
    apply subset_antisymm
    · exact fun z hz => by rw [← hP₃F]; exact ⟨hz.2, hP₁F hz.1⟩
    · rintro z (rfl | rfl)
      · exact ⟨hP₁.left_mem, hP₃.left_mem⟩
      · exact ⟨hP₁.right_mem, hP₃.right_mem⟩
  have hP₂₃ : P₂ ∩ P₃ = {a, q} := by
    apply subset_antisymm
    · exact fun z hz => by rw [← hP₃F]; exact ⟨hz.2, hP₂F hz.1⟩
    · rintro z (rfl | rfl)
      · exact ⟨hP₂.left_mem, hP₃.left_mem⟩
      · exact ⟨hP₂.right_mem, hP₃.right_mem⟩
  have hP₃r : ∀ z ∈ P₃, z ≠ a → z ∈ r := fun z hz hne => by
    rcases hz with h | h
    · refine hr₃ ⟨hγ₃St (hA₃s h), fun hL => ?_⟩
      rcases (hi₃ ▸ ⟨hL, hA₃s h⟩ : z ∈ ({a, b₃} : Set S)) with h1 | h1
      · exact hne h1
      · exact hA₃b hq₃b (h1 ▸ h)
    · exact hβ₃r h
  obtain ⟨Δ₃, hΔ₃, hbd₃, hU₃'⟩ := curve_disc hΓ hr haN hFO hFr
  obtain ⟨Δ₁, hΔ₁, hbd₁, hU₁'⟩ := curve_disc hΓ hr haN (oArc_of_lines hP₂ hP₃ hP₂₃) (F := P₂ ∪ P₃)
    (fun z hz hne => Or.elim hz (fun h => hFr z (hP₂F h) hne) (fun h => hP₃r z h hne))
  obtain ⟨Δ₂, hΔ₂, hbd₂, hU₂'⟩ := curve_disc hΓ hr haN (oArc_of_lines hP₁ hP₃ hP₁₃) (F := P₁ ∪ P₃)
    (fun z hz hne => Or.elim hz (fun h => hFr z (hP₁F h) hne) (fun h => hP₃r z h hne))
  let B : Set S := {b₁, b₂, b₃} \ {a}
  have hBf : B.Finite := (toFinite _).subset sdiff_subset
  have haB : a ∉ closure B := by
    rw [hBf.isClosed.closure_eq]
    exact fun h => h.2 rfl
  have hgen : ∀ {P Q Sp Sq Sk : Set S}, a ∉ closure (P \ Sp) → a ∉ closure (Q \ Sq) →
    (∀ z ∈ Sp, z ∈ Sk → z = a ∨ z ∈ B) → (∀ z ∈ Sq, z ∈ Sk → z = a ∨ z ∈ B) →
      a ∉ closure (((P ∪ Q) ∩ Sk) \ {a}) := fun {P Q Sp Sq Sk} gP gQ hp hq h => by
    refine not_mem_closure_union (not_mem_closure_union gP gQ) haB (closure_mono ?_ h)
    rintro z ⟨⟨h1 | h1, h2⟩, h3⟩
    · by_cases h4 : z ∈ Sp
      · exact .inr ((hp z h4 h2).resolve_left h3)
      · exact .inl (.inl ⟨h1, h4⟩)
    · by_cases h4 : z ∈ Sq
      · exact .inr ((hq z h4 h2).resolve_left h3)
      · exact .inl (.inr ⟨h1, h4⟩)
  have hb₂B : ∀ z, z = a ∨ z = b₂ → z = a ∨ z ∈ B := by
    rintro z (h | rfl)
    · exact .inl h
    · by_cases h : z = a
      · exact .inl h
      · exact .inr ⟨.inr (.inl rfl), h⟩
  have hb₃B : ∀ z, z = a ∨ z = b₃ → z = a ∨ z ∈ B := by
    rintro z (h | rfl)
    · exact .inl h
    · by_cases h : z = a
      · exact .inl h
      · exact .inr ⟨.inr (.inr rfl), h⟩
  have h31 : ∀ z ∈ St₁, z ∈ St₃ → z = a ∨ z ∈ B := fun z h h' => hb₃B z (hA₃' ⟨h', .inl (.inr h)⟩)
  have h32 : ∀ z ∈ St₂, z ∈ St₃ → z = a ∨ z ∈ B := fun z h h' => hb₃B z (hA₃' ⟨h', .inr h⟩)
  have h21 : ∀ z ∈ St₁, z ∈ St₂ → z = a ∨ z ∈ B := fun z h h' => hb₂B z (hA₂' ⟨h', h⟩)
  have h12' : ∀ z ∈ St₂, z ∈ St₁ → z = a ∨ z ∈ B := fun z h h' => h21 z h' h
  have h13' : ∀ z ∈ St₃, z ∈ St₁ → z = a ∨ z ∈ B := fun z h h' => h31 z h' h
  have h23' : ∀ z ∈ St₃, z ∈ St₂ → z = a ∨ z ∈ B := fun z h h' => h32 z h' h
  have hA₁St : A₁ ⊆ St₁ := hA₁s.trans ((hb₁ ▸ subset_union_right).trans (discBd_subset St₁))
  have hA'St : A' ⊆ St₂ := hA's.trans ((hb₂ ▸ subset_union_right).trans (discBd_subset St₂))
  have g₁ : a ∉ closure (P₁ \ St₁) := fun h => by
    have h5 : P₁ \ St₁ ⊆ P₁ \ A₁ := fun z hz => ⟨hz.1, fun h' => hz.2 (hA₁St h')⟩
    exact hg₁ (closure_mono h5 h)
  have hβa : a ∉ closure β := by
    rw [hβ.isCompact.isClosed.closure_eq]
    exact fun h => hNr haN (hβr h)
  have g₂ : a ∉ closure (P₂ \ St₂) := fun h => by
    refine not_mem_closure_union hg₂ hβa (closure_mono ?_ h)
    rintro z ⟨h1, h2⟩
    by_cases h3 : z ∈ β
    · exact .inr h3
    · exact .inl ⟨h1, fun h4 => h4.elim (fun h5 => h2 (hA'St h5)) h3⟩
  have g₃ : a ∉ closure (P₃ \ St₃) := fun h => by
    have hβ₃a : a ∉ closure β₃ := by
      rw [hβ₃.isCompact.isClosed.closure_eq]
      exact fun h => hNr haN (hβ₃r h)
    refine hβ₃a (closure_mono ?_ h)
    rintro z ⟨h1 | h1, h2⟩
    · exact absurd (hγ₃St (hA₃s h1)) h2
    · exact h1
  have hLb₁ : L₁ ⊆ discBd St₁ := hb₁ ▸ subset_union_left
  have hLb₂ : L₂ ⊆ discBd St₂ := hb₂ ▸ subset_union_left
  have hLb₃ : L₃ ⊆ discBd St₃ := hb₃ ▸ subset_union_left
  have hb12 : discBd Δ₃ = P₁ ∪ P₂ := by rw [hbd₃, hun]
  have hinner : ∀ {P Q : Set S}, P ∩ Q = {a, q} → Disjoint (P \ {a, q}) Q := fun he =>
    disjoint_left.mpr fun _ hz hz' => hz.2 (he ▸ ⟨hz.1, hz'⟩)
  have hinner' : ∀ {P Q : Set S}, P ∩ Q = {a, q} → Disjoint (Q \ {a, q}) P := fun he =>
    disjoint_left.mpr fun _ hz hz' => hz.2 (he ▸ ⟨hz', hz.1⟩)
  have hd₃ : Disjoint (P₃ \ {a, q}) Δ₃ := third_off hman hSt₃ hs₃.1.2.1 hLb₃ hΔ₃ hb12 (fun z hz hne
    => hU₃' z (hU₃ hz) hne) hP₃
    (by
      refine disjoint_union_right.mpr ⟨hinner' hP₁₃, hinner' hP₂₃⟩) g₃ (hgen g₁ g₂ h31 h32)
  have hd₁ : Disjoint (P₁ \ {a, q}) Δ₁ := third_off hman hSt₁ hs₁.1.2.1 hLb₁ hΔ₁ hbd₁ (fun z hz hne
    => hU₁' z (hU₁ hz) hne) hP₁
    (by
      refine disjoint_union_right.mpr ⟨hinner hin, hinner hP₁₃⟩) g₁ (hgen g₂ g₃ h12' h13')
  have hd₂ : Disjoint (P₂ \ {a, q}) Δ₂ := third_off hman hSt₂ hs₂.1.2.1 hLb₂ hΔ₂ hbd₂ (fun z hz hne
    => hU₂' z (hU₂ hz) hne) hP₂
    (by
      exact disjoint_union_right.mpr ⟨hinner' hin, hinner hP₂₃⟩) g₂ (hgen g₁ g₃ h21 h23')
  have hcov := theta_cover hS hP₁ hP₂ hP₃ hin hP₂₃ hΔ₃ hΔ₁ hΔ₂ hb12 hbd₁ hbd₂ hd₃ hd₁ hd₂
  obtain ⟨z, hz, hza, -, -⟩ := exists_inner hs₁.1.2.1 (finite_empty (α := S))
  rcases (hcov ▸ mem_univ z : z ∈ Δ₃ ∪ Δ₁ ∪ Δ₂) with (h | h) | h
  · exact hU₃' z (hU₁ hz) hza h
  · exact hU₁' z (hU₁ hz) hza h
  · exact hU₂' z (hU₁ hz) hza h

end Painting

end GraphMinor.GM17
