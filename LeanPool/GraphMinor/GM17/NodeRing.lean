/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Sector

/-!
# Curves around an internal node with few cells

Here we prove the part of `RegionBoundaryOArcCriterionStatement` on internal nodes that lie on at
most one cell, or on two cells one of which has only two nodes, which is used in (8.7)
of Graph Minors XVII (page 183). We find a closed disc that holds these cells, has the node inside
or on its boundary and has its other nodes on its boundary, and take a ring around it
that is pinned at the other nodes (`ring_node`). If there are two cells, the disc is made of the two
cells and a sector of a region between them (`two_cell_disc`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

namespace Painting

variable {Γ : Painting S} [T2Space S]

/-- A ring around a disc that holds the cells at a node gives the curve of (8.7). -/
theorem ring_node [ConnectedSpace S] (hS : IsSurface S) {E c₀ c₁ : Set S} {n : S}
  (hE : IsClosedDisc E) (h₀ : c₀ ∈ Γ.C) (h₁ : c₁ ∈ Γ.C) (h₀E : closure c₀ ⊆ E)
    (h₁E : closure c₁ ⊆ E) (hEU : E ∩ Γ.U ⊆ closure c₀ ∪ closure c₁)
    (hnE : n ∈ E) (hn : n ∈ Γ.N) (hcells : ∀ d ∈ Γ.C, n ∈ tilde d → d = c₀ ∨ d = c₁)
      (hP : ∀ z ∈ E, z ∈ Γ.N → z ≠ n → z ∈ discBd E) (hEb : E ∩ bd S ⊆ Γ.N) (hnb : n ∉ bd S)
    (hcard : ((E ∩ Γ.N) \ {n}).ncard ≤ 3) (hthree : ((E ∩ Γ.N) \ {n}).ncard = 3 →
      (tilde c₁).ncard ≠ 2) :
    ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧ (F ∩ Γ.N).ncard ≤ 3 ∧
      ∀ Δ : Set S, IsClosedDisc Δ → discBd Δ = F →
        ((Δ ∩ Γ.N ⊆ F ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard ≤ 1) ∨ ((F ∩ Γ.N).ncard = 3 ∧ ∀ c ∈ Γ.C, c ⊆ Δ →
          (tilde c).ncard = 2)) →
        ∃ d₁ ∈ Γ.C, ∃ d₂ ∈ Γ.C, Γ.C ⊆ {d₁, d₂} ∪ {c ∈ Γ.C | c ⊆ Δ} := by
  classical
  let Z : Set S := (Γ.N \ {n}) ∪ ⋃ d ∈ Γ.C \ {c₀, c₁}, closure d
  have hZ : IsClosed Z := (Γ.finite_N.subset sdiff_subset).isClosed.union
    (Γ.finite_cells.subset sdiff_subset |>.isClosed_biUnion fun _ _ => isClosed_closure)
  have hUcell : ∀ {z}, z ∈ Γ.U → z ∉ Γ.N → ∃ d ∈ Γ.C, z ∈ d := fun {z} h h' => by
    obtain ⟨d, hd, hz⟩ := exists_mem_arcComponentsIn (F := Γ.U \ Γ.N) (x := z) ⟨h, h'⟩
    exact ⟨d, hd, hz⟩
  have hnZ : n ∉ Z := by
    rintro (h | h)
    · exact h.2 rfl
    · obtain ⟨d, hd, hnd⟩ := mem_iUnion₂.mp h
      have h3 : n ∈ tilde d := by
        rw [← Γ.closure_cell_inter_N hd.1]
        exact ⟨hnd, hn⟩
      rcases hcells d hd.1 h3 with e | e
      · exact hd.2 (.inl e)
      · exact hd.2 (.inr e)
  have hZE : ∀ z ∈ Z, z ∈ E → z ∈ Γ.N := by
    rintro z (h | h) hzE
    · exact h.1
    · obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp h
      rcases hEU ⟨hzE, Γ.closure_cell_subset_U hd.1 hzd⟩ with h' | h'
      · exact closure_inter_closure hd.1 h₀ (fun e => hd.2 (.inl e)) ⟨hzd, h'⟩
      · exact closure_inter_closure hd.1 h₁ (fun e => hd.2 (.inr e)) ⟨hzd, h'⟩
  have hZb : Z ∩ E ⊆ discBd E := fun z hz => hP z hz.2 (hZE z hz.1 hz.2) (fun e => hnZ (e ▸ hz.1))
  have hEb' : E ∩ bd S ⊆ Z := fun z hz => .inl ⟨hEb hz, fun e => hnb ((mem_singleton_iff.mp e) ▸
    hz.2)⟩
  obtain ⟨Δ, hΔ, hEΔ, hΔZ, hbE, -⟩ := exists_ring_sub hS hE hZ hZb hEb'
  have hnF : n ∉ discBd Δ := fun h => by
    have h3 : n ∈ E ∩ Z := hbE ▸ ⟨h, hnE⟩
    exact hnZ h3.2
  have hN' : ∀ z ∈ Γ.N, z ≠ n → z ∈ Z := fun z hz hne => .inl ⟨hz, hne⟩
  have hFN : discBd Δ ∩ Γ.N = (E ∩ Γ.N) \ {n} := by
    apply subset_antisymm
    · rintro z ⟨hz, hzN⟩
      have hne : z ≠ n := fun e => hnF (e ▸ hz)
      have h3 : z ∈ E ∩ Z := hΔZ ▸ ⟨discBd_subset Δ hz, hN' z hzN hne⟩
      exact ⟨⟨h3.1, hzN⟩, hne⟩
    · rintro z ⟨⟨hz, hzN⟩, hne⟩
      have h3 : z ∈ discBd Δ ∩ E := hbE.symm ▸ ⟨hz, hN' z hzN hne⟩
      exact ⟨h3.1, hzN⟩
  have hnorm : Γ.IsNormal (discBd Δ) := by
    rintro z ⟨hz, hzU⟩
    by_contra hzN
    obtain ⟨d, hd, hzd⟩ := hUcell hzU hzN
    by_cases hdc : d = c₀ ∨ d = c₁
    · have hzE : z ∈ E := hdc.elim (fun e => h₀E (e ▸ subset_closure hzd)) (fun e => h₁E
      (e ▸ subset_closure hzd))
      have h3 : z ∈ E ∩ Z := hbE ▸ ⟨hz, hzE⟩
      exact hzN (hZE z h3.2 hzE)
    · have hzZ : z ∈ Z := .inr (mem_iUnion₂.mpr ⟨d, ⟨hd, hdc⟩, subset_closure hzd⟩)
      have h3 : z ∈ E ∩ Z := hΔZ ▸ ⟨discBd_subset Δ hz, hzZ⟩
      exact hzN (hZE z hzZ h3.1)
  refine ⟨discBd Δ, hΔ.isOArc_discBd, hnorm, hFN ▸ hcard, fun Δ' hΔ' hb halt => ?_⟩
  rcases two_discs hS hΔ hΔ' hb.symm with rfl | ⟨hcov, -⟩
  · exfalso
    rcases halt with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact hnF (h1 ⟨hEΔ hnE, hn⟩)
    · rw [hFN] at h1
      exact hthree h1 (h2 c₁ h₁ (subset_closure.trans (h₁E.trans hEΔ)))
  · refine ⟨c₀, h₀, c₁, h₁, fun d hd => ?_⟩
    by_cases hdc : d ∈ ({c₀, c₁} : Set (Set S))
    · exact .inl hdc
    · refine .inr ⟨hd, fun z hz => ?_⟩
      rcases (hcov.ge (mem_univ z) : z ∈ Δ ∪ Δ') with h | h
      · exfalso
        have hzZ : z ∈ Z := .inr (mem_iUnion₂.mpr ⟨d, ⟨hd, hdc⟩, subset_closure hz⟩)
        have h3 : z ∈ E ∩ Z := hΔZ ▸ ⟨h, hzZ⟩
        exact disjoint_left.mp (Γ.cell_disjoint_N hd) hz (hZE z hzZ h3.1)
      · exact h

/-- The curve for a node on only one cell. -/
theorem node_one [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {n : S} (hn : n ∈ Γ.N)
  (hnb : n ∉ bd S) (h : {c ∈ Γ.C | n ∈ tilde c}.ncard ≤ 1) :
    ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧ (F ∩ Γ.N).ncard ≤ 3 ∧
      ∀ Δ : Set S, IsClosedDisc Δ → discBd Δ = F →
        ((Δ ∩ Γ.N ⊆ F ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard ≤ 1) ∨ ((F ∩ Γ.N).ncard = 3 ∧ ∀ c ∈ Γ.C, c ⊆ Δ →
          (tilde c).ncard = 2)) →
        ∃ d₁ ∈ Γ.C, ∃ d₂ ∈ Γ.C, Γ.C ⊆ {d₁, d₂} ∪ {c ∈ Γ.C | c ⊆ Δ} := by
  obtain ⟨c, hc, hnc⟩ := node_on_cell hS hΓ hn
  have hfin : {c ∈ Γ.C | n ∈ tilde c}.Finite := Γ.finite_cells.subset fun _ h => h.1
  have hcells : ∀ d ∈ Γ.C, n ∈ tilde d → d = c ∨ d = c := fun d hd hnd =>
    .inl ((Set.ncard_le_one_iff hfin).mp h ⟨hd, hnd⟩ ⟨hc, hnc⟩)
  have hint : ¬ (c ∩ bd S).Nonempty := fun hb => by
    obtain ⟨u, v, -, ht, -, -, hu, hv⟩ := Γ.border_cell_exists_ends hc hb
    rcases (ht ▸ hnc : n ∈ ({u, v} : Set S)) with rfl | rfl
    · exact hnb hu.2
    · exact hnb hv.2
  have hdisc := Γ.isClosedDisc_closure_cell hc
  have htN : closure c ∩ Γ.N = tilde c := Γ.closure_cell_inter_N hc
  have hle : ((closure c ∩ Γ.N) \ {n}).ncard ≤ 2 := by
    rw [htN, Set.ncard_sdiff_singleton_of_mem hnc]
    have := Γ.ncard_tilde_cell_le hc
    omega
  refine ring_node hS hdisc hc hc subset_rfl subset_rfl (fun z hz => .inl hz.1) hnc.1 hn hcells
    (fun z hz hzN _ => ?_) (fun z hz => ?_) hnb (by omega) (by omega)
  · refine Γ.tilde_subset_discBd hc ?_
    rw [← htN]
    exact ⟨hz, hzN⟩
  · have h3 : z ∈ tilde c := ⟨hz.1, fun h' => hint ⟨z, h', hz.2⟩⟩
    exact Γ.tilde_subset_N hc h3

/-- A closed disc made of two cells at a node and a sector of a region between them. -/
theorem two_cell_disc [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {c₀ c₁ t₀ t₁ r : Set S}
  {n m e : S} (hr : r ∈ Γ.regions) (hs₀ : Γ.IsSide c₀ t₀ n m) (hs₁ : Γ.IsSide c₁ t₁ n e)
    (hne : c₀ ≠ c₁)
    (hcl₀ : t₀ ⊆ closure r) (hcl₁ : t₁ ⊆ closure r) (ht₀ : tilde c₀ = {n, m})
      (hinter : tilde c₀ ∩ tilde c₁ ⊆ {n, e}) :
    ∃ E, IsClosedDisc E ∧ closure c₀ ⊆ E ∧ closure c₁ ⊆ E ∧ E ∩ Γ.U ⊆ closure c₀ ∪ closure c₁ ∧
      (∀ z ∈ E, z ∈ Γ.N → z ≠ n → z ∈ discBd E) ∧
      ∀ z, z ∈ discBd (closure c₀) ∪ discBd (closure c₁) → z ∉ t₀ \ {n, m} → z ∉ t₁ \ {n, e}
        → z ∈ discBd E := by
  have h₀ := hs₀.1.1
  have h₁ := hs₁.1.1
  have hmeet : ∀ {z}, z ∈ closure c₀ → z ∈ closure c₁ → (z = n ∨ z = e) ∧ (z = n ∨ z = m)
    := fun {z} h h' => by
    have hzN := closure_inter_closure h₀ h₁ hne ⟨h, h'⟩
    have h3 : z ∈ tilde c₀ := by
      rw [← Γ.closure_cell_inter_N h₀]
      exact ⟨h, hzN⟩
    have h4 : z ∈ tilde c₁ := by
      rw [← Γ.closure_cell_inter_N h₁]
      exact ⟨h', hzN⟩
    have h5 := hinter ⟨h3, h4⟩
    rw [ht₀] at h3
    exact ⟨h5, h3⟩
  have ht₀c := fun {z} (h : z ∈ t₀) => hs₀.1.subset_closure h
  have ht₁c := fun {z} (h : z ∈ t₁) => hs₁.1.subset_closure h
  have hnt₀ : n ∈ t₀ := hs₀.1.2.1.left_mem
  have hmt₀ : m ∈ t₀ := hs₀.1.2.1.right_mem
  have hnt₁ : n ∈ t₁ := hs₁.1.2.1.left_mem
  have het₁ : e ∈ t₁ := hs₁.1.2.1.right_mem
  obtain ⟨Y, hY, h₀Y, h₁Y, hYU⟩ := sector hS hΓ hr hs₀ hs₁ hcl₀ hcl₁ (fun z hz => (hmeet
    (ht₀c hz.1) (ht₁c hz.2)).1)
  have hsub : ∀ {z}, z ∈ closure c₀ → z ∈ closure c₁ → z ∈ t₀ ∧ z ∈ t₁ := fun {z} h h' => by
    obtain ⟨h3, h4⟩ := hmeet h h'
    refine ⟨h4.elim (fun e' => e' ▸ hnt₀) (fun e' => e' ▸ hmt₀), h3.elim (fun e' => e' ▸ hnt₁)
      (fun e' => e' ▸ het₁)⟩
  have hm₀ : closure c₀ ∩ Y = t₀ := by
    apply subset_antisymm
    · rintro z ⟨h, h'⟩
      rcases hYU ⟨h', Γ.closure_cell_subset_U h₀ h⟩ with h3 | h3
      · exact h3
      · exact (hsub h (ht₁c h3)).1
    · exact fun z hz => ⟨ht₀c hz, discBd_subset Y (h₀Y hz)⟩
  obtain ⟨hA, hbA⟩ := disc_union _ _ _ _ _ (Γ.isClosedDisc_closure_cell h₀) hY hs₀.1.2.1 hm₀
    hs₀.1.2.2.1 h₀Y
  have hm₁ : (closure c₀ ∪ Y) ∩ closure c₁ = t₁ := by
    apply subset_antisymm
    · rintro z ⟨h | h, h'⟩
      · exact (hsub h h').2
      · rcases hYU ⟨h, Γ.closure_cell_subset_U h₁ h'⟩ with h3 | h3
        · exact (hsub (ht₀c h3) h').2
        · exact h3
    · exact fun z hz => ⟨.inr (discBd_subset Y (h₁Y hz)), ht₁c hz⟩
  have ht₁A : t₁ ⊆ discBd (closure c₀ ∪ Y) := fun z hz => by
    rw [hbA]
    refine ⟨.inr (h₁Y hz), fun h => ?_⟩
    exact h.2 (hmeet (ht₀c h.1) (ht₁c hz)).2
  obtain ⟨hE, hbE⟩ := disc_union _ _ _ _ _ hA (Γ.isClosedDisc_closure_cell h₁) hs₁.1.2.1 hm₁ ht₁A
    hs₁.1.2.2.1
  refine ⟨_, hE, fun z h => .inl (.inl h), fun z h => .inr h, ?_, ?_, ?_⟩
  · rintro z ⟨(h | h) | h, hzU⟩
    · exact .inl h
    · exact (hYU ⟨h, hzU⟩).elim (fun h3 => .inl (ht₀c h3)) (fun h3 => .inr (ht₁c h3))
    · exact .inr h
  · intro z hz hzN hne'
    have hn₀ : z ∉ t₀ \ {n, m} := fun h => h.2 (hs₀.1.2.2.2.le ⟨h.1, hzN⟩)
    have hn₁ : z ∉ t₁ \ {n, e} := fun h => h.2 (hs₁.1.2.2.2.le ⟨h.1, hzN⟩)
    have hc₀ : z ∈ closure c₀ → z ∈ discBd (closure c₀) := fun h => Γ.tilde_subset_discBd h₀
      (Γ.closure_cell_inter_N h₀ ▸ ⟨h, hzN⟩)
    have hc₁ : z ∈ closure c₁ → z ∈ discBd (closure c₁) := fun h => Γ.tilde_subset_discBd h₁
      (Γ.closure_cell_inter_N h₁ ▸ ⟨h, hzN⟩)
    rw [hbE, hbA]
    refine ⟨?_, hn₁⟩
    rcases hz with (h | h) | h
    · exact .inl ⟨.inl (hc₀ h), hn₀⟩
    · rcases hYU ⟨h, Γ.N_subset hzN⟩ with h3 | h3
      · exact .inl ⟨.inl (hc₀ (ht₀c h3)), hn₀⟩
      · exact .inr (hc₁ (ht₁c h3))
    · exact .inr (hc₁ h)
  · intro z hz hn₀ hn₁
    rw [hbE, hbA]
    refine ⟨?_, hn₁⟩
    rcases hz with h | h
    · exact .inl ⟨.inl h, hn₀⟩
    · exact .inr h

/-- Two sides of a cell with the same two ends do not lie on one region, as this would leave only
these two nodes. -/
theorem no_wrap [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {c L L' r : Set S} {n m : S}
  (hr : r ∈ Γ.regions) (hL : Γ.IsSide c L n m) (hL' : Γ.IsSide c L' n m) (hne : L ≠ L')
    (hcl : L ⊆ closure r) (hcl' : L' ⊆ closure r) (ht : tilde c = {n, m}) : False := by
  have hcS : CompactSpace S := hS.1
  have hman := hS.2.2
  have hc := hL.1.1
  have hi : L ∩ L' = {n, m} := by
    apply subset_antisymm
    · rintro z ⟨h, h'⟩
      refine hL.1.2.2.2.le ⟨h, ?_⟩
      by_contra hn
      exact hne (hL.1.unique hL'.1 h h' hn).2
    · rintro z (rfl | rfl)
      · exact ⟨hL.1.2.1.left_mem, hL'.1.2.1.left_mem⟩
      · exact ⟨hL.1.2.1.right_mem, hL'.1.2.1.right_mem⟩
  have hO : IsOArc (L ∪ L') := oArc_of_lines hL.1.2.1 hL'.1.2.1 hi
  have hdisc := Γ.isClosedDisc_closure_cell hc
  obtain ⟨φ⟩ := id (frontier_isOArc hS hΓ hr)
  obtain ⟨ψ⟩ := id hdisc.isOArc_discBd
  have hU : L ∪ L' ⊆ Γ.U := union_subset hL.1.subset_U hL'.1.subset_U
  have hfr : L ∪ L' = closure r \ r := oarc_eq φ hO fun z hz => ⟨union_subset hcl hcl' hz, fun h
    => region_subset hr h (hU hz)⟩
  have hbc : L ∪ L' = discBd (closure c) := oarc_eq ψ hO (union_subset hL.1.2.2.1 hL'.1.2.2.1)
  obtain ⟨St, γ, -, -, -, -, -, -, -, hStr, hnb⟩ := side_strip' hS hΓ hr hL hcl (isClosed_empty (X
    := S)) (by simp)
  obtain ⟨St', γ', -, -, -, -, -, -, -, hStr', hnb'⟩ := side_strip' hS hΓ hr hL' hcl'
    (isClosed_empty (X := S)) (by simp)
  let W : Set S := closure r ∪ closure c
  have hStW : ∀ {St T : Set S}, T ⊆ closure r → St \ T ⊆ r → closure c ∪ St ⊆ W
    := fun {St T} h1 h2 z hz => by
    rcases hz with h | h
    · exact .inr h
    · by_cases hzT : z ∈ T
      · exact .inl (h1 hzT)
      · exact .inl (subset_closure (h2 ⟨h, hzT⟩))
  have hside : ∀ x ∈ L ∪ L', x ∉ ({n, m} : Set S) → W ∈ 𝓝 x := by
    rintro x (h | h) hx
    · exact Filter.mem_of_superset (hnb x h (fun e => hx (.inl e)) (fun e => hx (.inr e)))
        (hStW hcl hStr)
    · exact Filter.mem_of_superset (hnb' x h (fun e => hx (.inl e)) (fun e => hx (.inr e)))
        (hStW hcl' hStr')
  have hnbW : ∀ x ∈ W, x ∉ ({n, m} : Set S) → W ∈ 𝓝 x := by
    rintro x (h | h) hx
    · by_cases hxr : x ∈ r
      · exact Filter.mem_of_superset ((hΓ.isOpen r hr).mem_nhds hxr) (subset_closure.trans
        subset_union_left)
      · exact hside x (hfr ▸ ⟨h, hxr⟩) hx
    · by_cases hxb : x ∈ discBd (closure c)
      · exact hside x (hbc ▸ hxb) hx
      · exact Filter.mem_of_superset ((hdisc.isOpen_discInt hman).mem_nhds ⟨h,
          hxb⟩) fun y hy => .inr hy.1
  have hWc : IsClosed W := isClosed_closure.union isClosed_closure
  obtain ⟨z, hz⟩ := arcComponentsIn_nonempty hc
  have hzA : z ∉ ({n, m} : Set S) := fun h => disjoint_left.mp (Γ.cell_disjoint_N hc) hz (h.elim
    (fun e => e ▸ hL.1.left_mem_N) (fun e => e ▸ hL.1.right_mem_N))
  refine hΓ.not_covered (A := {n, m}) (toFinite _) ((Set.ncard_pair hL.1.2.1.ne').le.trans
    (by norm_num)) fun y hy => ?_
  by_contra hyA
  rcases cover_off hman hWc (toFinite _) ⟨z, .inr (subset_closure hz), hzA⟩ hnbW hyA with h | h
  · refine hyA ?_
    by_cases hyr : y ∈ r
    · exact absurd (Γ.N_subset hy) (region_subset hr hyr)
    · rcases (hfr ▸ (⟨h, hyr⟩ : y ∈ closure r \ r) : y ∈ L ∪ L') with h3 | h3
      · exact hL.1.2.2.2.le ⟨h3, hy⟩
      · exact hL'.1.2.2.2.le ⟨h3, hy⟩
  · exact hyA (ht ▸ Γ.closure_cell_inter_N hc ▸ ⟨h, hy⟩)

/-- The side next to a side of a two-node cell, around one of its nodes, is a side of another cell
at this node. -/
theorem partner [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {c₀ c₁ L : Set S} {n m : S}
  (hL : Γ.IsSide c₀ L n m) (ht : tilde c₀ = {n, m}) (hn : n ∈ Γ.N) (hcells : ∀ d ∈ Γ.C, n ∈ tilde d
    → d = c₀ ∨ d = c₁) :
    ∃ r L₁ e, r ∈ Γ.regions ∧ L ⊆ closure r ∧ Γ.SideOf r L ∧ Γ.SideOf r L₁ ∧ L₁ ≠ L
      ∧ L₁ ⊆ closure r ∧ Γ.IsSide c₁ L₁ n e := by
  have hcS : CompactSpace S := hS.1
  obtain ⟨St, γ, r, -, -, -, -, -, -, -, hr, -, hcl, -⟩ := side_strip hS hΓ.isOpen hL
    (isClosed_empty (X := S)) (by simp)
  have hso : Γ.SideOf r L := ⟨c₀, n, m, hL, hcl⟩
  obtain ⟨L', hso', hnL', hne⟩ := other_side hS hΓ hr hso hL.1.2.1.left_mem hn
  obtain ⟨c', u', v', hs', hcl'⟩ := id hso'
  obtain ⟨e, hs⟩ := hs'.exists_end hnL' hn
  have hnt : n ∈ tilde c' := Γ.closure_cell_inter_N hs.1.1 ▸ ⟨hs.1.subset_closure hnL', hn⟩
  rcases hcells c' hs.1.1 hnt with rfl | rfl
  · exfalso
    have het : e ∈ tilde c' := Γ.closure_cell_inter_N hs.1.1 ▸ ⟨hs.1.subset_closure
      hs.1.2.1.right_mem, hs.1.right_mem_N⟩
    rcases (ht ▸ het : e ∈ ({n, m} : Set S)) with rfl | rfl
    · exact hs.1.2.1.ne' rfl
    · exact no_wrap hS hΓ hr hL hs hne.symm hcl hcl' ht
  · exact ⟨r, L', e, hr, hcl, hso, hso', hne, hcl', hs⟩

/-- The two sides of a two-node cell are the whole boundary of the closed cell. -/
theorem other_gap {c L : Set S} {n m : S} (hL : Γ.IsSide c L n m) (ht : tilde c = {n, m}) (hint : ¬
  (c ∩ bd S).Nonempty) : ∃ R, Γ.IsSide c R n m ∧ R ≠ L := by
  obtain ⟨R, hR, hun, hin⟩ := oarc_split (Γ.isClosedDisc_closure_cell hL.1.1).isOArc_discBd
    hL.1.2.1 hL.1.2.2.1
  have hRs : R ⊆ discBd (closure c) := hun ▸ subset_union_right
  have hG : Γ.IsGap c R n m := by
    refine ⟨hL.1.1, hR, hRs, ?_⟩
    apply subset_antisymm
    · rintro z ⟨h, hzN⟩
      exact ht ▸ Γ.closure_cell_inter_N hL.1.1 ▸ ⟨discBd_subset _ (hRs h), hzN⟩
    · rintro z (rfl | rfl)
      · exact ⟨hR.left_mem, hL.1.left_mem_N⟩
      · exact ⟨hR.right_mem, hL.1.right_mem_N⟩
  refine ⟨R, isSide_of_internal hG hint, fun e => ?_⟩
  obtain ⟨z, hz, h3, h4, -⟩ := exists_inner hL.1.2.1 (finite_empty (α := S))
  exact (hin.le ⟨hz, e ▸ hz⟩).elim h3 h4

/-- The curve for a node on two cells, one of them with only two nodes. -/
theorem node_two [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {n : S} {c₀ : Set S}
  (hn : n ∈ Γ.N) (hnb : n ∉ bd S) (h : {c ∈ Γ.C | n ∈ tilde c}.ncard = 2) (h₀ : c₀ ∈ Γ.C)
    (hnc₀ : n ∈ tilde c₀) (h2 : (tilde c₀).ncard = 2) :
    ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧ (F ∩ Γ.N).ncard ≤ 3 ∧
      ∀ Δ : Set S, IsClosedDisc Δ → discBd Δ = F →
        ((Δ ∩ Γ.N ⊆ F ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard ≤ 1) ∨ ((F ∩ Γ.N).ncard = 3 ∧ ∀ c ∈ Γ.C, c ⊆ Δ →
          (tilde c).ncard = 2)) →
        ∃ d₁ ∈ Γ.C, ∃ d₂ ∈ Γ.C, Γ.C ⊆ {d₁, d₂} ∪ {c ∈ Γ.C | c ⊆ Δ} := by
  classical
  have hcS : CompactSpace S := hS.1
  have hman := hS.2.2
  obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp h
  have hx : x ∈ {c ∈ Γ.C | n ∈ tilde c} := hset ▸ .inl rfl
  have hy : y ∈ {c ∈ Γ.C | n ∈ tilde c} := hset ▸ .inr rfl
  have hall : ∀ d ∈ Γ.C, n ∈ tilde d → d = x ∨ d = y := fun d hd hnd => by
    have h3 : d ∈ {c ∈ Γ.C | n ∈ tilde c} := ⟨hd, hnd⟩
    rw [hset] at h3
    exact h3
  obtain ⟨c₁, hne, hc₁, hnc₁, hcells⟩ : ∃ c₁, c₀ ≠ c₁ ∧ c₁ ∈ Γ.C ∧ n ∈ tilde c₁
    ∧ ∀ d ∈ Γ.C, n ∈ tilde d → d = c₀ ∨ d = c₁ := by
    rcases hall c₀ h₀ hnc₀ with rfl | rfl
    · exact ⟨y, hxy, hy.1, hy.2, hall⟩
    · exact ⟨x, hxy.symm, hx.1, hx.2, fun d hd hnd => (hall d hd hnd).symm⟩
  have hint : ∀ d ∈ Γ.C, n ∈ tilde d → ¬ (d ∩ bd S).Nonempty := fun d hd hnd hb => by
    obtain ⟨u, v, -, ht, -, -, hu, hv⟩ := Γ.border_cell_exists_ends hd hb
    rcases (ht ▸ hnd : n ∈ ({u, v} : Set S)) with rfl | rfl
    · exact hnb hu.2
    · exact hnb hv.2
  obtain ⟨m, hmn, ht⟩ : ∃ m, m ≠ n ∧ tilde c₀ = {n, m} := by
    obtain ⟨p, q, hpq, htq⟩ := Set.ncard_eq_two.mp h2
    rcases (htq ▸ hnc₀ : n ∈ ({p, q} : Set S)) with rfl | rfl
    · exact ⟨q, hpq.symm, htq⟩
    · exact ⟨p, hpq, by rw [htq, pair_comm]⟩
  have hmt : m ∈ tilde c₀ := ht ▸ .inr rfl
  obtain ⟨s₀, hs₀G⟩ := exists_gap_pair h₀ hnc₀ hmt hmn.symm
  have hs₀ := isSide_of_internal hs₀G (hint c₀ h₀ hnc₀)
  obtain ⟨R, hR, hRne⟩ := other_gap hs₀ ht (hint c₀ h₀ hnc₀)
  obtain ⟨r, s₁, a, hr, hcl₀, hso₀, hso₁, hne₁, hcl₁, hs₁⟩ := partner hS hΓ hs₀ ht hn hcells
  obtain ⟨r', s₁', b, hr', hclR, hsoR, hso₁', hne₁', hcl₁', hs₁'⟩ := partner hS hΓ hR ht hn hcells
  have hss : s₁ ≠ s₁' := by
    rintro rfl
    obtain rfl := SideOf.unique hS hΓ.isOpen hr hr' hso₁ hso₁'
    exact three_sides hS hΓ hr hso₀ hsoR hso₁ hs₀.1.2.1.left_mem hR.1.2.1.left_mem
      hs₁.1.2.1.left_mem hn hRne.symm hne₁.symm hne₁'.symm
  have hN₁ := hs₁.1.2.2.2
  have hN₁' := hs₁'.1.2.2.2
  obtain ⟨t₀, t₁, ρ, e, hρ, hst₀, hst₁, hclt₀, hclt₁, hinter⟩ : ∃ t₀ t₁ ρ e, ρ ∈ Γ.regions
    ∧ Γ.IsSide c₀ t₀ n m ∧ Γ.IsSide c₁ t₁ n e ∧ t₀ ⊆ closure ρ ∧ t₁ ⊆ closure ρ
      ∧ tilde c₀ ∩ tilde c₁ ⊆ {n, e} := by
    by_cases hm : m ∈ tilde c₁
    · have hor : m = a ∨ m = b := by
        by_contra hcon
        push Not at hcon
        obtain ⟨hma, hmb⟩ := hcon
        by_cases hab : a = b
        · subst hab
          have hi : s₁ ∩ s₁' = {n, a} := by
            apply subset_antisymm
            · rintro z ⟨h3, h4⟩
              refine hN₁.le ⟨h3, ?_⟩
              by_contra hzN
              exact hss (hs₁.1.unique hs₁'.1 h3 h4 hzN).2
            · rintro z (rfl | rfl)
              · exact ⟨hs₁.1.2.1.left_mem, hs₁'.1.2.1.left_mem⟩
              · exact ⟨hs₁.1.2.1.right_mem, hs₁'.1.2.1.right_mem⟩
          obtain ⟨ψ⟩ := id (Γ.isClosedDisc_closure_cell hc₁).isOArc_discBd
          have hbc := oarc_eq ψ (oArc_of_lines hs₁.1.2.1 hs₁'.1.2.1 hi)
            (union_subset hs₁.1.2.2.1 hs₁'.1.2.2.1)
          have hmN : m ∈ Γ.N := Γ.tilde_subset_N h₀ hmt
          rcases (hbc ▸ Γ.tilde_subset_discBd hc₁ hm : m ∈ s₁ ∪ s₁') with h3 | h3
          · exact (hN₁.le ⟨h3, hmN⟩).elim hmn hma
          · exact (hN₁'.le ⟨h3, hmN⟩).elim hmn hma
        · have hat : a ∈ tilde c₁ := Γ.closure_cell_inter_N hc₁ ▸ ⟨hs₁.1.subset_closure
          hs₁.1.2.1.right_mem, hs₁.1.right_mem_N⟩
          have hbt : b ∈ tilde c₁ := Γ.closure_cell_inter_N hc₁ ▸ ⟨hs₁'.1.subset_closure
            hs₁'.1.2.1.right_mem, hs₁'.1.right_mem_N⟩
          have hcard : ({n, a, b, m} : Finset S).card = 4 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
              Finset.card_pair hmb.symm]
            · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hab, hma.symm⟩
            · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hs₁.1.2.1.ne', hs₁'.1.2.1.ne', hmn.symm⟩
          have h4 : ((({n, a, b, m} : Finset S) : Set S)).ncard ≤ (tilde c₁).ncard := by
            refine Set.ncard_le_ncard ?_ (Γ.finite_tilde_cell hc₁)
            intro z hz
            simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
              mem_singleton_iff] at hz
            rcases hz with rfl | rfl | rfl | rfl <;> assumption
          rw [Set.ncard_coe_finset, hcard] at h4
          have := Γ.ncard_tilde_cell_le hc₁
          omega
      rcases hor with rfl | rfl
      · refine ⟨s₀, s₁, r, m, hr, hs₀, hs₁, hcl₀, hcl₁, fun z hz => ?_⟩
        rw [ht] at hz
        exact hz.1
      · refine ⟨R, s₁', r', m, hr', hR, hs₁', hclR, hcl₁', fun z hz => ?_⟩
        rw [ht] at hz
        exact hz.1
    · refine ⟨s₀, s₁, r, a, hr, hs₀, hs₁, hcl₀, hcl₁, fun z hz => ?_⟩
      rcases (ht ▸ hz.1 : z ∈ ({n, m} : Set S)) with rfl | rfl
      · exact .inl rfl
      · exact absurd hz.2 hm
  obtain ⟨E, hE, h₀E, h₁E, hEU, hP, -⟩ := two_cell_disc hS hΓ hρ hst₀ hst₁ hne hclt₀ hclt₁ ht hinter
  have htN : ∀ {c z}, c ∈ Γ.C → z ∈ closure c → z ∈ Γ.N → z ∈ tilde c := fun hc h h'
    => Γ.closure_cell_inter_N hc ▸ ⟨h, h'⟩
  have hEb : E ∩ bd S ⊆ Γ.N := by
    rintro z ⟨hz, hzb⟩
    rcases hEU ⟨hz, Γ.bd_subset hzb⟩ with h3 | h3
    · by_contra hzN
      exact hint c₀ h₀ hnc₀ ⟨z, closure_eq_cell h₀ h3 hzN, hzb⟩
    · by_contra hzN
      exact hint c₁ hc₁ hnc₁ ⟨z, closure_eq_cell hc₁ h3 hzN, hzb⟩
  have hsub : (E ∩ Γ.N) \ {n} ⊆ insert m (tilde c₁ \ {n}) := by
    rintro z ⟨⟨hz, hzN⟩, hzn⟩
    rcases hEU ⟨hz, Γ.N_subset hzN⟩ with h3 | h3
    · rcases (ht ▸ htN h₀ h3 hzN : z ∈ ({n, m} : Set S)) with e' | e'
      · exact absurd e' hzn
      · exact .inl e'
    · exact .inr ⟨htN hc₁ h3 hzN, hzn⟩
  have hfin : (insert m (tilde c₁ \ {n})).Finite := ((Γ.finite_tilde_cell hc₁).subset
    sdiff_subset).insert m
  have hle : ((E ∩ Γ.N) \ {n}).ncard ≤ (tilde c₁).ncard := by
    have h1 := Set.ncard_le_ncard hsub hfin
    have h3 := Set.ncard_insert_le m (tilde c₁ \ {n})
    have h4 := Set.ncard_sdiff_singleton_of_mem hnc₁
    have h5 : 0 < (tilde c₁).ncard := (Set.ncard_pos (Γ.finite_tilde_cell hc₁)).mpr ⟨n, hnc₁⟩
    omega
  have h3 := Γ.ncard_tilde_cell_le hc₁
  exact ring_node hS hE h₀ hc₁ h₀E h₁E hEU (h₀E hnc₀.1) hn hcells hP hEb hnb (by omega) (by omega)

end Painting

end GraphMinor.GM17
