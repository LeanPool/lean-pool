/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.NodeRing

/-!
# A curve past a border node

Here we prove the part of `RegionBoundaryOArcCriterionStatement` on a node on the boundary of the
surface with only border cells at it, which is used in (8.4) of Graph Minors XVII
(page 182). The two sides at the node of the two border cells at it lie on one region. A sector of
this region joins the two cells to a closed disc. A thin disc along the rest of its
boundary gives the normal `I`-arc past the node (`border_node`). A disc that bounds this arc and
misses the node would fill up the surface, so there would be only three nodes.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

namespace Painting

variable {Γ : Painting S} [T2Space S]

/-- `border_side` with a given node as first end. -/
theorem border_side_at (hS : IsSurface S) {c : Set S} {n : S} (hc : c ∈ Γ.C) (hbd :
  (c ∩ bd S).Nonempty) (hn : n ∈ tilde c) :
    ∃ u O, tilde c = {n, u} ∧ IsLineWithEnds (closure c ∩ bd S) n u ∧ Γ.IsSide c O n u ∧ discBd
      (closure c) = (closure c ∩ bd S) ∪ O ∧ (closure c ∩ bd S) ∩ O = {n, u} := by
  obtain ⟨a, b, O, ht, hB, hs, hd, hi, -, -, -⟩ := border_side hS hc hbd
  rcases (ht ▸ hn : n ∈ ({a, b} : Set S)) with rfl | rfl
  · exact ⟨b, O, ht, hB, hs, hd, hi⟩
  · exact ⟨a, O, by rw [ht, pair_comm], hB.symm, hs.symm, hd, by rw [hi, pair_comm]⟩

private theorem normal_border_arc_cannot_bound_node_free_disc
    {S : Type}
    [TopologicalSpace S]
    {Γ : Painting S}
    [T2Space S]
    [ConnectedSpace S]
    (hS : IsSurface S)
    (hΓ : Γ.Tame)
    {n : S}
    (hn : n ∈ Γ.N)
    (hman : ∀ (x : S), IsManifoldPoint x)
    (c₁ : Set S)
    (h₁ : c₁ ∈ Γ.C)
    (hnc₁ : n ∈ tilde c₁)
    (u : S)
    (hB₁ : IsLineWithEnds (closure c₁ ∩ bd S) n u)
    (c₂ : Set S)
    (h₂ : c₂ ∈ Γ.C)
    (v : S)
    (hB₂ : IsLineWithEnds (closure c₂ ∩ bd S) n v)
    (E : Set S)
    (hE : IsClosedDisc E)
    (h₁E : closure c₁ ⊆ E)
    (h₂E : closure c₂ ⊆ E)
    (hEbd : ∀ {z : S}, z ∈ E → z ∈ bd S → z ∈ closure c₁ ∩ bd S ∨ z ∈ closure c₂ ∩ bd S)
    (hEN : ∀ {z : S}, z ∈ E → z ∈ Γ.N → z = n ∨ z = u ∨ z = v)
    (hBnb : ∀ {c : Set S}, c ∈ Γ.C → closure c ⊆ E → ∀ {a b x : S}, IsLineWithEnds (closure c ∩ bd
      S) a b → closure c ∩ bd S ⊆ discBd (closure c) → x ∈ closure c ∩ bd S → x ≠ a → x ≠ b → E ∈
      𝓝 x)
    (hbs₁ : closure c₁ ∩ bd S ⊆ discBd (closure c₁))
    (hbs₂ : closure c₂ ∩ bd S ⊆ discBd (closure c₂))
    (hnu : n ≠ u)
    (hnv : n ≠ v)
    (huv : ¬u = v)
    (L : Set S)
    (hL : IsLineWithEnds L u v)
    (hun : closure c₁ ∩ bd S ∪ closure c₂ ∩ bd S ∪ L = discBd E)
    (hMsub : closure c₁ ∩ bd S ∪ closure c₂ ∩ bd S ⊆ discBd E)
    (hLE : L ⊆ E)
    (hLM : ∀ {z : S}, z ∈ L → z ∈ closure c₁ ∩ bd S ∪ closure c₂ ∩ bd S → z = u ∨ z = v)
    (St : Set S)
    (F : Set S)
    (hSt : IsClosedDisc St)
    (hF : IsLineWithEnds F u v)
    (hbSt : discBd St = L ∪ F)
    (hiF : L ∩ F = {u, v})
    (hStE : St ∩ E = L)
    (hStZ : St ∩ (Γ.N ∪ ⋃ d ∈ Γ.C \ {c₁, c₂}, closure d) ⊆ {u, v})
    (hStb : St ∩ bd S ⊆ {u, v})
    (hnbS : ∀ x ∈ L, x ≠ u → x ≠ v → E ∪ St ∈ 𝓝 x)
    (hFS : F ⊆ St)
    (hLS : L ⊆ St)
    (huL : u ∈ F)
    (hvL : v ∈ F)
    (huU : u ∈ Γ.N)
    (hvU : v ∈ Γ.N)
    (hFb : F ∩ bd S = {u, v})
    (hFN : F ∩ Γ.N = {u, v}) :
    ∀ (Δ : Set S), IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S → ¬(Δ ∩ Γ.N ⊆ F ∧ {c | c ∈
      Γ.C ∧ c ⊆ Δ}.ncard = 1) := by
  let Z := Γ.N ∪ ⋃ d ∈ Γ.C \ {c₁, c₂}, closure d
  rintro Δ hΔ h1 h2 ⟨hN, -⟩
  obtain ⟨K, hK, hunK, hinK, hKb, -, hnbΔ⟩ := disc_along_bd hS hΔ hF hFb h1 h2
  have hnΔ : n ∉ Δ := fun h => by
    have h3 : n ∈ F ∩ Γ.N := ⟨hN ⟨h, hn⟩, hn⟩
    rw [hFN] at h3
    exact h3.elim hnu hnv
  have hP := isPreconnected_disc_diff hE hMsub
  have hPd : Disjoint (E \ ((closure c₁ ∩ bd S) ∪ (closure c₂ ∩ bd S))) (discBd Δ) := by
    refine disjoint_left.mpr fun z hz hz' => ?_
    rcases (hunK ▸ hz' : z ∈ F ∪ K) with h | h
    · have h3 : z ∈ L := hStE.le ⟨hFS h, hz.1⟩
      rcases hiF.le ⟨h3, h⟩ with rfl | rfl
      · exact hz.2 (.inl hB₁.right_mem)
      · exact hz.2 (.inr hB₂.right_mem)
    · exact hz.2 (hEbd hz.1 (hKb h))
  have hPoff : Disjoint (E \ ((closure c₁ ∩ bd S) ∪ (closure c₂ ∩ bd S))) Δ := by
    rcases hΔ.side hman hP hPd with h | h
    · exfalso
      have hsub : discInt E ⊆ E \ ((closure c₁ ∩ bd S) ∪ (closure c₂ ∩ bd S)) := fun z hz
        => ⟨hz.1, fun h' => hz.2 (hMsub h')⟩
      have h3 : E ⊆ Δ := hE.subset_closure_discInt.trans (closure_minimal (hsub.trans
        (h.trans fun _ h' => h'.1)) hΔ.isClosed)
      exact hnΔ (h3 (h₁E hnc₁.1))
    · exact h
  obtain ⟨w, hw, hwu, hwv, -⟩ := exists_inner hL (finite_empty (α := S))
  have hwF : w ∉ F := fun h => (hiF.le ⟨hw, h⟩).elim hwu hwv
  have hwM : w ∉ (closure c₁ ∩ bd S) ∪ (closure c₂ ∩ bd S) := fun h => (hLM hw h).elim hwu hwv
  have h1' : F ⊆ discBd Δ := h1
  have hStΔ : St ∩ Δ = F := by
    apply subset_antisymm
    · refine disc_off hman hSt (hbSt ▸ subset_union_right) hΔ (fun z hz hzF h => ?_)
        (hLS hw) hwF (fun h => disjoint_left.mp hPoff ⟨hLE hw, hwM⟩ h)
      rcases (hunK ▸ h : z ∈ F ∪ K) with h | h
      · exact hzF h
      · exact hzF ((hStb ⟨hz, hKb h⟩).elim (fun e' => e' ▸ huL) (fun e' => e' ▸ hvL))
    · exact fun z hz => ⟨hFS hz, discBd_subset Δ (h1 hz)⟩
  let W : Set S := (E ∪ St) ∪ Δ
  have hWc : IsClosed W := (hE.isClosed.union hSt.isClosed).union hΔ.isClosed
  have hFnb : ∀ {x}, x ∈ F → x ≠ u → x ≠ v → W ∈ 𝓝 x := fun {x} hx hxu hxv =>
    Filter.mem_of_superset (union_nhds hman hSt hΔ hF hStΔ (hbSt ▸ subset_union_right) h1 hx hxu
      hxv) (union_subset (subset_union_right.trans subset_union_left) subset_union_right)
  have hLnb : ∀ {x}, x ∈ L → x ≠ u → x ≠ v → W ∈ 𝓝 x := fun {x} hx hxu hxv =>
    Filter.mem_of_superset (hnbS x hx hxu hxv) subset_union_left
  have hnbW : ∀ x ∈ W, x ∉ ({n, u, v} : Set S) → W ∈ 𝓝 x := by
    intro x hx hxA
    have hxn : x ≠ n := fun e' => hxA (.inl e')
    have hxu : x ≠ u := fun e' => hxA (.inr (.inl e'))
    have hxv : x ≠ v := fun e' => hxA (.inr (.inr e'))
    rcases hx with (h | h) | h
    · by_cases hxb : x ∈ discBd E
      · rcases (hun ▸ hxb : x ∈ ((closure c₁ ∩ bd S) ∪ (closure c₂ ∩ bd S)) ∪ L) with (h3 | h3) | h3
        · exact Filter.mem_of_superset (hBnb h₁ h₁E hB₁ hbs₁ h3 hxn hxu)
            (subset_union_left.trans subset_union_left)
        · exact Filter.mem_of_superset (hBnb h₂ h₂E hB₂ hbs₂ h3 hxn hxv)
            (subset_union_left.trans subset_union_left)
        · exact hLnb h3 hxu hxv
      · exact Filter.mem_of_superset ((hE.isOpen_discInt hman).mem_nhds ⟨h,
          hxb⟩) fun y hy => .inl (.inl hy.1)
    · by_cases hxL : x ∈ L
      · exact hLnb hxL hxu hxv
      · by_cases hxF : x ∈ F
        · exact hFnb hxF hxu hxv
        · exact Filter.mem_of_superset ((hSt.isOpen_discInt hman).mem_nhds ⟨h,
            fun h3 => (hbSt ▸ h3 : x ∈ L ∪ F).elim hxL hxF⟩) fun y hy => .inl (.inr hy.1)
    · by_cases hxF : x ∈ F
      · exact hFnb hxF hxu hxv
      · exact Filter.mem_of_superset (hnbΔ x h hxF) subset_union_right
  obtain ⟨z, hz⟩ := arcComponentsIn_nonempty h₁
  have hzA : z ∉ ({n, u, v} : Set S) := fun h => by
    refine disjoint_left.mp (Γ.cell_disjoint_N h₁) hz ?_
    rcases h with e' | e' | e'
    · exact e' ▸ hn
    · exact e' ▸ huU
    · exact e' ▸ hvU
  have hAc : ({n, u, v} : Set S).ncard ≤ 5 := by
    have h3 := Set.ncard_insert_le n ({u, v} : Set S)
    rw [Set.ncard_pair huv] at h3
    omega
  refine hΓ.not_covered (A := {n, u, v}) (toFinite _) hAc fun y hy => ?_
  by_contra hyA
  rcases cover_off hman hWc (toFinite _) ⟨z, .inl (.inl (h₁E (subset_closure hz))), hzA⟩ hnbW hyA
    with (h | h) | h
  · exact hyA (hEN h hy)
  · exact hyA (.inr (hStZ ⟨h, .inl hy⟩))
  · exact hyA (.inr (hFN ▸ (⟨hN ⟨h, hy⟩, hy⟩ : y ∈ F ∩ Γ.N)))

/-- A node on the boundary of the surface with only border cells at it is passed by a normal arc
that bounds no disc without further nodes. -/
theorem border_node [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {n : S} (hn : n ∈ Γ.N)
  (hall : ∀ c ∈ Γ.C, n ∈ tilde c → (c ∩ bd S).Nonempty) :
    ∃ F : Set S, IsLine F ∧ Γ.IsNormal F ∧ F ∩ bd S = lineEnds F ∧ (F ∩ Γ.N).ncard = 2 ∧
      ∀ Δ : Set S, IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S → ¬ (Δ ∩ Γ.N ⊆ F
        ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard = 1) := by
  classical
  have hcS : CompactSpace S := hS.1
  have hman := hS.2.2
  obtain ⟨c₁, h₁, hnc₁⟩ := node_on_cell hS hΓ hn
  obtain ⟨u, O₁, ht₁, hB₁, hs₁, hd₁, hi₁⟩ := border_side_at hS h₁ (hall c₁ h₁ hnc₁) hnc₁
  obtain ⟨St₀, γ₀, r, -, -, -, -, -, -, -, hr, -, hcl₁, -⟩ := side_strip hS hΓ.isOpen hs₁
    (isClosed_empty (X := S)) (by simp)
  obtain ⟨L', hso', hnL', hL'ne⟩ := other_side hS hΓ hr ⟨c₁, n, u, hs₁, hcl₁⟩ hs₁.1.2.1.left_mem hn
  obtain ⟨c₂, u', v', hs', hcl'⟩ := id hso'
  obtain ⟨e, hsL⟩ := hs'.exists_end hnL' hn
  have h₂ := hsL.1.1
  have hnc₂ : n ∈ tilde c₂ := Γ.closure_cell_inter_N h₂ ▸ ⟨hsL.1.subset_closure hnL', hn⟩
  have hne : c₁ ≠ c₂ := by
    rintro rfl
    obtain ⟨z, hz, h3, h4, -⟩ := exists_inner hsL.1.2.1 (finite_empty (α := S))
    have hzb : z ∉ bd S := fun h => disjoint_left.mp hsL.2 ⟨hz, by
      rintro (e' | e')
      · exact h3 e'
      · exact h4 e'⟩ h
    rcases (hd₁ ▸ hsL.1.2.2.1 hz : z ∈ (closure c₁ ∩ bd S) ∪ O₁) with h | h
    · exact hzb h.2
    · exact hL'ne (hsL.1.unique hs₁.1 hz h (hsL.1.not_mem_N hz h3 h4)).2
  obtain ⟨v, O₂, ht₂, hB₂, hs₂, hd₂, hi₂⟩ := border_side_at hS h₂ (hall c₂ h₂ hnc₂) hnc₂
  have hL'O : L' = O₂ := by
    have hev : e = v := by
      have h3 : e ∈ tilde c₂ := Γ.closure_cell_inter_N h₂ ▸ ⟨hsL.1.subset_closure
        hsL.1.2.1.right_mem, hsL.1.right_mem_N⟩
      rw [ht₂] at h3
      exact h3.elim (fun e' => absurd e'.symm hsL.1.2.1.ne') id
    subst hev
    have hsub : L' ⊆ O₂ := by
      refine hsL.1.2.1.subset_closure_diff.trans (closure_minimal (fun z hz
        => ?_) hs₂.1.2.1.isCompact.isClosed)
      rcases (hd₂ ▸ hsL.1.2.2.1 hz.1 : z ∈ (closure c₂ ∩ bd S) ∪ O₂) with h | h
      · exact absurd h.2 (disjoint_left.mp hsL.2 hz)
      · exact h
    exact hs₂.1.2.1.eq_of_subset (isPreconnected_line hsL.1.2.1) hsub hnL' hsL.1.2.1.right_mem
  subst hL'O
  have hmeet : ∀ {z}, z ∈ closure c₁ → z ∈ closure c₂ → z ∈ Γ.N ∧ (z = n ∨ z = u) ∧ (z = n ∨ z = v)
    := fun {z} h h' => by
    have hzN := closure_inter_closure h₁ h₂ hne ⟨h, h'⟩
    have h3 : z ∈ tilde c₁ := Γ.closure_cell_inter_N h₁ ▸ ⟨h, hzN⟩
    have h4 : z ∈ tilde c₂ := Γ.closure_cell_inter_N h₂ ▸ ⟨h', hzN⟩
    rw [ht₁] at h3
    rw [ht₂] at h4
    exact ⟨hzN, h3, h4⟩
  obtain ⟨E, hE, h₁E, h₂E, hEU, -, hbE⟩ := two_cell_disc hS hΓ hr hs₁ hs₂ hne hcl₁ hcl' ht₁
    (fun z hz => by
    rw [ht₂] at hz
    exact hz.2)
  have hBB₁ : closure c₁ ∩ bd S ⊆ discBd E := fun z hz => hbE z (.inl (hd₁ ▸ .inl hz)) (fun h
    => h.2 (hi₁.le ⟨hz, h.1⟩)) (fun h => disjoint_left.mp hs₂.2 h hz.2)
  have hBB₂ : closure c₂ ∩ bd S ⊆ discBd E := fun z hz => hbE z (.inr (hd₂ ▸ .inl hz)) (fun h
    => disjoint_left.mp hs₁.2 h hz.2) (fun h => h.2 (hi₂.le ⟨hz, h.1⟩))
  have hEbd : ∀ {z}, z ∈ E → z ∈ bd S → z ∈ closure c₁ ∩ bd S ∨ z ∈ closure c₂ ∩ bd S
    := fun {z} hz hb =>
    (hEU ⟨hz, Γ.bd_subset hb⟩).elim (fun h => .inl ⟨h, hb⟩) (fun h => .inr ⟨h, hb⟩)
  have hEN : ∀ {z}, z ∈ E → z ∈ Γ.N → z = n ∨ z = u ∨ z = v := fun {z} hz hzN => by
    rcases hEU ⟨hz, Γ.N_subset hzN⟩ with h | h
    · have h3 : z ∈ tilde c₁ := Γ.closure_cell_inter_N h₁ ▸ ⟨h, hzN⟩
      rw [ht₁] at h3
      exact h3.elim .inl (fun e' => .inr (.inl e'))
    · have h3 : z ∈ tilde c₂ := Γ.closure_cell_inter_N h₂ ▸ ⟨h, hzN⟩
      rw [ht₂] at h3
      exact h3.elim .inl (fun e' => .inr (.inr e'))
  have hBnb : ∀ {c}, c ∈ Γ.C → closure c ⊆ E → ∀ {a b x}, IsLineWithEnds (closure c ∩ bd S) a b
    → closure c ∩ bd S ⊆ discBd (closure c) → x ∈ closure c ∩ bd S →
      x ≠ a → x ≠ b → E ∈ 𝓝 x := by
    intro c hc hcE a b x hl hs hx hxa hxb
    exact Filter.mem_of_superset (disc_nhds hS (Γ.isClosedDisc_closure_cell hc) hl hs rfl hx hxa
      hxb) hcE
  have hbs₁ : closure c₁ ∩ bd S ⊆ discBd (closure c₁) := hd₁ ▸ subset_union_left
  have hbs₂ : closure c₂ ∩ bd S ⊆ discBd (closure c₂) := hd₂ ▸ subset_union_left
  have hnu : n ≠ u := hB₁.ne'
  have hnv : n ≠ v := hB₂.ne'
  by_cases huv : u = v
  · exfalso
    subst huv
    have hi : (closure c₁ ∩ bd S) ∩ (closure c₂ ∩ bd S) = {n, u} := by
      apply subset_antisymm
      · exact fun z hz => (hmeet hz.1.1 hz.2.1).2.1
      · rintro z (rfl | rfl)
        · exact ⟨hB₁.left_mem, hB₂.left_mem⟩
        · exact ⟨hB₁.right_mem, hB₂.right_mem⟩
    obtain ⟨ψ⟩ := id hE.isOArc_discBd
    have hbc := oarc_eq ψ (oArc_of_lines hB₁ hB₂ hi) (union_subset hBB₁ hBB₂)
    have hnbW : ∀ x ∈ E, x ∉ ({n, u} : Set S) → E ∈ 𝓝 x := fun x hx hxA => by
      have hxn : x ≠ n := fun e' => hxA (.inl e')
      have hxu : x ≠ u := fun e' => hxA (.inr e')
      by_cases hxb : x ∈ discBd E
      · rcases (hbc ▸ hxb : x ∈ (closure c₁ ∩ bd S) ∪ (closure c₂ ∩ bd S)) with h | h
        · exact hBnb h₁ h₁E hB₁ hbs₁ h hxn hxu
        · exact hBnb h₂ h₂E hB₂ hbs₂ h hxn hxu
      · exact Filter.mem_of_superset ((hE.isOpen_discInt hman).mem_nhds ⟨hx, hxb⟩) fun y hy => hy.1
    obtain ⟨z, hz⟩ := arcComponentsIn_nonempty h₁
    have hzA : z ∉ ({n, u} : Set S) := fun h => disjoint_left.mp (Γ.cell_disjoint_N h₁) hz (h.elim
      (fun e' => e' ▸ hn) (fun e' => e' ▸ hs₁.1.right_mem_N))
    refine hΓ.not_covered (A := {n, u}) (toFinite _) ((Set.ncard_pair hnu).le.trans
      (by norm_num)) fun y hy => ?_
    by_contra hyA
    rcases hEN (cover_off hman hE.isClosed (toFinite _) ⟨z, h₁E (subset_closure hz), hzA⟩ hnbW hyA)
      hy with e' | e' | e'
    · exact hyA (.inl e')
    · exact hyA (.inr e')
    · exact hyA (.inr e')
  have hiM : (closure c₁ ∩ bd S) ∩ (closure c₂ ∩ bd S) = {n} := by
    apply subset_antisymm
    · rintro z ⟨hz, hz'⟩
      obtain ⟨-, h3, h4⟩ := hmeet hz.1 hz'.1
      rcases h3 with h3 | h3
      · exact h3
      · rcases h4 with h4 | h4
        · exact h4
        · exact absurd (h3.symm.trans h4) huv
    · rintro _ rfl
      exact ⟨hB₁.left_mem, hB₂.left_mem⟩
  have hM := hB₁.symm.union hB₂ hiM
  obtain ⟨L, hL, hun, hin⟩ := oarc_split hE.isOArc_discBd hM (union_subset hBB₁ hBB₂)
  have hMsub : (closure c₁ ∩ bd S) ∪ (closure c₂ ∩ bd S) ⊆ discBd E := union_subset hBB₁ hBB₂
  have hLb : L ⊆ discBd E := hun ▸ subset_union_right
  have hLE : L ⊆ E := hLb.trans (discBd_subset E)
  have hLM : ∀ {z}, z ∈ L → z ∈ (closure c₁ ∩ bd S) ∪ (closure c₂ ∩ bd S) → z = u ∨ z = v
    := fun {z} h h' => hin.le ⟨h', h⟩
  have hLbd : ∀ x ∈ L, x ≠ u → x ≠ v → x ∉ bd S := fun x hx hxu hxv hb =>
    (hLM hx (hEbd (hLE hx) hb)).elim hxu hxv
  have hLN : ∀ {z}, z ∈ L → z ∈ Γ.N → z = u ∨ z = v := fun {z} hz hzN => by
    rcases hEN (hLE hz) hzN with rfl | e' | e'
    · exact hLM hz (.inl hB₁.left_mem)
    · exact .inl e'
    · exact .inr e'
  let Z : Set S := Γ.N ∪ ⋃ d ∈ Γ.C \ {c₁, c₂}, closure d
  have hZ : IsClosed Z := others_closed Γ _
  have hZL : Z ∩ L ⊆ {u, v} := by
    rintro z ⟨h | h, hz⟩
    · exact hLN hz h
    · obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp h
      have hzN : z ∈ Γ.N := by
        rcases hEU ⟨hLE hz, Γ.closure_cell_subset_U hd.1 hzd⟩ with h3 | h3
        · exact closure_inter_closure hd.1 h₁ (fun e' => hd.2 (.inl e')) ⟨hzd, h3⟩
        · exact closure_inter_closure hd.1 h₂ (fun e' => hd.2 (.inr e')) ⟨hzd, h3⟩
      exact hLN hz hzN
  obtain ⟨St, F, hSt, hF, hbSt, hiF, hStE, hStZ, hStb, hnbS⟩ := strip_along hS hE hL hLb hLbd hZ hZL
  have hFS : F ⊆ St := (hbSt ▸ subset_union_right).trans (discBd_subset St)
  have hLS : L ⊆ St := (hbSt ▸ subset_union_left).trans (discBd_subset St)
  have huL : u ∈ F := hF.left_mem
  have hvL : v ∈ F := hF.right_mem
  have hSU : ∀ {z}, z ∈ St → z ∈ Γ.U → z ∈ L := fun {z} hz hzU => by
    have hend : z ∈ Z → z ∈ L := fun h => (hStZ ⟨hz, h⟩).elim (fun e' => e' ▸ hL.left_mem) (fun e'
      => e' ▸ hL.right_mem)
    by_cases hzN : z ∈ Γ.N
    · exact hend (.inl hzN)
    obtain ⟨d, hd, hzd⟩ := exists_mem_arcComponentsIn (F := Γ.U \ Γ.N) (x := z) ⟨hzU, hzN⟩
    by_cases hdc : d ∈ ({c₁, c₂} : Set (Set S))
    · have hzE : z ∈ E := hdc.elim (fun e' => h₁E (e' ▸ subset_closure hzd)) (fun e' => h₂E
      (e' ▸ subset_closure hzd))
      exact hStE.le ⟨hz, hzE⟩
    · exact hend (.inr (mem_iUnion₂.mpr ⟨d, ⟨hd, hdc⟩, subset_closure hzd⟩))
  have hFU : ∀ {z}, z ∈ F → z ∈ Γ.U → z = u ∨ z = v := fun {z} hz hzU => hiF.le ⟨hSU
    (hFS hz) hzU, hz⟩
  have huU : u ∈ Γ.N := hs₁.1.right_mem_N
  have hvU : v ∈ Γ.N := hs₂.1.right_mem_N
  have huB : u ∈ bd S := hB₁.right_mem.2
  have hvB : v ∈ bd S := hB₂.right_mem.2
  have hFb : F ∩ bd S = {u, v} := by
    apply subset_antisymm
    · exact fun z hz => hFU hz.1 (Γ.bd_subset hz.2)
    · rintro z (rfl | rfl)
      · exact ⟨huL, huB⟩
      · exact ⟨hvL, hvB⟩
  have hFN : F ∩ Γ.N = {u, v} := by
    apply subset_antisymm
    · exact fun z hz => hFU hz.1 (Γ.N_subset hz.2)
    · rintro z (rfl | rfl)
      · exact ⟨huL, huU⟩
      · exact ⟨hvL, hvU⟩
  have hnorm : Γ.IsNormal F := fun z hz => (hFU hz.1 hz.2).elim (fun e' => e' ▸ huU) (fun e'
    => e' ▸ hvU)
  obtain ⟨f, -, -⟩ := id hF
  have hnoCap : ∀ Δ : Set S, IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S →
      ¬ (Δ ∩ Γ.N ⊆ F ∧ {c ∈ Γ.C | c ⊆ Δ}.ncard = 1) := by
    exact normal_border_arc_cannot_bound_node_free_disc (S := S) (Γ := Γ) hS hΓ (n := n) hn hman
      c₁ h₁ hnc₁ u hB₁ c₂ h₂ v hB₂ E hE h₁E h₂E hEbd hEN hBnb hbs₁ hbs₂ hnu hnv huv L hL hun hMsub
      hLE hLM St F hSt hF hbSt hiF hStE hStZ hStb hnbS hFS hLS huL hvL huU hvU hFb hFN
  exact ⟨F, ⟨f⟩, hnorm, by rw [lineEnds_eq hF, hFb], by rw [hFN, Set.ncard_pair huv], hnoCap⟩

end Painting

end GraphMinor.GM17
