/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.RegionCycle

/-!
# Arcs along internal cells

Here we prove the parts of `RegionBoundaryOArcCriterionStatement` on internal cells, which are used
in (8.6) of Graph Minors XVII (page 182). Two nodes of an internal cell on the
boundary of the surface are ends of a side, so pushing this side off the cell gives a normal `I`-arc
(`internal_arc`). If all nodes of an internal cell lie on the boundary of
the surface, one of these arcs bounds no disc with one cell (`internal_bd_arc`). Otherwise the discs
on all sides fill up the surface with few nodes.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- A closed set that is a neighbourhood of its points off a finite set is everything off this set,
if it has a point off the finite set. -/
theorem cover_off [T2Space S] [ConnectedSpace S] (hman : ∀ x : S, IsManifoldPoint x) {W A : Set S}
  (hW : IsClosed W) (hA : A.Finite) (hne : (W \ A).Nonempty)
    (hnb : ∀ x ∈ W, x ∉ A → W ∈ 𝓝 x) {y : S} (hy : y ∉ A) : y ∈ W := by
  have hop : IsOpen (W \ A) := by
    rw [isOpen_iff_mem_nhds]
    exact fun x hx => Filter.inter_mem (hnb x hx.1 hx.2) (hA.isClosed.isOpen_compl.mem_nhds hx.2)
  have hcl : closure (W \ A) ⊆ (W \ A) ∪ A := fun x hx => by
    have h1 : x ∈ W := closure_minimal sdiff_subset hW hx
    by_cases h2 : x ∈ A
    · exact .inr h2
    · exact .inl ⟨h1, h2⟩
  exact (eq_compl_of_frontier_finite hman hop hne hA hcl hy).1

/-- Two discs that share a line of their boundaries and meet only there: their union is a
neighbourhood of the inner points of the line. -/
theorem union_nhds [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {D D' F : Set S} {u v x : S}
  (hD : IsClosedDisc D) (hD' : IsClosedDisc D') (hF : IsLineWithEnds F u v) (hi : D ∩ D' = F)
    (h1 : F ⊆ discBd D) (h2 : F ⊆ discBd D')
    (hx : x ∈ F) (hu : x ≠ u) (hv : x ≠ v) : D ∪ D' ∈ 𝓝 x := by
  obtain ⟨hE, hEb⟩ := disc_union _ _ _ _ _ hD hD' hF hi h1 h2
  have hxi : x ∈ discInt (D ∪ D') := by
    refine ⟨.inl (discBd_subset D (h1 hx)), fun hm => ?_⟩
    rw [hEb] at hm
    refine hm.2 ⟨hx, ?_⟩
    rintro (e | e)
    · exact hu e
    · exact hv e
  exact Filter.mem_of_superset ((hE.isOpen_discInt hman).mem_nhds hxi) fun y hy => hy.1

/-- A disc whose boundary is a line and a part of the boundary of the surface. -/
theorem disc_along_bd [T2Space S] (hS : IsSurface S) {Δ F : Set S} {u v : S} (hΔ : IsClosedDisc Δ)
  (hF : IsLineWithEnds F u v) (hFb : F ∩ bd S = {u, v})
    (h1 : F ⊆ discBd Δ) (h2 : discBd Δ ⊆ F ∪ bd S) :
    ∃ K, IsLineWithEnds K u v ∧ discBd Δ = F ∪ K ∧ F ∩ K = {u, v} ∧ K ⊆ bd S ∧ Δ ∩ bd S = K
      ∧ ∀ x ∈ Δ, x ∉ F → Δ ∈ 𝓝 x := by
  obtain ⟨K, hK, hun, hin⟩ := oarc_split hΔ.isOArc_discBd hF h1
  have hKb : K ⊆ bd S := fun x hx => by
    by_cases hxF : x ∈ F
    · have h3 : x ∈ F ∩ K := ⟨hxF, hx⟩
      rw [hin, ← hFb] at h3
      exact h3.2
    · exact (h2 (hun ▸ .inr hx)).resolve_left hxF
  have hKΔ : K ⊆ discBd Δ := hun ▸ subset_union_right
  have hDb : Δ ∩ bd S = K := by
    apply subset_antisymm
    · rintro y ⟨hy, hyb⟩
      have hyB : y ∈ discBd Δ := by
        by_contra hn
        exact hyb (isInteriorPoint_of_mem_discInt hS.2.2 hΔ ⟨hy, hn⟩)
      rcases (hun ▸ hyB : y ∈ F ∪ K) with h3 | h3
      · have h4 : y ∈ F ∩ K := by
          rw [hin, ← hFb]
          exact ⟨h3, hyb⟩
        exact h4.2
      · exact h3
    · exact fun x hx => ⟨discBd_subset _ (hKΔ hx), hKb hx⟩
  refine ⟨K, hK, hun.symm, hin, hKb, hDb, fun x hx hxF => ?_⟩
  by_cases hxb : x ∈ discBd Δ
  · have hxK : x ∈ K := (hun ▸ hxb : x ∈ F ∪ K).resolve_left hxF
    refine disc_nhds hS hΔ hK hKΔ hDb hxK ?_ ?_
    · rintro rfl
      exact hxF hF.left_mem
    · rintro rfl
      exact hxF hF.right_mem
  · exact Filter.mem_of_superset ((hΔ.isOpen_discInt hS.2.2).mem_nhds ⟨hx, hxb⟩) fun y hy => hy.1

namespace Painting

variable {Γ : Painting S} [T2Space S]

/-- Two distinct nodes of a cell are the ends of a gap, as a cell has at most three nodes. -/
theorem exists_gap_pair {c : Set S} {n₁ n₂ : S} (hc : c ∈ Γ.C) (h₁ : n₁ ∈ tilde c)
  (h₂ : n₂ ∈ tilde c) (hne : n₁ ≠ n₂) : ∃ L, Γ.IsGap c L n₁ n₂ := by
  classical
  have hO := (Γ.isClosedDisc_closure_cell hc).isOArc_discBd
  obtain ⟨A, B, hA, hB, hu, hi⟩ := hO.lines (Γ.tilde_subset_discBd hc h₁)
    (Γ.tilde_subset_discBd hc h₂) hne
  have hAs : A ⊆ discBd (closure c) := hu ▸ subset_union_left
  have hBs : B ⊆ discBd (closure c) := hu ▸ subset_union_right
  have hgap : ∀ {P : Set S}, IsLineWithEnds P n₁ n₂ → P ⊆ discBd (closure c) →
    (∀ x ∈ P, x ∈ tilde c → x = n₁ ∨ x = n₂) → Γ.IsGap c P n₁ n₂ := fun {P} hP hs h => by
    refine ⟨hc, hP, hs, ?_⟩
    apply subset_antisymm
    · rintro x ⟨hx, hxN⟩
      have h3 : x ∈ tilde c := by
        rw [← Γ.closure_cell_inter_N hc]
        exact ⟨discBd_subset _ (hs hx), hxN⟩
      exact h x hx h3
    · rintro x (rfl | rfl)
      · exact ⟨hP.left_mem, Γ.tilde_subset_N hc h₁⟩
      · exact ⟨hP.right_mem, Γ.tilde_subset_N hc h₂⟩
  by_cases hAg : ∀ x ∈ A, x ∈ tilde c → x = n₁ ∨ x = n₂
  · exact ⟨A, hgap hA hAs hAg⟩
  by_cases hBg : ∀ x ∈ B, x ∈ tilde c → x = n₁ ∨ x = n₂
  · exact ⟨B, hgap hB hBs hBg⟩
  exfalso
  push Not at hAg hBg
  obtain ⟨x, hx, hxt, hx1, hx2⟩ := hAg
  obtain ⟨y, hy, hyt, hy1, hy2⟩ := hBg
  have hxy : x ≠ y := by
    rintro rfl
    rcases (hi ▸ ⟨hx, hy⟩ : x ∈ ({n₁, n₂} : Set S)) with h | h
    · exact hx1 h
    · exact hx2 h
  have hs : ({n₁, n₂, x, y} : Finset S).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hxy]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hx2, Ne.symm hy2⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne, Ne.symm hx1, Ne.symm hy1⟩
  have h4 : ((({n₁, n₂, x, y} : Finset S) : Set S)).ncard ≤ (tilde c).ncard := by
    refine Set.ncard_le_ncard ?_ (Γ.finite_tilde_cell hc)
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  rw [Set.ncard_coe_finset, hs] at h4
  have := Γ.ncard_tilde_cell_le hc
  omega

omit [T2Space S] in
theorem isSide_of_internal {c L : Set S} {u v : S} (hL : Γ.IsGap c L u v) (hint : ¬
  (c ∩ bd S).Nonempty) : Γ.IsSide c L u v :=
  ⟨hL, disjoint_left.mpr fun x hx hxb => hint ⟨x, hL.mem_cell hx.1 (fun e => hx.2 (.inl e)) (fun e
    => hx.2 (.inr e)), hxb⟩⟩

/-- The arc from a side with both ends on the boundary of the surface. -/
theorem side_arc [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {c L : Set S} {u v : S}
  (hL : Γ.IsSide c L u v) (hu : u ∈ bd S) (hv : v ∈ bd S) :
    ∃ St F, IsClosedDisc St ∧ IsLineWithEnds F u v ∧ discBd St = L ∪ F ∧ L ∩ F = {u, v}
      ∧ St ∩ Γ.U ⊆ L ∧ F ∩ bd S = {u, v} ∧ F ∩ Γ.N = {u, v} ∧ Γ.IsNormal F
      ∧ (∀ x ∈ L, x ≠ u → x ≠ v → closure c ∪ St ∈ 𝓝 x) := by
  have hcS : CompactSpace S := hS.1
  obtain ⟨St, F, r, hSt, hF, hb, hi, -, -, hSU, -, -, -, hnb⟩ := side_strip hS hΓ.isOpen hL
    isClosed_empty (by simp)
  have hFSt : F ⊆ St := (hb ▸ subset_union_right).trans (discBd_subset St)
  have hUe : ∀ {x}, x ∈ F → x ∈ Γ.U → x = u ∨ x = v := fun {x} hx hxU
    => hi.le ⟨hSU ⟨hFSt hx, hxU⟩, hx⟩
  refine ⟨St, F, hSt, hF, hb, hi, hSU, ?_, ?_, ?_, hnb⟩
  · apply subset_antisymm
    · exact fun x hx => hUe hx.1 (Γ.bd_subset hx.2)
    · rintro x (rfl | rfl)
      · exact ⟨hF.left_mem, hu⟩
      · exact ⟨hF.right_mem, hv⟩
  · apply subset_antisymm
    · exact fun x hx => hUe hx.1 (Γ.N_subset hx.2)
    · rintro x (rfl | rfl)
      · exact ⟨hF.left_mem, hL.1.left_mem_N⟩
      · exact ⟨hF.right_mem, hL.1.right_mem_N⟩
  · intro x hx
    rcases hUe hx.1 hx.2 with rfl | rfl
    · exact hL.1.left_mem_N
    · exact hL.1.right_mem_N

/-- Two nodes on the boundary of the surface of an internal cell are joined by a normal arc. -/
theorem internal_arc [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {c : Set S} {n₁ n₂ : S}
  (hc : c ∈ Γ.C) (hint : ¬ (c ∩ bd S).Nonempty)
    (h₁ : n₁ ∈ closure c ∩ bd S) (h₂ : n₂ ∈ closure c ∩ bd S) (hne : n₁ ≠ n₂) :
    ∃ F : Set S, IsLineWithEnds F n₁ n₂ ∧ Γ.IsNormal F ∧ F ∩ bd S = lineEnds F ∧ F ∩ bd S
      = {n₁, n₂} ∧ F ∩ Γ.N = {n₁, n₂} ∧
      ∀ Δ : Set S, IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S → (Δ ∩
        (bd S \ {n₁, n₂})).Nonempty ∧ ∀ c₀ ∈ Γ.C, (c₀ ∩ Δ).Nonempty → c₀ ⊆ Δ := by
  have ht : ∀ {x}, x ∈ closure c ∩ bd S → x ∈ tilde c := fun {x} hx => ⟨hx.1, fun h
    => hint ⟨x, h, hx.2⟩⟩
  obtain ⟨L, hL⟩ := exists_gap_pair hc (ht h₁) (ht h₂) hne
  obtain ⟨St, F, -, hF, -, -, -, hFb, hFN, hnorm, -⟩ := side_arc hS hΓ
    (isSide_of_internal hL hint) h₁.2 h₂.2
  refine ⟨F, hF, hnorm, by rw [lineEnds_eq hF, hFb], hFb, hFN, fun Δ hΔ h1 h2 => ?_⟩
  obtain ⟨K, hK, hun, hin, hKb, hDb, hnb⟩ := disc_along_bd hS hΔ hF hFb h1 h2
  constructor
  · obtain ⟨z, hz, h3, h4, -⟩ := exists_inner hK (finite_empty (α := S))
    exact ⟨z, ⟨discBd_subset _ (hun ▸ .inr hz), hKb hz, by rintro (e | e); exacts [h3 e, h4 e]⟩⟩
  · rintro c₀ hc₀ ⟨x, hx, hxΔ⟩
    rcases cell_side hc₀ hnorm hΔ (fun y hy => hnb y hy.1 hy.2) with h | h
    · exact h
    · exact absurd hxΔ (h hx)

/-- The piece of the surface on the far side of a side with ends on the boundary of the surface, if
the arc from the side bounds a disc with one cell and no other nodes. -/
theorem side_piece [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {c L : Set S} {u v : S}
  (hint : ¬ (c ∩ bd S).Nonempty) (hL : Γ.IsSide c L u v) (hu : u ∈ bd S) (hv : v ∈ bd S)
    (hno : ∀ F : Set S, IsLine F → Γ.IsNormal F → F ∩ bd S = lineEnds F → (F ∩ Γ.N).ncard = 2
      → ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S
        ∧ Δ ∩ Γ.N ⊆ F ∧ {d ∈ Γ.C | d ⊆ Δ}.ncard = 1) :
    ∃ D, IsClosed D ∧ (∀ x ∈ D, x ≠ u → x ≠ v → closure c ∪ D ∈ 𝓝 x) ∧ (∀ x ∈ L, x ≠ u → x ≠ v
      → closure c ∪ D ∈ 𝓝 x) ∧ D ∩ Γ.N ⊆ {u, v} := by
  have hman := hS.2.2
  have hc := hL.1.1
  obtain ⟨St, F, hSt, hF, hb, hi, hSU, hFb, hFN, hnorm, hnb⟩ := side_arc hS hΓ hL hu hv
  have huv := hF.ne'
  have hcard : (F ∩ Γ.N).ncard = 2 := by
    rw [hFN, Set.ncard_pair huv]
  obtain ⟨f, -, -⟩ := id hF
  obtain ⟨Δ, hΔ, h1, h2, hN, hcount⟩ := hno F ⟨f⟩ hnorm (by rw [lineEnds_eq hF, hFb]) hcard
  obtain ⟨K, hK, hun, hin, hKb, -, hnbΔ⟩ := disc_along_bd hS hΔ hF hFb h1 h2
  have hside := fun d hd => cell_side (Γ := Γ) (c := d) hd hnorm hΔ (fun y hy => hnbΔ y hy.1 hy.2)
  have hKΔ : K ⊆ Δ := (hun ▸ subset_union_right : K ⊆ discBd Δ).trans (discBd_subset Δ)
  obtain ⟨c', hc', hc'Δ, hc'b, -, -⟩ := exists_border_cell hK hKb hKΔ hL.1.left_mem_N hside
  have hcoff : c ⊆ Δᶜ := by
    rcases hside c hc with h | h
    · exfalso
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hcount
      have e1 : c ∈ ({a} : Set (Set S)) := ha ▸ ⟨hc, h⟩
      have e2 : c' ∈ ({a} : Set (Set S)) := ha ▸ ⟨hc', hc'Δ⟩
      rw [mem_singleton_iff] at e1 e2
      exact hint (e1.trans e2.symm ▸ hc'b)
    · exact h
  have hLF : F ⊆ discBd St := hb ▸ subset_union_right
  have hStΔ : St ∩ Δ = F := by
    apply subset_antisymm
    · have hY := isPreconnected_disc_diff hSt hLF
      have hd : Disjoint (St \ F) (discBd Δ) := by
        refine disjoint_left.mpr fun y hy hy' => ?_
        have hyK : y ∈ K := (hun ▸ hy' : y ∈ F ∪ K).resolve_left hy.2
        have hyL : y ∈ L := hSU ⟨hy.1, Γ.bd_subset (hKb hyK)⟩
        by_cases hu' : y = u
        · exact hy.2 (hu' ▸ hF.left_mem)
        · by_cases hv' : y = v
          · exact hy.2 (hv' ▸ hF.right_mem)
          · exact disjoint_left.mp hL.2 ⟨hyL, by rintro (e | e); exacts [hu' e, hv' e]⟩ (hKb hyK)
      rcases hΔ.side hman hY hd with h | h
      · exfalso
        obtain ⟨z, hz, h3, h4, -⟩ := exists_inner hL.1.2.1 (finite_empty (α := S))
        have hzc := hL.1.mem_cell hz h3 h4
        have hzSt : z ∈ St := discBd_subset St (hb ▸ .inl hz)
        have hzF : z ∉ F := fun h5 => by
          rcases (hi ▸ ⟨hz, h5⟩ : z ∈ ({u, v} : Set S)) with e | e
          · exact h3 e
          · exact h4 e
        exact hcoff hzc (h ⟨hzSt, hzF⟩).1
      · rintro y ⟨hy, hy'⟩
        by_contra hn
        exact disjoint_left.mp h ⟨hy, hn⟩ hy'
    · exact fun x hx => ⟨discBd_subset St (hLF hx), discBd_subset Δ (h1 hx)⟩
  refine ⟨St ∪ Δ, hSt.isClosed.union hΔ.isClosed, ?_, ?_, ?_⟩
  · rintro x hx hxu hxv
    by_cases hxF : x ∈ F
    · apply Filter.mem_of_superset (union_nhds hman hSt hΔ hF hStΔ hLF h1 hxF hxu hxv)
      exact subset_union_right
    · rcases hx with hx | hx
      · by_cases hxL : x ∈ L
        · exact Filter.mem_of_superset (hnb x hxL hxu hxv)
            (union_subset_union_right _ subset_union_left)
        · have hxi : x ∈ discInt St := ⟨hx, fun h => (hb ▸ h : x ∈ L ∪ F).elim hxL hxF⟩
          exact Filter.mem_of_superset ((hSt.isOpen_discInt hman).mem_nhds hxi) fun y hy => .inr
            (.inl hy.1)
      · exact Filter.mem_of_superset (hnbΔ x hx hxF) fun y hy => .inr (.inr hy)
  · intro x hx hxu hxv
    exact Filter.mem_of_superset (hnb x hx hxu hxv) (union_subset_union_right _ subset_union_left)
  · rintro x ⟨hx | hx, hxN⟩
    · exact (hL.1.2.2.2 ▸ ⟨hSU ⟨hx, Γ.N_subset hxN⟩, hxN⟩ : x ∈ ({u, v} : Set S))
    · rw [← hFN]
      exact ⟨hN ⟨hx, hxN⟩, hxN⟩

/-- If all nodes of an internal cell lie on the boundary of the surface, then the arc from one of
its sides bounds no disc with one cell and no other nodes. -/
theorem internal_bd_arc [ConnectedSpace S] (hS : IsSurface S) (hΓ : Γ.Tame) {c : Set S}
  (hc : c ∈ Γ.C) (hint : ¬ (c ∩ bd S).Nonempty) (ht : tilde c ⊆ bd S) :
    ∃ F : Set S, IsLine F ∧ Γ.IsNormal F ∧ F ∩ bd S = lineEnds F ∧ (F ∩ Γ.N).ncard = 2
      ∧ ∀ Δ : Set S, IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S →
        ¬ (Δ ∩ Γ.N ⊆ F ∧ {d ∈ Γ.C | d ⊆ Δ}.ncard = 1) := by
  classical
  by_contra hcon
  push Not at hcon
  have hno : ∀ F : Set S, IsLine F → Γ.IsNormal F → F ∩ bd S = lineEnds F → (F ∩ Γ.N).ncard = 2
    → ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S
      ∧ Δ ∩ Γ.N ⊆ F ∧ {d ∈ Γ.C | d ⊆ Δ}.ncard = 1 := by
    intro F h1 h2 h3 h4
    obtain ⟨Δ, h5, h6, h7, h8, h9⟩ := hcon F h1 h2 h3 h4
    exact ⟨Δ, h5, h6, h7, h8, h9⟩
  have hman := hS.2.2
  obtain ⟨x₀, hx₀, y₀, hy₀, hne⟩ := two_nodes hS hΓ hc
  obtain ⟨𝓕, hf, hgap, hu⟩ := exists_gaps hc hx₀ hy₀ hne
  have htN : ∀ {x}, x ∈ closure c → x ∈ Γ.N → x ∈ tilde c := fun {x} hx hn => by
    rw [← Γ.closure_cell_inter_N hc]
    exact ⟨hx, hn⟩
  have hkey : ∀ F ∈ 𝓕, ∃ D, IsClosed D ∧ (∀ x ∈ D, x ∉ tilde c → closure c ∪ D ∈ 𝓝 x) ∧
    (∀ x ∈ F, x ∉ tilde c → closure c ∪ D ∈ 𝓝 x) ∧ D ∩ Γ.N ⊆ tilde c := fun F hF => by
    obtain ⟨u, v, hG⟩ := hgap F hF
    have hut : u ∈ tilde c := htN (hG.subset_closure hG.2.1.left_mem) hG.left_mem_N
    have hvt : v ∈ tilde c := htN (hG.subset_closure hG.2.1.right_mem) hG.right_mem_N
    obtain ⟨D, h1, h2, h3, h4⟩ := side_piece hS hΓ hint (isSide_of_internal hG hint) (ht hut)
      (ht hvt) hno
    refine ⟨D, h1, fun x hx hxt => h2 x hx (fun e => hxt (e ▸ hut)) (fun e => hxt (e ▸ hvt)),
      fun x hx hxt => h3 x hx (fun e => hxt (e ▸ hut)) (fun e => hxt (e ▸ hvt)), fun x hx => ?_⟩
    rcases h4 hx with rfl | rfl
    · exact hut
    · exact hvt
  choose! D hDc hD1 hD2 hDN using hkey
  let W : Set S := closure c ∪ ⋃ F ∈ 𝓕, D F
  have hWc : IsClosed W := isClosed_closure.union (hf.isClosed_biUnion hDc)
  have hsub : ∀ {F}, F ∈ 𝓕 → closure c ∪ D F ⊆ W := fun {F} hF x hx => hx.elim .inl (fun h => .inr
    (mem_iUnion₂.mpr ⟨F, hF, h⟩))
  obtain ⟨z, hz⟩ := arcComponentsIn_nonempty hc
  have hWne : (W \ tilde c).Nonempty := ⟨z, .inl (subset_closure hz), fun h => h.2 hz⟩
  have hnbW : ∀ x ∈ W, x ∉ tilde c → W ∈ 𝓝 x := by
    rintro x (hx | hx) hxt
    · by_cases hxb : x ∈ discBd (closure c)
      · obtain ⟨F, hF, hxF⟩ := (hu ▸ hxb : x ∈ ⋃₀ 𝓕)
        exact Filter.mem_of_superset (hD2 F hF x hxF hxt) (hsub hF)
      · exact Filter.mem_of_superset (((Γ.isClosedDisc_closure_cell hc).isOpen_discInt
        hman).mem_nhds ⟨hx, hxb⟩) fun y hy => .inl hy.1
    · obtain ⟨F, hF, hxF⟩ := mem_iUnion₂.mp hx
      exact Filter.mem_of_superset (hD1 F hF x hxF hxt) (hsub hF)
  refine hΓ.not_covered (Γ.finite_tilde_cell hc) ((Γ.ncard_tilde_cell_le hc).trans
    (by norm_num)) fun n hn => ?_
  by_contra hnt
  rcases cover_off hman hWc (Γ.finite_tilde_cell hc) hWne hnbW hnt with h | h
  · exact hnt (htN h hn)
  · obtain ⟨F, hF, h1⟩ := mem_iUnion₂.mp h
    exact hnt (hDN F hF ⟨h1, hn⟩)

end Painting

end GraphMinor.GM17
