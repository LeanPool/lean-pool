/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section2

/-!
# Walk transfer and linkages through a middle cell

The proofs of Graph Minors XVII (7.3) and (11.3) use the same passage through the two side areas
and the same pairing of the two ends in the middle cell.
-/

public section

namespace GraphMinor.GM17

open Set Surface Hypergraph GM10

/-- Lift a walk to the two side areas and the middle cell, preserving its vertex sequence. -/
theorem walk_lifts_to_three_areas
    {α β : Type*} {G : Hypergraph α β} (π : Portrayal G)
    {Δ c I₁ I₂ N₁ N₂ : Set π.S} (active : Set π.S → Prop) (nodes : Set π.S → Set π.S)
    (hborder_split : ∀ d ∈ π.Γ.C, d ⊆ Δ → (d ∩ bd π.S).Nonempty → d ≠ c →
      tilde d ⊆ I₁ ∨ tilde d ⊆ I₂)
    (hint_split : ∀ d ∈ π.Γ.C, d ⊆ Δ → ¬ (d ∩ bd π.S).Nonempty →
      nodes d ⊆ N₁ ∪ I₁ ∨ nodes d ⊆ N₂ ∪ I₂)
    {a b : α} (walk : (π.areaGraph Δ).skeleton.Walk a b) {supportVertices : Set α}
    (hQ_sub : {z | z ∈ walk.support} ⊆ supportVertices)
    (hcell_active : ∀ {d : Set π.S}, d ∈ π.Γ.C ∧ d ⊆ Δ → ¬ (d ∩ bd π.S).Nonempty →
      ∀ {x y : α}, x ∈ supportVertices → y ∈ supportVertices → x ≠ y →
      ∀ {e₀ : β}, (π.cellGraph d).Inc e₀ x → (π.cellGraph d).Inc e₀ y → active d) :
    let I_Δ := {d | d ∈ π.Γ.C ∧ d ⊆ Δ}
    let D₁ := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₁ ∨
      ¬ (d ∩ bd π.S).Nonempty ∧ active d ∧ nodes d ⊆ N₁ ∪ I₁)}
    let D₂ := {d | d ∈ I_Δ ∧ ((d ∩ bd π.S).Nonempty ∧ d ≠ c ∧ tilde d ⊆ I₂ ∨
      ¬ (d ∩ bd π.S).Nonempty ∧ active d ∧ nodes d ⊆ N₂ ∪ I₂)}
    let H₁ := π.cellsUnion D₁
    let H₂ := π.cellsUnion D₂
    let Hc := π.cellGraph c
    ∃ w₀ : (H₁ ∪ (H₂ ∪ Hc)).skeleton.Walk a b, w₀.support = walk.support := by
  intro I_Δ D₁ D₂ H₁ H₂ Hc
  have hstep_all : ∀ {x y : α}, x ∈ supportVertices → y ∈ supportVertices →
      (π.areaGraph Δ).skeleton.Adj x y → (H₁ ∪ (H₂ ∪ Hc)).skeleton.Adj x y := by
    rintro x y hx hy ⟨hxy, e₀, hincx, hincy⟩
    have he₀_mem : e₀ ∈ (π.areaGraph Δ).edgeSet :=
      (π.areaGraph Δ).edge_mem_of_inc hincx
    change e₀ ∈ ⋃ d ∈ _, _ at he₀_mem
    rw [mem_iUnion₂] at he₀_mem
    rcases he₀_mem with ⟨d, ⟨hd_I, hd_C⟩, hed⟩
    have hincx_G : G.Inc e₀ x :=
      (inc_iff_of_le (π.cellsUnion_le I_Δ) ((π.areaGraph Δ).edge_mem_of_inc hincx)).mp hincx
    have hincy_G : G.Inc e₀ y :=
      (inc_iff_of_le (π.cellsUnion_le I_Δ) ((π.areaGraph Δ).edge_mem_of_inc hincy)).mp hincy
    have hincx_d : (π.cellGraph d).Inc e₀ x :=
      (inc_iff_of_le (π.cellGraph_le d hd_C) hed).mpr hincx_G
    have hincy_d : (π.cellGraph d).Inc e₀ y :=
      (inc_iff_of_le (π.cellGraph_le d hd_C) hed).mpr hincy_G
    by_cases hdc : d = c
    · subst hdc
      exact ⟨hxy, e₀, Or.inr (Or.inr hincx_d), Or.inr (Or.inr hincy_d)⟩
    · by_cases hbd_d : (d ∩ bd π.S).Nonempty
      · rcases hborder_split d hd_I.1 hd_I.2 hbd_d hdc with ht₁ | ht₂
        · have hd_D₁ : d ∈ D₁ := ⟨hd_I, Or.inl ⟨hbd_d, hdc, ht₁⟩⟩
          refine ⟨hxy, e₀,
            Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₁ hd_C) hed).mp hincx_d),
            Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₁ hd_C) hed).mp hincy_d)⟩
        · have hd_D₂ : d ∈ D₂ := ⟨hd_I, Or.inl ⟨hbd_d, hdc, ht₂⟩⟩
          refine ⟨hxy, e₀,
            Or.inr (Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₂ hd_C) hed).mp
              hincx_d)),
            Or.inr (Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₂ hd_C) hed).mp
              hincy_d))⟩
      · have hact_d : active d :=
          hcell_active hd_I hbd_d hx hy hxy hincx_d hincy_d
        rcases hint_split d hd_I.1 hd_I.2 hbd_d with he₁ | he₂
        · have hd_D₁ : d ∈ D₁ := ⟨hd_I, Or.inr ⟨hbd_d, hact_d, he₁⟩⟩
          refine ⟨hxy, e₀,
            Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₁ hd_C) hed).mp hincx_d),
            Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₁ hd_C) hed).mp hincy_d)⟩
        · have hd_D₂ : d ∈ D₂ := ⟨hd_I, Or.inr ⟨hbd_d, hact_d, he₂⟩⟩
          refine ⟨hxy, e₀,
            Or.inr (Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₂ hd_C) hed).mp
              hincx_d)),
            Or.inr (Or.inl ((inc_iff_of_le (π.cellGraph_le_cellsUnion hd_D₂ hd_C) hed).mp
              hincy_d))⟩
  have hlift_walk : ∀ {a b : α} (w : (π.areaGraph Δ).skeleton.Walk a b),
      {z | z ∈ w.support} ⊆ {z | z ∈ supportVertices} →
      ∃ w₀ : (H₁ ∪ (H₂ ∪ Hc)).skeleton.Walk a b, w₀.support = w.support := by
    intro a b w hw_sub
    induction w with
    | nil => exact ⟨.nil, rfl⟩
    | @cons a x b hadj tail ih =>
      have ha_P : a ∈ supportVertices := hw_sub (SimpleGraph.Walk.start_mem_support _)
      have hx_P : x ∈ supportVertices :=
        hw_sub (List.mem_cons_of_mem a (SimpleGraph.Walk.start_mem_support tail))
      obtain ⟨tail₀, hsup⟩ := ih (fun z hz => hw_sub (List.mem_cons_of_mem a hz))
      refine ⟨.cons (hstep_all ha_P hx_P hadj) tail₀, ?_⟩
      dsimp [SimpleGraph.Walk.support]
      rw [hsup]
  exact hlift_walk walk hQ_sub

/-- A full linkage through the middle cell pairs the two marked end vertices. -/
theorem no_partial_middle_cell_linkage
    {α β : Type*} {G : Hypergraph α β} (π : Portrayal G) {Θ c : Set π.S} {p : ℕ}
    (supportVertices : Fin (p + 1) → Set α) (hP_disj : Pairwise fun i j =>
      Disjoint (supportVertices i) (supportVertices j))
    (hwarp : π.warpAt Θ ≤ p) {m₁ m₂ : π.S}
    (hm₁_bd : m₁ ∈ π.Γ.N ∩ bd π.S) (hm₂_bd : m₂ ∈ π.Γ.N ∩ bd π.S) (hm_ne : m₁ ≠ m₂)
    (hc_C : c ∈ π.Γ.C) (hc_Θ : (c ∩ Θ).Nonempty) (hc_bd : (c ∩ bd π.S).Nonempty)
    (htilde_c : tilde c = {m₁, m₂}) {j₀ : Fin (p + 1)}
    (hP_m₁ : π.nodeVertex m₁ ∈ supportVertices j₀)
    (hP_m₂ : ¬ (m₂ ∈ π.domγ ∧ π.nodeVertex m₂ ∈ supportVertices j₀))
    (hclaim : ∀ j, ∃ Q : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂),
      {z | z ∈ Q.walk.support} ⊆ supportVertices j) : False := by
  let Q' : Fin (p + 1) → PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂) :=
    fun j => Classical.choose (hclaim j)
  have hQ'_sub : ∀ j, {z | z ∈ (Q' j).walk.support} ⊆ supportVertices j :=
    fun j => Classical.choose_spec (hclaim j)
  have hQ'_disj : Pairwise fun i j =>
      Disjoint {z | z ∈ (Q' i).walk.support} {z | z ∈ (Q' j).walk.support} :=
    fun _ _ hij => (hP_disj hij).mono (hQ'_sub _) (hQ'_sub _)
  have hinj_Q'_first : Function.Injective (fun j => (Q' j).first) := by
    intro i j hij
    change (Q' i).first = (Q' j).first at hij
    by_contra hne_ij
    have hi_mem : (Q' j).first ∈ {z | z ∈ (Q' i).walk.support} :=
      hij ▸ SimpleGraph.Walk.start_mem_support (Q' i).walk
    exact Set.disjoint_left.mp (hQ'_disj hne_ij) hi_mem
      (SimpleGraph.Walk.start_mem_support (Q' j).walk)
  have hinj_Q'_last : Function.Injective (fun j => (Q' j).last) := by
    intro i j hij
    change (Q' i).last = (Q' j).last at hij
    by_contra hne_ij
    have hi_mem : (Q' j).last ∈ {z | z ∈ (Q' i).walk.support} :=
      hij ▸ SimpleGraph.Walk.end_mem_support (Q' i).walk
    exact Set.disjoint_left.mp (hQ'_disj hne_ij) hi_mem
      (SimpleGraph.Walk.end_mem_support (Q' j).walk)
  have hm₁_tc : m₁ ∈ tilde c := htilde_c ▸ mem_insert _ _
  have hm₂_tc : m₂ ∈ tilde c := htilde_c ▸ mem_insert_of_mem _ (mem_singleton _)
  have hcw_le : π.cellWarp c ≤ p := (π.cellWarp_le_warpAt hc_C hc_Θ).trans hwarp
  have hspec_c := π.cellWarp_spec hc_C hc_bd m₁ hm₁_tc m₂ hm₂_tc hm_ne
  have hbp_m₁_le : (π.borderPlus m₁).ncard ≤ π.cellWarp c + 1 :=
    (π.ncard_borderPlus_le hm₁_bd).trans (Nat.add_le_add_right hspec_c.1 1)
  have hbp_m₂_le : (π.borderPlus m₂).ncard ≤ π.cellWarp c + 1 :=
    (π.ncard_borderPlus_le hm₂_bd).trans (Nat.add_le_add_right hspec_c.2.1 1)
  have hbp_m₁_ge : p + 1 ≤ (π.borderPlus m₁).ncard := by
    have hsub : Set.range (fun j => (Q' j).first) ⊆ π.borderPlus m₁ := by
      rintro _ ⟨j, rfl⟩; exact (Q' j).first_mem
    have hcard_r : (Set.range (fun j => (Q' j).first)).ncard = p + 1 := by
      rw [ncard_range_of_injective hinj_Q'_first, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hcard_r ▸ ncard_le_ncard hsub (π.borderPlus_finite hm₁_bd)
  have hbp_m₂_ge : p + 1 ≤ (π.borderPlus m₂).ncard := by
    have hsub : Set.range (fun j => (Q' j).last) ⊆ π.borderPlus m₂ := by
      rintro _ ⟨j, rfl⟩; exact (Q' j).last_mem
    have hcard_r : (Set.range (fun j => (Q' j).last)).ncard = p + 1 := by
      rw [ncard_range_of_injective hinj_Q'_last, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hcard_r ▸ ncard_le_ncard hsub (π.borderPlus_finite hm₂_bd)
  have hcw_eq : π.cellWarp c = p := by omega
  have hlink_c : Portrayal.LinkagePairs (π.cellGraph c).skeleton
      (π.borderPlus m₁) (π.borderPlus m₂) (p + 1) (π.nodeVertex m₁) (π.nodeVertex m₂) := by
    have h1 : (π.borderPlus m₁).ncard = π.cellWarp c + 1 := by omega
    have h2 : (π.borderPlus m₂).ncard = π.cellWarp c + 1 := by omega
    have h0 := hspec_c.2.2 h1 h2
    rwa [hcw_eq] at h0
  have hm₂_dom : m₂ ∈ π.domγ := by
    by_contra hm₂_not
    have hbp_eq : π.borderPlus m₂ = π.borderSet m₂ := by
      ext v; simp [Portrayal.borderPlus, hm₂_not]
    rw [hbp_eq] at hbp_m₂_ge
    have := hspec_c.2.1
    omega
  obtain ⟨j₁, hj₁_first, hj₁_last⟩ := hlink_c Q' hQ'_disj
  have hj₁_eq_j₀ : j₁ = j₀ := by
    by_contra hne_j
    exact Set.disjoint_left.mp (hP_disj hne_j)
      (hQ'_sub j₁ (hj₁_first ▸ SimpleGraph.Walk.start_mem_support (Q' j₁).walk))
      hP_m₁
  have hm₂_in_P₀ : π.nodeVertex m₂ ∈ supportVertices j₀ :=
    hj₁_eq_j₀ ▸ hQ'_sub j₁ (hj₁_last ▸ SimpleGraph.Walk.end_mem_support (Q' j₁).walk)
  exact hP_m₂ ⟨hm₂_dom, hm₂_in_P₀⟩

end GraphMinor.GM17
