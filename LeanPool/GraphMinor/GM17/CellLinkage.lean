/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section2
import LeanPool.GraphMinor.GM17.Section7
import LeanPool.GraphMinor.GM17.CuffOrder

/-!
# Walk transfer and linkages through a middle cell

The proofs of Graph Minors XVII (7.3) and (11.3) use the same passage through the two side areas
and the same pairing of the two ends in the middle cell.
-/

public section

namespace GraphMinor.GM17

open Set Surface Hypergraph GM10

universe u v

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

/-- A path using an edge of an interior cell meets at least two of that cell's nodes. -/
theorem interior_cell_active_of_path_edge
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (c₁_end : Set π.S)
    (hc₁_C : c₁_end ∈ π.Γ.C)
    (hc₁_Δ : c₁_end ⊆ Δ)
    (hc₁_bd : (c₁_end ∩ bd π.S).Nonempty)
    (hn₁_c₁ : n₁ ∈ tilde c₁_end)
    (c₂_end : Set π.S)
    (hc₂_C : c₂_end ∈ π.Γ.C)
    (hc₂_Δ : c₂_end ⊆ Δ)
    (hc₂_bd : (c₂_end ∩ bd π.S).Nonempty)
    (hn₂_c₂ : n₂ ∈ tilde c₂_end)
    (j : Fin (p + 1)) :
    ∀ {d : Set π.S}, d ∈ ({d | d ∈ π.Γ.C ∧ d ⊆ Δ}) → ¬(d ∩ bd π.S).Nonempty → ∀ {x y : α}, x ∈ (P
      j).walk.support → y ∈ (P j).walk.support → x ≠ y → ∀ {e₀ : β}, (π.cellGraph d).Inc e₀ x →
      (π.cellGraph d).Inc e₀ y → (fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex ''
      (tilde d ∩ π.domγ)}.ncard) d j := by
  let activeFor := fun d l => 2 ≤ {z | z ∈ (P l).walk.support ∧ z ∈ π.nodeVertex '' (tilde d ∩
    π.domγ)}.ncard
  let I_Δ := {d | d ∈ π.Γ.C ∧ d ⊆ Δ}
  intro d hd hd_int x y hx_sup hy_sup hxy e₀ hincx hincy
  by_contra hnot_act
  have hle_one : ({z ∈ (P j).walk.support |
      z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}).ncard ≤ 1 := by
    change ¬ 2 ≤ _ at hnot_act
    omega
  let H₁ := π.cellsUnion (I_Δ \ {d})
  let H₂ := π.cellGraph d
  have hH₁_le : H₁ ≤ G := π.cellsUnion_le _
  have hH₂_le : H₂ ≤ G := π.cellGraph_le d hd.1
  have h_union : H₁ ∪ H₂ = π.areaGraph Δ := by
    apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq (union_le hH₁_le hH₂_le)
      (π.cellsUnion_le I_Δ)
    · ext v
      simp only [H₁, H₂, Portrayal.cellsUnion, union_vertexSet, mem_union, mem_iUnion]
      exact ⟨by rintro (⟨d', ⟨⟨hd'₁, hd'₂⟩, _⟩, hv⟩ | hv)
                · exact ⟨d', ⟨hd'₁, hd'₁.1⟩, hv⟩
                · exact ⟨d, ⟨hd, hd.1⟩, hv⟩,
             by rintro ⟨d', ⟨hd'₁, _⟩, hv⟩
                by_cases hEq : d' = d
                · exact Or.inr (hEq ▸ hv)
                · exact Or.inl ⟨d', ⟨⟨hd'₁, hEq⟩, hd'₁.1⟩, hv⟩⟩
    · ext e'
      simp only [H₁, H₂, Portrayal.cellsUnion, union_edgeSet, mem_union, mem_iUnion]
      exact ⟨by rintro (⟨d', ⟨⟨hd'₁, hd'₂⟩, _⟩, he'⟩ | he')
                · exact ⟨d', ⟨hd'₁, hd'₁.1⟩, he'⟩
                · exact ⟨d, ⟨hd, hd.1⟩, he'⟩,
             by rintro ⟨d', ⟨hd'₁, _⟩, he'⟩
                by_cases hEq : d' = d
                · exact Or.inr (hEq ▸ he')
                · exact Or.inl ⟨d', ⟨⟨hd'₁, hEq⟩, hd'₁.1⟩, he'⟩⟩
  have hu_H₁ : (P j).first ∈ H₁.vertexSet := by
    have hc₁_ne : c₁_end ≠ d := fun h => hd_int (h ▸ hc₁_bd)
    have hvc₁ : (P j).first ∈ (π.cellGraph c₁_end).vertexSet :=
      π.borderPlus_subset_cellGraph hc₁_C hc₁_bd hn₁_c₁ (P j).first_mem
    exact mem_biUnion ⟨⟨⟨hc₁_C, hc₁_Δ⟩, hc₁_ne⟩, hc₁_C⟩ hvc₁
  have hv_H₁ : (P j).last ∈ H₁.vertexSet := by
    have hc₂_ne : c₂_end ≠ d := fun h => hd_int (h ▸ hc₂_bd)
    have hvc₂ : (P j).last ∈ (π.cellGraph c₂_end).vertexSet :=
      π.borderPlus_subset_cellGraph hc₂_C hc₂_bd hn₂_c₂ (P j).last_mem
    exact mem_biUnion ⟨⟨⟨hc₂_C, hc₂_Δ⟩, hc₂_ne⟩, hc₂_C⟩ hvc₂
  have hsub_inter : {z ∈ (P j).walk.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet} ⊆
      {z ∈ (P j).walk.support | z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)} := by
    rintro z ⟨hz_sup, hz₁, hz₂⟩
    change z ∈ ⋃ d' ∈ _, _ at hz₁
    rw [mem_iUnion₂] at hz₁
    rcases hz₁ with ⟨d', ⟨⟨hd'_I, hd'_ne⟩, _⟩, hzd'⟩
    exact ⟨hz_sup, π.p5 d hd.1 hd_int z hz₂ ⟨d', hd'_I.1, hd'_ne, hzd'⟩⟩
  have hcard_inter : ({z ∈ (P j).walk.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet}).ncard ≤ 1
    := by
    have hfin : ({z ∈ (P j).walk.support |
        z ∈ π.nodeVertex '' (tilde d ∩ π.domγ)}).Finite :=
      (((π.Γ.finite_tilde_cell hd.1).inter_of_left _).image _).subset fun _ hz => hz.2
    exact (ncard_le_ncard hsub_inter hfin).trans hle_one
  have hlift_w : ∀ {a b : α} (w : (π.areaGraph Δ).skeleton.Walk a b),
      ∃ w' : (H₁ ∪ H₂).skeleton.Walk a b, w'.support = w.support := by
    intro a b w
    induction w with
    | nil => exact ⟨.nil, rfl⟩
    | @cons a u b hadj tail ih =>
      obtain ⟨tail', hsup⟩ := ih
      have hadj' : (H₁ ∪ H₂).skeleton.Adj a u := by
        rw [h_union]; exact hadj
      refine ⟨.cons hadj' tail', ?_⟩
      dsimp [SimpleGraph.Walk.support]
      rw [hsup]
  obtain ⟨w', hw'_sup⟩ := hlift_w (P j).walk
  have hw'_path : w'.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hw'_sup]
    exact (P j).isPath.support_nodup
  have hcard_w' : ({z ∈ w'.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet}).ncard ≤ 1 := by
    simpa only [hw'_sup] using hcard_inter
  have hall_H₁ := walk_in_left_of_ncard_support_inter_le_one hH₁_le hH₂_le
    hu_H₁ hv_H₁ w' hw'_path hcard_w'
  have hx_H₁ : x ∈ H₁.vertexSet := hall_H₁ x (hw'_sup ▸ hx_sup)
  have hy_H₁ : y ∈ H₁.vertexSet := hall_H₁ y (hw'_sup ▸ hy_sup)
  have hx_H₂ : x ∈ H₂.vertexSet := H₂.vertex_mem_of_inc hincx
  have hy_H₂ : y ∈ H₂.vertexSet := H₂.vertex_mem_of_inc hincy
  have hpair : ({x, y} : Set α) ⊆
      {z ∈ (P j).walk.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet} := by
    rintro z (rfl | rfl)
    · exact ⟨hx_sup, hx_H₁, hx_H₂⟩
    · exact ⟨hy_sup, hy_H₁, hy_H₂⟩
  have hfin₂ : ({z ∈ (P j).walk.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet}).Finite :=
    H₁.vertexSet_finite.subset fun _ hz => hz.2.1
  have h2 : 2 ≤ ({z ∈ (P j).walk.support | z ∈ H₁.vertexSet ∩ H₂.vertexSet}).ncard := by
    rw [← ncard_pair hxy]
    exact ncard_le_ncard hpair hfin₂
  omega

/-- A one-vertex path at the shared boundary gives a trivial path in the middle cell. -/
theorem common_boundary_vertex_yields_trivial_path
    {α : Type u}
    {β : Type v}
    {G : Hypergraph α β}
    (π : Portrayal G)
    {Θ : Set π.S}
    {Δ : Set π.S}
    {n₁ : π.S}
    {n₂ : π.S}
    {p : ℕ}
    (hΘ : Θ ∈ cuffs π.S)
    (hn₁ : n₁ ∈ π.Γ.N ∩ Θ)
    (hn₂ : n₂ ∈ π.Γ.N ∩ Θ)
    (hinter_sub : ∀ n ∈ π.Γ.N ∩ (Θ ∩ discBd Δ), π.borderPlus n₁ ∩ π.borderPlus n₂ ⊆ π.borderPlus
      n)
    (P : Fin (p + 1) → PathFromTo (π.areaGraph Δ).skeleton (π.borderPlus n₁) (π.borderPlus n₂))
    (m₁ : π.S)
    (m₂ : π.S)
    (c : Set π.S)
    (I₁ : Set π.S)
    (I₂ : Set π.S)
    (hm₁_mem : m₁ ∈ π.Γ.N ∩ (Θ ∩ discBd Δ))
    (hm₂_mem : m₂ ∈ π.Γ.N ∩ (Θ ∩ discBd Δ))
    (hI₁_sub : I₁ ⊆ Θ ∩ discBd Δ)
    (hI₂_sub : I₂ ⊆ Θ ∩ discBd Δ)
    (hord_I : ∀ n ∈ I₁ ∩ π.Γ.N, ∀ n' ∈ I₂ ∩ π.Γ.N, (n ≠ n₁ → n ≠ m₁ → GM19.InOrderOn Θ n₁ n m₁ n')
      ∧ (m₁ ≠ n₁ → n' ≠ n₂ → GM19.InOrderOn Θ n₁ m₁ n' n₂) ∧ (n' ≠ m₂ → n' ≠ n₂ → GM19.InOrderOn Θ
      n m₂ n' n₂) ∧ (n ≠ n₁ → m₂ ≠ n₂ → GM19.InOrderOn Θ n₁ n m₂ n₂))
    (j : Fin (p + 1))
    (Q : PathFromTo (π.areaGraph Δ).skeleton (⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n)
      (⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n))
    (hQ_sub : {z | z ∈ Q.walk.support} ⊆ {z | z ∈ (P j).walk.support})
    (hst : Q.first = Q.last) :
    ∃ Q' : PathFromTo (π.cellGraph c).skeleton (π.borderPlus m₁) (π.borderPlus m₂),
      {z | z ∈ Q'.walk.support} ⊆ {z | z ∈ (P j).walk.support} ∧
        Q'.first ∈ (⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n) ∧ Q'.last ∈ (⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus
          n) := by
  let B₁ := ⋃ n ∈ I₁ ∩ π.Γ.N, π.borderPlus n
  let B₂ := ⋃ n ∈ I₂ ∩ π.Γ.N, π.borderPlus n
  let s := Q.first
  have hs_B₁₀ : s ∈ B₁ := Q.first_mem
  have hs_B₂₀ : s ∈ B₂ := by
    change Q.first ∈ B₂
    rw [hst]
    exact Q.last_mem
  have hs_B₁ : s ∈ B₁ := hs_B₁₀
  have hs_B₂ : s ∈ B₂ := hs_B₂₀
  rw [mem_iUnion₂] at hs_B₁ hs_B₂
  rcases hs_B₁ with ⟨n, hn_I₁, hsn⟩
  rcases hs_B₂ with ⟨n', hn'_I₂, hsn'⟩
  have hn_Θ : n ∈ π.Γ.N ∩ Θ := ⟨hn_I₁.2, (hI₁_sub hn_I₁.1).1⟩
  have hn'_Θ : n' ∈ π.Γ.N ∩ Θ := ⟨hn'_I₂.2, (hI₂_sub hn'_I₂.1).1⟩
  have hm₁_Θ : m₁ ∈ π.Γ.N ∩ Θ := ⟨hm₁_mem.1, hm₁_mem.2.1⟩
  have hm₂_Θ : m₂ ∈ π.Γ.N ∩ Θ := ⟨hm₂_mem.1, hm₂_mem.2.1⟩
  obtain ⟨hord₁, hord₂, hord₃, hord₄⟩ := hord_I n hn_I₁ n' hn'_I₂
  have hs_m₁ : s ∈ π.borderPlus m₁ := by
    by_contra hnot_m₁
    have hs_n₁ : s ∈ π.borderPlus n₁ := by
      by_cases hnn₁ : n = n₁
      · exact hnn₁ ▸ hsn
      · have hnm₁ : n ≠ m₁ := fun h => hnot_m₁ (h ▸ hsn)
        have hord := inOrderOn_cyclic (hord₁ hnn₁ hnm₁)
        exact (π.p7 Θ hΘ n hn_Θ m₁ hm₁_Θ n' hn'_Θ n₁ hn₁ hord s hsn hsn').resolve_left hnot_m₁
    have hm₁_ne_n₁ : m₁ ≠ n₁ := fun h => hnot_m₁ (h ▸ hs_n₁)
    have hs_n₂ : s ∈ π.borderPlus n₂ := by
      by_cases hn'n₂ : n' = n₂
      · exact hn'n₂ ▸ hsn'
      · have hord := hord₂ hm₁_ne_n₁ hn'n₂
        exact (π.p7 Θ hΘ n₁ hn₁ m₁ hm₁_Θ n' hn'_Θ n₂ hn₂ hord s hs_n₁ hsn').resolve_left hnot_m₁
    exact hnot_m₁ (hinter_sub m₁ hm₁_mem ⟨hs_n₁, hs_n₂⟩)
  have hs_m₂ : s ∈ π.borderPlus m₂ := by
    by_contra hnot_m₂
    have hs_n₂ : s ∈ π.borderPlus n₂ := by
      by_cases hn'n₂ : n' = n₂
      · exact hn'n₂ ▸ hsn'
      · have hn'm₂ : n' ≠ m₂ := fun h => hnot_m₂ (h ▸ hsn')
        have hord := hord₃ hn'm₂ hn'n₂
        exact (π.p7 Θ hΘ n hn_Θ m₂ hm₂_Θ n' hn'_Θ n₂ hn₂ hord s hsn hsn').resolve_left hnot_m₂
    have hm₂_ne_n₂ : m₂ ≠ n₂ := fun h => hnot_m₂ (h ▸ hs_n₂)
    have hs_n₁ : s ∈ π.borderPlus n₁ := by
      by_cases hnn₁ : n = n₁
      · exact hnn₁ ▸ hsn
      · have hord := inOrderOn_cyclic (hord₄ hnn₁ hm₂_ne_n₂)
        exact (π.p7 Θ hΘ n hn_Θ m₂ hm₂_Θ n₂ hn₂ n₁ hn₁ hord s hsn hs_n₂).resolve_left hnot_m₂
    exact hnot_m₂ (hinter_sub m₂ hm₂_mem ⟨hs_n₁, hs_n₂⟩)
  refine ⟨⟨s, s, .nil, SimpleGraph.Walk.IsPath.nil, hs_m₁, hs_m₂⟩, ?_, hs_B₁₀, hs_B₂₀⟩
  intro z hz
  exact hQ_sub ((List.mem_singleton.mp hz) ▸ SimpleGraph.Walk.start_mem_support Q.walk)

end GraphMinor.GM17
