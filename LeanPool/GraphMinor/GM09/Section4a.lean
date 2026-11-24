/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2a
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3b
import LeanPool.GraphMinor.GM09.Section3c
import Mathlib.Data.Set.Card

/-!
# Graph Minors IX, Section 4 (Part 1): Separating Paths and (4.1)–(4.3)

This file formalizes (4.1), (4.2), and (4.3) from Section 4 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (pages 49–50).
-/

public section

namespace GraphMinor.GM09

open Set Graph GraphMinor GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

/-! ## Subpath equality when ends match -/

private theorem walk_support_edges_sub_of_isSimple_left {G G₁ G₂ : Graph α β} {a b s : α}
    {W : GraphWalk G a b} {W₁ : GraphWalk G₁ a s} {W₂ : GraphWalk G₂ a s}
    (hl₁ : ∀ ⦃e x y⦄, G₁.IsLink e x y → G.IsLink e x y)
    (hl₂ : ∀ ⦃e x y⦄, G₂.IsLink e x y → G.IsLink e x y)
    (hW : W.IsSimple) (hW₁ : W₁.IsSimple) (hW₂ : W₂.IsSimple)
    (he₁ : ∀ e ∈ W₁.edges, e ∈ W.edges)
    (he₂ : ∀ e ∈ W₂.edges, e ∈ W.edges) :
    (∀ x ∈ W₁.support, x ∈ W₂.support) ∧ (∀ e ∈ W₁.edges, e ∈ W₂.edges) := by
  induction W with
  | nil _ =>
    cases W₁ with
    | nil _ =>
      refine ⟨fun x hx => ?_, fun e he => by simp [GraphWalk.edges] at he⟩
      simp only [GraphWalk.support_nil, List.mem_singleton] at hx
      exact hx ▸ W₂.start_mem_support
    | @cons _ _ _ e _ _ =>
      exact (List.not_mem_nil (he₁ e List.mem_cons_self)).elim
  | @cons u y w e hxy W_tail ih =>
    have hnodup : (u :: W_tail.support).Nodup := hW
    have ha_not_tail : u ∉ W_tail.support := (List.nodup_cons.mp hnodup).1
    have hW_tail_simple : W_tail.IsSimple := (List.nodup_cons.mp hnodup).2
    have hay : u ≠ y := fun h => ha_not_tail (h ▸ W_tail.start_mem_support)
    cases W₁ with
    | nil _ =>
      refine ⟨fun x hx => ?_, fun f hf => by simp [GraphWalk.edges] at hf⟩
      simp only [GraphWalk.support_nil, List.mem_singleton] at hx
      exact hx ▸ W₂.start_mem_support
    | @cons _ y₁ _ e₁ hxy₁ W₁_tail =>
      have hnodup₁ : (u :: W₁_tail.support).Nodup := hW₁
      have ha_not_tail₁ : u ∉ W₁_tail.support := (List.nodup_cons.mp hnodup₁).1
      have hW₁_tail_simple : W₁_tail.IsSimple := (List.nodup_cons.mp hnodup₁).2
      have hus : u ≠ s := fun h => ha_not_tail₁ (h ▸ W₁_tail.end_mem_support)
      cases W₂ with
      | nil _ => exact (hus rfl).elim
      | @cons _ y₂ _ e₂ hxy₂ W₂_tail =>
        have hnodup₂ : (u :: W₂_tail.support).Nodup := hW₂
        have hW₂_tail_simple : W₂_tail.IsSimple := (List.nodup_cons.mp hnodup₂).2
        have hxy₁G : G.IsLink e₁ u y₁ := hl₁ hxy₁
        have hxy₂G : G.IsLink e₂ u y₂ := hl₂ hxy₂
        have he₁_eq : e = e₁ := by
          rcases List.mem_cons.mp (he₁ e₁ List.mem_cons_self) with rfl | he_t
          · rfl
          · exact (ha_not_tail (W_tail.left_mem_support_of_mem_edges he_t hxy₁G)).elim
        subst he₁_eq
        have hy₁_eq : y = y₁ := by
          rcases hxy.symm.left_eq_or_eq hxy₁G with rfl | rfl
          · exact (hay rfl).elim
          · rfl
        subst hy₁_eq
        have he₂_eq : e = e₂ := by
          rcases List.mem_cons.mp (he₂ e₂ List.mem_cons_self) with rfl | he_t
          · rfl
          · exact (ha_not_tail (W_tail.left_mem_support_of_mem_edges he_t hxy₂G)).elim
        subst he₂_eq
        have hy₂_eq : y = y₂ := by
          rcases hxy.symm.left_eq_or_eq hxy₂G with rfl | rfl
          · exact (hay rfl).elim
          · rfl
        subst hy₂_eq
        have he₁_tail : ∀ f ∈ W₁_tail.edges, f ∈ W_tail.edges := by
          intro f hf
          have hnodup_edges₁ : (e :: W₁_tail.edges).Nodup := hW₁.edges_nodup
          have he_not_tail₁ : e ∉ W₁_tail.edges := (List.nodup_cons.mp hnodup_edges₁).1
          rcases List.mem_cons.mp (he₁ f (List.mem_cons_of_mem e hf)) with rfl | hf_t
          · exact (he_not_tail₁ hf).elim
          · exact hf_t
        have he₂_tail : ∀ f ∈ W₂_tail.edges, f ∈ W_tail.edges := by
          intro f hf
          have hnodup_edges₂ : (e :: W₂_tail.edges).Nodup := hW₂.edges_nodup
          have he_not_tail₂ : e ∉ W₂_tail.edges := (List.nodup_cons.mp hnodup_edges₂).1
          rcases List.mem_cons.mp (he₂ f (List.mem_cons_of_mem e hf)) with rfl | hf_t
          · exact (he_not_tail₂ hf).elim
          · exact hf_t
        obtain ⟨ih_V, ih_E⟩ := ih hW_tail_simple hW₁_tail_simple hW₂_tail_simple he₁_tail he₂_tail
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx_tail
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem u (ih_V x hx_tail)
        · intro f hf
          rcases List.mem_cons.mp hf with rfl | hf_tail
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem e (ih_E f hf_tail)

/-- If `H ≤ Q` and both `H` and `Q` are paths in `G` with the same ends `a, b`, then `H = Q`. -/
theorem IsGraphPathWithEnds.eq_of_le_of_same_ends {G Q H : Graph α β} {a b : α}
    (hQ : IsGraphPathWithEnds G Q a b) (hH : IsGraphPathWithEnds G H a b)
    (hHQ : H ≤ Q) : H = Q := by
  rcases hQ with ⟨hQG, W, hW, hVQ, hEQ⟩
  rcases hH with ⟨hHG, W', hW', hVH, hEH⟩
  have hedges : ∀ e ∈ W'.edges, e ∈ W.edges := by
    intro e he
    have heH : e ∈ E(H) := by rwa [hEH]
    have heQ : e ∈ E(Q) := hHQ.edgeSet_mono heH
    rwa [hEQ] at heQ
  obtain ⟨hV_sub, hE_sub⟩ :=
    walk_support_edges_sub_of_isSimple_left
      (fun _ _ _ hl => hl) (fun _ _ _ hl => hl.mono hHQ)
      hW hW hW' (fun _ h => h) hedges
  refine (Compatible.of_le_le hHG hQG).ext ?_ ?_
  · apply Subset.antisymm hHQ.vertexSet_mono
    intro x hx
    rw [hVQ, mem_ofPred_eq] at hx
    rw [hVH, mem_ofPred_eq]
    exact hV_sub x hx
  · apply Subset.antisymm hHQ.edgeSet_mono
    intro e he
    rw [hEQ, mem_ofPred_eq] at he
    rw [hEH, mem_ofPred_eq]
    exact hE_sub e he

/-- If `Q` is a path in `G` with ends `a, b`, and `H₁, H₂` are subpaths of `Q` with ends `a, s`,
then `H₁ = H₂`. -/
theorem IsGraphPathWithEnds.subpath_unique_of_left {G Q H₁ H₂ : Graph α β} {a b s : α}
    (hQ : IsGraphPathWithEnds G Q a b)
    (hH₁ : IsGraphPathWithEnds Q H₁ a s)
    (hH₂ : IsGraphPathWithEnds Q H₂ a s) : H₁ = H₂ := by
  rcases hQ with ⟨hQG, W, hW, _, hEQ⟩
  rcases hH₁ with ⟨hH₁Q, W₁, hW₁, hVH₁, hEH₁⟩
  rcases hH₂ with ⟨hH₂Q, W₂, hW₂, hVH₂, hEH₂⟩
  have he₁ : ∀ e ∈ W₁.edges, e ∈ W.edges := by
    intro e he
    have heH₁ : e ∈ E(H₁) := by rwa [hEH₁]
    have heQ : e ∈ E(Q) := hH₁Q.edgeSet_mono heH₁
    rwa [hEQ] at heQ
  have he₂ : ∀ e ∈ W₂.edges, e ∈ W.edges := by
    intro e he
    have heH₂ : e ∈ E(H₂) := by rwa [hEH₂]
    have heQ : e ∈ E(Q) := hH₂Q.edgeSet_mono heH₂
    rwa [hEQ] at heQ
  obtain ⟨hV₁₂, hE₁₂⟩ :=
    walk_support_edges_sub_of_isSimple_left
      (fun _ _ _ hl => hl.mono hH₁Q) (fun _ _ _ hl => hl.mono hH₂Q)
      hW hW₁ hW₂ he₁ he₂
  obtain ⟨hV₂₁, hE₂₁⟩ :=
    walk_support_edges_sub_of_isSimple_left
      (fun _ _ _ hl => hl.mono hH₂Q) (fun _ _ _ hl => hl.mono hH₁Q)
      hW hW₂ hW₁ he₂ he₁
  refine (Compatible.of_le_le (hH₁Q.trans hQG) (hH₂Q.trans hQG)).ext ?_ ?_
  · apply Subset.antisymm
    · intro x hx; rw [hVH₁, mem_ofPred_eq] at hx; rw [hVH₂, mem_ofPred_eq]; exact hV₁₂ x hx
    · intro x hx; rw [hVH₂, mem_ofPred_eq] at hx; rw [hVH₁, mem_ofPred_eq]; exact hV₂₁ x hx
  · apply Subset.antisymm
    · intro e he; rw [hEH₁, mem_ofPred_eq] at he; rw [hEH₂, mem_ofPred_eq]; exact hE₁₂ e he
    · intro e he; rw [hEH₂, mem_ofPred_eq] at he; rw [hEH₁, mem_ofPred_eq]; exact hE₂₁ e he

namespace Society

variable (S : Society α β)

/-! ## Dual fence cut and peripheral member bounds for (4.1) -/

/-- Dual of `fence_cut_G₁`: cutting `G₁ = Ω.interval a'_0 b_0` at `x₁ ∈ G₁` so that `x₁ ∈ A_f`:
`A_f := {a_0, x₁} ∪ Ω.interval a_0 x₁` and `B_f := Ω.interval x₁ a_0` satisfy
`A_arc ∪ {x₁} ⊆ A_f` and `B_arc ∪ G₂ ⊆ B_f`. -/
theorem fence_cut_G₁_dual {Ω : CyclicPerm α} {A B W' : Set α}
    (hfence : Ω.IsFence A B) (hW' : W' ⊆ Ω.bar)
    {a_0 a'_0 b_0 b'_0 x₁ : α}
    (ha_0 : a_0 ∈ A ∩ W') (ha'_0 : a'_0 ∈ A ∩ W')
    (hb_0 : b_0 ∈ B ∩ W') (hb'_0 : b'_0 ∈ B ∩ W')
    (hd_ab : Disjoint (Ω.interval a'_0 b_0) W')
    (hd_ba : Disjoint (Ω.interval b'_0 a_0) W')
    (hx₁ : x₁ ∈ Ω.interval a'_0 b_0) :
    let G₁ := Ω.interval a'_0 b_0
    let G₂ := Ω.interval b'_0 a_0
    let A_arc := ({a'_0} ∪ Ω.interval b'_0 a'_0) \ G₂
    let B_arc := ({b'_0} ∪ Ω.interval a'_0 b'_0) \ G₁
    ∃ A_f B_f : Set α, Ω.IsFence A_f B_f ∧
      A_arc ⊆ A_f ∧ x₁ ∈ A_f ∧ B_arc ⊆ B_f ∧ G₂ ⊆ B_f := by
  intro G₁ G₂ A_arc B_arc
  obtain ⟨_, hB_sub, _, hG₁_sub_P₂, hdisj_P, _⟩ :=
    four_arc_partition hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
  have ha_0_bar : a_0 ∈ Ω.bar := hW' ha_0.2
  have hx₁_bar : x₁ ∈ Ω.bar := hx₁.1.1
  have ha'_0_in_a0b0 : a'_0 ∈ {a_0} ∪ Ω.interval a_0 b_0 := by
    by_cases h_eq : a'_0 = a_0
    · exact Or.inl h_eq
    · exact Or.inr (Ω.mem_interval_rotate_left
        (Ω.mem_interval_of_mem_B_of_disjoint_AB hfence.symm hW' hb'_0 ha_0 hd_ba
          hb_0 ha'_0 h_eq).1)
  have hG₁_sub_a0b0 : Ω.interval a'_0 b_0 ⊆ Ω.interval a_0 b_0 := by
    rcases ha'_0_in_a0b0 with h_eq | ha'_in
    · rw [mem_singleton_iff.mp h_eq]
    · exact Ω.interval_subset_interval_right ha'_in
  have hx₁_a0b0 : x₁ ∈ Ω.interval a_0 b_0 := hG₁_sub_a0b0 hx₁
  have ha_0_ne_x₁ : a_0 ≠ x₁ := fun h => Ω.not_mem_interval_left a_0 b_0 (h ▸ hx₁_a0b0)
  have hb_0_in_x₁a0 : b_0 ∈ Ω.interval x₁ a_0 := Ω.mem_interval_rotate_left hx₁_a0b0
  have hQ₂_sub : {b_0} ∪ Ω.interval b_0 a_0 ⊆ Ω.interval x₁ a_0 := by
    rintro z (rfl | hz)
    · exact hb_0_in_x₁a0
    · exact Ω.interval_subset_interval_right hb_0_in_x₁a0 hz
  have hb'_0_in_b0a0 : b'_0 ∈ {b_0} ∪ Ω.interval b_0 a_0 := by
    by_cases h_eq : b'_0 = b_0
    · exact Or.inl h_eq
    · exact Or.inr (Ω.mem_interval_rotate_left
        (Ω.mem_interval_of_mem_B_of_disjoint_AB hfence hW' ha'_0 hb_0 hd_ab
          ha_0 hb'_0 h_eq).1)
  have hG₂_sub_b0a0 : Ω.interval b'_0 a_0 ⊆ Ω.interval b_0 a_0 := by
    rcases hb'_0_in_b0a0 with h_eq | hb'_in
    · rw [mem_singleton_iff.mp h_eq]
    · exact Ω.interval_subset_interval_right hb'_in
  have hB_arc_sub_Q₂ : B_arc ⊆ {b_0} ∪ Ω.interval b_0 a_0 := by
    rintro z ⟨rfl | hz_in, hz_not_G₁⟩
    · exact hb'_0_in_b0a0
    · have hb_0_in_P₂ : b_0 ∈ {b'_0} ∪ Ω.interval a'_0 b'_0 := (hB_sub hb_0).1
      rcases hb_0_in_P₂ with h_eq | hb_0_in
      · rw [← mem_singleton_iff.mp h_eq] at hz_in
        exact (hz_not_G₁ hz_in).elim
      · rw [Ω.interval_eq_union_of_mem hb_0_in] at hz_in
        rcases hz_in with (hz_G₁ | rfl) | hz_b0b'
        · exact (hz_not_G₁ hz_G₁).elim
        · exact Or.inl rfl
        · rcases hb'_0_in_b0a0 with h_eq | hb'_in
          · exact (Ω.not_mem_interval_right a'_0 b'_0 (h_eq ▸ hb_0_in)).elim
          · exact Or.inr (Ω.interval_subset_interval_left hb'_in hz_b0b')
  have hfence_f : Ω.IsFence ({a_0, x₁} ∪ Ω.interval a_0 x₁) (Ω.interval x₁ a_0) :=
    Ω.isFence_interval_compl ha_0_bar hx₁_bar ha_0_ne_x₁
  have hA_arc_sub_Af : A_arc ⊆ {a_0, x₁} ∪ Ω.interval a_0 x₁ := by
    rintro z ⟨hz_P₁, hz_not_G₂⟩
    have hz_bar : z ∈ Ω.bar := by
      rcases hz_P₁ with rfl | hz
      · exact hW' ha'_0.2
      · exact hz.1.1
    have hz_union : z ∈ ({a_0, x₁} ∪ Ω.interval a_0 x₁) ∪ Ω.interval x₁ a_0 :=
      hfence_f.2.2.2.1.symm ▸ hz_bar
    refine hz_union.resolve_right fun hz_Bf => ?_
    rw [Ω.interval_eq_union_of_mem hb_0_in_x₁a0] at hz_Bf
    rcases hz_Bf with (hz_x₁b0 | rfl) | hz_b0a0
    · have hz_G₁ : z ∈ Ω.interval a'_0 b_0 := Ω.interval_subset_interval_right hx₁ hz_x₁b0
      exact disjoint_left.mp hdisj_P hz_P₁ (Or.inr (hG₁_sub_P₂ hz_G₁))
    · exact disjoint_left.mp hdisj_P hz_P₁ (hB_sub hb_0).1
    · rcases hb'_0_in_b0a0 with h_eq | hb'_in
      · rw [← mem_singleton_iff.mp h_eq] at hz_b0a0
        exact hz_not_G₂ hz_b0a0
      · rw [Ω.interval_eq_union_of_mem hb'_in] at hz_b0a0
        rcases hz_b0a0 with (hz_b0b' | rfl) | hz_G₂
        · have hb_0_in_P₂ : b_0 ∈ {b'_0} ∪ Ω.interval a'_0 b'_0 := (hB_sub hb_0).1
          have hb_0_a'b' : b_0 ∈ Ω.interval a'_0 b'_0 :=
            hb_0_in_P₂.resolve_left fun h => Ω.not_mem_interval_left b_0 a_0 (h ▸ hb'_in)
          exact disjoint_left.mp hdisj_P hz_P₁
            (Or.inr (Ω.interval_subset_interval_right hb_0_a'b' hz_b0b'))
        · exact disjoint_left.mp hdisj_P hz_P₁ (Or.inl rfl)
        · exact hz_not_G₂ hz_G₂
  exact ⟨{a_0, x₁} ∪ Ω.interval a_0 x₁, Ω.interval x₁ a_0, hfence_f,
    hA_arc_sub_Af, Or.inl (Or.inr rfl), hB_arc_sub_Q₂.trans hQ₂_sub,
    hG₂_sub_b0a0.trans (subset_union_right.trans hQ₂_sub)⟩

/-- For any `s ∈ G₁ = Ω.interval a'_0 b_0` and any `t ∈ Ω.bar \ G₁`, there is a fence `(A_f, B_f)`
of `Ω` with `A ∩ W' ⊆ A_f`, `B ∩ W' ⊆ B_f`, and one of `s, t` in `A_f` and the other in `B_f`. -/
theorem exists_fence_for_gap_and_other {Ω : CyclicPerm α} {A B W' : Set α}
    (hfence : Ω.IsFence A B) (hW' : W' ⊆ Ω.bar)
    {a_0 a'_0 b_0 b'_0 s t : α}
    (ha_0 : a_0 ∈ A ∩ W') (ha'_0 : a'_0 ∈ A ∩ W')
    (hb_0 : b_0 ∈ B ∩ W') (hb'_0 : b'_0 ∈ B ∩ W')
    (hd_ab : Disjoint (Ω.interval a'_0 b_0) W')
    (hd_ba : Disjoint (Ω.interval b'_0 a_0) W')
    (hs : s ∈ Ω.interval a'_0 b_0)
    (ht_bar : t ∈ Ω.bar) (ht_not_G₁ : t ∉ Ω.interval a'_0 b_0) :
    ∃ A_f B_f : Set α, Ω.IsFence A_f B_f ∧
      A ∩ W' ⊆ A_f ∧ B ∩ W' ⊆ B_f ∧
      ((t ∈ A_f ∧ s ∈ B_f) ∨ (s ∈ A_f ∧ t ∈ B_f)) := by
  obtain ⟨hA_sub, hB_sub, _, _, _, hpart⟩ :=
    four_arc_partition hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
  by_cases ht_G₂ : t ∈ Ω.interval b'_0 a_0
  · obtain ⟨A₁, B₁, hff₁, hA₁, hG₂₁, hB₁, hs₁⟩ :=
      fence_cut_G₁ hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba hs
    exact ⟨A₁, B₁, hff₁, hA_sub.trans hA₁, hB_sub.trans hB₁,
      Or.inl ⟨hG₂₁ ht_G₂, hs₁⟩⟩
  · rcases hpart t ht_bar ht_not_G₁ ht_G₂ with ht_A | ht_B
    · obtain ⟨A₁, B₁, hff₁, hA₁, _, hB₁, hs₁⟩ :=
        fence_cut_G₁ hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba hs
      exact ⟨A₁, B₁, hff₁, hA_sub.trans hA₁, hB_sub.trans hB₁,
        Or.inl ⟨hA₁ ht_A, hs₁⟩⟩
    · obtain ⟨A₂, B₂, hff₂, hA₂, hs₂, hB₂, _⟩ :=
        fence_cut_G₁_dual hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba hs
      exact ⟨A₂, B₂, hff₂, hA_sub.trans hA₂, hB_sub.trans hB₂,
        Or.inr ⟨hs₂, hB₂ ht_B⟩⟩

/-- No transaction can have three distinct peripheral members. -/
theorem IsFenceFor.not_three_peripheral {P_set : Set (Graph α β)} {A B : Set α}
    (hfence : S.IsFenceFor P_set A B)
    {P₁ P₂ P₃ : Graph α β}
    (hper₁ : S.IsPeripheralIn P_set P₁)
    (hper₂ : S.IsPeripheralIn P_set P₂)
    (hper₃ : S.IsPeripheralIn P_set P₃)
    (hne12 : P₁ ≠ P₂) (hne13 : P₁ ≠ P₃) (hne23 : P₂ ≠ P₃) : False := by
  have h₁_in : P₁ ∈ P_set := hper₁.1
  have h₂_in : P₂ ∈ P_set := hper₂.1
  have h₃_in : P₃ ∈ P_set := hper₃.1
  obtain ⟨a₁, ha₁, b₁, hb₁, he₁⟩ := hfence.2.2 P₁ h₁_in
  obtain ⟨a₂, ha₂, b₂, hb₂, he₂⟩ := hfence.2.2 P₂ h₂_in
  obtain ⟨a₃, ha₃, b₃, hb₃, he₃⟩ := hfence.2.2 P₃ h₃_in
  let W := S.transactionEnds P_set
  have hW : W ⊆ S.Ω.bar := S.transactionEnds_subset_bar P_set
  have ha₁W : a₁ ∈ A ∩ W := ⟨ha₁, he₁.mem_transactionEnds_left S h₁_in⟩
  have hb₁W : b₁ ∈ B ∩ W := ⟨hb₁, he₁.mem_transactionEnds_right S h₁_in⟩
  have ha₂W : a₂ ∈ A ∩ W := ⟨ha₂, he₂.mem_transactionEnds_left S h₂_in⟩
  have hb₂W : b₂ ∈ B ∩ W := ⟨hb₂, he₂.mem_transactionEnds_right S h₂_in⟩
  have ha₃W : a₃ ∈ A ∩ W := ⟨ha₃, he₃.mem_transactionEnds_left S h₃_in⟩
  have hb₃W : b₃ ∈ B ∩ W := ⟨hb₃, he₃.mem_transactionEnds_right S h₃_in⟩
  have ha12 : a₁ ≠ a₂ :=
    fun h => disjoint_left.mp (hfence.1.2 h₁_in h₂_in hne12) he₁.1.left_mem (h ▸ he₂.1.left_mem)
  have ha13 : a₁ ≠ a₃ :=
    fun h => disjoint_left.mp (hfence.1.2 h₁_in h₃_in hne13) he₁.1.left_mem (h ▸ he₃.1.left_mem)
  have ha23 : a₂ ≠ a₃ :=
    fun h => disjoint_left.mp (hfence.1.2 h₂_in h₃_in hne23) he₂.1.left_mem (h ▸ he₃.1.left_mem)
  have hb12 : b₁ ≠ b₂ :=
    fun h => disjoint_left.mp (hfence.1.2 h₁_in h₂_in hne12) he₁.1.right_mem (h ▸ he₂.1.right_mem)
  have hb13 : b₁ ≠ b₃ :=
    fun h => disjoint_left.mp (hfence.1.2 h₁_in h₃_in hne13) he₁.1.right_mem (h ▸ he₃.1.right_mem)
  have hb23 : b₂ ≠ b₃ :=
    fun h => disjoint_left.mp (hfence.1.2 h₂_in h₃_in hne23) he₂.1.right_mem (h ▸ he₃.1.right_mem)
  rcases (he₁.isPeripheralIn_iff S h₁_in).mp hper₁ with hd₁ | hd₁ <;>
  rcases (he₂.isPeripheralIn_iff S h₂_in).mp hper₂ with hd₂ | hd₂ <;>
  rcases (he₃.isPeripheralIn_iff S h₃_in).mp hper₃ with hd₃ | hd₃
  · exact ha12 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW ha₁W hb₁W ha₂W hb₂W hd₁ hd₂).1
  · exact ha12 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW ha₁W hb₁W ha₂W hb₂W hd₁ hd₂).1
  · exact ha13 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW ha₁W hb₁W ha₃W hb₃W hd₁ hd₃).1
  · exact hb23 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW hb₂W ha₂W hb₃W ha₃W hd₂
    hd₃).1
  · exact ha23 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW ha₂W hb₂W ha₃W hb₃W hd₂ hd₃).1
  · exact hb13 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW hb₁W ha₁W hb₃W ha₃W hd₁
    hd₃).1
  · exact hb12 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW hb₁W ha₁W hb₂W ha₂W hd₁
    hd₂).1
  · exact hb12 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW hb₁W ha₁W hb₂W ha₂W hd₁
    hd₂).1

/-- If `T₁ ⊆ T₂` and `R ∈ T₁` is peripheral in `T₂`, then `R` is peripheral in `T₁`. -/
theorem IsPeripheralIn.mono_subset {T₁ T₂ : Set (Graph α β)} {R : Graph α β}
    (hsub : T₁ ⊆ T₂) (hR : R ∈ T₁) (hper : S.IsPeripheralIn T₂ R) :
    S.IsPeripheralIn T₁ R := by
  obtain ⟨_, a, b, hR_ends, hd⟩ := hper
  have hW_sub : S.transactionEnds T₁ ⊆ S.transactionEnds T₂ :=
    fun x ⟨P, hP, y, hP_ends⟩ => ⟨P, hsub hP, y, hP_ends⟩
  refine ⟨hR, a, b, hR_ends, ?_⟩
  rcases hd with hd₁ | hd₂
  · exact Or.inl (hd₁.mono_right hW_sub)
  · exact Or.inr (hd₂.mono_right hW_sub)

private theorem peripheral_replacement_of_two_switches
    {P_set : Set (Graph α β)} {P P₁ S_sw S'_sw : Graph α β} {A B : Set α}
    {s₀ a b a₁ b₁ : α}
    (hfence : S.IsFenceFor P_set A B) (hperP : S.IsPeripheralIn P_set P)
    (hP₁_in : P₁ ∈ P_set) (hP₁_ne_P : P₁ ≠ P)
    (haW : a ∈ A ∩ S.transactionEnds P_set) (hbW : b ∈ B ∩ S.transactionEnds P_set)
    (ha₁W : a₁ ∈ A ∩ S.transactionEnds P_set) (hb₁W : b₁ ∈ B ∩ S.transactionEnds P_set)
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set))
    (hs₀_ab : s₀ ∈ S.Ω.interval a b)
    (hP_ends : S.IsOmegaPathWithEnds P a b) (hP₁_ends : S.IsOmegaPathWithEnds P₁ a₁ b₁)
    (hS_ends : S.IsOmegaPathWithEnds S_sw s₀ a₁) (hS'_ends : S.IsOmegaPathWithEnds S'_sw s₀ b₁) :
    let P_set' := (P_set \ {P₁}) ∪ {S_sw}
    let P_set'' := (P_set \ {P₁}) ∪ {S'_sw}
    S.IsTransaction P_set' → S.IsTransaction P_set'' →
    P_set'.ncard = P_set.ncard → P_set''.ncard = P_set.ncard →
    ∃ P_set' : Set (Graph α β), S.IsTransaction P_set' ∧
      P_set.ncard ≤ P_set'.ncard ∧
      ∀ R, S.IsPeripheralIn P_set' R → S.IsPeripheralIn P_set R ∧ R ≠ P := by
  intro P_set' P_set'' htrans' htrans'' hcard' hcard''
  have hP_in := hperP.1
  let W := S.transactionEnds P_set
  have hW_bar : W ⊆ S.Ω.bar := S.transactionEnds_subset_bar P_set
  -- Both `S_sw` and `S'_sw` cross `P`, so neither `P` nor `S_sw` (resp. `S'_sw`) is peripheral.
  have ha₁_ba : a₁ ∈ S.Ω.interval b a := by
    have ha₁_ne_a : a₁ ≠ a :=
      fun h => disjoint_left.mp (hfence.1.2 hP₁_in hP_in hP₁_ne_P) hP₁_ends.1.left_mem
        (h ▸ hP_ends.1.left_mem)
    have ha₁_ne_b : a₁ ≠ b :=
      fun h => disjoint_left.mp hfence.2.1.2.2.1 ha₁W.1 (h ▸ hbW.1)
    exact (S.Ω.mem_interval_or_interval_swap hP_ends.2.2.1 hP_ends.2.2.2 hP₁_ends.2.2.1
      hP_ends.2.1 ha₁_ne_a ha₁_ne_b).resolve_left (disjoint_right.mp hd_ab ha₁W.2)
  have hb₁_ba : b₁ ∈ S.Ω.interval b a := by
    have hb₁_ne_a : b₁ ≠ a :=
      fun h => disjoint_left.mp hfence.2.1.2.2.1 haW.1 (h ▸ hb₁W.1)
    have hb₁_ne_b : b₁ ≠ b :=
      fun h => disjoint_left.mp (hfence.1.2 hP₁_in hP_in hP₁_ne_P) hP₁_ends.1.right_mem
        (h ▸ hP_ends.1.right_mem)
    exact (S.Ω.mem_interval_or_interval_swap hP_ends.2.2.1 hP_ends.2.2.2 hP₁_ends.2.2.2
      hP_ends.2.1 hb₁_ne_a hb₁_ne_b).resolve_left (disjoint_right.mp hd_ab hb₁W.2)
  have hP_in_diff : P ∈ P_set \ {P₁} := ⟨hP_in, Ne.symm hP₁_ne_P⟩
  have hS_not_per' : ¬ S.IsPeripheralIn P_set' S_sw := by
    intro hper
    have hd := (hS_ends.isPeripheralIn_iff S (Or.inr rfl)).mp hper
    have ha_in_ends : a ∈ S.transactionEnds P_set' :=
      hP_ends.mem_transactionEnds_left S (Or.inl hP_in_diff)
    have hb_in_ends : b ∈ S.transactionEnds P_set' :=
      hP_ends.mem_transactionEnds_right S (Or.inl hP_in_diff)
    have hcr_SP : S.Ω.Crosses a b s₀ a₁ :=
      S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hs₀_ab, ha₁_ba⟩)
    rcases S.Ω.crosses_iff_interval.mp hcr_SP.symm with ⟨ha_in, hb_in⟩ | ⟨hb_in, ha_in⟩ <;>
    rcases hd with hd₁ | hd₂
    · exact disjoint_left.mp hd₁ ha_in ha_in_ends
    · exact disjoint_left.mp hd₂ hb_in hb_in_ends
    · exact disjoint_left.mp hd₁ hb_in hb_in_ends
    · exact disjoint_left.mp hd₂ ha_in ha_in_ends
  have hP_not_per' : ¬ S.IsPeripheralIn P_set' P := by
    intro hper
    have hd := (hP_ends.isPeripheralIn_iff S (Or.inl hP_in_diff)).mp hper
    have hs₀_in_ends : s₀ ∈ S.transactionEnds P_set' :=
      hS_ends.mem_transactionEnds_left S (Or.inr rfl)
    have ha₁_in_ends : a₁ ∈ S.transactionEnds P_set' :=
      hS_ends.mem_transactionEnds_right S (Or.inr rfl)
    rcases hd with hd₁ | hd₂
    · exact disjoint_left.mp hd₁ hs₀_ab hs₀_in_ends
    · exact disjoint_left.mp hd₂ ha₁_ba ha₁_in_ends
  have hS'_not_per'' : ¬ S.IsPeripheralIn P_set'' S'_sw := by
    intro hper
    have hd := (hS'_ends.isPeripheralIn_iff S (Or.inr rfl)).mp hper
    have ha_in_ends : a ∈ S.transactionEnds P_set'' :=
      hP_ends.mem_transactionEnds_left S (Or.inl hP_in_diff)
    have hb_in_ends : b ∈ S.transactionEnds P_set'' :=
      hP_ends.mem_transactionEnds_right S (Or.inl hP_in_diff)
    have hcr_S'P : S.Ω.Crosses a b s₀ b₁ :=
      S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hs₀_ab, hb₁_ba⟩)
    rcases S.Ω.crosses_iff_interval.mp hcr_S'P.symm with ⟨ha_in, hb_in⟩ | ⟨hb_in, ha_in⟩ <;>
    rcases hd with hd₁ | hd₂
    · exact disjoint_left.mp hd₁ ha_in ha_in_ends
    · exact disjoint_left.mp hd₂ hb_in hb_in_ends
    · exact disjoint_left.mp hd₁ hb_in hb_in_ends
    · exact disjoint_left.mp hd₂ ha_in ha_in_ends
  have hP_not_per'' : ¬ S.IsPeripheralIn P_set'' P := by
    intro hper
    have hd := (hP_ends.isPeripheralIn_iff S (Or.inl hP_in_diff)).mp hper
    have hs₀_in_ends : s₀ ∈ S.transactionEnds P_set'' :=
      hS'_ends.mem_transactionEnds_left S (Or.inr rfl)
    have hb₁_in_ends : b₁ ∈ S.transactionEnds P_set'' :=
      hS'_ends.mem_transactionEnds_right S (Or.inr rfl)
    rcases hd with hd₁ | hd₂
    · exact disjoint_left.mp hd₁ hs₀_ab hs₀_in_ends
    · exact disjoint_left.mp hd₂ hb₁_ba hb₁_in_ends
  -- Show that either `P_set'` or `P_set''` satisfies the requirement.
  by_cases hgood' : ∀ R, S.IsPeripheralIn P_set' R → S.IsPeripheralIn P_set R ∧ R ≠ P
  · exact ⟨P_set', htrans', hcard'.symm.le, hgood'⟩
  · refine ⟨P_set'', htrans'', hcard''.symm.le, ?_⟩
    by_contra! hbad''
    rcases not_forall.mp hgood' with ⟨P', hP'_bad⟩
    rw [not_imp, not_and_or] at hP'_bad
    rcases hP'_bad with ⟨hP'_per', hP'_not_per | hP'_eq_P⟩
    · rcases hbad'' with ⟨P'', hP''_per'', hP''_not⟩
      have hP''_not_per : ¬ S.IsPeripheralIn P_set P'' :=
        fun h => hP_not_per'' (hP''_not h ▸ hP''_per'')
      have hP'_in_diff : P' ∈ P_set \ {P₁} :=
        hP'_per'.1.resolve_right fun h => hS_not_per' (mem_singleton_iff.mp h ▸ hP'_per')
      have hP''_in_diff : P'' ∈ P_set \ {P₁} :=
        hP''_per''.1.resolve_right fun h => hS'_not_per'' (mem_singleton_iff.mp h ▸ hP''_per'')
      have hP'_ne_P : P' ≠ P := fun h => hP_not_per' (h ▸ hP'_per')
      have hP''_ne_P : P'' ≠ P := fun h => hP_not_per'' (h ▸ hP''_per'')
      have hP'_per_diff : S.IsPeripheralIn (P_set \ {P₁}) P' :=
        hP'_per'.mono_subset S subset_union_left hP'_in_diff
      have hP''_per_diff : S.IsPeripheralIn (P_set \ {P₁}) P'' :=
        hP''_per''.mono_subset S subset_union_left hP''_in_diff
      have hP_per_diff : S.IsPeripheralIn (P_set \ {P₁}) P :=
        hperP.mono_subset S sdiff_subset hP_in_diff
      -- If `P' = P''`, then `P'` is peripheral in both `P_set'` and `P_set''`, hence in `P_set`.
      have hP'_ne_P'' : P' ≠ P'' := by
        rintro rfl
        apply hP'_not_per
        obtain ⟨a', ha'A, b', hb'B, hP'_ends⟩ := hfence.2.2 P' hP'_in_diff.1
        have ha'W : a' ∈ A ∩ W := ⟨ha'A, hP'_ends.mem_transactionEnds_left S hP'_in_diff.1⟩
        have hb'W : b' ∈ B ∩ W := ⟨hb'B, hP'_ends.mem_transactionEnds_right S hP'_in_diff.1⟩
        have hsub_ab : S.Ω.interval a b ⊆ S.Ω.interval a' b' :=
          S.Ω.interval_subset_of_disjoint_AB hfence.2.1 hW_bar haW hbW hd_ab ha'W hb'W
        have hs₀_a'b' : s₀ ∈ S.Ω.interval a' b' := hsub_ab hs₀_ab
        have hd' := (hP'_ends.isPeripheralIn_iff S (Or.inl hP'_in_diff)).mp hP'_per'
        have hd'' := (hP'_ends.isPeripheralIn_iff S (Or.inl hP'_in_diff)).mp hP''_per''
        have hs₀_ends' : s₀ ∈ S.transactionEnds P_set' :=
          hS_ends.mem_transactionEnds_left S (Or.inr rfl)
        have ha₁_ends' : a₁ ∈ S.transactionEnds P_set' :=
          hS_ends.mem_transactionEnds_right S (Or.inr rfl)
        have hs₀_ends'' : s₀ ∈ S.transactionEnds P_set'' :=
          hS'_ends.mem_transactionEnds_left S (Or.inr rfl)
        have hb₁_ends'' : b₁ ∈ S.transactionEnds P_set'' :=
          hS'_ends.mem_transactionEnds_right S (Or.inr rfl)
        have hd'_ba : Disjoint (S.Ω.interval b' a') (S.transactionEnds P_set') :=
          hd'.resolve_left fun hd_l => disjoint_left.mp hd_l hs₀_a'b' hs₀_ends'
        have hd''_ba : Disjoint (S.Ω.interval b' a') (S.transactionEnds P_set'') :=
          hd''.resolve_left fun hd_l => disjoint_left.mp hd_l hs₀_a'b' hs₀_ends''
        refine (hP'_ends.isPeripheralIn_iff S hP'_in_diff.1).mpr (Or.inr ?_)
        rw [hfence.transactionEnds_eq_union S hP₁_in hP₁_ends, disjoint_union_right]
        refine ⟨hd'_ba.mono_right ?_, ?_⟩
        · rintro z ⟨R, hR, y, hRe⟩
          exact ⟨R, Or.inl hR, y, hRe⟩
        · rw [disjoint_left]
          rintro z hz (rfl | rfl)
          · exact disjoint_left.mp hd'_ba hz ha₁_ends'
          · exact disjoint_left.mp hd''_ba hz hb₁_ends''
      have hfence_diff : S.IsFenceFor (P_set \ {P₁}) A B :=
        ⟨⟨fun R hR => hfence.1.1 R hR.1, fun R₁ hR₁ R₂ hR₂ hne => hfence.1.2 hR₁.1 hR₂.1 hne⟩,
          hfence.2.1, fun R hR => hfence.2.2 R hR.1⟩
      exact hfence_diff.not_three_peripheral S hP_per_diff hP'_per_diff hP''_per_diff
        hP'_ne_P.symm hP''_ne_P.symm hP'_ne_P''
    · exact hP_not_per' (not_not.mp hP'_eq_P ▸ hP'_per')

private theorem peripheral_replacement_of_disjoint_cross
    {P_set : Set (Graph α β)} {P Q₀ : Graph α β} {A B : Set α}
    {a b a_0 b'_0 x s₀ : α}
    (hfence : S.IsFenceFor P_set A B) (hP_in : P ∈ P_set)
    (haW : a ∈ A ∩ S.transactionEnds P_set) (hbW : b ∈ B ∩ S.transactionEnds P_set)
    (ha_0 : a_0 ∈ A ∩ S.transactionEnds P_set)
    (hb'_0 : b'_0 ∈ B ∩ S.transactionEnds P_set)
    (hd_ab : Disjoint (S.Ω.interval a b) (S.transactionEnds P_set))
    (hd_ba : Disjoint (S.Ω.interval b'_0 a_0) (S.transactionEnds P_set))
    (hP_ends : S.IsOmegaPathWithEnds P a b)
    (hQ₀_ft : IsFromToPathWithEnds S.G Q₀
      (V(S.transactionUnion P_set) ∪ S.Ω.interval b a) (S.Ω.interval a b) x s₀)
    (hx_ba : x ∈ S.Ω.interval b a) (hx_U : x ∉ V(S.transactionUnion P_set))
    (hs₀_ab : s₀ ∈ S.Ω.interval a b) :
    ∃ P_set' : Set (Graph α β), S.IsTransaction P_set' ∧
      P_set.ncard ≤ P_set'.ncard ∧
      ∀ R, S.IsPeripheralIn P_set' R → S.IsPeripheralIn P_set R ∧ R ≠ P := by
  let W := S.transactionEnds P_set
  have hW_bar : W ⊆ S.Ω.bar := S.transactionEnds_subset_bar P_set
  have hfin_P : P_set.Finite := hfence.1.finite S
  have hs₀_bar : s₀ ∈ S.Ω.bar := hs₀_ab.1.1
  have hdisj_Q₀_U : Disjoint V(Q₀) V(S.transactionUnion P_set) := by
    rw [disjoint_left]
    intro z hzQ₀ hzU
    have hz_x : z = x := by
      have hz_in : z ∈ V(Q₀) ∩ (V(S.transactionUnion P_set) ∪ S.Ω.interval b a) :=
        ⟨hzQ₀, Or.inl hzU⟩
      rwa [hQ₀_ft.2.1, mem_singleton_iff] at hz_in
    exact hx_U (hz_x ▸ hzU)
  have hx_bar : x ∈ S.Ω.bar := hx_ba.1.1
  have hxs₀ : x ≠ s₀ :=
    fun h => disjoint_left.mp (S.Ω.disjoint_interval_swap a b) hs₀_ab (h ▸ hx_ba)
  have hx_not_ab : x ∉ S.Ω.interval a b :=
    disjoint_right.mp (S.Ω.disjoint_interval_swap a b) hx_ba
  have hQ₀_ends : S.IsOmegaPathWithEnds Q₀ x s₀ :=
    ⟨hQ₀_ft.1, hxs₀, hx_bar, hs₀_bar⟩
  let P_set' := P_set ∪ {Q₀}
  obtain ⟨A_f, B_f, hff, hAf, hBf, h_xs₀⟩ :=
    exists_fence_for_gap_and_other hfence.2.1 hW_bar ha_0 haW hbW hb'_0 hd_ab hd_ba
      hs₀_ab hx_bar hx_not_ab
  have hdisj_Q₀_R : ∀ R ∈ P_set, Disjoint V(Q₀) V(R) := by
    intro R hR
    exact hdisj_Q₀_U.mono_right fun z hz => mem_iUnion₂.mpr ⟨R, hR, hz⟩
  have htrans' : S.IsTransaction P_set' := by
    refine ⟨A_f, B_f, ⟨⟨?_, ?_⟩, hff, ?_⟩⟩
    · rintro R (hR | rfl)
      · exact hfence.1.1 R hR
      · exact ⟨x, s₀, hQ₀_ends⟩
    · rintro M₁ (hM₁ | rfl) M₂ (hM₂ | rfl) hne
      · exact hfence.1.2 hM₁ hM₂ hne
      · exact (hdisj_Q₀_R M₁ hM₁).symm
      · exact hdisj_Q₀_R M₂ hM₂
      · exact (hne rfl).elim
    · rintro R (hR | rfl)
      · obtain ⟨aR, haR, bR, hbR, hR_e⟩ := hfence.2.2 R hR
        exact ⟨aR, hAf ⟨haR, hR_e.mem_transactionEnds_left S hR⟩,
          bR, hBf ⟨hbR, hR_e.mem_transactionEnds_right S hR⟩, hR_e⟩
      · rcases h_xs₀ with ⟨hxA, hs₀B⟩ | ⟨hs₀A, hxB⟩
        · exact ⟨x, hxA, s₀, hs₀B, hQ₀_ends⟩
        · exact ⟨s₀, hs₀A, x, hxB, hQ₀_ends.symm S⟩
  have hQ₀_not_P : Q₀ ∉ P_set := fun h_in =>
    disjoint_left.mp (hdisj_Q₀_R Q₀ h_in) hQ₀_ft.1.left_mem hQ₀_ft.1.left_mem
  have hcard' : P_set.ncard ≤ P_set'.ncard := by
    have hset_eq : P_set' = insert Q₀ P_set := by ext R; simp [P_set']
    rw [hset_eq, ncard_insert_of_notMem hQ₀_not_P hfin_P]
    exact Nat.le_succ _
  have hQ₀_not_per' : ¬ S.IsPeripheralIn P_set' Q₀ := by
    intro hper
    have hd := (hQ₀_ends.isPeripheralIn_iff S (Or.inr rfl)).mp hper
    have ha_in_ends : a ∈ S.transactionEnds P_set' :=
      hP_ends.mem_transactionEnds_left S (Or.inl hP_in)
    have hb_in_ends : b ∈ S.transactionEnds P_set' :=
      hP_ends.mem_transactionEnds_right S (Or.inl hP_in)
    have hcr_Q₀P : S.Ω.Crosses a b s₀ x :=
      S.Ω.crosses_iff_interval.mpr (Or.inl ⟨hs₀_ab, hx_ba⟩)
    rcases S.Ω.crosses_iff_interval.mp hcr_Q₀P.symm.swap_left with ⟨ha_in, hb_in⟩ | ⟨hb_in, ha_in⟩
      <;>
    rcases hd with hd₁ | hd₂
    · exact disjoint_left.mp hd₁ ha_in ha_in_ends
    · exact disjoint_left.mp hd₂ hb_in hb_in_ends
    · exact disjoint_left.mp hd₁ hb_in hb_in_ends
    · exact disjoint_left.mp hd₂ ha_in ha_in_ends
  have hP_not_per' : ¬ S.IsPeripheralIn P_set' P := by
    intro hper
    have hd := (hP_ends.isPeripheralIn_iff S (Or.inl hP_in)).mp hper
    have hx_in_ends : x ∈ S.transactionEnds P_set' :=
      hQ₀_ends.mem_transactionEnds_left S (Or.inr rfl)
    have hs₀_in_ends : s₀ ∈ S.transactionEnds P_set' :=
      hQ₀_ends.mem_transactionEnds_right S (Or.inr rfl)
    rcases hd with hd₁ | hd₂
    · exact disjoint_left.mp hd₁ hs₀_ab hs₀_in_ends
    · exact disjoint_left.mp hd₂ hx_ba hx_in_ends
  refine ⟨P_set', htrans', hcard', fun R hR_per' => ?_⟩
  have hR_in_P : R ∈ P_set :=
    hR_per'.1.resolve_right fun h => hQ₀_not_per' (mem_singleton_iff.mp h ▸ hR_per')
  exact ⟨hR_per'.mono_subset S subset_union_left hR_in_P,
    fun h_eq => hP_not_per' (h_eq ▸ hR_per')⟩

/-- Single step in the proof of (4.1): if `P_set` is a transaction in which `P ∈ P_set` is
peripheral and non-separating, then there is a transaction `P_set_next` with
`P_set_next.ncard ≥ P_set.ncard` whose peripheral members are all peripheral in `P_set` and
different from `P`. -/
private theorem theorem_4_1_step {P_set : Set (Graph α β)}
    (htrans : S.IsTransaction P_set)
    {P : Graph α β} (hperP : S.IsPeripheralIn P_set P)
    (hnonsepP : S.IsNonSeparatingOmegaPath P) :
    ∃ P_set' : Set (Graph α β), S.IsTransaction P_set' ∧
      P_set.ncard ≤ P_set'.ncard ∧
      ∀ R, S.IsPeripheralIn P_set' R → S.IsPeripheralIn P_set R ∧ R ≠ P := by
  have hP_in : P ∈ P_set := hperP.1
  obtain ⟨A₀, B₀, hfence₀⟩ := htrans
  obtain ⟨a₀_raw, ha₀_raw, b₀_raw, hb₀_raw, hP_ends_raw⟩ := hfence₀.2.2 P hP_in
  -- Ensure `Disjoint (S.Ω.interval a b) W` by swapping `(A₀, B₀)` if needed.
  have hex_fence : ∃ A B : Set α, S.IsFenceFor P_set A B ∧
      ∃ a ∈ A, ∃ b ∈ B, S.IsOmegaPathWithEnds P a b ∧
        Disjoint (S.Ω.interval a b) (S.transactionEnds P_set) := by
    rcases (hP_ends_raw.isPeripheralIn_iff S hP_in).mp hperP with hd | hd
    · exact ⟨A₀, B₀, hfence₀, a₀_raw, ha₀_raw, b₀_raw, hb₀_raw, hP_ends_raw, hd⟩
    · refine ⟨B₀, A₀, ⟨hfence₀.1, hfence₀.2.1.symm, fun R hR => ?_⟩,
        b₀_raw, hb₀_raw, a₀_raw, ha₀_raw, hP_ends_raw.symm S, hd⟩
      obtain ⟨x, hx, y, hy, hxy⟩ := hfence₀.2.2 R hR
      exact ⟨y, hy, x, hx, hxy.symm S⟩
  obtain ⟨A, B, hfence, a, haA, b, hbB, hP_ends, hd_ab⟩ := hex_fence
  let W := S.transactionEnds P_set
  have hW_bar : W ⊆ S.Ω.bar := S.transactionEnds_subset_bar P_set
  have haW : a ∈ A ∩ W := ⟨haA, hP_ends.mem_transactionEnds_left S hP_in⟩
  have hbW : b ∈ B ∩ W := ⟨hbB, hP_ends.mem_transactionEnds_right S hP_in⟩
  -- Find the other empty-interval boundary pair `(b'_0, a_0)` of `(B, A)` with respect to `W`.
  have hW_sub_BA : W ⊆ B ∪ A := by
    rw [union_comm, hfence.2.1.2.2.2.1]
    exact hW_bar
  obtain ⟨b'_0, hb'_0, a_0, ha_0, hd_ba⟩ :=
    S.Ω.exists_empty_interval_AB_of_subset_union hW_bar hW_sub_BA
      ⟨b, hbW⟩ ⟨a, haW⟩
  -- Since `P` is non-separating, there is an `Ω`-path `Q` crossing `P`.
  obtain ⟨_, Q_raw, hcross_QP⟩ := hnonsepP
  rcases hcross_QP with ⟨hdisj_QP, s_raw, t_raw, a', b', hQ_raw_ends, hP_ends', hcr_raw⟩
  have hcr : S.Ω.Crosses s_raw t_raw a b := by
    rcases hP_ends.ends_eq S hP_ends' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcr_raw
    · exact (hcr_raw.symm.swap_left).symm
  -- Order the ends of `Q_raw` as `(s, t)` with `s ∈ S.Ω.interval a b` and `t ∈ S.Ω.interval b a`.
  have hex_Q : ∃ s t : α, S.IsOmegaPathWithEnds Q_raw s t ∧
      s ∈ S.Ω.interval a b ∧ t ∈ S.Ω.interval b a := by
    rcases S.Ω.crosses_iff_interval.mp (hcr.symm) with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact ⟨s_raw, t_raw, hQ_raw_ends, hs, ht⟩
    · exact ⟨t_raw, s_raw, hQ_raw_ends.symm S, hs, ht⟩
  obtain ⟨s, t, hQ_ends, hs_ab, ht_ba⟩ := hex_Q
  -- Extract a minimal `(V(⋃ P_set) ∪ S.Ω.interval b a) → S.Ω.interval a b` subpath `Q₀ ≤ Q_raw`.
  obtain ⟨x, hx_X, s₀, hs₀_ab, Q₀, hQ₀_le, hQ₀_ft⟩ :=
    hQ_ends.1.symm.exists_isFromToPathWithEnds
      (X := V(S.transactionUnion P_set) ∪ S.Ω.interval b a)
      (Y := S.Ω.interval a b)
      (Or.inr ht_ba) hs_ab
  have hdisj_Q₀P : Disjoint V(Q₀) V(P) := hdisj_QP.mono_left hQ₀_le.vertexSet_mono
  have hs₀_bar : s₀ ∈ S.Ω.bar := hs₀_ab.1.1
  have hs₀_not_W : s₀ ∉ W := disjoint_left.mp hd_ab hs₀_ab
  have hfin_P : P_set.Finite := hfence.1.finite S
  by_cases hx_U : x ∈ V(S.transactionUnion P_set)
  · -- Case 2: `x ∈ V(S.transactionUnion P_set)`.
    change x ∈ ⋃ R ∈ P_set, V(R) at hx_U
    obtain ⟨P₁, hP₁_in, hx_P₁⟩ := mem_iUnion₂.mp hx_U
    have hP₁_ne_P : P₁ ≠ P := fun h_eq => disjoint_left.mp hdisj_Q₀P hQ₀_ft.1.left_mem
      (h_eq ▸ hx_P₁)
    obtain ⟨a₁, ha₁A, b₁, hb₁B, hP₁_ends⟩ := hfence.2.2 P₁ hP₁_in
    have ha₁W : a₁ ∈ A ∩ W := ⟨ha₁A, hP₁_ends.mem_transactionEnds_left S hP₁_in⟩
    have hb₁W : b₁ ∈ B ∩ W := ⟨hb₁B, hP₁_ends.mem_transactionEnds_right S hP₁_in⟩
    -- Split `P₁` at `x ∈ V(P₁)` into `R₁` (from `x` to `a₁`) and `R₂` (from `x` to `b₁`).
    obtain ⟨R₁_rev, R₂, hR₁P₁, hR₂P₁, hR₁_rev, hR₂, _, _, _⟩ := hP₁_ends.1.exists_split_at hx_P₁
    have hR₁ : IsGraphPathWithEnds P₁ R₁_rev x a₁ := hR₁_rev.symm
    let S_sw := subgraphUnion S.G Q₀ R₁_rev
    let S'_sw := subgraphUnion S.G Q₀ R₂
    let P_set' := (P_set \ {P₁}) ∪ {S_sw}
    let P_set'' := (P_set \ {P₁}) ∪ {S'_sw}
    have hinter_U : V(Q₀) ∩ V(S.transactionUnion P_set) = {x} := by
      apply Subset.antisymm
      · intro z ⟨hzQ₀, hzU⟩
        have hz_X : z ∈ V(Q₀) ∩ (V(S.transactionUnion P_set) ∪ S.Ω.interval b a) :=
          ⟨hzQ₀, Or.inl hzU⟩
        rwa [hQ₀_ft.2.1] at hz_X
      · rintro z rfl
        exact ⟨hQ₀_ft.1.left_mem, mem_iUnion₂.mpr ⟨P₁, hP₁_in, hx_P₁⟩⟩
    have hinter_P₁ : V(Q₀) ∩ V(P₁) = {x} := by
      apply Subset.antisymm
      · intro z ⟨hzQ₀, hzP₁⟩
        have hzU : z ∈ V(Q₀) ∩ V(S.transactionUnion P_set) :=
          ⟨hzQ₀, mem_iUnion₂.mpr ⟨P₁, hP₁_in, hzP₁⟩⟩
        rwa [hinter_U] at hzU
      · rintro z rfl
        exact ⟨hQ₀_ft.1.left_mem, hx_P₁⟩
    have hdisj_Q₀_other : ∀ R ∈ P_set \ {P₁}, Disjoint V(Q₀) V(R) := by
      intro R ⟨hR_in, hR_ne⟩
      rw [disjoint_left]
      intro z hzQ₀ hzR
      have hz_x : z = x := by
        have hzU : z ∈ V(Q₀) ∩ V(S.transactionUnion P_set) :=
          ⟨hzQ₀, mem_iUnion₂.mpr ⟨R, hR_in, hzR⟩⟩
        rwa [hinter_U, mem_singleton_iff] at hzU
      subst hz_x
      exact disjoint_left.mp (hfence.1.2 hP₁_in hR_in (Ne.symm hR_ne)) hx_P₁ hzR
    have hS_ends : S.IsOmegaPathWithEnds S_sw s₀ a₁ := by
      have hinter_R₁ : V(Q₀) ∩ V(R₁_rev) = {x} := by
        apply Subset.antisymm
        · intro z ⟨hzQ₀, hzR₁⟩
          have hz_in : z ∈ V(Q₀) ∩ V(P₁) := ⟨hzQ₀, hR₁P₁.vertexSet_mono hzR₁⟩
          rwa [hinter_P₁] at hz_in
        · rintro z rfl
          exact ⟨hQ₀_ft.1.left_mem, hR₁.left_mem⟩
      refine ⟨hQ₀_ft.1.symm.subgraphUnion (hR₁.mono hP₁_ends.1.le) hinter_R₁,
        fun h => hs₀_not_W (h ▸ ha₁W.2), hs₀_bar, hP₁_ends.2.2.1⟩
    have hS'_ends : S.IsOmegaPathWithEnds S'_sw s₀ b₁ := by
      have hinter_R₂ : V(Q₀) ∩ V(R₂) = {x} := by
        apply Subset.antisymm
        · intro z ⟨hzQ₀, hzR₂⟩
          have hz_in : z ∈ V(Q₀) ∩ V(P₁) := ⟨hzQ₀, hR₂P₁.vertexSet_mono hzR₂⟩
          rwa [hinter_P₁] at hz_in
        · rintro z rfl
          exact ⟨hQ₀_ft.1.left_mem, hR₂.left_mem⟩
      refine ⟨hQ₀_ft.1.symm.subgraphUnion (hR₂.mono hP₁_ends.1.le) hinter_R₂,
        fun h => hs₀_not_W (h ▸ hb₁W.2), hs₀_bar, hP₁_ends.2.2.2⟩
    have hdisj_S_other : ∀ R ∈ P_set \ {P₁}, Disjoint V(S_sw) V(R) := by
      intro R hR
      rw [vertexSet_subgraphUnion, disjoint_union_left]
      exact ⟨hdisj_Q₀_other R hR,
        (hfence.1.2 hP₁_in hR.1 (Ne.symm hR.2)).mono_left hR₁P₁.vertexSet_mono⟩
    have hdisj_S'_other : ∀ R ∈ P_set \ {P₁}, Disjoint V(S'_sw) V(R) := by
      intro R hR
      rw [vertexSet_subgraphUnion, disjoint_union_left]
      exact ⟨hdisj_Q₀_other R hR,
        (hfence.1.2 hP₁_in hR.1 (Ne.symm hR.2)).mono_left hR₂P₁.vertexSet_mono⟩
    -- Prove `P_set'` and `P_set''` are transactions with cardinality `P_set.ncard`.
    obtain ⟨hA_sub, hB_sub, _, _, _, _⟩ :=
      four_arc_partition hfence.2.1 hW_bar ha_0 haW hbW hb'_0 hd_ab hd_ba
    obtain ⟨A₁, B₁, hff₁, hA₁, _, hB₁, hs₁⟩ :=
      fence_cut_G₁ hfence.2.1 hW_bar ha_0 haW hbW hb'_0 hd_ab hd_ba hs₀_ab
    obtain ⟨A₂, B₂, hff₂, hA₂, hs₂, hB₂, _⟩ :=
      fence_cut_G₁_dual hfence.2.1 hW_bar ha_0 haW hbW hb'_0 hd_ab hd_ba hs₀_ab
    have htrans' : S.IsTransaction P_set' := by
      refine ⟨A₁, B₁, ⟨⟨?_, ?_⟩, hff₁, ?_⟩⟩
      · rintro R (hR | rfl)
        · exact hfence.1.1 R hR.1
        · exact ⟨s₀, a₁, hS_ends⟩
      · rintro M₁ (hM₁ | rfl) M₂ (hM₂ | rfl) hne
        · exact hfence.1.2 hM₁.1 hM₂.1 hne
        · exact (hdisj_S_other M₁ hM₁).symm
        · exact hdisj_S_other M₂ hM₂
        · exact (hne rfl).elim
      · rintro R (hR | rfl)
        · obtain ⟨aR, haR, bR, hbR, hR_e⟩ := hfence.2.2 R hR.1
          exact ⟨aR, hA₁ (hA_sub ⟨haR, hR_e.mem_transactionEnds_left S hR.1⟩),
            bR, hB₁ (hB_sub ⟨hbR, hR_e.mem_transactionEnds_right S hR.1⟩), hR_e⟩
        · exact ⟨a₁, hA₁ (hA_sub ha₁W), s₀, hs₁, hS_ends.symm S⟩
    have htrans'' : S.IsTransaction P_set'' := by
      refine ⟨A₂, B₂, ⟨⟨?_, ?_⟩, hff₂, ?_⟩⟩
      · rintro R (hR | rfl)
        · exact hfence.1.1 R hR.1
        · exact ⟨s₀, b₁, hS'_ends⟩
      · rintro M₁ (hM₁ | rfl) M₂ (hM₂ | rfl) hne
        · exact hfence.1.2 hM₁.1 hM₂.1 hne
        · exact (hdisj_S'_other M₁ hM₁).symm
        · exact hdisj_S'_other M₂ hM₂
        · exact (hne rfl).elim
      · rintro R (hR | rfl)
        · obtain ⟨aR, haR, bR, hbR, hR_e⟩ := hfence.2.2 R hR.1
          exact ⟨aR, hA₂ (hA_sub ⟨haR, hR_e.mem_transactionEnds_left S hR.1⟩),
            bR, hB₂ (hB_sub ⟨hbR, hR_e.mem_transactionEnds_right S hR.1⟩), hR_e⟩
        · exact ⟨s₀, hs₂, b₁, hB₂ (hB_sub hb₁W), hS'_ends⟩
    have hS_not_diff : S_sw ∉ P_set \ {P₁} := fun h_in =>
      disjoint_left.mp (hdisj_S_other S_sw h_in) (Or.inl hQ₀_ft.1.left_mem)
        (Or.inl hQ₀_ft.1.left_mem)
    have hS'_not_diff : S'_sw ∉ P_set \ {P₁} := fun h_in =>
      disjoint_left.mp (hdisj_S'_other S'_sw h_in) (Or.inl hQ₀_ft.1.left_mem)
        (Or.inl hQ₀_ft.1.left_mem)
    have hcard' : P_set'.ncard = P_set.ncard := by
      have hset_eq : P_set' = insert S_sw (P_set \ {P₁}) := by ext R; simp [P_set', or_comm]
      rw [hset_eq, ncard_insert_of_notMem hS_not_diff hfin_P.sdiff,
        ncard_sdiff_singleton_add_one hP₁_in hfin_P]
    have hcard'' : P_set''.ncard = P_set.ncard := by
      have hset_eq : P_set'' = insert S'_sw (P_set \ {P₁}) := by ext R; simp [P_set'', or_comm]
      rw [hset_eq, ncard_insert_of_notMem hS'_not_diff hfin_P.sdiff,
        ncard_sdiff_singleton_add_one hP₁_in hfin_P]
    exact peripheral_replacement_of_two_switches S hfence hperP hP₁_in hP₁_ne_P
      haW hbW ha₁W hb₁W hd_ab hs₀_ab hP_ends hP₁_ends hS_ends hS'_ends
      htrans' htrans'' hcard' hcard''
  · exact peripheral_replacement_of_disjoint_cross S hfence hP_in haW hbW ha_0 hb'_0 hd_ab hd_ba
      hP_ends hQ₀_ft (hx_X.resolve_left hx_U) hx_U hs₀_ab

/-- Two crossing `Ω`-paths form a crooked transaction of cardinality 2. -/
theorem OmegaPathsCross.isCrookedTransaction_pair {P₁ P₂ : Graph α β}
    (hcross : S.OmegaPathsCross P₁ P₂) :
    S.IsCrookedTransaction {P₁, P₂} ∧ ({P₁, P₂} : Set (Graph α β)).ncard = 2 := by
  rcases hcross with ⟨hdisj, s₁, t₁, s₂, t₂, h₁, h₂, hcr⟩
  have h12 : P₁ ≠ P₂ := fun h => disjoint_left.mp hdisj h₁.1.left_mem (h ▸ h₁.1.left_mem)
  have hex₁ : ∃ s₁' t₁' : α, S.IsOmegaPathWithEnds P₁ s₁' t₁' ∧
      s₁' ∈ S.Ω.interval s₂ t₂ ∧ t₁' ∈ S.Ω.interval t₂ s₂ := by
    rcases S.Ω.crosses_iff_interval.mp hcr.symm with ⟨hs₁, ht₁⟩ | ⟨hs₁, ht₁⟩
    · exact ⟨s₁, t₁, h₁, hs₁, ht₁⟩
    · exact ⟨t₁, s₁, h₁.symm S, hs₁, ht₁⟩
  obtain ⟨s₁', t₁', h₁', hs₁', ht₁'⟩ := hex₁
  have hs₂_ne_s₁' : s₂ ≠ s₁' := fun h => S.Ω.not_mem_interval_left s₂ t₂ (h ▸ hs₁')
  have hfence : S.Ω.IsFence ({s₂, s₁'} ∪ S.Ω.interval s₂ s₁') (S.Ω.interval s₁' s₂) :=
    S.Ω.isFence_interval_compl h₂.2.2.1 h₁'.2.2.1 hs₂_ne_s₁'
  have ht₂_in : t₂ ∈ S.Ω.interval s₁' s₂ := S.Ω.mem_interval_rotate_left hs₁'
  have ht₁'_in : t₁' ∈ S.Ω.interval s₁' s₂ :=
    S.Ω.interval_subset_interval_right ht₂_in ht₁'
  refine ⟨⟨⟨{s₂, s₁'} ∪ S.Ω.interval s₂ s₁', S.Ω.interval s₁' s₂, ⟨?_, ?_⟩, hfence, ?_⟩, ?_⟩,
    ncard_pair h12⟩
  · rintro R (rfl | rfl)
    · exact ⟨s₁', t₁', h₁'⟩
    · exact ⟨s₂, t₂, h₂⟩
  · rintro R₁ (rfl | rfl) R₂ (rfl | rfl) hne
    · exact (hne rfl).elim
    · exact hdisj
    · exact hdisj.symm
    · exact (hne rfl).elim
  · rintro R (rfl | rfl)
    · exact ⟨s₁', Or.inl (Or.inr rfl), t₁', ht₁'_in, h₁'⟩
    · exact ⟨s₂, Or.inl (Or.inl rfl), t₂, ht₂_in, h₂⟩
  · rintro R (rfl | rfl) hper
    · exact S.not_omegaPathsCross_of_isPeripheralIn hper (Or.inr rfl)
        ⟨hdisj.symm, s₂, t₂, s₁, t₁, h₂, h₁, hcr.symm⟩
    · exact S.not_omegaPathsCross_of_isPeripheralIn hper (Or.inl rfl)
        ⟨hdisj, s₁, t₁, s₂, t₂, h₁, h₂, hcr⟩

/-- **Graph Minors IX, (4.1)** (page 49):
"Let $\mathscr{P}$ be a transaction in $(G, \Omega)$, such that every peripheral member is
non-separating. Then there is a crooked transaction $\mathscr{P}'$ in $(G, \Omega)$ with
$|\mathscr{P}'| \ge |\mathscr{P}|$." -/
theorem theorem_4_1_proof {P_set : Set (Graph α β)}
    (htrans : S.IsTransaction P_set)
    (hnonsep : ∀ P ∈ P_set, S.IsPeripheralIn P_set P → S.IsNonSeparatingOmegaPath P) :
    ∃ P_set' : Set (Graph α β), S.IsCrookedTransaction P_set' ∧ P_set.ncard ≤ P_set'.ncard := by
  by_cases hcrooked : S.IsCrookedTransaction P_set
  · exact ⟨P_set, hcrooked, le_rfl⟩
  · -- Since `P_set` is a transaction and not crooked, `P_set` has a peripheral member `P₁`.
    have hex_per₁ : ∃ P₁ ∈ P_set, S.IsPeripheralIn P_set P₁ := by
      by_contra! hno
      exact hcrooked ⟨htrans, hno⟩
    obtain ⟨P₁, hP₁_in, hper₁⟩ := hex_per₁
    -- Apply `theorem_4_1_step` to `P₁`.
    obtain ⟨P_set₁, htrans₁, hcard₁, hper_sub₁⟩ :=
      S.theorem_4_1_step htrans hper₁ (hnonsep P₁ hP₁_in hper₁)
    by_cases hcrooked₁ : S.IsCrookedTransaction P_set₁
    · exact ⟨P_set₁, hcrooked₁, hcard₁⟩
    · have hex_per₂ : ∃ P₂ ∈ P_set₁, S.IsPeripheralIn P_set₁ P₂ := by
        by_contra! hno
        exact hcrooked₁ ⟨htrans₁, hno⟩
      obtain ⟨P₂, _, hper₂'⟩ := hex_per₂
      obtain ⟨hper₂, hP₂_ne_P₁⟩ := hper_sub₁ P₂ hper₂'
      -- Apply `theorem_4_1_step` a second time to `P₂` in `P_set₁`.
      obtain ⟨P_set₂, htrans₂, hcard₂, hper_sub₂⟩ :=
        S.theorem_4_1_step htrans₁ hper₂' (hnonsep P₂ hper₂.1 hper₂)
      refine ⟨P_set₂, ⟨htrans₂, fun P₃ _ hper₃'' => ?_⟩, hcard₁.trans hcard₂⟩
      obtain ⟨hper₃', hP₃_ne_P₂⟩ := hper_sub₂ P₃ hper₃''
      obtain ⟨hper₃, hP₃_ne_P₁⟩ := hper_sub₁ P₃ hper₃'
      obtain ⟨A, B, hfence⟩ := htrans
      exact hfence.not_three_peripheral S hper₁ hper₂ hper₃
        hP₂_ne_P₁.symm hP₃_ne_P₁.symm hP₃_ne_P₂.symm

/-! ## Statement S, (4.2), and (4.3) -/

/-- **Graph Minors IX, (4.2)** (page 50):
"Let* **S** *be true. Suppose that $w, w' \in W(\mathscr{Q})$ are distinct, and that neither
of the corresponding attachments is exchangeable. Then $w, w'$ are both ends of the same
member of $\mathscr{Q}$." -/
theorem theorem_4_2_proof {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B)
    {w w' : α} (_hw_ne : w ≠ w')
    {P P' : Graph α β}
    (hatt : S.IsCorrespondingAttachment P_set Q_set w P)
    (hatt' : S.IsCorrespondingAttachment P_set Q_set w' P')
    (hnot_exch : ¬ S.IsExchangeableAttachment P_set P)
    (hnot_exch' : ¬ S.IsExchangeableAttachment P_set P') :
    ∃ Q ∈ Q_set, w ∈ pathEnds S.G Q ∧ w' ∈ pathEnds S.G Q := by
  rcases hatt with ⟨_, Q, hQ_in, hw_Q, hPQ, v, hatt_vw⟩
  rcases hatt' with ⟨_, Q', hQ'_in, hw'_Q', hP'Q', v', hatt'_v'w'⟩
  by_cases hQQ' : Q = Q'
  · subst hQQ'
    exact ⟨Q, hQ_in, hw_Q, hw'_Q'⟩
  · exfalso
    have hdisj_QQ' : Disjoint V(Q) V(Q') := hS.isTransaction_Q.choose_spec.choose_spec.1.2 hQ_in
      hQ'_in hQQ'
    have hdisj_PP' : Disjoint V(P) V(P') :=
      hdisj_QQ'.mono hPQ.vertexSet_mono hP'Q'.vertexSet_mono
    obtain ⟨P'', hP''_in, _, _, _, b, b', ⟨u_b, hatt_bu⟩, _, ⟨u_b', hatt'_b'u'⟩, _,
      M, hMP'', hM_path, P_set', hcrooked', hcard', hunion_le, hdisj_EM⟩ :=
      S.theorem_3_3_proof hS.isCrooked_P ⟨v, w, hatt_vw⟩ hnot_exch ⟨v', w', hatt'_v'w'⟩ hnot_exch'
        hdisj_PP'
    have hb_eq_v : b = v := by
      have hb_in : b ∈ V(P) ∩ V(S.transactionUnion P_set) :=
        ⟨hatt_bu.1.left_mem, hatt_bu.foot_mem_transactionUnion S⟩
      rwa [hatt_vw.2.1, mem_singleton_iff] at hb_in
    have hb'_eq_v' : b' = v' := by
      have hb'_in : b' ∈ V(P') ∩ V(S.transactionUnion P_set) :=
        ⟨hatt'_b'u'.1.left_mem, hatt'_b'u'.foot_mem_transactionUnion S⟩
      rwa [hatt'_v'w'.2.1, mem_singleton_iff] at hb'_in
    subst hb_eq_v
    subst hb'_eq_v'
    have hvv' : b ≠ b' :=
      fun h => disjoint_left.mp hdisj_PP' hatt_vw.1.left_mem (h ▸ hatt'_v'w'.1.left_mem)
    -- `P ∪ P' ≤ ⋃ Q_set`, so `⋃ P_set' ∪ ⋃ Q_set ≤ ⋃ P_set ∪ ⋃ Q_set`.
    have hQ_set_le : ∀ R ∈ Q_set, R ≤ S.G := fun R hR => by
      obtain ⟨_, _, h⟩ := hS.isTransaction_Q.choose_spec.choose_spec.1.1 R hR
      exact h.1.le
    have hP_set_le : ∀ R ∈ P_set, R ≤ S.G := fun R hR => by
      obtain ⟨_, _, h⟩ := hS.isFenceFor_P.1.1 R hR
      exact h.1.le
    have hP_set'_le : ∀ R ∈ P_set', R ≤ S.G := fun R hR => by
      obtain ⟨_, _, h⟩ := hcrooked'.1.choose_spec.choose_spec.1.1 R hR
      exact h.1.le
    have hUP_le : S.transactionUnion P_set ≤ S.G := subgraphSUnion_le hP_set_le
    have hUP'_le : S.transactionUnion P_set' ≤ S.G := subgraphSUnion_le hP_set'_le
    have hUQ_le : S.transactionUnion Q_set ≤ S.G := subgraphSUnion_le hQ_set_le
    have hQ_le_UQ : Q ≤ S.transactionUnion Q_set := le_subgraphSUnion hQ_set_le hQ_in
    have hQ'_le_UQ : Q' ≤ S.transactionUnion Q_set := le_subgraphSUnion hQ_set_le hQ'_in
    have hPP'_le_UQ : subgraphUnion S.G P P' ≤ S.transactionUnion Q_set :=
      (subgraphUnion_le_iff hatt_vw.1.le hatt'_v'w'.1.le hUQ_le).mpr
        ⟨hPQ.trans hQ_le_UQ, hP'Q'.trans hQ'_le_UQ⟩
    have hunion_sub :
        subgraphUnion S.G (S.transactionUnion P_set') (S.transactionUnion Q_set) ≤
          subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set) := by
      rw [subgraphUnion_le_iff hUP'_le hUQ_le (subgraphUnion_le hUP_le hUQ_le)]
      refine ⟨hunion_le.trans ?_, le_subgraphUnion_right hUP_le hUQ_le⟩
      rw [subgraphUnion_le_iff hUP_le (subgraphUnion_le hatt_vw.1.le hatt'_v'w'.1.le)
        (subgraphUnion_le hUP_le hUQ_le)]
      exact ⟨le_subgraphUnion_left hUP_le hUQ_le,
        hPP'_le_UQ.trans (le_subgraphUnion_right hUP_le hUQ_le)⟩
    have hunion_eq :
        subgraphUnion S.G (S.transactionUnion P_set') (S.transactionUnion Q_set) =
          subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set) :=
      hS.minimal_union P_set' hcrooked'
        (hS.card_P_ge.trans (by rw [hcard']; exact Nat.le_succ _)) hunion_sub
    -- Since `Disjoint E(M) E(S.transactionUnion P_set')`, every edge of `M` lies in
    -- `E(S.transactionUnion Q_set)`.
    have hEM_sub_UQ : E(M) ⊆ E(S.transactionUnion Q_set) := by
      intro e heM
      have he_in_P : e ∈ E(S.transactionUnion P_set) :=
        (hMP''.trans (le_subgraphSUnion hP_set_le hP''_in)).edgeSet_mono heM
      have he_rhs : e ∈ E(subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set))
        := by
        rw [edgeSet_subgraphUnion hUP_le hUQ_le]
        exact Or.inl he_in_P
      rw [← hunion_eq, edgeSet_subgraphUnion hUP'_le hUQ_le] at he_rhs
      exact he_rhs.resolve_left (disjoint_left.mp hdisj_EM heM)
    -- Walk along `M` from `b ∈ V(Q)` to `b' ∈ V(Q')`: since `Q_set` is pairwise vertex-disjoint,
    -- all vertices of `M` lie in `V(Q)`.
    have hM_G : IsGraphPathWithEnds S.G M b b' := hM_path.mono (hP_set_le P'' hP''_in)
    rcases hM_G with ⟨hMG, W_M, _, hVM, hEM⟩
    have hsupp_in_Q : ∀ z ∈ W_M.support, z ∈ V(Q) := by
      have hb_in_Q : b ∈ V(Q) := hPQ.vertexSet_mono hatt_vw.1.left_mem
      have h_ind : ∀ {u_w v_w : α} (W : GraphWalk M u_w v_w),
          (∀ e ∈ W.edges, e ∈ E(M)) → u_w ∈ V(Q) → ∀ z ∈ W.support, z ∈ V(Q) := by
        intro u_w v_w W
        induction W with
        | nil _ =>
          intro _ hu_Q z hz
          simp only [GraphWalk.support_nil, List.mem_singleton] at hz
          exact hz ▸ hu_Q
        | @cons u_c w_c _ e_c he_c W_tail ih =>
          intro hW_edges hu_Q z hz
          have he_M : e_c ∈ E(M) := hW_edges e_c List.mem_cons_self
          have he_UQ : e_c ∈ ⋃ R ∈ Q_set, E(R) := by
            have h := hEM_sub_UQ he_M
            rwa [show E(S.transactionUnion Q_set) = ⋃ R ∈ Q_set, E(R) from
              edgeSet_subgraphSUnion hQ_set_le] at h
          obtain ⟨R, hR_in, he_R⟩ := mem_iUnion₂.mp he_UQ
          obtain ⟨x_R, y_R, hxy_R⟩ := R.exists_isLink_of_mem_edgeSet he_R
          have hxy_G : S.G.IsLink e_c x_R y_R := hxy_R.mono (hQ_set_le R hR_in)
          have he_G : S.G.IsLink e_c u_c w_c := he_c.mono hMG
          have hu_R : u_c ∈ V(R) := by
            rcases he_G.left_eq_or_eq hxy_G with rfl | rfl
            · exact hxy_R.left_mem
            · exact hxy_R.right_mem
          have hw_R : w_c ∈ V(R) := by
            rcases he_G.symm.left_eq_or_eq hxy_G with rfl | rfl
            · exact hxy_R.left_mem
            · exact hxy_R.right_mem
          have hRQ : R = Q := by
            by_contra hne
            exact disjoint_left.mp
              (hS.isTransaction_Q.choose_spec.choose_spec.1.2 hR_in hQ_in hne) hu_R hu_Q
          subst hRQ
          rcases List.mem_cons.mp hz with rfl | hz_tail
          · exact hu_Q
          · exact ih (fun e he => hW_edges e (List.mem_cons_of_mem e_c he)) hw_R z hz_tail
      exact h_ind W_M (fun e he => by rwa [hEM, mem_ofPred_eq]) hb_in_Q
    have hb'_in_Q : b' ∈ V(Q) := hsupp_in_Q b' W_M.end_mem_support
    have hb'_in_Q' : b' ∈ V(Q') := hP'Q'.vertexSet_mono hatt'_v'w'.1.left_mem
    exact disjoint_left.mp hdisj_QQ' hb'_in_Q hb'_in_Q'

private theorem path_le_member_of_transaction {R_b Q : Graph α β} {s e₂ : α}
    {Q_set : Set (Graph α β)} (hQset : S.IsDisjointOmegaPathSet Q_set)
    (hQ_in : Q ∈ Q_set) (hRb_G : IsGraphPathWithEnds S.G R_b s e₂)
    (hs_in_Q : s ∈ V(Q)) (hERb_sub_UQ : E(R_b) ⊆ E(S.transactionUnion Q_set)) : R_b ≤ Q := by
  have hRb_le := hRb_G.le
  have hQ_set_le : ∀ M ∈ Q_set, M ≤ S.G := fun M hM => by
    obtain ⟨_, _, hpath⟩ := hQset.1 M hM
    exact hpath.1.le
  have hQ_le := hQ_set_le Q hQ_in
  rcases hRb_G with ⟨_, W_Rb, _, hVRb, hERb⟩
  have h_ind : ∀ {u_w v_w : α} (W : GraphWalk R_b u_w v_w),
      (∀ e ∈ W.edges, e ∈ E(R_b)) → u_w ∈ V(Q) →
      (∀ z ∈ W.support, z ∈ V(Q)) ∧ (∀ e ∈ W.edges, e ∈ E(Q)) := by
    intro u_w v_w W
    induction W with
    | nil _ =>
      intro _ hu_Q
      refine ⟨fun z hz => ?_, fun e he => by simp [GraphWalk.edges] at he⟩
      simp only [GraphWalk.support_nil, List.mem_singleton] at hz
      exact hz ▸ hu_Q
    | @cons u_c w_c _ e_c he_c W_tail ih =>
      intro hW_edges hu_Q
      have he_Rb : e_c ∈ E(R_b) := hW_edges e_c List.mem_cons_self
      have he_UQ : e_c ∈ ⋃ M ∈ Q_set, E(M) := by
        have h := hERb_sub_UQ he_Rb
        rwa [show E(S.transactionUnion Q_set) = ⋃ M ∈ Q_set, E(M) from
          edgeSet_subgraphSUnion hQ_set_le] at h
      obtain ⟨M, hM_in, he_M⟩ := mem_iUnion₂.mp he_UQ
      obtain ⟨x_M, y_M, hxy_M⟩ := M.exists_isLink_of_mem_edgeSet he_M
      have hxy_G : S.G.IsLink e_c x_M y_M := hxy_M.mono (hQ_set_le M hM_in)
      have he_G : S.G.IsLink e_c u_c w_c := he_c.mono hRb_le
      have hu_M : u_c ∈ V(M) := by
        rcases he_G.left_eq_or_eq hxy_G with rfl | rfl
        · exact hxy_M.left_mem
        · exact hxy_M.right_mem
      have hw_M : w_c ∈ V(M) := by
        rcases he_G.symm.left_eq_or_eq hxy_G with rfl | rfl
        · exact hxy_M.left_mem
        · exact hxy_M.right_mem
      have hMQ : M = Q := by
        by_contra hne
        exact disjoint_left.mp
          (hQset.2 hM_in hQ_in hne) hu_M hu_Q
      subst hMQ
      obtain ⟨ih_V, ih_E⟩ := ih (fun e he => hW_edges e (List.mem_cons_of_mem e_c he)) hw_M
      refine ⟨?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz_tail
        · exact hu_Q
        · exact ih_V z hz_tail
      · intro e he
        rcases List.mem_cons.mp he with rfl | he_tail
        · exact he_M
        · exact ih_E e he_tail
  obtain ⟨hV_sub, hE_sub⟩ := h_ind W_Rb (fun e he => by rwa [hERb, mem_ofPred_eq]) hs_in_Q
  rw [(Compatible.of_le_le hRb_le hQ_le).le_iff]
  exact ⟨fun z hz => hV_sub z (by rwa [hVRb, mem_ofPred_eq] at hz),
    fun e he => hE_sub e (by rwa [hERb, mem_ofPred_eq] at he)⟩

private theorem disjoint_from_replacement {P_set : Set (Graph α β)} {P₁ P R_a_rev R_b : Graph α β}
    {s e₂ : α} (hPset : S.IsDisjointOmegaPathSet P_set) (hP₁_in : P₁ ∈ P_set)
    (hRb_P₁ : R_b ≤ P₁) (hRb : IsGraphPathWithEnds S.G R_b s e₂)
    (hP_le : P ≤ S.G) (hRa_le : R_a_rev ≤ S.G) (hdisj_ERab : Disjoint E(R_a_rev) E(R_b))
    (hP_inter : V(R_b) ∩ V(P) ⊆ {s}) :
    let P_set' := (P_set \ {P₁}) ∪ {subgraphUnion S.G P R_a_rev}
    Disjoint E(R_b) E(S.transactionUnion P_set') := by
  intro P_set'
  have hRb_le := hRb.le
  have hP_set_le : ∀ M ∈ P_set, M ≤ S.G := fun M hM => by
    obtain ⟨_, _, hpath⟩ := hPset.1 M hM
    exact hpath.1.le
  have hP_set'_le : ∀ M ∈ P_set', M ≤ S.G := by
    rintro M (hM | rfl)
    · exact hP_set_le M hM.1
    · exact subgraphUnion_le hP_le hRa_le
  rw [show E(S.transactionUnion P_set') = ⋃ M ∈ P_set', E(M) from edgeSet_subgraphSUnion hP_set'_le,
    disjoint_iUnion₂_right]
  rintro M (hM | rfl)
  · rw [disjoint_left]
    intro e heRb heM
    obtain ⟨x_b, y_b, hxy_b⟩ := R_b.exists_isLink_of_mem_edgeSet heRb
    obtain ⟨x_M, y_M, hxy_M⟩ := M.exists_isLink_of_mem_edgeSet heM
    have hxy_bG : S.G.IsLink e x_b y_b := hxy_b.mono hRb_le
    have hxy_MG : S.G.IsLink e x_M y_M := hxy_M.mono (hP_set_le M hM.1)
    have hne_P₁M : P₁ ≠ M := fun h => hM.2 h.symm
    rcases hxy_bG.left_eq_or_eq hxy_MG with rfl | rfl
    · exact disjoint_left.mp (hPset.2 hP₁_in hM.1 hne_P₁M)
        (hRb_P₁.vertexSet_mono hxy_b.left_mem) hxy_M.left_mem
    · exact disjoint_left.mp (hPset.2 hP₁_in hM.1 hne_P₁M)
        (hRb_P₁.vertexSet_mono hxy_b.left_mem) hxy_M.right_mem
  · rw [edgeSet_subgraphUnion hP_le hRa_le, disjoint_union_right]
    refine ⟨disjoint_edgeSet_of_inter_singleton (z := s) hRb hP_le ?_,
      hdisj_ERab.symm⟩
    exact hP_inter

/-- If `StatementS` holds and `Q ∈ Q_set` satisfies none of (4.3)(i), (ii), (iii), then some end
`w` of `Q` belongs to `W(Q_set)` and has a non-exchangeable corresponding attachment `P ≤ Q`. -/
private theorem exists_nonExchangeable_correspondingAttachment_of_not_4_3
    {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B)
    {Q : Graph α β} (hQ_in : Q ∈ Q_set)
    (h_not_i : (V(Q) ∩ V(S.transactionUnion P_set)).Nonempty)
    (h_not_ii : ¬ pathEnds S.G Q ⊆ S.transactionEnds P_set)
    (h_not_iii : ¬ S.IsHalfCovered P_set Q) :
    ∃ w ∈ pathEnds S.G Q, ∃ P : Graph α β,
      S.IsCorrespondingAttachment P_set Q_set w P ∧
      ¬ S.IsExchangeableAttachment P_set P := by
  obtain ⟨a_raw, b_raw, hQ_ends_raw⟩ :=
    hS.isTransaction_Q.choose_spec.choose_spec.1.1 Q hQ_in
  -- Ensure the first end `w` of `Q` is not in `S.transactionEnds P_set`.
  have hex_ends : ∃ w t : α, S.IsOmegaPathWithEnds Q w t ∧ w ∉ S.transactionEnds P_set := by
    rw [hQ_ends_raw.1.pathEnds_eq] at h_not_ii
    by_cases ha_in : a_raw ∈ S.transactionEnds P_set
    · have hb_not : b_raw ∉ S.transactionEnds P_set := fun hb_in =>
        h_not_ii (by rintro z (rfl | rfl); exacts [ha_in, hb_in])
      exact ⟨b_raw, a_raw, hQ_ends_raw.symm S, hb_not⟩
    · exact ⟨a_raw, b_raw, hQ_ends_raw, ha_in⟩
  obtain ⟨w, t, hQ_ends, hw_not_P⟩ := hex_ends
  have hQ_le := hQ_ends.1.le
  -- Extract a minimal `V(⋃ P_set) → (S.Ω.bar \ V(P_set))` subpath `P ≤ Q`.
  obtain ⟨x₀, hx₀Q, hx₀U⟩ := h_not_i
  obtain ⟨Q₁, hQ₁Q, _, hQ₁_path⟩ := hQ_ends.1.exists_subpath hx₀Q hQ_ends.1.left_mem
  obtain ⟨s, hs_U, u, hu_bar_diff, P, hPQ₁, hP_ft⟩ :=
    hQ₁_path.exists_isFromToPathWithEnds
      (X := V(S.transactionUnion P_set))
      (Y := S.Ω.bar \ S.transactionEnds P_set)
      hx₀U ⟨hQ_ends.2.2.1, hw_not_P⟩
  have hPQ : P ≤ Q := hPQ₁.trans hQ₁Q
  have hatt_su : S.IsAttachmentWithEnds P_set P s u := hP_ft
  -- Since `Q` has no internal vertex in `S.Ω.bar`, `u ∈ V(P) ⊆ V(Q)` with `u ∈ S.Ω.bar` must be an
  -- end of `Q`.
  have hu_ends_Q : u ∈ pathEnds S.G Q := by
    by_contra hu_not_end
    have hu_int : u ∈ pathInternalVerts S.G Q := ⟨hPQ.vertexSet_mono hP_ft.1.right_mem, hu_not_end⟩
    exact disjoint_left.mp (hS.no_internal_in_bar Q hQ_in) hu_int hu_bar_diff.1
  have hu_in_W : u ∈ S.uncoveredSet P_set Q_set := by
    have hu_ends_pair : u = w ∨ u = t := by
      rwa [hQ_ends.1.pathEnds_eq, mem_insert_iff, mem_singleton_iff] at hu_ends_Q
    have hu_trans_Q : u ∈ S.transactionEnds Q_set := by
      rcases hu_ends_pair with rfl | rfl
      · exact hQ_ends.mem_transactionEnds_left S hQ_in
      · exact hQ_ends.mem_transactionEnds_right S hQ_in
    exact ⟨hu_trans_Q, hu_bar_diff.2, Q, hQ_in, hu_ends_Q, ⟨x₀, hx₀Q, hx₀U⟩⟩
  have hcorr : S.IsCorrespondingAttachment P_set Q_set u P :=
    ⟨hu_in_W, Q, hQ_in, hu_ends_Q, hPQ, s, hatt_su⟩
  refine ⟨u, hu_ends_Q, P, hcorr, ?_⟩
  -- Suppose for contradiction that `P` is exchangeable; we deduce `S.IsHalfCovered P_set Q`.
  rintro ⟨_, P₁, L', hsw, hcrooked'⟩
  apply h_not_iii
  rcases hsw with ⟨hP₁_in, b_sw, u_sw, a₁_sw, b₁_sw, hatt_sw, hb_sw_P₁, hP₁_ends_sw, R, hR_or, rfl⟩
  have hb_eq_s : s = b_sw := by
    have hb_in : b_sw ∈ V(P) ∩ V(S.transactionUnion P_set) :=
      ⟨hatt_sw.1.left_mem, hatt_sw.foot_mem_transactionUnion S⟩
    rw [hatt_su.2.1, mem_singleton_iff] at hb_in
    exact hb_in.symm
  subst hb_eq_s
  -- Orient `P₁` so that `R` is the subpath of `P₁` from `s` to the first end `e₁` of `P₁`.
  have hex_P₁ : ∃ e₁ e₂ : α, S.IsOmegaPathWithEnds P₁ e₁ e₂ ∧ IsGraphPathWithEnds P₁ R s e₁ := by
    rcases hR_or with hR_a | hR_b
    · exact ⟨a₁_sw, b₁_sw, hP₁_ends_sw, hR_a⟩
    · exact ⟨b₁_sw, a₁_sw, hP₁_ends_sw.symm S, hR_b⟩
  obtain ⟨e₁, e₂, hP₁_ends, hR_e₁⟩ := hex_P₁
  obtain ⟨R_a_rev, R_b, hRa_P₁, hRb_P₁, hRa_rev, hRb, _, hinter_Rab, hdisj_ERab⟩ :=
    hP₁_ends.1.exists_split_at hb_sw_P₁
  have hRa_eq_R : R_a_rev = R :=
    hP₁_ends.1.subpath_unique_of_left hRa_rev hR_e₁.symm
  subst hRa_eq_R
  let L' := subgraphUnion S.G P R_a_rev
  let P_set' := (P_set \ {P₁}) ∪ {L'}
  have hQ_set_le : ∀ M ∈ Q_set, M ≤ S.G := fun M hM => by
    obtain ⟨_, _, h⟩ := hS.isTransaction_Q.choose_spec.choose_spec.1.1 M hM
    exact h.1.le
  have hP_set_le : ∀ M ∈ P_set, M ≤ S.G := fun M hM => by
    obtain ⟨_, _, h⟩ := hS.isFenceFor_P.1.1 M hM
    exact h.1.le
  have hP_set'_le : ∀ M ∈ P_set', M ≤ S.G := fun M hM => by
    obtain ⟨_, _, h⟩ := hcrooked'.1.choose_spec.choose_spec.1.1 M hM
    exact h.1.le
  have hUP_le : S.transactionUnion P_set ≤ S.G := subgraphSUnion_le hP_set_le
  have hUP'_le : S.transactionUnion P_set' ≤ S.G := subgraphSUnion_le hP_set'_le
  have hUQ_le : S.transactionUnion Q_set ≤ S.G := subgraphSUnion_le hQ_set_le
  have hP₁_le : P₁ ≤ S.G := hP₁_ends.1.le
  have hP_le : P ≤ S.G := hatt_su.1.le
  have hRa_le : R_a_rev ≤ S.G := hRa_P₁.trans hP₁_le
  have hRb_le : R_b ≤ S.G := hRb_P₁.trans hP₁_le
  -- `|P_set'| = |P_set| ≥ p` and `⋃ P_set' ∪ ⋃ Q_set ≤ ⋃ P_set ∪ ⋃ Q_set`.
  have hL'_not_diff : L' ∉ P_set \ {P₁} :=
    IsAttachmentWithEnds.subgraphUnion_not_mem_sdiff S hS.isFenceFor_P.1 hatt_su hP₁_in hb_sw_P₁
  have hfin_P : P_set.Finite := hS.isFenceFor_P.1.finite S
  have hcard' : P_set'.ncard = P_set.ncard := by
    have hset_eq : P_set' = insert L' (P_set \ {P₁}) := by ext M; simp [P_set', or_comm]
    rw [hset_eq, ncard_insert_of_notMem hL'_not_diff hfin_P.sdiff,
      ncard_sdiff_singleton_add_one hP₁_in hfin_P]
  have hunion_sub :
      subgraphUnion S.G (S.transactionUnion P_set') (S.transactionUnion Q_set) ≤
        subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set) := by
    rw [subgraphUnion_le_iff hUP'_le hUQ_le (subgraphUnion_le hUP_le hUQ_le)]
    refine ⟨?_, le_subgraphUnion_right hUP_le hUQ_le⟩
    rw [(Compatible.of_le_le hUP'_le (subgraphUnion_le hUP_le hUQ_le)).le_iff]
    constructor
    · intro x hx
      change x ∈ ⋃ M ∈ P_set', V(M) at hx
      rw [mem_iUnion₂] at hx
      rcases hx with ⟨M, hM | rfl, hxM⟩
      · exact Or.inl (mem_iUnion₂.mpr ⟨M, hM.1, hxM⟩)
      · rcases hxM with hxP | hxRa
        · exact Or.inr (mem_iUnion₂.mpr ⟨Q, hQ_in, hPQ.vertexSet_mono hxP⟩)
        · exact Or.inl (mem_iUnion₂.mpr ⟨P₁, hP₁_in, hRa_P₁.vertexSet_mono hxRa⟩)
    · rw [show E(S.transactionUnion P_set') = ⋃ M ∈ P_set', E(M) from edgeSet_subgraphSUnion
      hP_set'_le,
        edgeSet_subgraphUnion hUP_le hUQ_le,
        show E(S.transactionUnion P_set) = ⋃ M ∈ P_set, E(M) from edgeSet_subgraphSUnion hP_set_le,
        show E(S.transactionUnion Q_set) = ⋃ M ∈ Q_set, E(M) from edgeSet_subgraphSUnion hQ_set_le]
      intro e he
      rw [mem_iUnion₂] at he
      rcases he with ⟨M, hM | rfl, heM⟩
      · exact Or.inl (mem_iUnion₂.mpr ⟨M, hM.1, heM⟩)
      · rw [edgeSet_subgraphUnion hP_le hRa_le] at heM
        rcases heM with heP | heRa
        · exact Or.inr (mem_iUnion₂.mpr ⟨Q, hQ_in, hPQ.edgeSet_mono heP⟩)
        · exact Or.inl (mem_iUnion₂.mpr ⟨P₁, hP₁_in, hRa_P₁.edgeSet_mono heRa⟩)
  have hunion_eq :
      subgraphUnion S.G (S.transactionUnion P_set') (S.transactionUnion Q_set) =
        subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set) :=
    hS.minimal_union P_set' hcrooked' (hcard' ▸ hS.card_P_ge) hunion_sub
  -- `R_b` is edge-disjoint from `⋃ P_set'`, so `E(R_b) ⊆ E(⋃ Q_set)`.
  have hdisj_ERb_UP' : Disjoint E(R_b) E(S.transactionUnion P_set') :=
    disjoint_from_replacement S hS.isFenceFor_P.1 hP₁_in hRb_P₁ (hRb.mono hP₁_le)
      hP_le hRa_le hdisj_ERab (by
        rw [← hatt_su.inter_leg_eq_singleton S hP₁_in hb_sw_P₁, inter_comm V(P) V(P₁)]
        exact inter_subset_inter_left _ hRb_P₁.vertexSet_mono)
  have hERb_sub_UQ : E(R_b) ⊆ E(S.transactionUnion Q_set) := by
    intro e heRb
    have he_in_P : e ∈ E(S.transactionUnion P_set) :=
      (hRb_P₁.trans (le_subgraphSUnion hP_set_le hP₁_in)).edgeSet_mono heRb
    have he_rhs : e ∈ E(subgraphUnion S.G (S.transactionUnion P_set) (S.transactionUnion Q_set))
      := by
      rw [edgeSet_subgraphUnion hUP_le hUQ_le]
      exact Or.inl he_in_P
    rw [← hunion_eq, edgeSet_subgraphUnion hUP'_le hUQ_le] at he_rhs
    exact he_rhs.resolve_left (disjoint_left.mp hdisj_ERb_UP' heRb)
  -- Since `R_b` starts at `s ∈ V(Q)` and `Q_set` is pairwise vertex-disjoint, `R_b ≤ Q`.
  have hRb_le_Q : R_b ≤ Q :=
    path_le_member_of_transaction S hS.isTransaction_Q.choose_spec.choose_spec.1 hQ_in
      (hRb.mono hP₁_le)
      (hPQ.vertexSet_mono hatt_su.1.left_mem) hERb_sub_UQ
  -- `e₂ ∈ V(R_b) ⊆ V(Q)` and `e₂ ∈ S.Ω.bar`, so `e₂ ∈ pathEnds S.G Q` and `e₂ ≠ u`.
  have he₂_in_Q : e₂ ∈ V(Q) := hRb_le_Q.vertexSet_mono hRb.right_mem
  have he₂_ends_Q : e₂ ∈ pathEnds S.G Q := by
    by_contra he₂_not_end
    have he₂_int : e₂ ∈ pathInternalVerts S.G Q := ⟨he₂_in_Q, he₂_not_end⟩
    exact disjoint_left.mp (hS.no_internal_in_bar Q hQ_in) he₂_int hP₁_ends.2.2.2
  have he₂_ne_u : e₂ ≠ u := fun h =>
    hu_bar_diff.2 (h ▸ hP₁_ends.mem_transactionEnds_right S hP₁_in)
  have hQ_ends_e₂u : S.IsOmegaPathWithEnds Q e₂ u := by
    rw [hQ_ends.1.pathEnds_eq, mem_insert_iff, mem_singleton_iff] at hu_ends_Q he₂_ends_Q
    rcases he₂_ends_Q with rfl | rfl <;> rcases hu_ends_Q with rfl | rfl
    · exact (he₂_ne_u rfl).elim
    · exact hQ_ends
    · exact hQ_ends.symm S
    · exact (he₂_ne_u rfl).elim
  -- `subgraphUnion S.G R_b P ≤ Q` has the same ends `e₂, u` as `Q`, so `Q = subgraphUnion S.G R_b
  -- P`.
  have hinter_RbP : V(R_b) ∩ V(P) = {s} := by
    apply Subset.antisymm
    · intro z ⟨hzRb, hzP⟩
      have hz_in : z ∈ V(P) ∩ V(P₁) := ⟨hzP, hRb_P₁.vertexSet_mono hzRb⟩
      rwa [hatt_su.inter_leg_eq_singleton S hP₁_in hb_sw_P₁] at hz_in
    · rintro z rfl
      exact ⟨hRb.left_mem, hatt_su.1.left_mem⟩
  have hRbP_path : IsGraphPathWithEnds S.G (subgraphUnion S.G R_b P) e₂ u :=
    (hRb.mono hP₁_le).symm.subgraphUnion hatt_su.1 hinter_RbP
  have hRbP_le_Q : subgraphUnion S.G R_b P ≤ Q :=
    (subgraphUnion_le_iff hRb_le hP_le hQ_le).mpr ⟨hRb_le_Q, hPQ⟩
  have hQ_eq : subgraphUnion S.G R_b P = Q :=
    hQ_ends_e₂u.1.eq_of_le_of_same_ends hRbP_path hRbP_le_Q
  -- Conclude `S.IsHalfCovered P_set Q`.
  refine ⟨P₁, hP₁_in, ⟨s, hb_sw_P₁, hPQ.vertexSet_mono hatt_su.1.left_mem⟩, ?_,
    e₂, e₁, e₂, u, s, hP₁_ends.symm S, hQ_ends_e₂u, rfl, hu_bar_diff.2, ?_⟩
  · intro P' hP'_in ⟨z, hzP', hzQ⟩
    rw [← hQ_eq, vertexSet_subgraphUnion] at hzQ
    by_contra hne
    rcases hzQ with hzRb | hzP
    · exact disjoint_left.mp (hS.isFenceFor_P.1.2 hP'_in hP₁_in hne)
        hzP' (hRb_P₁.vertexSet_mono hzRb)
    · have hz_eq_s : z = s := by
        have hzU : z ∈ V(P) ∩ V(S.transactionUnion P_set) :=
          ⟨hzP, mem_iUnion₂.mpr ⟨P', hP'_in, hzP'⟩⟩
        rwa [hatt_su.2.1, mem_singleton_iff] at hzU
      subst hz_eq_s
      exact disjoint_left.mp (hS.isFenceFor_P.1.2 hP'_in hP₁_in hne) hzP' hb_sw_P₁
  · have hinter_P₁Q : subgraphInter S.G P₁ Q = R_b := by
      refine (Compatible.of_le_le (subgraphInter_le hP₁_le) hRb_le).ext ?_ ?_
      · rw [vertexSet_subgraphInter, ← hQ_eq, vertexSet_subgraphUnion]
        ext z
        simp only [mem_inter_iff, mem_union]
        constructor
        · rintro ⟨hzP₁, hzRb | hzP⟩
          · exact hzRb
          · have hzs : z = s := by
              have h_in : z ∈ V(P) ∩ V(P₁) := ⟨hzP, hzP₁⟩
              rwa [hatt_su.inter_leg_eq_singleton S hP₁_in hb_sw_P₁, mem_singleton_iff] at h_in
            exact hzs ▸ hRb.left_mem
        · intro hzRb
          exact ⟨hRb_P₁.vertexSet_mono hzRb, Or.inl hzRb⟩
      · rw [edgeSet_subgraphInter hP₁_le hQ_le, ← hQ_eq, edgeSet_subgraphUnion hRb_le hP_le]
        ext e
        simp only [mem_inter_iff, mem_union]
        constructor
        · rintro ⟨heP₁, heRb | heP⟩
          · exact heRb
          · have hdisj_EP₁P : Disjoint E(P₁) E(P) :=
              disjoint_edgeSet_of_inter_singleton (z := s) hP₁_ends.1 hP_le (by
                rw [← hatt_su.inter_leg_eq_singleton S hP₁_in hb_sw_P₁, inter_comm])
            exact (disjoint_left.mp hdisj_EP₁P heP₁ heP).elim
        · intro heRb
          exact ⟨hRb_P₁.edgeSet_mono heRb, Or.inl heRb⟩
    rw [hinter_P₁Q]
    exact (hRb.mono hP₁_le).symm

/-- **Graph Minors IX, (4.3)** (page 50):
"Let* **S** *be true. For every $Q \in \mathscr{Q}$ except possibly one, either* (i) *$Q \cap
\bigcup \mathscr{P} = \emptyset$, or* (ii) *both ends of $Q$ are in $V(\mathscr{P})$, or*
(iii) *$Q$ meets exactly one member $P$ of $\mathscr{P}$, $P \cap Q$ is a path, and $P, Q$
and $P \cap Q$ have a common end, and the other end of $Q$ is not in $V(\mathscr{P})$.* *If
(i), (ii), (iii) are all false for some $Q \in \mathscr{Q}$ then $\mathscr{P}$ has an
overpass." -/
theorem theorem_4_3_proof {p : ℕ} {P_set Q_set : Set (Graph α β)} {A B : Set α}
    (hS : S.StatementS p P_set Q_set A B) :
    (∀ Q₁ ∈ Q_set, ∀ Q₂ ∈ Q_set,
      ¬ (Disjoint V(Q₁) V(S.transactionUnion P_set) ∨
          pathEnds S.G Q₁ ⊆ S.transactionEnds P_set ∨
          S.IsHalfCovered P_set Q₁) →
      ¬ (Disjoint V(Q₂) V(S.transactionUnion P_set) ∨
          pathEnds S.G Q₂ ⊆ S.transactionEnds P_set ∨
          S.IsHalfCovered P_set Q₂) →
      Q₁ = Q₂) ∧
    (∀ Q ∈ Q_set,
      ¬ (Disjoint V(Q) V(S.transactionUnion P_set) ∨
          pathEnds S.G Q ⊆ S.transactionEnds P_set ∨
          S.IsHalfCovered P_set Q) →
      ∃ P₁ ∈ P_set, S.IsOverpass P_set P₁) := by
  refine ⟨fun Q₁ hQ₁ Q₂ hQ₂ hnot₁ hnot₂ => ?_, fun Q hQ hnot => ?_⟩
  · push Not at hnot₁ hnot₂
    rw [not_disjoint_iff_nonempty_inter] at hnot₁ hnot₂
    obtain ⟨w₁, hw₁_ends, P₁, hcorr₁, hnot_exch₁⟩ :=
      S.exists_nonExchangeable_correspondingAttachment_of_not_4_3 hS hQ₁
        hnot₁.1 hnot₁.2.1 hnot₁.2.2
    obtain ⟨w₂, hw₂_ends, P₂, hcorr₂, hnot_exch₂⟩ :=
      S.exists_nonExchangeable_correspondingAttachment_of_not_4_3 hS hQ₂
        hnot₂.1 hnot₂.2.1 hnot₂.2.2
    by_contra hne
    have hdisj_Q12 : Disjoint V(Q₁) V(Q₂) :=
      hS.isTransaction_Q.choose_spec.choose_spec.1.2 hQ₁ hQ₂ hne
    have hw₁_V : w₁ ∈ V(Q₁) := by
      rcases hw₁_ends with ⟨_, h⟩
      exact h.left_mem
    have hw₂_V : w₂ ∈ V(Q₂) := by
      rcases hw₂_ends with ⟨_, h⟩
      exact h.left_mem
    have hw_ne : w₁ ≠ w₂ := fun h => disjoint_left.mp hdisj_Q12 hw₁_V (h ▸ hw₂_V)
    obtain ⟨Q₀, hQ₀_in, hw₁_Q₀, hw₂_Q₀⟩ :=
      S.theorem_4_2_proof hS hw_ne hcorr₁ hcorr₂ hnot_exch₁ hnot_exch₂
    have hw₁_VQ₀ : w₁ ∈ V(Q₀) := by rcases hw₁_Q₀ with ⟨_, h⟩; exact h.left_mem
    have hw₂_VQ₀ : w₂ ∈ V(Q₀) := by rcases hw₂_Q₀ with ⟨_, h⟩; exact h.left_mem
    have hQ₀_eq_Q₁ : Q₀ = Q₁ := by
      by_contra hne₁
      exact disjoint_left.mp
        (hS.isTransaction_Q.choose_spec.choose_spec.1.2 hQ₀_in hQ₁ hne₁) hw₁_VQ₀ hw₁_V
    have hQ₀_eq_Q₂ : Q₀ = Q₂ := by
      by_contra hne₂
      exact disjoint_left.mp
        (hS.isTransaction_Q.choose_spec.choose_spec.1.2 hQ₀_in hQ₂ hne₂) hw₂_VQ₀ hw₂_V
    exact hne (hQ₀_eq_Q₁.symm.trans hQ₀_eq_Q₂)
  · push Not at hnot
    rw [not_disjoint_iff_nonempty_inter] at hnot
    obtain ⟨w, _, P, hcorr, hnot_exch⟩ :=
      S.exists_nonExchangeable_correspondingAttachment_of_not_4_3 hS hQ
        hnot.1 hnot.2.1 hnot.2.2
    rcases hcorr with ⟨_, _, _, _, _, s, hatt_sw⟩
    obtain ⟨_, P₁, hleg, hover⟩ := S.theorem_3_2_proof hS.isCrooked_P ⟨s, w, hatt_sw⟩ hnot_exch
    exact ⟨P₁, hleg.1, hover⟩

end Society

end GraphMinor.GM09
