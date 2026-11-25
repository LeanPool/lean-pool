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
import LeanPool.GraphMinor.GM09.Section2d
import LeanPool.GraphMinor.GM09.Section3a
import LeanPool.GraphMinor.GM09.Section3b
import Mathlib.Data.Set.Card

/-!
# Graph Minors IX, Section 3 (Part 3): Two-Point Path Splitting and (3.3)

This file establishes:
- absence of loop edges in paths (`IsGraphPathWithEnds.not_isLoopAt`) and edge-disjointness of
  paths meeting at a single vertex (`disjoint_edgeSet_of_inter_singleton`),
- splitting a path `L` at two distinct vertices `b, b' ∈ V(L)` into two disjoint end-subpaths
  `Q₁, Q₂` and the middle subpath `M` between `b` and `b'` (`exists_two_point_split`),
- Graph Minors IX, (3.3) (`theorem_3_3`, page 48): if `P` and `P'` are disjoint non-exchangeable
  attachments to a crooked transaction `P_set`, then they have a common leg `P₁` which is an
  overpass of `P_set`, and replacing `P₁` by the two disjoint switches of `P` and `P'` yields a
  crooked transaction `P_set'` of cardinality `|P_set| + 1` with no edge of `P₁` between the two
  feet in `⋃ P_set'`.
-/

public section

namespace GraphMinor.GM09

open Set Graph GraphMinor GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

/-! ## Loop-freeness of paths and two-point path splitting -/

private theorem walk_not_isLoopAt_of_isSimple {G : Graph α β} {a b : α}
    {W : GraphWalk G a b} (hW : W.IsSimple) {e : β} (he : e ∈ W.edges) (z : α) :
    ¬ G.IsLink e z z := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons u w _ f hfu W' ih =>
    have hnodup : (u :: W'.support).Nodup := hW
    have hu_not_in : u ∉ W'.support := (List.nodup_cons.mp hnodup).1
    have hW'_simple : W'.IsSimple := (List.nodup_cons.mp hnodup).2
    simp only [GraphWalk.edges, List.mem_cons] at he
    rcases he with rfl | he'
    · intro hloop
      have huz : u = z := (hfu.left_eq_or_eq hloop).elim id id
      have hwz : w = z := (hfu.symm.left_eq_or_eq hloop).elim id id
      exact hu_not_in (huz.trans hwz.symm ▸ W'.start_mem_support)
    · exact ih hW'_simple he'

theorem IsGraphPathWithEnds.not_isLoopAt {G R : Graph α β} {a b : α}
    (hR : IsGraphPathWithEnds G R a b) {e : β} (he : e ∈ E(R)) (z : α) :
    ¬ G.IsLink e z z := by
  rcases hR with ⟨hRG, W, hW, _, hER⟩
  rw [hER, mem_ofPred_eq] at he
  intro hloop
  exact walk_not_isLoopAt_of_isSimple hW he z ((hRG.isLink_iff (hER ▸ he)).mpr hloop)

theorem disjoint_edgeSet_of_inter_singleton {G R P : Graph α β} {a b z : α}
    (hR : IsGraphPathWithEnds G R a b) (hPG : P ≤ G)
    (hinter : V(R) ∩ V(P) ⊆ {z}) :
    Disjoint E(R) E(P) := by
  rw [disjoint_left]
  intro e heR heP
  obtain ⟨x, y, hxyR⟩ := R.exists_isLink_of_mem_edgeSet heR
  have hxyG : G.IsLink e x y := hxyR.mono hR.le
  have hxyP : P.IsLink e x y := (hPG.isLink_iff heP).mpr hxyG
  have hxz : x = z := mem_singleton_iff.mp (hinter ⟨hxyR.left_mem, hxyP.left_mem⟩)
  have hyz : y = z := mem_singleton_iff.mp (hinter ⟨hxyR.right_mem, hxyP.right_mem⟩)
  rw [hxz, hyz] at hxyG
  exact hR.not_isLoopAt heR z hxyG

/-- If `L` is a path in `G` with ends `a₁, b₁` and `b, b' ∈ V(L)` are distinct, then `L` splits into
three subpaths `Q₁, M, Q₂ ≤ L` such that `M` is the subpath of `L` between `b` and `b'`, `Q₁` and
`Q₂` are vertex-disjoint subpaths from `b, b'` to opposite ends of `L`, and `M` is edge-disjoint
from both `Q₁` and `Q₂`. -/
theorem IsGraphPathWithEnds.exists_two_point_split {G L : Graph α β} {a₁ b₁ b b' : α}
    (hL : IsGraphPathWithEnds G L a₁ b₁)
    (hb : b ∈ V(L)) (hb' : b' ∈ V(L)) (hne : b ≠ b') :
    ∃ Q₁ Q₂ M : Graph α β,
      Q₁ ≤ L ∧ Q₂ ≤ L ∧ M ≤ L ∧
      IsGraphPathWithEnds L M b b' ∧
      ((IsGraphPathWithEnds L Q₁ b a₁ ∧ IsGraphPathWithEnds L Q₂ b' b₁) ∨
        (IsGraphPathWithEnds L Q₁ b b₁ ∧ IsGraphPathWithEnds L Q₂ b' a₁)) ∧
      Disjoint V(Q₁) V(Q₂) ∧
      Disjoint E(M) E(Q₁) ∧ Disjoint E(M) E(Q₂) := by
  obtain ⟨L₁, L₂, hL₁L, hL₂L, hL₁, hL₂, hunion, hinter, hdisjE⟩ := hL.exists_split_at hb
  have hb'_union : b' ∈ V(L₁) ∪ V(L₂) := by
    rw [← vertexSet_subgraphUnion L L₁ L₂, hunion]
    exact hb'
  rcases hb'_union with hb'₁ | hb'₂
  · -- `b' ∈ V(L₁)`: split `L₁` at `b'`.
    obtain ⟨Q₂', M', hQ₂'L₁, hM'L₁, hQ₂', hM', _, hinter₁, hdisjE₁⟩ := hL₁.exists_split_at hb'₁
    have hQ₂L : Q₂' ≤ L := hQ₂'L₁.trans hL₁L
    have hML : M' ≤ L := hM'L₁.trans hL₁L
    refine ⟨L₂, Q₂', M', hL₂L, hQ₂L, hML,
      (hM'.mono hL₁L).symm, Or.inr ⟨hL₂, (hQ₂'.mono hL₁L).symm⟩, ?_, ?_, hdisjE₁.symm⟩
    · rw [disjoint_left]
      intro z hzL₂ hzQ₂'
      have hz_inter : z ∈ V(L₁) ∩ V(L₂) := ⟨hQ₂'L₁.vertexSet_mono hzQ₂', hzL₂⟩
      rw [hinter, mem_singleton_iff] at hz_inter
      subst hz_inter
      have hz_inter₁ : z ∈ V(Q₂') ∩ V(M') := ⟨hzQ₂', hM'.right_mem⟩
      rw [hinter₁, mem_singleton_iff] at hz_inter₁
      exact hne hz_inter₁
    · exact hdisjE.mono_left hM'L₁.edgeSet_mono
  · -- `b' ∈ V(L₂)`: split `L₂` at `b'`.
    obtain ⟨M', Q₂', hM'L₂, hQ₂'L₂, hM', hQ₂', _, hinter₂, hdisjE₂⟩ := hL₂.exists_split_at hb'₂
    have hML : M' ≤ L := hM'L₂.trans hL₂L
    have hQ₂L : Q₂' ≤ L := hQ₂'L₂.trans hL₂L
    refine ⟨L₁, Q₂', M', hL₁L, hQ₂L, hML,
      hM'.mono hL₂L, Or.inl ⟨hL₁.symm, hQ₂'.mono hL₂L⟩, ?_, ?_, hdisjE₂⟩
    · rw [disjoint_left]
      intro z hzL₁ hzQ₂'
      have hz_inter : z ∈ V(L₁) ∩ V(L₂) := ⟨hzL₁, hQ₂'L₂.vertexSet_mono hzQ₂'⟩
      rw [hinter, mem_singleton_iff] at hz_inter
      subst hz_inter
      have hz_inter₂ : z ∈ V(M') ∩ V(Q₂') := ⟨hM'.left_mem, hzQ₂'⟩
      rw [hinter₂, mem_singleton_iff] at hz_inter₂
      exact hne hz_inter₂
    · exact hdisjE.symm.mono_left hM'L₂.edgeSet_mono

namespace Society

/-- Every set of mutually vertex-disjoint `Ω`-paths in a society `S` is finite. -/
theorem IsDisjointOmegaPathSet.finite (S : Society α β)
    {P_set : Set (Graph α β)} (h : S.IsDisjointOmegaPathSet P_set) :
    P_set.Finite := by
  have hex : ∀ P : P_set, ∃ a : S.Ω.bar, (a : α) ∈ V(P.1) := by
    intro ⟨P, hP⟩
    obtain ⟨a, _, hP_ends⟩ := h.1 P hP
    exact ⟨⟨a, hP_ends.2.2.1⟩, hP_ends.1.left_mem⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩ heq
    by_contra hne
    have hne' : P₁ ≠ P₂ := fun h_eq => hne (Subtype.ext h_eq)
    exact disjoint_left.mp (h.2 hP₁ hP₂ hne') (hf ⟨P₁, hP₁⟩) ( congrArg Subtype.val heq ▸ hf ⟨P₂,
      hP₂⟩)
  have : Finite S.Ω.bar := S.Ω.finite_bar.to_subtype
  have : Finite P_set := Finite.of_injective f hinj
  exact Set.toFinite P_set

/-! ## Four-arc decomposition around an overpass and crookedness of switches -/

/-- Given a fence `(A, B)` of `Ω` and `W' ⊆ Ω.bar` with empty-interval boundary pairs
`(a'_0, b_0) ∈ (A ∩ W') × (B ∩ W')` and `(b'_0, a_0) ∈ (B ∩ W') × (A ∩ W')`, let
`G₁ := Ω.interval a'_0 b_0`, `G₂ := Ω.interval b'_0 a_0`,
`A_arc := ({a'_0} ∪ Ω.interval b'_0 a'_0) \ G₂`, and
`B_arc := ({b'_0} ∪ Ω.interval a'_0 b'_0) \ G₁`.
Then `A ∩ W' ⊆ A_arc`, `B ∩ W' ⊆ B_arc`, and `Ω.bar = A_arc ∪ G₁ ∪ B_arc ∪ G₂` as a pairwise
disjoint union. -/
theorem four_arc_partition {Ω : CyclicPerm α} {A B W' : Set α}
    (hfence : Ω.IsFence A B) (hW' : W' ⊆ Ω.bar)
    {a_0 a'_0 b_0 b'_0 : α}
    (ha_0 : a_0 ∈ A ∩ W') (ha'_0 : a'_0 ∈ A ∩ W')
    (hb_0 : b_0 ∈ B ∩ W') (hb'_0 : b'_0 ∈ B ∩ W')
    (hd_ab : Disjoint (Ω.interval a'_0 b_0) W')
    (hd_ba : Disjoint (Ω.interval b'_0 a_0) W') :
    let G₁ := Ω.interval a'_0 b_0
    let G₂ := Ω.interval b'_0 a_0
    let A_arc := ({a'_0} ∪ Ω.interval b'_0 a'_0) \ G₂
    let B_arc := ({b'_0} ∪ Ω.interval a'_0 b'_0) \ G₁
    A ∩ W' ⊆ A_arc ∧ B ∩ W' ⊆ B_arc ∧
    G₂ ⊆ Ω.interval b'_0 a'_0 ∧ G₁ ⊆ Ω.interval a'_0 b'_0 ∧
    Disjoint ({a'_0} ∪ Ω.interval b'_0 a'_0) ({b'_0} ∪ Ω.interval a'_0 b'_0) ∧
    (∀ z ∈ Ω.bar, z ∉ G₁ → z ∉ G₂ → z ∈ A_arc ∨ z ∈ B_arc) := by
  intro G₁ G₂ A_arc B_arc
  have ha'_0_bar : a'_0 ∈ Ω.bar := hW' ha'_0.2
  have hb'_0_bar : b'_0 ∈ Ω.bar := hW' hb'_0.2
  have ha'_ne_b' : a'_0 ≠ b'_0 :=
    fun h => disjoint_left.mp hfence.2.2.1 ha'_0.1 (h ▸ hb'_0.1)
  have hA_sub_P₁ : A ∩ W' ⊆ {a'_0} ∪ Ω.interval b'_0 a'_0 := by
    intro x hx
    by_cases hxa' : x = a'_0
    · exact Or.inl hxa'
    · exact Or.inr (Ω.mem_interval_rotate_right
        (Ω.mem_interval_of_mem_A_of_disjoint_AB hfence hW' ha'_0 hb_0 hd_ab hx hxa' hb'_0).1)
  have hB_sub_P₂ : B ∩ W' ⊆ {b'_0} ∪ Ω.interval a'_0 b'_0 := by
    intro y hy
    by_cases hyb' : y = b'_0
    · exact Or.inl hyb'
    · exact Or.inr (Ω.mem_interval_rotate_right
        (Ω.mem_interval_of_mem_A_of_disjoint_AB hfence.symm hW' hb'_0 ha_0 hd_ba hy hyb' ha'_0).1)
  have hA_sub : A ∩ W' ⊆ A_arc :=
    fun x hx => ⟨hA_sub_P₁ hx, disjoint_right.mp hd_ba hx.2⟩
  have hB_sub : B ∩ W' ⊆ B_arc :=
    fun y hy => ⟨hB_sub_P₂ hy, disjoint_right.mp hd_ab hy.2⟩
  have hG₂_sub : G₂ ⊆ Ω.interval b'_0 a'_0 := by
    change Ω.interval b'_0 a_0 ⊆ Ω.interval b'_0 a'_0
    rcases hA_sub_P₁ ha_0 with h_eq | ha_0_in
    · rw [mem_singleton_iff.mp h_eq]
    · exact Ω.interval_subset_interval_left ha_0_in
  have hG₁_sub : G₁ ⊆ Ω.interval a'_0 b'_0 := by
    change Ω.interval a'_0 b_0 ⊆ Ω.interval a'_0 b'_0
    rcases hB_sub_P₂ hb_0 with h_eq | hb_0_in
    · rw [mem_singleton_iff.mp h_eq]
    · exact Ω.interval_subset_interval_left hb_0_in
  have hdisj_P : Disjoint ({a'_0} ∪ Ω.interval b'_0 a'_0) ({b'_0} ∪ Ω.interval a'_0 b'_0) := by
    rw [disjoint_left]
    rintro z (hz₁ | hz₁) (hz₂ | hz₂)
    · exact ha'_ne_b' ((mem_singleton_iff.mp hz₁).symm.trans (mem_singleton_iff.mp hz₂))
    · exact Ω.not_mem_interval_left a'_0 b'_0 (mem_singleton_iff.mp hz₁ ▸ hz₂)
    · exact Ω.not_mem_interval_left b'_0 a'_0 (mem_singleton_iff.mp hz₂ ▸ hz₁)
    · exact disjoint_left.mp (Ω.disjoint_interval_swap b'_0 a'_0) hz₁ hz₂
  refine ⟨hA_sub, hB_sub, hG₂_sub, hG₁_sub, hdisj_P, fun z hz_bar hz_not_G₁ hz_not_G₂ => ?_⟩
  by_cases hza' : z = a'_0
  · exact Or.inl ⟨Or.inl hza', hz_not_G₂⟩
  · by_cases hzb' : z = b'_0
    · exact Or.inr ⟨Or.inl hzb', hz_not_G₁⟩
    · rcases Ω.mem_interval_or_interval_swap hb'_0_bar ha'_0_bar hz_bar ha'_ne_b'.symm hzb' hza'
        with hz₁ | hz₂
      · exact Or.inl ⟨Or.inr hz₁, hz_not_G₂⟩
      · exact Or.inr ⟨Or.inr hz₂, hz_not_G₁⟩

/-- Interval fence cutting `G₁ = Ω.interval a'_0 b_0` at `x₁ ∈ G₁`:
`A_f := Ω.interval b'_0 x₁` and `B_f := {b'_0, x₁} ∪ Ω.interval x₁ b'_0` satisfy
`A_arc ∪ G₂ ⊆ A_f` and `B_arc ∪ {x₁} ⊆ B_f`. -/
theorem fence_cut_G₁ {Ω : CyclicPerm α} {A B W' : Set α}
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
      A_arc ⊆ A_f ∧ G₂ ⊆ A_f ∧ B_arc ⊆ B_f ∧ x₁ ∈ B_f := by
  intro G₁ G₂ A_arc B_arc
  obtain ⟨_, _, hG₂_sub, hG₁_sub, _, _⟩ :=
    four_arc_partition hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
  have hb'_0_bar : b'_0 ∈ Ω.bar := hW' hb'_0.2
  have hx₁_bar : x₁ ∈ Ω.bar := hx₁.1.1
  have hx₁_a'b' : x₁ ∈ Ω.interval a'_0 b'_0 := hG₁_sub hx₁
  have hx₁_ne_b' : x₁ ≠ b'_0 := fun h => Ω.not_mem_interval_right a'_0 b'_0 (h ▸ hx₁_a'b')
  have ha'_in_b'x₁ : a'_0 ∈ Ω.interval b'_0 x₁ := Ω.mem_interval_rotate_right hx₁_a'b'
  have hP₁_sub : {a'_0} ∪ Ω.interval b'_0 a'_0 ⊆ Ω.interval b'_0 x₁ := by
    rintro z (rfl | hz)
    · exact ha'_in_b'x₁
    · exact Ω.interval_subset_interval_left ha'_in_b'x₁ hz
  refine ⟨Ω.interval b'_0 x₁, {b'_0, x₁} ∪ Ω.interval x₁ b'_0,
    pair_comm x₁ b'_0 ▸ (Ω.isFence_interval_compl hx₁_bar hb'_0_bar hx₁_ne_b').symm,
    sdiff_subset.trans hP₁_sub, hG₂_sub.trans (subset_union_right.trans hP₁_sub), ?_,
    Or.inl (Or.inr rfl)⟩
  rintro y ⟨rfl | hy_in, hy_not_G₁⟩
  · exact Or.inl (Or.inl rfl)
  · rw [Ω.interval_eq_union_of_mem hx₁_a'b'] at hy_in
    rcases hy_in with (hy_a'x₁ | rfl) | hy_x₁b'
    · exact (hy_not_G₁ (Ω.interval_subset_interval_left hx₁ hy_a'x₁)).elim
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr hy_x₁b'

/-- Interval fence for `u, u' ∈ A_arc` (where `u ∉ W'`):
`A_f := {a_0, a'_0} ∪ Ω.interval a_0 a'_0` and `B_f := Ω.interval a'_0 a_0` satisfy
`A_arc = A_f` and `B_arc ∪ G₁ ∪ G₂ ⊆ B_f`. -/
theorem fence_cut_A_arc {Ω : CyclicPerm α} {A B W' : Set α}
    (hfence : Ω.IsFence A B) (hW' : W' ⊆ Ω.bar)
    {a_0 a'_0 b_0 b'_0 u : α}
    (ha_0 : a_0 ∈ A ∩ W') (ha'_0 : a'_0 ∈ A ∩ W')
    (hb_0 : b_0 ∈ B ∩ W') (hb'_0 : b'_0 ∈ B ∩ W')
    (hd_ab : Disjoint (Ω.interval a'_0 b_0) W')
    (hd_ba : Disjoint (Ω.interval b'_0 a_0) W')
    (hu_in : u ∈ ({a'_0} ∪ Ω.interval b'_0 a'_0) \ Ω.interval b'_0 a_0)
    (hu_not_W' : u ∉ W') :
    let G₁ := Ω.interval a'_0 b_0
    let G₂ := Ω.interval b'_0 a_0
    let A_arc := ({a'_0} ∪ Ω.interval b'_0 a'_0) \ G₂
    let B_arc := ({b'_0} ∪ Ω.interval a'_0 b'_0) \ G₁
    ∃ A_f B_f : Set α, Ω.IsFence A_f B_f ∧
      A_arc ⊆ A_f ∧ B_arc ⊆ B_f ∧ G₁ ⊆ B_f ∧ G₂ ⊆ B_f := by
  intro G₁ G₂ A_arc B_arc
  obtain ⟨hA_sub, _, _, _, hdisj_P, _⟩ :=
    four_arc_partition hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
  have ha_0_bar : a_0 ∈ Ω.bar := hW' ha_0.2
  have ha'_0_bar : a'_0 ∈ Ω.bar := hW' ha'_0.2
  have ha_0_in_P₁ : a_0 ∈ {a'_0} ∪ Ω.interval b'_0 a'_0 := (hA_sub ha_0).1
  have ha_0_ne_a'_0 : a_0 ≠ a'_0 := by
    intro h_eq
    rcases hu_in.1 with rfl | hu_int
    · exact hu_not_W' ha'_0.2
    · exact hu_in.2 (h_eq.symm ▸ hu_int)
  have ha_0_b'a' : a_0 ∈ Ω.interval b'_0 a'_0 :=
    ha_0_in_P₁.resolve_left ha_0_ne_a'_0
  have hP₁_split : Ω.interval b'_0 a'_0 = G₂ ∪ {a_0} ∪ Ω.interval a_0 a'_0 :=
    Ω.interval_eq_union_of_mem ha_0_b'a'
  let A_f := {a_0, a'_0} ∪ Ω.interval a_0 a'_0
  let B_f := Ω.interval a'_0 a_0
  have hfence_f : Ω.IsFence A_f B_f :=
    Ω.isFence_interval_compl ha_0_bar ha'_0_bar ha_0_ne_a'_0
  have hA_arc_eq : A_arc ⊆ A_f := by
    rintro z ⟨rfl | hz_in, hz_not_G₂⟩
    · exact Or.inl (Or.inr rfl)
    · rw [hP₁_split] at hz_in
      rcases hz_in with (hz_G₂ | rfl) | hz_a0a'
      · exact (hz_not_G₂ hz_G₂).elim
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hz_a0a'
  have hA_f_sub_A_arc : A_f ⊆ A_arc := by
    have hdisj_G₂_a0a' : Disjoint G₂ (Ω.interval a_0 a'_0) :=
      (Ω.disjoint_interval_swap a'_0 a_0).mono_left
        (Ω.interval_subset_interval_right (Ω.mem_interval_rotate_right ha_0_b'a'))
    rintro z ((rfl | rfl) | hz_in)
    · exact hA_sub ha_0
    · exact hA_sub ha'_0
    · exact ⟨Or.inr (Ω.interval_subset_interval_right ha_0_b'a' hz_in),
        disjoint_right.mp hdisj_G₂_a0a' hz_in⟩
  have hsub_Bf : ∀ {S_set : Set α}, S_set ⊆ Ω.bar → Disjoint S_set A_arc → S_set ⊆ B_f := by
    intro S_set hS_bar hS_disj z hz
    have hz_union : z ∈ A_f ∪ B_f := hfence_f.2.2.2.1.symm ▸ hS_bar hz
    exact hz_union.resolve_left fun hzA => disjoint_left.mp hS_disj hz (hA_f_sub_A_arc hzA)
  have hB_arc_sub : B_arc ⊆ B_f := by
    apply hsub_Bf
    · rintro z ⟨rfl | hz, _⟩
      · exact hW' hb'_0.2
      · exact hz.1.1
    · exact hdisj_P.symm.mono sdiff_subset sdiff_subset
  have hG₁_sub : G₁ ⊆ B_f := by
    apply hsub_Bf (Ω.interval_subset_bar a'_0 b_0)
    obtain ⟨_, _, _, hG₁_sub_P₂, _, _⟩ :=
      four_arc_partition hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
    exact hdisj_P.symm.mono (hG₁_sub_P₂.trans subset_union_right) sdiff_subset
  have hG₂_sub : G₂ ⊆ B_f :=
    hsub_Bf (Ω.interval_subset_bar b'_0 a_0) disjoint_sdiff_self_right
  exact ⟨A_f, B_f, hfence_f, hA_arc_eq, hB_arc_sub, hG₁_sub, hG₂_sub⟩

private theorem fence_for_two_switches_of_first_nonmember {Ω : CyclicPerm α} {A B W' : Set α}
    (hfence : Ω.IsFence A B) (hW' : W' ⊆ Ω.bar)
    {a_0 a'_0 b_0 b'_0 x₁ x₂ u u' : α}
    (ha_0 : a_0 ∈ A ∩ W') (ha'_0 : a'_0 ∈ A ∩ W')
    (hb_0 : b_0 ∈ B ∩ W') (hb'_0 : b'_0 ∈ B ∩ W')
    (hd_ab : Disjoint (Ω.interval a'_0 b_0) W')
    (hd_ba : Disjoint (Ω.interval b'_0 a_0) W')
    (hx₁ : x₁ ∈ Ω.interval a'_0 b_0)
    (hx₂ : x₂ ∈ Ω.interval b'_0 a_0)
    (hu_bar : u ∈ Ω.bar) (hu_not_W' : u ∉ W')
    (hu_not_G₁ : u ∉ Ω.interval a'_0 b_0) (hu_not_G₂ : u ∉ Ω.interval b'_0 a_0)
    (hu'_bar : u' ∈ Ω.bar)
    (hu'_not_G₁ : u' ∉ Ω.interval a'_0 b_0) (hu'_not_G₂ : u' ∉ Ω.interval b'_0 a_0) :
    ∃ A_f B_f : Set α, Ω.IsFence A_f B_f ∧
      A ∩ W' ⊆ A_f ∧ B ∩ W' ⊆ B_f ∧
      ((u ∈ A_f ∧ x₁ ∈ B_f) ∨ (x₁ ∈ A_f ∧ u ∈ B_f)) ∧
      ((u' ∈ A_f ∧ x₂ ∈ B_f) ∨ (x₂ ∈ A_f ∧ u' ∈ B_f)) := by
  obtain ⟨hA_sub, hB_sub, _, _, _, hpart⟩ :=
    four_arc_partition hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
  have hu_AB := hpart u hu_bar hu_not_G₁ hu_not_G₂
  have hu'_AB := hpart u' hu'_bar hu'_not_G₁ hu'_not_G₂
  rcases hu_AB with huA | huB <;> rcases hu'_AB with hu'A | hu'B
  · -- `u ∈ A_arc` and `u' ∈ A_arc`: use `fence_cut_A_arc`.
    obtain ⟨A_f, B_f, hff, hAf, hBf, hG₁f, hG₂f⟩ :=
      fence_cut_A_arc hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba huA hu_not_W'
    exact ⟨A_f, B_f, hff, hA_sub.trans hAf, hB_sub.trans hBf,
      Or.inl ⟨hAf huA, hG₁f hx₁⟩, Or.inl ⟨hAf hu'A, hG₂f hx₂⟩⟩
  · -- `u ∈ A_arc` and `u' ∈ B_arc`: use `fence_cut_G₁`.
    obtain ⟨A_f, B_f, hff, hAf, hG₂f, hBf, hx₁f⟩ :=
      fence_cut_G₁ hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba hx₁
    exact ⟨A_f, B_f, hff, hA_sub.trans hAf, hB_sub.trans hBf,
      Or.inl ⟨hAf huA, hx₁f⟩, Or.inr ⟨hG₂f hx₂, hBf hu'B⟩⟩
  · -- `u ∈ B_arc` and `u' ∈ A_arc`: apply `fence_cut_G₁` to `(B, A)` at `x₂ ∈ G₂`?
    -- Wait: in `(B, A)` at `x₂ ∈ G₂`, `B_arc` and `G₁` are on one side, and `A_arc` and `{x₂}` on
    -- the other!
    -- Instead, apply `fence_cut_G₁` to `(A, B)`? No: `fence_cut_G₁` puts `A_arc ∪ G₂` in `A_f` and
    -- `B_arc ∪ {x₁}` in `B_f`.
    -- We want `A_arc ∪ {x₁}` in `A_f` and `B_arc ∪ G₂` in `B_f`, which is `A_f := {a_0, x₁} ∪
    -- Ω.interval a_0 x₁` and `B_f := Ω.interval x₁ a_0`!
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
    have hB_arc_sub_Q₂ : ({b'_0} ∪ Ω.interval a'_0 b'_0) \ Ω.interval a'_0 b_0 ⊆
        {b_0} ∪ Ω.interval b_0 a_0 := by
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
    have hA_arc_sub_Af : ({a'_0} ∪ Ω.interval b'_0 a'_0) \ Ω.interval b'_0 a_0 ⊆
        {a_0, x₁} ∪ Ω.interval a_0 x₁ := by
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
        obtain ⟨_, _, _, hG₁_sub_P₂, hdisj_P, _⟩ :=
          four_arc_partition hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
        exact disjoint_left.mp hdisj_P hz_P₁ (Or.inr (hG₁_sub_P₂ hz_G₁))
      · obtain ⟨_, _, _, _, hdisj_P, _⟩ :=
          four_arc_partition hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
        exact disjoint_left.mp hdisj_P hz_P₁ (hB_sub hb_0).1
      · rcases hb'_0_in_b0a0 with h_eq | hb'_in
        · rw [← mem_singleton_iff.mp h_eq] at hz_b0a0
          exact hz_not_G₂ hz_b0a0
        · rw [Ω.interval_eq_union_of_mem hb'_in] at hz_b0a0
          rcases hz_b0a0 with (hz_b0b' | rfl) | hz_G₂
          · obtain ⟨_, _, _, _, hdisj_P, _⟩ :=
              four_arc_partition hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
            have hb_0_in_P₂ : b_0 ∈ {b'_0} ∪ Ω.interval a'_0 b'_0 := (hB_sub hb_0).1
            have hb_0_a'b' : b_0 ∈ Ω.interval a'_0 b'_0 :=
              hb_0_in_P₂.resolve_left fun h => Ω.not_mem_interval_left b_0 a_0 (h ▸ hb'_in)
            exact disjoint_left.mp hdisj_P hz_P₁
              (Or.inr (Ω.interval_subset_interval_right hb_0_a'b' hz_b0b'))
          · obtain ⟨_, _, _, _, hdisj_P, _⟩ :=
              four_arc_partition hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
            exact disjoint_left.mp hdisj_P hz_P₁ (Or.inl rfl)
          · exact hz_not_G₂ hz_G₂
    exact ⟨{a_0, x₁} ∪ Ω.interval a_0 x₁, Ω.interval x₁ a_0, hfence_f,
      hA_sub.trans hA_arc_sub_Af, hB_sub.trans (hB_arc_sub_Q₂.trans hQ₂_sub),
      Or.inr ⟨Or.inl (Or.inr rfl), hQ₂_sub (hB_arc_sub_Q₂ huB)⟩,
      Or.inl ⟨hA_arc_sub_Af hu'A, hQ₂_sub (Or.inr (hG₂_sub_b0a0 hx₂))⟩⟩
  · -- `u ∈ B_arc` and `u' ∈ B_arc`: use `fence_cut_A_arc` on `(B, A)`.
    obtain ⟨B_f, A_f, hff, hBf, hAf, hG₂f, hG₁f⟩ :=
      fence_cut_A_arc hfence.symm hW' hb_0 hb'_0 ha_0 ha'_0 hd_ba hd_ab huB hu_not_W'
    exact ⟨A_f, B_f, hff.symm, hA_sub.trans hAf, hB_sub.trans hBf,
      Or.inr ⟨hG₁f hx₁, hBf huB⟩, Or.inr ⟨hG₂f hx₂, hBf hu'B⟩⟩

/-- Combining the four interval fences: for any `x₁ ∈ G₁`, `x₂ ∈ G₂`, and `u, u' ∈ A_arc ∪ B_arc`
with `u, u' ∉ W'`, there is a fence `(A_f, B_f)` of `Ω` such that `A ∩ W' ⊆ A_f`, `B ∩ W' ⊆ B_f`,
`u` and `x₁` lie on opposite sides of `(A_f, B_f)`, and `u'` and `x₂` lie on opposite sides of
`(A_f, B_f)`. -/
theorem exists_fence_for_two_switches {Ω : CyclicPerm α} {A B W' : Set α}
    (hfence : Ω.IsFence A B) (hW' : W' ⊆ Ω.bar)
    {a_0 a'_0 b_0 b'_0 x₁ x₂ u u' : α}
    (ha_0 : a_0 ∈ A ∩ W') (ha'_0 : a'_0 ∈ A ∩ W')
    (hb_0 : b_0 ∈ B ∩ W') (hb'_0 : b'_0 ∈ B ∩ W')
    (hd_ab : Disjoint (Ω.interval a'_0 b_0) W')
    (hd_ba : Disjoint (Ω.interval b'_0 a_0) W')
    (hx₁ : x₁ ∈ Ω.interval a'_0 b_0)
    (hx₂ : x₂ ∈ Ω.interval b'_0 a_0)
    (hu_bar : u ∈ Ω.bar) (hu_not_W' : u ∉ W')
    (hu_not_G₁ : u ∉ Ω.interval a'_0 b_0) (hu_not_G₂ : u ∉ Ω.interval b'_0 a_0)
    (hu'_bar : u' ∈ Ω.bar) (_hu'_not_W' : u' ∉ W')
    (hu'_not_G₁ : u' ∉ Ω.interval a'_0 b_0) (hu'_not_G₂ : u' ∉ Ω.interval b'_0 a_0) :
    ∃ A_f B_f : Set α, Ω.IsFence A_f B_f ∧
      A ∩ W' ⊆ A_f ∧ B ∩ W' ⊆ B_f ∧
      ((u ∈ A_f ∧ x₁ ∈ B_f) ∨ (x₁ ∈ A_f ∧ u ∈ B_f)) ∧
      ((u' ∈ A_f ∧ x₂ ∈ B_f) ∨ (x₂ ∈ A_f ∧ u' ∈ B_f)) := by
  exact fence_for_two_switches_of_first_nonmember hfence hW' ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
    hx₁ hx₂ hu_bar hu_not_W' hu_not_G₁ hu_not_G₂ hu'_bar hu'_not_G₁ hu'_not_G₂

/-- If `x₁ ∈ G₁ = S.Ω.interval a'_0 b_0` and `u ∈ S.Ω.bar \ (G₁ ∪ {a'_0, b_0})`, then
`b_0 ∈ S.Ω.interval x₁ u` and `a'_0 ∈ S.Ω.interval u x₁`. -/
theorem mem_interval_of_mem_gap_and_not_mem {Ω : CyclicPerm α}
    {a'_0 b_0 x₁ u : α}
    (ha'_0 : a'_0 ∈ Ω.bar) (hb_0 : b_0 ∈ Ω.bar) (hab : a'_0 ≠ b_0)
    (hx₁ : x₁ ∈ Ω.interval a'_0 b_0)
    (hu_bar : u ∈ Ω.bar) (hua' : u ≠ a'_0) (hub : u ≠ b_0)
    (hu_not : u ∉ Ω.interval a'_0 b_0) :
    b_0 ∈ Ω.interval x₁ u ∧ a'_0 ∈ Ω.interval u x₁ := by
  have hu_ba : u ∈ Ω.interval b_0 a'_0 :=
    (Ω.mem_interval_or_interval_swap ha'_0 hb_0 hu_bar hab hua' hub).resolve_left hu_not
  have hcw4 : Ω.IsClockwise4 a'_0 x₁ b_0 u :=
    Ω.isClockwise4_iff_interval.mpr ⟨hx₁, hu_ba⟩
  exact Ω.isClockwise4_iff_interval.mp (Ω.isClockwise4_rotate hcw4)

/-- Any non-exchangeable attachment `P` to a crooked transaction `P_set` with leg `P₁` (an overpass
of `P_set`) has its outer end `u` outside both gap intervals `G₁ = S.Ω.interval a'_0 b_0` and
`G₂ = S.Ω.interval b'_0 a_0`. -/
theorem end_not_mem_gaps_of_not_exchangeable (S : Society α β)
    {P_set : Set (Graph α β)} {A B : Set α}
    (_hcrooked : S.IsCrookedTransaction P_set)
    (hfence : S.IsFenceFor P_set A B)
    {P P₁ : Graph α β} {v u e₁ e₂ a_0 a'_0 b_0 b'_0 : α}
    (hatt : S.IsAttachmentWithEnds P_set P v u)
    (hnot_exch : ¬ S.IsExchangeableAttachment P_set P)
    (hP₁ : P₁ ∈ P_set) (hvP₁ : v ∈ V(P₁))
    (hP₁_ends : S.IsOmegaPathWithEnds P₁ e₁ e₂)
    (W' : Set α) (hW'_def : W' = S.transactionEnds (P_set \ {P₁}))
    (ha_0 : a_0 ∈ A ∩ W') (ha'_0 : a'_0 ∈ A ∩ W')
    (hb_0 : b_0 ∈ B ∩ W') (hb'_0 : b'_0 ∈ B ∩ W')
    (hd_ab : Disjoint (S.Ω.interval a'_0 b_0) W')
    (hd_ba : Disjoint (S.Ω.interval b'_0 a_0) W')
    (he₁ : e₁ ∈ S.Ω.interval a'_0 b_0)
    (he₂ : e₂ ∈ S.Ω.interval b'_0 a_0) :
    u ∉ S.Ω.interval a'_0 b_0 ∧ u ∉ S.Ω.interval b'_0 a_0 := by
  have hW'_bar : W' ⊆ S.Ω.bar := hW'_def ▸ S.transactionEnds_subset_bar (P_set \ {P₁})
  obtain ⟨Q_1', Q_2, _, _, hQ_1', hQ_2, _, _, _⟩ := hP₁_ends.1.exists_split_at hvP₁
  have hQ_1 : IsGraphPathWithEnds P₁ Q_1' v e₁ := hQ_1'.symm
  -- Helper: if a switch `L'` of `P` with end `e ∈ {e₁, e₂}` has one of `{u, e}` in `G₁` and the
  -- other in `G₂`, then `(P_set \ {P₁}) ∪ {L'}` is a crooked transaction, contradicting
  -- `hnot_exch`.
  have hnot_both_gaps : ∀ {Q : Graph α β} {e x₁ x₂ : α},
      (IsGraphPathWithEnds P₁ Q v e₁ ∧ e = e₁ ∨ IsGraphPathWithEnds P₁ Q v e₂ ∧ e = e₂) →
      ({u, e} : Set α) = {x₁, x₂} →
      x₁ ∈ S.Ω.interval a'_0 b_0 → x₂ ∈ S.Ω.interval b'_0 a_0 → False := by
    intro Q e x₁ x₂ hQe hpair hx₁ hx₂
    have hQ : IsGraphPathWithEnds P₁ Q v e := by
      rcases hQe with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> exact h
    have he_or : e = e₁ ∨ e = e₂ := by
      rcases hQe with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    let L' := subgraphUnion S.G P Q
    let P_set' := (P_set \ {P₁}) ∪ {L'}
    have hL'_ends_ue : S.IsOmegaPathWithEnds L' u e :=
      hatt.isOmegaPathWithEnds_subgraphUnion S hP₁ hvP₁ hP₁_ends hQ he_or
    have hL'_ends : S.IsOmegaPathWithEnds L' x₂ x₁ := by
      have hx₂_in : x₂ ∈ ({u, e} : Set α) := by rw [hpair]; simp
      have hx₁_in : x₁ ∈ ({u, e} : Set α) := by rw [hpair]; simp
      obtain ⟨_, _, _, hG₁_sub, hdisj_P, _⟩ :=
        four_arc_partition hfence.2.1 hW'_bar ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
      obtain ⟨_, _, hG₂_sub, _, _, _⟩ :=
        four_arc_partition hfence.2.1 hW'_bar ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
      have hx12 : x₁ ≠ x₂ := fun h =>
        disjoint_left.mp hdisj_P (Or.inr (hG₂_sub hx₂)) (h ▸ Or.inr (hG₁_sub hx₁))
      rcases hx₂_in with rfl | rfl <;> rcases hx₁_in with rfl | rfl
      · exact (hx12 rfl).elim
      · exact hL'_ends_ue
      · exact hL'_ends_ue.symm S
      · exact (hx12 rfl).elim
    obtain ⟨A_f, B_f, hff, hAf, hG₂f, hBf, hx₁f⟩ :=
      fence_cut_G₁ hfence.2.1 hW'_bar ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba hx₁
    obtain ⟨hA_sub, hB_sub, _, _, _, _⟩ :=
      four_arc_partition hfence.2.1 hW'_bar ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
    have hdisj' : S.IsDisjointOmegaPathSet P_set' :=
      hatt.isDisjointOmegaPathSet_switch S hfence.1 hP₁ hvP₁ hP₁_ends hQ he_or
    have hfence' : S.IsFenceFor P_set' A_f B_f := by
      refine ⟨hdisj', hff, ?_⟩
      rintro R (hR | rfl)
      · obtain ⟨a_R, ha_R, b_R, hb_R, hR_ends⟩ := hfence.2.2 R hR.1
        have ha_R_W' : a_R ∈ A ∩ W' := ⟨ha_R, hW'_def ▸ hR_ends.mem_transactionEnds_left S hR⟩
        have hb_R_W' : b_R ∈ B ∩ W' := ⟨hb_R, hW'_def ▸ hR_ends.mem_transactionEnds_right S hR⟩
        exact ⟨a_R, hAf (hA_sub ha_R_W'), b_R, hBf (hB_sub hb_R_W'), hR_ends⟩
      · exact ⟨x₂, hG₂f hx₂, x₁, hx₁f, hL'_ends⟩
    have hW'_sub_ends : W' ⊆ S.transactionEnds P_set' := by
      rw [hW'_def, hatt.transactionEnds_switch S hP₁ hvP₁ hP₁_ends hQ he_or]
      exact subset_union_left
    have hx₁_mem_ends : x₁ ∈ S.transactionEnds P_set' :=
      hL'_ends.mem_transactionEnds_right S (Or.inr rfl)
    have hx₂_mem_ends : x₂ ∈ S.transactionEnds P_set' :=
      hL'_ends.mem_transactionEnds_left S (Or.inr rfl)
    have hcr' : S.IsCrookedTransaction P_set' := by
      refine ⟨⟨A_f, B_f, hfence'⟩, ?_⟩
      rintro R (hR | rfl) hper
      · obtain ⟨a_R, ha_R, b_R, hb_R, hR_ends⟩ := hfence.2.2 R hR.1
        have ha_R_W' : a_R ∈ A ∩ W' := ⟨ha_R, hW'_def ▸ hR_ends.mem_transactionEnds_left S hR⟩
        have hb_R_W' : b_R ∈ B ∩ W' := ⟨hb_R, hW'_def ▸ hR_ends.mem_transactionEnds_right S hR⟩
        have hper' := (hR_ends.isPeripheralIn_iff S (Or.inl hR)).mp hper
        rcases hper' with hd₁ | hd₂
        · have hsub₁ := S.Ω.interval_subset_of_disjoint_AB hfence.2.1 hW'_bar
            ha'_0 hb_0 hd_ab ha_R_W' hb_R_W'
          exact disjoint_left.mp hd₁ (hsub₁ hx₁) hx₁_mem_ends
        · have hsub₂ := S.Ω.interval_subset_of_disjoint_AB hfence.2.1.symm hW'_bar
            hb'_0 ha_0 hd_ba hb_R_W' ha_R_W'
          exact disjoint_left.mp hd₂ (hsub₂ hx₂) hx₂_mem_ends
      · have hper' := (hL'_ends.isPeripheralIn_iff S (Or.inr rfl)).mp hper
        obtain ⟨_, _, hG₂_sub, hG₁_sub, hdisj_P, _⟩ :=
          four_arc_partition hfence.2.1 hW'_bar ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
        have hx₂_not_G₁ : x₂ ∉ S.Ω.interval a'_0 b_0 := fun h =>
          disjoint_left.mp hdisj_P (Or.inr (hG₂_sub hx₂)) (Or.inr (hG₁_sub h))
        have hx₂_ne_a' : x₂ ≠ a'_0 := fun h =>
          S.Ω.not_mem_interval_right b'_0 a'_0 (h ▸ hG₂_sub hx₂)
        have hx₂_ne_b : x₂ ≠ b_0 := fun h =>
          disjoint_right.mp hd_ba hb_0.2 (h ▸ hx₂)
        have ha'_ne_b : a'_0 ≠ b_0 := fun h =>
          disjoint_left.mp hfence.2.1.2.2.1 ha'_0.1 (h ▸ hb_0.1)
        have h_in := mem_interval_of_mem_gap_and_not_mem
          (hW'_bar ha'_0.2) (hW'_bar hb_0.2) ha'_ne_b hx₁ hx₂.1.1 hx₂_ne_a' hx₂_ne_b hx₂_not_G₁
        rcases hper' with hd₁ | hd₂
        · exact disjoint_left.mp hd₁ h_in.2 (hW'_sub_ends ha'_0.2)
        · exact disjoint_left.mp hd₂ h_in.1 (hW'_sub_ends hb_0.2)
    have hsw : S.IsSwitch P_set P P₁ L' := by
      refine ⟨hP₁, v, u, e₁, e₂, hatt, hvP₁, hP₁_ends, Q, ?_, rfl⟩
      rcases hQe with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    exact hnot_exch ⟨⟨v, u, hatt⟩, P₁, L', hsw, hcr'⟩
  refine ⟨fun hu_G₁ => ?_, fun hu_G₂ => ?_⟩
  · exact hnot_both_gaps (Or.inr ⟨hQ_2, rfl⟩) rfl hu_G₁ he₂
  · exact hnot_both_gaps (Or.inl ⟨hQ_1, rfl⟩) (pair_comm u e₁) he₁ hu_G₂

private theorem exists_overpass_gaps (S : Society α β)
    {P_set : Set (Graph α β)} {P₁ : Graph α β} {A B : Set α}
    (hcrooked : S.IsCrookedTransaction P_set) (hfence : S.IsFenceFor P_set A B)
    (hP₁_in : P₁ ∈ P_set) (hover : S.IsOverpass P_set P₁) :
    let W' := S.transactionEnds (P_set \ {P₁})
    ∃ a₀ ∈ A ∩ W', ∃ a'₀ ∈ A ∩ W', ∃ b₀ ∈ B ∩ W', ∃ b'₀ ∈ B ∩ W',
      Disjoint (S.Ω.interval a'₀ b₀) W' ∧ Disjoint (S.Ω.interval b'₀ a₀) W' ∧
      ∃ e₁ e₂, S.IsOmegaPathWithEnds P₁ e₁ e₂ ∧
        e₁ ∈ S.Ω.interval a'₀ b₀ ∧ e₂ ∈ S.Ω.interval b'₀ a₀ := by
  obtain ⟨a₁_raw, ha₁_raw, b₁_raw, hb₁_raw, hP₁_ends_raw⟩ := hfence.2.2 P₁ hP₁_in
  rcases hover with ⟨_, _, R₁, hR₁_in, R₂, hR₂_in, hR12, hper₁, hper₂⟩
  obtain ⟨x₁, hx₁, y₁, hy₁, hR₁_ends⟩ := hfence.2.2 R₁ hR₁_in.1
  obtain ⟨x₂, hx₂, y₂, hy₂, hR₂_ends⟩ := hfence.2.2 R₂ hR₂_in.1
  let W' := S.transactionEnds (P_set \ {P₁})
  have hW'_bar : W' ⊆ S.Ω.bar := S.transactionEnds_subset_bar (P_set \ {P₁})
  have hx₁W' : x₁ ∈ A ∩ W' := ⟨hx₁, hR₁_ends.mem_transactionEnds_left S hR₁_in⟩
  have hy₁W' : y₁ ∈ B ∩ W' := ⟨hy₁, hR₁_ends.mem_transactionEnds_right S hR₁_in⟩
  have hx₂W' : x₂ ∈ A ∩ W' := ⟨hx₂, hR₂_ends.mem_transactionEnds_left S hR₂_in⟩
  have hy₂W' : y₂ ∈ B ∩ W' := ⟨hy₂, hR₂_ends.mem_transactionEnds_right S hR₂_in⟩
  have hper₁' := (hR₁_ends.isPeripheralIn_iff S hR₁_in).mp hper₁
  have hper₂' := (hR₂_ends.isPeripheralIn_iff S hR₂_in).mp hper₂
  have hdisj_R12 : Disjoint V(R₁) V(R₂) := hfence.1.2 hR₁_in.1 hR₂_in.1 hR12
  have hx12 : x₁ ≠ x₂ := fun h => disjoint_left.mp hdisj_R12 hR₁_ends.1.left_mem
    (h ▸ hR₂_ends.1.left_mem)
  have hy12 : y₁ ≠ y₂ := fun h => disjoint_left.mp hdisj_R12 hR₁_ends.1.right_mem
    (h ▸ hR₂_ends.1.right_mem)
  have hex_boundary :
      ∃ a_0 ∈ A ∩ W', ∃ a'_0 ∈ A ∩ W', ∃ b_0 ∈ B ∩ W', ∃ b'_0 ∈ B ∩ W',
        Disjoint (S.Ω.interval a'_0 b_0) W' ∧ Disjoint (S.Ω.interval b'_0 a_0) W' := by
    rcases hper₁' with hd₁ | hd₁ <;> rcases hper₂' with hd₂ | hd₂
    · exfalso
      exact hx12 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW'_bar hx₁W' hy₁W' hx₂W'
        hy₂W' hd₁ hd₂).1
    · exact ⟨x₂, hx₂W', x₁, hx₁W', y₁, hy₁W', y₂, hy₂W', hd₁, hd₂⟩
    · exact ⟨x₁, hx₁W', x₂, hx₂W', y₂, hy₂W', y₁, hy₁W', hd₂, hd₁⟩
    · exfalso
      exact hy12 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW'_bar hy₁W' hx₁W' hy₂W'
        hx₂W' hd₁ hd₂).1
  obtain ⟨a_0, ha_0, a'_0, ha'_0, b_0, hb_0, b'_0, hb'_0, hd_ab, hd_ba⟩ := hex_boundary
  -- One end `e₁` of `P₁` lies in `G₁ = S.Ω.interval a'_0 b_0` and the other `e₂` lies in
  -- `G₂ = S.Ω.interval b'_0 a_0`.
  have hR_ab : ∃ R_ab ∈ P_set \ {P₁}, S.IsOmegaPathWithEnds R_ab a'_0 b_0 := by
    rcases hper₁' with hd₁ | hd₁
    · obtain ⟨rfl, rfl⟩ := S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW'_bar
        ha'_0 hb_0 hx₁W' hy₁W' hd_ab hd₁
      exact ⟨R₁, hR₁_in, hR₁_ends⟩
    · rcases hper₂' with hd₂ | hd₂
      · obtain ⟨rfl, rfl⟩ := S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW'_bar
          ha'_0 hb_0 hx₂W' hy₂W' hd_ab hd₂
        exact ⟨R₂, hR₂_in, hR₂_ends⟩
      · exfalso
        exact hy12 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW'_bar
          hy₁W' hx₁W' hy₂W' hx₂W' hd₁ hd₂).1
  have hR_ba : ∃ R_ba ∈ P_set \ {P₁}, S.IsOmegaPathWithEnds R_ba a_0 b'_0 := by
    rcases hper₁' with hd₁ | hd₁
    · rcases hper₂' with hd₂ | hd₂
      · exfalso
        exact hx12 (S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1 hW'_bar
          hx₁W' hy₁W' hx₂W' hy₂W' hd₁ hd₂).1
      · obtain ⟨rfl, rfl⟩ := S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW'_bar
          hb'_0 ha_0 hy₂W' hx₂W' hd_ba hd₂
        exact ⟨R₂, hR₂_in, hR₂_ends⟩
    · obtain ⟨rfl, rfl⟩ := S.Ω.unique_empty_interval_AB_of_isFence hfence.2.1.symm hW'_bar
        hb'_0 ha_0 hy₁W' hx₁W' hd_ba hd₁
      exact ⟨R₁, hR₁_in, hR₁_ends⟩
  obtain ⟨R_ab, hR_ab_in, hR_ab_ends⟩ := hR_ab
  obtain ⟨R_ba, hR_ba_in, hR_ba_ends⟩ := hR_ba
  have h_e_G₁ := S.mem_interval_of_peripheral_diff_singleton hfence hcrooked hP₁_in hR_ab_in
    ha₁_raw hb₁_raw hP₁_ends_raw ha'_0.1 hb_0.1 hR_ab_ends hd_ab
  have hfence_BA : S.IsFenceFor P_set B A :=
    ⟨hfence.1, hfence.2.1.symm, fun R hR => by
      obtain ⟨a, ha, b_e, hb_e, hR_e⟩ := hfence.2.2 R hR
      exact ⟨b_e, hb_e, a, ha, hR_e.symm S⟩⟩
  have h_e_G₂ := S.mem_interval_of_peripheral_diff_singleton hfence_BA hcrooked hP₁_in hR_ba_in
    hb₁_raw ha₁_raw (hP₁_ends_raw.symm S) hb'_0.1 ha_0.1 (hR_ba_ends.symm S) hd_ba
  obtain ⟨_, _, hG₂_sub, hG₁_sub, hdisj_P, _⟩ :=
    four_arc_partition hfence.2.1 hW'_bar ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
  have hdisj_G₁G₂ : Disjoint (S.Ω.interval a'_0 b_0) (S.Ω.interval b'_0 a_0) :=
    hdisj_P.symm.mono (hG₁_sub.trans subset_union_right) (hG₂_sub.trans subset_union_right)
  have hex_ends : ∃ e₁ e₂ : α,
      S.IsOmegaPathWithEnds P₁ e₁ e₂ ∧
      e₁ ∈ S.Ω.interval a'_0 b_0 ∧ e₂ ∈ S.Ω.interval b'_0 a_0 := by
    rcases h_e_G₁ with ⟨ha₁_G₁, _⟩ | ⟨hb₁_G₁, _⟩ <;>
    rcases h_e_G₂ with ⟨hb₁_G₂, _⟩ | ⟨ha₁_G₂, _⟩
    · exact ⟨a₁_raw, b₁_raw, hP₁_ends_raw, ha₁_G₁, hb₁_G₂⟩
    · exact (disjoint_left.mp hdisj_G₁G₂ ha₁_G₁ ha₁_G₂).elim
    · exact (disjoint_left.mp hdisj_G₁G₂ hb₁_G₁ hb₁_G₂).elim
    · exact ⟨b₁_raw, a₁_raw, hP₁_ends_raw.symm S, hb₁_G₁, ha₁_G₂⟩
  obtain ⟨e₁, e₂, hP₁_ends, he₁_G₁, he₂_G₂⟩ := hex_ends
  exact ⟨a_0, ha_0, a'_0, ha'_0, b_0, hb_0, b'_0, hb'_0, hd_ab, hd_ba, e₁, e₂,
    hP₁_ends, he₁_G₁, he₂_G₂⟩

/-- Replacing one path by two disjoint switches across its gaps preserves crookedness. -/
theorem crookedTransaction_of_two_switches (S : Society α β)
    {P_set : Set (Graph α β)} {P₁ L₁ L₂ : Graph α β} {A B : Set α}
    {a_0 a'_0 b_0 b'_0 e₁ e₂ u₁ u₂ : α}
    (hfence : S.IsFenceFor P_set A B)
    (ha_0 : a_0 ∈ A ∩ S.transactionEnds (P_set \ {P₁}))
    (ha'_0 : a'_0 ∈ A ∩ S.transactionEnds (P_set \ {P₁}))
    (hb_0 : b_0 ∈ B ∩ S.transactionEnds (P_set \ {P₁}))
    (hb'_0 : b'_0 ∈ B ∩ S.transactionEnds (P_set \ {P₁}))
    (hd_ab : Disjoint (S.Ω.interval a'_0 b_0) (S.transactionEnds (P_set \ {P₁})))
    (hd_ba : Disjoint (S.Ω.interval b'_0 a_0) (S.transactionEnds (P_set \ {P₁})))
    (he₁_G₁ : e₁ ∈ S.Ω.interval a'_0 b_0) (he₂_G₂ : e₂ ∈ S.Ω.interval b'_0 a_0)
    (hdisj_L12 : Disjoint V(L₁) V(L₂))
    (hdisj_LR : ∀ R ∈ P_set \ {P₁}, Disjoint V(L₁) V(R) ∧ Disjoint V(L₂) V(R))
    (hL₁_ends : S.IsOmegaPathWithEnds L₁ u₁ e₁)
    (hL₂_ends : S.IsOmegaPathWithEnds L₂ u₂ e₂)
    (hu₁_bar : u₁ ∈ S.Ω.bar) (hu₁_not_W' : u₁ ∉ S.transactionEnds (P_set \ {P₁}))
    (hu₁_G₁ : u₁ ∉ S.Ω.interval a'_0 b_0) (hu₁_G₂ : u₁ ∉ S.Ω.interval b'_0 a_0)
    (hu₂_bar : u₂ ∈ S.Ω.bar) (hu₂_not_W' : u₂ ∉ S.transactionEnds (P_set \ {P₁}))
    (hu₂_G₁ : u₂ ∉ S.Ω.interval a'_0 b_0) (hu₂_G₂ : u₂ ∉ S.Ω.interval b'_0 a_0) :
    S.IsCrookedTransaction ((P_set \ {P₁}) ∪ {L₁, L₂}) := by
  let W' := S.transactionEnds (P_set \ {P₁})
  have hW'_bar : W' ⊆ S.Ω.bar := S.transactionEnds_subset_bar (P_set \ {P₁})
  let P_set'' := (P_set \ {P₁}) ∪ {L₁, L₂}
  obtain ⟨A_f, B_f, hff, hAf, hBf, h_u₁e₁, h_u₂e₂⟩ :=
    fence_for_two_switches_of_first_nonmember hfence.2.1 hW'_bar ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
      he₁_G₁ he₂_G₂ hu₁_bar hu₁_not_W' hu₁_G₁ hu₁_G₂ hu₂_bar hu₂_G₁ hu₂_G₂
  have hdisj'' : S.IsDisjointOmegaPathSet P_set'' := by
    refine ⟨?_, ?_⟩
    · rintro R (hR | rfl | rfl)
      · exact hfence.1.1 R hR.1
      · exact ⟨u₁, e₁, hL₁_ends⟩
      · exact ⟨u₂, e₂, hL₂_ends⟩
    · rintro M₁ (hM₁ | rfl | rfl) M₂ (hM₂ | rfl | rfl) hne
      · exact hfence.1.2 hM₁.1 hM₂.1 hne
      · exact (hdisj_LR M₁ hM₁).1.symm
      · exact (hdisj_LR M₁ hM₁).2.symm
      · exact (hdisj_LR M₂ hM₂).1
      · exact (hne rfl).elim
      · exact hdisj_L12
      · exact (hdisj_LR M₂ hM₂).2
      · exact hdisj_L12.symm
      · exact (hne rfl).elim
  have hfence'' : S.IsFenceFor P_set'' A_f B_f := by
    refine ⟨hdisj'', hff, ?_⟩
    rintro R (hR | rfl | rfl)
    · obtain ⟨a_R, ha_R, b_R, hb_R, hR_ends⟩ := hfence.2.2 R hR.1
      have ha_R_W' : a_R ∈ A ∩ W' := ⟨ha_R, hR_ends.mem_transactionEnds_left S hR⟩
      have hb_R_W' : b_R ∈ B ∩ W' := ⟨hb_R, hR_ends.mem_transactionEnds_right S hR⟩
      exact ⟨a_R, hAf ha_R_W', b_R, hBf hb_R_W', hR_ends⟩
    · rcases h_u₁e₁ with ⟨hu₁A, he₁B⟩ | ⟨he₁A, hu₁B⟩
      · exact ⟨u₁, hu₁A, e₁, he₁B, hL₁_ends⟩
      · exact ⟨e₁, he₁A, u₁, hu₁B, hL₁_ends.symm S⟩
    · rcases h_u₂e₂ with ⟨hu₂A, he₂B⟩ | ⟨he₂A, hu₂B⟩
      · exact ⟨u₂, hu₂A, e₂, he₂B, hL₂_ends⟩
      · exact ⟨e₂, he₂A, u₂, hu₂B, hL₂_ends.symm S⟩
  have hW'_sub_ends : W' ⊆ S.transactionEnds P_set'' :=
    fun z ⟨R, hR, y, hR_e⟩ => ⟨R, Or.inl hR, y, hR_e⟩
  have he₁_mem_ends : e₁ ∈ S.transactionEnds P_set'' :=
    hL₁_ends.mem_transactionEnds_right S (Or.inr (Or.inl rfl))
  have he₂_mem_ends : e₂ ∈ S.transactionEnds P_set'' :=
    hL₂_ends.mem_transactionEnds_right S (Or.inr (Or.inr rfl))
  refine ⟨⟨A_f, B_f, hfence''⟩, ?_⟩
  rintro R (hR | rfl | rfl) hper
  · obtain ⟨a_R, ha_R, b_R, hb_R, hR_ends⟩ := hfence.2.2 R hR.1
    have ha_R_W' : a_R ∈ A ∩ W' := ⟨ha_R, hR_ends.mem_transactionEnds_left S hR⟩
    have hb_R_W' : b_R ∈ B ∩ W' := ⟨hb_R, hR_ends.mem_transactionEnds_right S hR⟩
    have hper' := (hR_ends.isPeripheralIn_iff S (Or.inl hR)).mp hper
    rcases hper' with hd₁ | hd₂
    · have hsub₁ := S.Ω.interval_subset_of_disjoint_AB hfence.2.1 hW'_bar
        ha'_0 hb_0 hd_ab ha_R_W' hb_R_W'
      exact disjoint_left.mp hd₁ (hsub₁ he₁_G₁) he₁_mem_ends
    · have hsub₂ := S.Ω.interval_subset_of_disjoint_AB hfence.2.1.symm hW'_bar
        hb'_0 ha_0 hd_ba hb_R_W' ha_R_W'
      exact disjoint_left.mp hd₂ (hsub₂ he₂_G₂) he₂_mem_ends
  · have hper' := (hL₁_ends.isPeripheralIn_iff S (Or.inr (Or.inl rfl))).mp hper
    have ha'_ne_b : a'_0 ≠ b_0 := fun h =>
      disjoint_left.mp hfence.2.1.2.2.1 ha'_0.1 (h ▸ hb_0.1)
    have hu₁_ne_a' : u₁ ≠ a'_0 := fun h => hu₁_not_W' (h ▸ ha'_0.2)
    have hu₁_ne_b : u₁ ≠ b_0 := fun h => hu₁_not_W' (h ▸ hb_0.2)
    have h_in := mem_interval_of_mem_gap_and_not_mem
      (hW'_bar ha'_0.2) (hW'_bar hb_0.2) ha'_ne_b he₁_G₁ hu₁_bar hu₁_ne_a' hu₁_ne_b hu₁_G₁
    rcases hper' with hd₁ | hd₂
    · exact disjoint_left.mp hd₁ h_in.2 (hW'_sub_ends ha'_0.2)
    · exact disjoint_left.mp hd₂ h_in.1 (hW'_sub_ends hb_0.2)
  · have hper' := (hL₂_ends.isPeripheralIn_iff S (Or.inr (Or.inr rfl))).mp hper
    have hb'_ne_a : b'_0 ≠ a_0 := fun h =>
      disjoint_left.mp hfence.2.1.2.2.1 ha_0.1 (h ▸ hb'_0.1)
    have hu₂_ne_b' : u₂ ≠ b'_0 := fun h => hu₂_not_W' (h ▸ hb'_0.2)
    have hu₂_ne_a : u₂ ≠ a_0 := fun h => hu₂_not_W' (h ▸ ha_0.2)
    have h_in := mem_interval_of_mem_gap_and_not_mem
      (hW'_bar hb'_0.2) (hW'_bar ha_0.2) hb'_ne_a he₂_G₂ hu₂_bar hu₂_ne_b' hu₂_ne_a hu₂_G₂
    rcases hper' with hd₁ | hd₂
    · exact disjoint_left.mp hd₁ h_in.2 (hW'_sub_ends hb'_0.2)
    · exact disjoint_left.mp hd₂ h_in.1 (hW'_sub_ends ha_0.2)

/-- **Graph Minors IX, (3.3)** (page 48):
"Let $\mathscr{P}$ be a crooked transaction in $(G, \Omega)$. If $P$ and $P'$ are both
non-exchangeable attachments to $\mathscr{P}$ and $P, P'$ are disjoint, then there is a
crooked transaction $\mathscr{P}'$ with $|\mathscr{P}'| = |\mathscr{P}| + 1$ and* $$ \bigcup
\mathscr{P}' \subseteq \bigcup \mathscr{P} \cup (P \cup P'). $$ *Moreover, the two
attachments have a common leg, which is an overpass of $\mathscr{P}$, and no edge of this
leg between the two feet is in $\bigcup \mathscr{P}'$." -/
theorem theorem_3_3_proof (S : Society α β)
    {P_set : Set (Graph α β)} {P P' : Graph α β}
    (hcrooked : S.IsCrookedTransaction P_set)
    (hatt : S.IsAttachment P_set P)
    (hnot_exch : ¬ S.IsExchangeableAttachment P_set P)
    (hatt' : S.IsAttachment P_set P')
    (hnot_exch' : ¬ S.IsExchangeableAttachment P_set P')
    (hdisj_PP' : Disjoint V(P) V(P')) :
    ∃ P₁ ∈ P_set,
      S.IsOverpass P_set P₁ ∧
      S.IsLeg P_set P P₁ ∧
      S.IsLeg P_set P' P₁ ∧
      ∃ b b' : α,
        S.IsFoot P_set P b ∧ b ∈ V(P₁) ∧
        S.IsFoot P_set P' b' ∧ b' ∈ V(P₁) ∧
        ∃ M : Graph α β,
          M ≤ P₁ ∧ IsGraphPathWithEnds P₁ M b b' ∧
          ∃ P_set' : Set (Graph α β),
            S.IsCrookedTransaction P_set' ∧
            P_set'.ncard = P_set.ncard + 1 ∧
            S.transactionUnion P_set' ≤
              subgraphUnion S.G (S.transactionUnion P_set) (subgraphUnion S.G P P') ∧
            Disjoint E(M) E(S.transactionUnion P_set') := by
  -- By (3.2) and (3.1), `P` and `P'` have a common leg `P₁` which is an overpass of `P_set`.
  obtain ⟨_, P₁, hleg, hover⟩ := S.theorem_3_2_proof hcrooked hatt hnot_exch
  obtain ⟨_, P₁', hleg', hover'⟩ := S.theorem_3_2_proof hcrooked hatt' hnot_exch'
  have hP₁_eq : P₁' = P₁ := S.theorem_3_1_proof hcrooked hover' hover
  rw [hP₁_eq] at hleg'
  rcases hleg with ⟨hP₁_in, b, ⟨u, hatt_bu⟩, hbP₁⟩
  rcases hleg' with ⟨_, b', ⟨u', hatt'_b'u'⟩, hb'P₁⟩
  have hbb' : b ≠ b' :=
    fun h => disjoint_left.mp hdisj_PP' hatt_bu.1.left_mem (h ▸ hatt'_b'u'.1.left_mem)
  refine ⟨P₁, hP₁_in, hover,
    ⟨hP₁_in, b, ⟨u, hatt_bu⟩, hbP₁⟩,
    ⟨hP₁_in, b', ⟨u', hatt'_b'u'⟩, hb'P₁⟩,
    b, b', ⟨u, hatt_bu⟩, hbP₁, ⟨u', hatt'_b'u'⟩, hb'P₁, ?_⟩
  -- Unpack the fence `(A, B)` for `P_set` and the two peripheral members of `P_set \ {P₁}`.
  obtain ⟨A, B, hfence⟩ := hcrooked.1
  let W' := S.transactionEnds (P_set \ {P₁})
  obtain ⟨a_0, ha_0, a'_0, ha'_0, b_0, hb_0, b'_0, hb'_0, hd_ab, hd_ba, e₁, e₂,
    hP₁_ends, he₁_G₁, he₂_G₂⟩ :=
    exists_overpass_gaps S hcrooked hfence hP₁_in hover
  -- By `end_not_mem_gaps_of_not_exchangeable`, neither `u` nor `u'` lies in `G₁ ∪ G₂`.
  have hu_gaps := S.end_not_mem_gaps_of_not_exchangeable hcrooked hfence hatt_bu hnot_exch
    hP₁_in hbP₁ hP₁_ends W' rfl ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba he₁_G₁ he₂_G₂
  have hu'_gaps := S.end_not_mem_gaps_of_not_exchangeable hcrooked hfence hatt'_b'u' hnot_exch'
    hP₁_in hb'P₁ hP₁_ends W' rfl ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba he₁_G₁ he₂_G₂
  -- Split `P₁` at `b` and `b'`.
  obtain ⟨Q₁, Q₂, M, hQ₁P₁, hQ₂P₁, hMP₁, hM_path, hQ_ends_or, hdisj_Q12, hdisj_MQ₁, hdisj_MQ₂⟩ :=
    hP₁_ends.1.exists_two_point_split hbP₁ hb'P₁ hbb'
  refine ⟨M, hMP₁, hM_path, ?_⟩
  let S_sw := subgraphUnion S.G P Q₁
  let T_sw := subgraphUnion S.G P' Q₂
  let P_set' := (P_set \ {P₁}) ∪ {S_sw, T_sw}
  have hdisj_ST : Disjoint V(S_sw) V(T_sw) := by
    rw [vertexSet_subgraphUnion, vertexSet_subgraphUnion,
      disjoint_union_left, disjoint_union_right, disjoint_union_right]
    refine ⟨⟨hdisj_PP', ?_⟩, ⟨?_, hdisj_Q12⟩⟩
    · rw [disjoint_left]
      intro z hzP hzQ₂
      have hzb : z = b := by
        have hz_inter : z ∈ V(P) ∩ V(P₁) := ⟨hzP, hQ₂P₁.vertexSet_mono hzQ₂⟩
        rwa [hatt_bu.inter_leg_eq_singleton S hP₁_in hbP₁, mem_singleton_iff] at hz_inter
      rw [hzb] at hzQ₂
      have hbQ₁ : b ∈ V(Q₁) := by
        rcases hQ_ends_or with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact h1.left_mem
      exact disjoint_left.mp hdisj_Q12 hbQ₁ hzQ₂
    · rw [disjoint_left]
      intro z hzQ₁ hzP'
      have hzb' : z = b' := by
        have hz_inter : z ∈ V(P') ∩ V(P₁) := ⟨hzP', hQ₁P₁.vertexSet_mono hzQ₁⟩
        rwa [hatt'_b'u'.inter_leg_eq_singleton S hP₁_in hb'P₁, mem_singleton_iff] at hz_inter
      rw [hzb'] at hzQ₁
      have hb'Q₂ : b' ∈ V(Q₂) := by
        rcases hQ_ends_or with ⟨_, h2⟩ | ⟨_, h2⟩ <;> exact h2.left_mem
      exact disjoint_left.mp hdisj_Q12 hzQ₁ hb'Q₂
  -- Helper that proves `P_set'` is a crooked transaction once we know which switch ends at `e₁` and
  -- which ends at `e₂`.
  have hcrooked_P_set' : S.IsCrookedTransaction P_set' := by
    have hu_not_W' : u ∉ W' := fun huW' =>
      hatt_bu.end_not_mem_transactionEnds S (by
        rw [hfence.transactionEnds_eq_union S hP₁_in hP₁_ends]
        exact Or.inl huW')
    have hu'_not_W' : u' ∉ W' := fun hu'W' =>
      hatt'_b'u'.end_not_mem_transactionEnds S (by
        rw [hfence.transactionEnds_eq_union S hP₁_in hP₁_ends]
        exact Or.inl hu'W')
    have hdisj_ST_R : ∀ R ∈ P_set \ {P₁}, Disjoint V(S_sw) V(R) ∧ Disjoint V(T_sw) V(R) :=
      fun R hR =>
        ⟨hatt_bu.disjoint_subgraphUnion_of_ne_leg S hfence.1 hP₁_in hbP₁ hQ₁P₁ hR.1 hR.2,
          hatt'_b'u'.disjoint_subgraphUnion_of_ne_leg S hfence.1 hP₁_in hb'P₁ hQ₂P₁ hR.1 hR.2⟩
    rcases hQ_ends_or with ⟨hQ₁_e₁, hQ₂_e₂⟩ | ⟨hQ₁_e₂, hQ₂_e₁⟩
    · have hS_ends : S.IsOmegaPathWithEnds S_sw u e₁ :=
        hatt_bu.isOmegaPathWithEnds_subgraphUnion S hP₁_in hbP₁ hP₁_ends hQ₁_e₁ (Or.inl rfl)
      have hT_ends : S.IsOmegaPathWithEnds T_sw u' e₂ :=
        hatt'_b'u'.isOmegaPathWithEnds_subgraphUnion S hP₁_in hb'P₁ hP₁_ends hQ₂_e₂ (Or.inr rfl)
      exact crookedTransaction_of_two_switches S hfence ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
        he₁_G₁ he₂_G₂ hdisj_ST hdisj_ST_R hS_ends hT_ends
        (hatt_bu.end_mem_bar S) hu_not_W' hu_gaps.1 hu_gaps.2
        (hatt'_b'u'.end_mem_bar S) hu'_not_W' hu'_gaps.1 hu'_gaps.2
    · have hS_ends : S.IsOmegaPathWithEnds S_sw u e₂ :=
        hatt_bu.isOmegaPathWithEnds_subgraphUnion S hP₁_in hbP₁ hP₁_ends hQ₁_e₂ (Or.inr rfl)
      have hT_ends : S.IsOmegaPathWithEnds T_sw u' e₁ :=
        hatt'_b'u'.isOmegaPathWithEnds_subgraphUnion S hP₁_in hb'P₁ hP₁_ends hQ₂_e₁ (Or.inl rfl)
      have hpair : ({S_sw, T_sw} : Set (Graph α β)) = {T_sw, S_sw} := pair_comm S_sw T_sw
      have hset_eq : P_set' = (P_set \ {P₁}) ∪ {T_sw, S_sw} := by rw [← hpair]
      rw [hset_eq]
      exact crookedTransaction_of_two_switches S hfence ha_0 ha'_0 hb_0 hb'_0 hd_ab hd_ba
        he₁_G₁ he₂_G₂ hdisj_ST.symm (fun R hR => ⟨(hdisj_ST_R R hR).2, (hdisj_ST_R R hR).1⟩)
        hT_ends hS_ends
        (hatt'_b'u'.end_mem_bar S) hu'_not_W' hu'_gaps.1 hu'_gaps.2
        (hatt_bu.end_mem_bar S) hu_not_W' hu_gaps.1 hu_gaps.2
  -- Prove `P_set'.ncard = P_set.ncard + 1`, `⋃ P_set' ≤ ⋃ P_set ∪ (P ∪ P')`, and edge disjointness.
  have hS_not_diff : S_sw ∉ P_set \ {P₁} :=
    IsAttachmentWithEnds.subgraphUnion_not_mem_sdiff S hfence.1 hatt_bu hP₁_in hbP₁
  have hT_not_diff : T_sw ∉ P_set \ {P₁} :=
    IsAttachmentWithEnds.subgraphUnion_not_mem_sdiff S hfence.1 hatt'_b'u' hP₁_in hb'P₁
  have hST_ne : S_sw ≠ T_sw := fun h_eq =>
    disjoint_left.mp hdisj_ST (Or.inl hatt_bu.1.left_mem) (h_eq ▸ Or.inl hatt_bu.1.left_mem)
  have hfin_P : P_set.Finite := hfence.1.finite S
  have hfin_diff : (P_set \ {P₁}).Finite := hfin_P.sdiff
  have hcard_eq : P_set'.ncard = P_set.ncard + 1 := by
    have hset_eq : P_set' = insert S_sw (insert T_sw (P_set \ {P₁})) := by
      ext R
      simp [P_set', or_comm, or_left_comm]
    rw [hset_eq,
      ncard_insert_of_notMem (by simp [hST_ne, hS_not_diff]) (hfin_diff.insert T_sw),
      ncard_insert_of_notMem hT_not_diff hfin_diff,
      ncard_sdiff_singleton_add_one hP₁_in hfin_P]
  have hP_le : P ≤ S.G := hatt_bu.1.le
  have hP'_le : P' ≤ S.G := hatt'_b'u'.1.le
  have hP₁_le : P₁ ≤ S.G := hP₁_ends.1.le
  have hQ₁_le : Q₁ ≤ S.G := hQ₁P₁.trans hP₁_le
  have hQ₂_le : Q₂ ≤ S.G := hQ₂P₁.trans hP₁_le
  have hS_le : S_sw ≤ S.G := subgraphUnion_le hP_le hQ₁_le
  have hT_le : T_sw ≤ S.G := subgraphUnion_le hP'_le hQ₂_le
  have hP_set_le : ∀ R ∈ P_set, R ≤ S.G := fun R hR => by
    obtain ⟨_, _, h⟩ := hfence.1.1 R hR
    exact h.1.le
  have hP_set'_le : ∀ R ∈ P_set', R ≤ S.G := by
    rintro R (hR | rfl | rfl)
    · exact hP_set_le R hR.1
    · exact hS_le
    · exact hT_le
  have hunion_le :
      S.transactionUnion P_set' ≤
        subgraphUnion S.G (S.transactionUnion P_set) (subgraphUnion S.G P P') := by
    have hU₁_le : S.transactionUnion P_set ≤ S.G := subgraphSUnion_le hP_set_le
    have hU₂_le : subgraphUnion S.G P P' ≤ S.G := subgraphUnion_le hP_le hP'_le
    have hRHS_le : subgraphUnion S.G (S.transactionUnion P_set) (subgraphUnion S.G P P') ≤ S.G :=
      subgraphUnion_le hU₁_le hU₂_le
    have hLHS_le : S.transactionUnion P_set' ≤ S.G := subgraphSUnion_le hP_set'_le
    rw [(Compatible.of_le_le hLHS_le hRHS_le).le_iff]
    constructor
    · intro x hx
      change x ∈ ⋃ R ∈ P_set', V(R) at hx
      rw [mem_iUnion₂] at hx
      rcases hx with ⟨R, hR | rfl | rfl, hxR⟩
      · exact Or.inl (mem_iUnion₂.mpr ⟨R, hR.1, hxR⟩)
      · rcases hxR with hxP | hxQ₁
        · exact Or.inr (Or.inl hxP)
        · exact Or.inl (mem_iUnion₂.mpr ⟨P₁, hP₁_in, hQ₁P₁.vertexSet_mono hxQ₁⟩)
      · rcases hxR with hxP' | hxQ₂
        · exact Or.inr (Or.inr hxP')
        · exact Or.inl (mem_iUnion₂.mpr ⟨P₁, hP₁_in, hQ₂P₁.vertexSet_mono hxQ₂⟩)
    · rw [show E(S.transactionUnion P_set') = ⋃ R ∈ P_set', E(R) from
        edgeSet_subgraphSUnion hP_set'_le,
        edgeSet_subgraphUnion hU₁_le hU₂_le,
        show E(S.transactionUnion P_set) = ⋃ R ∈ P_set, E(R) from
        edgeSet_subgraphSUnion hP_set_le,
        edgeSet_subgraphUnion hP_le hP'_le]
      intro e he
      rw [mem_iUnion₂] at he
      rcases he with ⟨R, hR | rfl | rfl, heR⟩
      · exact Or.inl (mem_iUnion₂.mpr ⟨R, hR.1, heR⟩)
      · rw [edgeSet_subgraphUnion hP_le hQ₁_le] at heR
        rcases heR with heP | heQ₁
        · exact Or.inr (Or.inl heP)
        · exact Or.inl (mem_iUnion₂.mpr ⟨P₁, hP₁_in, hQ₁P₁.edgeSet_mono heQ₁⟩)
      · rw [edgeSet_subgraphUnion hP'_le hQ₂_le] at heR
        rcases heR with heP' | heQ₂
        · exact Or.inr (Or.inr heP')
        · exact Or.inl (mem_iUnion₂.mpr ⟨P₁, hP₁_in, hQ₂P₁.edgeSet_mono heQ₂⟩)
  have hdisj_EM : Disjoint E(M) E(S.transactionUnion P_set') := by
    rw [show E(S.transactionUnion P_set') = ⋃ R ∈ P_set', E(R) from
      edgeSet_subgraphSUnion hP_set'_le]
    rw [disjoint_iUnion₂_right]
    rintro R (hR | rfl | rfl)
    · rw [disjoint_left]
      intro e heM heR
      obtain ⟨x, y, hxyM⟩ := M.exists_isLink_of_mem_edgeSet heM
      obtain ⟨u_R, v_R, huvR⟩ := R.exists_isLink_of_mem_edgeSet heR
      have hxyG : S.G.IsLink e x y := hxyM.mono (hMP₁.trans hP₁_le)
      have huvG : S.G.IsLink e u_R v_R := huvR.mono (hP_set_le R hR.1)
      have hne_P₁R : P₁ ≠ R := fun h => hR.2 h.symm
      rcases hxyG.left_eq_or_eq huvG with rfl | rfl
      · exact disjoint_left.mp (hfence.1.2 hP₁_in hR.1 hne_P₁R)
          (hMP₁.vertexSet_mono hxyM.left_mem) huvR.left_mem
      · exact disjoint_left.mp (hfence.1.2 hP₁_in hR.1 hne_P₁R)
          (hMP₁.vertexSet_mono hxyM.left_mem) huvR.right_mem
    · rw [edgeSet_subgraphUnion hP_le hQ₁_le, disjoint_union_right]
      refine ⟨disjoint_edgeSet_of_inter_singleton (z := b) (hM_path.mono hP₁_le) hP_le ?_,
        hdisj_MQ₁⟩
      rw [← hatt_bu.inter_leg_eq_singleton S hP₁_in hbP₁, inter_comm V(P) V(P₁)]
      exact inter_subset_inter_left _ hMP₁.vertexSet_mono
    · rw [edgeSet_subgraphUnion hP'_le hQ₂_le, disjoint_union_right]
      refine ⟨disjoint_edgeSet_of_inter_singleton (z := b') (hM_path.mono hP₁_le) hP'_le ?_,
        hdisj_MQ₂⟩
      rw [← hatt'_b'u'.inter_leg_eq_singleton S hP₁_in hb'P₁, inter_comm V(P') V(P₁)]
      exact inter_subset_inter_left _ hMP₁.vertexSet_mono
  exact ⟨P_set', hcrooked_P_set', hcard_eq, hunion_le, hdisj_EM⟩

end Society

end GraphMinor.GM09
