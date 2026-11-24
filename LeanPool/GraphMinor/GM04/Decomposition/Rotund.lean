/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Decomposition.Linked

/-!
# Rotund tree-decompositions (Graph Minors IV, (4.1) and (4.2))

This file proves Graph Minors IV, (4.1) and (4.2) (pages 236–238):
* (4.1) (`theorem_4_1`): if `(T, τ)` is a tree-decomposition with `τ × T ∈ ℛ` and `F ⊆ E(T)` is
  rotund in `(T, τ)`, then there is a tree-decomposition `(T, τ')` of `τ × T` with
  `τ'(t)⁻ = τ(t)⁻` for all `t ∈ V(T)` such that `F` is linked in `(T, τ')`.
* (4.2) (`theorem_4_2`): if `𝒮` is a good and symmetric class of star-decompositions and
  `(T_i, τ_i)` is a sequence of rotund tree-decompositions all of whose branchings belong to `𝒮`,
  then there exist `i < i'` such that `τ_i × T_i` is simulated in `τ_{i'} × T_{i'}`.
-/

public section

namespace GraphMinor.GM04

open Hypergraph

universe u

variable {α β ι : Type*} {R : Set (RootedHypergraph α β)}
  {sim : RootedHypergraph α β → RootedHypergraph α β → Prop}

namespace RootedTree

variable (T : RootedTree ι)

/-- Among the vertices on the directed path from `u` to `v` that satisfy `P`, there is one `y`
closest to `u` (furthest from `v`). -/
theorem exists_furthest_ancestor {P : ι → Prop} {u v : ι} (huv : T.Reaches u v)
    (hP : ∃ x, P x ∧ T.Reaches u x ∧ T.Reaches x v) :
    ∃ y, P y ∧ T.Reaches u y ∧ T.Reaches y v ∧
      ∀ z, P z → T.Reaches u z → T.Reaches z y → z = y := by
  obtain ⟨hv, n, hn⟩ := huv
  induction n generalizing v with
  | zero =>
    rw [Function.iterate_zero_apply] at hn
    subst hn
    obtain ⟨x, hxP, hux, hxu⟩ := hP
    have h_eq : x = v := T.reaches_antisymm hxu hux
    subst h_eq
    exact ⟨x, hxP, T.reaches_refl hv, T.reaches_refl hv,
      fun z _ huz hzu ↦ T.reaches_antisymm hzu huz⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply] at hn
    by_cases hP' : ∃ x, P x ∧ T.Reaches u x ∧ T.Reaches x (T.parent v)
    · obtain ⟨y, hyP, huy, hyp, hmin⟩ := ih hP' (T.parent_mem v hv) hn
      exact ⟨y, hyP, huy, T.reaches_trans hyp (T.reaches_parent hv), hmin⟩
    · obtain ⟨x, hxP, hux, hxv⟩ := hP
      have hxv_eq : x = v := by
        rcases (T.reaches_iff_eq_or_reaches_parent hv).mp hxv with rfl | hxp
        · rfl
        · exact absurd ⟨x, hxP, hux, hxp⟩ hP'
      subst hxv_eq
      refine ⟨x, hxP, hux, T.reaches_refl hv, fun z hzP huz hzx ↦ ?_⟩
      rcases (T.reaches_iff_eq_or_reaches_parent hv).mp hzx with rfl | hzp
      · rfl
      · exact absurd ⟨z, hzP, huz, hzp⟩ hP'

/-- Among the vertices on the directed path from `u` to `v` that satisfy `P`, there is one `y`
closest to `v`. -/
theorem exists_closest_ancestor {P : ι → Prop} {u v : ι} (hu : P u) (huv : T.Reaches u v) :
    ∃ y, P y ∧ T.Reaches u y ∧ T.Reaches y v ∧
      ∀ z, P z → T.Reaches z v → T.Reaches z y := by
  obtain ⟨hv, n, hn⟩ := huv
  induction n generalizing v with
  | zero =>
    rw [Function.iterate_zero_apply] at hn
    subst hn
    exact ⟨v, hu, T.reaches_refl hv, T.reaches_refl hv, fun _ _ hzv ↦ hzv⟩
  | succ k ih =>
    by_cases hvP : P v
    · exact ⟨v, hvP, ⟨hv, k + 1, hn⟩, T.reaches_refl hv, fun _ _ hzv ↦ hzv⟩
    · rw [Function.iterate_succ_apply] at hn
      obtain ⟨y, hyP, huy, hyp, hmax⟩ := ih (T.parent_mem v hv) hn
      refine ⟨y, hyP, huy, T.reaches_trans hyp (T.reaches_parent hv), fun z hzP hzv ↦ ?_⟩
      have hzv_ne : z ≠ v := by
        rintro rfl
        exact hvP hzP
      exact hmax z hzP (T.reaches_parent_of_reaches_of_ne hzv hzv_ne)

end RootedTree

/-- Updating the marches of `τ` while preserving the underlying hypergraphs and root sets preserves
being a tree-decomposition of `cross τ T.verts T.root` (when the root march is unchanged). -/
theorem IsTreeDecomposition.of_toHypergraph_eq {G : RootedHypergraph α β} {T : RootedTree ι}
    {τ τ' : ι → RootedHypergraph α β} (hdec : IsTreeDecomposition G T τ)
    (hH : ∀ t ∈ T.verts, (τ' t).toHypergraph = (τ t).toHypergraph)
    (hroot : (τ' T.root).roots = (τ T.root).roots)
    (hrootSet : ∀ f ∈ T.edges, (τ' f).rootSet = (τ f).rootSet) :
    IsTreeDecomposition G T τ' where
  le t ht := by rw [hH t ht]; exact hdec.le t ht
  biUnion_eq := by
    rw [Hypergraph.biUnion_congr rfl (fun t ht ↦ hH t ht)]
    exact hdec.biUnion_eq
  edgeSet_inter_eq t₁ ht₁ t₂ ht₂ hne := by
    rw [hH t₁ ht₁, hH t₂ ht₂]
    exact hdec.edgeSet_inter_eq t₁ ht₁ t₂ ht₂ hne
  inter_le t₁ ht₁ t₂ ht₂ t₃ ht₃ hon := by
    rw [hH t₁ ht₁, hH t₂ ht₂, hH t₃ ht₃]
    exact hdec.inter_le t₁ ht₁ t₂ ht₂ t₃ ht₃ hon
  roots_root := hroot.trans hdec.roots_root
  rootSet_edge f hf := by
    have hfv : f ∈ T.verts := T.edges_subset_verts hf
    rw [hrootSet f hf, hH f hfv, hH (T.parent f) (T.parent_mem f hfv)]
    exact hdec.rootSet_edge f hf

/-- Graph Minors IV, (4.1), Claim (2) (page 237): given `e₀ = f_{p-1} ∈ F` and `f = f_p ∈ F` of
the same order `k` with `e₀ ≠ f`, `T.Reaches e₀ f`, and no edge of `pathEdges e₀ f ∩ F` of order
`< k`, there is a rooted hypergraph `H` with `H⁻ = (τ × T^f)⁻` and `πBar(H) = πBar(τ(f))` such that
`H`
is simulated in `(τ' × T^{e₀})`. -/
theorem theorem_4_1_claim_2 (hA1 : Axiom1 R) (hA3 : Axiom3 R sim)
    {T : RootedTree ι} {τ τ' : ι → RootedHypergraph α β}
    (hdec : IsTreeDecomposition (cross τ T.verts T.root) T τ)
    (hR : cross τ T.verts T.root ∈ R) {F : Set ι} (hF : F ⊆ T.edges)
    (hrot : IsRotund T τ F)
    (hH : ∀ t ∈ T.verts, (τ' t).toHypergraph = (τ t).toHypergraph)
    (hrootSet : ∀ t ∈ T.verts, (τ' t).rootSet = (τ t).rootSet)
    {e₀ f : ι} (he₀F : e₀ ∈ F) (hfF : f ∈ F) (hne : e₀ ≠ f)
    (hreach : T.Reaches e₀ f) (hord : edgeOrder T τ f = edgeOrder T τ e₀)
    (hmin : ∀ g ∈ T.pathEdges e₀ f ∩ F, edgeOrder T τ f ≤ edgeOrder T τ g) :
    ∃ H : RootedHypergraph α β,
      H.toHypergraph = (cross τ (T.subtreeAt f) f).toHypergraph ∧
      H.rootSet = (τ f).rootSet ∧
      sim H (cross τ' (T.subtreeAt e₀) e₀) := by
  classical
  have he₀e : e₀ ∈ T.edges := hF he₀F
  have hfe : f ∈ T.edges := hF hfF
  have he₀v : e₀ ∈ T.verts := T.edges_subset_verts he₀e
  have hfv : f ∈ T.verts := T.edges_subset_verts hfe
  have hpv : T.parent f ∈ T.verts := T.parent_mem f hfv
  have he₀_sub : e₀ ∈ T.subtreeAt e₀ := T.self_mem_subtreeAt he₀v
  have hf_sub : f ∈ T.subtreeAt f := T.self_mem_subtreeAt hfv
  let G₀ : RootedHypergraph α β := cross τ' (T.subtreeAt e₀) e₀
  have hG₀_toH : G₀.toHypergraph = (cross τ (T.subtreeAt e₀) e₀).toHypergraph :=
    cross_toHypergraph_congr he₀_sub he₀_sub fun t ht ↦ hH t (T.subtreeAt_subset_verts e₀ ht)
  have hG₀_R : G₀ ∈ R := by
    refine hA1 (cross τ T.verts T.root) hR G₀ ?_
    rw [hG₀_toH]
    exact hdec.cross_le (T.subtreeAt_subset_verts e₀) he₀_sub
  have hG₀_len : G₀.roots.length = edgeOrder T τ f := by
    rw [hord, hdec.edgeOrder_eq_ncard_rootSet he₀e, ← hrootSet e₀ he₀v,
      RootedHypergraph.ncard_rootSet]
    rfl
  let G₁ : RootedHypergraph α β := cross τ (T.subtreeAt f) f
  let S₂ : Finset ι := T.subtreeAt e₀ \ T.subtreeAt f
  have he₀_S₂ : e₀ ∈ S₂ := by
    rw [Finset.mem_sdiff, T.mem_subtreeAt, T.mem_subtreeAt]
    exact ⟨T.reaches_refl he₀v, fun hfe₀ ↦ hne (T.reaches_antisymm hreach hfe₀)⟩
  have hp_S₂ : T.parent f ∈ S₂ := by
    rw [Finset.mem_sdiff, T.mem_subtreeAt, T.mem_subtreeAt]
    exact ⟨T.reaches_parent_of_reaches_of_ne hreach hne, T.not_reaches_parent hfe⟩
  have hS₂_sub_e₀ : S₂ ⊆ T.subtreeAt e₀ := Finset.sdiff_subset
  have hS₂_sub_root : S₂ ⊆ T.rootSide f := by
    intro x hx
    rw [Finset.mem_sdiff, T.mem_subtreeAt, T.mem_subtreeAt] at hx
    exact T.mem_rootSide.mpr ⟨T.reaches_mem_right hx.1, hx.2⟩
  let G₂ : RootedHypergraph α β :=
    { toHypergraph := (cross τ S₂ e₀).toHypergraph
      roots := (τ' e₀).roots
      roots_nodup := (τ' e₀).roots_nodup
      roots_subset := fun v hv ↦ by
        have hv' : v ∈ (τ e₀).vertexSet := by
          rw [← hH e₀ he₀v]
          exact (τ' e₀).roots_subset v hv
        exact (hdec.le_cross (hS₂_sub_e₀.trans (T.subtreeAt_subset_verts e₀))
          he₀_S₂ he₀_S₂).vertexSet_subset hv' }
  have hG₁_le_G₀ : G₁.toHypergraph ≤ G₀.toHypergraph := by
    rw [hG₀_toH]
    exact hdec.cross_le_cross (T.subtreeAt_mono hreach) (T.subtreeAt_subset_verts e₀)
      hf_sub he₀_sub
  have hG₂_le_G₀ : G₂.toHypergraph ≤ G₀.toHypergraph := by
    rw [hG₀_toH]
    exact hdec.cross_le_cross hS₂_sub_e₀ (T.subtreeAt_subset_verts e₀) he₀_S₂ he₀_sub
  have hG₁₂_inter : G₁.toHypergraph ∩ G₂.toHypergraph =
      (τ f).toHypergraph ∩ (τ (T.parent f)).toHypergraph := by
    have hle₁ : (τ f).toHypergraph ≤ G₁.toHypergraph :=
      hdec.le_cross (T.subtreeAt_subset_verts f) hf_sub hf_sub
    have hle₂ : (τ (T.parent f)).toHypergraph ≤ G₂.toHypergraph :=
      hdec.le_cross (hS₂_sub_e₀.trans (T.subtreeAt_subset_verts e₀)) he₀_S₂ hp_S₂
    have hle₃ : G₂.toHypergraph ≤ (cross τ (T.rootSide f) T.root).toHypergraph :=
      hdec.cross_le_cross hS₂_sub_root (T.rootSide_subset_verts f)
        he₀_S₂ (T.root_mem_rootSide hfe)
    have h_low : (τ f).toHypergraph ∩ (τ (T.parent f)).toHypergraph ≤
        G₁.toHypergraph ∩ G₂.toHypergraph :=
      Hypergraph.le_inter
        ((Hypergraph.inter_le_left (hdec.le f hfv) (hdec.le _ hpv)).trans hle₁)
        ((Hypergraph.inter_le_right (hdec.le f hfv) (hdec.le _ hpv)).trans hle₂)
    refine (Hypergraph.eq_of_le_of_subset h_low ?_ ?_).symm
    · have hsub : (G₁.toHypergraph ∩ G₂.toHypergraph).vertexSet ⊆
          (G₁.toHypergraph ∩ (cross τ (T.rootSide f) T.root).toHypergraph).vertexSet :=
        Set.inter_subset_inter_right _ hle₃.vertexSet_subset
      rwa [hdec.subtreeAt_inter_rootSide_eq hfe] at hsub
    · have hsub : (G₁.toHypergraph ∩ G₂.toHypergraph).edgeSet ⊆
          (G₁.toHypergraph ∩ (cross τ (T.rootSide f) T.root).toHypergraph).edgeSet :=
        Set.inter_subset_inter_right _ hle₃.edgeSet_subset
      rwa [hdec.subtreeAt_inter_rootSide_eq hfe] at hsub
  have hsep_G₀ : G₀.IsSeparation G₁ G₂ := by
    refine ⟨⟨hG₁_le_G₀, hG₂_le_G₀, ?_, ?_⟩, rfl, ?_⟩
    · change (cross τ (T.subtreeAt f) f).toHypergraph ∪ (cross τ S₂ e₀).toHypergraph =
        G₀.toHypergraph
      rw [hG₀_toH, cross_toHypergraph_of_mem τ hf_sub, cross_toHypergraph_of_mem τ he₀_S₂,
        cross_toHypergraph_of_mem τ he₀_sub, ← Hypergraph.biUnion_union,
        Finset.union_sdiff_of_subset (T.subtreeAt_mono hreach)]
    · rw [hG₁₂_inter]
      exact hdec.edgeSet_inter_eq f hfv (T.parent f) hpv (T.parent_ne_self hfe).symm
    · rw [cross_rootSet, hG₁₂_inter, hdec.rootSet_edge f hfe]
  have hord_G₁₂ : separationOrder G₁.toHypergraph G₂.toHypergraph = G₀.roots.length := by
    rw [hG₀_len, hdec.edgeOrder_eq_ncard_inter hfe]
    simp only [separationOrder, hG₁₂_inter]
  have hno_sep : ¬ ∃ H₁ H₂ : RootedHypergraph α β, G₀.IsSeparation H₁ H₂ ∧
      G₁.toHypergraph ≤ H₁.toHypergraph ∧
      separationOrder H₁.toHypergraph H₂.toHypergraph < G₀.roots.length := by
    rintro ⟨H₁, H₂, hsepH, hG₁_H₁, hordH⟩
    have hsep_e₀ := hdec.isSeparation_edge he₀e
    let R_e₀ := (cross τ (T.rootSide e₀) T.root).toHypergraph
    have hH₁_le_G : H₁.toHypergraph ≤ (cross τ T.verts T.root).toHypergraph :=
      hsepH.isSeparation.left_le.trans (hG₀_toH ▸ hsep_e₀.isSeparation.left_le)
    have hH₂_le_G : H₂.toHypergraph ≤ (cross τ T.verts T.root).toHypergraph :=
      hsepH.isSeparation.right_le.trans (hG₀_toH ▸ hsep_e₀.isSeparation.left_le)
    have hR_le_G : R_e₀ ≤ (cross τ T.verts T.root).toHypergraph :=
      hsep_e₀.isSeparation.right_le
    let K₁ : Hypergraph α β := H₁.toHypergraph
    let K₂ : Hypergraph α β := H₂.toHypergraph ∪ R_e₀
    have h_root_in_H₂ : (G₀.toHypergraph ∩ R_e₀).vertexSet ⊆ H₂.vertexSet := by
      rw [hG₀_toH, ← hsep_e₀.rootSet_left, cross_rootSet, ← hrootSet e₀ he₀v]
      intro v hv
      change v ∈ (τ' e₀).roots at hv
      have h_roots_eq : H₂.roots = (τ' e₀).roots := hsepH.roots_right
      rw [← h_roots_eq] at hv
      exact H₂.roots_subset v hv
    have hK₁₂_vertex : (K₁ ∩ K₂).vertexSet = (H₁.toHypergraph ∩ H₂.toHypergraph).vertexSet := by
      ext v
      simp only [K₁, K₂, inter_vertexSet, union_vertexSet, Set.mem_inter_iff, Set.mem_union]
      refine ⟨fun ⟨hv₁, hv₂⟩ ↦ ⟨hv₁, hv₂.elim id fun hvR ↦ ?_⟩,
        fun ⟨hv₁, hv₂⟩ ↦ ⟨hv₁, Or.inl hv₂⟩⟩
      exact h_root_in_H₂ ⟨hsepH.isSeparation.left_le.vertexSet_subset hv₁, hvR⟩
    have hK₁₂_edge : (K₁ ∩ K₂).edgeSet = ∅ := by
      ext e
      simp only [K₁, K₂, inter_edgeSet, union_edgeSet, Set.mem_inter_iff, Set.mem_union,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro he₁ (he₂ | heR)
      · have he : e ∈ (H₁.toHypergraph ∩ H₂.toHypergraph).edgeSet := ⟨he₁, he₂⟩
        rw [hsepH.isSeparation.edgeSet_inter_eq] at he
        exact False.elim he
      · have he : e ∈ ((cross τ (T.subtreeAt e₀) e₀).toHypergraph ∩ R_e₀).edgeSet := by
          rw [← hG₀_toH]
          exact ⟨hsepH.isSeparation.left_le.edgeSet_subset he₁, heR⟩
        rw [hsep_e₀.isSeparation.edgeSet_inter_eq] at he
        exact False.elim he
    have hK₁₂_union : K₁ ∪ K₂ = (cross τ T.verts T.root).toHypergraph := by
      have hle : K₁ ∪ K₂ ≤ (cross τ T.verts T.root).toHypergraph :=
        Hypergraph.union_le hH₁_le_G (Hypergraph.union_le hH₂_le_G hR_le_G)
      refine Hypergraph.eq_of_le_of_subset hle ?_ ?_
      · intro v hv
        rw [← hsep_e₀.isSeparation.union_eq, union_vertexSet, ← hG₀_toH,
          ← hsepH.isSeparation.union_eq, union_vertexSet] at hv
        simp only [K₁, K₂, union_vertexSet, Set.mem_union] at hv ⊢
        tauto
      · intro e he
        rw [← hsep_e₀.isSeparation.union_eq, union_edgeSet, ← hG₀_toH,
          ← hsepH.isSeparation.union_eq, union_edgeSet] at he
        simp only [K₁, K₂, union_edgeSet, Set.mem_union] at he ⊢
        tauto
    have hsepK : (cross τ T.verts T.root).toHypergraph.IsSeparation K₁ K₂ :=
      ⟨hH₁_le_G, Hypergraph.union_le hH₂_le_G hR_le_G, hK₁₂_union, hK₁₂_edge⟩
    have hR_le_K₂ : R_e₀ ≤ K₂ := Hypergraph.le_union_right hH₂_le_G hR_le_G
    have hordK : separationOrder K₁ K₂ < edgeOrder T τ f := by
      rw [← hG₀_len]
      simpa only [separationOrder, hK₁₂_vertex] using hordH
    exact hrot f hfF e₀ he₀F hreach hord hmin ⟨K₁, K₂, hsepK, hG₁_H₁, hR_le_K₂, hordK⟩
  exact hA3 G₀ hG₀_R G₁ G₂ hsep_G₀ hord_G₁₂ hno_sep

private theorem coe_eq_of_sdiff_card_zero {ι : Type*} [DecidableEq ι]
    {D Ffin : Finset ι} {F : Set ι} (hFfin : ∀ x, x ∈ Ffin ↔ x ∈ F)
    (hsub : D ⊆ Ffin) (hcard : (Ffin \ D).card = 0) : (D : Set ι) = F := by
  have hback : Ffin ⊆ D := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hcard)
  have hEq : D = Ffin := Finset.Subset.antisymm hsub hback
  subst hEq
  exact Set.ext hFfin

private theorem sdiff_insert_card_eq {ι : Type*} [DecidableEq ι] {D Ffin : Finset ι} {f : ι}
    {m : ℕ} (hf : f ∈ Ffin \ D) (hcard : (Ffin \ D).card = m + 1) :
    (Ffin \ insert f D).card = m := by
  have hsdiff : Ffin \ insert f D = (Ffin \ D).erase f := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
    tauto
  rw [hsdiff, Finset.card_erase_of_mem hf, hcard]
  rfl

/-- Graph Minors IV, (4.1). -/
theorem theorem_4_1_proof {ι : Type*} (hA1 : Axiom1 R) (hA2 : Axiom2 R sim) (hA3 : Axiom3 R sim)
    (T : RootedTree ι) (τ : ι → RootedHypergraph α β)
    (hdec : IsTreeDecomposition (cross τ T.verts T.root) T τ)
    (hR : cross τ T.verts T.root ∈ R) (F : Set ι) (hF : F ⊆ T.edges)
    (hrot : IsRotund T τ F) :
    ∃ τ' : ι → RootedHypergraph α β,
      IsTreeDecomposition (cross τ T.verts T.root) T τ' ∧
      (∀ t ∈ T.verts, (τ' t).toHypergraph = (τ t).toHypergraph) ∧ IsLinked sim T τ' F := by
  classical
  let F_fin : Finset ι := T.edges.filter (· ∈ F)
  have hF_fin : ∀ x, x ∈ F_fin ↔ x ∈ F := by
    intro x
    simp only [F_fin, Finset.mem_filter]
    exact ⟨And.right, fun hx ↦ ⟨hF hx, hx⟩⟩
  -- Inductive step: extend a downward-closed subset `D ⊆ F_fin` until `F_fin \ D = ∅`.
  suffices h_ind : ∀ (n : ℕ) (D : Finset ι) (τ' : ι → RootedHypergraph α β),
      D ⊆ F_fin →
      (F_fin \ D).card = n →
      (∀ f ∈ D, ∀ e ∈ F, T.Reaches e f → e ∈ D) →
      (∀ t, (τ' t).toHypergraph = (τ t).toHypergraph) →
      (∀ t, (τ' t).rootSet = (τ t).rootSet) →
      (τ' T.root).roots = (τ T.root).roots →
      IsLinked sim T τ' (D : Set ι) →
      ∃ τ'' : ι → RootedHypergraph α β,
        (∀ t, (τ'' t).toHypergraph = (τ t).toHypergraph) ∧
        (∀ t, (τ'' t).rootSet = (τ t).rootSet) ∧
        (τ'' T.root).roots = (τ T.root).roots ∧
        IsLinked sim T τ'' F by
    obtain ⟨τ'', hH, hrootSet, hroot, hlinked⟩ :=
      h_ind F_fin.card ∅ τ (Finset.empty_subset _) (by simp) (by simp)
        (fun _ ↦ rfl) (fun _ ↦ rfl) rfl (by simp [IsLinked])
    refine ⟨τ'', hdec.of_toHypergraph_eq (fun t _ ↦ hH t) hroot (fun f _ ↦ hrootSet f),
      fun t _ ↦ hH t, hlinked⟩
  intro n
  induction n with
  | zero =>
    intro D τ' hD_sub hcard _ hH hrootSet hroot hlinkedD
    have hF_eq : (D : Set ι) = F :=
      coe_eq_of_sdiff_card_zero hF_fin hD_sub hcard
    rw [hF_eq] at hlinkedD
    exact ⟨τ', hH, hrootSet, hroot, hlinkedD⟩
  | succ m ih =>
    intro D τ' hD_sub hcard hD_down hH hrootSet hroot hlinkedD
    have hne : (F_fin \ D).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x₀, hx₀⟩ := hne
    have hx₀v : x₀ ∈ T.verts := T.edges_subset_verts (hF ((hF_fin x₀).mp
      (Finset.mem_sdiff.mp hx₀).1))
    obtain ⟨f, hf_sdiff, _, _, hf_min⟩ :=
      T.exists_furthest_ancestor (T.reaches_root hx₀v)
        ⟨x₀, hx₀, T.reaches_root hx₀v, T.reaches_refl hx₀v⟩
    have hf_F : f ∈ F := (hF_fin f).mp (Finset.mem_sdiff.mp hf_sdiff).1
    have hf_notD : f ∉ D := (Finset.mem_sdiff.mp hf_sdiff).2
    have hfe : f ∈ T.edges := hF hf_F
    have hfv : f ∈ T.verts := T.edges_subset_verts hfe
    have hf_anc_in_D : ∀ e ∈ F, e ≠ f → T.Reaches e f → e ∈ D := by
      intro e heF hef hef_reach
      by_contra heD
      have he_sdiff : e ∈ F_fin \ D := Finset.mem_sdiff.mpr ⟨(hF_fin e).mpr heF, heD⟩
      have hev : e ∈ T.verts := T.edges_subset_verts (hF heF)
      exact hef (hf_min e he_sdiff (T.reaches_root hev) hef_reach)
    let D' : Finset ι := insert f D
    have hD'_sub : D' ⊆ F_fin :=
      Finset.insert_subset ((Finset.mem_sdiff.mp hf_sdiff).1) hD_sub
    have hcard' : (F_fin \ D').card = m :=
      sdiff_insert_card_eq hf_sdiff hcard
    have hD'_down : ∀ x ∈ D', ∀ e ∈ F, T.Reaches e x → e ∈ D' := by
      intro x hx e heF hex
      rcases Finset.mem_insert.mp hx with rfl | hxD
      · by_cases hef : e = x
        · subst hef
          exact Finset.mem_insert_self e D
        · exact Finset.mem_insert_of_mem (hf_anc_in_D e heF hef hex)
      · exact Finset.mem_insert_of_mem (hD_down x hxD e heF hex)
    -- Define the predicate `P e` for strict ancestors `e ∈ F` of `f` on a constant-order path.
    let P : ι → Prop := fun e ↦ e ∈ F ∧ e ≠ f ∧ edgeOrder T τ f = edgeOrder T τ e ∧
      ∀ g ∈ T.pathEdges e f ∩ F, edgeOrder T τ f ≤ edgeOrder T τ g
    have h_choice : ∃ H_f : RootedHypergraph α β,
        H_f.toHypergraph = (τ f).toHypergraph ∧
        H_f.rootSet = (τ f).rootSet ∧
        ∀ e, P e → T.Reaches e f →
          sim (cross (Function.update τ' f H_f) (T.subtreeAt f) f)
            (cross τ' (T.subtreeAt e) e) := by
      by_cases hP_ex : ∃ e, P e ∧ T.Reaches e f
      · obtain ⟨e₁, he₁P, he₁f⟩ := hP_ex
        obtain ⟨e₀, he₀P, _, he₀f, he₀_max⟩ := T.exists_closest_ancestor he₁P he₁f
        obtain ⟨H, hH_to, hH_rootSet, hsim_e₀⟩ :=
          theorem_4_1_claim_2 hA1 hA3 hdec hR hF hrot
            (fun t _ ↦ hH t) (fun t _ ↦ hrootSet t)
            he₀P.1 hf_F he₀P.2.1 he₀f he₀P.2.2.1 he₀P.2.2.2
        let H_f : RootedHypergraph α β :=
          { toHypergraph := (τ f).toHypergraph
            roots := H.roots
            roots_nodup := H.roots_nodup
            roots_subset := fun v hv ↦ by
              have hv' : v ∈ H.rootSet := hv
              rw [hH_rootSet] at hv'
              exact (τ f).roots_subset v hv' }
        have hcross_eq : cross (Function.update τ' f H_f) (T.subtreeAt f) f = H := by
          apply RootedHypergraph.ext
          · rw [hH_to]
            refine cross_toHypergraph_congr (T.self_mem_subtreeAt hfv) (T.self_mem_subtreeAt hfv)
              fun t _ ↦ ?_
            by_cases htf : t = f
            · subst htf
              simp [H_f]
            · simp [htf, hH t]
          · simp [H_f]
        refine ⟨H_f, rfl, hH_rootSet, fun e heP hef ↦ ?_⟩
        rw [hcross_eq]
        have hee₀ : T.Reaches e e₀ := he₀_max e heP hef
        have he₀D : e₀ ∈ D := hf_anc_in_D e₀ he₀P.1 he₀P.2.1 he₀f
        have heD : e ∈ D := hf_anc_in_D e heP.1 heP.2.1 hef
        have hord_e₀_e : edgeOrder T τ' e₀ = edgeOrder T τ' e := by
          rw [edgeOrder_congr (hF he₀P.1) (fun t _ ↦ hH t),
            edgeOrder_congr (hF heP.1) (fun t _ ↦ hH t),
            ← he₀P.2.2.1, ← heP.2.2.1]
        have hmin_e₀_e : ∀ g ∈ T.pathEdges e e₀ ∩ ↑D, edgeOrder T τ' e₀ ≤ edgeOrder T τ' g := by
          rintro g ⟨⟨heg, hge₀⟩, hgD⟩
          have hgF : g ∈ F := (hF_fin g).mp (hD_sub hgD)
          rw [edgeOrder_congr (hF he₀P.1) (fun t _ ↦ hH t),
            edgeOrder_congr (hF hgF) (fun t _ ↦ hH t), ← he₀P.2.2.1]
          exact heP.2.2.2 g ⟨⟨heg, T.reaches_trans hge₀ he₀f⟩, hgF⟩
        have hsim_e₀_e : sim (cross τ' (T.subtreeAt e₀) e₀) (cross τ' (T.subtreeAt e) e) :=
          hlinkedD e₀ he₀D e heD hee₀ hord_e₀_e hmin_e₀_e
        have hH_R : H ∈ R := by
          refine hA1 (cross τ T.verts T.root) hR H ?_
          rw [hH_to]
          exact hdec.cross_le (T.subtreeAt_subset_verts f) (T.self_mem_subtreeAt hfv)
        have he₀_R : cross τ' (T.subtreeAt e₀) e₀ ∈ R := by
          refine hA1 (cross τ T.verts T.root) hR _ ?_
          have he₀v : e₀ ∈ T.verts := T.edges_subset_verts (hF he₀P.1)
          rw [cross_toHypergraph_congr (T.self_mem_subtreeAt he₀v) (T.self_mem_subtreeAt he₀v)
            (fun t _ ↦ hH t)]
          exact hdec.cross_le (T.subtreeAt_subset_verts e₀) (T.self_mem_subtreeAt he₀v)
        have he_R : cross τ' (T.subtreeAt e) e ∈ R := by
          refine hA1 (cross τ T.verts T.root) hR _ ?_
          have hev : e ∈ T.verts := T.edges_subset_verts (hF heP.1)
          rw [cross_toHypergraph_congr (T.self_mem_subtreeAt hev) (T.self_mem_subtreeAt hev)
            (fun t _ ↦ hH t)]
          exact hdec.cross_le (T.subtreeAt_subset_verts e) (T.self_mem_subtreeAt hev)
        exact hA2.2 H hH_R _ he₀_R _ he_R hsim_e₀ hsim_e₀_e
      · refine ⟨τ' f, hH f, hrootSet f, fun e heP hef ↦ False.elim (hP_ex ⟨e, heP, hef⟩)⟩
    obtain ⟨H_f, hHf_to, hHf_rootSet, hHf_sim⟩ := h_choice
    let τ'' : ι → RootedHypergraph α β := Function.update τ' f H_f
    have hH'' : ∀ t, (τ'' t).toHypergraph = (τ t).toHypergraph := by
      intro t
      by_cases htf : t = f
      · subst htf
        simpa [τ''] using hHf_to
      · simp [τ'', htf, hH t]
    have hrootSet'' : ∀ t, (τ'' t).rootSet = (τ t).rootSet := by
      intro t
      by_cases htf : t = f
      · subst htf
        simpa [τ''] using hHf_rootSet
      · simp [τ'', htf, hrootSet t]
    have hroot'' : (τ'' T.root).roots = (τ T.root).roots := by
      have hrf : T.root ≠ f := (T.mem_edges_iff.mp hfe).2.symm
      simp [τ'', hrf, hroot]
    have hcross_ne : ∀ e ∈ T.verts, e ≠ f →
        cross τ'' (T.subtreeAt e) e = cross τ' (T.subtreeAt e) e := by
      intro e hev hef
      refine cross_congr (T.self_mem_subtreeAt hev) (fun t _ ↦ ?_) ?_
      · rw [hH'' t, hH t]
      · simp [τ'', hef]
    have hlinkedD' : IsLinked sim T τ'' (D' : Set ι) := by
      intro f₁ hf₁ f₂ hf₂ hreach hord hmin
      have hf₁F : f₁ ∈ F := (hF_fin f₁).mp (hD'_sub hf₁)
      have hf₂F : f₂ ∈ F := (hF_fin f₂).mp (hD'_sub hf₂)
      have hf₁v : f₁ ∈ T.verts := T.edges_subset_verts (hF hf₁F)
      have hf₂v : f₂ ∈ T.verts := T.edges_subset_verts (hF hf₂F)
      by_cases h₁₂ : f₁ = f₂
      · subst h₁₂
        refine hA2.1 _ (hA1 (cross τ T.verts T.root) hR _ ?_)
        rw [cross_toHypergraph_congr (T.self_mem_subtreeAt hf₁v) (T.self_mem_subtreeAt hf₁v)
          (fun t _ ↦ hH'' t)]
        exact hdec.cross_le (T.subtreeAt_subset_verts f₁) (T.self_mem_subtreeAt hf₁v)
      · have hf₂_ne_f : f₂ ≠ f := by
          rintro rfl
          have hf₁D : f₁ ∈ D := (Finset.mem_insert.mp hf₁).resolve_left h₁₂
          exact hf_notD (hD_down f₁ hf₁D f₂ hf₂F hreach)
        have hf₂D : f₂ ∈ D := (Finset.mem_insert.mp hf₂).resolve_left hf₂_ne_f
        rw [hcross_ne f₂ hf₂v hf₂_ne_f]
        rcases Finset.mem_insert.mp hf₁ with rfl | hf₁D
        · refine hHf_sim f₂ ⟨hf₂F, hf₂_ne_f, ?_, ?_⟩ hreach
          · rw [← edgeOrder_congr (hF hf₁F) (fun t _ ↦ hH'' t),
              ← edgeOrder_congr (hF hf₂F) (fun t _ ↦ hH'' t), hord]
          · rintro g ⟨hg_path, hgF⟩
            have hgD' : g ∈ D' := hD'_down f₁ (Finset.mem_insert_self f₁ D) g hgF hg_path.2
            rw [← edgeOrder_congr (hF hf₁F) (fun t _ ↦ hH'' t),
              ← edgeOrder_congr (hF hgF) (fun t _ ↦ hH'' t)]
            exact hmin g ⟨hg_path, hgD'⟩
        · have hf₁_ne_f : f₁ ≠ f := fun h ↦ hf_notD (h ▸ hf₁D)
          rw [hcross_ne f₁ hf₁v hf₁_ne_f]
          refine hlinkedD f₁ hf₁D f₂ hf₂D hreach ?_ ?_
          · rw [edgeOrder_congr (hF hf₁F) (fun t _ ↦ hH t),
              edgeOrder_congr (hF hf₂F) (fun t _ ↦ hH t),
              ← edgeOrder_congr (hF hf₁F) (fun t _ ↦ hH'' t),
              ← edgeOrder_congr (hF hf₂F) (fun t _ ↦ hH'' t), hord]
          · rintro g ⟨hg_path, hgD⟩
            have hgF : g ∈ F := (hF_fin g).mp (hD_sub hgD)
            rw [edgeOrder_congr (hF hf₁F) (fun t _ ↦ hH t),
              edgeOrder_congr (hF hgF) (fun t _ ↦ hH t),
              ← edgeOrder_congr (hF hf₁F) (fun t _ ↦ hH'' t),
              ← edgeOrder_congr (hF hgF) (fun t _ ↦ hH'' t)]
            exact hmin g ⟨hg_path, Finset.mem_insert_of_mem hgD⟩
    exact ih D' τ'' hD'_sub hcard' hD'_down hH'' hrootSet'' hroot'' hlinkedD'

/-- Graph Minors IV, (4.2). -/
theorem theorem_4_2_proof (h22 : TreeLemma22Statement.{u}) {ι : Type u}
    (hA1 : Axiom1 R) (hA2 : Axiom2 R sim) (hA3 : Axiom3 R sim)
    (𝒮 : Set (RootedTree ι × (ι → RootedHypergraph α β))) (h𝒮 : IsGood R sim 𝒮)
    (hsym : IsSymmetric 𝒮) (T : ℕ → RootedTree ι) (τ : ℕ → ι → RootedHypergraph α β)
    (hdec : ∀ i, IsTreeDecomposition (cross (τ i) (T i).verts (T i).root) (T i) (τ i))
    (hrot : ∀ i, IsRotund (T i) (τ i) (T i).edges)
    (hbr : ∀ i, ∀ s ∈ (T i).verts, ((T i).starAt s, branching (T i) (τ i) s) ∈ 𝒮) :
    ∃ i i', i < i' ∧
      sim (cross (τ i) (T i).verts (T i).root) (cross (τ i') (T i').verts (T i').root) := by
  have hR : ∀ i, cross (τ i) (T i).verts (T i).root ∈ R := by
    intro i
    have h := h𝒮.2.1 ((T i).starAt (T i).root, branching (T i) (τ i) (T i).root)
      (hbr i (T i).root (T i).root_mem)
    dsimp only at h
    rwa [cross_branching_eq (T i) (τ i) (T i).root_mem, cross_subtreeAt_root] at h
  have h41 : ∀ i, ∃ τ' : ι → RootedHypergraph α β,
      IsTreeDecomposition (cross (τ i) (T i).verts (T i).root) (T i) τ' ∧
      (∀ t ∈ (T i).verts, (τ' t).toHypergraph = (τ i t).toHypergraph) ∧
      IsLinked sim (T i) τ' (T i).edges :=
    fun i ↦ theorem_4_1_proof hA1 hA2 hA3 (T i) (τ i) (hdec i) (hR i) (T i).edges subset_rfl
      (hrot i)
  choose τ' hdec' hH' hlinked' using h41
  have hrootSet' : ∀ i, ∀ t ∈ (T i).verts, (τ' i t).rootSet = (τ i t).rootSet := by
    intro i t ht
    by_cases htr : t = (T i).root
    · subst htr
      have h1 : (τ' i (T i).root).roots = (τ i (T i).root).roots :=
        (hdec' i).roots_root.trans (hdec i).roots_root.symm
      simp only [RootedHypergraph.rootSet, h1]
    · have hte : t ∈ (T i).edges := (T i).mem_edges_iff.mpr ⟨ht, htr⟩
      rw [(hdec' i).rootSet_edge t hte, (hdec i).rootSet_edge t hte,
        hH' i t ht, hH' i ((T i).parent t) ((T i).parent_mem t ht)]
  have hcross_eq : ∀ i,
      cross (τ' i) (T i).verts (T i).root = cross (τ i) (T i).verts (T i).root :=
    fun i ↦ (hdec' i).cross_verts_eq
  have hdec'' : ∀ i, IsTreeDecomposition (cross (τ' i) (T i).verts (T i).root) (T i) (τ' i) := by
    intro i
    rw [hcross_eq i]
    exact hdec' i
  have hbr' : ∀ i, ∀ s ∈ (T i).verts, ((T i).starAt s, branching (T i) (τ' i) s) ∈ 𝒮 := by
    intro i s hs
    refine hsym ((T i).starAt s, branching (T i) (τ i) s) (hbr i s hs)
      (branching (T i) (τ' i) s) ((hdec' i).isStarDecomposition_branching hs) ?_
    intro t ht
    dsimp only at ht ⊢
    rcases (T i).mem_starAt_verts.mp ht with rfl | htc
    · simp only [branching_self]
      exact ⟨hH' i t hs, hrootSet' i t hs⟩
    · rw [branching_of_mem_children (T i) (τ' i) htc, branching_of_mem_children (T i) (τ i) htc]
      have htv : t ∈ (T i).verts := (T i).children_subset_verts s htc
      have ht_sub : t ∈ (T i).subtreeAt t := (T i).self_mem_subtreeAt htv
      refine ⟨cross_toHypergraph_congr ht_sub ht_sub
        (fun u hu ↦ hH' i u ((T i).subtreeAt_subset_verts t hu)), ?_⟩
      simp only [cross_rootSet]
      exact hrootSet' i t htv
  obtain ⟨i, i', hii', hsim⟩ := theorem_3_3_proof h22 hA1 hA2 𝒮 h𝒮 T τ' hdec'' hlinked' hbr'
  rw [hcross_eq i, hcross_eq i'] at hsim
  exact ⟨i, i', hii', hsim⟩

end GraphMinor.GM04
