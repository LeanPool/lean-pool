/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM09.Section2a

/-!
# Graph Minors IX, Section 2 (Part 2): Completion of (2.1)

This file completes the proof of (2.1) from Section 2 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (pages 43–44).
-/

public section

namespace GraphMinor.GM09

open Set Graph GraphMinor.Surface GraphMinor.GM06

universe u v

variable {α : Type u} {β : Type v}

private theorem detour_excludes_marked_vertex
    {K P P_sa P_ac P_ct R : Graph α β} {s t a c u v : α}
    (hPK : IsGraphPathWithEnds K P s t)
    (hP_sa_le : P_sa ≤ P) (hP_ac_le : P_ac ≤ P) (hP_ct_le : P_ct ≤ P)
    (hpath_sa : IsGraphPathWithEnds P P_sa s a)
    (hpath_ac : IsGraphPathWithEnds P P_ac a c)
    (hpath_ct : IsGraphPathWithEnds P P_ct c t)
    (hinter_sa : V(P_sa) ∩ V(P_ac) = {a})
    (hinter_ct : V(P_ac) ∩ V(P_ct) = {c})
    (hdisj_sact : Disjoint V(P_sa) V(P_ct))
    (hforced : ∀ Q : Graph α β, IsGraphPathWithEnds K Q s t → a ∈ V(Q))
    (hv_sa : v ∈ V(P_sa)) (hu_ac : u ∈ V(P_ac))
    (hva_ne : v ≠ a) (hau_ne : a ≠ u)
    (hRK : IsGraphPathWithEnds K R u v) (hRP : V(R) ∩ V(P) = {u, v}) : False := by
  obtain ⟨P_sv, P_va, hP_sv, hP_va, hpath_sv, hpath_va, _, hinter_v, _⟩ :=
    hpath_sa.exists_split_at hv_sa
  obtain ⟨P_au, P_uc, hP_au, hP_uc, hpath_au, hpath_uc, _, hinter_u, _⟩ :=
    hpath_ac.exists_split_at hu_ac
  have hV_va_au : V(P_va) ∩ V(P_au) = {a} := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    exact ⟨fun ⟨hz₁, hz₂⟩ => by
      have : z ∈ V(P_sa) ∩ V(P_ac) := ⟨hP_va.vertexSet_mono hz₁, hP_au.vertexSet_mono hz₂⟩
      rwa [hinter_sa, mem_singleton_iff] at this,
      fun h => h ▸ ⟨hpath_va.right_mem, hpath_au.left_mem⟩⟩
  have hpath_vu : IsGraphPathWithEnds P (subgraphUnion P P_va P_au) v u :=
    (hpath_va.mono hP_sa_le).subgraphUnion (hpath_au.mono hP_ac_le) hV_va_au
  have hV_uc_ct : V(P_uc) ∩ V(P_ct) = {c} := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    exact ⟨fun ⟨hz₁, hz₂⟩ => by
      have : z ∈ V(P_ac) ∩ V(P_ct) := ⟨hP_uc.vertexSet_mono hz₁, hz₂⟩
      rwa [hinter_ct, mem_singleton_iff] at this,
      fun h => h ▸ ⟨hpath_uc.right_mem, hpath_ct.left_mem⟩⟩
  have hpath_ut : IsGraphPathWithEnds P (subgraphUnion P P_uc P_ct) u t :=
    (hpath_uc.mono hP_ac_le).subgraphUnion hpath_ct hV_uc_ct
  have hinter_sv_vu : V(P_sv) ∩ V(subgraphUnion P P_va P_au) = {v} := by
    ext z
    simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hz₁, hz₂ | hz₃⟩
      · have : z ∈ V(P_sv) ∩ V(P_va) := ⟨hz₁, hz₂⟩
        rwa [hinter_v, mem_singleton_iff] at this
      · have hz_a : z = a := by
          have : z ∈ V(P_sa) ∩ V(P_ac) := ⟨hP_sv.vertexSet_mono hz₁, hP_au.vertexSet_mono hz₃⟩
          rwa [hinter_sa, mem_singleton_iff] at this
        subst hz_a
        have : z ∈ V(P_sv) ∩ V(P_va) := ⟨hz₁, hpath_va.right_mem⟩
        rwa [hinter_v, mem_singleton_iff] at this
    · rintro rfl
      exact ⟨hpath_sv.right_mem, Or.inl hpath_va.left_mem⟩
  have hinter_vu_ut : V(subgraphUnion P P_va P_au) ∩ V(subgraphUnion P P_uc P_ct) = {u} := by
    ext z
    simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hz₁ | hz₂, hz₃ | hz₄⟩
      · have hz_a : z = a := by
          have : z ∈ V(P_sa) ∩ V(P_ac) := ⟨hP_va.vertexSet_mono hz₁, hP_uc.vertexSet_mono hz₃⟩
          rwa [hinter_sa, mem_singleton_iff] at this
        subst hz_a
        have : z ∈ V(P_au) ∩ V(P_uc) := ⟨hpath_au.left_mem, hz₃⟩
        rwa [hinter_u, mem_singleton_iff] at this
      · exact (disjoint_left.mp hdisj_sact (hP_va.vertexSet_mono hz₁) hz₄).elim
      · have : z ∈ V(P_au) ∩ V(P_uc) := ⟨hz₂, hz₃⟩
        rwa [hinter_u, mem_singleton_iff] at this
      · have hz_c : z = c := by
          have : z ∈ V(P_ac) ∩ V(P_ct) := ⟨hP_au.vertexSet_mono hz₂, hz₄⟩
          rwa [hinter_ct, mem_singleton_iff] at this
        subst hz_c
        have : z ∈ V(P_au) ∩ V(P_uc) := ⟨hz₂, hpath_uc.right_mem⟩
        rwa [hinter_u, mem_singleton_iff] at this
    · rintro rfl
      exact ⟨Or.inr hpath_au.right_mem, Or.inl hpath_uc.left_mem⟩
  have hdisj_sv_ut : Disjoint V(P_sv) V(subgraphUnion P P_uc P_ct) := by
    rw [vertexSet_subgraphUnion, disjoint_union_right]
    refine ⟨?_, hdisj_sact.mono_left hP_sv.vertexSet_mono⟩
    rw [disjoint_left]
    intro z hz₁ hz₂
    have hz_a : z = a := by
      have : z ∈ V(P_sa) ∩ V(P_ac) := ⟨hP_sv.vertexSet_mono hz₁, hP_uc.vertexSet_mono hz₂⟩
      rwa [hinter_sa, mem_singleton_iff] at this
    subst hz_a
    have ha_v : z = v := by
      have : z ∈ V(P_sv) ∩ V(P_va) := ⟨hz₁, hpath_va.right_mem⟩
      rwa [hinter_v, mem_singleton_iff] at this
    exact hva_ne ha_v.symm
  obtain ⟨Q, hQK, hdisjQ⟩ := exists_detour_path hPK
    (hP_sv.trans hP_sa_le)
    (subgraphUnion_le (hP_va.trans hP_sa_le) (hP_au.trans hP_ac_le))
    (subgraphUnion_le (hP_uc.trans hP_ac_le) hP_ct_le)
    (hpath_sv.mono hP_sa_le) hpath_vu hpath_ut
    hinter_sv_vu hinter_vu_ut hdisj_sv_ut hRK.symm
    (by rw [hRP]; ext z; simp [or_comm])
  have ha_in_vu : a ∈ V(subgraphUnion P P_va P_au) \ {v, u} :=
    ⟨Or.inl hpath_va.right_mem, by simp [hva_ne.symm, hau_ne]⟩
  exact disjoint_left.mp hdisjQ ha_in_vu (hforced Q hQK)

/-- Given a three-way split `P = P_sa ∪ P_ac ∪ P_ct` at `a, c ∈ X ∪ {s, t}` with
`Disjoint (V(P_ac) \ {a, c}) (X ∪ {s, t})`, let `W` be the set of vertices in `V(K) \ V(P)` that
are in a component `C` of `K \ V(P)` having a neighbor in `V(P_ac) \ {a, c}`. Then no vertex of
`(V(P_ac) ∪ W) \ {a, c}` is adjacent in `G` to any vertex outside `V(P_ac) ∪ W`. -/
theorem no_out_of_open_interval_and_components {G H P P_sa P_ac P_ct : Graph α β}
    {Z : Set α} {s t a c : α}
    (hHG : H ≤ G) (hZ : Catches Z H)
    (hmax : ∀ H' : Graph α β, H ≤ H' → H' ≤ G → Catches Z H' →
      (∃ Q : Graph α β, IsGraphPathWithEnds G Q s t ∧ Avoids Q V(H')) → H' = H)
    (hPK : IsGraphPathWithEnds (deleteVertices G V(H)) P s t)
    (ha_mem : a ∈ {x ∈ V(deleteVertices G V(H)) | ∃ h ∈ V(H), G.Adj x h} ∪ {s, t})
    (hc_mem : c ∈ {x ∈ V(deleteVertices G V(H)) | ∃ h ∈ V(H), G.Adj x h} ∪ {s, t})
    (hP_sa_le : P_sa ≤ P) (hP_ac_le : P_ac ≤ P) (hP_ct_le : P_ct ≤ P)
    (hpath_sa : IsGraphPathWithEnds P P_sa s a)
    (hpath_ac : IsGraphPathWithEnds P P_ac a c)
    (hpath_ct : IsGraphPathWithEnds P P_ct c t)
    (hinter_sa : V(P_sa) ∩ V(P_ac) = {a})
    (hinter_ct : V(P_ac) ∩ V(P_ct) = {c})
    (hdisj_sact : Disjoint V(P_sa) V(P_ct))
    (hV_union : V(P_sa) ∪ V(P_ac) ∪ V(P_ct) = V(P))
    (hdisj_X : Disjoint (V(P_ac) \ {a, c})
      ({x ∈ V(deleteVertices G V(H)) | ∃ h ∈ V(H), G.Adj x h} ∪ {s, t})) :
    let K := deleteVertices G V(H)
    let W := {y ∈ V(deleteVertices K V(P)) |
      ∃ w ∈ V(P_ac) \ {a, c}, ∃ z ∈ V(reachableComponent (deleteVertices K V(P)) y), K.Adj w z}
    ∀ x ∈ (V(P_ac) ∪ W) \ {a, c}, ∀ y : α, G.Adj x y → y ∈ V(P_ac) ∪ W := by
  intro K W x ⟨hx_in, hx_not_ac⟩ y hxy_adj
  have hKG : K ≤ G := deleteVertices_le G V(H)
  have hX_sub_Q : ∀ Q : Graph α β, IsGraphPathWithEnds K Q s t →
      {x ∈ V(K) | ∃ h ∈ V(H), G.Adj x h} ⊆ V(Q) :=
    fun Q hQK z ⟨hzK, hadj⟩ => lemma_2_1_claim_1 hHG hZ hmax hQK hzK hadj
  have hX_sub_P : {x ∈ V(K) | ∃ h ∈ V(H), G.Adj x h} ⊆ V(P) := hX_sub_Q P hPK
  have hno_cross_path : ∀ u ∈ V(P_ac) \ {a, c}, ∀ v ∈ V(P) \ V(P_ac),
      ∀ R : Graph α β, IsGraphPathWithEnds K R u v → V(R) ∩ V(P) ≠ {u, v} := by
    intro u ⟨hu_ac, hu_not_ac⟩ v ⟨hvP, hv_not_ac⟩ R hRK hRP
    have hv_in : v ∈ V(P_sa) ∪ V(P_ct) := by
      have : v ∈ V(P_sa) ∪ V(P_ac) ∪ V(P_ct) := hV_union.symm ▸ hvP
      rcases this with (hv_sa | hv_ac) | hv_ct
      · exact Or.inl hv_sa
      · exact (hv_not_ac hv_ac).elim
      · exact Or.inr hv_ct
    rcases hv_in with hv_sa | hv_ct
    · apply detour_excludes_marked_vertex hPK hP_sa_le hP_ac_le hP_ct_le
        hpath_sa hpath_ac hpath_ct hinter_sa hinter_ct hdisj_sact ?_ hv_sa hu_ac ?_ ?_ hRK hRP
      · intro Q hQK
        rcases ha_mem with haX | (rfl | rfl)
        · exact hX_sub_Q Q hQK haX
        · exact hQK.left_mem
        · exact hQK.right_mem
      · exact fun h => hv_not_ac (h ▸ hpath_ac.left_mem)
      · exact fun h => hu_not_ac (by simp [h.symm])
    · apply detour_excludes_marked_vertex hPK.symm hP_ct_le hP_ac_le hP_sa_le
        hpath_ct.symm hpath_ac.symm hpath_sa.symm (by rw [inter_comm, hinter_ct])
        (by rw [inter_comm, hinter_sa]) hdisj_sact.symm ?_ hv_ct hu_ac ?_ ?_ hRK hRP
      · intro Q hQK
        rcases hc_mem with hcX | (rfl | rfl)
        · exact hX_sub_Q Q hQK.symm hcX
        · exact hQK.right_mem
        · exact hQK.left_mem
      · exact fun h => hv_not_ac (h ▸ hpath_ac.right_mem)
      · exact fun h => hu_not_ac (by simp [h.symm])
  rcases hxy_adj with ⟨e, hxy⟩
  rcases hx_in with hx_ac | hx_W
  · have hxP : x ∈ V(P) := hP_ac_le.vertexSet_mono hx_ac
    have hxK : x ∈ V(K) := hPK.1.vertexSet_mono hxP
    have hy_not_H : y ∉ V(H) := by
      intro hyH
      have hxX : x ∈ {z ∈ V(K) | ∃ h ∈ V(H), G.Adj z h} := ⟨hxK, y, hyH, ⟨e, hxy⟩⟩
      exact disjoint_left.mp hdisj_X ⟨hx_ac, hx_not_ac⟩ (Or.inl hxX)
    have hyK : y ∈ V(K) := ⟨hxy.right_mem, hy_not_H⟩
    have hxyK : K.IsLink e x y := (deleteVertices_isLink G V(H)).mpr ⟨hxy, hxK.2, hy_not_H⟩
    by_cases hyP : y ∈ V(P)
    · left
      by_contra hy_not_ac
      have hxy_ne : x ≠ y := fun h => hy_not_ac (h ▸ hx_ac)
      let W_xy : GraphWalk K x y := .cons hxyK (.nil hyK)
      have hW_xy : W_xy.IsSimple := by
        simp [GraphWalk.IsSimple, W_xy, hxy_ne]
      have hRK : IsGraphPathWithEnds K (walkSubgraph W_xy) x y :=
        isGraphPathWithEnds_walkSubgraph hW_xy
      have hRP : V(walkSubgraph W_xy) ∩ V(P) = {x, y} := by
        ext z
        simp only [vertexSet_walkSubgraph, W_xy, GraphWalk.support_cons, GraphWalk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false, mem_inter_iff, mem_ofPred_eq,
          mem_insert_iff, mem_singleton_iff]
        exact ⟨fun h => h.1, fun h => ⟨h, h.elim (fun h1 => h1 ▸ hxP) (fun h2 => h2 ▸ hyP)⟩⟩
      exact hno_cross_path x ⟨hx_ac, hx_not_ac⟩ y ⟨hyP, hy_not_ac⟩ (walkSubgraph W_xy) hRK hRP
    · have hy_KP : y ∈ V(deleteVertices K V(P)) := ⟨hyK, hyP⟩
      right
      exact ⟨hy_KP, x, ⟨hx_ac, hx_not_ac⟩, y, self_mem_reachableComponent hy_KP, ⟨e, hxyK⟩⟩
  · rcases hx_W with ⟨hx_KP, w, hw_ac, z, hz_reach, ⟨ewz, hewz⟩⟩
    have hxK : x ∈ V(K) := hx_KP.1
    have hx_not_P : x ∉ V(P) := hx_KP.2
    have hy_not_H : y ∉ V(H) := by
      intro hyH
      have hxX : x ∈ {u ∈ V(K) | ∃ h ∈ V(H), G.Adj u h} := ⟨hxK, y, hyH, ⟨e, hxy⟩⟩
      exact hx_not_P (hX_sub_P hxX)
    have hyK : y ∈ V(K) := ⟨hxy.right_mem, hy_not_H⟩
    have hxyK : K.IsLink e x y := (deleteVertices_isLink G V(H)).mpr ⟨hxy, hxK.2, hy_not_H⟩
    by_cases hyP : y ∈ V(P)
    · left
      by_contra hy_not_ac
      rw [vertexSet_reachableComponent] at hz_reach
      obtain ⟨_, ⟨W_xz⟩⟩ := hz_reach
      obtain ⟨W_zxK, hs_zx, _⟩ :=
        exists_walk_up_of_le (deleteVertices_le K V(P)) W_xz.reverse
      let W_wy : GraphWalk K w y :=
        .cons hewz (W_zxK.append (.cons hxyK (.nil hyK)))
      obtain ⟨R, hRK, hR_subV, _⟩ := exists_isGraphPathWithEnds_of_walk W_wy
      have hRP : V(R) ∩ V(P) = {w, y} := by
        ext u
        simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
        constructor
        · rintro ⟨huR, huP⟩
          have huW := hR_subV huR
          simp only [W_wy, GraphWalk.support_cons, GraphWalk.mem_support_append,
            GraphWalk.support_nil, List.mem_cons, List.not_mem_nil, or_false, hs_zx] at huW
          rcases huW with rfl | hu_xz | rfl | rfl
          · exact Or.inl rfl
          · have hu_not_P : u ∉ V(P) :=
              (W_xz.reverse.mem_vertexSet_of_mem_support hu_xz).2
            exact (hu_not_P huP).elim
          · exact (hx_not_P huP).elim
          · exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨hRK.left_mem, hP_ac_le.vertexSet_mono hw_ac.1⟩
          · exact ⟨hRK.right_mem, hyP⟩
      exact hno_cross_path w hw_ac y ⟨hyP, hy_not_ac⟩ R hRK hRP
    · right
      have hy_KP : y ∈ V(deleteVertices K V(P)) := ⟨hyK, hyP⟩
      have hxy_KP : (deleteVertices K V(P)).IsLink e x y :=
        (deleteVertices_isLink K V(P)).mpr ⟨hxyK, hx_not_P, hyP⟩
      have hcomp_eq : reachableComponent (deleteVertices K V(P)) y =
          reachableComponent (deleteVertices K V(P)) x := by
        refine isGraphComponent_eq_of_mem_inter
          (isGraphComponent_reachableComponent hy_KP)
          (isGraphComponent_reachableComponent hx_KP)
          ⟨y, self_mem_reachableComponent hy_KP, ?_⟩
        exact (mem_graphComponent_iff_of_isLink
          (isGraphComponent_reachableComponent hx_KP) hxy_KP).mp
          (self_mem_reachableComponent hx_KP)
      exact ⟨hy_KP, w, hw_ac, z, hcomp_eq.symm ▸ hz_reach, ⟨ewz, hewz⟩⟩

private theorem separation_of_path_interval {G H P : Graph α β}
    {Z : Set α} {s t : α}
    (hHG : H ≤ G) (hZ : Catches Z H)
    (hmax : ∀ H' : Graph α β, H ≤ H' → H' ≤ G → Catches Z H' →
      (∃ Q : Graph α β, IsGraphPathWithEnds G Q s t ∧ Avoids Q V(H')) → H' = H)
    (hPK : IsGraphPathWithEnds (deleteVertices G V(H)) P s t) :
    let K := deleteVertices G V(H)
    let X : Set α := {x ∈ V(K) | ∃ h ∈ V(H), G.Adj x h}
    let Y : Set α := X ∪ {s, t}
    ∀ a ∈ Y, ∀ c ∈ Y, a ≠ c →
      ∀ P_sa P_ac P_ct : Graph α β,
      P_sa ≤ P → P_ac ≤ P → P_ct ≤ P →
      IsGraphPathWithEnds P P_sa s a →
      IsGraphPathWithEnds P P_ac a c →
      IsGraphPathWithEnds P P_ct c t →
      V(P_sa) ∩ V(P_ac) = {a} →
      V(P_ac) ∩ V(P_ct) = {c} →
      Disjoint V(P_sa) V(P_ct) →
      V(P_sa) ∪ V(P_ac) ∪ V(P_ct) = V(P) →
      Disjoint (V(P_ac) \ {a, c}) Y →
      let W := {y ∈ V(deleteVertices K V(P)) |
        ∃ w ∈ V(P_ac) \ {a, c}, ∃ z ∈ V(reachableComponent (deleteVertices K V(P)) y), K.Adj w z}
      V(P_ac) ∪ W ≠ {a, c} →
      ∃ G₁ G₂ : Graph α β,
        IsGraphSeparation G G₁ G₂ ∧
        {s, t} ⊆ V(G₁) ∧
        (V(G₁) ∩ V(G₂)).ncard = 2 ∧
        (E(P) ∩ E(G₂)).Nonempty ∧
        subgraphInter G G₁ G₂ ≤ P ∧
        H ≤ G₁ ∧
        V(G₁) ≠ V(G) := by
  intro K X Y
  have hsY : s ∈ Y := Or.inr (Or.inl rfl)
  have htY : t ∈ Y := Or.inr (Or.inr rfl)
  intro a haY c hcY hac P_sa P_ac P_ct hP_sa hP_ac hP_ct hpath_sa hpath_ac hpath_ct
    hinter_sa hinter_ct hdisj_sact hV_union hdisj_Y W hne_ac
  have haP : a ∈ V(P) := hP_ac.vertexSet_mono hpath_ac.left_mem
  have hcP : c ∈ V(P) := hP_ac.vertexSet_mono hpath_ac.right_mem
  have hV₂_sub : V(P_ac) ∪ W ⊆ V(K) := by
    rintro z (hz_ac | hz_W)
    · exact hPK.1.vertexSet_mono (hP_ac.vertexSet_mono hz_ac)
    · exact hz_W.1.1
  have haV₂ : a ∈ V(P_ac) ∪ W := Or.inl hpath_ac.left_mem
  have hcV₂ : c ∈ V(P_ac) ∪ W := Or.inl hpath_ac.right_mem
  have hs_not : s ∉ (V(P_ac) ∪ W) \ {a, c} := by
    rintro ⟨hs_ac | hs_W, hs_ne⟩
    · exact disjoint_left.mp hdisj_Y ⟨hs_ac, hs_ne⟩ hsY
    · exact hs_W.1.2 hPK.left_mem
  have ht_not : t ∉ (V(P_ac) ∪ W) \ {a, c} := by
    rintro ⟨ht_ac | ht_W, ht_ne⟩
    · exact disjoint_left.mp hdisj_Y ⟨ht_ac, ht_ne⟩ htY
    · exact ht_W.1.2 hPK.right_mem
  have hno_out : ∀ x ∈ (V(P_ac) ∪ W) \ {a, c}, ∀ y : α, G.Adj x y → y ∈ V(P_ac) ∪ W :=
    no_out_of_open_interval_and_components hHG hZ hmax hPK haY hcY
      hP_sa hP_ac hP_ct hpath_sa hpath_ac hpath_ct hinter_sa hinter_ct hdisj_sact hV_union hdisj_Y
  have hEP_inter : (E(P) ∩ E(K.induce (V(P_ac) ∪ W))).Nonempty := by
    obtain ⟨e₀, he₀⟩ := nonempty_edgeSet_of_isGraphPathWithEnds_ne hpath_ac hac
    obtain ⟨x₀, y₀, hx₀y₀⟩ := P_ac.exists_isLink_of_mem_edgeSet he₀
    have hx₀y₀P : P.IsLink e₀ x₀ y₀ := hx₀y₀.mono hP_ac
    have hx₀y₀K : K.IsLink e₀ x₀ y₀ := hx₀y₀P.mono hPK.1
    have hx₀y₀_ind : (K.induce (V(P_ac) ∪ W)).IsLink e₀ x₀ y₀ := by
      rw [induce_isLink]
      exact ⟨hx₀y₀K, Or.inl hx₀y₀.left_mem, Or.inl hx₀y₀.right_mem⟩
    exact ⟨e₀, hx₀y₀P.edge_mem, hx₀y₀_ind.edge_mem⟩
  exact exists_separation_of_isolated_subset hHG hPK hac haP hcP (V(P_ac) ∪ W)
    hV₂_sub haV₂ hcV₂ hs_not ht_not hne_ac hno_out hEP_inter

private theorem separation_of_path_interval_and_component {G H P C : Graph α β}
    {Z : Set α} {s t y₀ : α}
    (hHG : H ≤ G) (hZ : Catches Z H)
    (hmax : ∀ H' : Graph α β, H ≤ H' → H' ≤ G → Catches Z H' →
      (∃ Q : Graph α β, IsGraphPathWithEnds G Q s t ∧ Avoids Q V(H')) → H' = H)
    (hPK : IsGraphPathWithEnds (deleteVertices G V(H)) P s t)
    (hC_comp : IsGraphComponent C (deleteVertices (deleteVertices G V(H)) V(P)))
    (hy₀C : y₀ ∈ V(C)) (hy₀_not_P : y₀ ∉ V(P)) :
    let K := deleteVertices G V(H)
    let X : Set α := {x ∈ V(K) | ∃ h ∈ V(H), G.Adj x h}
    let Y : Set α := X ∪ {s, t}
    ∀ a ∈ Y, ∀ c ∈ Y, a ≠ c →
      ∀ P_sa P_ac P_ct : Graph α β,
      P_sa ≤ P → P_ac ≤ P → P_ct ≤ P →
      IsGraphPathWithEnds P P_sa s a →
      IsGraphPathWithEnds P P_ac a c →
      IsGraphPathWithEnds P P_ct c t →
      V(P_sa) ∩ V(P_ac) = {a} →
      V(P_ac) ∩ V(P_ct) = {c} →
      Disjoint V(P_sa) V(P_ct) →
      V(P_sa) ∪ V(P_ac) ∪ V(P_ct) = V(P) →
      Disjoint (V(P_ac) \ {a, c}) Y →
      (∀ z ∈ V(C), ∀ w ∈ V(P), K.Adj z w → w ∈ V(P_ac)) →
      ∃ G₁ G₂ : Graph α β,
        IsGraphSeparation G G₁ G₂ ∧
        {s, t} ⊆ V(G₁) ∧
        (V(G₁) ∩ V(G₂)).ncard = 2 ∧
        (E(P) ∩ E(G₂)).Nonempty ∧
        subgraphInter G G₁ G₂ ≤ P ∧
        H ≤ G₁ ∧
        V(G₁) ≠ V(G) := by
  intro K X Y
  have hsY : s ∈ Y := Or.inr (Or.inl rfl)
  have htY : t ∈ Y := Or.inr (Or.inr rfl)
  have hX_sub_Q : ∀ Q : Graph α β, IsGraphPathWithEnds K Q s t → X ⊆ V(Q) :=
    fun Q hQK z ⟨hzK, hadj⟩ => lemma_2_1_claim_1 hHG hZ hmax hQK hzK hadj
  intro a haY c hcY hac P_sa P_ac P_ct hP_sa hP_ac hP_ct hpath_sa hpath_ac hpath_ct
    hinter_sa hinter_ct hdisj_sact hV_union hdisj_Y hC_nb_in_ac
  let W := {y ∈ V(deleteVertices K V(P)) |
    ∃ w ∈ V(P_ac) \ {a, c}, ∃ z ∈ V(reachableComponent (deleteVertices K V(P)) y), K.Adj w z}
  let V₂ := V(C) ∪ (V(P_ac) ∪ W)
  have haP : a ∈ V(P) := hP_ac.vertexSet_mono hpath_ac.left_mem
  have hcP : c ∈ V(P) := hP_ac.vertexSet_mono hpath_ac.right_mem
  have hV₂_sub : V₂ ⊆ V(K) := by
    rintro z (hzC | hz_ac | hz_W)
    · exact (hC_comp.1.vertexSet_mono hzC).1
    · exact hPK.1.vertexSet_mono (hP_ac.vertexSet_mono hz_ac)
    · exact hz_W.1.1
  have haV₂ : a ∈ V₂ := Or.inr (Or.inl hpath_ac.left_mem)
  have hcV₂ : c ∈ V₂ := Or.inr (Or.inl hpath_ac.right_mem)
  have hs_not : s ∉ V₂ \ {a, c} := by
    rintro ⟨hsC | hs_ac | hs_W, hs_ne⟩
    · exact (hC_comp.1.vertexSet_mono hsC).2 hPK.left_mem
    · exact disjoint_left.mp hdisj_Y ⟨hs_ac, hs_ne⟩ hsY
    · exact hs_W.1.2 hPK.left_mem
  have ht_not : t ∉ V₂ \ {a, c} := by
    rintro ⟨htC | ht_ac | ht_W, ht_ne⟩
    · exact (hC_comp.1.vertexSet_mono htC).2 hPK.right_mem
    · exact disjoint_left.mp hdisj_Y ⟨ht_ac, ht_ne⟩ htY
    · exact ht_W.1.2 hPK.right_mem
  have hV₂_ne : V₂ ≠ {a, c} := by
    intro hV₂_eq
    have hy₀_ac : y₀ ∈ ({a, c} : Set α) := hV₂_eq ▸ Or.inl hy₀C
    rcases hy₀_ac with rfl | rfl
    · exact hy₀_not_P haP
    · exact hy₀_not_P hcP
  have hno_out_acW : ∀ x ∈ (V(P_ac) ∪ W) \ {a, c}, ∀ y : α, G.Adj x y → y ∈ V(P_ac) ∪ W :=
    no_out_of_open_interval_and_components hHG hZ hmax hPK haY hcY
      hP_sa hP_ac hP_ct hpath_sa hpath_ac hpath_ct hinter_sa hinter_ct hdisj_sact hV_union hdisj_Y
  have hno_out : ∀ x ∈ V₂ \ {a, c}, ∀ y : α, G.Adj x y → y ∈ V₂ := by
    rintro x ⟨hxC | hx_acW, hx_not_ac⟩ y hxy_adj
    · rcases hxy_adj with ⟨e, hxy⟩
      have hx_KP : x ∈ V(deleteVertices K V(P)) := hC_comp.1.vertexSet_mono hxC
      have hy_not_H : y ∉ V(H) := by
        intro hyH
        have hxX : x ∈ X := ⟨hx_KP.1, y, hyH, ⟨e, hxy⟩⟩
        exact hx_KP.2 (hX_sub_Q P hPK hxX)
      have hyK : y ∈ V(K) := ⟨hxy.right_mem, hy_not_H⟩
      have hxyK : K.IsLink e x y := (deleteVertices_isLink G V(H)).mpr ⟨hxy, hx_KP.1.2, hy_not_H⟩
      by_cases hyP : y ∈ V(P)
      · exact Or.inr (Or.inl (hC_nb_in_ac x hxC y hyP ⟨e, hxyK⟩))
      · left
        have hxy_KP : (deleteVertices K V(P)).IsLink e x y :=
          (deleteVertices_isLink K V(P)).mpr ⟨hxyK, hx_KP.2, hyP⟩
        exact (mem_graphComponent_iff_of_isLink hC_comp hxy_KP).mp hxC
    · exact Or.inr (hno_out_acW x ⟨hx_acW, hx_not_ac⟩ y hxy_adj)
  have hEP_inter : (E(P) ∩ E(K.induce V₂)).Nonempty := by
    obtain ⟨e₀, he₀⟩ := nonempty_edgeSet_of_isGraphPathWithEnds_ne hpath_ac hac
    obtain ⟨x₀, y₀', hx₀y₀⟩ := P_ac.exists_isLink_of_mem_edgeSet he₀
    have hx₀y₀P : P.IsLink e₀ x₀ y₀' := hx₀y₀.mono hP_ac
    have hx₀y₀K : K.IsLink e₀ x₀ y₀' := hx₀y₀P.mono hPK.1
    have hx₀y₀_ind : (K.induce V₂).IsLink e₀ x₀ y₀' := by
      rw [induce_isLink]
      exact ⟨hx₀y₀K, Or.inr (Or.inl hx₀y₀.left_mem), Or.inr (Or.inl hx₀y₀.right_mem)⟩
    exact ⟨e₀, hx₀y₀P.edge_mem, hx₀y₀_ind.edge_mem⟩
  exact exists_separation_of_isolated_subset hHG hPK hac haP hcP V₂
    hV₂_sub haV₂ hcV₂ hs_not ht_not hV₂_ne hno_out hEP_inter

private theorem separation_of_missing_edge {G H P : Graph α β} {Z : Set α} {s t : α}
    (hG_loopless : ∀ x : α, ¬ G.Adj x x)
    (hG_simple : ∀ e₁ e₂ x y, G.IsLink e₁ x y → G.IsLink e₂ x y → e₁ = e₂)
    (hHG : H ≤ G) (hZ : Catches Z H)
    (hmax : ∀ H' : Graph α β, H ≤ H' → H' ≤ G → Catches Z H' →
      (∃ Q : Graph α β, IsGraphPathWithEnds G Q s t ∧ Avoids Q V(H')) → H' = H)
    (hPK : IsGraphPathWithEnds (deleteVertices G V(H)) P s t)
    (hPK_eq : P ≠ deleteVertices G V(H)) (hVP_eq : V(P) = V(deleteVertices G V(H))) :
    ∃ G₁ G₂ : Graph α β,
      IsGraphSeparation G G₁ G₂ ∧
      {s, t} ⊆ V(G₁) ∧
      (V(G₁) ∩ V(G₂)).ncard = 2 ∧
      (E(P) ∩ E(G₂)).Nonempty ∧
      subgraphInter G G₁ G₂ ≤ P ∧
      H ≤ G₁ ∧
      V(G₁) ≠ V(G) := by
  classical
  let K := deleteVertices G V(H)
  have hKG : K ≤ G := deleteVertices_le G V(H)
  let X : Set α := {x ∈ V(K) | ∃ h ∈ V(H), G.Adj x h}
  let Y : Set α := X ∪ {s, t}
  have hsY : s ∈ Y := Or.inr (Or.inl rfl)
  have htY : t ∈ Y := Or.inr (Or.inr rfl)
  have hX_sub_Q : ∀ Q : Graph α β, IsGraphPathWithEnds K Q s t → X ⊆ V(Q) :=
    fun Q hQK z ⟨hzK, hadj⟩ => lemma_2_1_claim_1 hHG hZ hmax hQK hzK hadj
  have hY_sub_Q : ∀ Q : Graph α β, IsGraphPathWithEnds K Q s t → Y ⊆ V(Q) := by
    intro Q hQK z hzY
    rcases hzY with hzX | (rfl | rfl)
    · exact hX_sub_Q Q hQK hzX
    · exact hQK.left_mem
    · exact hQK.right_mem
  have hEP_ne : E(P) ≠ E(K) := fun hE =>
    hPK_eq ((Compatible.of_le_le hPK.1 le_rfl).ext hVP_eq hE)
  have hssub : E(P) ⊂ E(K) := ⟨hPK.1.edgeSet_mono, fun h => hEP_ne (Subset.antisymm
    hPK.1.edgeSet_mono h)⟩
  obtain ⟨e₀, he₀K, he₀_not_P⟩ := exists_of_ssubset hssub
  obtain ⟨u, v, huvK⟩ := K.exists_isLink_of_mem_edgeSet he₀K
  have huP : u ∈ V(P) := hVP_eq.symm ▸ huvK.left_mem
  have hvP : v ∈ V(P) := hVP_eq.symm ▸ huvK.right_mem
  have huv_ne : u ≠ v := fun h => hG_loopless u (h ▸ (huvK.mono hKG).adj)
  -- Let `R` be the 1-edge path `walkSubgraph (.cons huvK (.nil huvK.right_mem))` in `K`.
  let W_uv : GraphWalk K u v := .cons huvK (.nil huvK.right_mem)
  have hW_uv : W_uv.IsSimple := by simp [GraphWalk.IsSimple, W_uv, huv_ne]
  have hRK : IsGraphPathWithEnds K (walkSubgraph W_uv) u v :=
    isGraphPathWithEnds_walkSubgraph hW_uv
  have hRP : V(walkSubgraph W_uv) ∩ V(P) = {u, v} := by
    ext z
    simp only [vertexSet_walkSubgraph, W_uv, GraphWalk.support_cons, GraphWalk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false, mem_inter_iff, mem_ofPred_eq,
      mem_insert_iff, mem_singleton_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, h.elim (fun h1 => h1 ▸ huP) (fun h2 => h2 ▸ hvP)⟩⟩
  have hno_Y : ∀ u' v' : α, ({u', v'} : Set α) = {u, v} →
      ∀ P_su P_uv P_vt : Graph α β,
      P_su ≤ P → P_uv ≤ P → P_vt ≤ P →
      IsGraphPathWithEnds P P_su s u' →
      IsGraphPathWithEnds P P_uv u' v' →
      IsGraphPathWithEnds P P_vt v' t →
      V(P_su) ∩ V(P_uv) = {u'} →
      V(P_uv) ∩ V(P_vt) = {v'} →
      Disjoint V(P_su) V(P_vt) →
      Disjoint (V(P_uv) \ {u', v'}) Y := by
    intro u' v' huv_eq P_su P_uv P_vt hP_su hP_uv hP_vt hpath_su hpath_uv hpath_vt
      hinter_su hinter_vt hdisj_suvt
    have hRK' : IsGraphPathWithEnds K (walkSubgraph W_uv) u' v' := by
      have hu'_in : u' = u ∨ u' = v := by
        have : u' ∈ ({u, v} : Set α) := huv_eq ▸ by simp
        simpa using this
      have hv'_in : v' = u ∨ v' = v := by
        have : v' ∈ ({u, v} : Set α) := huv_eq ▸ by simp
        simpa using this
      rcases hu'_in with hu' | hu' <;> rcases hv'_in with hv' | hv'
      · rw [hu', hv'] at huv_eq
        have : v = u := by
          have : v ∈ ({u, u} : Set α) := huv_eq ▸ by simp
          simpa using this
        exact (huv_ne this.symm).elim
      · rw [hu', hv']; exact hRK
      · rw [hu', hv']; exact hRK.symm
      · rw [hu', hv'] at huv_eq
        have : u = v := by
          have : u ∈ ({v, v} : Set α) := huv_eq ▸ by simp
          simpa using this
        exact (huv_ne this).elim
    obtain ⟨Q, hQK, hdisjQ⟩ := exists_detour_path hPK hP_su hP_uv hP_vt
      hpath_su hpath_uv hpath_vt hinter_su hinter_vt hdisj_suvt hRK' (huv_eq ▸ hRP)
    exact hdisjQ.mono_right (hY_sub_Q Q hQK)
  obtain ⟨a, haY, c, hcY, hac, P_sa, P_ac, P_ct,
    hP_sa, hP_ac, hP_ct, hpath_sa, hpath_ac, hpath_ct,
    hinter_sa, hinter_ct, hdisj_sact, hV_union, hu_ac, hv_ac, hdisj_Y⟩ :=
    exists_minimal_Y_interval_containing_pair hPK hsY htY huP hvP huv_ne hno_Y
  -- Now we check if `V(P_ac) = {a, c}`. If `V(P_ac) = {a, c}`, then `{u, v} ⊆ {a, c}`, so
  -- `e₀` links `a` and `c` in `G`, while `P_ac` also has an edge `e₁ ∈ E(P_ac) ⊆ E(P)` linking
  -- `a` and `c` in `G`, contradicting `hG_simple` and `e₀ ∉ E(P)`!
  have hVP_ac_ne : V(P_ac) ≠ {a, c} := by
    intro hVP_ac_eq
    have hu_in_ac : u = a ∨ u = c := by
      have : u ∈ ({a, c} : Set α) := hVP_ac_eq ▸ hu_ac
      simpa using this
    have hv_in_ac : v = a ∨ v = c := by
      have : v ∈ ({a, c} : Set α) := hVP_ac_eq ▸ hv_ac
      simpa using this
    obtain ⟨e₁, he₁⟩ := nonempty_edgeSet_of_isGraphPathWithEnds_ne hpath_ac hac
    obtain ⟨x₁, y₁, hx₁y₁⟩ := P_ac.exists_isLink_of_mem_edgeSet he₁
    have hx₁_in : x₁ = a ∨ x₁ = c := by
      have : x₁ ∈ ({a, c} : Set α) := hVP_ac_eq ▸ hx₁y₁.left_mem
      simpa using this
    have hy₁_in : y₁ = a ∨ y₁ = c := by
      have : y₁ ∈ ({a, c} : Set α) := hVP_ac_eq ▸ hx₁y₁.right_mem
      simpa using this
    have hx₁y₁_ne : x₁ ≠ y₁ := fun h =>
      hG_loopless x₁ (h ▸ ((hx₁y₁.mono hP_ac).mono (hPK.1.trans hKG)).adj)
    have he₁_ac : G.IsLink e₁ a c := by
      have hG₁ := (hx₁y₁.mono hP_ac).mono (hPK.1.trans hKG)
      rcases hx₁_in with rfl | rfl <;> rcases hy₁_in with rfl | rfl
      · exact (hx₁y₁_ne rfl).elim
      · exact hG₁
      · exact hG₁.symm
      · exact (hx₁y₁_ne rfl).elim
    have he₀_ac : G.IsLink e₀ a c := by
      have hG₀ := huvK.mono hKG
      rcases hu_in_ac with rfl | rfl <;> rcases hv_in_ac with rfl | rfl
      · exact (huv_ne rfl).elim
      · exact hG₀
      · exact hG₀.symm
      · exact (huv_ne rfl).elim
    have he₀_eq_e₁ : e₀ = e₁ := hG_simple e₀ e₁ a c he₀_ac he₁_ac
    exact he₀_not_P (he₀_eq_e₁ ▸ hP_ac.edgeSet_mono he₁)
  refine separation_of_path_interval hHG hZ hmax hPK a haY c hcY hac P_sa P_ac P_ct
    hP_sa hP_ac hP_ct hpath_sa hpath_ac hpath_ct hinter_sa hinter_ct hdisj_sact hV_union hdisj_Y ?_
  intro hVW_eq
  apply hVP_ac_ne
  refine Subset.antisymm (fun z hz => hVW_eq ▸ Or.inl hz) ?_
  rintro z (rfl | rfl)
  · exact hpath_ac.left_mem
  · exact hpath_ac.right_mem

/-- **Graph Minors IX, (2.1)** (page 43):
"Let $G$ be a simple graph and let $Z \subseteq V(G)$. Let $s, t \in V(G)$ be distinct and
such that there is a path between $s$ and $t$ avoiding $Z$. Choose a subgraph $H$ of $G$
maximal such that $Z$ catches $H$, and there is a path of $G$ between $s$ and $t$ avoiding
$V(H)$. Let $K = G \setminus V(H)$, and let $P$ be a path of $K$ between $s$ and $t$. Then
either $P = K$, or there is a separation $(G_1, G_2)$ of $G$ with $\{s, t\} \subseteq
V(G_1)$, $|V(G_1 \cap G_2)| = 2$, $E(P \cap G_2) \ne \emptyset$ (and hence $G_1 \cap G_2
\subseteq P$), $H \subseteq G_1$, and $V(G_1) \ne V(G)$." -/
theorem theorem_2_1_proof {G H P : Graph α β} {Z : Set α} {s t : α}
    (hG_loopless : ∀ x : α, ¬ G.Adj x x)
    (hG_simple : ∀ e₁ e₂ x y, G.IsLink e₁ x y → G.IsLink e₂ x y → e₁ = e₂)
    (hst : s ≠ t)
    (hHG : H ≤ G) (hZ : Catches Z H)
    (hmax : ∀ H' : Graph α β, H ≤ H' → H' ≤ G → Catches Z H' →
      (∃ Q : Graph α β, IsGraphPathWithEnds G Q s t ∧ Avoids Q V(H')) → H' = H)
    (hPK : IsGraphPathWithEnds (deleteVertices G V(H)) P s t) :
    P = deleteVertices G V(H) ∨
      ∃ G₁ G₂ : Graph α β,
        IsGraphSeparation G G₁ G₂ ∧
        {s, t} ⊆ V(G₁) ∧
        (V(G₁) ∩ V(G₂)).ncard = 2 ∧
        (E(P) ∩ E(G₂)).Nonempty ∧
        subgraphInter G G₁ G₂ ≤ P ∧
        H ≤ G₁ ∧
        V(G₁) ≠ V(G) := by
  classical
  let K := deleteVertices G V(H)
  let X : Set α := {x ∈ V(K) | ∃ h ∈ V(H), G.Adj x h}
  let Y : Set α := X ∪ {s, t}
  have hsY : s ∈ Y := Or.inr (Or.inl rfl)
  have htY : t ∈ Y := Or.inr (Or.inr rfl)
  have hX_sub_Q : ∀ Q : Graph α β, IsGraphPathWithEnds K Q s t → X ⊆ V(Q) :=
    fun Q hQK z ⟨hzK, hadj⟩ => lemma_2_1_claim_1 hHG hZ hmax hQK hzK hadj
  have hY_sub_Q : ∀ Q : Graph α β, IsGraphPathWithEnds K Q s t → Y ⊆ V(Q) := by
    intro Q hQK z hzY
    rcases hzY with hzX | (rfl | rfl)
    · exact hX_sub_Q Q hQK hzX
    · exact hQK.left_mem
    · exact hQK.right_mem
  -- Helper: given any three-way split `P = P_sa ∪ P_ac ∪ P_ct` at `a, c ∈ Y` with `a ≠ c` and
  -- `Disjoint (V(P_ac) \ {a, c}) Y`, let `W(a, c)` be the union of components of `K \ V(P)` with a
  -- neighbor in `V(P_ac) \ {a, c}`; if `V(P_ac) ∪ W(a, c) ≠ {a, c}`, then we get the desired
  -- separation `(G₁, G₂)`!
  by_cases hPK_eq : P = K
  · exact Or.inl hPK_eq
  · right
    -- Suppose `P ≠ K`. Since `P ≤ K`, either `V(P) ≠ V(K)` or `V(P) = V(K)` and `E(P) ≠ E(K)`.
    by_cases hVP_eq : V(P) = V(K)
    · exact separation_of_missing_edge hG_loopless hG_simple hHG hZ hmax hPK hPK_eq hVP_eq
    · -- Case 2: `V(P) ≠ V(K)`. Let `y₀ ∈ V(K) \ V(P)` and let `C` be the component of `K \ V(P)`
      -- containing `y₀`.
      have hssub : V(P) ⊂ V(K) :=
        ⟨hPK.1.vertexSet_mono, fun h => hVP_eq (Subset.antisymm hPK.1.vertexSet_mono h)⟩
      obtain ⟨y₀, hy₀K, hy₀_not_P⟩ := exists_of_ssubset hssub
      have hy₀_KP : y₀ ∈ V(deleteVertices K V(P)) := ⟨hy₀K, hy₀_not_P⟩
      let C := reachableComponent (deleteVertices K V(P)) y₀
      have hC_comp : IsGraphComponent C (deleteVertices K V(P)) :=
        isGraphComponent_reachableComponent hy₀_KP
      have hy₀C : y₀ ∈ V(C) := self_mem_reachableComponent hy₀_KP
      have hsep_of_C_in_ac :=
        separation_of_path_interval_and_component hHG hZ hmax hPK hC_comp hy₀C hy₀_not_P
      -- Now let `N_C = {w ∈ V(P) | ∃ z ∈ V(C), K.Adj z w}` be the set of neighbors of `V(C)` in
      -- `V(P)`.
      -- Either `N_C` has at least two distinct vertices `u ≠ v`, or `N_C ⊆ {u}` for some `u ∈
      -- V(P)`.
      by_cases htwo_nb : ∃ u ∈ V(P), ∃ v ∈ V(P), u ≠ v ∧
          (∃ z₁ ∈ V(C), K.Adj z₁ u) ∧ (∃ z₂ ∈ V(C), K.Adj z₂ v)
      · obtain ⟨u, huP, v, hvP, huv_ne, ⟨z₁, hz₁C, ⟨e₁, hz₁u⟩⟩, ⟨z₂, hz₂C, ⟨e₂, hz₂v⟩⟩⟩ := htwo_nb
        -- First construct a path `R` in `K` from `u` to `v` with `V(R) ∩ V(P) = {u, v}`:
        have hpath_through_C : ∀ w₁ ∈ V(P), ∀ w₂ ∈ V(P), w₁ ≠ w₂ →
            (∃ z ∈ V(C), K.Adj z w₁) → (∃ z ∈ V(C), K.Adj z w₂) →
            ∃ R : Graph α β, IsGraphPathWithEnds K R w₁ w₂ ∧ V(R) ∩ V(P) = {w₁, w₂} := by
          intro w₁ hw₁P w₂ hw₂P hw₁₂ ⟨x₁, hx₁C, ⟨ex₁, hex₁⟩⟩ ⟨x₂, hx₂C, ⟨ex₂, hex₂⟩⟩
          have hx₁_reach : x₁ ∈ V(reachableComponent (deleteVertices K V(P)) y₀) := hx₁C
          have hx₂_reach : x₂ ∈ V(reachableComponent (deleteVertices K V(P)) y₀) := hx₂C
          rw [vertexSet_reachableComponent] at hx₁_reach hx₂_reach
          obtain ⟨_, ⟨W₁⟩⟩ := hx₁_reach
          obtain ⟨_, ⟨W₂⟩⟩ := hx₂_reach
          let W₁₂ : GraphWalk (deleteVertices K V(P)) x₁ x₂ := W₁.reverse.append W₂
          obtain ⟨W₁₂K, hs₁₂, _⟩ := exists_walk_up_of_le (deleteVertices_le K V(P)) W₁₂
          have hw₂K : w₂ ∈ V(K) := hPK.1.vertexSet_mono hw₂P
          let W_full : GraphWalk K w₁ w₂ :=
            .cons hex₁.symm (W₁₂K.append (.cons hex₂ (.nil hw₂K)))
          obtain ⟨R, hRK, hR_subV, _⟩ := exists_isGraphPathWithEnds_of_walk W_full
          refine ⟨R, hRK, ?_⟩
          ext z
          simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
          constructor
          · rintro ⟨hzR, hzP⟩
            have hzW := hR_subV hzR
            simp only [W_full, GraphWalk.support_cons, GraphWalk.mem_support_append,
              GraphWalk.support_nil, List.mem_cons, List.not_mem_nil, or_false, hs₁₂] at hzW
            rcases hzW with rfl | hz₁₂ | rfl | rfl
            · exact Or.inl rfl
            · exact ((W₁₂.mem_vertexSet_of_mem_support hz₁₂).2 hzP).elim
            · exact ((hC_comp.1.vertexSet_mono hx₂C).2 hzP).elim
            · exact Or.inr rfl
          · rintro (rfl | rfl)
            · exact ⟨hRK.left_mem, hw₁P⟩
            · exact ⟨hRK.right_mem, hw₂P⟩
        obtain ⟨R_uv, hRK_uv, hRP_uv⟩ :=
          hpath_through_C u huP v hvP huv_ne ⟨z₁, hz₁C, ⟨e₁, hz₁u⟩⟩ ⟨z₂, hz₂C, ⟨e₂, hz₂v⟩⟩
        have hno_Y : ∀ u' v' : α, ({u', v'} : Set α) = {u, v} →
            ∀ P_su P_uv P_vt : Graph α β,
            P_su ≤ P → P_uv ≤ P → P_vt ≤ P →
            IsGraphPathWithEnds P P_su s u' →
            IsGraphPathWithEnds P P_uv u' v' →
            IsGraphPathWithEnds P P_vt v' t →
            V(P_su) ∩ V(P_uv) = {u'} →
            V(P_uv) ∩ V(P_vt) = {v'} →
            Disjoint V(P_su) V(P_vt) →
            Disjoint (V(P_uv) \ {u', v'}) Y := by
          intro u' v' huv_eq P_su P_uv P_vt hP_su hP_uv hP_vt hpath_su hpath_uv hpath_vt
            hinter_su hinter_vt hdisj_suvt
          have hRK' : IsGraphPathWithEnds K R_uv u' v' := by
            have hu'_in : u' = u ∨ u' = v := by
              have : u' ∈ ({u, v} : Set α) := huv_eq ▸ by simp
              simpa using this
            have hv'_in : v' = u ∨ v' = v := by
              have : v' ∈ ({u, v} : Set α) := huv_eq ▸ by simp
              simpa using this
            rcases hu'_in with hu' | hu' <;> rcases hv'_in with hv' | hv'
            · rw [hu', hv'] at huv_eq
              have : v = u := by
                have : v ∈ ({u, u} : Set α) := huv_eq ▸ by simp
                simpa using this
              exact (huv_ne this.symm).elim
            · rw [hu', hv']; exact hRK_uv
            · rw [hu', hv']; exact hRK_uv.symm
            · rw [hu', hv'] at huv_eq
              have : u = v := by
                have : u ∈ ({v, v} : Set α) := huv_eq ▸ by simp
                simpa using this
              exact (huv_ne this).elim
          obtain ⟨Q, hQK, hdisjQ⟩ := exists_detour_path hPK hP_su hP_uv hP_vt
            hpath_su hpath_uv hpath_vt hinter_su hinter_vt hdisj_suvt hRK' (huv_eq ▸ hRP_uv)
          exact hdisjQ.mono_right (hY_sub_Q Q hQK)
        obtain ⟨a, haY, c, hcY, hac, P_sa, P_ac, P_ct,
          hP_sa, hP_ac, hP_ct, hpath_sa, hpath_ac, hpath_ct,
          hinter_sa, hinter_ct, hdisj_sact, hV_union, hu_ac, hv_ac, hdisj_Y⟩ :=
          exists_minimal_Y_interval_containing_pair hPK hsY htY huP hvP huv_ne hno_Y
        refine hsep_of_C_in_ac a haY c hcY hac P_sa P_ac P_ct
          hP_sa hP_ac hP_ct hpath_sa hpath_ac hpath_ct hinter_sa hinter_ct hdisj_sact hV_union
            hdisj_Y ?_
        intro z hzC w hwP hzw
        by_contra hw_not_ac
        have hw_in : w ∈ V(P_sa) ∪ V(P_ct) := by
          have : w ∈ V(P_sa) ∪ V(P_ac) ∪ V(P_ct) := hV_union.symm ▸ hwP
          rcases this with (hw_sa | hw_ac) | hw_ct
          · exact Or.inl hw_sa
          · exact (hw_not_ac hw_ac).elim
          · exact Or.inr hw_ct
        rcases hw_in with hw_sa | hw_ct
        · -- `w ∈ V(P_sa)` and `w ∉ V(P_ac)`, so `w ≠ a`.
          -- Since `u ≠ v`, at least one of `u, v` is `≠ a`. Call it `u₀ ∈ V(P_ac) \ {a}`!
          have hex_u₀ : ∃ u₀ ∈ V(P_ac), u₀ ≠ a ∧ ∃ z₀ ∈ V(C), K.Adj z₀ u₀ := by
            by_cases hua : u = a
            · exact ⟨v, hv_ac, fun hva => huv_ne (hua.trans hva.symm), z₂, hz₂C, ⟨e₂, hz₂v⟩⟩
            · exact ⟨u, hu_ac, hua, z₁, hz₁C, ⟨e₁, hz₁u⟩⟩
          obtain ⟨u₀, hu₀_ac, hu₀_ne_a, z₀, hz₀C, hz₀u₀⟩ := hex_u₀
          have hu₀P : u₀ ∈ V(P) := hP_ac.vertexSet_mono hu₀_ac
          have hwa_ne : w ≠ a := fun h => hw_not_ac (h ▸ hpath_ac.left_mem)
          have hwu₀_ne : w ≠ u₀ := fun h => hw_not_ac (h ▸ hu₀_ac)
          obtain ⟨R, hRK, hRP⟩ :=
            hpath_through_C w hwP u₀ hu₀P hwu₀_ne ⟨z, hzC, hzw⟩ ⟨z₀, hz₀C, hz₀u₀⟩
          exact detour_excludes_marked_vertex hPK hP_sa hP_ac hP_ct hpath_sa hpath_ac hpath_ct
            hinter_sa hinter_ct hdisj_sact (fun Q hQK => hY_sub_Q Q hQK haY)
            hw_sa hu₀_ac hwa_ne hu₀_ne_a.symm hRK.symm (by rw [hRP, pair_comm])
        · -- `w ∈ V(P_ct)` and `w ∉ V(P_ac)`, so `w ≠ c`.
          have hex_u₀ : ∃ u₀ ∈ V(P_ac), u₀ ≠ c ∧ ∃ z₀ ∈ V(C), K.Adj z₀ u₀ := by
            by_cases huc : u = c
            · exact ⟨v, hv_ac, fun hvc => huv_ne (huc.trans hvc.symm), z₂, hz₂C, ⟨e₂, hz₂v⟩⟩
            · exact ⟨u, hu_ac, huc, z₁, hz₁C, ⟨e₁, hz₁u⟩⟩
          obtain ⟨u₀, hu₀_ac, hu₀_ne_c, z₀, hz₀C, hz₀u₀⟩ := hex_u₀
          have hu₀P : u₀ ∈ V(P) := hP_ac.vertexSet_mono hu₀_ac
          have hwc_ne : w ≠ c := fun h => hw_not_ac (h ▸ hpath_ac.right_mem)
          have hu₀w_ne : u₀ ≠ w := fun h => hw_not_ac (h ▸ hu₀_ac)
          obtain ⟨R, hRK, hRP⟩ :=
            hpath_through_C u₀ hu₀P w hwP hu₀w_ne ⟨z₀, hz₀C, hz₀u₀⟩ ⟨z, hzC, hzw⟩
          exact detour_excludes_marked_vertex hPK.symm hP_ct hP_ac hP_sa
            hpath_ct.symm hpath_ac.symm hpath_sa.symm (by rw [inter_comm, hinter_ct])
            (by rw [inter_comm, hinter_sa]) hdisj_sact.symm
            (fun Q hQK => hY_sub_Q Q hQK.symm hcY)
            hw_ct hu₀_ac hwc_ne hu₀_ne_c.symm hRK hRP
      · -- `C` has at most one neighbor in `V(P)`.
        have hex_u : ∃ u ∈ V(P), ∀ z ∈ V(C), ∀ w ∈ V(P), K.Adj z w → w = u := by
          by_cases hone : ∃ u ∈ V(P), ∃ z ∈ V(C), K.Adj z u
          · obtain ⟨u, huP, z₁, hz₁C, hz₁u⟩ := hone
            refine ⟨u, huP, fun z₂ hz₂C w hwP hzw => ?_⟩
            by_contra hwu
            exact htwo_nb ⟨u, huP, w, hwP, Ne.symm hwu, ⟨z₁, hz₁C, hz₁u⟩, ⟨z₂, hz₂C, hzw⟩⟩
          · refine ⟨s, hPK.left_mem, fun z hzC w hwP hzw => ?_⟩
            exact (hone ⟨w, hwP, z, hzC, hzw⟩).elim
        obtain ⟨u, huP, hC_nb_eq_u⟩ := hex_u
        obtain ⟨a, haY, c, hcY, hac, P_sa, P_ac, P_ct,
          hP_sa, hP_ac, hP_ct, hpath_sa, hpath_ac, hpath_ct,
          hinter_sa, hinter_ct, hdisj_sact, hV_union, hu_ac, hdisj_Y⟩ :=
          exists_minimal_Y_interval_containing_single hPK hst hsY htY huP
        refine hsep_of_C_in_ac a haY c hcY hac P_sa P_ac P_ct
          hP_sa hP_ac hP_ct hpath_sa hpath_ac hpath_ct hinter_sa hinter_ct hdisj_sact hV_union
            hdisj_Y ?_
        intro z hzC w hwP hzw
        rw [hC_nb_eq_u z hzC w hwP hzw]
        exact hu_ac

end GraphMinor.GM09
