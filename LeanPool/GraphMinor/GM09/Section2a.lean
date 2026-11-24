/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.GM09.Basic

/-!
# Graph Minors IX, Section 2 (Part 1): Lemma (2.1)

This file formalizes (2.1) and its claim (1) from Section 2 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (pages 43–44).
-/

public section

namespace GraphMinor.GM09

open Set Graph GraphMinor.Surface GraphMinor.GM06

universe u v

variable {α : Type u} {β : Type v}

/-- If `Z` catches `H` and `C` is a connected subgraph of `G` with `V(C) ∩ V(H) ≠ ∅`, then `Z`
catches `H ∪ C`. -/
private theorem catches_subgraphUnion_of_connected {G H C : Graph α β} {Z : Set α}
    (hHG : H ≤ G) (hCG : C ≤ G) (hZ : Catches Z H) (hC_conn : IsGraphConnected C)
    (hinter : (V(C) ∩ V(H)).Nonempty) :
    Catches Z (subgraphUnion G H C) := by
  refine ⟨hZ.1.trans (subset_union_left (t := V(C))), fun D hD => ?_⟩
  have hHD_or : (V(D) ∩ V(H)).Nonempty ∨ Disjoint V(D) V(H) := by
    by_cases h : (V(D) ∩ V(H)).Nonempty
    · exact Or.inl h
    · exact Or.inr (not_nonempty_iff_eq_empty.mp h |> disjoint_iff_inter_eq_empty.mpr)
  have hH_le : H ≤ subgraphUnion G H C := le_subgraphUnion_left hHG hCG
  have hC_le : C ≤ subgraphUnion G H C := le_subgraphUnion_right hHG hCG
  rcases hinter with ⟨w, hwC, hwH⟩
  obtain ⟨H₀, hH₀_comp, hwH₀⟩ := exists_graphComponent_of_mem hwH
  obtain ⟨z₀, hz₀Z, hz₀H₀⟩ := hZ.2 H₀ hH₀_comp
  obtain ⟨D', hD'_comp, hwD'⟩ := exists_graphComponent_of_mem (hH_le.vertexSet_mono hwH)
  have hC_sub_D' : C ≤ D' :=
    hD'_comp.2.2 (subgraphUnion (subgraphUnion G H C) D' C)
      (le_subgraphUnion_left hD'_comp.1 hC_le)
      (subgraphUnion_le hD'_comp.1 hC_le)
      (isGraphConnected_subgraphUnion hD'_comp.1 hC_le hD'_comp.2.1 hC_conn ⟨w, hwD', hwC⟩)
      |>.symm ▸ le_subgraphUnion_right hD'_comp.1 hC_le
  rcases hHD_or with ⟨x, hxD, hxH⟩ | hdisj
  · obtain ⟨H₁, hH₁_comp, hxH₁⟩ := exists_graphComponent_of_mem hxH
    obtain ⟨z₁, hz₁Z, hz₁H₁⟩ := hZ.2 H₁ hH₁_comp
    have hH₁_sub_D : H₁ ≤ D :=
      hD.2.2 (subgraphUnion (subgraphUnion G H C) D H₁)
        (le_subgraphUnion_left hD.1 (hH₁_comp.1.trans hH_le))
        (subgraphUnion_le hD.1 (hH₁_comp.1.trans hH_le))
        (isGraphConnected_subgraphUnion hD.1 (hH₁_comp.1.trans hH_le) hD.2.1 hH₁_comp.2.1
          ⟨x, hxD, hxH₁⟩)
        |>.symm ▸ le_subgraphUnion_right hD.1 (hH₁_comp.1.trans hH_le)
    exact ⟨z₁, hz₁Z, hH₁_sub_D.vertexSet_mono hz₁H₁⟩
  · obtain ⟨y, hyD⟩ := hD.2.1.1
    have hy_union : y ∈ V(H) ∪ V(C) := hD.1.vertexSet_mono hyD
    rcases hy_union with hyH | hyC
    · exact (disjoint_left.mp hdisj hyD hyH).elim
    · have hDD' : D = D' :=
        isGraphComponent_eq_of_mem_inter hD hD'_comp ⟨y, hyD, hC_sub_D'.vertexSet_mono hyC⟩
      subst hDD'
      have hH₀_sub_D : H₀ ≤ D :=
        hD.2.2 (subgraphUnion (subgraphUnion G H C) D H₀)
          (le_subgraphUnion_left hD.1 (hH₀_comp.1.trans hH_le))
          (subgraphUnion_le hD.1 (hH₀_comp.1.trans hH_le))
          (isGraphConnected_subgraphUnion hD.1 (hH₀_comp.1.trans hH_le) hD.2.1 hH₀_comp.2.1
            ⟨w, hwD', hwH₀⟩)
          |>.symm ▸ le_subgraphUnion_right hD.1 (hH₀_comp.1.trans hH_le)
      exact ⟨z₀, hz₀Z, hH₀_sub_D.vertexSet_mono hz₀H₀⟩

/-- **Graph Minors IX, (2.1), Claim (1)** (page 44):
"Let $X \subseteq V(K)$ be the set of all vertices of $K$ which are adjacent in $G$ to some
vertex of $H$. We observe, from the maximality of $H$, that (1) *Every path of $K$ between
$s$ and $t$ passes through every vertex of $X$." -/
theorem lemma_2_1_claim_1 {G H P : Graph α β} {Z : Set α} {s t x : α}
    (hHG : H ≤ G) (hZ : Catches Z H)
    (hmax : ∀ H' : Graph α β, H ≤ H' → H' ≤ G → Catches Z H' →
      (∃ Q : Graph α β, IsGraphPathWithEnds G Q s t ∧ Avoids Q V(H')) → H' = H)
    (hPK : IsGraphPathWithEnds (deleteVertices G V(H)) P s t)
    (hxK : x ∈ V(deleteVertices G V(H)))
    (hadj : ∃ h ∈ V(H), G.Adj x h) :
    x ∈ V(P) := by
  by_contra hxP
  rcases hadj with ⟨h, hhH, e, hexh⟩
  let E_x := G.induce {x, h}
  have hEx_le : E_x ≤ G := G.induce_le (by
    intro u hu
    rcases hu with rfl | rfl
    · exact hxK.1
    · exact hHG.vertexSet_mono hhH)
  have hEx_link : E_x.IsLink e x h := by
    rw [induce_isLink]
    exact ⟨hexh, by simp, by simp⟩
  have hEx_conn : IsGraphConnected E_x := by
    refine ⟨⟨x, by simp [E_x]⟩, fun u hu v hv => ?_⟩
    simp only [E_x] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact ⟨.nil (by simp [E_x])⟩
    · exact ⟨.cons hEx_link (.nil (by simp [E_x]))⟩
    · exact ⟨.cons hEx_link.symm (.nil (by simp [E_x]))⟩
    · exact ⟨.nil (by simp [E_x])⟩
  have hinter : (V(E_x) ∩ V(H)).Nonempty := ⟨h, by simp [E_x], hhH⟩
  have hcatch' : Catches Z (subgraphUnion G H E_x) :=
    catches_subgraphUnion_of_connected hHG hEx_le hZ hEx_conn hinter
  have hP_G : IsGraphPathWithEnds G P s t := hPK.mono (deleteVertices_le G V(H))
  have hav' : Avoids P V(subgraphUnion G H E_x) := by
    rw [Avoids, vertexSet_subgraphUnion, disjoint_union_left]
    refine ⟨?_, ?_⟩
    · rw [disjoint_left]
      intro u huH huP
      exact (hPK.1.vertexSet_mono huP).2 huH
    · rw [disjoint_left]
      intro u huEx huP
      simp only [E_x] at huEx
      rcases huEx with rfl | rfl
      · exact hxP huP
      · exact (hPK.1.vertexSet_mono huP).2 hhH
  have heq := hmax (subgraphUnion G H E_x) (le_subgraphUnion_left hHG hEx_le)
    (subgraphUnion_le hHG hEx_le) hcatch' ⟨P, hP_G, hav'⟩
  have hxH : x ∈ V(H) := by
    rw [← heq, vertexSet_subgraphUnion]
    right
    simp [E_x]
  exact hxK.2 hxH

/-- If `P` is a path in `K` from `s` to `t`, `a, c ∈ V(P)` are distinct, `P` splits into
`P_sa` (from `s` to `a`), `P_ac` (from `a` to `c`), and `P_ct` (from `c` to `t`), and `R` is a
path in `K` from `a` to `c` with `V(R) ∩ V(P) = {a, c}`, then `P_sa ∪ R ∪ P_ct` is a path in `K`
from `s` to `t` whose intersection with `V(P)` is `V(P_sa) ∪ V(P_ct)` (hence disjoint from
`V(P_ac) \ {a, c}`). -/
theorem exists_detour_path {K P P_sa P_ac P_ct R : Graph α β} {s t a c : α}
    (hPK : IsGraphPathWithEnds K P s t)
    (hP_sa_le : P_sa ≤ P) (hP_ac_le : P_ac ≤ P) (hP_ct_le : P_ct ≤ P)
    (hpath_sa : IsGraphPathWithEnds P P_sa s a)
    (hpath_ac : IsGraphPathWithEnds P P_ac a c)
    (hpath_ct : IsGraphPathWithEnds P P_ct c t)
    (hinter_sa : V(P_sa) ∩ V(P_ac) = {a})
    (hinter_ct : V(P_ac) ∩ V(P_ct) = {c})
    (hdisj_sact : Disjoint V(P_sa) V(P_ct))
    (hRK : IsGraphPathWithEnds K R a c)
    (hRP : V(R) ∩ V(P) = {a, c}) :
    ∃ Q : Graph α β,
      IsGraphPathWithEnds K Q s t ∧
      Disjoint (V(P_ac) \ {a, c}) V(Q) := by
  have hP_saK : IsGraphPathWithEnds K P_sa s a := hpath_sa.mono hPK.le
  have hP_ctK : IsGraphPathWithEnds K P_ct c t := hpath_ct.mono hPK.le
  have hV_saR : V(P_sa) ∩ V(R) = {a} := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hz₁, hzR⟩
      have hz_ac : z = a ∨ z = c := by
        have : z ∈ V(R) ∩ V(P) := ⟨hzR, hP_sa_le.vertexSet_mono hz₁⟩
        rwa [hRP, mem_insert_iff, mem_singleton_iff] at this
      rcases hz_ac with rfl | rfl
      · rfl
      · exact (disjoint_left.mp hdisj_sact hz₁ hpath_ct.left_mem).elim
    · rintro rfl
      exact ⟨hpath_sa.right_mem, hRK.left_mem⟩
  have hP_saR : IsGraphPathWithEnds K (subgraphUnion K P_sa R) s c :=
    hP_saK.subgraphUnion hRK hV_saR
  have hV_saR_ct : V(subgraphUnion K P_sa R) ∩ V(P_ct) = {c} := by
    ext z
    simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hz₁ | hzR, hz₃⟩
      · exact (disjoint_left.mp hdisj_sact hz₁ hz₃).elim
      · have hz_ac : z = a ∨ z = c := by
          have : z ∈ V(R) ∩ V(P) := ⟨hzR, hP_ct_le.vertexSet_mono hz₃⟩
          rwa [hRP, mem_insert_iff, mem_singleton_iff] at this
        rcases hz_ac with rfl | rfl
        · exact (disjoint_left.mp hdisj_sact hpath_sa.right_mem hz₃).elim
        · rfl
    · rintro rfl
      exact ⟨Or.inr hRK.right_mem, hpath_ct.left_mem⟩
  refine ⟨subgraphUnion K (subgraphUnion K P_sa R) P_ct,
    hP_saR.subgraphUnion hP_ctK hV_saR_ct, ?_⟩
  rw [disjoint_left]
  rintro z ⟨hz_ac, hz_not_ac⟩ hzQ
  simp only [vertexSet_subgraphUnion, mem_union] at hzQ
  rcases hzQ with (hz_sa | hzR) | hz_ct
  · have : z ∈ V(P_sa) ∩ V(P_ac) := ⟨hz_sa, hz_ac⟩
    rw [hinter_sa, mem_singleton_iff] at this
    exact hz_not_ac (by simp [this])
  · have : z ∈ V(R) ∩ V(P) := ⟨hzR, hP_ac_le.vertexSet_mono hz_ac⟩
    rw [hRP] at this
    exact hz_not_ac this
  · have : z ∈ V(P_ac) ∩ V(P_ct) := ⟨hz_ac, hz_ct⟩
    rw [hinter_ct, mem_singleton_iff] at this
    exact hz_not_ac (by simp [this])

/-- Given distinct `u, v ∈ V(P)` on a path `P` in `K` from `s` to `t`, `P` splits into three
subpaths `P_sa` (from `s` to `a`), `P_ac` (from `a` to `c`), and `P_ct` (from `c` to `t`) where
`{a, c} = {u, v}`. -/
theorem exists_three_way_split {K P : Graph α β} {s t u v : α}
    (hPK : IsGraphPathWithEnds K P s t)
    (huP : u ∈ V(P)) (hvP : v ∈ V(P)) (huv : u ≠ v) :
    ∃ a c : α, ({a, c} : Set α) = {u, v} ∧ a ≠ c ∧
      ∃ P_sa P_ac P_ct : Graph α β,
        P_sa ≤ P ∧ P_ac ≤ P ∧ P_ct ≤ P ∧
        IsGraphPathWithEnds P P_sa s a ∧
        IsGraphPathWithEnds P P_ac a c ∧
        IsGraphPathWithEnds P P_ct c t ∧
        V(P_sa) ∩ V(P_ac) = {a} ∧
        V(P_ac) ∩ V(P_ct) = {c} ∧
        Disjoint V(P_sa) V(P_ct) ∧
        V(P_sa) ∪ V(P_ac) ∪ V(P_ct) = V(P) ∧
        E(P_sa) ∪ E(P_ac) ∪ E(P_ct) = E(P) ∧
        Disjoint E(P_sa) E(P_ac) ∧
        Disjoint E(P_ac) E(P_ct) ∧
        Disjoint E(P_sa) E(P_ct) := by
  obtain ⟨P_su, P_ut, hP_su, hP_ut, hpath_su, hpath_ut, hunion_u, hinter_u, hdisjE_u⟩ :=
    hPK.exists_split_at huP
  have hv_u : v ∈ V(P_su) ∪ V(P_ut) := by
    rw [← vertexSet_subgraphUnion P P_su P_ut, hunion_u]; exact hvP
  rcases hv_u with hv_su | hv_ut
  · -- `v ∈ V(P_su)`: split `P_su` at `v` into `P_sv, P_vu`!
    obtain ⟨P_sv, P_vu, hP_sv, hP_vu, hpath_sv, hpath_vu, hunion_v, hinter_v, hdisjE_v⟩ :=
      hpath_su.exists_split_at hv_su
    refine ⟨v, u, by ext x; simp [or_comm], huv.symm,
      P_sv, P_vu, P_ut, hP_sv.trans hP_su, hP_vu.trans hP_su, hP_ut,
      hpath_sv.mono hP_su, hpath_vu.mono hP_su, hpath_ut, hinter_v, ?_, ?_, ?_, ?_,
      hdisjE_v, ?_, ?_⟩
    · ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      exact ⟨fun ⟨hz_vu, hz_ut⟩ => by
        have : z ∈ V(P_su) ∩ V(P_ut) := ⟨hP_vu.vertexSet_mono hz_vu, hz_ut⟩
        rwa [hinter_u, mem_singleton_iff] at this,
        fun h => h ▸ ⟨hpath_vu.right_mem, hpath_ut.left_mem⟩⟩
    · rw [disjoint_left]
      intro z hz_sv hz_ut
      have hz_u : z = u := by
        have : z ∈ V(P_su) ∩ V(P_ut) := ⟨hP_sv.vertexSet_mono hz_sv, hz_ut⟩
        rwa [hinter_u, mem_singleton_iff] at this
      subst hz_u
      have : z ∈ V(P_sv) ∩ V(P_vu) := ⟨hz_sv, hpath_vu.right_mem⟩
      rw [hinter_v, mem_singleton_iff] at this
      exact huv this
    · have hV1 : V(P_sv) ∪ V(P_vu) = V(P_su) := by
        rw [← vertexSet_subgraphUnion P_su P_sv P_vu, hunion_v]
      have hV2 : V(P_su) ∪ V(P_ut) = V(P) := by
        rw [← vertexSet_subgraphUnion P P_su P_ut, hunion_u]
      rw [hV1, hV2]
    · have hE1 : E(P_sv) ∪ E(P_vu) = E(P_su) := by
        rw [← edgeSet_subgraphUnion hP_sv hP_vu, hunion_v]
      have hE2 : E(P_su) ∪ E(P_ut) = E(P) := by
        rw [← edgeSet_subgraphUnion hP_su hP_ut, hunion_u]
      rw [hE1, hE2]
    · exact hdisjE_u.mono_left hP_vu.edgeSet_mono
    · exact hdisjE_u.mono_left hP_sv.edgeSet_mono
  · -- `v ∈ V(P_ut)`: split `P_ut` at `v` into `P_uv, P_vt`!
    obtain ⟨P_uv, P_vt, hP_uv, hP_vt, hpath_uv, hpath_vt, hunion_v, hinter_v, hdisjE_v⟩ :=
      hpath_ut.exists_split_at hv_ut
    refine ⟨u, v, rfl, huv,
      P_su, P_uv, P_vt, hP_su, hP_uv.trans hP_ut, hP_vt.trans hP_ut,
      hpath_su, hpath_uv.mono hP_ut, hpath_vt.mono hP_ut, ?_, hinter_v, ?_, ?_, ?_,
      ?_, hdisjE_v, ?_⟩
    · ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      exact ⟨fun ⟨hz_su, hz_uv⟩ => by
        have : z ∈ V(P_su) ∩ V(P_ut) := ⟨hz_su, hP_uv.vertexSet_mono hz_uv⟩
        rwa [hinter_u, mem_singleton_iff] at this,
        fun h => h ▸ ⟨hpath_su.right_mem, hpath_uv.left_mem⟩⟩
    · rw [disjoint_left]
      intro z hz_su hz_vt
      have hz_u : z = u := by
        have : z ∈ V(P_su) ∩ V(P_ut) := ⟨hz_su, hP_vt.vertexSet_mono hz_vt⟩
        rwa [hinter_u, mem_singleton_iff] at this
      subst hz_u
      have : z ∈ V(P_uv) ∩ V(P_vt) := ⟨hpath_uv.left_mem, hz_vt⟩
      rw [hinter_v, mem_singleton_iff] at this
      exact huv this
    · have hV1 : V(P_uv) ∪ V(P_vt) = V(P_ut) := by
        rw [← vertexSet_subgraphUnion P_ut P_uv P_vt, hunion_v]
      have hV2 : V(P_su) ∪ V(P_ut) = V(P) := by
        rw [← vertexSet_subgraphUnion P P_su P_ut, hunion_u]
      rw [union_assoc, hV1, hV2]
    · have hE1 : E(P_uv) ∪ E(P_vt) = E(P_ut) := by
        rw [← edgeSet_subgraphUnion hP_uv hP_vt, hunion_v]
      have hE2 : E(P_su) ∪ E(P_ut) = E(P) := by
        rw [← edgeSet_subgraphUnion hP_su hP_ut, hunion_u]
      rw [union_assoc, hE1, hE2]
    · exact hdisjE_u.mono_right hP_uv.edgeSet_mono
    · exact hdisjE_u.mono_right hP_vt.edgeSet_mono

/-- Given a subset `V₂ ⊆ V(K)` and `a, c ∈ V₂` with `a ≠ c`, such that:
- `s, t ∈ V(K) \ (V₂ \ {a, c})`,
- `V₂ ≠ {a, c}`,
- no vertex of `V₂ \ {a, c}` is adjacent in `G` to any vertex outside `V₂`,
- `G₂ = K.induce V₂` and `G₁ = (G.induce (V(G) \ (V₂ \ {a, c}))).restrict (E(G) \ E(G₂))`,
- `E(P) ∩ E(G₂) ≠ ∅` and `{a, c} ⊆ V(P)` with any edge of `G₁ ∩ G₂` empty,
then `(G₁, G₂)` is a separation of `G` satisfying all conclusions of `(2.1)`. -/
theorem exists_separation_of_isolated_subset {G H P : Graph α β} {s t a c : α}
    (hHG : H ≤ G)
    (hPK : IsGraphPathWithEnds (deleteVertices G V(H)) P s t)
    (hac : a ≠ c) (haP : a ∈ V(P)) (hcP : c ∈ V(P))
    (V₂ : Set α) (hV₂_sub : V₂ ⊆ V(deleteVertices G V(H)))
    (haV₂ : a ∈ V₂) (hcV₂ : c ∈ V₂)
    (hs_not : s ∉ V₂ \ {a, c}) (ht_not : t ∉ V₂ \ {a, c})
    (hV₂_ne : V₂ ≠ {a, c})
    (hno_out : ∀ x ∈ V₂ \ {a, c}, ∀ y : α, G.Adj x y → y ∈ V₂)
    (hEP_inter : (E(P) ∩ E((deleteVertices G V(H)).induce V₂)).Nonempty) :
    ∃ G₁ G₂ : Graph α β,
      IsGraphSeparation G G₁ G₂ ∧
      {s, t} ⊆ V(G₁) ∧
      (V(G₁) ∩ V(G₂)).ncard = 2 ∧
      (E(P) ∩ E(G₂)).Nonempty ∧
      subgraphInter G G₁ G₂ ≤ P ∧
      H ≤ G₁ ∧
      V(G₁) ≠ V(G) := by
  let K := deleteVertices G V(H)
  have hKG : K ≤ G := deleteVertices_le G V(H)
  have hPG : P ≤ G := hPK.1.trans hKG
  let G₂ : Graph α β := K.induce V₂
  have hG₂K : G₂ ≤ K := K.induce_le hV₂_sub
  have hG₂G : G₂ ≤ G := hG₂K.trans hKG
  have hVG₂ : V(G₂) = V₂ := rfl
  let G₁ : Graph α β := (G.induce (V(G) \ (V₂ \ {a, c}))).restrict (E(G) \ E(G₂))
  have hG₁G : G₁ ≤ G := restrict_le.trans (G.induce_le sdiff_subset)
  have hVG₁ : V(G₁) = V(G) \ (V₂ \ {a, c}) := rfl
  have hEG₁ : E(G₁) = E(G) \ E(G₂) := by
    change E(G.induce (V(G) \ (V₂ \ {a, c}))) ∩ (E(G) \ E(G₂)) = E(G) \ E(G₂)
    rw [inter_eq_right]
    rintro e ⟨heG, he_not_G₂⟩
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet heG
    refine ⟨x, y, hxy, ⟨hxy.left_mem, ?_⟩, ⟨hxy.right_mem, ?_⟩⟩
    · intro hx_in
      have hyV₂ : y ∈ V₂ := hno_out x hx_in y hxy.adj
      have hxV₂ : x ∈ V₂ := hx_in.1
      have hxyK : K.IsLink e x y := by
        rw [deleteVertices_isLink]
        exact ⟨hxy, (hV₂_sub hxV₂).2, (hV₂_sub hyV₂).2⟩
      have hxyG₂ : G₂.IsLink e x y := by
        rw [induce_isLink]
        exact ⟨hxyK, hxV₂, hyV₂⟩
      exact he_not_G₂ hxyG₂.edge_mem
    · intro hy_in
      have hxV₂ : x ∈ V₂ := hno_out y hy_in x hxy.symm.adj
      have hyV₂ : y ∈ V₂ := hy_in.1
      have hxyK : K.IsLink e x y := by
        rw [deleteVertices_isLink]
        exact ⟨hxy, (hV₂_sub hxV₂).2, (hV₂_sub hyV₂).2⟩
      have hxyG₂ : G₂.IsLink e x y := by
        rw [induce_isLink]
        exact ⟨hxyK, hxV₂, hyV₂⟩
      exact he_not_G₂ hxyG₂.edge_mem
  have hV_inter : V(G₁) ∩ V(G₂) = {a, c} := by
    rw [hVG₁, hVG₂]
    ext z
    simp only [mem_inter_iff, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨_, hz_not⟩, hzV₂⟩
      by_contra hne
      exact hz_not ⟨hzV₂, hne⟩
    · rintro (rfl | rfl)
      · exact ⟨⟨(hV₂_sub haV₂).1, fun h => h.2 (Or.inl rfl)⟩, haV₂⟩
      · exact ⟨⟨(hV₂_sub hcV₂).1, fun h => h.2 (Or.inr rfl)⟩, hcV₂⟩
  refine ⟨G₁, G₂, ?_, ?_, ?_, hEP_inter, ?_, ?_, ?_⟩
  · -- `IsGraphSeparation G G₁ G₂`
    refine ⟨hG₁G, hG₂G, ?_, ?_, hEG₁ ▸ disjoint_sdiff_self_left⟩
    · rw [hVG₁, hVG₂]
      ext z
      simp only [mem_union, mem_sdiff]
      exact ⟨fun h => h.elim (fun h1 => h1.1) (fun h2 => (hV₂_sub h2).1),
        fun hzG => by_cases (fun hzV₂ : z ∈ V₂ => Or.inr hzV₂)
          (fun hzV₂ => Or.inl ⟨hzG, fun h => hzV₂ h.1⟩)⟩
    · rw [hEG₁]
      exact sdiff_union_of_subset hG₂G.edgeSet_mono
  · -- `{s, t} ⊆ V(G₁)`
    intro z hz
    rw [hVG₁]
    rcases hz with rfl | rfl
    · exact ⟨(hPK.1.vertexSet_mono hPK.left_mem).1, hs_not⟩
    · exact ⟨(hPK.1.vertexSet_mono hPK.right_mem).1, ht_not⟩
  · -- `(V(G₁) ∩ V(G₂)).ncard = 2`
    rw [hV_inter]
    exact Set.ncard_pair hac
  · -- `subgraphInter G G₁ G₂ ≤ P`
    rw [(Compatible.of_le_le (subgraphInter_le hG₁G) hPG).le_iff]
    rw [vertexSet_subgraphInter, hV_inter, edgeSet_subgraphInter hG₁G hG₂G, hEG₁,
      sdiff_inter_self]
    refine ⟨?_, empty_subset _⟩
    intro z hz
    rcases hz with rfl | rfl
    · exact haP
    · exact hcP
  · -- `H ≤ G₁`
    rw [(Compatible.of_le_le hHG hG₁G).le_iff, hVG₁, hEG₁]
    refine ⟨fun z hzH => ⟨hHG.vertexSet_mono hzH, fun hzV₂ => (hV₂_sub hzV₂.1).2 hzH⟩,
      fun e heH => ⟨hHG.edgeSet_mono heH, fun heG₂ => ?_⟩⟩
    obtain ⟨x, y, hxyH⟩ := H.exists_isLink_of_mem_edgeSet heH
    obtain ⟨x', y', hxyG₂⟩ := G₂.exists_isLink_of_mem_edgeSet heG₂
    have heq := (hxyH.mono hHG).left_eq_or_eq (hxyG₂.mono hG₂G)
    rcases heq with rfl | rfl
    · exact (hG₂K.vertexSet_mono hxyG₂.left_mem).2 hxyH.left_mem
    · exact (hG₂K.vertexSet_mono hxyG₂.right_mem).2 hxyH.left_mem
  · -- `V(G₁) ≠ V(G)`
    intro heq
    have hssub : {a, c} ⊂ V₂ :=
      ⟨fun z hz => by rcases hz with rfl | rfl <;> assumption,
        fun h => hV₂_ne (Subset.antisymm h (fun z hz => by rcases hz with rfl | rfl
          <;> assumption))⟩
    obtain ⟨w, hwV₂, hw_not_ac⟩ := exists_of_ssubset hssub
    have hwG : w ∈ V(G) := (hV₂_sub hwV₂).1
    rw [← heq, hVG₁] at hwG
    exact hwG.2 ⟨hwV₂, hw_not_ac⟩

/-- If `K = deleteVertices G V(H)` and `P` is a path in `K` from `s` to `t`, and `R` is a path in
`K` between distinct `u, v ∈ V(P)` with `V(R) ∩ V(P) = {u, v}`, then no internal vertex of the
subpath of `P` between `u` and `v` is adjacent in `G` to `V(H)` (by `lemma_2_1_claim_1` applied
to the detour path `Q`). -/
theorem no_X_in_open_interval_of_detour {G H P P_sa P_ac P_ct R : Graph α β}
    {Z : Set α} {s t a c : α}
    (hHG : H ≤ G) (hZ : Catches Z H)
    (hmax : ∀ H' : Graph α β, H ≤ H' → H' ≤ G → Catches Z H' →
      (∃ Q : Graph α β, IsGraphPathWithEnds G Q s t ∧ Avoids Q V(H')) → H' = H)
    (hPK : IsGraphPathWithEnds (deleteVertices G V(H)) P s t)
    (hP_sa_le : P_sa ≤ P) (hP_ac_le : P_ac ≤ P) (hP_ct_le : P_ct ≤ P)
    (hpath_sa : IsGraphPathWithEnds P P_sa s a)
    (hpath_ac : IsGraphPathWithEnds P P_ac a c)
    (hpath_ct : IsGraphPathWithEnds P P_ct c t)
    (hinter_sa : V(P_sa) ∩ V(P_ac) = {a})
    (hinter_ct : V(P_ac) ∩ V(P_ct) = {c})
    (hdisj_sact : Disjoint V(P_sa) V(P_ct))
    (hRK : IsGraphPathWithEnds (deleteVertices G V(H)) R a c)
    (hRP : V(R) ∩ V(P) = {a, c})
    {x : α} (hx : x ∈ V(P_ac) \ {a, c}) :
    ¬ ∃ h ∈ V(H), G.Adj x h := by
  intro hadj
  obtain ⟨Q, hQK, hdisjQ⟩ := exists_detour_path hPK hP_sa_le hP_ac_le hP_ct_le
    hpath_sa hpath_ac hpath_ct hinter_sa hinter_ct hdisj_sact hRK hRP
  have hxK : x ∈ V(deleteVertices G V(H)) :=
    hPK.1.vertexSet_mono (hP_ac_le.vertexSet_mono hx.1)
  have hxQ : x ∈ V(Q) := lemma_2_1_claim_1 hHG hZ hmax hQK hxK hadj
  exact disjoint_left.mp hdisjQ hx hxQ

/-- Every path `P_ac` between distinct vertices `a ≠ c` has at least one edge. -/
theorem nonempty_edgeSet_of_isGraphPathWithEnds_ne {G P : Graph α β} {a c : α}
    (hP : IsGraphPathWithEnds G P a c) (hac : a ≠ c) : E(P).Nonempty := by
  rcases hP with ⟨_, W, _, _, hE⟩
  rw [hE]
  cases W with
  | nil _ => exact (hac rfl).elim
  | cons h _ => exact ⟨_, List.mem_cons_self⟩

private theorem trim_path_from_left {Q : Graph α β} {s t : α} {Y : Set α} :
  ∀ (n : ℕ) (a₀ : α) (P_sa₀ P_a₀u : Graph α β),
    a₀ ∈ Y → P_sa₀ ≤ Q → P_a₀u ≤ Q →
    IsGraphPathWithEnds Q P_sa₀ s a₀ →
    IsGraphPathWithEnds Q P_a₀u a₀ t →
    V(P_sa₀) ∩ V(P_a₀u) = {a₀} →
    V(P_sa₀) ∪ V(P_a₀u) = V(Q) →
    V(P_a₀u).ncard = n →
    ∃ a ∈ Y, ∃ P_sa P_au : Graph α β,
      P_sa ≤ Q ∧ P_au ≤ Q ∧
      IsGraphPathWithEnds Q P_sa s a ∧
      IsGraphPathWithEnds Q P_au a t ∧
      V(P_sa) ∩ V(P_au) = {a} ∧
      V(P_sa) ∪ V(P_au) = V(Q) ∧
      Disjoint (V(P_au) \ {a}) Y := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro a₀ P_sa₀ P_a₀u ha₀Y hP_sa₀ hP_a₀u hpath_sa₀ hpath_a₀u hinter_a₀ hunion_a₀ hcard
    by_cases hhit : ∃ y ∈ V(P_a₀u) \ {a₀}, y ∈ Y
    · rcases hhit with ⟨y, ⟨hy_in, hy_ne⟩, hyY⟩
      simp only [mem_singleton_iff] at hy_ne
      obtain ⟨P_a₀y, P_yu, hP_a₀y, hP_yu, hpath_a₀y, hpath_yu, hunion_y, hinter_y, _⟩ :=
        hpath_a₀u.exists_split_at hy_in
      have ha₀_not_yu : a₀ ∉ V(P_yu) := by
        intro ha₀_yu
        have : a₀ ∈ V(P_a₀y) ∩ V(P_yu) := ⟨hpath_a₀y.left_mem, ha₀_yu⟩
        rw [hinter_y, mem_singleton_iff] at this
        exact hy_ne this.symm
      have hlt : V(P_yu).ncard < n := by
        rw [← hcard]
        exact Set.ncard_lt_ncard
          ⟨hP_yu.vertexSet_mono, fun hsub => ha₀_not_yu (hsub hpath_a₀u.left_mem)⟩
          hpath_a₀u.vertexSet_finite
      have hV_sa₀_a₀y : V(P_sa₀) ∩ V(P_a₀y) = {a₀} := by
        ext z
        simp only [mem_inter_iff, mem_singleton_iff]
        exact ⟨fun ⟨hz₁, hz₂⟩ => by
          have : z ∈ V(P_sa₀) ∩ V(P_a₀u) := ⟨hz₁, hP_a₀y.vertexSet_mono hz₂⟩
          rwa [hinter_a₀, mem_singleton_iff] at this,
          fun h => h ▸ ⟨hpath_sa₀.right_mem, hpath_a₀y.left_mem⟩⟩
      have hpath_sy : IsGraphPathWithEnds Q (subgraphUnion Q P_sa₀ P_a₀y) s y :=
        hpath_sa₀.subgraphUnion (hpath_a₀y.mono hP_a₀u) hV_sa₀_a₀y
      have hinter_sy : V(subgraphUnion Q P_sa₀ P_a₀y) ∩ V(P_yu) = {y} := by
        ext z
        simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
        constructor
        · rintro ⟨hz₁ | hz₂, hz₃⟩
          · have hz_a₀ : z = a₀ := by
              have : z ∈ V(P_sa₀) ∩ V(P_a₀u) := ⟨hz₁, hP_yu.vertexSet_mono hz₃⟩
              rwa [hinter_a₀, mem_singleton_iff] at this
            subst hz_a₀
            exact (ha₀_not_yu hz₃).elim
          · have : z ∈ V(P_a₀y) ∩ V(P_yu) := ⟨hz₂, hz₃⟩
            rwa [hinter_y, mem_singleton_iff] at this
        · rintro rfl
          exact ⟨Or.inr hpath_a₀y.right_mem, hpath_yu.left_mem⟩
      have hunion_sy : V(subgraphUnion Q P_sa₀ P_a₀y) ∪ V(P_yu) = V(Q) := by
        rw [vertexSet_subgraphUnion, union_assoc,
          ← vertexSet_subgraphUnion P_a₀u P_a₀y P_yu, hunion_y, hunion_a₀]
      exact ih V(P_yu).ncard hlt y (subgraphUnion Q P_sa₀ P_a₀y) P_yu hyY
        (subgraphUnion_le hP_sa₀ (hP_a₀y.trans hP_a₀u)) (hP_yu.trans hP_a₀u)
        hpath_sy (hpath_yu.mono hP_a₀u) hinter_sy hunion_sy rfl
    · refine ⟨a₀, ha₀Y, P_sa₀, P_a₀u, hP_sa₀, hP_a₀u, hpath_sa₀, hpath_a₀u, hinter_a₀,
        hunion_a₀, ?_⟩
      rw [disjoint_left]
      exact fun y hy hyY => hhit ⟨y, hy, hyY⟩

/-- If `P` is a path in `K` from `s` to `t`, `Y ⊆ V(P)` with `s, t ∈ Y`, and `u, v ∈ V(P)` are
distinct vertices such that for every three-way split `P = P_su ∪ P_uv ∪ P_vt` between `{u, v}`,
`Disjoint (V(P_uv) \ {u, v}) Y`, then there exist `a, c ∈ Y` with `a ≠ c` and a three-way split
`P = P_sa ∪ P_ac ∪ P_ct` such that `u, v ∈ V(P_ac)` and `Disjoint (V(P_ac) \ {a, c}) Y`. -/
theorem exists_minimal_Y_interval_containing_pair {K P : Graph α β} {s t u v : α} {Y : Set α}
    (hPK : IsGraphPathWithEnds K P s t)
    (hsY : s ∈ Y) (htY : t ∈ Y)
    (huP : u ∈ V(P)) (hvP : v ∈ V(P)) (huv : u ≠ v)
    (hno_Y_between : ∀ u' v' : α, ({u', v'} : Set α) = {u, v} →
      ∀ P_su P_uv P_vt : Graph α β,
      P_su ≤ P → P_uv ≤ P → P_vt ≤ P →
      IsGraphPathWithEnds P P_su s u' →
      IsGraphPathWithEnds P P_uv u' v' →
      IsGraphPathWithEnds P P_vt v' t →
      V(P_su) ∩ V(P_uv) = {u'} →
      V(P_uv) ∩ V(P_vt) = {v'} →
      Disjoint V(P_su) V(P_vt) →
      Disjoint (V(P_uv) \ {u', v'}) Y) :
    ∃ a ∈ Y, ∃ c ∈ Y, a ≠ c ∧
      ∃ P_sa P_ac P_ct : Graph α β,
        P_sa ≤ P ∧ P_ac ≤ P ∧ P_ct ≤ P ∧
        IsGraphPathWithEnds P P_sa s a ∧
        IsGraphPathWithEnds P P_ac a c ∧
        IsGraphPathWithEnds P P_ct c t ∧
        V(P_sa) ∩ V(P_ac) = {a} ∧
        V(P_ac) ∩ V(P_ct) = {c} ∧
        Disjoint V(P_sa) V(P_ct) ∧
        V(P_sa) ∪ V(P_ac) ∪ V(P_ct) = V(P) ∧
        u ∈ V(P_ac) ∧ v ∈ V(P_ac) ∧
        Disjoint (V(P_ac) \ {a, c}) Y := by
  classical
  -- First obtain the three-way split of `P` at `u` and `v`:
  obtain ⟨u', v', huv_eq, huv'_ne, P_su, P_uv, P_vt,
    hP_su, hP_uv, hP_vt, hpath_su, hpath_uv, hpath_vt,
    hinter_su, hinter_vt, hdisj_suvt, hV_union_suvt, _, _, _, _⟩ :=
    exists_three_way_split hPK huP hvP huv
  have hdisj_uv_Y : Disjoint (V(P_uv) \ {u', v'}) Y :=
    hno_Y_between u' v' huv_eq P_su P_uv P_vt hP_su hP_uv hP_vt
      hpath_su hpath_uv hpath_vt hinter_su hinter_vt hdisj_suvt
  obtain ⟨P_ss, P_su', hP_ss, hP_su', hpath_ss, hpath_su', hunion_ss, hinter_ss, _⟩ :=
    hpath_su.exists_split_at hpath_su.left_mem
  have hV_ss : V(P_ss) ∪ V(P_su') = V(P_su) := by
    rw [← vertexSet_subgraphUnion P_su P_ss P_su', hunion_ss]
  obtain ⟨a, haY, P_sa, P_au, hP_sa, hP_au, hpath_sa, hpath_au, hinter_au, hunion_au, hdisj_au⟩ :=
    trim_path_from_left V(P_su').ncard s P_ss P_su' hsY hP_ss hP_su'
      hpath_ss hpath_su' hinter_ss hV_ss rfl
  obtain ⟨P_vt', P_tt, hP_vt', hP_tt, hpath_vt', hpath_tt, hunion_tt, hinter_tt, _⟩ :=
    hpath_vt.exists_split_at hpath_vt.right_mem
  have hV_tt : V(P_vt') ∪ V(P_tt) = V(P_vt) := by
    rw [← vertexSet_subgraphUnion P_vt P_vt' P_tt, hunion_tt]
  obtain ⟨c, hcY, P_ct, P_vc, hP_ct, hP_vc, hpath_tc, hpath_cv, hinter_cv, hunion_cv, hdisj_vc⟩ :=
    trim_path_from_left V(P_vt').ncard t P_tt P_vt' htY hP_tt hP_vt'
      hpath_tt.symm hpath_vt'.symm (inter_comm _ _ ▸ hinter_tt)
      (union_comm _ _ ▸ hV_tt) rfl
  have hpath_vc := hpath_cv.symm
  have hpath_ct := hpath_tc.symm
  have hinter_vc : V(P_vc) ∩ V(P_ct) = {c} := inter_comm _ _ ▸ hinter_cv
  have hunion_vc : V(P_vc) ∪ V(P_ct) = V(P_vt) := union_comm _ _ ▸ hunion_cv
  -- Now combine `P_ac := P_au ∪ P_uv ∪ P_vc`!
  have hP_auP : P_au ≤ P := hP_au.trans hP_su
  have hP_vcP : P_vc ≤ P := hP_vc.trans hP_vt
  have hV_au_uv : V(P_au) ∩ V(P_uv) = {u'} := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    exact ⟨fun ⟨hz₁, hz₂⟩ => by
      have : z ∈ V(P_su) ∩ V(P_uv) := ⟨hP_au.vertexSet_mono hz₁, hz₂⟩
      rwa [hinter_su, mem_singleton_iff] at this,
      fun h => h ▸ ⟨hpath_au.right_mem, hpath_uv.left_mem⟩⟩
  have hpath_av : IsGraphPathWithEnds P (subgraphUnion P P_au P_uv) a v' :=
    (hpath_au.mono hP_su).subgraphUnion hpath_uv hV_au_uv
  have hV_av_vc : V(subgraphUnion P P_au P_uv) ∩ V(P_vc) = {v'} := by
    ext z
    simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hz₁ | hz₂, hz₃⟩
      · exact (disjoint_left.mp hdisj_suvt (hP_au.vertexSet_mono hz₁)
        (hP_vc.vertexSet_mono hz₃)).elim
      · have : z ∈ V(P_uv) ∩ V(P_vt) := ⟨hz₂, hP_vc.vertexSet_mono hz₃⟩
        rwa [hinter_vt, mem_singleton_iff] at this
    · rintro rfl
      exact ⟨Or.inr hpath_uv.right_mem, hpath_vc.left_mem⟩
  let P_ac := subgraphUnion P (subgraphUnion P P_au P_uv) P_vc
  have hP_acP : P_ac ≤ P := subgraphUnion_le (subgraphUnion_le hP_auP hP_uv) hP_vcP
  have hpath_ac : IsGraphPathWithEnds P P_ac a c :=
    hpath_av.subgraphUnion (hpath_vc.mono hP_vt) hV_av_vc
  have hac_ne : a ≠ c := by
    intro hac_eq
    have ha_su : a ∈ V(P_su) := hP_au.vertexSet_mono hpath_au.left_mem
    have hc_vt : c ∈ V(P_vt) := hP_vc.vertexSet_mono hpath_vc.right_mem
    exact disjoint_left.mp hdisj_suvt ha_su (hac_eq ▸ hc_vt)
  refine ⟨a, haY, c, hcY, hac_ne, P_sa, P_ac, P_ct,
    hP_sa.trans hP_su, hP_acP, hP_ct.trans hP_vt,
    hpath_sa.mono hP_su, hpath_ac, hpath_ct.mono hP_vt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `V(P_sa) ∩ V(P_ac) = {a}`
    ext z
    simp only [P_ac, vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hz_sa, (hz_au | hz_uv) | hz_vc⟩
      · have : z ∈ V(P_sa) ∩ V(P_au) := ⟨hz_sa, hz_au⟩
        rwa [hinter_au, mem_singleton_iff] at this
      · have hz_u' : z = u' := by
          have : z ∈ V(P_su) ∩ V(P_uv) := ⟨hP_sa.vertexSet_mono hz_sa, hz_uv⟩
          rwa [hinter_su, mem_singleton_iff] at this
        subst hz_u'
        have : z ∈ V(P_sa) ∩ V(P_au) := ⟨hz_sa, hpath_au.right_mem⟩
        rwa [hinter_au, mem_singleton_iff] at this
      · exact (disjoint_left.mp hdisj_suvt (hP_sa.vertexSet_mono hz_sa)
        (hP_vc.vertexSet_mono hz_vc)).elim
    · rintro rfl
      exact ⟨hpath_sa.right_mem, Or.inl (Or.inl hpath_au.left_mem)⟩
  · -- `V(P_ac) ∩ V(P_ct) = {c}`
    ext z
    simp only [P_ac, vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨(hz_au | hz_uv) | hz_vc, hz_ct⟩
      · exact (disjoint_left.mp hdisj_suvt (hP_au.vertexSet_mono hz_au)
        (hP_ct.vertexSet_mono hz_ct)).elim
      · have hz_v' : z = v' := by
          have : z ∈ V(P_uv) ∩ V(P_vt) := ⟨hz_uv, hP_ct.vertexSet_mono hz_ct⟩
          rwa [hinter_vt, mem_singleton_iff] at this
        subst hz_v'
        have : z ∈ V(P_vc) ∩ V(P_ct) := ⟨hpath_vc.left_mem, hz_ct⟩
        rwa [hinter_vc, mem_singleton_iff] at this
      · have : z ∈ V(P_vc) ∩ V(P_ct) := ⟨hz_vc, hz_ct⟩
        rwa [hinter_vc, mem_singleton_iff] at this
    · rintro rfl
      exact ⟨Or.inr hpath_vc.right_mem, hpath_ct.left_mem⟩
  · -- `Disjoint V(P_sa) V(P_ct)`
    exact hdisj_suvt.mono hP_sa.vertexSet_mono hP_ct.vertexSet_mono
  · -- `V(P_sa) ∪ V(P_ac) ∪ V(P_ct) = V(P)`
    change V(P_sa) ∪ (V(P_au) ∪ V(P_uv) ∪ V(P_vc)) ∪ V(P_ct) = V(P)
    have : V(P_sa) ∪ (V(P_au) ∪ V(P_uv) ∪ V(P_vc)) ∪ V(P_ct) =
        (V(P_sa) ∪ V(P_au)) ∪ V(P_uv) ∪ (V(P_vc) ∪ V(P_ct)) := by
      ext z; simp [or_assoc]
    rw [this, hunion_au, hunion_vc, hV_union_suvt]
  · -- `u ∈ V(P_ac)`
    have hu_in : u ∈ ({u', v'} : Set α) := by rw [huv_eq]; simp
    simp only [P_ac, vertexSet_subgraphUnion, mem_union]
    rcases hu_in with rfl | rfl
    · exact Or.inl (Or.inr hpath_uv.left_mem)
    · exact Or.inl (Or.inr hpath_uv.right_mem)
  · -- `v ∈ V(P_ac)`
    have hv_in : v ∈ ({u', v'} : Set α) := by rw [huv_eq]; simp
    simp only [P_ac, vertexSet_subgraphUnion, mem_union]
    rcases hv_in with rfl | rfl
    · exact Or.inl (Or.inr hpath_uv.left_mem)
    · exact Or.inl (Or.inr hpath_uv.right_mem)
  · -- `Disjoint (V(P_ac) \ {a, c}) Y`
    rw [disjoint_left]
    rintro z ⟨hz_ac, hz_not_ac⟩ hzY
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz_not_ac
    simp only [P_ac, vertexSet_subgraphUnion, mem_union] at hz_ac
    rcases hz_ac with (hz_au | hz_uv) | hz_vc
    · exact disjoint_left.mp hdisj_au ⟨hz_au, hz_not_ac.1⟩ hzY
    · by_cases hzu : z = u'
      · subst hzu
        exact disjoint_left.mp hdisj_au ⟨hpath_au.right_mem, hz_not_ac.1⟩ hzY
      · by_cases hzv : z = v'
        · subst hzv
          exact disjoint_left.mp hdisj_vc ⟨hpath_vc.left_mem, hz_not_ac.2⟩ hzY
        · exact disjoint_left.mp hdisj_uv_Y ⟨hz_uv, by simp [hzu, hzv]⟩ hzY
    · exact disjoint_left.mp hdisj_vc ⟨hz_vc, hz_not_ac.2⟩ hzY

private theorem trim_path_around_vertex {P : Graph α β} {s t u : α} {Y : Set α} :
  ∀ (n : ℕ) (a₀ c₀ : α) (P_sa₀ P_ac₀ P_c₀t : Graph α β),
    a₀ ∈ Y → c₀ ∈ Y → a₀ ≠ c₀ →
    P_sa₀ ≤ P → P_ac₀ ≤ P → P_c₀t ≤ P →
    IsGraphPathWithEnds P P_sa₀ s a₀ →
    IsGraphPathWithEnds P P_ac₀ a₀ c₀ →
    IsGraphPathWithEnds P P_c₀t c₀ t →
    V(P_sa₀) ∩ V(P_ac₀) = {a₀} →
    V(P_ac₀) ∩ V(P_c₀t) = {c₀} →
    Disjoint V(P_sa₀) V(P_c₀t) →
    V(P_sa₀) ∪ V(P_ac₀) ∪ V(P_c₀t) = V(P) →
    u ∈ V(P_ac₀) →
    V(P_ac₀).ncard = n →
    ∃ a ∈ Y, ∃ c ∈ Y, a ≠ c ∧
      ∃ P_sa P_ac P_ct : Graph α β,
        P_sa ≤ P ∧ P_ac ≤ P ∧ P_ct ≤ P ∧
        IsGraphPathWithEnds P P_sa s a ∧
        IsGraphPathWithEnds P P_ac a c ∧
        IsGraphPathWithEnds P P_ct c t ∧
        V(P_sa) ∩ V(P_ac) = {a} ∧
        V(P_ac) ∩ V(P_ct) = {c} ∧
        Disjoint V(P_sa) V(P_ct) ∧
        V(P_sa) ∪ V(P_ac) ∪ V(P_ct) = V(P) ∧
        u ∈ V(P_ac) ∧
        Disjoint (V(P_ac) \ {a, c}) Y := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro a₀ c₀ P_sa₀ P_ac₀ P_c₀t ha₀Y hc₀Y ha₀c₀ hP_sa₀ hP_ac₀ hP_c₀t
      hpath_sa₀ hpath_ac₀ hpath_c₀t hinter_sa₀ hinter_c₀t hdisj_sa₀c₀t hunion_sa₀c₀t hu_ac₀ hcard
    by_cases hhit : ∃ y ∈ V(P_ac₀) \ {a₀, c₀}, y ∈ Y
    · rcases hhit with ⟨y, ⟨hy_in, hy_ne⟩, hyY⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at hy_ne
      obtain ⟨P_a₀y, P_yc₀, hP_a₀y, hP_yc₀, hpath_a₀y, hpath_yc₀, hunion_y, hinter_y, _⟩ :=
        hpath_ac₀.exists_split_at hy_in
      have hV_y : V(P_a₀y) ∪ V(P_yc₀) = V(P_ac₀) := by
        rw [← vertexSet_subgraphUnion P_ac₀ P_a₀y P_yc₀, hunion_y]
      have ha₀_not_yc₀ : a₀ ∉ V(P_yc₀) := by
        intro h
        have : a₀ ∈ V(P_a₀y) ∩ V(P_yc₀) := ⟨hpath_a₀y.left_mem, h⟩
        rw [hinter_y, mem_singleton_iff] at this
        exact hy_ne.1 this.symm
      have hc₀_not_a₀y : c₀ ∉ V(P_a₀y) := by
        intro h
        have : c₀ ∈ V(P_a₀y) ∩ V(P_yc₀) := ⟨h, hpath_yc₀.right_mem⟩
        rw [hinter_y, mem_singleton_iff] at this
        exact hy_ne.2 this.symm
      have hu_split : u ∈ V(P_a₀y) ∪ V(P_yc₀) := by
        rw [hV_y]; exact hu_ac₀
      rcases hu_split with hu_a₀y | hu_yc₀
      · -- `u ∈ V(P_a₀y)`: replace `c₀` by `y`!
        have hlt : V(P_a₀y).ncard < n := by
          rw [← hcard]
          exact Set.ncard_lt_ncard
            ⟨hP_a₀y.vertexSet_mono, fun hsub => hc₀_not_a₀y (hsub hpath_ac₀.right_mem)⟩
            hpath_ac₀.vertexSet_finite
        have hV_yc₀_c₀t : V(P_yc₀) ∩ V(P_c₀t) = {c₀} := by
          ext z
          simp only [mem_inter_iff, mem_singleton_iff]
          exact ⟨fun ⟨hz₁, hz₂⟩ => by
            have : z ∈ V(P_ac₀) ∩ V(P_c₀t) := ⟨hP_yc₀.vertexSet_mono hz₁, hz₂⟩
            rwa [hinter_c₀t, mem_singleton_iff] at this,
            fun h => h ▸ ⟨hpath_yc₀.right_mem, hpath_c₀t.left_mem⟩⟩
        have hpath_yt : IsGraphPathWithEnds P (subgraphUnion P P_yc₀ P_c₀t) y t :=
          (hpath_yc₀.mono hP_ac₀).subgraphUnion hpath_c₀t hV_yc₀_c₀t
        have hinter_sa₀_a₀y : V(P_sa₀) ∩ V(P_a₀y) = {a₀} := by
          ext z
          simp only [mem_inter_iff, mem_singleton_iff]
          exact ⟨fun ⟨hz₁, hz₂⟩ => by
            have : z ∈ V(P_sa₀) ∩ V(P_ac₀) := ⟨hz₁, hP_a₀y.vertexSet_mono hz₂⟩
            rwa [hinter_sa₀, mem_singleton_iff] at this,
            fun h => h ▸ ⟨hpath_sa₀.right_mem, hpath_a₀y.left_mem⟩⟩
        have hinter_a₀y_yt : V(P_a₀y) ∩ V(subgraphUnion P P_yc₀ P_c₀t) = {y} := by
          ext z
          simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
          constructor
          · rintro ⟨hz₁, hz₂ | hz₃⟩
            · have : z ∈ V(P_a₀y) ∩ V(P_yc₀) := ⟨hz₁, hz₂⟩
              rwa [hinter_y, mem_singleton_iff] at this
            · have hz_c₀ : z = c₀ := by
                have : z ∈ V(P_ac₀) ∩ V(P_c₀t) := ⟨hP_a₀y.vertexSet_mono hz₁, hz₃⟩
                rwa [hinter_c₀t, mem_singleton_iff] at this
              subst hz_c₀
              exact (hc₀_not_a₀y hz₁).elim
          · rintro rfl
            exact ⟨hpath_a₀y.right_mem, Or.inl hpath_yc₀.left_mem⟩
        have hdisj_sa₀_yt : Disjoint V(P_sa₀) V(subgraphUnion P P_yc₀ P_c₀t) := by
          rw [vertexSet_subgraphUnion, disjoint_union_right]
          refine ⟨?_, hdisj_sa₀c₀t⟩
          rw [disjoint_left]
          intro z hz₁ hz₂
          have hz_a₀ : z = a₀ := by
            have : z ∈ V(P_sa₀) ∩ V(P_ac₀) := ⟨hz₁, hP_yc₀.vertexSet_mono hz₂⟩
            rwa [hinter_sa₀, mem_singleton_iff] at this
          subst hz_a₀
          exact ha₀_not_yc₀ hz₂
        have hunion_new : V(P_sa₀) ∪ V(P_a₀y) ∪ V(subgraphUnion P P_yc₀ P_c₀t) = V(P) := by
          rw [vertexSet_subgraphUnion]
          have : V(P_sa₀) ∪ V(P_a₀y) ∪ (V(P_yc₀) ∪ V(P_c₀t)) =
              V(P_sa₀) ∪ (V(P_a₀y) ∪ V(P_yc₀)) ∪ V(P_c₀t) := by
            ext z; simp [or_assoc]
          rw [this, hV_y, hunion_sa₀c₀t]
        exact ih V(P_a₀y).ncard hlt a₀ y P_sa₀ P_a₀y (subgraphUnion P P_yc₀ P_c₀t)
          ha₀Y hyY (Ne.symm hy_ne.1) hP_sa₀ (hP_a₀y.trans hP_ac₀)
          (subgraphUnion_le (hP_yc₀.trans hP_ac₀) hP_c₀t)
          hpath_sa₀ (hpath_a₀y.mono hP_ac₀) hpath_yt
          hinter_sa₀_a₀y hinter_a₀y_yt hdisj_sa₀_yt hunion_new hu_a₀y rfl
      · -- `u ∈ V(P_yc₀)`: replace `a₀` by `y`!
        have hlt : V(P_yc₀).ncard < n := by
          rw [← hcard]
          exact Set.ncard_lt_ncard
            ⟨hP_yc₀.vertexSet_mono, fun hsub => ha₀_not_yc₀ (hsub hpath_ac₀.left_mem)⟩
            hpath_ac₀.vertexSet_finite
        have hV_sa₀_a₀y : V(P_sa₀) ∩ V(P_a₀y) = {a₀} := by
          ext z
          simp only [mem_inter_iff, mem_singleton_iff]
          exact ⟨fun ⟨hz₁, hz₂⟩ => by
            have : z ∈ V(P_sa₀) ∩ V(P_ac₀) := ⟨hz₁, hP_a₀y.vertexSet_mono hz₂⟩
            rwa [hinter_sa₀, mem_singleton_iff] at this,
            fun h => h ▸ ⟨hpath_sa₀.right_mem, hpath_a₀y.left_mem⟩⟩
        have hpath_sy : IsGraphPathWithEnds P (subgraphUnion P P_sa₀ P_a₀y) s y :=
          hpath_sa₀.subgraphUnion (hpath_a₀y.mono hP_ac₀) hV_sa₀_a₀y
        have hinter_sy_yc₀ : V(subgraphUnion P P_sa₀ P_a₀y) ∩ V(P_yc₀) = {y} := by
          ext z
          simp only [vertexSet_subgraphUnion, mem_inter_iff, mem_union, mem_singleton_iff]
          constructor
          · rintro ⟨hz₁ | hz₂, hz₃⟩
            · have hz_a₀ : z = a₀ := by
                have : z ∈ V(P_sa₀) ∩ V(P_ac₀) := ⟨hz₁, hP_yc₀.vertexSet_mono hz₃⟩
                rwa [hinter_sa₀, mem_singleton_iff] at this
              subst hz_a₀
              exact (ha₀_not_yc₀ hz₃).elim
            · have : z ∈ V(P_a₀y) ∩ V(P_yc₀) := ⟨hz₂, hz₃⟩
              rwa [hinter_y, mem_singleton_iff] at this
          · rintro rfl
            exact ⟨Or.inr hpath_a₀y.right_mem, hpath_yc₀.left_mem⟩
        have hinter_yc₀_c₀t : V(P_yc₀) ∩ V(P_c₀t) = {c₀} := by
          ext z
          simp only [mem_inter_iff, mem_singleton_iff]
          exact ⟨fun ⟨hz₁, hz₂⟩ => by
            have : z ∈ V(P_ac₀) ∩ V(P_c₀t) := ⟨hP_yc₀.vertexSet_mono hz₁, hz₂⟩
            rwa [hinter_c₀t, mem_singleton_iff] at this,
            fun h => h ▸ ⟨hpath_yc₀.right_mem, hpath_c₀t.left_mem⟩⟩
        have hdisj_sy_c₀t : Disjoint V(subgraphUnion P P_sa₀ P_a₀y) V(P_c₀t) := by
          rw [vertexSet_subgraphUnion, disjoint_union_left]
          refine ⟨hdisj_sa₀c₀t, ?_⟩
          rw [disjoint_left]
          intro z hz₁ hz₂
          have hz_c₀ : z = c₀ := by
            have : z ∈ V(P_ac₀) ∩ V(P_c₀t) := ⟨hP_a₀y.vertexSet_mono hz₁, hz₂⟩
            rwa [hinter_c₀t, mem_singleton_iff] at this
          subst hz_c₀
          exact hc₀_not_a₀y hz₁
        have hunion_new : V(subgraphUnion P P_sa₀ P_a₀y) ∪ V(P_yc₀) ∪ V(P_c₀t) = V(P) := by
          rw [vertexSet_subgraphUnion]
          have : (V(P_sa₀) ∪ V(P_a₀y)) ∪ V(P_yc₀) ∪ V(P_c₀t) =
              V(P_sa₀) ∪ (V(P_a₀y) ∪ V(P_yc₀)) ∪ V(P_c₀t) := by
            ext z; simp [or_assoc]
          rw [this, hV_y, hunion_sa₀c₀t]
        exact ih V(P_yc₀).ncard hlt y c₀ (subgraphUnion P P_sa₀ P_a₀y) P_yc₀ P_c₀t
          hyY hc₀Y hy_ne.2
          (subgraphUnion_le hP_sa₀ (hP_a₀y.trans hP_ac₀)) (hP_yc₀.trans hP_ac₀) hP_c₀t
          hpath_sy (hpath_yc₀.mono hP_ac₀) hpath_c₀t
          hinter_sy_yc₀ hinter_yc₀_c₀t hdisj_sy_c₀t hunion_new hu_yc₀ rfl
    · refine ⟨a₀, ha₀Y, c₀, hc₀Y, ha₀c₀, P_sa₀, P_ac₀, P_c₀t,
        hP_sa₀, hP_ac₀, hP_c₀t, hpath_sa₀, hpath_ac₀, hpath_c₀t,
        hinter_sa₀, hinter_c₀t, hdisj_sa₀c₀t, hunion_sa₀c₀t, hu_ac₀, ?_⟩
      rw [disjoint_left]
      exact fun y hy hyY => hhit ⟨y, hy, hyY⟩

/-- If `P` is a path in `K` from `s` to `t`, `Y ⊆ V(P)` with `s, t ∈ Y` and `s ≠ t`, and `u ∈ V(P)`,
then there exist `a, c ∈ Y` with `a ≠ c` and a three-way split `P = P_sa ∪ P_ac ∪ P_ct` such that
`u ∈ V(P_ac)` and `Disjoint (V(P_ac) \ {a, c}) Y`. -/
theorem exists_minimal_Y_interval_containing_single {K P : Graph α β} {s t u : α} {Y : Set α}
    (hPK : IsGraphPathWithEnds K P s t)
    (hst : s ≠ t) (hsY : s ∈ Y) (htY : t ∈ Y) (huP : u ∈ V(P)) :
    ∃ a ∈ Y, ∃ c ∈ Y, a ≠ c ∧
      ∃ P_sa P_ac P_ct : Graph α β,
        P_sa ≤ P ∧ P_ac ≤ P ∧ P_ct ≤ P ∧
        IsGraphPathWithEnds P P_sa s a ∧
        IsGraphPathWithEnds P P_ac a c ∧
        IsGraphPathWithEnds P P_ct c t ∧
        V(P_sa) ∩ V(P_ac) = {a} ∧
        V(P_ac) ∩ V(P_ct) = {c} ∧
        Disjoint V(P_sa) V(P_ct) ∧
        V(P_sa) ∪ V(P_ac) ∪ V(P_ct) = V(P) ∧
        u ∈ V(P_ac) ∧
        Disjoint (V(P_ac) \ {a, c}) Y := by
  classical
  obtain ⟨s', t', hst_eq, hst'_ne, P_ss, P_st, P_tt,
    hP_ss, hP_st, hP_tt, hpath_ss, hpath_st, hpath_tt,
    hinter_ss, hinter_tt, hdisj_sstt, hV_union, _, _, _, _⟩ :=
    exists_three_way_split hPK hPK.left_mem hPK.right_mem hst
  -- From `exists_three_way_split` at `s, t`, `s' = s` and `t' = t`!
  have hs'_eq : s' = s := by
    have hs_in : s = s' ∨ s = t' := by
      have : s ∈ ({s', t'} : Set α) := by rw [hst_eq]; simp
      simpa using this
    rcases hs_in with h | h
    · exact h.symm
    · rw [← h] at hpath_tt
      exact (disjoint_left.mp hdisj_sstt hpath_ss.left_mem hpath_tt.left_mem).elim
  have ht'_eq : t' = t := by
    have ht_in : t = s' ∨ t = t' := by
      have : t ∈ ({s', t'} : Set α) := by rw [hst_eq]; simp
      simpa using this
    rcases ht_in with h | h
    · exact (hst (hs'_eq.symm.trans h.symm)).elim
    · exact h.symm
  rw [hs'_eq] at hpath_ss hpath_st hinter_ss
  rw [ht'_eq] at hpath_st hpath_tt hinter_tt
  have hu_st : u ∈ V(P_st) := by
    have hu_in : u ∈ V(P_ss) ∪ V(P_st) ∪ V(P_tt) := by rw [hV_union]; exact huP
    rcases hu_in with (hu_ss | hu_st) | hu_tt
    · rcases hpath_ss with ⟨_, W_ss, hW_ss, hV_ss, _⟩
      have hlen0 := hW_ss.length_eq_zero
      cases W_ss with
      | nil _ =>
        rw [hV_ss] at hu_ss
        simp only [GraphWalk.support_nil, List.mem_singleton] at hu_ss
        rw [hu_ss]
        exact hpath_st.left_mem
      | cons _ _ => simp at hlen0
    · exact hu_st
    · rcases hpath_tt with ⟨_, W_tt, hW_tt, hV_tt, _⟩
      have hlen0 := hW_tt.length_eq_zero
      cases W_tt with
      | nil _ =>
        rw [hV_tt] at hu_tt
        simp only [GraphWalk.support_nil, List.mem_singleton] at hu_tt
        rw [hu_tt]
        exact hpath_st.right_mem
      | cons _ _ => simp at hlen0
  exact trim_path_around_vertex V(P_st).ncard s t P_ss P_st P_tt hsY htY hst
    hP_ss hP_st hP_tt hpath_ss hpath_st hpath_tt hinter_ss hinter_tt hdisj_sstt hV_union hu_st rfl

end GraphMinor.GM09
