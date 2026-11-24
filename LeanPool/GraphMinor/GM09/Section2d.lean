/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Section2c
import LeanPool.GraphMinor.Menger.SimpleGraph

/-!
# Graph Minors IX, Section 2 (Part 4): Menger's Theorem for Graphs and Lemma (2.3)

This file formalizes Lemma (2.3) from Section 2 of
N. Robertson and P. D. Seymour, *Graph Minors. IX. Disjoint crossed paths*,
J. Combin. Theory Ser. B **49** (1990) 40–77 (pages 44–45):
if `{P₁, P₂, P₃}` is a tripod in a society `(G, Ω)`, then either `(G, Ω)` has a cross, or there is
an internal 3-separation `(G₁, G₂)` of `(G, Ω)` with `P₁ ∪ P₂ ∪ P₃ ⊆ G₁`.
-/

public section

namespace GraphMinor.GM09

open Set Graph GraphMinor.Surface GraphMinor.GM06

universe u v

variable {α : Type u} {β : Type v}

/-! ## Menger's Theorem for `Graph α β` -/

/-- Every walk `W : GraphWalk G u v` in `G` with `u ∈ V(G₁)` and `v ∈ V(G₂)` for a separation
`(G₁, G₂)` of `G` contains a vertex in `V(G₁) ∩ V(G₂)`. -/
theorem exists_mem_inter_of_graphWalk {G G₁ G₂ : Graph α β}
    (hsep : IsGraphSeparation G G₁ G₂) {u v : α} (W : GraphWalk G u v)
    (hu : u ∈ V(G₁)) (hv : v ∈ V(G₂)) :
    ∃ z ∈ W.support, z ∈ V(G₁) ∩ V(G₂) := by
  induction W with
  | @nil u _ =>
    exact ⟨u, by simp [GraphWalk.support], hu, hv⟩
  | @cons u w v e hlink rest ih =>
    by_cases hw₁ : w ∈ V(G₁)
    · obtain ⟨z, hz, hz_mem⟩ := ih hw₁ hv
      exact ⟨z, List.mem_cons_of_mem _ hz, hz_mem⟩
    · have he : e ∈ E(G₁) ∪ E(G₂) := by
        rw [hsep.2.2.2.1]
        exact hlink.edge_mem
      rcases he with he₁ | he₂
      · have hlink₁ : G₁.IsLink e u w := (hsep.1.isLink_iff he₁).mpr hlink
        exact (hw₁ hlink₁.right_mem).elim
      · have hlink₂ : G₂.IsLink e u w := (hsep.2.1.isLink_iff he₂).mpr hlink
        exact ⟨u, by simp [GraphWalk.support], hu, hlink₂.left_mem⟩

/-- Every path `P` in `G` from `x ∈ X` to `y ∈ Y` meets `V(G₁) ∩ V(G₂)` whenever `(G₁, G₂)` is a
separation of `G` with `X ⊆ V(G₁)` and `Y ⊆ V(G₂)`. -/
theorem exists_mem_inter_of_isGraphPathWithEnds {G G₁ G₂ P : Graph α β}
    (hsep : IsGraphSeparation G G₁ G₂) {x y : α} (hP : IsGraphPathWithEnds G P x y)
    (hx : x ∈ V(G₁)) (hy : y ∈ V(G₂)) :
    ∃ z ∈ V(P), z ∈ V(G₁) ∩ V(G₂) := by
  rcases hP with ⟨hPG, W, _, hVP, _⟩
  obtain ⟨W_G, hs, _⟩ := W.exists_transfer (fun _ _ _ _ hl => hl.mono hPG)
    (fun _ hz => hPG.vertexSet_mono (W.mem_vertexSet_of_mem_support hz))
  obtain ⟨z, hzW, hz_inter⟩ := exists_mem_inter_of_graphWalk hsep W_G hx hy
  rw [hs] at hzW
  exact ⟨z, by rw [hVP]; exact hzW, hz_inter⟩

/-- If `(G₁, G₂)` is a separation of `G` with `X ⊆ V(G₁)` and `Y ⊆ V(G₂)`, and there are `k`
mutually disjoint paths in `G` from `X` to `Y`, then `k ≤ (V(G₁) ∩ V(G₂)).ncard`. -/
theorem ncard_inter_ge_of_disjoint_paths {G G₁ G₂ : Graph α β} [Finite V(G)]
    (hsep : IsGraphSeparation G G₁ G₂) {X Y : Set α} (hX : X ⊆ V(G₁)) (hY : Y ⊆ V(G₂))
    {k : ℕ} {P : Fin k → Graph α β} {x y : Fin k → α}
    (hdisj : Pairwise (fun i j => Disjoint V(P i) V(P j)))
    (hP : ∀ i : Fin k, IsGraphPathWithEnds G (P i) (x i) (y i) ∧ x i ∈ X ∧ y i ∈ Y) :
    k ≤ (V(G₁) ∩ V(G₂)).ncard := by
  have hex : ∀ i : Fin k, ∃ z ∈ V(P i), z ∈ V(G₁) ∩ V(G₂) := fun i =>
    exists_mem_inter_of_isGraphPathWithEnds hsep (hP i).1 (hX (hP i).2.1) (hY (hP i).2.2)
  choose z hzP hz_inter using hex
  have hz_inj : Function.Injective z := by
    intro i j hij
    by_contra hne
    exact disjoint_left.mp (hdisj hne) (hzP i) (hij ▸ hzP j)
  have hsub : range z ⊆ V(G₁) ∩ V(G₂) := by rintro _ ⟨i, rfl⟩; exact hz_inter i
  have hfin : (V(G₁) ∩ V(G₂)).Finite :=
    (toFinite V(G)).subset (inter_subset_left.trans hsep.1.vertexSet_mono)
  have hle := ncard_le_ncard hsub hfin
  rwa [ncard_range_of_injective hz_inj, Nat.card_fin] at hle

/-- The vertices of `G` reachable from `X` by walks in `G` avoiding `S`. -/
private def reachableWalkAvoiding (G : Graph α β) (X S : Set α) : Set α :=
  {v ∈ V(G) | ∃ x ∈ X, ∃ W : GraphWalk G x v, ∀ z ∈ W.support, z ∉ S}

/-- From a vertex separator `S ⊆ V(G)` between `X` and `Y` in `G`, construct a separation
`(G₁, G₂)` of `G` with `G₁ = G.induce V(G₁)`, `X ⊆ V(G₁)`, `Y ⊆ V(G₂)`, and `V(G₁) ∩ V(G₂) = S`. -/
theorem exists_graphSeparation_of_vertexSeparator {G : Graph α β} {X Y S : Set α}
    (hX : X ⊆ V(G)) (hY : Y ⊆ V(G)) (hS : S ⊆ V(G))
    (hsep_walk : ∀ x ∈ X, ∀ y ∈ Y, ∀ W : GraphWalk G x y, ∃ z ∈ W.support, z ∈ S) :
    ∃ G₁ G₂ : Graph α β,
      IsGraphSeparation G G₁ G₂ ∧
      G₁ = G.induce V(G₁) ∧
      X ⊆ V(G₁) ∧
      Y ⊆ V(G₂) ∧
      V(G₁) ∩ V(G₂) = S := by
  let R := reachableWalkAvoiding G X S
  have hR_sub : R ⊆ V(G) \ S := by
    rintro v ⟨hvG, x, _, W, hW⟩
    exact ⟨hvG, hW v W.end_mem_support⟩
  let V₁ : Set α := R ∪ S
  let V₂ : Set α := V(G) \ R
  have hV₁_sub : V₁ ⊆ V(G) := union_subset (hR_sub.trans sdiff_subset) hS
  have hV₂_sub : V₂ ⊆ V(G) := sdiff_subset
  let G₁ : Graph α β := G.induce V₁
  let G₂ : Graph α β := (G.induce V₂).restrict (E(G) \ E(G₁))
  have hG₁_le : G₁ ≤ G := G.induce_le hV₁_sub
  have hG₂_le : G₂ ≤ G := restrict_le.trans (G.induce_le hV₂_sub)
  have hV₁_eq : V(G₁) = V₁ := rfl
  have hV₂_eq : V(G₂) = V₂ := rfl
  have hE₂_eq : E(G₂) = E(G) \ E(G₁) := by
    change E((G.induce V₂).restrict (E(G) \ E(G₁))) = E(G) \ E(G₁)
    rw [edgeSet_restrict, inter_eq_right]
    rintro e ⟨heG, he_not_G₁⟩
    obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet heG
    refine ⟨u, v, huv, ⟨huv.left_mem, fun huR => he_not_G₁ ?_⟩,
      ⟨huv.right_mem, fun hvR => he_not_G₁ ?_⟩⟩
    · refine ⟨u, v, huv, Or.inl huR, ?_⟩
      by_cases hvS : v ∈ S
      · exact Or.inr hvS
      · obtain ⟨_, x, hxX, W, hW⟩ := huR
        refine Or.inl ⟨huv.right_mem, x, hxX, W.append (.cons huv (.nil huv.right_mem)), ?_⟩
        intro z hz
        rw [GraphWalk.mem_support_append] at hz
        rcases hz with hzW | hz_v
        · exact hW z hzW
        · simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false] at hz_v
          rcases hz_v with rfl | rfl
          · exact hW z W.end_mem_support
          · exact hvS
    · refine ⟨u, v, huv, ?_, Or.inl hvR⟩
      by_cases huS : u ∈ S
      · exact Or.inr huS
      · obtain ⟨_, x, hxX, W, hW⟩ := hvR
        refine Or.inl ⟨huv.left_mem, x, hxX, W.append (.cons huv.symm (.nil huv.left_mem)), ?_⟩
        intro z hz
        rw [GraphWalk.mem_support_append] at hz
        rcases hz with hzW | hz_u
        · exact hW z hzW
        · simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false] at hz_u
          rcases hz_u with rfl | rfl
          · exact hW z W.end_mem_support
          · exact huS
  refine ⟨G₁, G₂, ⟨hG₁_le, hG₂_le, ?_, ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
  · ext v
    simp only [hV₁_eq, hV₂_eq, V₁, V₂, mem_union, mem_sdiff]
    constructor
    · rintro ((hvR | hvS) | ⟨hvG, _⟩)
      · exact hvR.1
      · exact hS hvS
      · exact hvG
    · intro hvG
      by_cases hvR : v ∈ R
      · exact Or.inl (Or.inl hvR)
      · exact Or.inr ⟨hvG, hvR⟩
  · rw [hE₂_eq, union_sdiff_cancel hG₁_le.edgeSet_mono]
  · rw [hE₂_eq]
    exact disjoint_sdiff_right
  · intro x hxX
    by_cases hxS : x ∈ S
    · exact Or.inr hxS
    · refine Or.inl ⟨hX hxX, x, hxX, .nil (hX hxX), fun z hz => ?_⟩
      simp only [GraphWalk.support, List.mem_singleton] at hz
      exact hz ▸ hxS
  · intro y hyY
    refine ⟨hY hyY, ?_⟩
    rintro ⟨_, x, hxX, W, hW⟩
    obtain ⟨z, hzW, hzS⟩ := hsep_walk x hxX y hyY W
    exact hW z hzW hzS
  · ext v
    simp only [hV₁_eq, hV₂_eq, V₁, V₂, mem_inter_iff, mem_union, mem_sdiff]
    constructor
    · rintro ⟨hvR | hvS, _, hv_not_R⟩
      · exact (hv_not_R hvR).elim
      · exact hvS
    · intro hvS
      exact ⟨Or.inr hvS, hS hvS, fun hvR => (hR_sub hvR).2 hvS⟩

/-- **Menger's Theorem for `Graph α β`**:
For any finite graph `G`, subsets `X, Y ⊆ V(G)`, and `k : ℕ`, either there exist `k` mutually
disjoint `X → Y` paths in `G`, or there exists a separation `(G₁, G₂)` of `G` with
`G₁ = G.induce V(G₁)`, `X ⊆ V(G₁)`, `Y ⊆ V(G₂)`, and `(V(G₁) ∩ V(G₂)).ncard < k`. -/
theorem exists_fromToPaths_or_graphSeparation {G : Graph α β} [Finite V(G)]
    {X Y : Set α} (hX : X ⊆ V(G)) (hY : Y ⊆ V(G)) (k : ℕ) :
    (∃ Q : Fin k → Graph α β,
      Pairwise (fun i j => Disjoint V(Q i) V(Q j)) ∧
      ∀ i : Fin k, IsFromToPath G (Q i) X Y) ∨
    (∃ G₁ G₂ : Graph α β,
      IsGraphSeparation G G₁ G₂ ∧
      G₁ = G.induce V(G₁) ∧
      X ⊆ V(G₁) ∧
      Y ⊆ V(G₂) ∧
      (V(G₁) ∩ V(G₂)).ncard < k) := by
  classical
  let K : SimpleGraph ↥V(G) := {
    Adj u v := u ≠ v ∧ ∃ e : β, G.IsLink e u.1 v.1
    symm := ⟨fun _ _ ⟨hne, e, he⟩ => ⟨hne.symm, e, he.symm⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩
  }
  let X₀ : Set ↥V(G) := {u : ↥V(G) | u.1 ∈ X}
  let Y₀ : Set ↥V(G) := {u : ↥V(G) | u.1 ∈ Y}
  by_cases hM : ∀ S₀ : Set ↥V(G),
      (∀ P : PathFromTo K X₀ Y₀, ∃ x ∈ P.walk.support, x ∈ S₀) → k ≤ S₀.ncard
  · left
    obtain ⟨P₀, hP₀_disj⟩ :=
      GraphMinor.Menger.exists_disjointPaths K X₀ Y₀ inferInstance k hM
    -- Lift any `SimpleGraph.Walk` in `K` to a `GraphWalk` in `G` with the same vertex support.
    have hlift_walk : ∀ {u v : ↥V(G)} (w : K.Walk u v),
        ∃ W : GraphWalk G u.1 v.1, W.support = w.support.map Subtype.val := by
      intro u v w
      induction w with
      | @nil u =>
        exact ⟨.nil u.2, rfl⟩
      | @cons u u' v hadj rest ih =>
        obtain ⟨_, e, he⟩ := hadj
        obtain ⟨W', hW'⟩ := ih
        exact ⟨.cons he W', by simp [GraphWalk.support, hW']⟩
    have hpath_ex : ∀ i : Fin k, ∃ Q_i : Graph α β,
        V(Q_i) ⊆ Subtype.val '' {u : ↥V(G) | u ∈ (P₀ i).walk.support} ∧
        IsFromToPath G Q_i X Y := by
      intro i
      obtain ⟨W_i, hW_i_supp⟩ := hlift_walk (P₀ i).walk
      have hW_i_simple : W_i.IsSimple := by
        unfold GraphWalk.IsSimple
        rw [hW_i_supp]
        exact (P₀ i).isPath.support_nodup.map Subtype.val_injective
      have hP_i : IsGraphPathWithEnds G (walkSubgraph W_i) (P₀ i).first.1 (P₀ i).last.1 :=
        isGraphPathWithEnds_walkSubgraph hW_i_simple
      obtain ⟨x_i, _, y_i, _, Q_i, hQ_i_le, hQ_i⟩ :=
        hP_i.exists_isFromToPathWithEnds (P₀ i).first_mem (P₀ i).last_mem
      refine ⟨Q_i, ?_, x_i, y_i, hQ_i⟩
      intro z hz
      have hzW : z ∈ V(walkSubgraph W_i) := hQ_i_le.vertexSet_mono hz
      rw [vertexSet_walkSubgraph, mem_ofPred_eq, hW_i_supp, List.mem_map] at hzW
      rcases hzW with ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
    choose Q hQ_sub hQ using hpath_ex
    refine ⟨Q, fun i j hij => disjoint_left.mpr fun z hzi hzj => ?_, hQ⟩
    obtain ⟨ui, hui, rfl⟩ := hQ_sub i hzi
    obtain ⟨uj, huj, huj_eq⟩ := hQ_sub j hzj
    have hu_eq : ui = uj := Subtype.val_injective huj_eq.symm
    exact disjoint_left.mp (hP₀_disj hij) hui (hu_eq ▸ huj)
  · right
    push Not at hM
    obtain ⟨S₀, hS₀_sep, hS₀_lt⟩ := hM
    let S : Set α := Subtype.val '' S₀
    have hS_sub : S ⊆ V(G) := by rintro _ ⟨u, _, rfl⟩; exact u.2
    have hS_card : S.ncard < k := by
      rwa [ncard_image_of_injective S₀ Subtype.val_injective]
    -- Every `GraphWalk G x y` projects to a `K.Walk` with support contained in `W.support`.
    have hproj_walk : ∀ {x y : α} (W : GraphWalk G x y),
        ∃ (hx : x ∈ V(G)) (hy : y ∈ V(G)) (w : K.Walk ⟨x, hx⟩ ⟨y, hy⟩),
          ∀ u ∈ w.support, u.1 ∈ W.support := by
      intro x y W
      induction W with
      | @nil x hx =>
        refine ⟨hx, hx, .nil, fun u hu => ?_⟩
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
        subst hu
        exact List.mem_cons_self
      | @cons x x' y e hlink rest ih =>
        obtain ⟨hx', hy, w', hw'⟩ := ih
        have hx : x ∈ V(G) := hlink.left_mem
        by_cases hxx' : (⟨x, hx⟩ : ↥V(G)) = ⟨x', hx'⟩
        · refine ⟨hx, hy, w'.copy hxx'.symm rfl, fun u hu => ?_⟩
          rw [SimpleGraph.Walk.support_copy] at hu
          exact List.mem_cons_of_mem _ (hw' u hu)
        · have hadj : K.Adj ⟨x, hx⟩ ⟨x', hx'⟩ := ⟨hxx', e, hlink⟩
          refine ⟨hx, hy, .cons hadj w', fun u hu => ?_⟩
          rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hu
          rcases hu with rfl | hu'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hw' u hu')
    have hsep_walk : ∀ x ∈ X, ∀ y ∈ Y, ∀ W : GraphWalk G x y, ∃ z ∈ W.support, z ∈ S := by
      intro x hxX y hyY W
      obtain ⟨hxG, hyG, w, hw⟩ := hproj_walk W
      let p : PathFromTo K X₀ Y₀ :=
        ⟨⟨x, hxG⟩, ⟨y, hyG⟩, w.bypass, w.bypass_isPath, hxX, hyY⟩
      obtain ⟨u, hu_supp, hu_S₀⟩ := hS₀_sep p
      exact ⟨u.1, hw u (w.support_bypass_subset_support hu_supp), u, hu_S₀, rfl⟩
    obtain ⟨G₁, G₂, hsep, hG₁_ind, hX₁, hY₂, hinter⟩ :=
      exists_graphSeparation_of_vertexSeparator hX hY hS_sub hsep_walk
    exact ⟨G₁, G₂, hsep, hG₁_ind, hX₁, hY₂, hinter ▸ hS_card⟩

/-! ## Four Distinct Elements in a Cyclic Permutation -/

namespace CyclicPerm

variable {Ω : CyclicPerm α}

theorem isClockwise4_iff {v₁ v₂ v₃ v₄ : α} :
    Ω.IsClockwiseSeq [v₁, v₂, v₃, v₄] ↔
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ v₄ ∧ v₂ ≠ v₃ ∧ v₂ ≠ v₄ ∧ v₃ ≠ v₄ ∧
      v₁ ∈ Ω.bar ∧ v₂ ∈ Ω.bar ∧ v₃ ∈ Ω.bar ∧ v₄ ∈ Ω.bar ∧
      Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₁ v₂ ∧
      Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₂ v₃ ∧
      Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₃ v₄ ∧
      Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₄ v₁ := by
  unfold IsClockwiseSeq
  have hset : {v | v ∈ ([v₁, v₂, v₃, v₄] : List α)} = {v₁, v₂, v₃, v₄} := by
    ext x; simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hnodup, hmem, hhit⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnodup
    have h0 : Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₁ v₂ := by
      have := hhit 0 (by simp); rwa [hset] at this
    have h1 : Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₂ v₃ := by
      have := hhit 1 (by simp); rwa [hset] at this
    have h2 : Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₃ v₄ := by
      have := hhit 2 (by simp); rwa [hset] at this
    have h3 : Ω.FirstHitIn {v₁, v₂, v₃, v₄} v₄ v₁ := by
      have := hhit 3 (by simp); rw [hset] at this; simpa using this
    exact ⟨hnodup.1.1, hnodup.1.2.1, hnodup.1.2.2, hnodup.2.1.1, hnodup.2.1.2, hnodup.2.2.1,
      hmem v₁ (by simp), hmem v₂ (by simp), hmem v₃ (by simp), hmem v₄ (by simp),
      h0, h1, h2, h3⟩
  · rintro ⟨h12, h13, h14, h23, h24, h34, hv1, hv2, hv3, hv4, h0, h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [h12, h13, h14, h23, h24, h34]
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> assumption
    · intro i hi
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hi
      rw [hset]
      rcases i with _ | _ | _ | _ | i
      · exact h0
      · exact h1
      · exact h2
      · simpa using h3
      · omega

theorem isClockwise4_rotate {v₁ v₂ v₃ v₄ : α} (h : Ω.IsClockwiseSeq [v₁, v₂, v₃, v₄]) :
    Ω.IsClockwiseSeq [v₂, v₃, v₄, v₁] := by
  rw [isClockwise4_iff] at h ⊢
  rcases h with ⟨h12, h13, h14, h23, h24, h34, hv1, hv2, hv3, hv4, h0, h1, h2, h3⟩
  have hset : ({v₂, v₃, v₄, v₁} : Set α) = {v₁, v₂, v₃, v₄} := by
    ext x; simp [or_comm, or_left_comm]
  rw [hset]
  exact ⟨h23, h24, h12.symm, h34, h13.symm, h14.symm, hv2, hv3, hv4, hv1, h1, h2, h3, h0⟩

theorem not_firstHitIn_two_cycle {X : Set α} {a b c : α}
    (ha : a ∈ Ω.bar) (hc : c ∈ Ω.bar) (haX : a ∈ X) (hcX : c ∈ X)
    (hca : c ≠ a) (hcb : c ≠ b)
    (h₁ : Ω.FirstHitIn X a b) (h₂ : Ω.FirstHitIn X b a) : False := by
  rcases h₁ with ⟨k₁, hk₁, rfl, _, hmin₁⟩
  rcases h₂ with ⟨k₂, hk₂, heq₂, _, hmin₂⟩
  have hself : Ω.FirstHitIn (X \ {(Ω.toFun^[k₁]) a}) a a := by
    refine ⟨k₁ + k₂, by omega, ?_, ⟨haX, fun h => ?_⟩, fun j hj1 hjlt hj_in => ?_⟩
    · rw [add_comm, Function.iterate_add_apply, heq₂]
    · rw [mem_singleton_iff] at h
      exact Ω.not_firstHitIn_self ha hc hcX hca
        ⟨k₁, hk₁, h.symm, haX, hmin₁⟩
    · rcases lt_trichotomy j k₁ with hlt | rfl | hgt
      · exact hmin₁ j hj1 hlt hj_in.1
      · exact hj_in.2 rfl
      · have hd1 : 1 ≤ j - k₁ := by omega
        have hd2 : j - k₁ < k₂ := by omega
        have heq_j : (Ω.toFun^[j - k₁]) ((Ω.toFun^[k₁]) a) = (Ω.toFun^[j]) a := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hgt)]
        exact hmin₂ (j - k₁) hd1 hd2 (heq_j ▸ hj_in.1)
  have hcb' : c ∈ X \ {(Ω.toFun^[k₁]) a} := ⟨hcX, by simpa using hcb⟩
  exact Ω.not_firstHitIn_self ha hc hcb' hca hself

theorem isClockwise4_of_firstHitIn_two {v₁ a b c : α}
    (hv₁ : v₁ ∈ Ω.bar) (ha : a ∈ Ω.bar) (hb : b ∈ Ω.bar) (hc : c ∈ Ω.bar)
    (h1a : v₁ ≠ a) (h1b : v₁ ≠ b) (h1c : v₁ ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hhit1 : Ω.FirstHitIn {v₁, a, b, c} v₁ a)
    (hhit2 : Ω.FirstHitIn {v₁, a, b, c} a b) :
    Ω.IsClockwiseSeq [v₁, a, b, c] := by
  have hne : (Ω.bar ∩ {v₁, a, b, c}).Nonempty := ⟨v₁, hv₁, by simp⟩
  obtain ⟨yb, hyb⟩ := Ω.exists_firstHitIn hb hne
  obtain ⟨yc, hyc⟩ := Ω.exists_firstHitIn hc hne
  have hyc_eq : yc = v₁ := by
    have hmem := hyc.mem_set
    simp only [mem_insert_iff, mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h
    · exact h
    · rw [h] at hyc
      exact (h1c (hhit1.inj_left hv₁ hc (by simp) (by simp) hyc)).elim
    · rw [h] at hyc
      exact (hac (hhit2.inj_left ha hc (by simp) (by simp) hyc)).elim
    · rw [h] at hyc
      exact (Ω.not_firstHitIn_self hc hv₁ (by simp) h1c hyc).elim
  rw [hyc_eq] at hyc
  have hyb_eq : yb = c := by
    have hmem := hyb.mem_set
    simp only [mem_insert_iff, mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h
    · rw [h] at hyb
      exact (hbc (hyb.inj_left hb hc (by simp) (by simp) hyc)).elim
    · rw [h] at hyb
      exact (h1b (hhit1.inj_left hv₁ hb (by simp) (by simp) hyb)).elim
    · rw [h] at hyb
      exact (Ω.not_firstHitIn_self hb hv₁ (by simp) h1b hyb).elim
    · exact h
  rw [hyb_eq] at hyb
  exact isClockwise4_iff.mpr ⟨h1a, h1b, h1c, hab, hac, hbc, hv₁, ha, hb, hc, hhit1, hhit2, hyb, hyc⟩

/-- For any four distinct elements `w₁, w₂, w₃, w₄ ∈ Ω.bar`, one of the three pairings crosses:
`{w₁, w₄}` crosses `{w₂, w₃}`, or `{w₁, w₂}` crosses `{w₃, w₄}`, or `{w₁, w₃}` crosses `{w₂, w₄}`.
-/
theorem crosses_of_four_distinct {w₁ w₂ w₃ w₄ : α}
    (hw₁ : w₁ ∈ Ω.bar) (hw₂ : w₂ ∈ Ω.bar) (hw₃ : w₃ ∈ Ω.bar) (hw₄ : w₄ ∈ Ω.bar)
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h14 : w₁ ≠ w₄)
    (h23 : w₂ ≠ w₃) (h24 : w₂ ≠ w₄) (h34 : w₃ ≠ w₄) :
    Ω.Crosses w₁ w₄ w₂ w₃ ∨ Ω.Crosses w₁ w₂ w₃ w₄ ∨ Ω.Crosses w₁ w₃ w₂ w₄ := by
  let X : Set α := {w₁, w₂, w₃, w₄}
  have hne : (Ω.bar ∩ X).Nonempty := ⟨w₁, hw₁, by simp [X]⟩
  obtain ⟨y₁, hy₁⟩ := Ω.exists_firstHitIn hw₁ hne
  have hy₁_ne : y₁ ≠ w₁ := fun h =>
    Ω.not_firstHitIn_self hw₁ hw₂ (by simp [X]) h12.symm (h ▸ hy₁)
  have hy₁_mem := hy₁.mem_set
  simp only [X, mem_insert_iff, mem_singleton_iff] at hy₁_mem
  rcases hy₁_mem with h1 | h1 | h1 | h1
  · exact (hy₁_ne h1).elim
  · rw [h1] at hy₁
    obtain ⟨y₂, hy₂⟩ := Ω.exists_firstHitIn hw₂ hne
    have hy₂_ne2 : y₂ ≠ w₂ := fun h =>
      Ω.not_firstHitIn_self hw₂ hw₁ (by simp [X]) h12 (h ▸ hy₂)
    have hy₂_ne1 : y₂ ≠ w₁ := fun h =>
      Ω.not_firstHitIn_two_cycle hw₁ hw₃ (by simp [X]) (by simp [X]) h13.symm h23.symm hy₁ (h ▸ hy₂)
    have hy₂_mem := hy₂.mem_set
    simp only [X, mem_insert_iff, mem_singleton_iff] at hy₂_mem
    rcases hy₂_mem with h2 | h2 | h2 | h2
    · exact (hy₂_ne1 h2).elim
    · exact (hy₂_ne2 h2).elim
    · rw [h2] at hy₂
      right; right; left
      exact isClockwise4_of_firstHitIn_two hw₁ hw₂ hw₃ hw₄ h12 h13 h14 h23 h24 h34 hy₁ hy₂
    · rw [h2] at hy₂
      left; left
      have hset : ({w₁, w₂, w₄, w₃} : Set α) = X := by ext x; simp [X, or_comm]
      exact isClockwise4_of_firstHitIn_two hw₁ hw₂ hw₄ hw₃ h12 h14 h13 h24 h23 h34.symm
        (hset.symm ▸ hy₁) (hset.symm ▸ hy₂)
  · rw [h1] at hy₁
    obtain ⟨y₃, hy₃⟩ := Ω.exists_firstHitIn hw₃ hne
    have hy₃_ne3 : y₃ ≠ w₃ := fun h =>
      Ω.not_firstHitIn_self hw₃ hw₁ (by simp [X]) h13 (h ▸ hy₃)
    have hy₃_ne1 : y₃ ≠ w₁ := fun h =>
      Ω.not_firstHitIn_two_cycle hw₁ hw₂ (by simp [X]) (by simp [X]) h12.symm h23 hy₁ (h ▸ hy₃)
    have hy₃_mem := hy₃.mem_set
    simp only [X, mem_insert_iff, mem_singleton_iff] at hy₃_mem
    rcases hy₃_mem with h3 | h3 | h3 | h3
    · exact (hy₃_ne1 h3).elim
    · rw [h3] at hy₃
      right; left; left
      have hset : ({w₁, w₃, w₂, w₄} : Set α) = X := by ext x; simp [X, or_left_comm]
      exact isClockwise4_of_firstHitIn_two hw₁ hw₃ hw₂ hw₄ h13 h12 h14 h23.symm h34 h24
        (hset.symm ▸ hy₁) (hset.symm ▸ hy₃)
    · exact (hy₃_ne3 h3).elim
    · rw [h3] at hy₃
      left; right
      have hset : ({w₁, w₃, w₄, w₂} : Set α) = X := by ext x; simp [X, or_comm, or_left_comm]
      exact isClockwise4_rotate (isClockwise4_of_firstHitIn_two hw₁ hw₃ hw₄ hw₂
        h13 h14 h12 h34 h23.symm h24.symm (hset.symm ▸ hy₁) (hset.symm ▸ hy₃))
  · rw [h1] at hy₁
    obtain ⟨y₄, hy₄⟩ := Ω.exists_firstHitIn hw₄ hne
    have hy₄_ne4 : y₄ ≠ w₄ := fun h =>
      Ω.not_firstHitIn_self hw₄ hw₁ (by simp [X]) h14 (h ▸ hy₄)
    have hy₄_ne1 : y₄ ≠ w₁ := fun h =>
      Ω.not_firstHitIn_two_cycle hw₁ hw₂ (by simp [X]) (by simp [X]) h12.symm h24 hy₁ (h ▸ hy₄)
    have hy₄_mem := hy₄.mem_set
    simp only [X, mem_insert_iff, mem_singleton_iff] at hy₄_mem
    rcases hy₄_mem with h4 | h4 | h4 | h4
    · exact (hy₄_ne1 h4).elim
    · rw [h4] at hy₄
      right; left; right
      have hset : ({w₁, w₄, w₂, w₃} : Set α) = X := by ext x; simp [X, or_comm, or_left_comm]
      exact isClockwise4_rotate (isClockwise4_of_firstHitIn_two hw₁ hw₄ hw₂ hw₃
        h14 h12 h13 h24.symm h34.symm h23 (hset.symm ▸ hy₁) (hset.symm ▸ hy₄))
    · rw [h4] at hy₄
      right; right; right
      have hset : ({w₁, w₄, w₃, w₂} : Set α) = X := by ext x; simp [X, or_comm, or_left_comm]
      exact isClockwise4_rotate (isClockwise4_of_firstHitIn_two hw₁ hw₄ hw₃ hw₂
        h14 h13 h12 h34.symm h24.symm h23.symm (hset.symm ▸ hy₁) (hset.symm ▸ hy₄))
    · exact (hy₄_ne4 h4).elim

theorem Crosses.ne_ends {a₁ b₁ a₂ b₂ : α} (h : Ω.Crosses a₁ b₁ a₂ b₂) :
    a₁ ≠ b₁ ∧ a₂ ≠ b₂ := by
  rcases h with h1 | h2
  · obtain ⟨_, h1b, _, _, h2b, _⟩ := isClockwise4_iff.mp h1
    exact ⟨h1b, h2b⟩
  · obtain ⟨_, h2b, _, _, h1b, _⟩ := isClockwise4_iff.mp h2
    exact ⟨h1b.symm, h2b.symm⟩

end CyclicPerm

/-! ## Proof of Lemma (2.3) (pages 44–45) -/

theorem IsGraphPathWithEnds.exists_walk_in {G P : Graph α β} {a b : α} {U : Set α}
    (hP : IsGraphPathWithEnds G P a b) (hU : V(P) ⊆ U) :
    ∃ W : GraphWalk G a b, {x | x ∈ W.support} ⊆ U := by
  rcases hP with ⟨hPG, W, _, hVP, _⟩
  obtain ⟨W_G, hs, _⟩ := W.exists_transfer (fun _ _ _ _ hl => hl.mono hPG)
    (fun _ hx => hPG.vertexSet_mono (W.mem_vertexSet_of_mem_support hx))
  refine ⟨W_G, fun x hx => hU ?_⟩
  rw [hVP, mem_ofPred_eq, ← hs]
  exact hx

theorem exists_walk_in_trans {G : Graph α β} {a b c : α} {U : Set α}
    (h₁ : ∃ W : GraphWalk G a b, {x | x ∈ W.support} ⊆ U)
    (h₂ : ∃ W : GraphWalk G b c, {x | x ∈ W.support} ⊆ U) :
    ∃ W : GraphWalk G a c, {x | x ∈ W.support} ⊆ U := by
  obtain ⟨W₁, hW₁⟩ := h₁
  obtain ⟨W₂, hW₂⟩ := h₂
  refine ⟨W₁.append W₂, fun x hx => ?_⟩
  rw [mem_ofPred_eq, GraphWalk.mem_support_append] at hx
  exact hx.elim (fun h => hW₁ h) (fun h => hW₂ h)

theorem Society.exists_isCross_of_disjoint_walks (S : Society α β)
    {a₁ b₁ a₂ b₂ : α} {U₁ U₂ : Set α}
    (ha₁ : a₁ ∈ S.Ω.bar) (hb₁ : b₁ ∈ S.Ω.bar) (ha₂ : a₂ ∈ S.Ω.bar) (hb₂ : b₂ ∈ S.Ω.bar)
    (hcross : S.Ω.Crosses a₁ b₁ a₂ b₂)
    (hdisj : Disjoint U₁ U₂)
    (hW₁ : ∃ W : GraphWalk S.G a₁ b₁, {x | x ∈ W.support} ⊆ U₁)
    (hW₂ : ∃ W : GraphWalk S.G a₂ b₂, {x | x ∈ W.support} ⊆ U₂) :
    ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂ := by
  obtain ⟨hab₁, hab₂⟩ := hcross.ne_ends
  obtain ⟨W₁, hU₁⟩ := hW₁
  obtain ⟨W₂, hU₂⟩ := hW₂
  obtain ⟨Q₁, hQ₁, hV₁, _⟩ := exists_isGraphPathWithEnds_of_walk W₁
  obtain ⟨Q₂, hQ₂, hV₂, _⟩ := exists_isGraphPathWithEnds_of_walk W₂
  exact ⟨Q₁, Q₂, hdisj.mono (hV₁.trans hU₁) (hV₂.trans hU₂),
    a₁, b₁, a₂, b₂, ⟨hQ₁, hab₁, ha₁, hb₁⟩, ⟨hQ₂, hab₂, ha₂, hb₂⟩, hcross⟩

/-- Helper for Case B and Case C of the tripod-with-4-paths cross construction:
given `P₁_v` (from `s₁` to `v` in `V(P₁) \ {u}`), `L_u` (from `u` to `s₄` in `V(P₁) \ {v}`),
with `Disjoint V(P₁_v) V(L_u)`, and `P_A` (from `u` to `v` with internal vertex `s_A`),
`P_B` (from `u` to `v` with internal vertex `s_B`), and disjoint `X → ΩBar` paths `R₁, R_A, R_B, R₄`
from `s₁, s_A, s_B, s₄` to `w₁, w_A, w_B, w₄`, there exist disjoint walks in `S.G` between
`(w₁, w_A)` and `(w_B, w₄)`. -/
private theorem exists_disjoint_walks_pairBC {G P₁ P_A P_B P₁_v L_u R₁ R_A R_B R₄ : Graph α β}
    {X Y : Set α} {u v s₁ s_A s_B s₄ w₁ w_A w_B w₄ : α}
    (hP₁_v_le : V(P₁_v) ⊆ V(P₁) \ {u})
    (hL_u_le : V(L_u) ⊆ V(P₁) \ {v})
    (hdisj_P₁ : Disjoint V(P₁_v) V(L_u))
    (hP₁_v : IsGraphPathWithEnds G P₁_v s₁ v)
    (hL_u : IsGraphPathWithEnds G L_u u s₄)
    (hP_A : IsGraphPathWithEnds G P_A u v)
    (hP_B : IsGraphPathWithEnds G P_B u v)
    (hinter_1A : V(P₁) ∩ V(P_A) = {u, v})
    (hinter_1B : V(P₁) ∩ V(P_B) = {u, v})
    (hinter_AB : V(P_A) ∩ V(P_B) = {u, v})
    (hs_A : s_A ∈ V(P_A) \ {u, v})
    (hs_B : s_B ∈ V(P_B) \ {u, v})
    (hX_sub : V(P₁) ∪ V(P_A) ∪ V(P_B) ⊆ X)
    (hs₁_X : s₁ ∈ V(P₁) \ {u, v})
    (hs₄_X : s₄ ∈ V(L_u))
    (hR₁ : IsFromToPathWithEnds G R₁ X Y s₁ w₁)
    (hR_A : IsFromToPathWithEnds G R_A X Y s_A w_A)
    (hR_B : IsFromToPathWithEnds G R_B X Y s_B w_B)
    (hR₄ : IsFromToPathWithEnds G R₄ X Y s₄ w₄)
    (hdisj_1B : Disjoint V(R₁) V(R_B))
    (hdisj_14 : Disjoint V(R₁) V(R₄))
    (hdisj_AB : Disjoint V(R_A) V(R_B))
    (hdisj_A4 : Disjoint V(R_A) V(R₄)) :
    ∃ U₁ U₂ : Set α, Disjoint U₁ U₂ ∧
      (∃ W₁ : GraphWalk G w₁ w_A, {x | x ∈ W₁.support} ⊆ U₁) ∧
      (∃ W₂ : GraphWalk G w_B w₄, {x | x ∈ W₂.support} ⊆ U₂) := by
  obtain ⟨PA_u, PA_v, hPA_u_le, hPA_v_le, hPA_u, hPA_v, _, hinter_PA, _⟩ :=
    hP_A.exists_split_at hs_A.1
  obtain ⟨PB_u, PB_v, hPB_u_le, hPB_v_le, hPB_u, hPB_v, _, hinter_PB, _⟩ :=
    hP_B.exists_split_at hs_B.1
  have hu_not_PAv : u ∉ V(PA_v) := by
    intro hu_in
    have : u ∈ V(PA_u) ∩ V(PA_v) := ⟨hPA_u.left_mem, hu_in⟩
    rw [hinter_PA, mem_singleton_iff] at this
    exact hs_A.2 (by simp [this])
  have hv_not_PBu : v ∉ V(PB_u) := by
    intro hv_in
    have : v ∈ V(PB_u) ∩ V(PB_v) := ⟨hv_in, hPB_v.right_mem⟩
    rw [hinter_PB, mem_singleton_iff] at this
    exact hs_B.2 (by simp [this])
  let U₁ : Set α := V(R₁) ∪ V(P₁_v) ∪ V(PA_v) ∪ V(R_A)
  let U₂ : Set α := V(R_B) ∪ V(PB_u) ∪ V(L_u) ∪ V(R₄)
  have hwalk₁ : ∃ W₁ : GraphWalk G w₁ w_A, {x | x ∈ W₁.support} ⊆ U₁ :=
    exists_walk_in_trans
      (exists_walk_in_trans
        (hR₁.1.symm.exists_walk_in (subset_union_left.trans (subset_union_left.trans
          subset_union_left)))
        (hP₁_v.exists_walk_in (subset_union_right.trans (subset_union_left.trans
          subset_union_left))))
      (exists_walk_in_trans
        ((hPA_v.mono hP_A.le).symm.exists_walk_in (subset_union_right.trans subset_union_left))
        (hR_A.1.exists_walk_in subset_union_right))
  have hwalk₂ : ∃ W₂ : GraphWalk G w_B w₄, {x | x ∈ W₂.support} ⊆ U₂ :=
    exists_walk_in_trans
      (exists_walk_in_trans
        (hR_B.1.symm.exists_walk_in (subset_union_left.trans (subset_union_left.trans
          subset_union_left)))
        ((hPB_u.mono hP_B.le).symm.exists_walk_in (subset_union_right.trans
          (subset_union_left.trans subset_union_left))))
      (exists_walk_in_trans
        (hL_u.exists_walk_in (subset_union_right.trans subset_union_left))
        (hR₄.1.exists_walk_in subset_union_right))
  refine ⟨U₁, U₂, disjoint_left.mpr fun z hz₁ hz₂ => ?_, hwalk₁, hwalk₂⟩
  -- Every vertex `z ∈ U₁` is either in `V(R₁) \ {s₁}`, `V(R_A) \ {s_A}`, or `V(P₁_v) ∪ V(PA_v)`.
  have hz₁_cases : z ∈ V(R₁) ∧ z ∉ X ∨ z ∈ V(R_A) ∧ z ∉ X ∨ z ∈ V(P₁_v) ∨ z ∈ V(PA_v) := by
    rcases hz₁ with ((hzR₁ | hzP₁v) | hzPAv) | hzRA
    · by_cases hzX : z ∈ X
      · have hzs₁ : z = s₁ := hR₁.eq_left_of_mem_X hzR₁ hzX
        exact Or.inr (Or.inr (Or.inl (hzs₁ ▸ hP₁_v.left_mem)))
      · exact Or.inl ⟨hzR₁, hzX⟩
    · exact Or.inr (Or.inr (Or.inl hzP₁v))
    · exact Or.inr (Or.inr (Or.inr hzPAv))
    · by_cases hzX : z ∈ X
      · have hzsA : z = s_A := hR_A.eq_left_of_mem_X hzRA hzX
        exact Or.inr (Or.inr (Or.inr (hzsA ▸ hPA_v.left_mem)))
      · exact Or.inr (Or.inl ⟨hzRA, hzX⟩)
  have hz₂_cases : z ∈ V(R_B) ∧ z ∉ X ∨ z ∈ V(R₄) ∧ z ∉ X ∨ z ∈ V(PB_u) ∨ z ∈ V(L_u) := by
    rcases hz₂ with ((hzRB | hzPBu) | hzLu) | hzR₄
    · by_cases hzX : z ∈ X
      · have hzsB : z = s_B := hR_B.eq_left_of_mem_X hzRB hzX
        exact Or.inr (Or.inr (Or.inl (hzsB ▸ hPB_u.right_mem)))
      · exact Or.inl ⟨hzRB, hzX⟩
    · exact Or.inr (Or.inr (Or.inl hzPBu))
    · exact Or.inr (Or.inr (Or.inr hzLu))
    · by_cases hzX : z ∈ X
      · have hzs₄ : z = s₄ := hR₄.eq_left_of_mem_X hzR₄ hzX
        exact Or.inr (Or.inr (Or.inr (hzs₄ ▸ hs₄_X)))
      · exact Or.inr (Or.inl ⟨hzR₄, hzX⟩)
  rcases hz₁_cases with ⟨hzR₁, hz_not_X⟩ | ⟨hzRA, hz_not_X⟩ | hzP₁v | hzPAv <;>
    rcases hz₂_cases with ⟨hzRB, hz_not_X₂⟩ | ⟨hzR₄, hz_not_X₂⟩ | hzPBu | hzLu
  · exact disjoint_left.mp hdisj_1B hzR₁ hzRB
  · exact disjoint_left.mp hdisj_14 hzR₁ hzR₄
  · exact hz_not_X (hX_sub (Or.inr (hPB_u_le.vertexSet_mono hzPBu)))
  · exact hz_not_X (hX_sub (Or.inl (Or.inl (hL_u_le hzLu).1)))
  · exact disjoint_left.mp hdisj_AB hzRA hzRB
  · exact disjoint_left.mp hdisj_A4 hzRA hzR₄
  · exact hz_not_X (hX_sub (Or.inr (hPB_u_le.vertexSet_mono hzPBu)))
  · exact hz_not_X (hX_sub (Or.inl (Or.inl (hL_u_le hzLu).1)))
  · exact hz_not_X₂ (hX_sub (Or.inl (Or.inl (hP₁_v_le hzP₁v).1)))
  · exact hz_not_X₂ (hX_sub (Or.inl (Or.inl (hP₁_v_le hzP₁v).1)))
  · have hz_inter : z ∈ V(P₁) ∩ V(P_B) := ⟨(hP₁_v_le hzP₁v).1, hPB_u_le.vertexSet_mono hzPBu⟩
    rw [hinter_1B, mem_insert_iff, mem_singleton_iff] at hz_inter
    rcases hz_inter with rfl | rfl
    · exact (hP₁_v_le hzP₁v).2 (by simp)
    · exact hv_not_PBu hzPBu
  · exact disjoint_left.mp hdisj_P₁ hzP₁v hzLu
  · exact hz_not_X₂ (hX_sub (Or.inl (Or.inr (hPA_v_le.vertexSet_mono hzPAv))))
  · exact hz_not_X₂ (hX_sub (Or.inl (Or.inr (hPA_v_le.vertexSet_mono hzPAv))))
  · have hz_inter : z ∈ V(P_A) ∩ V(P_B) :=
      ⟨hPA_v_le.vertexSet_mono hzPAv, hPB_u_le.vertexSet_mono hzPBu⟩
    rw [hinter_AB, mem_insert_iff, mem_singleton_iff] at hz_inter
    rcases hz_inter with rfl | rfl
    · exact hu_not_PAv hzPAv
    · exact hv_not_PBu hzPBu
  · have hz_inter : z ∈ V(P₁) ∩ V(P_A) := ⟨(hL_u_le hzLu).1, hPA_v_le.vertexSet_mono hzPAv⟩
    rw [hinter_1A, mem_insert_iff, mem_singleton_iff] at hz_inter
    rcases hz_inter with rfl | rfl
    · exact hu_not_PAv hzPAv
    · exact (hL_u_le hzLu).2 (by simp)

/-- Helper for Case A of the tripod-with-4-paths cross construction:
given `L_mid` (from `s₄` to `s₁` in `V(P₁) \ {v}`), `P₂` (from `u` to `v` with internal vertex
`s₂`), `P₃` (from `u` to `v` with internal vertex `s₃`), and disjoint `X → ΩBar` paths `R₁, R₂, R₃,
R₄`
from `s₁, s₂, s₃, s₄` to `w₁, w₂, w₃, w₄`, there exist disjoint walks in `G` between
`(w₁, w₄)` and `(w₂, w₃)`. -/
private theorem exists_disjoint_walks_pairA {G P₁ P₂ P₃ L_mid R₁ R₂ R₃ R₄ : Graph α β}
    {X Y : Set α} {u v s₁ s₂ s₃ s₄ w₁ w₂ w₃ w₄ : α}
    (hL_mid_le : V(L_mid) ⊆ V(P₁) \ {v})
    (hL_mid : IsGraphPathWithEnds G L_mid s₄ s₁)
    (hP₂ : IsGraphPathWithEnds G P₂ u v)
    (hP₃ : IsGraphPathWithEnds G P₃ u v)
    (hinter_12 : V(P₁) ∩ V(P₂) = {u, v})
    (hinter_13 : V(P₁) ∩ V(P₃) = {u, v})
    (hs₂ : s₂ ∈ V(P₂) \ {u, v})
    (hs₃ : s₃ ∈ V(P₃) \ {u, v})
    (hX_sub : V(P₁) ∪ V(P₂) ∪ V(P₃) ⊆ X)
    (hR₁ : IsFromToPathWithEnds G R₁ X Y s₁ w₁)
    (hR₂ : IsFromToPathWithEnds G R₂ X Y s₂ w₂)
    (hR₃ : IsFromToPathWithEnds G R₃ X Y s₃ w₃)
    (hR₄ : IsFromToPathWithEnds G R₄ X Y s₄ w₄)
    (hdisj_12 : Disjoint V(R₁) V(R₂))
    (hdisj_13 : Disjoint V(R₁) V(R₃))
    (hdisj_24 : Disjoint V(R₂) V(R₄))
    (hdisj_34 : Disjoint V(R₃) V(R₄)) :
    ∃ U₁ U₂ : Set α, Disjoint U₁ U₂ ∧
      (∃ W₁ : GraphWalk G w₁ w₄, {x | x ∈ W₁.support} ⊆ U₁) ∧
      (∃ W₂ : GraphWalk G w₂ w₃, {x | x ∈ W₂.support} ⊆ U₂) := by
  obtain ⟨P₂_u, P₂_v, _, hP₂_v_le, hP₂_u, hP₂_v, _, hinter_P₂, _⟩ :=
    hP₂.exists_split_at hs₂.1
  obtain ⟨P₃_u, P₃_v, _, hP₃_v_le, hP₃_u, hP₃_v, _, hinter_P₃, _⟩ :=
    hP₃.exists_split_at hs₃.1
  have hu_not_P₂v : u ∉ V(P₂_v) := by
    intro hu_in
    have : u ∈ V(P₂_u) ∩ V(P₂_v) := ⟨hP₂_u.left_mem, hu_in⟩
    rw [hinter_P₂, mem_singleton_iff] at this
    exact hs₂.2 (by simp [this])
  have hu_not_P₃v : u ∉ V(P₃_v) := by
    intro hu_in
    have : u ∈ V(P₃_u) ∩ V(P₃_v) := ⟨hP₃_u.left_mem, hu_in⟩
    rw [hinter_P₃, mem_singleton_iff] at this
    exact hs₃.2 (by simp [this])
  let U₁ : Set α := V(R₁) ∪ V(L_mid) ∪ V(R₄)
  let U₂ : Set α := V(R₂) ∪ V(P₂_v) ∪ V(P₃_v) ∪ V(R₃)
  have hwalk₁ : ∃ W₁ : GraphWalk G w₁ w₄, {x | x ∈ W₁.support} ⊆ U₁ :=
    exists_walk_in_trans
      (exists_walk_in_trans
        (hR₁.1.symm.exists_walk_in (subset_union_left.trans subset_union_left))
        (hL_mid.symm.exists_walk_in (subset_union_right.trans subset_union_left)))
      (hR₄.1.exists_walk_in subset_union_right)
  have hwalk₂ : ∃ W₂ : GraphWalk G w₂ w₃, {x | x ∈ W₂.support} ⊆ U₂ :=
    exists_walk_in_trans
      (exists_walk_in_trans
        (hR₂.1.symm.exists_walk_in (subset_union_left.trans (subset_union_left.trans
          subset_union_left)))
        ((hP₂_v.mono hP₂.le).exists_walk_in (subset_union_right.trans
          (subset_union_left.trans subset_union_left))))
      (exists_walk_in_trans
        ((hP₃_v.mono hP₃.le).symm.exists_walk_in (subset_union_right.trans subset_union_left))
        (hR₃.1.exists_walk_in subset_union_right))
  refine ⟨U₁, U₂, disjoint_left.mpr fun z hz₁ hz₂ => ?_, hwalk₁, hwalk₂⟩
  have hz₁_cases : z ∈ V(R₁) ∧ z ∉ X ∨ z ∈ V(R₄) ∧ z ∉ X ∨ z ∈ V(L_mid) := by
    rcases hz₁ with (hzR₁ | hzL) | hzR₄
    · by_cases hzX : z ∈ X
      · have hzs₁ : z = s₁ := hR₁.eq_left_of_mem_X hzR₁ hzX
        exact Or.inr (Or.inr (hzs₁ ▸ hL_mid.right_mem))
      · exact Or.inl ⟨hzR₁, hzX⟩
    · exact Or.inr (Or.inr hzL)
    · by_cases hzX : z ∈ X
      · have hzs₄ : z = s₄ := hR₄.eq_left_of_mem_X hzR₄ hzX
        exact Or.inr (Or.inr (hzs₄ ▸ hL_mid.left_mem))
      · exact Or.inr (Or.inl ⟨hzR₄, hzX⟩)
  have hz₂_cases : z ∈ V(R₂) ∧ z ∉ X ∨ z ∈ V(R₃) ∧ z ∉ X ∨ z ∈ V(P₂_v) ∨ z ∈ V(P₃_v) := by
    rcases hz₂ with ((hzR₂ | hzP₂v) | hzP₃v) | hzR₃
    · by_cases hzX : z ∈ X
      · have hzs₂ : z = s₂ := hR₂.eq_left_of_mem_X hzR₂ hzX
        exact Or.inr (Or.inr (Or.inl (hzs₂ ▸ hP₂_v.left_mem)))
      · exact Or.inl ⟨hzR₂, hzX⟩
    · exact Or.inr (Or.inr (Or.inl hzP₂v))
    · exact Or.inr (Or.inr (Or.inr hzP₃v))
    · by_cases hzX : z ∈ X
      · have hzs₃ : z = s₃ := hR₃.eq_left_of_mem_X hzR₃ hzX
        exact Or.inr (Or.inr (Or.inr (hzs₃ ▸ hP₃_v.left_mem)))
      · exact Or.inr (Or.inl ⟨hzR₃, hzX⟩)
  rcases hz₁_cases with ⟨hzR₁, hz_not_X⟩ | ⟨hzR₄, hz_not_X⟩ | hzL <;>
    rcases hz₂_cases with ⟨hzR₂, hz_not_X₂⟩ | ⟨hzR₃, hz_not_X₂⟩ | hzP₂v | hzP₃v
  · exact disjoint_left.mp hdisj_12 hzR₁ hzR₂
  · exact disjoint_left.mp hdisj_13 hzR₁ hzR₃
  · exact hz_not_X (hX_sub (Or.inl (Or.inr (hP₂_v_le.vertexSet_mono hzP₂v))))
  · exact hz_not_X (hX_sub (Or.inr (hP₃_v_le.vertexSet_mono hzP₃v)))
  · exact disjoint_left.mp hdisj_24.symm hzR₄ hzR₂
  · exact disjoint_left.mp hdisj_34.symm hzR₄ hzR₃
  · exact hz_not_X (hX_sub (Or.inl (Or.inr (hP₂_v_le.vertexSet_mono hzP₂v))))
  · exact hz_not_X (hX_sub (Or.inr (hP₃_v_le.vertexSet_mono hzP₃v)))
  · exact hz_not_X₂ (hX_sub (Or.inl (Or.inl (hL_mid_le hzL).1)))
  · exact hz_not_X₂ (hX_sub (Or.inl (Or.inl (hL_mid_le hzL).1)))
  · have hz_inter : z ∈ V(P₁) ∩ V(P₂) := ⟨(hL_mid_le hzL).1, hP₂_v_le.vertexSet_mono hzP₂v⟩
    rw [hinter_12, mem_insert_iff, mem_singleton_iff] at hz_inter
    rcases hz_inter with rfl | rfl
    · exact hu_not_P₂v hzP₂v
    · exact (hL_mid_le hzL).2 (by simp)
  · have hz_inter : z ∈ V(P₁) ∩ V(P₃) := ⟨(hL_mid_le hzL).1, hP₃_v_le.vertexSet_mono hzP₃v⟩
    rw [hinter_13, mem_insert_iff, mem_singleton_iff] at hz_inter
    rcases hz_inter with rfl | rfl
    · exact hu_not_P₃v hzP₃v
    · exact (hL_mid_le hzL).2 (by simp)

/-- Cross construction when `s₄ ∈ V(P₁_u) \ {s₁}` along the split `(P₁_u, P₁_v)` of `P₁` at `s₁`. -/
private theorem exists_cross_of_four_fromTo_in_prefix (S : Society α β)
    {P₁ P₂ P₃ P₁_u P₁_v R₁ R₂ R₃ R₄ : Graph α β} {X : Set α}
    {u v s₁ s₂ s₃ s₄ w₁ w₂ w₃ w₄ : α}
    (hP₁ : IsGraphPathWithEnds S.G P₁ u v)
    (hP₂ : IsGraphPathWithEnds S.G P₂ u v)
    (hP₃ : IsGraphPathWithEnds S.G P₃ u v)
    (hinter_12 : V(P₁) ∩ V(P₂) = {u, v})
    (hinter_13 : V(P₁) ∩ V(P₃) = {u, v})
    (hinter_23 : V(P₂) ∩ V(P₃) = {u, v})
    (hs₁ : s₁ ∈ V(P₁) \ {u, v})
    (hs₂ : s₂ ∈ V(P₂) \ {u, v})
    (hs₃ : s₃ ∈ V(P₃) \ {u, v})
    (hX_sub : V(P₁) ∪ V(P₂) ∪ V(P₃) ⊆ X)
    (hP₁_u_le : P₁_u ≤ P₁) (hP₁_v_le : P₁_v ≤ P₁)
    (hP₁_u : IsGraphPathWithEnds P₁ P₁_u u s₁)
    (hP₁_v : IsGraphPathWithEnds P₁ P₁_v s₁ v)
    (hinter_P₁ : V(P₁_u) ∩ V(P₁_v) = {s₁})
    (hs₄ : s₄ ∈ V(P₁_u) \ {s₁})
    (hR₁ : IsFromToPathWithEnds S.G R₁ X S.Ω.bar s₁ w₁)
    (hR₂ : IsFromToPathWithEnds S.G R₂ X S.Ω.bar s₂ w₂)
    (hR₃ : IsFromToPathWithEnds S.G R₃ X S.Ω.bar s₃ w₃)
    (hR₄ : IsFromToPathWithEnds S.G R₄ X S.Ω.bar s₄ w₄)
    (hdisj_12 : Disjoint V(R₁) V(R₂))
    (hdisj_13 : Disjoint V(R₁) V(R₃))
    (hdisj_14 : Disjoint V(R₁) V(R₄))
    (hdisj_23 : Disjoint V(R₂) V(R₃))
    (hdisj_24 : Disjoint V(R₂) V(R₄))
    (hdisj_34 : Disjoint V(R₃) V(R₄)) :
    ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂ := by
  obtain ⟨L_u, L_mid, hLu_le, hLmid_le, hLu, hLmid, _, hinter_L, _⟩ :=
    hP₁_u.exists_split_at hs₄.1
  have hv_not_P₁u : v ∉ V(P₁_u) := by
    intro hv_in
    have : v ∈ V(P₁_u) ∩ V(P₁_v) := ⟨hv_in, hP₁_v.right_mem⟩
    rw [hinter_P₁, mem_singleton_iff] at this
    exact hs₁.2 (by simp [this])
  have hu_not_P₁v : u ∉ V(P₁_v) := by
    intro hu_in
    have : u ∈ V(P₁_u) ∩ V(P₁_v) := ⟨hP₁_u.left_mem, hu_in⟩
    rw [hinter_P₁, mem_singleton_iff] at this
    exact hs₁.2 (by simp [this])
  have hs₁_not_Lu : s₁ ∉ V(L_u) := by
    intro hs₁_in
    have : s₁ ∈ V(L_u) ∩ V(L_mid) := ⟨hs₁_in, hLmid.right_mem⟩
    rw [hinter_L, mem_singleton_iff] at this
    exact hs₄.2 (by simp [this.symm])
  have hdisj_P₁v_Lu : Disjoint V(P₁_v) V(L_u) := by
    rw [disjoint_left]
    intro z hzv hzu
    have : z ∈ V(P₁_u) ∩ V(P₁_v) := ⟨hLu_le.vertexSet_mono hzu, hzv⟩
    rw [hinter_P₁, mem_singleton_iff] at this
    exact hs₁_not_Lu (this ▸ hzu)
  have hP₁v_sub : V(P₁_v) ⊆ V(P₁) \ {u} :=
    fun z hz => ⟨hP₁_v_le.vertexSet_mono hz, fun h => hu_not_P₁v (mem_singleton_iff.mp h ▸ hz)⟩
  have hLu_sub : V(L_u) ⊆ V(P₁) \ {v} :=
    fun z hz => ⟨(hLu_le.trans hP₁_u_le).vertexSet_mono hz,
      fun h => hv_not_P₁u (mem_singleton_iff.mp h ▸ hLu_le.vertexSet_mono hz)⟩
  have hLmid_sub : V(L_mid) ⊆ V(P₁) \ {v} :=
    fun z hz => ⟨(hLmid_le.trans hP₁_u_le).vertexSet_mono hz,
      fun h => hv_not_P₁u (mem_singleton_iff.mp h ▸ hLmid_le.vertexSet_mono hz)⟩
  have hw1 : w₁ ∈ S.Ω.bar := hR₁.right_mem_Y
  have hw2 : w₂ ∈ S.Ω.bar := hR₂.right_mem_Y
  have hw3 : w₃ ∈ S.Ω.bar := hR₃.right_mem_Y
  have hw4 : w₄ ∈ S.Ω.bar := hR₄.right_mem_Y
  have hw12 : w₁ ≠ w₂ := fun h => disjoint_left.mp hdisj_12 hR₁.1.right_mem (h ▸ hR₂.1.right_mem)
  have hw13 : w₁ ≠ w₃ := fun h => disjoint_left.mp hdisj_13 hR₁.1.right_mem (h ▸ hR₃.1.right_mem)
  have hw14 : w₁ ≠ w₄ := fun h => disjoint_left.mp hdisj_14 hR₁.1.right_mem (h ▸ hR₄.1.right_mem)
  have hw23 : w₂ ≠ w₃ := fun h => disjoint_left.mp hdisj_23 hR₂.1.right_mem (h ▸ hR₃.1.right_mem)
  have hw24 : w₂ ≠ w₄ := fun h => disjoint_left.mp hdisj_24 hR₂.1.right_mem (h ▸ hR₄.1.right_mem)
  have hw34 : w₃ ≠ w₄ := fun h => disjoint_left.mp hdisj_34 hR₃.1.right_mem (h ▸ hR₄.1.right_mem)
  rcases S.Ω.crosses_of_four_distinct hw1 hw2 hw3 hw4 hw12 hw13 hw14 hw23 hw24 hw34 with
    hcA | hcB | hcC
  · obtain ⟨U₁, U₂, hdisjU, hW₁, hW₂⟩ :=
      exists_disjoint_walks_pairA hLmid_sub (hLmid.mono (hP₁_u_le.trans hP₁.le)) hP₂ hP₃
        hinter_12 hinter_13 hs₂ hs₃ hX_sub hR₁ hR₂ hR₃ hR₄
        hdisj_12 hdisj_13 hdisj_24 hdisj_34
    exact S.exists_isCross_of_disjoint_walks hw1 hw4 hw2 hw3 hcA hdisjU hW₁ hW₂
  · obtain ⟨U₁, U₂, hdisjU, hW₁, hW₂⟩ :=
      exists_disjoint_walks_pairBC hP₁v_sub hLu_sub hdisj_P₁v_Lu
        (hP₁_v.mono hP₁.le) (hLu.mono (hP₁_u_le.trans hP₁.le)) hP₂ hP₃
        hinter_12 hinter_13 hinter_23 hs₂ hs₃ hX_sub hs₁ hLu.right_mem
        hR₁ hR₂ hR₃ hR₄ hdisj_13 hdisj_14 hdisj_23 hdisj_24
    exact S.exists_isCross_of_disjoint_walks hw1 hw2 hw3 hw4 hcB hdisjU hW₁ hW₂
  · have hX_sub' : V(P₁) ∪ V(P₃) ∪ V(P₂) ⊆ X := by
      intro z hz
      rcases hz with (hz1 | hz3) | hz2
      · exact hX_sub (Or.inl (Or.inl hz1))
      · exact hX_sub (Or.inr hz3)
      · exact hX_sub (Or.inl (Or.inr hz2))
    obtain ⟨U₁, U₂, hdisjU, hW₁, hW₂⟩ :=
      exists_disjoint_walks_pairBC hP₁v_sub hLu_sub hdisj_P₁v_Lu
        (hP₁_v.mono hP₁.le) (hLu.mono (hP₁_u_le.trans hP₁.le)) hP₃ hP₂
        hinter_13 hinter_12 (inter_comm V(P₃) V(P₂) ▸ hinter_23) hs₃ hs₂ hX_sub' hs₁ hLu.right_mem
        hR₁ hR₃ hR₂ hR₄ hdisj_12 hdisj_14 hdisj_23.symm hdisj_34
    exact S.exists_isCross_of_disjoint_walks hw1 hw3 hw2 hw4 hcC hdisjU hW₁ hW₂

/-- Cross construction when `s₄ ∈ V(P₁) \ {s₁}`. -/
private theorem exists_cross_of_four_fromTo_in_P₁ (S : Society α β)
    {P₁ P₂ P₃ R₁ R₂ R₃ R₄ : Graph α β} {X : Set α}
    {u v s₁ s₂ s₃ s₄ w₁ w₂ w₃ w₄ : α}
    (hP₁ : IsGraphPathWithEnds S.G P₁ u v)
    (hP₂ : IsGraphPathWithEnds S.G P₂ u v)
    (hP₃ : IsGraphPathWithEnds S.G P₃ u v)
    (hinter_12 : V(P₁) ∩ V(P₂) = {u, v})
    (hinter_13 : V(P₁) ∩ V(P₃) = {u, v})
    (hinter_23 : V(P₂) ∩ V(P₃) = {u, v})
    (hs₁ : s₁ ∈ V(P₁) \ {u, v})
    (hs₂ : s₂ ∈ V(P₂) \ {u, v})
    (hs₃ : s₃ ∈ V(P₃) \ {u, v})
    (hX_sub : V(P₁) ∪ V(P₂) ∪ V(P₃) ⊆ X)
    (hs₄ : s₄ ∈ V(P₁) \ {s₁})
    (hR₁ : IsFromToPathWithEnds S.G R₁ X S.Ω.bar s₁ w₁)
    (hR₂ : IsFromToPathWithEnds S.G R₂ X S.Ω.bar s₂ w₂)
    (hR₃ : IsFromToPathWithEnds S.G R₃ X S.Ω.bar s₃ w₃)
    (hR₄ : IsFromToPathWithEnds S.G R₄ X S.Ω.bar s₄ w₄)
    (hdisj_12 : Disjoint V(R₁) V(R₂))
    (hdisj_13 : Disjoint V(R₁) V(R₃))
    (hdisj_14 : Disjoint V(R₁) V(R₄))
    (hdisj_23 : Disjoint V(R₂) V(R₃))
    (hdisj_24 : Disjoint V(R₂) V(R₄))
    (hdisj_34 : Disjoint V(R₃) V(R₄)) :
    ∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂ := by
  obtain ⟨P₁_u, P₁_v, hP₁_u_le, hP₁_v_le, hP₁_u, hP₁_v, hP₁_union, hinter_P₁, _⟩ :=
    hP₁.exists_split_at hs₁.1
  have hs₄_union : s₄ ∈ V(P₁_u) ∪ V(P₁_v) := by
    rw [← vertexSet_subgraphUnion P₁ P₁_u P₁_v, hP₁_union]
    exact hs₄.1
  rcases hs₄_union with hs₄_u | hs₄_v
  · exact exists_cross_of_four_fromTo_in_prefix S hP₁ hP₂ hP₃ hinter_12 hinter_13 hinter_23
      hs₁ hs₂ hs₃ hX_sub hP₁_u_le hP₁_v_le hP₁_u hP₁_v hinter_P₁ ⟨hs₄_u, hs₄.2⟩
      hR₁ hR₂ hR₃ hR₄ hdisj_12 hdisj_13 hdisj_14 hdisj_23 hdisj_24 hdisj_34
  · -- Swap `u` and `v` using `.symm`.
    have hvu : ({v, u} : Set α) = {u, v} := pair_comm v u
    exact exists_cross_of_four_fromTo_in_prefix S hP₁.symm hP₂.symm hP₃.symm
      (hvu ▸ hinter_12) (hvu ▸ hinter_13) (hvu ▸ hinter_23)
      (hvu ▸ hs₁) (hvu ▸ hs₂) (hvu ▸ hs₃) hX_sub
      hP₁_v_le hP₁_u_le hP₁_v.symm hP₁_u.symm
      (inter_comm V(P₁_v) V(P₁_u) ▸ hinter_P₁) ⟨hs₄_v, hs₄.2⟩
      hR₁ hR₂ hR₃ hR₄ hdisj_12 hdisj_13 hdisj_14 hdisj_23 hdisj_24 hdisj_34

/-- **Graph Minors IX, (2.3)** (pages 44–45):
"Suppose that $\{P_1, P_2, P_3\}$ is a tripod in $(G, \Omega)$. Then either $(G, \Omega)$ ... has a
cross, or there is an internal 3-separation $(G_1, G_2)$ of $(G, \Omega)$ with
$P_1 \cup P_2 \cup P_3 \subseteq G_1$." -/
theorem theorem_2_3_proof (S : Society α β) {P₁ P₂ P₃ : Graph α β}
    (htripod : S.IsTripod P₁ P₂ P₃) :
    (∃ Q₁ Q₂ : Graph α β, S.IsCross Q₁ Q₂) ∨
    (∃ G₁ G₂ : Graph α β, S.IsInternalKSeparation 3 G₁ G₂ ∧
      subgraphUnion S.G (subgraphUnion S.G P₁ P₂) P₃ ≤ G₁) := by
  classical
  have : Finite V(S.G) := S.finite_V.to_subtype
  rcases htripod with ⟨u, v, huv, hP₁, hP₂, hP₃, hinter_12, hinter_13, hinter_23,
    s₁, hs₁, s₂, hs₂, s₃, hs₃, t₁, _, t₂, _, t₃, _, hred₃⟩
  let X : Set α := V(P₁) ∪ V(P₂) ∪ V(P₃)
  have hX_sub_G : X ⊆ V(S.G) :=
    union_subset (union_subset hP₁.le.vertexSet_mono hP₂.le.vertexSet_mono) hP₃.le.vertexSet_mono
  have hs12 : s₁ ≠ s₂ := by
    intro h
    have : s₁ ∈ V(P₁) ∩ V(P₂) := ⟨hs₁.1, h ▸ hs₂.1⟩
    rw [hinter_12] at this
    exact hs₁.2 this
  have hs13 : s₁ ≠ s₃ := by
    intro h
    have : s₁ ∈ V(P₁) ∩ V(P₃) := ⟨hs₁.1, h ▸ hs₃.1⟩
    rw [hinter_13] at this
    exact hs₁.2 this
  have hs23 : s₂ ≠ s₃ := by
    intro h
    have : s₂ ∈ V(P₂) ∩ V(P₃) := ⟨hs₂.1, h ▸ hs₃.1⟩
    rw [hinter_23] at this
    exact hs₂.2 this
  have hcard_s : ({s₁, s₂, s₃} : Set α).ncard = 3 := by
    rw [ncard_insert_of_notMem (by simp [hs12, hs13]), ncard_pair hs23]
  -- Apply Menger's theorem with `k = 4` between `X = V(P₁) ∪ V(P₂) ∪ V(P₃)` and `S.Ω.bar`.
  rcases exists_fromToPaths_or_graphSeparation hX_sub_G S.bar_subset 4 with hpaths4 | hsep3
  · -- Case 1: There exist 4 mutually disjoint `X → ΩBar` paths in `S.G`.
    left
    obtain ⟨X'', Y'', hX''_X, hY''_bar, hs_sub_X'', _, hX''_card, hY''_card, hred₄⟩ :=
      theorem_2_2_proof hX_sub_G S.bar_subset hpaths4 hred₃.1 hred₃.2.1 hred₃.2.2.1
        (by omega) hred₃
    have hX''_fin : X''.Finite := S.finite_V.subset (hX''_X.trans hX_sub_G)
    have hY''_fin : Y''.Finite := S.finite_V.subset (hY''_bar.trans S.bar_subset)
    obtain ⟨Q, x, y, hdisjQ, hQ, hx_range, _⟩ :=
      exists_indexed_of_redirectsTo hX''_fin hY''_fin hred₄ hX''_card
    obtain ⟨hx_inj, _, _, _, _⟩ := redirectsTo_of_disjoint_fromToPaths hdisjQ hQ
    have hs₁_in : s₁ ∈ range x := hx_range ▸ hs_sub_X'' (by simp)
    have hs₂_in : s₂ ∈ range x := hx_range ▸ hs_sub_X'' (by simp)
    have hs₃_in : s₃ ∈ range x := hx_range ▸ hs_sub_X'' (by simp)
    obtain ⟨i₁, hi₁⟩ := hs₁_in
    obtain ⟨i₂, hi₂⟩ := hs₂_in
    obtain ⟨i₃, hi₃⟩ := hs₃_in
    have hi12 : i₁ ≠ i₂ := fun h => hs12 (hi₁ ▸ hi₂ ▸ congrArg x h)
    have hi13 : i₁ ≠ i₃ := fun h => hs13 (hi₁ ▸ hi₃ ▸ congrArg x h)
    have hi23 : i₂ ≠ i₃ := fun h => hs23 (hi₂ ▸ hi₃ ▸ congrArg x h)
    have hex_i₄ : ∃ i₄ : Fin 4, i₄ ≠ i₁ ∧ i₄ ≠ i₂ ∧ i₄ ≠ i₃ := by
      have hcard3 : ({i₁, i₂, i₃} : Finset (Fin 4)).card ≤ 3 := by
        calc ({i₁, i₂, i₃} : Finset (Fin 4)).card
          _ ≤ ({i₂, i₃} : Finset (Fin 4)).card + 1 := Finset.card_insert_le _ _
          _ ≤ ({i₃} : Finset (Fin 4)).card + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
          _ = 3 := by simp
      have hlt : ({i₁, i₂, i₃} : Finset (Fin 4)).card < (Finset.univ : Finset (Fin 4)).card := by
        simp; omega
      obtain ⟨i₄, _, hi₄_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi₄_not
      exact ⟨i₄, hi₄_not.1, hi₄_not.2.1, hi₄_not.2.2⟩
    obtain ⟨i₄, hi41, hi42, hi43⟩ := hex_i₄
    have hs₄_not : x i₄ ∉ ({s₁, s₂, s₃} : Set α) := by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨fun h => hi41 (hx_inj (h.trans hi₁.symm)),
        fun h => hi42 (hx_inj (h.trans hi₂.symm)),
        fun h => hi43 (hx_inj (h.trans hi₃.symm))⟩
    have hs₄_X : x i₄ ∈ X := (hQ i₄).left_mem_X
    have hR₁ : IsFromToPathWithEnds S.G (Q i₁) X S.Ω.bar s₁ (y i₁) := hi₁ ▸ hQ i₁
    have hR₂ : IsFromToPathWithEnds S.G (Q i₂) X S.Ω.bar s₂ (y i₂) := hi₂ ▸ hQ i₂
    have hR₃ : IsFromToPathWithEnds S.G (Q i₃) X S.Ω.bar s₃ (y i₃) := hi₃ ▸ hQ i₃
    have hR₄ : IsFromToPathWithEnds S.G (Q i₄) X S.Ω.bar (x i₄) (y i₄) := hQ i₄
    rcases hs₄_X with (hs₄_P₁ | hs₄_P₂) | hs₄_P₃
    · exact exists_cross_of_four_fromTo_in_P₁ S hP₁ hP₂ hP₃ hinter_12 hinter_13 hinter_23
        hs₁ hs₂ hs₃ subset_rfl
        ⟨hs₄_P₁, fun h => hs₄_not (by simp [mem_singleton_iff.mp h])⟩
        hR₁ hR₂ hR₃ hR₄
        (hdisjQ hi12) (hdisjQ hi13) (hdisjQ hi41.symm)
        (hdisjQ hi23) (hdisjQ hi42.symm) (hdisjQ hi43.symm)
    · have hX_213 : V(P₂) ∪ V(P₁) ∪ V(P₃) ⊆ X := by
        intro z hz
        rcases hz with (hz2 | hz1) | hz3
        · exact Or.inl (Or.inr hz2)
        · exact Or.inl (Or.inl hz1)
        · exact Or.inr hz3
      exact exists_cross_of_four_fromTo_in_P₁ S hP₂ hP₁ hP₃
        (inter_comm V(P₂) V(P₁) ▸ hinter_12) hinter_23 hinter_13
        hs₂ hs₁ hs₃ hX_213
        ⟨hs₄_P₂, fun h => hs₄_not (by simp [mem_singleton_iff.mp h])⟩
        hR₂ hR₁ hR₃ hR₄
        (hdisjQ hi12.symm) (hdisjQ hi23) (hdisjQ hi42.symm)
        (hdisjQ hi13) (hdisjQ hi41.symm) (hdisjQ hi43.symm)
    · have hX_312 : V(P₃) ∪ V(P₁) ∪ V(P₂) ⊆ X := by
        intro z hz
        rcases hz with (hz3 | hz1) | hz2
        · exact Or.inr hz3
        · exact Or.inl (Or.inl hz1)
        · exact Or.inl (Or.inr hz2)
      exact exists_cross_of_four_fromTo_in_P₁ S hP₃ hP₁ hP₂
        (inter_comm V(P₃) V(P₁) ▸ hinter_13) (inter_comm V(P₃) V(P₂) ▸ hinter_23) hinter_12
        hs₃ hs₁ hs₂ hX_312
        ⟨hs₄_P₃, fun h => hs₄_not (by simp [mem_singleton_iff.mp h])⟩
        hR₃ hR₁ hR₂ hR₄
        (hdisjQ hi13.symm) (hdisjQ hi23.symm) (hdisjQ hi43.symm)
        (hdisjQ hi12) (hdisjQ hi41.symm) (hdisjQ hi42.symm)
  · -- Case 2: There is a separation `(G₁, G₂)` of `S` with `X ⊆ V(G₁)` and `|V(G₁ ∩ G₂)| ≤ 3`.
    right
    obtain ⟨G₁, G₂, hsep, hG₁_ind, hX_G₁, hbar_G₂, hinter_lt⟩ := hsep3
    have h5_sub : ({u, v, s₁, s₂, s₃} : Set α) ⊆ V(G₁) := by
      rintro z (rfl | rfl | rfl | rfl | rfl)
      · exact hX_G₁ (Or.inl (Or.inl hP₁.left_mem))
      · exact hX_G₁ (Or.inl (Or.inl hP₁.right_mem))
      · exact hX_G₁ (Or.inl (Or.inl hs₁.1))
      · exact hX_G₁ (Or.inl (Or.inr hs₂.1))
      · exact hX_G₁ (Or.inr hs₃.1)
    have h5_card : ({u, v, s₁, s₂, s₃} : Set α).ncard = 5 := by
      have hu_not : u ∉ ({v, s₁, s₂, s₃} : Set α) := by
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨huv, fun h => hs₁.2 (by simp [h.symm]),
          fun h => hs₂.2 (by simp [h.symm]), fun h => hs₃.2 (by simp [h.symm])⟩
      have hv_not : v ∉ ({s₁, s₂, s₃} : Set α) := by
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨fun h => hs₁.2 (by simp [h.symm]),
          fun h => hs₂.2 (by simp [h.symm]), fun h => hs₃.2 (by simp [h.symm])⟩
      rw [ncard_insert_of_notMem hu_not, ncard_insert_of_notMem hv_not, hcard_s]
    have hV₁_ge_5 : 5 ≤ V(G₁).ncard := by
      rw [← h5_card]
      exact ncard_le_ncard h5_sub (S.finite_V.subset hsep.1.vertexSet_mono)
    have hfin₁ : V(G₁).Finite := S.finite_V.subset hsep.1.vertexSet_mono
    have hfin₂ : V(G₂).Finite := S.finite_V.subset hsep.2.1.vertexSet_mono
    have hunion_inter := ncard_union_add_ncard_inter V(G₁) V(G₂) hfin₁ hfin₂
    rw [hsep.2.2.1] at hunion_inter
    have hV₂_add_2 : V(G₂).ncard + 2 ≤ V(S.G).ncard := by omega
    have hV₂_ne : V(G₂) ≠ V(S.G) := by
      intro heq
      rw [heq] at hV₂_add_2
      omega
    have hint_sep : S.IsInternalKSeparation 3 G₁ G₂ :=
      ⟨⟨⟨hsep, hbar_G₂⟩, by omega, hV₂_ne⟩, hV₂_add_2⟩
    have hle_G₁ : ∀ {H : Graph α β}, H ≤ S.G → V(H) ⊆ V(G₁) → H ≤ G₁ := by
      intro H hHG hVH
      rw [hG₁_ind]
      refine ⟨hVH, fun e x y hxy => ?_⟩
      rw [induce_isLink]
      exact ⟨hxy.mono hHG, hVH hxy.left_mem, hVH hxy.right_mem⟩
    have h12_le : subgraphUnion S.G P₁ P₂ ≤ S.G := subgraphUnion_le hP₁.le hP₂.le
    have h123_le : subgraphUnion S.G (subgraphUnion S.G P₁ P₂) P₃ ≤ S.G :=
      subgraphUnion_le h12_le hP₃.le
    refine ⟨G₁, G₂, hint_sep, hle_G₁ h123_le ?_⟩
    rw [vertexSet_subgraphUnion, vertexSet_subgraphUnion]
    exact hX_G₁

end GraphMinor.GM09
