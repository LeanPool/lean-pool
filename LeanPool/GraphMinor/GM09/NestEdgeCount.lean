/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Basic

/-!
# Edge minimization for nest uncrossing

These graph lemmas establish the three moves in the proof of Graph Minors III, (4.1),
pages 60–61. The drawing versions use the vertex and edge sets of the associated graphs.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Graph

universe u v

variable {α : Type u} {β : Type v}

/-- If `C, D ≤ G` are vertex-disjoint subgraphs of `G`, then their edge sets are disjoint. -/
theorem disjoint_edgeSet_of_disjoint_vertexSet {G C D : Graph α β}
    (hC : C ≤ G) (hD : D ≤ G) (hV : Disjoint V(C) V(D)) :
    Disjoint E(C) E(D) := by
  refine disjoint_left.mpr fun e heC heD => ?_
  obtain ⟨x, y, hxyC⟩ := C.exists_isLink_of_mem_edgeSet heC
  have hxyG : G.IsLink e x y := hxyC.mono hC
  have hxyD : D.IsLink e x y := (hD.isLink_iff heD).mpr hxyG
  exact disjoint_left.mp hV hxyC.left_mem hxyD.left_mem

/-- The set of all edges in `C₁ ∪ ⋯ ∪ C_s ∪ P₁ ∪ ⋯ ∪ P_r`. -/
def totalUnionEdgeSet {s r : ℕ} (C : Fin s → Graph α β) (P : Fin r → Graph α β) : Set β :=
  (⋃ j : Fin s, E(C j)) ∪ (⋃ i : Fin r, E(P i))

/-- The total number of edges `|E(C₁ ∪ ⋯ ∪ C_s ∪ P₁ ∪ ⋯ ∪ P_r)|` minimized in `(1)` of the proof of
Graph Minors III, (4.1) (page 60). -/
noncomputable def totalUnionEdges {s r : ℕ} (C : Fin s → Graph α β) (P : Fin r → Graph α β) : ℕ :=
  (totalUnionEdgeSet C P).ncard

theorem totalUnionEdgeSet_subset_edgeSet {s r : ℕ} {G : Graph α β}
    {C : Fin s → Graph α β} {P : Fin r → Graph α β}
    (hCG : ∀ j, C j ≤ G) (hPG : ∀ i, P i ≤ G) :
    totalUnionEdgeSet C P ⊆ E(G) :=
  union_subset (iUnion_subset fun j => (hCG j).edgeSet_mono)
    (iUnion_subset fun i => (hPG i).edgeSet_mono)

theorem totalUnionEdgeSet_finite {s r : ℕ} {G : Graph α β} (hfin : E(G).Finite)
    {C : Fin s → Graph α β} {P : Fin r → Graph α β}
    (hCG : ∀ j, C j ≤ G) (hPG : ∀ i, P i ≤ G) :
    (totalUnionEdgeSet C P).Finite :=
  hfin.subset (totalUnionEdgeSet_subset_edgeSet hCG hPG)

/-- Condition `(1)` of the proof of Graph Minors III, (4.1) (page 60):
"Choose $C_1, \dots, C_s, P_1, \dots, P_r$ with $$ |E(C_1 \cup \cdots \cup C_s \cup P_1 \cup
\cdots \cup P_r)| \text{ minimum.}" -/
theorem exists_min_totalUnionEdges {s r : ℕ}
    (IsValidPair : (Fin s → Graph α β) → (Fin r → Graph α β) → Prop)
    (hex : ∃ C₀ P₀, IsValidPair C₀ P₀) :
    ∃ C P, IsValidPair C P ∧
      ∀ C' P', IsValidPair C' P' → totalUnionEdges C P ≤ totalUnionEdges C' P' := by
  classical
  obtain ⟨C₀, P₀, h₀⟩ := hex
  have hne : {n : ℕ | ∃ C P, IsValidPair C P ∧ totalUnionEdges C P = n}.Nonempty :=
    ⟨totalUnionEdges C₀ P₀, C₀, P₀, h₀, rfl⟩
  obtain ⟨C, P, hCP, hmin⟩ := Nat.sInf_mem hne
  refine ⟨C, P, hCP, fun C' P' h' => ?_⟩
  rw [hmin]
  exact Nat.sInf_le ⟨C', P', h', rfl⟩

/-- **Move 1 (Boundary shortening move, GM03 (4.1) paragraph 2, page 60)**:
Replacing `P i` by a subpath `P'_i ≤ P i` that omits an edge `e ∈ E(P i)` not lying in any `E(C j)`
strictly decreases `totalUnionEdges C P`. -/
theorem totalUnionEdges_lt_of_replace_subpath {s r : ℕ} [DecidableEq (Fin r)] {G : Graph α β}
    (hfin : E(G).Finite)
    {C : Fin s → Graph α β} {P : Fin r → Graph α β}
    (hCG : ∀ j, C j ≤ G) (hPG : ∀ k, P k ≤ G)
    (hP_disj : Pairwise (fun k₁ k₂ => Disjoint V(P k₁) V(P k₂)))
    {i : Fin r} {P'_i : Graph α β} (hP'_le : P'_i ≤ P i)
    {e : β} (he_Pi : e ∈ E(P i)) (he_not_P' : e ∉ E(P'_i))
    (he_not_C : ∀ j : Fin s, e ∉ E(C j)) :
    totalUnionEdges C (Function.update P i P'_i) < totalUnionEdges C P := by
  have hsub : totalUnionEdgeSet C (Function.update P i P'_i) ⊆ totalUnionEdgeSet C P := by
    rintro f (hfC | hfP)
    · exact Or.inl hfC
    · obtain ⟨k, hfk⟩ := mem_iUnion.mp hfP
      by_cases hki : k = i
      · subst hki
        rw [Function.update_self] at hfk
        exact Or.inr (mem_iUnion.mpr ⟨k, hP'_le.edgeSet_mono hfk⟩)
      · rw [Function.update_of_ne hki] at hfk
        exact Or.inr (mem_iUnion.mpr ⟨k, hfk⟩)
  have he_in : e ∈ totalUnionEdgeSet C P :=
    Or.inr (mem_iUnion.mpr ⟨i, he_Pi⟩)
  have he_not_in : e ∉ totalUnionEdgeSet C (Function.update P i P'_i) := by
    rintro (heC | heP)
    · obtain ⟨j, hej⟩ := mem_iUnion.mp heC
      exact he_not_C j hej
    · obtain ⟨k, hek⟩ := mem_iUnion.mp heP
      by_cases hki : k = i
      · subst hki
        rw [Function.update_self] at hek
        exact he_not_P' hek
      · rw [Function.update_of_ne hki] at hek
        have hdisjE := disjoint_edgeSet_of_disjoint_vertexSet (hPG i) (hPG k) (hP_disj
          (Ne.symm hki))
        exact disjoint_left.mp hdisjE he_Pi hek
  exact Set.ncard_lt_ncard ⟨hsub, fun h => he_not_in (h he_in)⟩
    (totalUnionEdgeSet_finite hfin hCG hPG)

/-- **Move 2 (Outer detour move, GM03 (4.1) paragraph 4, page 60)**:
If `P_sub ≤ P i` and `C j = Q₁ ∪ Q₂` where `Q₁, Q₂ ≤ C j` are edge-disjoint and `Q₂` contains an
edge `e₀` not in any `E(P k)`, then replacing `C j` by `subgraphUnion G P_sub Q₁` strictly decreases
`totalUnionEdges C P`. -/
theorem totalUnionEdges_lt_of_replace_circuit {s r : ℕ} [DecidableEq (Fin s)] {G : Graph α β}
    (hfin : E(G).Finite)
    {C : Fin s → Graph α β} {P : Fin r → Graph α β}
    (hCG : ∀ m, C m ≤ G) (hPG : ∀ k, P k ≤ G)
    (hC_disj : Pairwise (fun m₁ m₂ => Disjoint V(C m₁) V(C m₂)))
    {j : Fin s} {i : Fin r} {P_sub Q₁ Q₂ : Graph α β}
    (hP_sub : P_sub ≤ P i) (hQ₁ : Q₁ ≤ C j) (hQ₂ : Q₂ ≤ C j)
    (hQ_disj : Disjoint E(Q₁) E(Q₂))
    {e₀ : β} (he₀_Q₂ : e₀ ∈ E(Q₂)) (he₀_not_P : ∀ k : Fin r, e₀ ∉ E(P k)) :
    totalUnionEdges (Function.update C j (subgraphUnion G P_sub Q₁)) P <
      totalUnionEdges C P := by
  have hP_sub_G : P_sub ≤ G := hP_sub.trans (hPG i)
  have hQ₁_G : Q₁ ≤ G := hQ₁.trans (hCG j)
  have he₀_Cj : e₀ ∈ E(C j) := hQ₂.edgeSet_mono he₀_Q₂
  have hsub : totalUnionEdgeSet (Function.update C j (subgraphUnion G P_sub Q₁)) P ⊆
      totalUnionEdgeSet C P := by
    rintro f (hfC | hfP)
    · obtain ⟨m, hfm⟩ := mem_iUnion.mp hfC
      by_cases hmj : m = j
      · subst hmj
        rw [Function.update_self, edgeSet_subgraphUnion hP_sub_G hQ₁_G] at hfm
        rcases hfm with hfm_P | hfm_Q₁
        · exact Or.inr (mem_iUnion.mpr ⟨i, hP_sub.edgeSet_mono hfm_P⟩)
        · exact Or.inl (mem_iUnion.mpr ⟨m, hQ₁.edgeSet_mono hfm_Q₁⟩)
      · rw [Function.update_of_ne hmj] at hfm
        exact Or.inl (mem_iUnion.mpr ⟨m, hfm⟩)
    · exact Or.inr hfP
  have he₀_in : e₀ ∈ totalUnionEdgeSet C P :=
    Or.inl (mem_iUnion.mpr ⟨j, he₀_Cj⟩)
  have he₀_not_in :
      e₀ ∉ totalUnionEdgeSet (Function.update C j (subgraphUnion G P_sub Q₁)) P := by
    rintro (heC | heP)
    · obtain ⟨m, hem⟩ := mem_iUnion.mp heC
      by_cases hmj : m = j
      · subst hmj
        rw [Function.update_self, edgeSet_subgraphUnion hP_sub_G hQ₁_G] at hem
        rcases hem with hem_P | hem_Q₁
        · exact he₀_not_P i (hP_sub.edgeSet_mono hem_P)
        · exact disjoint_left.mp hQ_disj hem_Q₁ he₀_Q₂
      · rw [Function.update_of_ne hmj] at hem
        have hdisjE := disjoint_edgeSet_of_disjoint_vertexSet (hCG j) (hCG m) (hC_disj
          (Ne.symm hmj))
        exact disjoint_left.mp hdisjE he₀_Cj hem
    · obtain ⟨k, hek⟩ := mem_iUnion.mp heP
      exact he₀_not_P k hek
  exact Set.ncard_lt_ncard ⟨hsub, fun h => he₀_not_in (h he₀_in)⟩
    (totalUnionEdgeSet_finite hfin hCG hPG)

/-- **Move 3 (Inner detour move, GM03 (4.1) paragraph 6, page 61)**:
If `P_sub ≤ P i`, `Q_k ≤ C j`, and `P'_i` is a rerouted path with `V(P'_i) ⊆ V(P i) ∪ V(Q_k)` and
`E(P'_i) ⊆ (E(P i) \ E(P_sub)) ∪ E(Q_k)`, where `V(Q_k)` is disjoint from `V(P i')` for all
`i' ≠ i`, and `e₁ ∈ E(P_sub)` lies in no `E(C m)`, then `Function.update P i P'_i` is pairwise
vertex-disjoint and strictly decreases `totalUnionEdges C P`. -/
theorem totalUnionEdges_lt_of_reroute_path {s r : ℕ} [DecidableEq (Fin r)] {G : Graph α β}
    (hfin : E(G).Finite)
    {C : Fin s → Graph α β} {P : Fin r → Graph α β}
    (hCG : ∀ m, C m ≤ G) (hPG : ∀ k, P k ≤ G)
    (hP_disj : Pairwise (fun k₁ k₂ => Disjoint V(P k₁) V(P k₂)))
    {j : Fin s} {i : Fin r} {P_sub Q_k P'_i : Graph α β}
    (hP_sub : P_sub ≤ P i) (hQ_k : Q_k ≤ C j)
    (hP'_V : V(P'_i) ⊆ V(P i) ∪ V(Q_k))
    (hP'_E : E(P'_i) ⊆ (E(P i) \ E(P_sub)) ∪ E(Q_k))
    (hQ_disj_other : ∀ i' : Fin r, i' ≠ i → Disjoint V(Q_k) V(P i'))
    {e₁ : β} (he₁_sub : e₁ ∈ E(P_sub)) (he₁_not_C : ∀ m : Fin s, e₁ ∉ E(C m)) :
    Pairwise (fun k₁ k₂ => Disjoint V(Function.update P i P'_i k₁) V(Function.update P i P'_i k₂)) ∧
      totalUnionEdges C (Function.update P i P'_i) < totalUnionEdges C P := by
  refine ⟨?_, ?_⟩
  · intro k₁ k₂ hk₁₂
    by_cases hk₁ : k₁ = i
    · subst hk₁
      have hk₂ : k₂ ≠ k₁ := hk₁₂.symm
      rw [Function.update_self, Function.update_of_ne hk₂]
      exact disjoint_of_subset_left hP'_V
        (disjoint_union_left.mpr ⟨hP_disj hk₁₂, hQ_disj_other k₂ hk₂⟩)
    · by_cases hk₂ : k₂ = i
      · subst hk₂
        rw [Function.update_of_ne hk₁, Function.update_self]
        exact disjoint_of_subset_right hP'_V
          (disjoint_union_right.mpr ⟨hP_disj hk₁₂, (hQ_disj_other k₁ hk₁).symm⟩)
      · rw [Function.update_of_ne hk₁, Function.update_of_ne hk₂]
        exact hP_disj hk₁₂
  · have he₁_Pi : e₁ ∈ E(P i) := hP_sub.edgeSet_mono he₁_sub
    have hsub : totalUnionEdgeSet C (Function.update P i P'_i) ⊆ totalUnionEdgeSet C P := by
      rintro f (hfC | hfP)
      · exact Or.inl hfC
      · obtain ⟨k, hfk⟩ := mem_iUnion.mp hfP
        by_cases hki : k = i
        · subst hki
          rw [Function.update_self] at hfk
          rcases hP'_E hfk with ⟨hfPi, _⟩ | hfQ
          · exact Or.inr (mem_iUnion.mpr ⟨k, hfPi⟩)
          · exact Or.inl (mem_iUnion.mpr ⟨j, hQ_k.edgeSet_mono hfQ⟩)
        · rw [Function.update_of_ne hki] at hfk
          exact Or.inr (mem_iUnion.mpr ⟨k, hfk⟩)
    have he₁_in : e₁ ∈ totalUnionEdgeSet C P :=
      Or.inr (mem_iUnion.mpr ⟨i, he₁_Pi⟩)
    have he₁_not_in : e₁ ∉ totalUnionEdgeSet C (Function.update P i P'_i) := by
      rintro (heC | heP)
      · obtain ⟨m, hem⟩ := mem_iUnion.mp heC
        exact he₁_not_C m hem
      · obtain ⟨k, hek⟩ := mem_iUnion.mp heP
        by_cases hki : k = i
        · subst hki
          rw [Function.update_self] at hek
          rcases hP'_E hek with ⟨_, he_not_sub⟩ | heQ
          · exact he_not_sub he₁_sub
          · exact he₁_not_C j (hQ_k.edgeSet_mono heQ)
        · rw [Function.update_of_ne hki] at hek
          have hdisjE := disjoint_edgeSet_of_disjoint_vertexSet (hPG i) (hPG k)
            (hP_disj (Ne.symm hki))
          exact disjoint_left.mp hdisjE he₁_Pi hek
    exact Set.ncard_lt_ncard ⟨hsub, fun h => he₁_not_in (h he₁_in)⟩
      (totalUnionEdgeSet_finite hfin hCG hPG)

end GraphMinor.GM09
