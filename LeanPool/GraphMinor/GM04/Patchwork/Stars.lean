/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Axioms
public import LeanPool.GraphMinor.GM04.Patchwork.Expansion
import LeanPool.GraphMinor.GM04.Patchwork.Menger

/-!
# Stars with small hearts: gluing and star-decomposition simulation (Graph Minors IV, Section 8)

This file formalizes Graph Minors IV, (8.1) and (8.2) (pages 247–249):

* `glueVertex` and `glueEdge`: the glued expansion `η` across separations `(G₁, G₂)` of `G` and
  `(G'₁, G'₂)` of `G'`.
* `lemma_8_1_claim_1`, `lemma_8_1_claim_2`, and `theorem_8_1`: Graph Minors IV, (8.1), showing that
  `η` is a realizable expansion of `P` in `P'`.
* `theorem_8_2`: Graph Minors IV, (8.2), showing that simulation of tips along a star-decomposition
  together with a root isomorphism `γ` and edge injection `α` gives simulation of `P` in `P'`.
-/

public section

namespace GraphMinor.GM04

open SimpleGraph Hypergraph

universe u v w

variable {Ω : Type w} [Preorder Ω] {α α' β β' ι ι' : Type*}

/-! ### Basic properties of separations and patchwork restrictions -/

theorem isSeparation_disjoint_edgeSet {G G₁ G₂ : Hypergraph α β}
    (hsep : G.IsSeparation G₁ G₂) : Disjoint G₁.edgeSet G₂.edgeSet := by
  rw [Set.disjoint_iff_inter_eq_empty]
  exact hsep.edgeSet_inter_eq

theorem isSeparation_vertexSet_union {G G₁ G₂ : Hypergraph α β}
    (hsep : G.IsSeparation G₁ G₂) : G₁.vertexSet ∪ G₂.vertexSet = G.vertexSet :=
  congrArg Hypergraph.vertexSet hsep.union_eq

theorem isSeparation_edgeSet_union {G G₁ G₂ : Hypergraph α β}
    (hsep : G.IsSeparation G₁ G₂) : G₁.edgeSet ∪ G₂.edgeSet = G.edgeSet :=
  congrArg Hypergraph.edgeSet hsep.union_eq

/-- Two `Ω`-patchworks agree on their rooted hypergraph, domain, and edge data on `E(G)`. -/
structure Patchwork.Agrees (P₁ P₂ : Patchwork Ω α β) : Prop where
  G_eq : P₁.G = P₂.G
  dom_eq : P₁.dom = P₂.dom
  μ_eq : ∀ e ∈ P₁.G.edgeSet, P₁.μ e = P₂.μ e
  Δ_eq : ∀ e ∈ P₁.G.edgeSet, P₁.Δ e = P₂.Δ e
  φ_eq : ∀ e ∈ P₁.G.edgeSet, P₁.φ e = P₂.φ e

omit [Preorder Ω] in
theorem Patchwork.Agrees.symm {P₁ P₂ : Patchwork Ω α β} (h : P₁.Agrees P₂) : P₂.Agrees P₁ where
  G_eq := h.G_eq.symm
  dom_eq := h.dom_eq.symm
  μ_eq e he := (h.μ_eq e (h.G_eq.symm ▸ he)).symm
  Δ_eq e he := (h.Δ_eq e (h.G_eq.symm ▸ he)).symm
  φ_eq e he := (h.φ_eq e (h.G_eq.symm ▸ he)).symm

omit [Preorder Ω] in
theorem Patchwork.agrees_restrict_self (P : Patchwork Ω α β) :
    (P.restrict P.G).Agrees P where
  G_eq := rfl
  dom_eq := by
    rw [P.restrict_dom le_rfl, Set.inter_eq_left.mpr P.dom_subset]
  μ_eq _ _ := rfl
  Δ_eq _ he := P.restrict_Δ le_rfl he
  φ_eq _ _ := rfl

omit [Preorder Ω] in
theorem Patchwork.agrees_restrict_restrict {P : Patchwork Ω α β}
    {G₁ G₂ : RootedHypergraph α β} (h₁ : G₁.toHypergraph ≤ P.G.toHypergraph)
    (h₂ : G₂.toHypergraph ≤ G₁.toHypergraph) :
    ((P.restrict G₁).restrict G₂).Agrees (P.restrict G₂) where
  G_eq := rfl
  dom_eq := by
    rw [(P.restrict G₁).restrict_dom h₂, P.restrict_dom h₁, P.restrict_dom (h₂.trans h₁),
      Set.inter_assoc, Set.inter_eq_right.mpr h₂.edgeSet_subset]
  μ_eq _ _ := rfl
  Δ_eq _ he := by
    rw [(P.restrict G₁).restrict_Δ h₂ he, P.restrict_Δ h₁ (h₂.edgeSet_subset he),
      P.restrict_Δ (h₂.trans h₁) he]
  φ_eq _ _ := rfl

theorem IsExpansion.congr {P₁ P₂ : Patchwork Ω α β} {P'₁ P'₂ : Patchwork Ω α' β'}
    {ηv : α → Set α'} {ηe : β → β'} (hP : P₁.Agrees P₂) (hP' : P'₁.Agrees P'₂)
    (h : IsExpansion P₁ P'₁ ηv ηe) : IsExpansion P₂ P'₂ ηv ηe where
  vertex_nonempty v hv := h.vertex_nonempty v (hP.G_eq.symm ▸ hv)
  vertex_subset v hv := hP'.G_eq ▸ h.vertex_subset v (hP.G_eq.symm ▸ hv)
  edge_mem e he := hP'.G_eq ▸ h.edge_mem e (hP.G_eq.symm ▸ he)
  vertex_disjoint v₁ hv₁ v₂ hv₂ hne :=
    h.vertex_disjoint v₁ (hP.G_eq.symm ▸ hv₁) v₂ (hP.G_eq.symm ▸ hv₂) hne
  edge_injOn := hP.G_eq ▸ h.edge_injOn
  mem_dom_iff e he := by
    rw [← hP.dom_eq, ← hP'.dom_eq]
    exact h.mem_dom_iff e (hP.G_eq.symm ▸ he)
  ends_nonempty e he hnd v hinc := by
    have he₁ : e ∈ P₁.G.edgeSet := hP.G_eq.symm ▸ he
    have hnd₁ : e ∉ P₁.dom := hP.dom_eq.symm ▸ hnd
    have hinc₁ : P₁.G.Inc e v := hP.G_eq.symm ▸ hinc
    obtain ⟨v', hv', hinc'⟩ := h.ends_nonempty e he₁ hnd₁ v hinc₁
    exact ⟨v', hv', hP'.G_eq ▸ hinc'⟩
  μ_length e he := by
    have he₁ : e ∈ P₁.dom := hP.dom_eq.symm ▸ he
    have heE₁ : e ∈ P₁.G.edgeSet := P₁.dom_subset he₁
    have he'E₁ : ηe e ∈ P'₁.G.edgeSet := h.edge_mem e heE₁
    rw [← hP.μ_eq e heE₁, ← hP'.μ_eq (ηe e) he'E₁]
    exact h.μ_length e he₁
  μ_mem e he i hi hi' := by
    have he₁ : e ∈ P₁.dom := hP.dom_eq.symm ▸ he
    have heE₁ : e ∈ P₁.G.edgeSet := P₁.dom_subset he₁
    have he'E₁ : ηe e ∈ P'₁.G.edgeSet := h.edge_mem e heE₁
    have hi₁ : i < (P₁.μ e).length := (hP.μ_eq e heE₁).symm ▸ hi
    have hi'₁ : i < (P'₁.μ (ηe e)).length := (hP'.μ_eq (ηe e) he'E₁).symm ▸ hi'
    have hmem := h.μ_mem e he₁ i hi₁ hi'₁
    simpa [hP.μ_eq e heE₁, hP'.μ_eq (ηe e) he'E₁] using hmem
  roots_length := by
    rw [← hP.G_eq, ← hP'.G_eq]
    exact h.roots_length
  roots_mem i hi hi' := by
    have hi₁ : i < P₁.G.roots.length := hP.G_eq.symm ▸ hi
    have hi'₁ : i < P'₁.G.roots.length := hP'.G_eq.symm ▸ hi'
    have hmem := h.roots_mem i hi₁ hi'₁
    simpa [hP.G_eq, hP'.G_eq] using hmem
  maps_Δ e he := by
    have he₁ : e ∈ P₁.dom := hP.dom_eq.symm ▸ he
    have heE₁ : e ∈ P₁.G.edgeSet := P₁.dom_subset he₁
    have he'E₁ : ηe e ∈ P'₁.G.edgeSet := h.edge_mem e heE₁
    rw [← hP.μ_eq e heE₁, ← hP'.μ_eq (ηe e) he'E₁, ← hP.Δ_eq e heE₁, ← hP'.Δ_eq (ηe e) he'E₁]
    exact h.maps_Δ e he₁
  φ_le e he := by
    have heE₁ : e ∈ P₁.G.edgeSet := hP.G_eq.symm ▸ he
    have he'E₁ : ηe e ∈ P'₁.G.edgeSet := h.edge_mem e heE₁
    rw [← hP.φ_eq e heE₁, ← hP'.φ_eq (ηe e) he'E₁]
    exact h.φ_le e heE₁

omit [Preorder Ω] in
theorem Realizes.congr {P₁ P₂ : Patchwork Ω α β} {P'₁ P'₂ : Patchwork Ω α' β'}
    {ηv : α → Set α'} {ηe : β → β'} {H : (⊤ : SimpleGraph α').Subgraph}
    (hP : P₁.Agrees P₂) (hP' : P'₁.Agrees P'₂) (h : Realizes P₁ P'₁ ηv ηe H) :
    Realizes P₂ P'₂ ηv ηe H := by
  obtain ⟨⟨δ, hδ, hH⟩, hcomp⟩ := h
  refine ⟨⟨δ, fun e he ↦ ?_, ?_⟩, fun v hv ↦ hcomp v (hP.G_eq.symm ▸ hv)⟩
  · have he₁ : e ∈ (P'₁.deleteEdges (ηe '' P₁.G.edgeSet)).G.edgeSet := by
      simpa [Patchwork.deleteEdges, RootedHypergraph.deleteEdges, Hypergraph.deleteEdges,
        hP.G_eq, hP'.G_eq] using he
    have hmem := hδ e he₁
    change δ e ∈ P'₂.Δ e
    rw [← hP'.Δ_eq e he₁.1]
    exact hmem
  · simpa [Patchwork.deleteEdges, RootedHypergraph.deleteEdges, Hypergraph.deleteEdges,
      hP.G_eq, hP'.G_eq] using hH

theorem IsRealizableExpansion.congr {P₁ P₂ : Patchwork Ω α β} {P'₁ P'₂ : Patchwork Ω α' β'}
    {ηv : α → Set α'} {ηe : β → β'} (hP : P₁.Agrees P₂) (hP' : P'₁.Agrees P'₂)
    (h : IsRealizableExpansion P₁ P'₁ ηv ηe) : IsRealizableExpansion P₂ P'₂ ηv ηe := by
  obtain ⟨hexp, H, hreal⟩ := h
  exact ⟨hexp.congr hP hP', H, hreal.congr hP hP'⟩

/-! ### Gluing expansions across separations: Graph Minors IV, (8.1) -/

open Classical in
/-- The vertex map `η(v)` of Graph Minors IV, (8.1) (page 247):
`η₁(v)` for `v ∈ V(G₁) - V(G₂)`, `η₂(v)` for `v ∈ V(G₂) - V(G₁)`, and `η₁(v) ∪ η₂(v)` for
`v ∈ V(G₁) ∩ V(G₂)`. -/
noncomputable def glueVertex (G₁ G₂ : RootedHypergraph α β) (η₁v η₂v : α → Set α') (v : α) :
    Set α' :=
  (if v ∈ G₁.vertexSet then η₁v v else ∅) ∪ (if v ∈ G₂.vertexSet then η₂v v else ∅)

open Classical in
/-- The edge map `η(e)` of Graph Minors IV, (8.1) (page 247):
`η₁(e)` for `e ∈ E(G₁)` and `η₂(e)` for `e ∈ E(G₂)`. -/
noncomputable def glueEdge (G₁ : RootedHypergraph α β) (η₁e η₂e : β → β') (e : β) : β' :=
  if e ∈ G₁.edgeSet then η₁e e else η₂e e

@[simp]
theorem mem_glueVertex_iff {G₁ G₂ : RootedHypergraph α β} {η₁v η₂v : α → Set α'}
    {v : α} {v' : α'} :
    v' ∈ glueVertex G₁ G₂ η₁v η₂v v ↔
      (v ∈ G₁.vertexSet ∧ v' ∈ η₁v v) ∨ (v ∈ G₂.vertexSet ∧ v' ∈ η₂v v) := by
  dsimp only [glueVertex]
  simp only [Set.mem_union]
  constructor
  · rintro (h | h)
    · split_ifs at h with hv₁
      · exact Or.inl ⟨hv₁, h⟩
      · exact False.elim h
    · split_ifs at h with hv₂
      · exact Or.inr ⟨hv₂, h⟩
      · exact False.elim h
  · rintro (⟨hv₁, h⟩ | ⟨hv₂, h⟩)
    · left
      simp [hv₁, h]
    · right
      simp [hv₂, h]

theorem glueEdge_of_mem_left {G₁ : RootedHypergraph α β} {η₁e η₂e : β → β'} {e : β}
    (he : e ∈ G₁.edgeSet) : glueEdge G₁ η₁e η₂e e = η₁e e := by
  simp [glueEdge, he]

theorem glueEdge_of_notMem_left {G₁ : RootedHypergraph α β} {η₁e η₂e : β → β'} {e : β}
    (he : e ∉ G₁.edgeSet) : glueEdge G₁ η₁e η₂e e = η₂e e := by
  simp [glueEdge, he]

/-- Graph Minors IV, (8.1), claim (1) (page 248):
"For $1 \le i \le k$ and all $v \in V(G)$, if $v'_i \in \eta(v)$ then $v = v_i$." -/
theorem lemma_8_1_claim_1 {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {G₁ G₂ : RootedHypergraph α β} {G'₁ G'₂ : RootedHypergraph α' β'}
    (hsep : P.G.IsSeparation G₁ G₂)
    {η₁v η₂v : α → Set α'} {η₁e η₂e : β → β'}
    (hη₁ : IsExpansion (P.restrict G₁) (P'.restrict G'₁) η₁v η₁e)
    (hη₂ : IsExpansion (P.restrict G₂) (P'.restrict G'₂) η₂v η₂e)
    (hroots_mem : ∀ (i : ℕ) (hi : i < G₁.roots.length) (hi' : i < G'₁.roots.length),
      G'₁.roots[i] ∈ η₂v G₁.roots[i])
    {i : ℕ} (hi : i < G₁.roots.length) (hi' : i < G'₁.roots.length)
    {v : α} (hv : G'₁.roots[i] ∈ glueVertex G₁ G₂ η₁v η₂v v) :
    v = G₁.roots[i] := by
  have hvi_root : G₁.roots[i] ∈ G₁.rootSet := List.getElem_mem hi
  rw [hsep.rootSet_left] at hvi_root
  have hvi₁ : G₁.roots[i] ∈ G₁.vertexSet := hvi_root.1
  have hvi₂ : G₁.roots[i] ∈ G₂.vertexSet := hvi_root.2
  rw [mem_glueVertex_iff] at hv
  rcases hv with ⟨hv₁, hv_mem₁⟩ | ⟨hv₂, hv_mem₂⟩
  · by_contra hne
    exact Set.disjoint_left.mp (hη₁.vertex_disjoint v hv₁ G₁.roots[i] hvi₁ hne)
      hv_mem₁ (hη₁.roots_mem i hi hi')
  · by_contra hne
    exact Set.disjoint_left.mp (hη₂.vertex_disjoint v hv₂ G₁.roots[i] hvi₂ hne)
      hv_mem₂ (hroots_mem i hi hi')

/-- Graph Minors IV, (8.1), claim (2) (page 248):
"For distinct $u_1, u_2 \in V(G)$, $\eta(u_1) \cap \eta(u_2) = \emptyset$." -/
theorem lemma_8_1_claim_2 {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {G₁ G₂ : RootedHypergraph α β} {G'₁ G'₂ : RootedHypergraph α' β'}
    (hsep : P.G.IsSeparation G₁ G₂) (hsep' : P'.G.IsSeparation G'₁ G'₂)
    {η₁v η₂v : α → Set α'} {η₁e η₂e : β → β'}
    (hη₁ : IsExpansion (P.restrict G₁) (P'.restrict G'₁) η₁v η₁e)
    (hη₂ : IsExpansion (P.restrict G₂) (P'.restrict G'₂) η₂v η₂e)
    (hroots_mem : ∀ (i : ℕ) (hi : i < G₁.roots.length) (hi' : i < G'₁.roots.length),
      G'₁.roots[i] ∈ η₂v G₁.roots[i])
    {u₁ u₂ : α} (hne : u₁ ≠ u₂) :
    Disjoint (glueVertex G₁ G₂ η₁v η₂v u₁) (glueVertex G₁ G₂ η₁v η₂v u₂) := by
  refine Set.disjoint_left.mpr fun v' h₁ h₂ ↦ hne ?_
  have h₁' := mem_glueVertex_iff.mp h₁
  have h₂' := mem_glueVertex_iff.mp h₂
  rcases h₁' with ⟨hu₁, hv'₁⟩ | ⟨hu₁, hv'₁⟩ <;> rcases h₂' with ⟨hu₂, hv'₂⟩ | ⟨hu₂, hv'₂⟩
  · by_contra hne'
    exact Set.disjoint_left.mp (hη₁.vertex_disjoint u₁ hu₁ u₂ hu₂ hne') hv'₁ hv'₂
  · have hv'_inter : v' ∈ (G'₁.toHypergraph ∩ G'₂.toHypergraph).vertexSet :=
      ⟨hη₁.vertex_subset u₁ hu₁ hv'₁, hη₂.vertex_subset u₂ hu₂ hv'₂⟩
    rw [← hsep'.rootSet_left] at hv'_inter
    obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hv'_inter
    have hi : i < G₁.roots.length := hη₁.roots_length.symm ▸ hi'
    have hEq₁ := lemma_8_1_claim_1 hsep hη₁ hη₂ hroots_mem hi hi' h₁
    have hEq₂ := lemma_8_1_claim_1 hsep hη₁ hη₂ hroots_mem hi hi' h₂
    exact hEq₁.trans hEq₂.symm
  · have hv'_inter : v' ∈ (G'₁.toHypergraph ∩ G'₂.toHypergraph).vertexSet :=
      ⟨hη₁.vertex_subset u₂ hu₂ hv'₂, hη₂.vertex_subset u₁ hu₁ hv'₁⟩
    rw [← hsep'.rootSet_left] at hv'_inter
    obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hv'_inter
    have hi : i < G₁.roots.length := hη₁.roots_length.symm ▸ hi'
    have hEq₁ := lemma_8_1_claim_1 hsep hη₁ hη₂ hroots_mem hi hi' h₁
    have hEq₂ := lemma_8_1_claim_1 hsep hη₁ hη₂ hroots_mem hi hi' h₂
    exact hEq₁.trans hEq₂.symm
  · by_contra hne'
    exact Set.disjoint_left.mp (hη₂.vertex_disjoint u₁ hu₁ u₂ hu₂ hne') hv'₁ hv'₂

/-- First half of Graph Minors IV, (8.1) (page 248): the glued map `(glueVertex, glueEdge)` is an
expansion of `P` in `P'`. -/
theorem theorem_8_1_expansion {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {G₁ G₂ : RootedHypergraph α β} {G'₁ G'₂ : RootedHypergraph α' β'}
    (hsep : P.G.IsSeparation G₁ G₂) (hsep' : P'.G.IsSeparation G'₁ G'₂)
    {η₁v η₂v : α → Set α'} {η₁e η₂e : β → β'}
    (hη₁ : IsExpansion (P.restrict G₁) (P'.restrict G'₁) η₁v η₁e)
    (hη₂ : IsExpansion (P.restrict G₂) (P'.restrict G'₂) η₂v η₂e)
    (hroots_mem : ∀ (i : ℕ) (hi : i < G₁.roots.length) (hi' : i < G'₁.roots.length),
      G'₁.roots[i] ∈ η₂v G₁.roots[i]) :
    IsExpansion P P' (glueVertex G₁ G₂ η₁v η₂v) (glueEdge G₁ η₁e η₂e) := by
  have hle₁ := hsep.isSeparation.left_le
  have hle₂ := hsep.isSeparation.right_le
  have hle'₁ := hsep'.isSeparation.left_le
  have hle'₂ := hsep'.isSeparation.right_le
  have hdisjE := isSeparation_disjoint_edgeSet hsep.isSeparation
  have hdisjE' := isSeparation_disjoint_edgeSet hsep'.isSeparation
  have he_or : ∀ e ∈ P.G.edgeSet, e ∈ G₁.edgeSet ∨ (e ∈ G₂.edgeSet ∧ e ∉ G₁.edgeSet) := by
    intro e he
    by_cases he₁ : e ∈ G₁.edgeSet
    · exact Or.inl he₁
    · rw [← isSeparation_edgeSet_union hsep.isSeparation] at he
      rcases he with he₁' | he₂
      · exact absurd he₁' he₁
      · exact Or.inr ⟨he₂, he₁⟩
  refine
    { vertex_nonempty := fun v hv ↦ ?_
      vertex_subset := fun v hv v' hv' ↦ ?_
      edge_mem := fun e he ↦ ?_
      vertex_disjoint := fun u₁ _ u₂ _ hne ↦
        lemma_8_1_claim_2 hsep hsep' hη₁ hη₂ hroots_mem hne
      edge_injOn := fun e₁ he₁ e₂ he₂ hEq ↦ ?_
      mem_dom_iff := fun e he ↦ ?_
      ends_nonempty := fun e he hnd v hinc ↦ ?_
      μ_length := fun e he ↦ ?_
      μ_mem := fun e he i hi hi' ↦ ?_
      roots_length := ?_
      roots_mem := fun i hi hi' ↦ ?_
      maps_Δ := fun e he ↦ ?_
      φ_le := fun e he ↦ ?_ }
  · rw [← isSeparation_vertexSet_union hsep.isSeparation] at hv
    rcases hv with hv₁ | hv₂
    · obtain ⟨v', hv'⟩ := hη₁.vertex_nonempty v hv₁
      exact ⟨v', mem_glueVertex_iff.mpr (Or.inl ⟨hv₁, hv'⟩)⟩
    · obtain ⟨v', hv'⟩ := hη₂.vertex_nonempty v hv₂
      exact ⟨v', mem_glueVertex_iff.mpr (Or.inr ⟨hv₂, hv'⟩)⟩
  · rcases mem_glueVertex_iff.mp hv' with ⟨hv₁, hv'₁⟩ | ⟨hv₂, hv'₂⟩
    · exact hle'₁.vertexSet_subset (hη₁.vertex_subset v hv₁ hv'₁)
    · exact hle'₂.vertexSet_subset (hη₂.vertex_subset v hv₂ hv'₂)
  · rcases he_or e he with he₁ | ⟨he₂, hne₁⟩
    · rw [glueEdge_of_mem_left he₁]
      exact hle'₁.edgeSet_subset (hη₁.edge_mem e he₁)
    · rw [glueEdge_of_notMem_left hne₁]
      exact hle'₂.edgeSet_subset (hη₂.edge_mem e he₂)
  · rcases he_or e₁ he₁ with h₁ | ⟨h₁, hn₁⟩ <;> rcases he_or e₂ he₂ with h₂ | ⟨h₂, hn₂⟩
    · rw [glueEdge_of_mem_left h₁, glueEdge_of_mem_left h₂] at hEq
      exact hη₁.edge_injOn h₁ h₂ hEq
    · rw [glueEdge_of_mem_left h₁, glueEdge_of_notMem_left hn₂] at hEq
      exact False.elim (Set.disjoint_left.mp hdisjE' (hη₁.edge_mem e₁ h₁)
        (hEq ▸ hη₂.edge_mem e₂ h₂))
    · rw [glueEdge_of_notMem_left hn₁, glueEdge_of_mem_left h₂] at hEq
      exact False.elim (Set.disjoint_left.mp hdisjE' (hEq ▸ hη₁.edge_mem e₂ h₂)
        (hη₂.edge_mem e₁ h₁))
    · rw [glueEdge_of_notMem_left hn₁, glueEdge_of_notMem_left hn₂] at hEq
      exact hη₂.edge_injOn h₁ h₂ hEq
  · rcases he_or e he with he₁ | ⟨he₂, hne₁⟩
    · rw [glueEdge_of_mem_left he₁]
      have hdom₁ := hη₁.mem_dom_iff e he₁
      rw [P.restrict_dom hle₁, P'.restrict_dom hle'₁] at hdom₁
      exact ⟨fun hd ↦ (hdom₁.mp ⟨hd, he₁⟩).1, fun hd' ↦ (hdom₁.mpr ⟨hd', hη₁.edge_mem e he₁⟩).1⟩
    · rw [glueEdge_of_notMem_left hne₁]
      have hdom₂ := hη₂.mem_dom_iff e he₂
      rw [P.restrict_dom hle₂, P'.restrict_dom hle'₂] at hdom₂
      exact ⟨fun hd ↦ (hdom₂.mp ⟨hd, he₂⟩).1, fun hd' ↦ (hdom₂.mpr ⟨hd', hη₂.edge_mem e he₂⟩).1⟩
  · rcases he_or e he with he₁ | ⟨he₂, hne₁⟩
    · rw [glueEdge_of_mem_left he₁]
      have hnd₁ : e ∉ (P.restrict G₁).dom := by
        rw [P.restrict_dom hle₁]
        exact fun h ↦ hnd h.1
      have hinc₁ : G₁.Inc e v := by
        change v ∈ G₁.ends e
        rw [← hle₁.ends_eq e he₁]
        exact hinc
      obtain ⟨v', hv', hinc'⟩ := hη₁.ends_nonempty e he₁ hnd₁ v hinc₁
      refine ⟨v', mem_glueVertex_iff.mpr (Or.inl ⟨G₁.vertex_mem_of_inc hinc₁, hv'⟩), ?_⟩
      change v' ∈ P'.G.ends (η₁e e)
      rw [hle'₁.ends_eq (η₁e e) (hη₁.edge_mem e he₁)]
      exact hinc'
    · rw [glueEdge_of_notMem_left hne₁]
      have hnd₂ : e ∉ (P.restrict G₂).dom := by
        rw [P.restrict_dom hle₂]
        exact fun h ↦ hnd h.1
      have hinc₂ : G₂.Inc e v := by
        change v ∈ G₂.ends e
        rw [← hle₂.ends_eq e he₂]
        exact hinc
      obtain ⟨v', hv', hinc'⟩ := hη₂.ends_nonempty e he₂ hnd₂ v hinc₂
      refine ⟨v', mem_glueVertex_iff.mpr (Or.inr ⟨G₂.vertex_mem_of_inc hinc₂, hv'⟩), ?_⟩
      change v' ∈ P'.G.ends (η₂e e)
      rw [hle'₂.ends_eq (η₂e e) (hη₂.edge_mem e he₂)]
      exact hinc'
  · rcases he_or e (P.dom_subset he) with he₁ | ⟨he₂, hne₁⟩
    · rw [glueEdge_of_mem_left he₁]
      have hd₁ : e ∈ (P.restrict G₁).dom := by
        rw [P.restrict_dom hle₁]
        exact ⟨he, he₁⟩
      exact hη₁.μ_length e hd₁
    · rw [glueEdge_of_notMem_left hne₁]
      have hd₂ : e ∈ (P.restrict G₂).dom := by
        rw [P.restrict_dom hle₂]
        exact ⟨he, he₂⟩
      exact hη₂.μ_length e hd₂
  · rcases he_or e (P.dom_subset he) with he₁ | ⟨he₂, hne₁⟩
    · simp only [glueEdge_of_mem_left he₁] at hi' ⊢
      have hd₁ : e ∈ (P.restrict G₁).dom := by
        rw [P.restrict_dom hle₁]
        exact ⟨he, he₁⟩
      have hv_end : (P.μ e)[i] ∈ G₁.ends e := by
        rw [← hle₁.ends_eq e he₁, ← P.μ_set e he]
        exact List.getElem_mem hi
      exact mem_glueVertex_iff.mpr
        (Or.inl ⟨G₁.vertex_mem_of_inc hv_end, hη₁.μ_mem e hd₁ i hi hi'⟩)
    · simp only [glueEdge_of_notMem_left hne₁] at hi' ⊢
      have hd₂ : e ∈ (P.restrict G₂).dom := by
        rw [P.restrict_dom hle₂]
        exact ⟨he, he₂⟩
      have hv_end : (P.μ e)[i] ∈ G₂.ends e := by
        rw [← hle₂.ends_eq e he₂, ← P.μ_set e he]
        exact List.getElem_mem hi
      exact mem_glueVertex_iff.mpr
        (Or.inr ⟨G₂.vertex_mem_of_inc hv_end, hη₂.μ_mem e hd₂ i hi hi'⟩)
  · rw [← hsep.roots_right, ← hsep'.roots_right]
    exact hη₂.roots_length
  · have hi₂ : i < G₂.roots.length := hsep.roots_right.symm ▸ hi
    have hi'₂ : i < G'₂.roots.length := hsep'.roots_right.symm ▸ hi'
    have hmem := hη₂.roots_mem i hi₂ hi'₂
    have hv₂ : G₂.roots[i] ∈ G₂.vertexSet := G₂.roots_subset _ (List.getElem_mem hi₂)
    have hmem' : G'₂.roots[i] ∈ glueVertex G₁ G₂ η₁v η₂v G₂.roots[i] :=
      mem_glueVertex_iff.mpr (Or.inr ⟨hv₂, hmem⟩)
    simpa [hsep.roots_right, hsep'.roots_right] using hmem'
  · rcases he_or e (P.dom_subset he) with he₁ | ⟨he₂, hne₁⟩
    · rw [glueEdge_of_mem_left he₁]
      have hd₁ : e ∈ (P.restrict G₁).dom := by
        rw [P.restrict_dom hle₁]
        exact ⟨he, he₁⟩
      have hmaps := hη₁.maps_Δ e hd₁
      rwa [P.restrict_Δ hle₁ he₁, P'.restrict_Δ hle'₁ (hη₁.edge_mem e he₁)] at hmaps
    · rw [glueEdge_of_notMem_left hne₁]
      have hd₂ : e ∈ (P.restrict G₂).dom := by
        rw [P.restrict_dom hle₂]
        exact ⟨he, he₂⟩
      have hmaps := hη₂.maps_Δ e hd₂
      rwa [P.restrict_Δ hle₂ he₂, P'.restrict_Δ hle'₂ (hη₂.edge_mem e he₂)] at hmaps
  · rcases he_or e he with he₁ | ⟨he₂, hne₁⟩
    · rw [glueEdge_of_mem_left he₁]
      exact hη₁.φ_le e he₁
    · rw [glueEdge_of_notMem_left hne₁]
      exact hη₂.φ_le e he₂

private theorem emptySubgraph_sup_emptySubgraph (X Y : Set α) :
    emptySubgraph X ⊔ emptySubgraph Y = emptySubgraph (X ∪ Y) := by
  ext v w
  · rfl
  · simp [emptySubgraph]

/-- **Graph Minors IV, (8.1)** (page 247):
"Let $P = (G, \mu, \Delta, \phi)$, $P' = (G', \mu', \Delta', \phi')$ be $\Omega$-patchworks, and
let $(G_1, G_2)$, $(G'_1, G'_2)$ be separations of $G$, $G'$ respectively. Let $\eta_1$ be a
realizable expansion of $P | G_1$ in $P' | G'_1$ (whence $|\bar{\pi}(G_1)| = |\bar{\pi}(G'_1)| = k$,
say) and let $\eta_2$ be a realizable expansion of $P | G_2$ in $P' | G'_2$ such that for
$1 \le i \le k$, $\eta_2(v)$ contains the $i$th term of $\pi(G'_1)$, where $v$ is the $i$th term of
$\pi(G_1)$. Define $\eta$ by
$$\begin{aligned}
\eta(v) &= \eta_1(v) && (v \in V(G_1) - V(G_2)) \\
&= \eta_2(v) && (v \in V(G_2) - V(G_1)) \\
&= \eta_1(v) \cup \eta_2(v) && (v \in V(G_1) \cap V(G_2)) \\
\eta(e) &= \eta_1(e) && (e \in E(G_1)) \\
&= \eta_2(e) && (e \in E(G_2)).
\end{aligned}$$
Then $\eta$ is a realizable expansion of $P$ in $P'$." -/
theorem theorem_8_1_proof {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {G₁ G₂ : RootedHypergraph α β} {G'₁ G'₂ : RootedHypergraph α' β'}
    (hsep : P.G.IsSeparation G₁ G₂) (hsep' : P'.G.IsSeparation G'₁ G'₂)
    {η₁v η₂v : α → Set α'} {η₁e η₂e : β → β'}
    (hη₁ : IsRealizableExpansion (P.restrict G₁) (P'.restrict G'₁) η₁v η₁e)
    (hη₂ : IsRealizableExpansion (P.restrict G₂) (P'.restrict G'₂) η₂v η₂e)
    (hroots_mem : ∀ (i : ℕ) (hi : i < G₁.roots.length) (hi' : i < G'₁.roots.length),
      G'₁.roots[i] ∈ η₂v G₁.roots[i]) :
    IsRealizableExpansion P P' (glueVertex G₁ G₂ η₁v η₂v) (glueEdge G₁ η₁e η₂e) := by
  classical
  obtain ⟨hexp₁, H₁, ⟨⟨δ₁, hδ₁, hH₁_eq⟩, hcomp₁⟩⟩ := hη₁
  obtain ⟨hexp₂, H₂, ⟨⟨δ₂, hδ₂, hH₂_eq⟩, hcomp₂⟩⟩ := hη₂
  have hexp := theorem_8_1_expansion hsep hsep' hexp₁ hexp₂ hroots_mem
  refine ⟨hexp, H₁ ⊔ H₂, ?_, ?_⟩
  · have hle'₁ := hsep'.isSeparation.left_le
    have hle'₂ := hsep'.isSeparation.right_le
    have hdisjE := isSeparation_disjoint_edgeSet hsep.isSeparation
    have hdisjE' := isSeparation_disjoint_edgeSet hsep'.isSeparation
    let ηe := glueEdge G₁ η₁e η₂e
    let δ : β' → (⊤ : SimpleGraph α').Subgraph :=
      fun e' ↦ if e' ∈ G'₁.edgeSet then δ₁ e' else δ₂ e'
    let S₁ : Set β' := G'₁.edgeSet \ (η₁e '' G₁.edgeSet)
    let S₂ : Set β' := G'₂.edgeSet \ (η₂e '' G₂.edgeSet)
    let S : Set β' := P'.G.edgeSet \ (ηe '' P.G.edgeSet)
    have hS₁_sub : ∀ e' ∈ S₁, e' ∈ S := by
      rintro e' ⟨he'₁, hne'₁⟩
      refine ⟨hle'₁.edgeSet_subset he'₁, ?_⟩
      rintro ⟨e, he, rfl⟩
      dsimp only [ηe] at he'₁ hne'₁
      by_cases he₁ : e ∈ G₁.edgeSet
      · rw [glueEdge_of_mem_left he₁] at hne'₁
        exact hne'₁ ⟨e, he₁, rfl⟩
      · rw [glueEdge_of_notMem_left he₁] at he'₁
        rw [← isSeparation_edgeSet_union hsep.isSeparation] at he
        rcases he with he₁' | he₂
        · exact he₁ he₁'
        · exact Set.disjoint_left.mp hdisjE' he'₁ (hexp₂.edge_mem e he₂)
    have hS₂_sub : ∀ e' ∈ S₂, e' ∈ S ∧ e' ∉ G'₁.edgeSet := by
      rintro e' ⟨he'₂, hne'₂⟩
      have hne'₁ : e' ∉ G'₁.edgeSet := fun h ↦ Set.disjoint_left.mp hdisjE' h he'₂
      refine ⟨⟨hle'₂.edgeSet_subset he'₂, ?_⟩, hne'₁⟩
      rintro ⟨e, he, rfl⟩
      dsimp only [ηe] at hne'₁ hne'₂
      by_cases he₁ : e ∈ G₁.edgeSet
      · rw [glueEdge_of_mem_left he₁] at hne'₁
        exact hne'₁ (hexp₁.edge_mem e he₁)
      · rw [glueEdge_of_notMem_left he₁] at hne'₂
        rw [← isSeparation_edgeSet_union hsep.isSeparation] at he
        rcases he with he₁' | he₂
        · exact he₁ he₁'
        · exact hne'₂ ⟨e, he₂, rfl⟩
    have hS_or : ∀ e' ∈ S, e' ∈ S₁ ∨ (e' ∈ S₂ ∧ e' ∉ G'₁.edgeSet) := by
      rintro e' ⟨he', hne'⟩
      by_cases he'₁ : e' ∈ G'₁.edgeSet
      · refine Or.inl ⟨he'₁, ?_⟩
        rintro ⟨e, he₁, rfl⟩
        exact hne' ⟨e, hsep.isSeparation.left_le.edgeSet_subset he₁, glueEdge_of_mem_left he₁⟩
      · rw [← isSeparation_edgeSet_union hsep'.isSeparation] at he'
        rcases he' with he'₁_abs | he'₂
        · exact absurd he'₁_abs he'₁
        · refine Or.inr ⟨⟨he'₂, ?_⟩, he'₁⟩
          rintro ⟨e, he₂, rfl⟩
          have hne₁ : e ∉ G₁.edgeSet := fun h ↦ Set.disjoint_left.mp hdisjE h he₂
          exact hne' ⟨e, hsep.isSeparation.right_le.edgeSet_subset he₂, glueEdge_of_notMem_left
            hne₁⟩
    refine ⟨δ, fun e' he' ↦ ?_, ?_⟩
    · rcases hS_or e' he' with he'₁ | ⟨he'₂, hne'₁⟩
      · dsimp only [δ]
        rw [ite_eq_left_iff.mpr (fun h ↦ absurd he'₁.1 h)]
        have hmem := hδ₁ e' he'₁
        change δ₁ e' ∈ (P'.restrict G'₁).Δ e' at hmem
        rwa [P'.restrict_Δ hle'₁ he'₁.1] at hmem
      · dsimp only [δ]
        rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hne'₁)]
        have hmem := hδ₂ e' he'₂
        change δ₂ e' ∈ (P'.restrict G'₂).Δ e' at hmem
        rwa [P'.restrict_Δ hle'₂ he'₂.1] at hmem
    · change H₁ ⊔ H₂ = emptySubgraph P'.G.vertexSet ⊔ ⨆ e' ∈ S, δ e'
      have hH₁_eq' : H₁ = emptySubgraph G'₁.vertexSet ⊔ ⨆ e' ∈ S₁, δ₁ e' := hH₁_eq
      have hH₂_eq' : H₂ = emptySubgraph G'₂.vertexSet ⊔ ⨆ e' ∈ S₂, δ₂ e' := hH₂_eq
      rw [hH₁_eq', hH₂_eq', sup_sup_sup_comm, emptySubgraph_sup_emptySubgraph,
        isSeparation_vertexSet_union hsep'.isSeparation]
      congr 1
      apply le_antisymm
      · refine sup_le (iSup₂_le fun e' he'₁ ↦ ?_) (iSup₂_le fun e' he'₂ ↦ ?_)
        · have hδ_eq : δ₁ e' = δ e' := by
            dsimp only [δ]
            rw [ite_eq_left_iff.mpr (fun h ↦ absurd he'₁.1 h)]
          rw [hδ_eq]
          exact le_biSup δ (hS₁_sub e' he'₁)
        · obtain ⟨he'S, hne'₁⟩ := hS₂_sub e' he'₂
          have hδ_eq : δ₂ e' = δ e' := by
            dsimp only [δ]
            rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hne'₁)]
          rw [hδ_eq]
          exact le_biSup δ he'S
      · refine iSup₂_le fun e' he' ↦ ?_
        rcases hS_or e' he' with he'₁ | ⟨he'₂, hne'₁⟩
        · have hδ_eq : δ e' = δ₁ e' := by
            dsimp only [δ]
            rw [ite_eq_left_iff.mpr (fun h ↦ absurd he'₁.1 h)]
          rw [hδ_eq]
          exact le_sup_of_le_left (le_biSup δ₁ he'₁)
        · have hδ_eq : δ e' = δ₂ e' := by
            dsimp only [δ]
            rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hne'₁)]
          rw [hδ_eq]
          exact le_sup_of_le_right (le_biSup δ₂ he'₂)
  · intro v hv
    have hH₁_verts : H₁.verts = G'₁.vertexSet :=
      Patchwork.IsRealization.verts_eq ⟨δ₁, hδ₁, hH₁_eq⟩
    have hH₂_verts : H₂.verts = G'₂.vertexSet :=
      Patchwork.IsRealization.verts_eq ⟨δ₂, hδ₂, hH₂_eq⟩
    have hH_verts : (H₁ ⊔ H₂).verts = P'.G.vertexSet := by
      change H₁.verts ∪ H₂.verts = P'.G.vertexSet
      rw [hH₁_verts, hH₂_verts, isSeparation_vertexSet_union hsep'.isSeparation]
    have hsub : glueVertex G₁ G₂ η₁v η₂v v ⊆ (H₁ ⊔ H₂).verts := by
      rw [hH_verts]
      exact hexp.vertex_subset v hv
    have h₁_prop : ∀ (hv₁ : v ∈ G₁.vertexSet),
        (∀ a ∈ η₁v v, ∀ b, H₁.Adj a b → b ∈ η₁v v) ∧
          (∀ a ∈ η₁v v, ∀ b ∈ η₁v v, sameComponent H₁ a b) := by
      intro hv₁
      have hsub₁ : η₁v v ⊆ H₁.verts := hH₁_verts ▸ hexp₁.vertex_subset v hv₁
      exact (exists_isComponent_verts_eq_iff (hexp₁.vertex_nonempty v hv₁) hsub₁).mp (hcomp₁ v hv₁)
    have h₂_prop : ∀ (hv₂ : v ∈ G₂.vertexSet),
        (∀ a ∈ η₂v v, ∀ b, H₂.Adj a b → b ∈ η₂v v) ∧
          (∀ a ∈ η₂v v, ∀ b ∈ η₂v v, sameComponent H₂ a b) := by
      intro hv₂
      have hsub₂ : η₂v v ⊆ H₂.verts := hH₂_verts ▸ hexp₂.vertex_subset v hv₂
      exact (exists_isComponent_verts_eq_iff (hexp₂.vertex_nonempty v hv₂) hsub₂).mp (hcomp₂ v hv₂)
    have h₁_mem : ∀ a ∈ glueVertex G₁ G₂ η₁v η₂v v, a ∈ G'₁.vertexSet →
        v ∈ G₁.vertexSet ∧ a ∈ η₁v v := by
      intro a ha ha₁
      rcases mem_glueVertex_iff.mp ha with ⟨hv₁, ha_mem₁⟩ | ⟨hv₂, ha_mem₂⟩
      · exact ⟨hv₁, ha_mem₁⟩
      · have ha_inter : a ∈ (G'₁.toHypergraph ∩ G'₂.toHypergraph).vertexSet :=
          ⟨ha₁, hexp₂.vertex_subset v hv₂ ha_mem₂⟩
        rw [← hsep'.rootSet_left] at ha_inter
        obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem ha_inter
        have hi : i < G₁.roots.length := hexp₁.roots_length.symm ▸ hi'
        have hv_eq := lemma_8_1_claim_1 hsep hexp₁ hexp₂ hroots_mem hi hi' ha
        subst hv_eq
        exact ⟨G₁.roots_subset _ (List.getElem_mem hi), hexp₁.roots_mem i hi hi'⟩
    have h₂_mem : ∀ a ∈ glueVertex G₁ G₂ η₁v η₂v v, a ∈ G'₂.vertexSet →
        v ∈ G₂.vertexSet ∧ a ∈ η₂v v := by
      intro a ha ha₂
      rcases mem_glueVertex_iff.mp ha with ⟨hv₁, ha_mem₁⟩ | ⟨hv₂, ha_mem₂⟩
      · have ha_inter : a ∈ (G'₁.toHypergraph ∩ G'₂.toHypergraph).vertexSet :=
          ⟨hexp₁.vertex_subset v hv₁ ha_mem₁, ha₂⟩
        rw [← hsep'.rootSet_left] at ha_inter
        obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem ha_inter
        have hi : i < G₁.roots.length := hexp₁.roots_length.symm ▸ hi'
        have hv_eq := lemma_8_1_claim_1 hsep hexp₁ hexp₂ hroots_mem hi hi' ha
        subst hv_eq
        have hvi_inter : G₁.roots[i] ∈ (G₁.toHypergraph ∩ G₂.toHypergraph).vertexSet := by
          rw [← hsep.rootSet_left]
          exact List.getElem_mem hi
        exact ⟨hvi_inter.2, hroots_mem i hi hi'⟩
      · exact ⟨hv₂, ha_mem₂⟩
    rw [exists_isComponent_verts_eq_iff (hexp.vertex_nonempty v hv) hsub]
    refine ⟨fun a ha b hab ↦ ?_, fun a ha b hb ↦ ?_⟩
    · rcases Subgraph.sup_adj.mp hab with hab₁ | hab₂
      · obtain ⟨hv₁, ha₁⟩ := h₁_mem a ha (hH₁_verts ▸ H₁.edge_vert hab₁)
        have hb₁ : b ∈ η₁v v := (h₁_prop hv₁).1 a ha₁ b hab₁
        exact mem_glueVertex_iff.mpr (Or.inl ⟨hv₁, hb₁⟩)
      · obtain ⟨hv₂, ha₂⟩ := h₂_mem a ha (hH₂_verts ▸ H₂.edge_vert hab₂)
        have hb₂ : b ∈ η₂v v := (h₂_prop hv₂).1 a ha₂ b hab₂
        exact mem_glueVertex_iff.mpr (Or.inr ⟨hv₂, hb₂⟩)
    · have hsc₁ : ∀ (hv₁ : v ∈ G₁.vertexSet), ∀ x ∈ η₁v v, ∀ y ∈ η₁v v,
          sameComponent (H₁ ⊔ H₂) x y :=
        fun hv₁ x hx y hy ↦ ((h₁_prop hv₁).2 x hx y hy).mono le_sup_left
      have hsc₂ : ∀ (hv₂ : v ∈ G₂.vertexSet), ∀ x ∈ η₂v v, ∀ y ∈ η₂v v,
          sameComponent (H₁ ⊔ H₂) x y :=
        fun hv₂ x hx y hy ↦ ((h₂_prop hv₂).2 x hx y hy).mono le_sup_right
      rcases mem_glueVertex_iff.mp ha with ⟨hv₁, ha₁⟩ | ⟨hv₂, ha₂⟩ <;>
        rcases mem_glueVertex_iff.mp hb with ⟨hv₁', hb₁⟩ | ⟨hv₂', hb₂⟩
      · exact hsc₁ hv₁ a ha₁ b hb₁
      · have hv_inter : v ∈ (G₁.toHypergraph ∩ G₂.toHypergraph).vertexSet := ⟨hv₁, hv₂'⟩
        rw [← hsep.rootSet_left] at hv_inter
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv_inter
        have hi' : i < G'₁.roots.length := hexp₁.roots_length ▸ hi
        exact (hsc₁ hv₁ a ha₁ G'₁.roots[i] (hexp₁.roots_mem i hi hi')).trans
          (hsc₂ hv₂' G'₁.roots[i] (hroots_mem i hi hi') b hb₂)
      · have hv_inter : v ∈ (G₁.toHypergraph ∩ G₂.toHypergraph).vertexSet := ⟨hv₁', hv₂⟩
        rw [← hsep.rootSet_left] at hv_inter
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv_inter
        have hi' : i < G'₁.roots.length := hexp₁.roots_length ▸ hi
        exact (hsc₂ hv₂ a ha₂ G'₁.roots[i] (hroots_mem i hi hi')).trans
          (hsc₁ hv₁' G'₁.roots[i] (hexp₁.roots_mem i hi hi') b hb₁)
      · exact hsc₂ hv₂ a ha₂ b hb₂

/-! ### Removable patchworks, star-decompositions, and Graph Minors IV, (8.2) -/



open Classical in
private theorem emptySubgraph_mono {X Y : Set α} (h : X ⊆ Y) :
    emptySubgraph X ≤ emptySubgraph Y :=
  ⟨h, fun _ _ hab ↦ False.elim hab⟩

omit [Preorder Ω] in
open Classical in
theorem Patchwork.IsRemovable.restrict {P : Patchwork Ω α β} (hP : P.IsRemovable)
    {G' : RootedHypergraph α β} (hle : G'.toHypergraph ≤ P.G.toHypergraph) :
    (P.restrict G').IsRemovable := by
  intro e he
  change emptySubgraph (G'.ends e) ∈ (P.restrict G').Δ e
  rw [P.restrict_Δ hle he, ← hle.ends_eq e he]
  exact hP e (hle.edgeSet_subset he)

omit [Preorder Ω] in
open Classical in
theorem Patchwork.IsRemovable.deleteEdges {P : Patchwork Ω α β} (hP : P.IsRemovable)
    (F : Set β) : (P.deleteEdges F).IsRemovable := by
  rintro e ⟨he, hneF⟩
  have hends : (P.deleteEdges F).G.ends e = P.G.ends e := by
    ext v
    exact ⟨fun hv ↦ hv.1, fun hv ↦ ⟨hv, hneF⟩⟩
  change emptySubgraph ((P.deleteEdges F).G.ends e) ∈ P.Δ e
  rw [hends]
  exact hP e he

omit [Preorder Ω] in
open Classical in
theorem Patchwork.IsRemovable.emptySubgraph_isRealization {P : Patchwork Ω α β}
    (hP : P.IsRemovable) : P.IsRealization (emptySubgraph P.G.vertexSet) := by
  refine ⟨fun e ↦ emptySubgraph (P.G.ends e), fun e he ↦ hP e he, ?_⟩
  apply le_antisymm le_sup_left
  refine sup_le le_rfl (iSup₂_le fun e _ ↦ emptySubgraph_mono fun _ hv ↦ P.G.vertex_mem_of_inc hv)

open Classical in
theorem exists_isComponent_emptySubgraph_singleton {X : Set α} {x : α} (hx : x ∈ X) :
    ∃ D, IsComponent (emptySubgraph X) D ∧ D.verts = {x} := by
  rw [exists_isComponent_verts_eq_iff (Set.singleton_nonempty x) (Set.singleton_subset_iff.mpr hx)]
  refine ⟨fun _ _ _ hab ↦ False.elim hab, ?_⟩
  rintro a rfl b rfl
  exact sameComponent_iff.mpr ⟨hx, hx, Reachable.refl _⟩

open Classical in
theorem Patchwork.IsRemovable.isRealizableExpansion_of_singleton {P : Patchwork Ω α β}
    {P' : Patchwork Ω α' β'} (hP' : P'.IsRemovable) {ηv : α → Set α'} {ηe : β → β'}
    (hexp : IsExpansion P P' ηv ηe) (hsing : ∀ v ∈ P.G.vertexSet, ∃ v', ηv v = {v'}) :
    IsRealizableExpansion P P' ηv ηe := by
  refine ⟨hexp, emptySubgraph P'.G.vertexSet,
    (hP'.deleteEdges (ηe '' P.G.edgeSet)).emptySubgraph_isRealization, fun v hv ↦ ?_⟩
  obtain ⟨v', hv'⟩ := hsing v hv
  have hv'_mem : v' ∈ P'.G.vertexSet := hexp.vertex_subset v hv (hv' ▸ Set.mem_singleton v')
  rw [hv']
  exact exists_isComponent_emptySubgraph_singleton hv'_mem

open Classical in
theorem Patchwork.IsRemovable.simulated_restrict_of_roots_eq {P' : Patchwork Ω α' β'}
    (hP' : P'.IsRemovable) {G'₀ : RootedHypergraph α' β'}
    (hle : G'₀.toHypergraph ≤ P'.G.toHypergraph) (hroots : G'₀.roots = P'.G.roots) :
    Simulated (P'.restrict G'₀) P' := by
  refine ⟨fun v ↦ {v}, id, hP'.isRealizableExpansion_of_singleton ?_ fun v _ ↦ ⟨v, rfl⟩⟩
  refine
    { vertex_nonempty := fun v _ ↦ Set.singleton_nonempty v
      vertex_subset := fun v hv _ hEq ↦ hEq.symm ▸ hle.vertexSet_subset hv
      edge_mem := fun e he ↦ hle.edgeSet_subset he
      vertex_disjoint := fun _ _ _ _ hne ↦ Set.disjoint_singleton.mpr hne
      edge_injOn := fun _ _ _ _ h ↦ h
      mem_dom_iff := fun e he ↦ by
        rw [P'.restrict_dom hle]
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, he⟩⟩
      ends_nonempty := fun e he _ v hv ↦ by
        refine ⟨v, rfl, ?_⟩
        change v ∈ P'.G.ends e
        rw [hle.ends_eq e he]
        exact hv
      μ_length := fun _ _ ↦ rfl
      μ_mem := fun _ _ _ _ _ ↦ rfl
      roots_length := congrArg List.length hroots
      roots_mem := fun i hi hi' ↦ by
        change P'.G.roots[i] = G'₀.roots[i]
        simp [hroots]
      maps_Δ := fun e he δ hδ ↦ by
        rw [P'.restrict_dom hle] at he
        rw [P'.restrict_Δ hle he.2] at hδ
        have hverts : δ.verts ⊆ {x | x ∈ P'.μ e} := by
          rw [((P'.Δ e).verts_eq δ hδ).trans (P'.Δ_verts e (hle.edgeSet_subset he.2)),
            P'.μ_set e he.1]
        change marchMapSubgraph (P'.μ e) (P'.μ e) δ ∈ (P'.Δ e).groupings
        rwa [marchMapSubgraph_id hverts]
      φ_le := fun _ _ ↦ le_rfl }

open Classical in
@[simp]
private theorem hypergraph_union_vertexSet (G₁ G₂ : Hypergraph α β) :
    (G₁ ∪ G₂).vertexSet = G₁.vertexSet ∪ G₂.vertexSet := rfl

open Classical in
@[simp]
private theorem hypergraph_union_edgeSet (G₁ G₂ : Hypergraph α β) :
    (G₁ ∪ G₂).edgeSet = G₁.edgeSet ∪ G₂.edgeSet := rfl

open Classical in
private theorem hypergraph_union_inc (G₁ G₂ : Hypergraph α β) (e : β) (v : α) :
    (G₁ ∪ G₂).Inc e v ↔ G₁.Inc e v ∨ G₂.Inc e v := Iff.rfl

open Classical in
@[simp]
private theorem hypergraph_inter_vertexSet (G₁ G₂ : Hypergraph α β) :
    (G₁ ∩ G₂).vertexSet = G₁.vertexSet ∩ G₂.vertexSet := rfl

open Classical in
@[simp]
private theorem hypergraph_inter_edgeSet (G₁ G₂ : Hypergraph α β) :
    (G₁ ∩ G₂).edgeSet = G₁.edgeSet ∩ G₂.edgeSet := rfl

open Classical in
theorem Hypergraph.biUnion_insert (s : ι) (A : Finset ι) (f : ι → Hypergraph α β) :
    Hypergraph.biUnion (insert s A) f = f s ∪ Hypergraph.biUnion A f := by
  ext v e
  · simp [Hypergraph.biUnion]
  · simp [Hypergraph.biUnion]
  · simp [Hypergraph.biUnion, hypergraph_union_inc]

open Classical in
theorem Hypergraph.biUnion_singleton (s : ι) (f : ι → Hypergraph α β) :
    Hypergraph.biUnion {s} f = f s := by
  ext v e
  · simp [Hypergraph.biUnion]
  · simp [Hypergraph.biUnion]
  · simp [Hypergraph.biUnion]

open Classical in
theorem Hypergraph.biUnion_ends_eq {G : Hypergraph α β} {C : Finset ι} {f : ι → Hypergraph α β}
    (hle : ∀ t ∈ C, f t ≤ G) {e : β} (he : e ∈ (Hypergraph.biUnion C f).edgeSet) :
    (Hypergraph.biUnion C f).ends e = G.ends e := by
  simp only [Hypergraph.biUnion, Set.mem_iUnion, exists_prop] at he
  obtain ⟨t₀, ht₀, he₀⟩ := he
  ext v
  simp only [Hypergraph.ends, Hypergraph.biUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, hinc⟩
    have he_t : e ∈ (f t).edgeSet := (f t).edge_mem_of_inc hinc
    change v ∈ G.ends e
    rw [(hle t ht).ends_eq e he_t]
    exact hinc
  · intro hv
    refine ⟨t₀, ht₀, ?_⟩
    change v ∈ (f t₀).ends e
    rw [← (hle t₀ ht₀).ends_eq e he₀]
    exact hv

open Classical in
theorem Hypergraph.biUnion_le {G : Hypergraph α β} {C : Finset ι} {f : ι → Hypergraph α β}
    (hle : ∀ t ∈ C, f t ≤ G) : Hypergraph.biUnion C f ≤ G where
  vertexSet_subset := by
    simp only [Hypergraph.biUnion, Set.iUnion_subset_iff]
    exact fun t ht ↦ (hle t ht).vertexSet_subset
  edgeSet_subset := by
    simp only [Hypergraph.biUnion, Set.iUnion_subset_iff]
    exact fun t ht ↦ (hle t ht).edgeSet_subset
  ends_eq _ he := (Hypergraph.biUnion_ends_eq hle he).symm

open Classical in
theorem Hypergraph.biUnion_le_biUnion {G : Hypergraph α β} {A B : Finset ι}
    {f : ι → Hypergraph α β} (hAB : A ⊆ B) (hle : ∀ t ∈ B, f t ≤ G) :
    Hypergraph.biUnion A f ≤ Hypergraph.biUnion B f where
  vertexSet_subset := Set.biUnion_mono hAB fun _ _ ↦ subset_rfl
  edgeSet_subset := Set.biUnion_mono hAB fun _ _ ↦ subset_rfl
  ends_eq e he := by
    have heB : e ∈ (Hypergraph.biUnion B f).edgeSet :=
      Set.biUnion_mono hAB (fun _ _ ↦ subset_rfl) he
    rw [Hypergraph.biUnion_ends_eq hle heB,
      Hypergraph.biUnion_ends_eq (fun t ht ↦ hle t (hAB ht)) he]

open Classical in
theorem cross_empty (σ : ι → RootedHypergraph α β) (r : ι) :
    cross σ ∅ r = σ r := by
  have hins : insert r (∅ : Finset ι) = {r} := rfl
  cases h : σ r with
  | mk toH roots nodup sub =>
    simp only [cross, hins, Hypergraph.biUnion_singleton, h]

open Classical in
theorem cross_verts_of_isTreeDecomposition {G : RootedHypergraph α β} {S : RootedTree ι}
    {σ : ι → RootedHypergraph α β} (htd : IsTreeDecomposition G S σ) :
    cross σ S.verts S.root = G := by
  have hins : insert S.root S.verts = S.verts := Finset.insert_eq_of_mem S.root_mem
  cases G with
  | mk toH roots nodup sub =>
    simp only [cross, hins, htd.biUnion_eq, htd.roots_root]

open Classical in
theorem cross_edges_of_isTreeDecomposition {G : RootedHypergraph α β} {S : RootedTree ι}
    {σ : ι → RootedHypergraph α β} (htd : IsTreeDecomposition G S σ) :
    cross σ S.edges S.root = G := by
  have hins : insert S.root S.edges = S.verts := Finset.insert_erase S.root_mem
  cases G with
  | mk toH roots nodup sub =>
    simp only [cross, hins, htd.biUnion_eq, htd.roots_root]

open Classical in
theorem cross_le_of_subset {G : RootedHypergraph α β} {S : RootedTree ι}
    {σ : ι → RootedHypergraph α β} (htd : IsTreeDecomposition G S σ)
    {F₁ F₂ : Finset ι} (h₁₂ : F₁ ⊆ F₂) (h₂ : F₂ ⊆ S.edges) :
    (cross σ F₁ S.root).toHypergraph ≤ (cross σ F₂ S.root).toHypergraph := by
  refine Hypergraph.biUnion_le_biUnion (G := G.toHypergraph)
    (Finset.insert_subset_insert S.root h₁₂) ?_
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht₂
  · exact htd.le S.root S.root_mem
  · exact htd.le t (Finset.mem_of_mem_erase (h₂ ht₂))

open Classical in
theorem cross_le_of_isTreeDecomposition {G : RootedHypergraph α β} {S : RootedTree ι}
    {σ : ι → RootedHypergraph α β} (htd : IsTreeDecomposition G S σ)
    {F : Finset ι} (hF : F ⊆ S.edges) :
    (cross σ F S.root).toHypergraph ≤ G.toHypergraph := by
  apply Hypergraph.biUnion_le
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | htF
  · exact htd.le S.root S.root_mem
  · exact htd.le t (Finset.mem_of_mem_erase (hF htF))

open Classical in
theorem isStar_reaches_iff {S : RootedTree ι} (hstar : S.IsStar) {s : ι} (hs : s ∈ S.edges)
    {x : ι} : S.Reaches x s ↔ x = s ∨ x = S.root := by
  have hs_verts : s ∈ S.verts := Finset.mem_of_mem_erase hs
  constructor
  · rintro ⟨_, n, hn⟩
    cases n with
    | zero => exact Or.inl hn.symm
    | succ m =>
      rw [Function.iterate_succ_apply, hstar s hs, Function.iterate_fixed S.parent_root m] at hn
      exact Or.inr hn.symm
  · rintro (rfl | rfl)
    · exact ⟨hs_verts, 0, rfl⟩
    · exact ⟨hs_verts, 1, hstar s hs⟩

open Classical in
theorem isStar_onPath_root {S : RootedTree ι} (hstar : S.IsStar) {s t : ι}
    (hs : s ∈ S.edges) (ht : t ∈ S.edges) (hne : s ≠ t) :
    S.OnPath s t S.root := by
  refine ⟨Or.inl ((isStar_reaches_iff hstar hs).mpr (Or.inr rfl)), fun x hxs hxt ↦ ?_⟩
  rcases (isStar_reaches_iff hstar hs).mp hxs with rfl | rfl
  · rcases (isStar_reaches_iff hstar ht).mp hxt with hst | hxroot
    · exact absurd hst hne
    · subst hxroot
      exact ⟨S.root_mem, 0, rfl⟩
  · exact ⟨S.root_mem, 0, rfl⟩

open Classical in
theorem isSeparation_cross_insert {G : RootedHypergraph α β} {S : RootedTree ι}
    {σ : ι → RootedHypergraph α β} (hstar : S.IsStar) (htd : IsTreeDecomposition G S σ)
    {F : Finset ι} (hF : F ⊆ S.edges) {s : ι} (hs : s ∈ S.edges) (hsF : s ∉ F) :
    (cross σ (insert s F) S.root).IsSeparation (σ s) (cross σ F S.root) := by
  have hs_verts : s ∈ S.verts := Finset.mem_of_mem_erase hs
  have hsub : insert S.root (insert s F) ⊆ S.verts :=
    Finset.insert_subset_iff.mpr ⟨S.root_mem,
      Finset.insert_subset_iff.mpr ⟨hs_verts, fun x hx ↦ Finset.mem_of_mem_erase (hF hx)⟩⟩
  have hle_all : ∀ t ∈ insert S.root (insert s F), (σ t).toHypergraph ≤ G.toHypergraph :=
    fun t ht ↦ htd.le t (hsub ht)
  refine
    { isSeparation :=
        { left_le := by
            rw [← Hypergraph.biUnion_singleton s (fun t ↦ (σ t).toHypergraph)]
            refine Hypergraph.biUnion_le_biUnion ?_ hle_all
            simp
          right_le := cross_le_of_subset htd (Finset.subset_insert s F)
            (Finset.insert_subset_iff.mpr ⟨hs, hF⟩)
          union_eq := by
            change (σ s).toHypergraph ∪
                Hypergraph.biUnion (insert S.root F) (fun t ↦ (σ t).toHypergraph) =
              Hypergraph.biUnion (insert S.root (insert s F)) (fun t ↦ (σ t).toHypergraph)
            rw [← Hypergraph.biUnion_insert s (insert S.root F) (fun t ↦ (σ t).toHypergraph),
              Finset.insert_comm]
          edgeSet_inter_eq := by
            ext e
            simp only [hypergraph_inter_edgeSet, cross, Hypergraph.biUnion, Set.mem_inter_iff,
              Set.mem_iUnion, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
            intro hes t ht het
            have ht_verts : t ∈ S.verts := by
              rcases Finset.mem_insert.mp ht with rfl | htF
              · exact S.root_mem
              · exact Finset.mem_of_mem_erase (hF htF)
            have hne : s ≠ t := by
              rintro rfl
              rcases Finset.mem_insert.mp ht with hs_root | hsF'
              · exact Finset.ne_of_mem_erase hs hs_root
              · exact hsF hsF'
            have hempty := htd.edgeSet_inter_eq s hs_verts t ht_verts hne
            have he_inter : e ∈ ((σ s).toHypergraph ∩ (σ t).toHypergraph).edgeSet := ⟨hes, het⟩
            rw [hempty] at he_inter
            exact he_inter }
      roots_right := rfl
      rootSet_left := by
        rw [htd.rootSet_edge s hs, hstar s hs]
        ext v
        simp only [hypergraph_inter_vertexSet, cross, Hypergraph.biUnion, Set.mem_inter_iff,
          Set.mem_iUnion, exists_prop]
        refine ⟨fun ⟨hvs, hvr⟩ ↦ ⟨hvs, S.root, Finset.mem_insert_self _ _, hvr⟩, ?_⟩
        rintro ⟨hvs, t, ht, hvt⟩
        refine ⟨hvs, ?_⟩
        rcases Finset.mem_insert.mp ht with rfl | htF
        · exact hvt
        · have ht_edges : t ∈ S.edges := hF htF
          have hne : s ≠ t := fun h ↦ hsF (h ▸ htF)
          have hOnPath := isStar_onPath_root hstar hs ht_edges hne
          exact (htd.inter_le s hs_verts S.root S.root_mem t
            (Finset.mem_of_mem_erase ht_edges) hOnPath).vertexSet_subset ⟨hvs, hvt⟩ }

open Classical in
/-- Given a star `S` and a subset `U ⊆ S.edges`, the sub-star with vertex set `{o(S)} ∪ U`. -/
noncomputable def subStar (S : RootedTree ι) (hstar : S.IsStar) (U : Finset ι)
    (hU : U ⊆ S.edges) : RootedTree ι where
  verts := by classical exact insert S.root U
  root := S.root
  parent := S.parent
  root_mem := by classical exact Finset.mem_insert_self S.root U
  parent_mem v hv := by
    classical
    rcases Finset.mem_insert.mp hv with rfl | hvU
    · rw [S.parent_root]
      exact Finset.mem_insert_self S.root U
    · rw [hstar v (hU hvU)]
      exact Finset.mem_insert_self S.root U
  parent_root := S.parent_root
  exists_iterate_eq_root v hv := by
    classical
    rcases Finset.mem_insert.mp hv with rfl | hvU
    · exact ⟨0, rfl⟩
    · exact ⟨1, hstar v (hU hvU)⟩

open Classical in
theorem subStar_edges {S : RootedTree ι} (hstar : S.IsStar) {U : Finset ι} (hU : U ⊆ S.edges) :
    (subStar S hstar U hU).edges = U := by
  classical
  have hnot : S.root ∉ U := fun h ↦ Finset.notMem_erase S.root S.verts (hU h)
  change (insert S.root U).erase S.root = U
  exact Finset.erase_insert hnot

open Classical in
theorem subStar_isStar {S : RootedTree ι} (hstar : S.IsStar) {U : Finset ι} (hU : U ⊆ S.edges) :
    (subStar S hstar U hU).IsStar := by
  intro v hv
  rw [subStar_edges hstar hU] at hv
  exact hstar v (hU hv)

open Classical in
/-- Base step of Graph Minors IV, (8.2) (page 249): `η₀(v) = {γ(v)}`, `η₀(e) = α(e)` is a
realizable expansion of `P | σ(o(S))` in `P' | σ'(o(S'))`. -/
theorem theorem_8_2_root {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    (hP' : P'.IsRemovable)
    {S : RootedTree ι} {σ : ι → RootedHypergraph α β}
    {S' : RootedTree ι'} {σ' : ι' → RootedHypergraph α' β'}
    (htd : IsTreeDecomposition P.G S σ) (htd' : IsTreeDecomposition P'.G S' σ')
    {γ : α → α'} (hγ_maps : Set.MapsTo γ (σ S.root).vertexSet (σ' S'.root).vertexSet)
    (hγ_inj : Set.InjOn γ (σ S.root).vertexSet)
    (hγ_roots : P'.G.roots = P.G.roots.map γ)
    {αe : β → β'} (hα_maps : Set.MapsTo αe (σ S.root).edgeSet (σ' S'.root).edgeSet)
    (hα_inj : Set.InjOn αe (σ S.root).edgeSet)
    (hα_dom : ∀ e ∈ (σ S.root).edgeSet, αe e ∈ P'.dom ↔ e ∈ P.dom)
    (hα_μ : ∀ e ∈ (σ S.root).edgeSet, e ∈ P.dom →
      P'.μ (αe e) = (P.μ e).map γ ∧
        Set.MapsTo (marchMapSubgraph (P.μ e) (P'.μ (αe e)))
          (P.Δ e).groupings (P'.Δ (αe e)).groupings)
    (hα_ends : ∀ e ∈ (σ S.root).edgeSet, e ∉ P.dom →
      ∀ v ∈ P.G.ends e, γ v ∈ P'.G.ends (αe e))
    (hα_φ : ∀ e ∈ (σ S.root).edgeSet, P.φ e ≤ P'.φ (αe e)) :
    IsRealizableExpansion (P.restrict (σ S.root)) (P'.restrict (σ' S'.root))
      (fun v ↦ {γ v}) αe := by
  have hle : (σ S.root).toHypergraph ≤ P.G.toHypergraph := htd.le S.root S.root_mem
  have hle' : (σ' S'.root).toHypergraph ≤ P'.G.toHypergraph := htd'.le S'.root S'.root_mem
  have hrem₀ : (P'.restrict (σ' S'.root)).IsRemovable := hP'.restrict hle'
  refine hrem₀.isRealizableExpansion_of_singleton ?_ fun v _ ↦ ⟨γ v, rfl⟩
  refine
    { vertex_nonempty := fun v _ ↦ Set.singleton_nonempty (γ v)
      vertex_subset := fun v hv _ hEq ↦ hEq.symm ▸ hγ_maps hv
      edge_mem := fun e he ↦ hα_maps he
      vertex_disjoint := fun v₁ hv₁ v₂ hv₂ hne ↦
        Set.disjoint_singleton.mpr fun hEq ↦ hne (hγ_inj hv₁ hv₂ hEq)
      edge_injOn := hα_inj
      mem_dom_iff := fun e he ↦ by
        rw [P.restrict_dom hle, P'.restrict_dom hle']
        exact ⟨fun ⟨hd, _⟩ ↦ ⟨(hα_dom e he).mpr hd, hα_maps he⟩,
          fun ⟨hd', _⟩ ↦ ⟨(hα_dom e he).mp hd', he⟩⟩
      ends_nonempty := fun e he hnd v hinc ↦ by
        rw [P.restrict_dom hle] at hnd
        have hndP : e ∉ P.dom := fun hd ↦ hnd ⟨hd, he⟩
        have hincP : v ∈ P.G.ends e := by
          rw [hle.ends_eq e he]
          exact hinc
        refine ⟨γ v, rfl, ?_⟩
        change γ v ∈ (σ' S'.root).ends (αe e)
        rw [← hle'.ends_eq (αe e) (hα_maps he)]
        exact hα_ends e he hndP v hincP
      μ_length := fun e he ↦ by
        rw [P.restrict_dom hle] at he
        have hμ := (hα_μ e he.2 he.1).1
        change (P.μ e).length = (P'.μ (αe e)).length
        rw [hμ, List.length_map]
      μ_mem := fun e he i hi hi' ↦ by
        rw [P.restrict_dom hle] at he
        have hμ := (hα_μ e he.2 he.1).1
        change (P'.μ (αe e))[i] ∈ {γ (P.μ e)[i]}
        simp only [Set.mem_singleton_iff, hμ, List.getElem_map]
        rfl
      roots_length := by
        change (σ S.root).roots.length = (σ' S'.root).roots.length
        rw [htd.roots_root, htd'.roots_root, hγ_roots, List.length_map]
      roots_mem := fun i hi hi' ↦ by
        change (σ' S'.root).roots[i] ∈ {γ (σ S.root).roots[i]}
        simp only [Set.mem_singleton_iff, htd.roots_root, htd'.roots_root, hγ_roots,
          List.getElem_map]
      maps_Δ := fun e he ↦ by
        rw [P.restrict_dom hle] at he
        rw [P.restrict_Δ hle he.2, P'.restrict_Δ hle' (hα_maps he.2)]
        exact (hα_μ e he.2 he.1).2
      φ_le := fun e he ↦ hα_φ e he }

open Classical in
/-- Inductive step of Graph Minors IV, (8.2) (page 249): for every subset `F ⊆ U(S)` of tips of
`S`, there is a realizable expansion `ζ` of `P | (σ × S_F)` in `P' | (σ' × S'_{β(F)})` such that
`γ(v) ∈ ζ(v)` for all `v ∈ V(σ(o(S)))`. -/
theorem theorem_8_2_subset {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    (hP' : P'.IsRemovable)
    {S : RootedTree ι} {σ : ι → RootedHypergraph α β}
    {S' : RootedTree ι'} {σ' : ι' → RootedHypergraph α' β'}
    (hstar : S.IsStar) (htd : IsTreeDecomposition P.G S σ)
    (hstar' : S'.IsStar) (htd' : IsTreeDecomposition P'.G S' σ')
    {γ : α → α'} (hγ_maps : Set.MapsTo γ (σ S.root).vertexSet (σ' S'.root).vertexSet)
    (hγ_inj : Set.InjOn γ (σ S.root).vertexSet)
    (hγ_roots : P'.G.roots = P.G.roots.map γ)
    {αe : β → β'} (hα_maps : Set.MapsTo αe (σ S.root).edgeSet (σ' S'.root).edgeSet)
    (hα_inj : Set.InjOn αe (σ S.root).edgeSet)
    (hα_dom : ∀ e ∈ (σ S.root).edgeSet, αe e ∈ P'.dom ↔ e ∈ P.dom)
    (hα_μ : ∀ e ∈ (σ S.root).edgeSet, e ∈ P.dom →
      P'.μ (αe e) = (P.μ e).map γ ∧
        Set.MapsTo (marchMapSubgraph (P.μ e) (P'.μ (αe e)))
          (P.Δ e).groupings (P'.Δ (αe e)).groupings)
    (hα_ends : ∀ e ∈ (σ S.root).edgeSet, e ∉ P.dom →
      ∀ v ∈ P.G.ends e, γ v ∈ P'.G.ends (αe e))
    (hα_φ : ∀ e ∈ (σ S.root).edgeSet, P.φ e ≤ P'.φ (αe e))
    {βf : ι → ι'} (hβ_maps : Set.MapsTo βf (S.edges : Set ι) (S'.edges : Set ι'))
    (hβ_inj : Set.InjOn βf (S.edges : Set ι))
    (hβ_roots : ∀ s ∈ S.edges, (σ' (βf s)).roots = (σ s).roots.map γ)
    (hβ_sim : ∀ s ∈ S.edges, Simulated (P.restrict (σ s)) (P'.restrict (σ' (βf s))))
    (F : Finset ι) (hF : F ⊆ S.edges) :
    ∃ (ζv : α → Set α') (ζe : β → β'),
      IsRealizableExpansion
        (P.restrict (cross σ F S.root))
        (P'.restrict (cross σ' (by classical exact F.image βf) S'.root))
        ζv ζe ∧
      ∀ v ∈ (σ S.root).vertexSet, γ v ∈ ζv v := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨fun v ↦ {γ v}, αe, ?_, fun v _ ↦ rfl⟩
    rw [Finset.image_empty, cross_empty, cross_empty]
    exact theorem_8_2_root hP' htd htd' hγ_maps hγ_inj hγ_roots
      hα_maps hα_inj hα_dom hα_μ hα_ends hα_φ
  | @insert s F hsF ih =>
    have hs : s ∈ S.edges := hF (Finset.mem_insert_self s F)
    have hF_sub : F ⊆ S.edges := (Finset.subset_insert s F).trans hF
    obtain ⟨ζv, ζe, hζ, hζ_root⟩ := ih hF_sub
    obtain ⟨η₁v, η₁e, hη₁⟩ := hβ_sim s hs
    have hF'_sub : F.image βf ⊆ S'.edges := by
      intro s' hs'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs'
      exact hβ_maps (hF_sub ht)
    have hbs : βf s ∈ S'.edges := hβ_maps hs
    have hbsF' : βf s ∉ F.image βf := by
      intro hmem
      obtain ⟨t, ht, hEq⟩ := Finset.mem_image.mp hmem
      exact hsF (hβ_inj (hF_sub ht) hs hEq ▸ ht)
    have hsep := isSeparation_cross_insert hstar htd hF_sub hs hsF
    have hsep' := isSeparation_cross_insert hstar' htd' hF'_sub hbs hbsF'
    let G_next := cross σ (insert s F) S.root
    let G'_next := cross σ' (insert (βf s) (F.image βf)) S'.root
    have hle_next : G_next.toHypergraph ≤ P.G.toHypergraph :=
      cross_le_of_isTreeDecomposition htd hF
    have hle'_next : G'_next.toHypergraph ≤ P'.G.toHypergraph :=
      cross_le_of_isTreeDecomposition htd' (Finset.insert_subset_iff.mpr ⟨hbs, hF'_sub⟩)
    have hη₁' : IsRealizableExpansion
        ((P.restrict G_next).restrict (σ s))
        ((P'.restrict G'_next).restrict (σ' (βf s))) η₁v η₁e :=
      hη₁.congr
        (Patchwork.agrees_restrict_restrict hle_next hsep.isSeparation.left_le).symm
        (Patchwork.agrees_restrict_restrict hle'_next hsep'.isSeparation.left_le).symm
    have hζ' : IsRealizableExpansion
        ((P.restrict G_next).restrict (cross σ F S.root))
        ((P'.restrict G'_next).restrict (cross σ' (F.image βf) S'.root)) ζv ζe :=
      hζ.congr
        (Patchwork.agrees_restrict_restrict hle_next hsep.isSeparation.right_le).symm
        (Patchwork.agrees_restrict_restrict hle'_next hsep'.isSeparation.right_le).symm
    have hroots_mem : ∀ (i : ℕ) (hi : i < (σ s).roots.length)
        (hi' : i < (σ' (βf s)).roots.length),
        (σ' (βf s)).roots[i] ∈ ζv (σ s).roots[i] := by
      intro i hi hi'
      have hvi_root : (σ s).roots[i] ∈ (σ S.root).vertexSet := by
        have hmem : (σ s).roots[i] ∈ (σ s).rootSet := List.getElem_mem hi
        rw [htd.rootSet_edge s hs, hstar s hs] at hmem
        exact hmem.2
      have hEq : (σ' (βf s)).roots[i] = γ (σ s).roots[i] := by
        simp [hβ_roots s hs]
      rw [hEq]
      exact hζ_root (σ s).roots[i] hvi_root
    have hglued := theorem_8_1_proof hsep hsep' hη₁' hζ' hroots_mem
    rw [Finset.image_insert]
    refine ⟨glueVertex (σ s) (cross σ F S.root) η₁v ζv, glueEdge (σ s) η₁e ζe, hglued,
      fun v hv ↦ ?_⟩
    have hv_in_F : v ∈ (cross σ F S.root).vertexSet :=
      Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_self S.root F)) hv
    exact mem_glueVertex_iff.mpr (Or.inr ⟨hv_in_F, hζ_root v hv⟩)

open Classical in
/-- **Graph Minors IV, (8.2)** (pages 248–249):
"Let $P = (G, \mu, \Delta, \phi)$, $P' = (G', \mu', \Delta', \phi')$ be $\Omega$-patchworks
where $P'$ is removable. Let $(S, \sigma)$, $(S', \sigma')$ be star-decompositions of $G$,
$G'$, respectively. Let $\gamma$ be a bijection from $V(\sigma(o(S)))$ to
$V(\sigma'(o(S')))$ mapping $\pi(G)$ to $\pi(G')$. Let $\alpha$ be an injection from
$E(\sigma(o(S)))$ into $E(\sigma'(o(S')))$, such that for each $e \in E(\sigma(o(S)))$* (i)
*$\alpha(e) \in \operatorname{dom}(\mu')$ if and only if $e \in \operatorname{dom}(\mu)$*
(ii) *if $e \in \operatorname{dom}(\mu)$ then $\gamma$ maps $\mu(e)$ to $\mu'(\alpha(e))$
... (iii) *if $e \notin \operatorname{dom}(\mu)$ then $\gamma$ maps $V_G(e)$ to
$V_{G'}(\alpha(e))$* (iv) *$\phi(e) \le \phi'(\alpha(e))$.* ... *Let $\beta$ be a bijection from
$U(S)$ to $U(S')$, such that for each $s \in U(S)$,* (v) *$\gamma$ maps $\pi(\sigma(s))$ to
$\pi(\sigma'(\beta(s)))$* (vi) *$P | \sigma(s)$ is simulated in $P' | \sigma'(\beta(s))$.*
*Then $P$ is simulated in $P'$."

Note on condition (ii): the paper omits '`μ(e) → μ'(α(e))` maps `Δ(e)` to `Δ'(α(e))`' in the
statement of (8.2)(ii), which is required for `η₀` to satisfy condition (viii) of an expansion;
in the proof of (8.4) (page 250, claims (4) and (6)(ii)), the paper explicitly establishes
`Δᵢ(e) = Δ_{i'}(α(e))` before invoking (8.2). -/
theorem theorem_8_2_proof {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    (hP' : P'.IsRemovable)
    {S : RootedTree ι} {σ : ι → RootedHypergraph α β}
    {S' : RootedTree ι'} {σ' : ι' → RootedHypergraph α' β'}
    (hstar : S.IsStar) (htd : IsTreeDecomposition P.G S σ)
    (hstar' : S'.IsStar) (htd' : IsTreeDecomposition P'.G S' σ')
    {γ : α → α'} (hγ_bij : Set.BijOn γ (σ S.root).vertexSet (σ' S'.root).vertexSet)
    (hγ_roots : P'.G.roots = P.G.roots.map γ)
    {αe : β → β'} (hα_maps : Set.MapsTo αe (σ S.root).edgeSet (σ' S'.root).edgeSet)
    (hα_inj : Set.InjOn αe (σ S.root).edgeSet)
    (hα_dom : ∀ e ∈ (σ S.root).edgeSet, αe e ∈ P'.dom ↔ e ∈ P.dom)
    (hα_μ : ∀ e ∈ (σ S.root).edgeSet, e ∈ P.dom →
      P'.μ (αe e) = (P.μ e).map γ ∧
        Set.MapsTo (marchMapSubgraph (P.μ e) (P'.μ (αe e)))
          (P.Δ e).groupings (P'.Δ (αe e)).groupings)
    (hα_ends : ∀ e ∈ (σ S.root).edgeSet, e ∉ P.dom →
      γ '' P.G.ends e = P'.G.ends (αe e))
    (hα_φ : ∀ e ∈ (σ S.root).edgeSet, P.φ e ≤ P'.φ (αe e))
    {βf : ι → ι'} (hβ_bij : Set.BijOn βf (S.edges : Set ι) (S'.edges : Set ι'))
    (hβ_roots : ∀ s ∈ S.edges, (σ' (βf s)).roots = (σ s).roots.map γ)
    (hβ_sim : ∀ s ∈ S.edges, Simulated (P.restrict (σ s)) (P'.restrict (σ' (βf s)))) :
    Simulated P P' := by
  classical
  have hα_ends' : ∀ e ∈ (σ S.root).edgeSet, e ∉ P.dom →
      ∀ v ∈ P.G.ends e, γ v ∈ P'.G.ends (αe e) := by
    intro e he hnd v hv
    rw [← hα_ends e he hnd]
    exact ⟨v, hv, rfl⟩
  obtain ⟨ζv, ζe, hζ, _⟩ :=
    theorem_8_2_subset hP' hstar htd hstar' htd' hγ_bij.mapsTo hγ_bij.injOn hγ_roots
      hα_maps hα_inj hα_dom hα_μ hα_ends' hα_φ hβ_bij.mapsTo hβ_bij.injOn hβ_roots hβ_sim
      S.edges subset_rfl
  have himg : S.edges.image βf = S'.edges := by
    apply Finset.coe_injective
    rw [Finset.coe_image]
    exact hβ_bij.image_eq
  rw [himg, cross_edges_of_isTreeDecomposition htd, cross_edges_of_isTreeDecomposition htd'] at hζ
  exact ⟨ζv, ζe, hζ.congr (Patchwork.agrees_restrict_self P) (Patchwork.agrees_restrict_self P')⟩

end GraphMinor.GM04
