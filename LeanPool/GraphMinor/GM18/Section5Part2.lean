/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM18.Section5Part1

/-!
# Graph Minors XVIII, Section 5 (Part 2): Place Hearts and Enlargements by Tree-Width (5.5)

This file formalizes (5.5) (pages 95–98) of Robertson and Seymour,
*Graph Minors. XVIII. Tree-decompositions and well-quasi-ordering*, J. Combin. Theory Ser. B 89
(2003) 77–108, together with its six claims `lemma_5_5_claim_1`–`lemma_5_5_claim_6` and general
constructions for hearts of partial `Ω`-places (`mkPlaceHeart`).
-/

public section

namespace GraphMinor.GM18

open Hypergraph SimpleGraph

universe u v w

variable {α : Type u} {β : Type v} {Ω : Type w}

/-! ## General construction and equivalence of place hearts -/

/-- From any `IsPlaceHeart P ℒ newEdge P'`, the underlying unlabeled patchworks satisfy
`IsPatchworkHeart P.toUnlabeled ℒ newEdge P'.toUnlabeled`. -/
theorem IsPlaceHeart.toIsPatchworkHeart {P P' : PartialPatchwork Ω α β}
    {ℒ : Set (RootedHypergraph α β)} {newEdge : RootedHypergraph α β → β}
    (h : IsPlaceHeart P ℒ newEdge P') :
    IsPatchworkHeart P.toUnlabeled ℒ newEdge P'.toUnlabeled where
  isRootedLocation := h.isRootedLocation
  injOn_newEdge := h.injOn_newEdge
  newEdge_notMem_core := h.newEdge_notMem_core
  vertexSet_eq := h.vertexSet_eq
  edgeSet_eq := h.edgeSet_eq
  roots_eq := h.roots_eq
  ends_core := h.ends_core
  ends_newEdge := h.ends_newEdge
  dom_eq := h.dom_eq
  μ_core := h.μ_core
  μ_newEdge := h.μ_newEdge
  Δ_core := h.Δ_core
  Δ_newEdge := h.Δ_newEdge

/-- `feasibleGroupings P.toUnlabeled = feasibleGroupings P`. -/
@[simp] theorem feasibleGroupings_toUnlabeled (P : GM04.Patchwork Ω α β) :
    feasibleGroupings P.toUnlabeled = feasibleGroupings P := rfl

/-- Version of `theorem_5_4_proof` for `IsPlaceHeart` on `PartialPatchwork`. -/
theorem theorem_5_4_place {P P' : PartialPatchwork Ω α β}
    {ℒ : Set (RootedHypergraph α β)} {newEdge : RootedHypergraph α β → β}
    (hP' : IsPlaceHeart P ℒ newEdge P') :
    P.G.vertexSet \ P.G.rootSet =
      (P'.G.vertexSet \ P'.G.rootSet) ∪ (⋃ A ∈ ℒ, A.vertexSet \ A.rootSet) ∧
    feasibleGroupings P = feasibleGroupings P' :=
  theorem_5_4_proof hP'.toIsPatchworkHeart

/-- Extensionality for `RootedHypergraph`: two rooted hypergraphs with the same `toHypergraph` and
`roots` are equal. -/
theorem RootedHypergraph.ext_iff {G₁ G₂ : RootedHypergraph α β} :
    G₁ = G₂ ↔ G₁.toHypergraph = G₂.toHypergraph ∧ G₁.roots = G₂.roots := by
  cases G₁
  cases G₂
  simp

theorem RootedHypergraph.ext {G₁ G₂ : RootedHypergraph α β}
    (hH : G₁.toHypergraph = G₂.toHypergraph) (hr : G₁.roots = G₂.roots) :
    G₁ = G₂ :=
  RootedHypergraph.ext_iff.2 ⟨hH, hr⟩

/-- Two hypergraphs with the same `vertexSet`, `edgeSet`, and `ends` on `edgeSet` are equal. -/
theorem hypergraph_ext_of_ends_eq {H₁ H₂ : Hypergraph α β}
    (hV : H₁.vertexSet = H₂.vertexSet) (hE : H₁.edgeSet = H₂.edgeSet)
    (hends : ∀ e ∈ H₁.edgeSet, H₁.ends e = H₂.ends e) :
    H₁ = H₂ := by
  apply Hypergraph.ext hV hE
  ext e v
  constructor
  · intro hinc
    have he : e ∈ H₁.edgeSet := H₁.edge_mem_of_inc hinc
    change v ∈ H₂.ends e
    rw [← hends e he]
    exact hinc
  · intro hinc
    have he : e ∈ H₁.edgeSet := hE.symm ▸ H₂.edge_mem_of_inc hinc
    change v ∈ H₁.ends e
    rw [hends e he]
    exact hinc

/-- Equivalence of `Ω`-patchworks in the sense of the paper (`G₁ = G₂`, `dom(μ₁) = dom(μ₂)`,
`μ₁(e) = μ₂(e)` for `e ∈ dom(μ₁)`, `Δ₁(e) = Δ₂(e)` and `φ₁(e) = φ₂(e)` for `e ∈ E(G₁)`). -/
structure PatchworkEquiv (P₁ P₂ : GM04.Patchwork Ω α β) : Prop where
  G_eq : P₁.G = P₂.G
  dom_eq : P₁.dom = P₂.dom
  μ_eq : ∀ ⦃e⦄, e ∈ P₁.dom → P₁.μ e = P₂.μ e
  Δ_eq : ∀ ⦃e⦄, e ∈ P₁.G.edgeSet → P₁.Δ e = P₂.Δ e
  φ_eq : ∀ ⦃e⦄, e ∈ P₁.G.edgeSet → P₁.φ e = P₂.φ e

theorem PatchworkEquiv.refl (P : GM04.Patchwork Ω α β) : PatchworkEquiv P P where
  G_eq := rfl
  dom_eq := rfl
  μ_eq _ _ := rfl
  Δ_eq _ _ := rfl
  φ_eq _ _ := rfl

theorem PatchworkEquiv.symm {P₁ P₂ : GM04.Patchwork Ω α β} (h : PatchworkEquiv P₁ P₂) :
    PatchworkEquiv P₂ P₁ where
  G_eq := h.G_eq.symm
  dom_eq := h.dom_eq.symm
  μ_eq _ he := (h.μ_eq (h.dom_eq.symm ▸ he)).symm
  Δ_eq _ he := (h.Δ_eq (h.G_eq.symm ▸ he)).symm
  φ_eq _ he := (h.φ_eq (h.G_eq.symm ▸ he)).symm

theorem PatchworkEquiv.trans {P₁ P₂ P₃ : GM04.Patchwork Ω α β}
    (h₁₂ : PatchworkEquiv P₁ P₂) (h₂₃ : PatchworkEquiv P₂ P₃) :
    PatchworkEquiv P₁ P₃ where
  G_eq := h₁₂.G_eq.trans h₂₃.G_eq
  dom_eq := h₁₂.dom_eq.trans h₂₃.dom_eq
  μ_eq _ he := (h₁₂.μ_eq he).trans (h₂₃.μ_eq (h₁₂.dom_eq ▸ he))
  Δ_eq _ he := (h₁₂.Δ_eq he).trans (h₂₃.Δ_eq (h₁₂.G_eq ▸ he))
  φ_eq _ he := (h₁₂.φ_eq he).trans (h₂₃.φ_eq (h₁₂.G_eq ▸ he))

theorem PatchworkEquiv.feasibleGroupings_eq {P₁ P₂ : GM04.Patchwork Ω α β}
    (h : PatchworkEquiv P₁ P₂) :
    feasibleGroupings P₁ = feasibleGroupings P₂ := by
  let _ : Preorder Unit := inferInstance
  exact feasibleGroupings_eq_of_edge_bij P₁.toUnlabeled P₂.toUnlabeled id
    (congrArg (fun G : RootedHypergraph α β ↦ G.vertexSet) h.G_eq)
    (congrArg RootedHypergraph.rootSet h.G_eq)
    (by rw [Set.image_id]; exact congrArg (fun G : RootedHypergraph α β ↦ G.edgeSet) h.G_eq)
    Function.injective_id.injOn
    (fun _ he ↦ (h.Δ_eq he).symm)

theorem PatchworkEquiv.isExpansion_congr [Preorder Ω] {α' β' : Type*}
    {P₁ P₂ : GM04.Patchwork Ω α β} {P'₁ P'₂ : GM04.Patchwork Ω α' β'}
    {ηv : α → Set α'} {ηe : β → β'}
    (hP : PatchworkEquiv P₁ P₂) (hP' : PatchworkEquiv P'₁ P'₂)
    (h : GM04.IsExpansion P₁ P'₁ ηv ηe) :
    GM04.IsExpansion P₂ P'₂ ηv ηe where
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
    have he'₁ : ηe e ∈ P'₁.dom := (h.mem_dom_iff e heE₁).1 he₁
    rw [← hP.μ_eq he₁, ← hP'.μ_eq he'₁]
    exact h.μ_length e he₁
  μ_mem e he i hi hi' := by
    have he₁ : e ∈ P₁.dom := hP.dom_eq.symm ▸ he
    have heE₁ : e ∈ P₁.G.edgeSet := P₁.dom_subset he₁
    have he'₁ : ηe e ∈ P'₁.dom := (h.mem_dom_iff e heE₁).1 he₁
    have hi₁ : i < (P₁.μ e).length := (hP.μ_eq he₁).symm ▸ hi
    have hi'₁ : i < (P'₁.μ (ηe e)).length := (hP'.μ_eq he'₁).symm ▸ hi'
    have hmem := h.μ_mem e he₁ i hi₁ hi'₁
    simpa [hP.μ_eq he₁, hP'.μ_eq he'₁] using hmem
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
    have he'₁ : ηe e ∈ P'₁.dom := (h.mem_dom_iff e heE₁).1 he₁
    have he'E₁ : ηe e ∈ P'₁.G.edgeSet := h.edge_mem e heE₁
    rw [← hP.μ_eq he₁, ← hP'.μ_eq he'₁, ← hP.Δ_eq heE₁, ← hP'.Δ_eq he'E₁]
    exact h.maps_Δ e he₁
  φ_le e he := by
    have heE₁ : e ∈ P₁.G.edgeSet := hP.G_eq.symm ▸ he
    have he'E₁ : ηe e ∈ P'₁.G.edgeSet := h.edge_mem e heE₁
    rw [← hP.φ_eq heE₁, ← hP'.φ_eq he'E₁]
    exact h.φ_le e heE₁

theorem PatchworkEquiv.isRealizableExpansion_congr [Preorder Ω] {α' β' : Type*}
    {P₁ P₂ : GM04.Patchwork Ω α β} {P'₁ P'₂ : GM04.Patchwork Ω α' β'}
    {ηv : α → Set α'} {ηe : β → β'}
    (hP : PatchworkEquiv P₁ P₂) (hP' : PatchworkEquiv P'₁ P'₂)
    (h : GM04.IsRealizableExpansion P₁ P'₁ ηv ηe) :
    GM04.IsRealizableExpansion P₂ P'₂ ηv ηe := by
  obtain ⟨hexp, H, ⟨⟨δ, hδ, hH⟩, hcomp⟩⟩ := h
  refine ⟨PatchworkEquiv.isExpansion_congr hP hP' hexp, H,
    ⟨⟨δ, fun e he ↦ ?_, ?_⟩, fun v hv ↦ hcomp v (hP.G_eq.symm ▸ hv)⟩⟩
  · have he₁ : e ∈ (P'₁.deleteEdges (ηe '' P₁.G.edgeSet)).G.edgeSet := by
      simpa [GM04.Patchwork.deleteEdges, RootedHypergraph.deleteEdges, Hypergraph.deleteEdges,
        hP.G_eq, hP'.G_eq] using he
    have hmem := hδ e he₁
    change δ e ∈ P'₂.Δ e
    rw [← hP'.Δ_eq he₁.1]
    exact hmem
  · simpa [GM04.Patchwork.deleteEdges, RootedHypergraph.deleteEdges, Hypergraph.deleteEdges,
      hP.G_eq, hP'.G_eq] using hH

open Classical in
/-- The underlying rooted hypergraph `G'` of the heart `P | ℒ` using `newEdge`. -/
@[expose] noncomputable def mkPlaceHeartHypergraph (G : RootedHypergraph α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ)
    (newEdge : RootedHypergraph α β → β) :
    RootedHypergraph α β where
  toHypergraph :=
    { vertexSet := (rootedLocationCore G ℒ).vertexSet
      edgeSet := (rootedLocationCore G ℒ).edgeSet ∪ (newEdge '' ℒ)
      Inc e v :=
        (e ∈ (rootedLocationCore G ℒ).edgeSet ∧ G.Inc e v) ∨
        (∃ A ∈ ℒ, newEdge A = e ∧ v ∈ A.rootSet)
      vertex_mem_of_inc e v h := by
        rcases h with ⟨he, hinc⟩ | ⟨A, hA, _, hv⟩
        · have hle : rootedLocationCore G ℒ ≤ G.toHypergraph := locationCore_le hℒ.isLocation
          have hv_ends : v ∈ (rootedLocationCore G ℒ).ends e := by
            rw [← hle.ends_eq e he]
            exact hinc
          exact (rootedLocationCore G ℒ).vertex_mem_of_inc hv_ends
        · exact mem_rootSet_subset_rootedLocationCore hℒ hA hv
      edge_mem_of_inc _ _ h := by
        rcases h with ⟨he, _⟩ | ⟨A, hA, rfl, _⟩
        · exact Or.inl he
        · exact Or.inr ⟨A, hA, rfl⟩
      vertexSet_finite := (rootedLocationCore G ℒ).vertexSet_finite
      edgeSet_finite :=
        (rootedLocationCore G ℒ).edgeSet_finite.union (hℒ.finite.image newEdge) }
  roots := G.roots
  roots_nodup := G.roots_nodup
  roots_subset _ hv := rootSet_subset_rootedLocationCore hℒ hv

open Classical in
/-- Explicit construction of the heart `P | ℒ` of a partial `Ω`-place `(P, ℒ)` using new elements
`newEdge` (Graph Minors XVIII, Section 5, pages 93–94). -/
@[expose] noncomputable def mkPlaceHeart (P : PartialPatchwork Ω α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation P.G ℒ)
    (newEdge : RootedHypergraph α β → β)
    (hinj : Set.InjOn newEdge ℒ)
    (hnotMem : ∀ ⦃A⦄, A ∈ ℒ → newEdge A ∉ (rootedLocationCore P.G ℒ).edgeSet) :
    PartialPatchwork Ω α β where
  G := mkPlaceHeartHypergraph P.G hℒ newEdge
  dom := ((rootedLocationCore P.G ℒ).edgeSet ∩ P.dom) ∪ (newEdge '' ℒ)
  μ e := if h : ∃ A ∈ ℒ, newEdge A = e then h.choose.roots else P.μ e
  Δ e := if h : ∃ A ∈ ℒ, newEdge A = e then feasibleGroupings (P.restrict h.choose) else P.Δ e
  φ e := if _ : ∃ A ∈ ℒ, newEdge A = e then ⊥ else P.φ e
  dom_subset := by
    rintro e (⟨he, _⟩ | ⟨A, hA, rfl⟩)
    · exact Or.inl he
    · exact Or.inr ⟨A, hA, rfl⟩
  μ_nodup := by
    intro e he
    by_cases hex : ∃ A ∈ ℒ, newEdge A = e
    · simp only [hex, ↓reduceDIte]
      exact hex.choose.roots_nodup
    · simp only [hex, ↓reduceDIte]
      rcases he with ⟨_, hd⟩ | ⟨A, hA, rfl⟩
      · exact P.μ_nodup e hd
      · exact (hex ⟨A, hA, rfl⟩).elim
  μ_set := by
    intro e he
    by_cases hex : ∃ A ∈ ℒ, newEdge A = e
    · simp only [hex, ↓reduceDIte]
      rcases hex with ⟨A, hA, rfl⟩
      have hex' : ∃ A' ∈ ℒ, newEdge A' = newEdge A := ⟨A, hA, rfl⟩
      have hchoose : hex'.choose = A := hinj hex'.choose_spec.1 hA hex'.choose_spec.2
      rw [hchoose]
      ext v
      change v ∈ A.rootSet ↔
        (newEdge A ∈ (rootedLocationCore P.G ℒ).edgeSet ∧ P.G.Inc (newEdge A) v) ∨
        (∃ A' ∈ ℒ, newEdge A' = newEdge A ∧ v ∈ A'.rootSet)
      constructor
      · intro hv
        exact Or.inr ⟨A, hA, rfl, hv⟩
      · rintro (⟨hcore, _⟩ | ⟨A', hA', hEq, hv⟩)
        · exact (hnotMem hA hcore).elim
        · rwa [← hinj hA' hA hEq]
    · simp only [hex, ↓reduceDIte]
      rcases he with ⟨hcore, hd⟩ | ⟨A, hA, rfl⟩
      · rw [P.μ_set e hd]
        ext v
        change P.G.Inc e v ↔
          (e ∈ (rootedLocationCore P.G ℒ).edgeSet ∧ P.G.Inc e v) ∨
          (∃ A ∈ ℒ, newEdge A = e ∧ v ∈ A.rootSet)
        exact ⟨fun hinc ↦ Or.inl ⟨hcore, hinc⟩,
          fun h ↦ h.elim (fun h1 ↦ h1.2)
            (fun ⟨A, hA, hEq, _⟩ ↦ (hex ⟨A, hA, hEq⟩).elim)⟩
      · exact (hex ⟨A, hA, rfl⟩).elim
  Δ_verts := by
    intro e he
    by_cases hex : ∃ A ∈ ℒ, newEdge A = e
    · simp only [hex, ↓reduceDIte]
      rcases hex with ⟨A, hA, rfl⟩
      have hex' : ∃ A' ∈ ℒ, newEdge A' = newEdge A := ⟨A, hA, rfl⟩
      have hchoose : hex'.choose = A := hinj hex'.choose_spec.1 hA hex'.choose_spec.2
      rw [hchoose]
      ext v
      change v ∈ A.rootSet ↔
        (newEdge A ∈ (rootedLocationCore P.G ℒ).edgeSet ∧ P.G.Inc (newEdge A) v) ∨
        (∃ A' ∈ ℒ, newEdge A' = newEdge A ∧ v ∈ A'.rootSet)
      exact ⟨fun hv ↦ Or.inr ⟨A, hA, rfl, hv⟩,
        fun h ↦ h.elim (fun ⟨hc, _⟩ ↦ (hnotMem hA hc).elim)
          (fun ⟨A', hA', hEq, hv⟩ ↦ hinj hA' hA hEq ▸ hv)⟩
    · simp only [hex, ↓reduceDIte]
      rcases he with hcore | ⟨A, hA, rfl⟩
      · have heG : e ∈ P.G.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 hcore).1
        rw [P.Δ_verts e heG]
        ext v
        change P.G.Inc e v ↔
          (e ∈ (rootedLocationCore P.G ℒ).edgeSet ∧ P.G.Inc e v) ∨
          (∃ A ∈ ℒ, newEdge A = e ∧ v ∈ A.rootSet)
        exact ⟨fun hinc ↦ Or.inl ⟨hcore, hinc⟩,
          fun h ↦ h.elim (fun h1 ↦ h1.2)
            (fun ⟨A, hA, hEq, _⟩ ↦ (hex ⟨A, hA, hEq⟩).elim)⟩
      · exact (hex ⟨A, hA, rfl⟩).elim
  Δ_free := by
    intro e he hnd
    by_cases hex : ∃ A ∈ ℒ, newEdge A = e
    · rcases hex with ⟨A, hA, rfl⟩
      exact (hnd (Or.inr ⟨A, hA, rfl⟩)).elim
    · simp only [hex, ↓reduceDIte]
      rcases he with hcore | ⟨A, hA, rfl⟩
      · have heG : e ∈ P.G.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 hcore).1
        have hndP : e ∉ P.dom := fun hd ↦ hnd (Or.inl ⟨hcore, hd⟩)
        exact P.Δ_free e heG hndP
      · exact (hex ⟨A, hA, rfl⟩).elim

open Classical in
/-- `mkPlaceHeart P hℒ newEdge hinj hnotMem` satisfies `IsPlaceHeart P ℒ newEdge`. -/
theorem isPlaceHeart_mkPlaceHeart (P : PartialPatchwork Ω α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation P.G ℒ)
    (newEdge : RootedHypergraph α β → β)
    (hinj : Set.InjOn newEdge ℒ)
    (hnotMem : ∀ ⦃A⦄, A ∈ ℒ → newEdge A ∉ (rootedLocationCore P.G ℒ).edgeSet) :
    IsPlaceHeart P ℒ newEdge (mkPlaceHeart P hℒ newEdge hinj hnotMem) where
  isRootedLocation := hℒ
  injOn_newEdge := hinj
  newEdge_notMem_core := hnotMem
  vertexSet_eq := rfl
  edgeSet_eq := rfl
  roots_eq := rfl
  ends_core f hf := by
    ext v
    change (f ∈ (rootedLocationCore P.G ℒ).edgeSet ∧ P.G.Inc f v) ∨
      (∃ A ∈ ℒ, newEdge A = f ∧ v ∈ A.rootSet) ↔ P.G.Inc f v
    refine ⟨?_, fun hinc ↦ Or.inl ⟨hf, hinc⟩⟩
    rintro (⟨_, hinc⟩ | ⟨A, hA, rfl, _⟩)
    · exact hinc
    · exact (hnotMem hA hf).elim
  ends_newEdge A hA := by
    ext v
    change (newEdge A ∈ (rootedLocationCore P.G ℒ).edgeSet ∧ P.G.Inc (newEdge A) v) ∨
      (∃ A' ∈ ℒ, newEdge A' = newEdge A ∧ v ∈ A'.rootSet) ↔ v ∈ A.rootSet
    refine ⟨?_, fun hv ↦ Or.inr ⟨A, hA, rfl, hv⟩⟩
    rintro (⟨hc, _⟩ | ⟨A', hA', hEq, hv⟩)
    · exact (hnotMem hA hc).elim
    · rwa [← hinj hA' hA hEq]
  dom_eq := rfl
  μ_core f hf := by
    have hnot : ¬ ∃ A ∈ ℒ, newEdge A = f := by
      rintro ⟨A, hA, rfl⟩
      exact hnotMem hA hf.1
    change (if h : ∃ A ∈ ℒ, newEdge A = f then h.choose.roots else P.μ f) = P.μ f
    simp only [hnot, ↓reduceDIte]
  μ_newEdge A hA := by
    have hex : ∃ A' ∈ ℒ, newEdge A' = newEdge A := ⟨A, hA, rfl⟩
    change (if h : ∃ A' ∈ ℒ, newEdge A' = newEdge A then h.choose.roots else P.μ (newEdge A)) =
      A.roots
    simp only [hex, ↓reduceDIte]
    exact congrArg RootedHypergraph.roots (hinj hex.choose_spec.1 hA hex.choose_spec.2)
  Δ_core f hf := by
    have hnot : ¬ ∃ A ∈ ℒ, newEdge A = f := by
      rintro ⟨A, hA, rfl⟩
      exact hnotMem hA hf
    change (if h : ∃ A ∈ ℒ, newEdge A = f then feasibleGroupings (P.restrict h.choose) else P.Δ f) =
      P.Δ f
    simp only [hnot, ↓reduceDIte]
  Δ_newEdge A hA := by
    have hex : ∃ A' ∈ ℒ, newEdge A' = newEdge A := ⟨A, hA, rfl⟩
    change (if h : ∃ A' ∈ ℒ, newEdge A' = newEdge A then
      feasibleGroupings (P.restrict h.choose) else P.Δ (newEdge A)) =
      feasibleGroupings (P.restrict A)
    simp only [hex, ↓reduceDIte]
    rw [hinj hex.choose_spec.1 hA hex.choose_spec.2]
  φ_core f hf := by
    have hnot : ¬ ∃ A ∈ ℒ, newEdge A = f := by
      rintro ⟨A, hA, rfl⟩
      exact hnotMem hA hf
    change (if _ : ∃ A ∈ ℒ, newEdge A = f then ⊥ else P.φ f) = P.φ f
    simp only [hnot, ↓reduceDIte]
  φ_newEdge A hA := by
    have hex : ∃ A' ∈ ℒ, newEdge A' = newEdge A := ⟨A, hA, rfl⟩
    change (if _ : ∃ A' ∈ ℒ, newEdge A' = newEdge A then ⊥ else P.φ (newEdge A)) = ⊥
    simp only [hex, ↓reduceDIte]

/-- Any two hearts `P₁', P₂'` of `(P, ℒ)` using the same `newEdge` satisfy `PatchworkEquiv P₁' P₂'`.
-/
theorem IsPlaceHeart.equiv {P P₁' P₂' : PartialPatchwork Ω α β}
    {ℒ : Set (RootedHypergraph α β)} {newEdge : RootedHypergraph α β → β}
    (h₁ : IsPlaceHeart P ℒ newEdge P₁') (h₂ : IsPlaceHeart P ℒ newEdge P₂') :
    PatchworkEquiv P₁' P₂' where
  G_eq := by
    refine RootedHypergraph.ext ?_ (h₁.roots_eq.trans h₂.roots_eq.symm)
    refine hypergraph_ext_of_ends_eq (h₁.vertexSet_eq.trans h₂.vertexSet_eq.symm)
      (h₁.edgeSet_eq.trans h₂.edgeSet_eq.symm) fun e he ↦ ?_
    rw [h₁.edgeSet_eq] at he
    rcases he with hf | ⟨A, hA, rfl⟩
    · rw [h₁.ends_core hf, h₂.ends_core hf]
    · rw [h₁.ends_newEdge hA, h₂.ends_newEdge hA]
  dom_eq := h₁.dom_eq.trans h₂.dom_eq.symm
  μ_eq e he := by
    rw [h₁.dom_eq] at he
    rcases he with hf | ⟨A, hA, rfl⟩
    · rw [h₁.μ_core hf, h₂.μ_core hf]
    · rw [h₁.μ_newEdge hA, h₂.μ_newEdge hA]
  Δ_eq e he := by
    rw [h₁.edgeSet_eq] at he
    rcases he with hf | ⟨A, hA, rfl⟩
    · rw [h₁.Δ_core hf, h₂.Δ_core hf]
    · rw [h₁.Δ_newEdge hA, h₂.Δ_newEdge hA]
  φ_eq e he := by
    rw [h₁.edgeSet_eq] at he
    rcases he with hf | ⟨A, hA, rfl⟩
    · rw [h₁.φ_core hf, h₂.φ_core hf]
    · rw [h₁.φ_newEdge hA, h₂.φ_newEdge hA]

/-! ## Tree-width transfer for Claim (1) of (5.5) -/

/-- Every hypergraph `H` has a tree-decomposition `(T, τ)` attaining `treeWidthPlusOne H`. -/
theorem exists_isTreeDecomposition_treeDecompWidthPlusOne_eq {γ : Type*} (H : Hypergraph α γ) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α γ),
      GM10.IsTreeDecomposition H T τ ∧
      GM10.treeDecompWidthPlusOne τ = GM10.treeWidthPlusOne H := by
  have hex : {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι)
      (τ : ι → Hypergraph α γ),
      GM10.IsTreeDecomposition H T τ ∧ GM10.treeDecompWidthPlusOne τ = w}.Nonempty := by
    refine ⟨GM10.treeDecompWidthPlusOne (fun _ : Unit ↦ H), Unit, inferInstance, ⊥,
      fun _ ↦ H, ?_, rfl⟩
    refine ⟨⟨⟨fun _ _ ↦ Reachable.refl _⟩, fun _ p hp ↦ ?_⟩, fun _ ↦ le_rfl, ?_,
      fun u v hne ↦ (hne (Subsingleton.elim u v)).elim, fun _ _ _ _ ↦ GM10.inter_le le_rfl le_rfl⟩
    · cases p with
      | nil => exact (Walk.not_isCycle_nil hp).elim
      | cons h _ => exact h.elim
    · refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (biUnion_le fun _ _ ↦ le_rfl) le_rfl ?_ ?_
      · ext v; simp [biUnion]
      · ext e; simp [biUnion]
  exact Nat.sInf_mem hex

/-- If `V(P₀.G) ⊆ V(H)`, every edge of `P₀.G` has the same ends as some edge of `H`, some edge of
`H` has ends containing `πBar(P₀.G)`, and `treeWidth H ≤ w`, then `P₀` has patchwork tree-width `≤
w`
(used in Claim (1) of (5.5), pages 95–96). -/
theorem hasPatchworkTreeWidthLE_of_ends_subset {γ : Type*}
    (P₀ : GM04.Patchwork Ω α β) (H : Hypergraph α γ) (w : ℕ)
    (hV : P₀.G.vertexSet ⊆ H.vertexSet)
    (hends : ∀ e ∈ P₀.G.edgeSet, ∃ e' ∈ H.edgeSet, P₀.G.ends e = H.ends e')
    (hroot_edge : ∃ e₀ ∈ H.edgeSet, P₀.G.rootSet ⊆ H.ends e₀)
    (htw : GM10.treeWidth H ≤ (w : ℤ)) :
    HasPatchworkTreeWidthLE P₀ w := by
  classical
  obtain ⟨ι, hfin_ι, T, τ, hD, hw⟩ := exists_isTreeDecomposition_treeDecompWidthPlusOne_eq H
  let _ : Fintype ι := hfin_ι
  have hex_edge_node : ∀ e' ∈ H.edgeSet, ∃ t : ι, e' ∈ (τ t).edgeSet := by
    intro e' he'
    rw [← hD.biUnion_eq] at he'
    simp only [biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion] at he'
    exact he'
  obtain ⟨e₀, he₀, hroot_sub⟩ := hroot_edge
  obtain ⟨t₀, ht₀_mem⟩ := hex_edge_node e₀ he₀
  have hroot_t₀ : P₀.G.rootSet ⊆ (τ t₀).vertexSet := by
    intro v hv
    have hv_H : v ∈ H.ends e₀ := hroot_sub hv
    rw [(hD.le t₀).ends_eq e₀ ht₀_mem] at hv_H
    exact (τ t₀).vertex_mem_of_inc hv_H
  have hex_node : ∀ e ∈ P₀.G.edgeSet, ∃ t : ι, P₀.G.ends e ⊆ (τ t).vertexSet := by
    intro e he
    obtain ⟨e', he', hends_eq⟩ := hends e he
    obtain ⟨t, ht_mem⟩ := hex_edge_node e' he'
    refine ⟨t, fun v hv ↦ ?_⟩
    have hv_H : v ∈ H.ends e' := hends_eq ▸ hv
    rw [(hD.le t).ends_eq e' ht_mem] at hv_H
    exact (τ t).vertex_mem_of_inc hv_H
  let nodeOf : β → ι := fun e ↦
    if he : e ∈ P₀.G.edgeSet then (hex_node e he).choose else t₀
  have hnodeOf_sub : ∀ e (he : e ∈ P₀.G.edgeSet), P₀.G.ends e ⊆ (τ (nodeOf e)).vertexSet := by
    intro e he
    simp only [nodeOf, he, ↓reduceDIte]
    exact (hex_node e he).choose_spec
  let τ' : ι → Hypergraph α β := fun t ↦
    { vertexSet := (τ t).vertexSet ∩ P₀.G.vertexSet
      edgeSet := {e ∈ P₀.G.edgeSet | nodeOf e = t}
      Inc e v := e ∈ P₀.G.edgeSet ∧ nodeOf e = t ∧ P₀.G.Inc e v
      vertex_mem_of_inc e v h :=
        ⟨h.2.1 ▸ hnodeOf_sub e h.1 h.2.2, P₀.G.vertex_mem_of_inc h.2.2⟩
      edge_mem_of_inc _ _ h := ⟨h.1, h.2.1⟩
      vertexSet_finite := ((τ t).vertexSet_finite).inter_of_left _
      edgeSet_finite := P₀.G.edgeSet_finite.sep _ }
  have hle' : ∀ t, τ' t ≤ P₀.G.toHypergraph := fun t ↦
    { vertexSet_subset := Set.inter_subset_right
      edgeSet_subset := fun _ h ↦ h.1
      ends_eq := fun e he ↦ Set.ext fun v ↦ ⟨fun h ↦ ⟨he.1, he.2, h⟩, fun h ↦ h.2.2⟩ }
  have hD' : GM10.IsTreeDecomposition P₀.G.toHypergraph T τ' :=
    { isTree := hD.isTree
      le := hle'
      biUnion_eq := by
        refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
          (biUnion_le fun t _ ↦ hle' t) le_rfl ?_ ?_
        · ext v
          simp only [biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, τ',
            Set.mem_inter_iff]
          refine ⟨fun ⟨_, _, hv⟩ ↦ hv, fun hv ↦ ?_⟩
          have hvH : v ∈ H.vertexSet := hV hv
          rw [← hD.biUnion_eq] at hvH
          simp only [biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion] at hvH
          obtain ⟨t, ht⟩ := hvH
          exact ⟨t, ht, hv⟩
        · ext e
          simp only [biUnion, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, τ',
            Set.mem_sep_iff, exists_eq_right']
      edgeSet_inter_eq := fun t₁ t₂ hne ↦ by
        ext e
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, rfl⟩, ⟨_, hEq⟩⟩
        exact hne hEq
      inter_le := fun t₁ t₂ t₃ hpath ↦ by
        have hinter := hD.inter_le hpath
        refine (GM10.le_iff_of_le (GM10.inter_le (hle' t₁) (hle' t₃)) (hle' t₂)).2 ⟨?_, ?_⟩
        · intro v ⟨⟨hv₁, hvP⟩, ⟨hv₃, _⟩⟩
          exact ⟨hinter.vertexSet_subset ⟨hv₁, hv₃⟩, hvP⟩
        · rintro e ⟨⟨he, rfl⟩, ⟨_, hEq⟩⟩
          cases hEq
          have ht₂ : t₂ ∈ (Walk.nil : T.Walk (nodeOf e) (nodeOf e)).support :=
            hpath Walk.nil Walk.IsPath.nil
          simp only [Walk.support_nil, List.mem_singleton] at ht₂
          exact ⟨he, ht₂.symm⟩ }
  have : Nonempty ι := ⟨t₀⟩
  have hw'_le : GM10.treeDecompWidthPlusOne τ' ≤ GM10.treeDecompWidthPlusOne τ := by
    unfold GM10.treeDecompWidthPlusOne
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨t, rfl⟩
    refine le_trans (Set.ncard_le_ncard Set.inter_subset_left (τ t).vertexSet_finite) ?_
    exact le_csSup (Set.toFinite _).bddAbove ⟨t, rfl⟩
  have htw'_le : GM10.treeDecompWidth τ' ≤ (w : ℤ) := by
    unfold GM10.treeDecompWidth
    unfold GM10.treeWidth at htw
    have h₁ : (GM10.treeDecompWidthPlusOne τ' : ℤ) ≤ (GM10.treeWidthPlusOne H : ℤ) := by
      rw [← hw]
      exact Nat.cast_le.2 hw'_le
    omega
  exact ⟨ι, hfin_ι, T, τ', t₀, hD', htw'_le, fun v hv ↦ ⟨hroot_t₀ hv, P₀.G.roots_subset v hv⟩⟩

/-! ## Proof of (5.5) and Claims (1)–(6) -/

/-- If `C₁, C₂ ∈ ℒ` are distinct members of a rooted location `ℒ` in `G` with the same underlying
hypergraph `C₁.toHypergraph = C₂.toHypergraph`, then `C₁.edgeSet = ∅` and
`C₁.vertexSet = C₁.rootSet`. -/
theorem eq_rootSet_of_toHypergraph_eq_of_ne {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ)
    {C₁ C₂ : RootedHypergraph α β} (h₁ : C₁ ∈ ℒ) (h₂ : C₂ ∈ ℒ) (hne : C₁ ≠ C₂)
    (hH : C₁.toHypergraph = C₂.toHypergraph) :
    C₁.edgeSet = ∅ ∧ C₁.vertexSet = C₁.rootSet := by
  have hle := hℒ.le_complement h₂ h₁ hne.symm
  rw [← hH] at hle
  have hE : C₁.edgeSet = ∅ := by
    ext e
    simp only [Set.mem_empty_iff_false, iff_false]
    intro he
    exact (hle.edgeSet_subset he).2 he
  have hV : C₁.vertexSet = C₁.rootSet := by
    apply Set.Subset.antisymm _ (rootSet_subset C₁)
    intro v hv
    exact (hle.vertexSet_subset hv).resolve_left fun h ↦ h.2 hv
  exact ⟨hE, hV⟩

/-- Setup and preliminary properties for the proof of (5.5) (Graph Minors XVIII, Section 5,
page 95): given a partition `partR : RootedHypergraph α β → Set (RootedHypergraph α β)` of `ℒ_star`
indexed by `C ∈ ℒ` such that for every `C ∈ ℒ` and `A ∈ partR C`, `A⁻ ⊆ C⁻` and
`(G \ C)⁻ ⊆ (G \ A)⁻`, each `A ∈ partR C` is complemented in `C` and `partR C` is a rooted
location in `C`. -/
theorem isComplemented_of_mem_partR {G : RootedHypergraph α β}
    {ℒ ℒ_star : Set (RootedHypergraph α β)}
    (hℒ : IsRootedLocation G ℒ) (hℒ_star : IsRootedLocation G ℒ_star)
    {partR : RootedHypergraph α β → Set (RootedHypergraph α β)}
    (hpart_sub : ∀ ⦃C⦄, C ∈ ℒ → partR C ⊆ ℒ_star)
    (hpart_le : ∀ ⦃C⦄, C ∈ ℒ → ∀ ⦃A⦄, A ∈ partR C →
      A.toHypergraph ≤ C.toHypergraph ∧
      complementHypergraph G C ≤ complementHypergraph G A)
    {C : RootedHypergraph α β} (hC : C ∈ ℒ) {A : RootedHypergraph α β} (hA : A ∈ partR C) :
    IsComplemented C A where
  le := (hpart_le hC hA).1
  roots_mem v hvA hvC_root := by
    have hvG : v ∈ G.vertexSet := (hℒ.isComplemented hC).le.vertexSet_subset
      (C.roots_subset v hvC_root)
    have hv_compC : v ∈ (complementHypergraph G C).vertexSet := Or.inr ⟨hvG, hvC_root⟩
    have hv_compA : v ∈ (complementHypergraph G A).vertexSet :=
      (hpart_le hC hA).2.vertexSet_subset hv_compC
    exact (hv_compA.resolve_left fun h ↦ h.2 hvA).2
  inc_diff_mem v e hvA he hinc := by
    have hA_star : A ∈ ℒ_star := hpart_sub hC hA
    have heG : e ∈ G.edgeSet \ A.edgeSet :=
      ⟨(hℒ.isComplemented hC).le.edgeSet_subset he.1, he.2⟩
    have hincG : G.Inc e v := GM10.inc_of_le (hℒ.isComplemented hC).le hinc
    exact (hℒ_star.isComplemented hA_star).inc_diff_mem hvA heG hincG

theorem isRootedLocation_partR {G : RootedHypergraph α β}
    {ℒ ℒ_star : Set (RootedHypergraph α β)}
    (hℒ : IsRootedLocation G ℒ) (hℒ_star : IsRootedLocation G ℒ_star)
    {partR : RootedHypergraph α β → Set (RootedHypergraph α β)}
    (hpart_sub : ∀ ⦃C⦄, C ∈ ℒ → partR C ⊆ ℒ_star)
    (hpart_le : ∀ ⦃C⦄, C ∈ ℒ → ∀ ⦃A⦄, A ∈ partR C →
      A.toHypergraph ≤ C.toHypergraph ∧
      complementHypergraph G C ≤ complementHypergraph G A)
    {C : RootedHypergraph α β} (hC : C ∈ ℒ) :
    IsRootedLocation C (partR C) where
  isComplemented _ hA := isComplemented_of_mem_partR hℒ hℒ_star hpart_sub hpart_le hC hA
  le_complement A₁ hA₁ A₂ hA₂ hne := by
    have hcompC₂ := isComplemented_of_mem_partR hℒ hℒ_star hpart_sub hpart_le hC hA₂
    have hA₁_C : A₁.toHypergraph ≤ C.toHypergraph := (hpart_le hC hA₁).1
    have hle_G := hℒ_star.le_complement (hpart_sub hC hA₁) (hpart_sub hC hA₂) hne
    refine (GM10.le_iff_of_le (hA₁_C.trans (hℒ.isComplemented hC).le)
      (hcompC₂.isSeparation.isSeparation.right_le.trans (hℒ.isComplemented hC).le)).2 ⟨?_, ?_⟩
    · intro v hv
      have hvC : v ∈ C.vertexSet := hA₁_C.vertexSet_subset hv
      rcases hle_G.vertexSet_subset hv with ⟨_, hnotA₂⟩ | hr₂
      · exact Or.inl ⟨hvC, hnotA₂⟩
      · exact Or.inr hr₂
    · intro e he
      exact ⟨hA₁_C.edgeSet_subset he, (hle_G.edgeSet_subset he).2⟩

/-- For each `C ∈ ℒ`, `M(C, ℒ_C) ⊆ M(G, ℒ*)` (first part of Claim (2) of (5.5), page 96). -/
theorem rootedLocationCore_partR_le {G : RootedHypergraph α β}
    {ℒ ℒ_star : Set (RootedHypergraph α β)}
    (hℒ : IsRootedLocation G ℒ) (hℒ_star : IsRootedLocation G ℒ_star)
    {partR : RootedHypergraph α β → Set (RootedHypergraph α β)}
    (hpart_sub : ∀ ⦃C⦄, C ∈ ℒ → partR C ⊆ ℒ_star)
    (hpart_union : (⋃ C ∈ ℒ, partR C) = ℒ_star)
    (hpart_le : ∀ ⦃C⦄, C ∈ ℒ → ∀ ⦃A⦄, A ∈ partR C →
      A.toHypergraph ≤ C.toHypergraph ∧
      complementHypergraph G C ≤ complementHypergraph G A)
    {C : RootedHypergraph α β} (hC : C ∈ ℒ) :
    rootedLocationCore C (partR C) ≤ rootedLocationCore G ℒ_star := by
  have hℒ_C := isRootedLocation_partR hℒ hℒ_star hpart_sub hpart_le hC
  have hle_C : rootedLocationCore C (partR C) ≤ G.toHypergraph :=
    (locationCore_le hℒ_C.isLocation).trans (hℒ.isComplemented hC).le
  have hle_star : rootedLocationCore G ℒ_star ≤ G.toHypergraph :=
    locationCore_le hℒ_star.isLocation
  refine (GM10.le_iff_of_le hle_C hle_star).2 ⟨?_, ?_⟩
  · intro v hv
    rw [mem_rootedLocationCore_vertexSet_iff hℒ_C] at hv
    rw [mem_rootedLocationCore_vertexSet_iff hℒ_star]
    refine ⟨(hℒ.isComplemented hC).le.vertexSet_subset hv.1, fun A hA hvA ↦ ?_⟩
    rw [← hpart_union, Set.mem_iUnion₂] at hA
    rcases hA with ⟨C', hC', hA_C'⟩
    by_cases hEq : C' = C
    · subst hEq
      exact hv.2 A hA_C' hvA
    · have hC_le_compC' := hℒ.le_complement hC hC' (Ne.symm hEq)
      rw [← complementHypergraph_eq_of_isComplemented (hℒ.isComplemented hC')] at hC_le_compC'
      have hC_le_compA : C.toHypergraph ≤ complementHypergraph G A :=
        hC_le_compC'.trans (hpart_le hC' hA_C').2
      exact ((hC_le_compA.vertexSet_subset hv.1).resolve_left fun h ↦ h.2 hvA).2
  · intro e he
    rw [mem_rootedLocationCore_edgeSet_iff] at he ⊢
    refine ⟨(hℒ.isComplemented hC).le.edgeSet_subset he.1, fun A hA heA ↦ ?_⟩
    rw [← hpart_union, Set.mem_iUnion₂] at hA
    rcases hA with ⟨C', hC', hA_C'⟩
    by_cases hEq : C' = C
    · subst hEq
      exact he.2 A hA_C' heA
    · have hA_C'le : A.toHypergraph ≤ (complement G C (hℒ.isComplemented hC)).toHypergraph :=
        (hpart_le hC' hA_C').1.trans (hℒ.le_complement hC' hC hEq)
      exact (hA_C'le.edgeSet_subset heA).2 he.1

/-- **Claim (1)** in the proof of Graph Minors XVIII, (5.5) (pages 95–96):
Each `P_i` (a heart of `(P | C_i, ℒ_i)` using `newEdge_star`) has patchwork tree-width `≤ w`. -/
theorem lemma_5_5_claim_1 {P : PartialPatchwork Ω α β}
    {ℒ ℒ_star : Set (RootedHypergraph α β)} {w : ℕ}
    (hℒ : IsRootedLocation P.G ℒ) (hℒ_star : IsRootedLocation P.G ℒ_star)
    {newEdge_star : RootedHypergraph α β → β}
    {part_loc : Hypergraph α β × Hypergraph α β → Set (Hypergraph α β × Hypergraph α β)}
    (hvia : IsLocationEnlargementVia P.G.toHypergraph
      (rootedLocationToLocation P.G ℒ) (rootedLocationToLocation P.G ℒ_star) part_loc)
    (htw : ∀ ⦃p⦄, p ∈ rootedLocationToLocation P.G ℒ →
      (locationTreeWidth P.G.toHypergraph (part_loc p ∪ {(p.2, p.1)}) : ℚ) ≤ (w : ℚ))
    {partR : RootedHypergraph α β → Set (RootedHypergraph α β)}
    (hpart_sub : ∀ ⦃C⦄, C ∈ ℒ → partR C ⊆ ℒ_star)
    (hpart_le : ∀ ⦃C⦄, C ∈ ℒ → ∀ ⦃A⦄, A ∈ partR C →
      A.toHypergraph ≤ C.toHypergraph ∧
      complementHypergraph P.G C ≤ complementHypergraph P.G A)
    (hpart_case : ∀ ⦃C⦄, C ∈ ℒ →
      rootedLocationToLocation P.G (partR C) =
        part_loc (C.toHypergraph, complementHypergraph P.G C) ∨
      (partR C = ∅ ∧ C.edgeSet = ∅ ∧ C.vertexSet = C.rootSet))
    {C : RootedHypergraph α β} (hC : C ∈ ℒ)
    {Q_C : PartialPatchwork Ω α β}
    (hQ_C : IsPlaceHeart (P.restrict C) (partR C) newEdge_star Q_C) :
    HasPatchworkTreeWidthLE Q_C w := by
  let G := P.G
  let D := complementHypergraph G C
  let p : Hypergraph α β × Hypergraph α β := (C.toHypergraph, D)
  have hp_mem : p ∈ rootedLocationToLocation G ℒ := ⟨C, hC, rfl⟩
  let ℳ : Set (Hypergraph α β × Hypergraph α β) := part_loc p ∪ {(D, C.toHypergraph)}
  let H := locationHeart G.toHypergraph ℳ
  have htw_H : GM10.treeWidth H ≤ (w : ℤ) := by
    have hq := htw hp_mem
    exact_mod_cast hq
  have hsep_CD : G.toHypergraph.IsSeparation C.toHypergraph D := by
    dsimp only [D]
    rw [complementHypergraph_eq_of_isComplemented (hℒ.isComplemented hC)]
    exact (hℒ.isComplemented hC).isSeparation.isSeparation
  have hloc_ℳ : GM10.IsLocation G.toHypergraph ℳ :=
    { isSeparation := by
        rintro q (hq | rfl)
        · exact hvia.isLocation_right.isSeparation (hvia.part_subset hp_mem hq)
        · exact hsep_CD.symm
      left_le_right := by
        rintro q₁ (hq₁ | rfl) q₂ (hq₂ | rfl) hne
        · exact hvia.isLocation_right.left_le_right
            (hvia.part_subset hp_mem hq₁) (hvia.part_subset hp_mem hq₂) hne
        · exact (hvia.le_of_mem_part hp_mem hq₁).1
        · exact (hvia.le_of_mem_part hp_mem hq₂).2
        · exact (hne rfl).elim }
  have hDC_mem : (D, C.toHypergraph) ∈ ℳ := Or.inr (Set.mem_singleton _)
  have hDC_sub : (D ∩ C.toHypergraph).vertexSet ⊆ (GM10.locationCore G.toHypergraph ℳ).vertexSet
    := by
    rw [← (theorem_2_3_2 hloc_ℳ hDC_mem).2]
    exact Set.inter_subset_right
  have hrootC_eq : C.rootSet = (D ∩ C.toHypergraph).vertexSet := by
    ext v
    dsimp only [D]
    rw [complementHypergraph_eq_of_isComplemented (hℒ.isComplemented hC), GM10.inter_comm]
    change v ∈ C.rootSet ↔
      v ∈ (C.toHypergraph ∩ (complement G C (hℒ.isComplemented hC)).toHypergraph).vertexSet
    rw [← (hℒ.isComplemented hC).isSeparation.rootSet_left]
  have hroot_edge : ∃ e₀ ∈ H.edgeSet, Q_C.G.rootSet ⊆ H.ends e₀ := by
    refine ⟨Sum.inr (D, C.toHypergraph),
      Or.inr ⟨(D, C.toHypergraph), ⟨hDC_mem, hsep_CD.symm, hDC_sub⟩, rfl⟩, ?_⟩
    intro v hv
    have hvC : v ∈ C.rootSet := by
      change v ∈ Q_C.G.roots at hv
      rw [hQ_C.roots_eq] at hv
      exact hv
    exact ⟨hDC_mem, hsep_CD.symm, hDC_sub, hrootC_eq ▸ hvC⟩
  have hℒ_C := isRootedLocation_partR hℒ hℒ_star hpart_sub hpart_le hC
  refine hasPatchworkTreeWidthLE_of_ends_subset Q_C H w ?_ ?_ hroot_edge htw_H
  · -- `Q_C.G.vertexSet ⊆ H.vertexSet`
    rw [hQ_C.vertexSet_eq]
    change (rootedLocationCore C (partR C)).vertexSet ⊆
      (GM10.locationCore G.toHypergraph ℳ).vertexSet
    rcases hpart_case hC with hpart_eq | ⟨_, _, hV_eq⟩
    · intro v hv
      rw [mem_rootedLocationCore_vertexSet_iff hℒ_C] at hv
      refine ⟨(hℒ.isComplemented hC).le.vertexSet_subset hv.1, ?_⟩
      rintro q (hq | rfl)
      · rw [← hpart_eq] at hq
        rcases hq with ⟨A, hA, rfl⟩
        dsimp only
        rw [complementHypergraph_eq_of_isComplemented (hℒ_star.isComplemented (hpart_sub hC hA))]
        by_cases hvA : v ∈ A.vertexSet
        · exact Or.inr (hv.2 A hA hvA)
        · exact Or.inl ⟨(hℒ.isComplemented hC).le.vertexSet_subset hv.1, hvA⟩
      · exact hv.1
    · intro v hv
      rw [mem_rootedLocationCore_vertexSet_iff hℒ_C] at hv
      have hv_root : v ∈ C.rootSet := hV_eq ▸ hv.1
      exact hDC_sub (hrootC_eq ▸ hv_root)
  · -- Every edge of `Q_C.G` has the same ends as some edge of `H`.
    intro e he
    rw [hQ_C.edgeSet_eq] at he
    change e ∈ (rootedLocationCore C (partR C)).edgeSet ∪ (newEdge_star '' partR C) at he
    rcases hpart_case hC with hpart_eq | ⟨hpart_empty, hE_empty, _⟩
    · rcases he with he_core | ⟨A, hA, rfl⟩
      · have he_H_core : e ∈ (GM10.locationCore G.toHypergraph ℳ).edgeSet := by
          rw [mem_rootedLocationCore_edgeSet_iff] at he_core
          refine ⟨(hℒ.isComplemented hC).le.edgeSet_subset he_core.1, ?_⟩
          rintro q (hq | rfl)
          · rw [← hpart_eq] at hq
            rcases hq with ⟨A, hA, rfl⟩
            exact ⟨(hℒ.isComplemented hC).le.edgeSet_subset he_core.1, he_core.2 A hA⟩
          · exact he_core.1
        refine ⟨Sum.inl e, Or.inl ⟨e, he_H_core, rfl⟩, ?_⟩
        rw [hQ_C.ends_core he_core]
        have heC : e ∈ C.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 he_core).1
        have hle_ℳ : GM10.locationCore G.toHypergraph ℳ ≤ G.toHypergraph := locationCore_le hloc_ℳ
        exact ((hℒ.isComplemented hC).le.ends_eq e heC).symm.trans (hle_ℳ.ends_eq e he_H_core)
      · let qA : Hypergraph α β × Hypergraph α β := (A.toHypergraph, complementHypergraph G A)
        have hqA_mem : qA ∈ ℳ := by
          left; rw [← hpart_eq]; exact ⟨A, hA, rfl⟩
        have hsepA : G.toHypergraph.IsSeparation qA.1 qA.2 := hloc_ℳ.isSeparation hqA_mem
        have hsubA : (qA.1 ∩ qA.2).vertexSet ⊆ (GM10.locationCore G.toHypergraph ℳ).vertexSet := by
          rw [← (theorem_2_3_2 hloc_ℳ hqA_mem).2]
          exact Set.inter_subset_right
        have hrootA_eq : A.rootSet = (qA.1 ∩ qA.2).vertexSet := by
          ext v
          dsimp only [qA]
          rw [complementHypergraph_eq_of_isComplemented (hℒ_star.isComplemented (hpart_sub hC hA))]
          change v ∈ A.rootSet ↔
            v ∈ (A.toHypergraph ∩ (complement G A (hℒ_star.isComplemented
              (hpart_sub hC hA))).toHypergraph).vertexSet
          rw [← (hℒ_star.isComplemented (hpart_sub hC hA)).isSeparation.rootSet_left]
        refine ⟨Sum.inr qA, Or.inr ⟨qA, ⟨hqA_mem, hsepA, hsubA⟩, rfl⟩, ?_⟩
        rw [hQ_C.ends_newEdge hA]
        ext v
        change v ∈ A.rootSet ↔
          qA ∈ ℳ ∧ G.toHypergraph.IsSeparation qA.1 qA.2 ∧
          (qA.1 ∩ qA.2).vertexSet ⊆ (GM10.locationCore G.toHypergraph ℳ).vertexSet ∧
          v ∈ (qA.1 ∩ qA.2).vertexSet
        exact ⟨fun hv ↦ ⟨hqA_mem, hsepA, hsubA, hrootA_eq ▸ hv⟩,
          fun h ↦ hrootA_eq.symm ▸ h.2.2.2⟩
    · rw [hpart_empty] at he
      rcases he with he_core | ⟨_, h, _⟩
      · exfalso
        have heC := (mem_rootedLocationCore_edgeSet_iff.1 he_core).1
        rw [hE_empty] at heC
        exact heC
      · exact h.elim

/-- **Claim (2)** in the proof of Graph Minors XVIII, (5.5) (page 96):
For each `C ∈ ℒ`, `G_C = mkPlaceHeartHypergraph C hℒ_C newEdge_star` is a complemented rooted
subhypergraph of `P_star.G`. -/
theorem lemma_5_5_claim_2 {P P_star : PartialPatchwork Ω α β}
    {ℒ ℒ_star : Set (RootedHypergraph α β)}
    (hℒ : IsRootedLocation P.G ℒ)
    {newEdge_star : RootedHypergraph α β → β}
    (hP_star : IsPlaceHeart P ℒ_star newEdge_star P_star)
    {partR : RootedHypergraph α β → Set (RootedHypergraph α β)}
    (hpart_sub : ∀ ⦃C⦄, C ∈ ℒ → partR C ⊆ ℒ_star)
    (hpart_union : (⋃ C ∈ ℒ, partR C) = ℒ_star)
    (hpart_le : ∀ ⦃C⦄, C ∈ ℒ → ∀ ⦃A⦄, A ∈ partR C →
      A.toHypergraph ≤ C.toHypergraph ∧
      complementHypergraph P.G C ≤ complementHypergraph P.G A)
    {C : RootedHypergraph α β} (hC : C ∈ ℒ) :
    IsComplemented P_star.G
      (mkPlaceHeartHypergraph C
        (isRootedLocation_partR hℒ hP_star.isRootedLocation hpart_sub hpart_le hC)
        newEdge_star) := by
  let G := P.G
  have hℒ_star := hP_star.isRootedLocation
  have hℒ_C := isRootedLocation_partR hℒ hℒ_star hpart_sub hpart_le hC
  let G_C := mkPlaceHeartHypergraph C hℒ_C newEdge_star
  have hcore_le := rootedLocationCore_partR_le hℒ hℒ_star hpart_sub hpart_union hpart_le hC
  have hnotMem_C : ∀ ⦃A⦄, A ∈ partR C → newEdge_star A ∉ (rootedLocationCore C (partR C)).edgeSet :=
    fun _ hA hc ↦ hP_star.newEdge_notMem_core (hpart_sub hC hA) (hcore_le.edgeSet_subset hc)
  have hinj_C : Set.InjOn newEdge_star (partR C) :=
    hP_star.injOn_newEdge.mono (hpart_sub hC)
  have hQ_C := isPlaceHeart_mkPlaceHeart (P.restrict C) hℒ_C newEdge_star hinj_C hnotMem_C
  have hG_C_le : G_C.toHypergraph ≤ P_star.G.toHypergraph :=
    { vertexSet_subset := by
        rw [hP_star.vertexSet_eq]
        exact hcore_le.vertexSet_subset
      edgeSet_subset := by
        rw [hP_star.edgeSet_eq]
        exact Set.union_subset_union hcore_le.edgeSet_subset (Set.image_mono (hpart_sub hC))
      ends_eq := fun e he ↦ by
        rcases he with he_core | ⟨A, hA, rfl⟩
        · have he_star_core := hcore_le.edgeSet_subset he_core
          have heC : e ∈ C.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 he_core).1
          rw [hP_star.ends_core he_star_core]
          exact ((hℒ.isComplemented hC).le.ends_eq e heC).trans (hQ_C.ends_core he_core).symm
        · rw [hP_star.ends_newEdge (hpart_sub hC hA)]
          exact (hQ_C.ends_newEdge hA).symm }
  have hrootSet_star : P_star.G.rootSet = G.rootSet := by
    ext v
    change v ∈ P_star.G.roots ↔ v ∈ G.roots
    rw [hP_star.roots_eq]
  refine ⟨hG_C_le, ?_, ?_⟩
  · intro v hvG_C hv_root
    rw [hrootSet_star] at hv_root
    have hvC : v ∈ C.vertexSet := (mem_rootedLocationCore_vertexSet_iff hℒ_C).1 hvG_C |>.1
    exact (hℒ.isComplemented hC).roots_mem hvC hv_root
  · intro v e hvG_C he_diff hinc_star
    have hvC : v ∈ C.vertexSet := (mem_rootedLocationCore_vertexSet_iff hℒ_C).1 hvG_C |>.1
    have he_star := he_diff.1
    rw [hP_star.edgeSet_eq] at he_star
    rcases he_star with he_core_star | ⟨A, hA_star, rfl⟩
    · have he_not_C : e ∉ C.edgeSet := by
        intro heC
        apply he_diff.2
        left
        rw [mem_rootedLocationCore_edgeSet_iff]
        refine ⟨heC, fun A hA ↦ ?_⟩
        exact (mem_rootedLocationCore_edgeSet_iff.1 he_core_star).2 A (hpart_sub hC hA)
      have heG : e ∈ G.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 he_core_star).1
      have hincG : G.Inc e v := by
        change v ∈ G.ends e
        rw [← hP_star.ends_core he_core_star]
        exact hinc_star
      exact (hℒ.isComplemented hC).inc_diff_mem hvC ⟨heG, he_not_C⟩ hincG
    · have hA_not_C : A ∉ partR C := fun hA_C ↦ he_diff.2 (Or.inr ⟨A, hA_C, rfl⟩)
      have hA_union : A ∈ ⋃ C' ∈ ℒ, partR C' := hpart_union.symm ▸ hA_star
      rw [Set.mem_iUnion₂] at hA_union
      rcases hA_union with ⟨C', hC', hA_C'⟩
      have hne : C' ≠ C := fun hEq ↦ hA_not_C (hEq ▸ hA_C')
      have hv_A : v ∈ A.rootSet := by
        rw [← hP_star.ends_newEdge hA_star]
        exact hinc_star
      have hvC' : v ∈ C'.vertexSet :=
        (hpart_le hC' hA_C').1.vertexSet_subset (A.roots_subset v hv_A)
      have hle_comp := hℒ.le_complement hC' hC hne
      exact (hle_comp.vertexSet_subset hvC').resolve_left fun h ↦ h.2 hvC

/-- **Claim (3)** in the proof of Graph Minors XVIII, (5.5) (page 96):
For each `C ∈ ℒ`, `P_star | G_C` is a heart of `(P | C, ℒ_C)` using `newEdge_star`
(`IsPlaceHeart (P.restrict C) (partR C) newEdge_star (P_star.restrict G_C)`). -/
theorem lemma_5_5_claim_3 {P P_star : PartialPatchwork Ω α β}
    {ℒ ℒ_star : Set (RootedHypergraph α β)}
    (hℒ : IsRootedLocation P.G ℒ)
    {newEdge_star : RootedHypergraph α β → β}
    (hP_star : IsPlaceHeart P ℒ_star newEdge_star P_star)
    {partR : RootedHypergraph α β → Set (RootedHypergraph α β)}
    (hpart_sub : ∀ ⦃C⦄, C ∈ ℒ → partR C ⊆ ℒ_star)
    (hpart_union : (⋃ C ∈ ℒ, partR C) = ℒ_star)
    (hpart_le : ∀ ⦃C⦄, C ∈ ℒ → ∀ ⦃A⦄, A ∈ partR C →
      A.toHypergraph ≤ C.toHypergraph ∧
      complementHypergraph P.G C ≤ complementHypergraph P.G A)
    {C : RootedHypergraph α β} (hC : C ∈ ℒ) :
    let hℒ_C := isRootedLocation_partR hℒ hP_star.isRootedLocation hpart_sub hpart_le hC
    let G_C := mkPlaceHeartHypergraph C hℒ_C newEdge_star
    IsPlaceHeart (P.restrict C) (partR C) newEdge_star (P_star.restrict G_C) := by
  intro hℒ_C G_C
  have hℒ_star := hP_star.isRootedLocation
  have hcore_le := rootedLocationCore_partR_le hℒ hℒ_star hpart_sub hpart_union hpart_le hC
  have hnotMem_C : ∀ ⦃A⦄, A ∈ partR C → newEdge_star A ∉ (rootedLocationCore C (partR C)).edgeSet :=
    fun _ hA hc ↦ hP_star.newEdge_notMem_core (hpart_sub hC hA) (hcore_le.edgeSet_subset hc)
  have hinj_C : Set.InjOn newEdge_star (partR C) :=
    hP_star.injOn_newEdge.mono (hpart_sub hC)
  have hQ_C := isPlaceHeart_mkPlaceHeart (P.restrict C) hℒ_C newEdge_star hinj_C hnotMem_C
  have hcomp_GC := lemma_5_5_claim_2 hℒ hP_star hpart_sub hpart_union hpart_le hC
  have hle_GC : G_C.toHypergraph ≤ P_star.G.toHypergraph := hcomp_GC.le
  have hle_C : C.toHypergraph ≤ P.G.toHypergraph := (hℒ.isComplemented hC).le
  refine
    { isRootedLocation := hℒ_C
      injOn_newEdge := hinj_C
      newEdge_notMem_core := hnotMem_C
      vertexSet_eq := rfl
      edgeSet_eq := rfl
      roots_eq := rfl
      ends_core := hQ_C.ends_core
      ends_newEdge := hQ_C.ends_newEdge
      dom_eq := by
        rw [P_star.restrict_dom hle_GC, hP_star.dom_eq, P.restrict_dom hle_C]
        change (((rootedLocationCore P.G ℒ_star).edgeSet ∩ P.dom) ∪ (newEdge_star '' ℒ_star)) ∩
          ((rootedLocationCore C (partR C)).edgeSet ∪ (newEdge_star '' partR C)) =
          ((rootedLocationCore C (partR C)).edgeSet ∩ (P.dom ∩ C.edgeSet)) ∪
            (newEdge_star '' partR C)
        ext e
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_image]
        constructor
        · rintro ⟨⟨he_core_star, hd⟩ | ⟨A, hA_star, rfl⟩, he_core_C | ⟨A', hA'_C, hEq⟩⟩
          · exact Or.inl ⟨he_core_C, hd, (mem_rootedLocationCore_edgeSet_iff.1 he_core_C).1⟩
          · exact Or.inr ⟨A', hA'_C, hEq⟩
          · exact (hP_star.newEdge_notMem_core hA_star (hcore_le.edgeSet_subset he_core_C)).elim
          · exact Or.inr ⟨A', hA'_C, hEq⟩
        · rintro (⟨he_core_C, hd, _⟩ | ⟨A, hA_C, rfl⟩)
          · exact ⟨Or.inl ⟨hcore_le.edgeSet_subset he_core_C, hd⟩, Or.inl he_core_C⟩
          · exact ⟨Or.inr ⟨A, hpart_sub hC hA_C, rfl⟩, Or.inr ⟨A, hA_C, rfl⟩⟩
      μ_core := fun f hf ↦ by
        rw [P.restrict_dom hle_C] at hf
        exact hP_star.μ_core ⟨hcore_le.edgeSet_subset hf.1, hf.2.1⟩
      μ_newEdge := fun A hA ↦ hP_star.μ_newEdge (hpart_sub hC hA)
      Δ_core := fun f hf ↦ by
        have hf_GC : f ∈ G_C.edgeSet := Or.inl hf
        have hf_C : f ∈ C.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 hf).1
        rw [P_star.restrict_Δ hle_GC hf_GC, hP_star.Δ_core (hcore_le.edgeSet_subset hf),
          P.restrict_Δ hle_C hf_C]
      Δ_newEdge := fun A hA ↦ by
        have hA_GC : newEdge_star A ∈ G_C.edgeSet := Or.inr ⟨A, hA, rfl⟩
        have hA_C : A.toHypergraph ≤ C.toHypergraph := (hpart_le hC hA).1
        rw [P_star.restrict_Δ hle_GC hA_GC, hP_star.Δ_newEdge (hpart_sub hC hA)]
        have hagrees := P.agrees_restrict_restrict hle_C hA_C
        have hequiv : PatchworkEquiv ((P.restrict C).restrict A) (P.restrict A) :=
          ⟨hagrees.G_eq, hagrees.dom_eq,
            fun e he ↦ hagrees.μ_eq e (((P.restrict C).restrict A).dom_subset he),
            fun e he ↦ hagrees.Δ_eq e he,
            fun e he ↦ hagrees.φ_eq e he⟩
        exact hequiv.feasibleGroupings_eq.symm
      φ_core := fun f hf ↦ hP_star.φ_core (hcore_le.edgeSet_subset hf)
      φ_newEdge := fun A hA ↦ hP_star.φ_newEdge (hpart_sub hC hA) }

/-- **Claim (4)** in the proof of Graph Minors XVIII, (5.5) (pages 96–97):
The rooted subhypergraphs `G_C` (`C ∈ ℒ`) are all distinct (`Set.InjOn`), and
`ℒ' = {G_C : C ∈ ℒ}` is a rooted location in `P_star.G`. -/
theorem lemma_5_5_claim_4 {P P_star : PartialPatchwork Ω α β}
    {ℒ ℒ_star : Set (RootedHypergraph α β)}
    (hℒ : IsRootedLocation P.G ℒ)
    {newEdge_star : RootedHypergraph α β → β}
    (hP_star : IsPlaceHeart P ℒ_star newEdge_star P_star)
    {partR : RootedHypergraph α β → Set (RootedHypergraph α β)}
    (hpart_sub : ∀ ⦃C⦄, C ∈ ℒ → partR C ⊆ ℒ_star)
    (hpart_disj : ∀ ⦃C₁⦄, C₁ ∈ ℒ → ∀ ⦃C₂⦄, C₂ ∈ ℒ → C₁ ≠ C₂ →
      Disjoint (partR C₁) (partR C₂))
    (hpart_union : (⋃ C ∈ ℒ, partR C) = ℒ_star)
    (hpart_le : ∀ ⦃C⦄, C ∈ ℒ → ∀ ⦃A⦄, A ∈ partR C →
      A.toHypergraph ≤ C.toHypergraph ∧
      complementHypergraph P.G C ≤ complementHypergraph P.G A)
    (G_of : RootedHypergraph α β → RootedHypergraph α β)
    (hG_of : ∀ ⦃C⦄ (hC : C ∈ ℒ),
      G_of C =
        mkPlaceHeartHypergraph C
          (isRootedLocation_partR hℒ hP_star.isRootedLocation hpart_sub hpart_le hC)
          newEdge_star) :
    Set.InjOn G_of ℒ ∧ IsRootedLocation P_star.G (G_of '' ℒ) := by
  have hℒ_star := hP_star.isRootedLocation
  have hcomp_of : ∀ ⦃C⦄, C ∈ ℒ → IsComplemented P_star.G (G_of C) := by
    intro C hC
    rw [hG_of hC]
    exact lemma_5_5_claim_2 hℒ hP_star hpart_sub hpart_union hpart_le hC
  have hle_comp_of : ∀ ⦃C₁⦄ (h₁ : C₁ ∈ ℒ) ⦃C₂⦄ (h₂ : C₂ ∈ ℒ), C₁ ≠ C₂ →
      (G_of C₁).toHypergraph ≤ (complement P_star.G (G_of C₂) (hcomp_of h₂)).toHypergraph := by
    intro C₁ h₁ C₂ h₂ hne
    have hℒ_C₁ := isRootedLocation_partR hℒ hℒ_star hpart_sub hpart_le h₁
    have hℒ_C₂ := isRootedLocation_partR hℒ hℒ_star hpart_sub hpart_le h₂
    have hcore₁_le := rootedLocationCore_partR_le hℒ hℒ_star hpart_sub hpart_union hpart_le h₁
    have hcore₂_le := rootedLocationCore_partR_le hℒ hℒ_star hpart_sub hpart_union hpart_le h₂
    refine (GM10.le_iff_of_le (hcomp_of h₁).le
      (hcomp_of h₂).isSeparation.isSeparation.right_le).2 ⟨?_, ?_⟩
    · intro v hv₁
      have hv_star : v ∈ P_star.G.vertexSet := (hcomp_of h₁).le.vertexSet_subset hv₁
      by_cases hv₂ : v ∈ (G_of C₂).vertexSet
      · right
        rw [hG_of h₁] at hv₁
        rw [hG_of h₂] at hv₂ ⊢
        have hvC₁ : v ∈ C₁.vertexSet := (mem_rootedLocationCore_vertexSet_iff hℒ_C₁).1 hv₁ |>.1
        have hvC₂ : v ∈ C₂.vertexSet := (mem_rootedLocationCore_vertexSet_iff hℒ_C₂).1 hv₂ |>.1
        have hle_C := hℒ.le_complement h₁ h₂ hne
        exact (hle_C.vertexSet_subset hvC₁).resolve_left fun h ↦ h.2 hvC₂
      · exact Or.inl ⟨hv_star, hv₂⟩
    · intro e he₁
      have he_star : e ∈ P_star.G.edgeSet := (hcomp_of h₁).le.edgeSet_subset he₁
      refine ⟨he_star, fun he₂ ↦ ?_⟩
      rw [hG_of h₁] at he₁
      rw [hG_of h₂] at he₂
      rcases he₁ with he_core₁ | ⟨A₁, hA₁, rfl⟩ <;> rcases he₂ with he_core₂ | ⟨A₂, hA₂, hEq⟩
      · have heC₁ := (mem_rootedLocationCore_edgeSet_iff.1 he_core₁).1
        have heC₂ := (mem_rootedLocationCore_edgeSet_iff.1 he_core₂).1
        exact ((hℒ.le_complement h₁ h₂ hne).edgeSet_subset heC₁).2 heC₂
      · exact hP_star.newEdge_notMem_core (hpart_sub h₂ hA₂)
          (hEq ▸ hcore₁_le.edgeSet_subset he_core₁)
      · exact hP_star.newEdge_notMem_core (hpart_sub h₁ hA₁)
          (hcore₂_le.edgeSet_subset he_core₂)
      · have hA_eq := hP_star.injOn_newEdge (hpart_sub h₂ hA₂) (hpart_sub h₁ hA₁) hEq
        exact Set.disjoint_left.1 (hpart_disj h₁ h₂ hne) hA₁ (hA_eq ▸ hA₂)
  have hinj_G : Set.InjOn G_of ℒ := by
    intro C₁ h₁ C₂ h₂ hEq
    by_contra hne
    have hle := hle_comp_of h₁ h₂ hne
    have hE_empty : (G_of C₁).edgeSet = ∅ := by
      ext e
      simp only [Set.mem_empty_iff_false, iff_false]
      intro he₁
      have he₂ : e ∈ (G_of C₂).edgeSet := hEq ▸ he₁
      exact (hle.edgeSet_subset he₁).2 he₂
    have h_eq_C : ∀ {C : RootedHypergraph α β} (hC : C ∈ ℒ),
        (G_of C).edgeSet = ∅ → G_of C = C := by
      intro C hC hE
      rw [hG_of hC] at hE ⊢
      have hℒ_C := isRootedLocation_partR hℒ hℒ_star hpart_sub hpart_le hC
      have hpart_empty : partR C = ∅ := by
        ext A
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hA
        have hmem : newEdge_star A ∈ (mkPlaceHeartHypergraph C hℒ_C newEdge_star).edgeSet :=
          Or.inr ⟨A, hA, rfl⟩
        rw [hE] at hmem
        exact hmem
      have hEC_empty : C.edgeSet = ∅ := by
        ext e
        simp only [Set.mem_empty_iff_false, iff_false]
        intro heC
        have hmem : e ∈ (mkPlaceHeartHypergraph C hℒ_C newEdge_star).edgeSet := by
          left
          rw [mem_rootedLocationCore_edgeSet_iff, hpart_empty]
          exact ⟨heC, fun _ h ↦ h.elim⟩
        rw [hE] at hmem
        exact hmem
      refine RootedHypergraph.ext ?_ rfl
      refine hypergraph_ext_of_ends_eq ?_ ?_ ?_
      · ext v
        change v ∈ (rootedLocationCore C (partR C)).vertexSet ↔ v ∈ C.vertexSet
        rw [mem_rootedLocationCore_vertexSet_iff hℒ_C, hpart_empty]
        exact ⟨fun h ↦ h.1, fun hv ↦ ⟨hv, fun _ h ↦ h.elim⟩⟩
      · rw [hE, hEC_empty]
      · intro e he
        rw [hE] at he
        exact he.elim
    have hG₁_C₁ : G_of C₁ = C₁ := h_eq_C h₁ hE_empty
    have hG₂_C₂ : G_of C₂ = C₂ := h_eq_C h₂ (hEq ▸ hE_empty)
    exact hne (hG₁_C₁.symm.trans (hEq.trans hG₂_C₂))
  refine ⟨hinj_G, ?_⟩
  refine
    { isComplemented := by
        rintro _ ⟨C, hC, rfl⟩
        exact hcomp_of hC
      le_complement := by
        rintro _ ⟨C₁, h₁, rfl⟩ _ ⟨C₂, h₂, rfl⟩ hne
        exact hle_comp_of h₁ h₂ fun hEq ↦ hne (congrArg G_of hEq) }

/-- **Claim (5)** in the proof of Graph Minors XVIII, (5.5) (page 97):
`M(G, ℒ) = M(G*, ℒ')`, where `ℒ' = {G_C : C ∈ ℒ}`. -/
theorem lemma_5_5_claim_5 {P P_star : PartialPatchwork Ω α β}
    {ℒ ℒ_star : Set (RootedHypergraph α β)}
    (hℒ : IsRootedLocation P.G ℒ)
    {newEdge_star : RootedHypergraph α β → β}
    (hP_star : IsPlaceHeart P ℒ_star newEdge_star P_star)
    {partR : RootedHypergraph α β → Set (RootedHypergraph α β)}
    (hpart_sub : ∀ ⦃C⦄, C ∈ ℒ → partR C ⊆ ℒ_star)
    (hpart_disj : ∀ ⦃C₁⦄, C₁ ∈ ℒ → ∀ ⦃C₂⦄, C₂ ∈ ℒ → C₁ ≠ C₂ →
      Disjoint (partR C₁) (partR C₂))
    (hpart_union : (⋃ C ∈ ℒ, partR C) = ℒ_star)
    (hpart_le : ∀ ⦃C⦄, C ∈ ℒ → ∀ ⦃A⦄, A ∈ partR C →
      A.toHypergraph ≤ C.toHypergraph ∧
      complementHypergraph P.G C ≤ complementHypergraph P.G A)
    (G_of : RootedHypergraph α β → RootedHypergraph α β)
    (hG_of : ∀ ⦃C⦄ (hC : C ∈ ℒ),
      G_of C =
        mkPlaceHeartHypergraph C
          (isRootedLocation_partR hℒ hP_star.isRootedLocation hpart_sub hpart_le hC)
          newEdge_star) :
    rootedLocationCore P.G ℒ = rootedLocationCore P_star.G (G_of '' ℒ) := by
  let G := P.G
  have hℒ_star := hP_star.isRootedLocation
  let ℒ' := G_of '' ℒ
  have hℒ' : IsRootedLocation P_star.G ℒ' :=
    (lemma_5_5_claim_4 hℒ hP_star hpart_sub hpart_disj hpart_union hpart_le G_of hG_of).2
  have hle₁ : rootedLocationCore G ℒ ≤ G.toHypergraph := locationCore_le hℒ.isLocation
  have hle_star : rootedLocationCore P_star.G ℒ' ≤ P_star.G.toHypergraph :=
    locationCore_le hℒ'.isLocation
  -- Every edge of `rootedLocationCore P_star.G ℒ'` lies in `rootedLocationCore G ℒ_star`.
  have he_in_core_star : ∀ e ∈ (rootedLocationCore P_star.G ℒ').edgeSet,
      e ∈ (rootedLocationCore G ℒ_star).edgeSet := by
    intro e he
    rw [mem_rootedLocationCore_edgeSet_iff] at he
    have he_star := he.1
    rw [hP_star.edgeSet_eq] at he_star
    rcases he_star with he_core | ⟨A, hA_star, rfl⟩
    · exact he_core
    · exfalso
      have hA_union : A ∈ ⋃ C ∈ ℒ, partR C := hpart_union.symm ▸ hA_star
      rw [Set.mem_iUnion₂] at hA_union
      rcases hA_union with ⟨C, hC, hA_C⟩
      refine he.2 (G_of C) ⟨C, hC, rfl⟩ ?_
      rw [hG_of hC]
      exact Or.inr ⟨A, hA_C, rfl⟩
  have hle₂ : rootedLocationCore P_star.G ℒ' ≤ G.toHypergraph :=
    { vertexSet_subset := by
        refine hle_star.vertexSet_subset.trans ?_
        rw [hP_star.vertexSet_eq]
        exact (locationCore_le hℒ_star.isLocation).vertexSet_subset
      edgeSet_subset := fun e he ↦
        (locationCore_le hℒ_star.isLocation).edgeSet_subset (he_in_core_star e he)
      ends_eq := fun e he ↦
        (hP_star.ends_core (he_in_core_star e he)).symm.trans (hle_star.ends_eq e he) }
  -- Use `theorem_5_4_vertexSet` on `(P.restrict C, partR C)` for each `C ∈ ℒ`.
  have h54_C : ∀ {C} (hC : C ∈ ℒ),
      C.vertexSet \ C.rootSet =
        ((G_of C).vertexSet \ (G_of C).rootSet) ∪ ⋃ A ∈ partR C, (A.vertexSet \ A.rootSet) := by
    intro C hC
    have hclaim3 := lemma_5_5_claim_3 hℒ hP_star hpart_sub hpart_union hpart_le hC
    have h54 := (theorem_5_4_place hclaim3).1
    simpa [← hG_of hC] using h54
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle₁ hle₂ ?_ ?_
  · ext v
    rw [mem_rootedLocationCore_vertexSet_iff hℒ, mem_rootedLocationCore_vertexSet_iff hℒ',
      hP_star.vertexSet_eq, mem_rootedLocationCore_vertexSet_iff hℒ_star]
    simp only [ℒ', Set.forall_mem_image]
    have hnot_diff : ∀ {B : RootedHypergraph α β},
        (v ∈ B.vertexSet → v ∈ B.rootSet) ↔ v ∉ B.vertexSet \ B.rootSet := by
      intro B
      simp only [Set.mem_sdiff, not_and, not_not]
    simp only [hnot_diff]
    rw [and_assoc]
    refine and_congr_right fun _ ↦ ?_
    constructor
    · intro hC
      refine ⟨fun A hA hvA ↦ ?_, fun {C} hc hvc ↦ ?_⟩
      · have hA_union : A ∈ ⋃ C ∈ ℒ, partR C := hpart_union.symm ▸ hA
        rw [Set.mem_iUnion₂] at hA_union
        rcases hA_union with ⟨C, hc, hA_C⟩
        apply hC C hc
        rw [h54_C hc]
        exact Or.inr (Set.mem_biUnion hA_C hvA)
      · apply hC C hc
        rw [h54_C hc]
        exact Or.inl hvc
    · rintro ⟨hA_all, hGC_all⟩ C hc hvc
      rw [h54_C hc] at hvc
      rcases hvc with hvGC | hv_union
      · exact hGC_all hc hvGC
      · rw [Set.mem_iUnion₂] at hv_union
        rcases hv_union with ⟨A, hA_C, hvA⟩
        exact hA_all A (hpart_sub hc hA_C) hvA
  · ext e
    rw [mem_rootedLocationCore_edgeSet_iff, mem_rootedLocationCore_edgeSet_iff]
    constructor
    · rintro ⟨heG, hallC⟩
      have he_core_star : e ∈ (rootedLocationCore G ℒ_star).edgeSet := by
        rw [mem_rootedLocationCore_edgeSet_iff]
        refine ⟨heG, fun A hA heA ↦ ?_⟩
        have hA_union : A ∈ ⋃ C ∈ ℒ, partR C := hpart_union.symm ▸ hA
        rw [Set.mem_iUnion₂] at hA_union
        rcases hA_union with ⟨C, hC, hA_C⟩
        exact hallC C hC ((hpart_le hC hA_C).1.edgeSet_subset heA)
      refine ⟨hP_star.edgeSet_eq ▸ Or.inl he_core_star, ?_⟩
      rintro _ ⟨C, hC, rfl⟩ heGC
      rw [hG_of hC] at heGC
      rcases heGC with he_coreC | ⟨A, hA_C, rfl⟩
      · exact hallC C hC (mem_rootedLocationCore_edgeSet_iff.1 he_coreC).1
      · exact hP_star.newEdge_notMem_core (hpart_sub hC hA_C) he_core_star
    · intro h
      have he_core_star : e ∈ (rootedLocationCore G ℒ_star).edgeSet :=
        he_in_core_star e (mem_rootedLocationCore_edgeSet_iff.2 h)
      have heG : e ∈ G.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 he_core_star).1
      refine ⟨heG, fun C hC heC ↦ ?_⟩
      apply h.2 (G_of C) ⟨C, hC, rfl⟩
      rw [hG_of hC]
      left
      rw [mem_rootedLocationCore_edgeSet_iff]
      exact ⟨heC, fun A hA_C ↦
        (mem_rootedLocationCore_edgeSet_iff.1 he_core_star).2 A (hpart_sub hC hA_C)⟩

/-- **Claim (6)** in the proof of Graph Minors XVIII, (5.5) (pages 97–98):
The heart `P'` of `(P, ℒ)` is also a heart of `(P*, ℒ')` (`HasPlaceHeart P_star ℒ' P'`). -/
theorem lemma_5_5_claim_6 {P P' P_star : PartialPatchwork Ω α β}
    {ℒ ℒ_star : Set (RootedHypergraph α β)}
    {newEdge newEdge_star : RootedHypergraph α β → β}
    (hP' : IsPlaceHeart P ℒ newEdge P')
    (hP_star : IsPlaceHeart P ℒ_star newEdge_star P_star)
    {partR : RootedHypergraph α β → Set (RootedHypergraph α β)}
    (hpart_sub : ∀ ⦃C⦄, C ∈ ℒ → partR C ⊆ ℒ_star)
    (hpart_disj : ∀ ⦃C₁⦄, C₁ ∈ ℒ → ∀ ⦃C₂⦄, C₂ ∈ ℒ → C₁ ≠ C₂ →
      Disjoint (partR C₁) (partR C₂))
    (hpart_union : (⋃ C ∈ ℒ, partR C) = ℒ_star)
    (hpart_le : ∀ ⦃C⦄, C ∈ ℒ → ∀ ⦃A⦄, A ∈ partR C →
      A.toHypergraph ≤ C.toHypergraph ∧
      complementHypergraph P.G C ≤ complementHypergraph P.G A)
    (G_of : RootedHypergraph α β → RootedHypergraph α β)
    (hG_of : ∀ ⦃C⦄ (hC : C ∈ ℒ),
      G_of C =
        mkPlaceHeartHypergraph C
          (isRootedLocation_partR hP'.isRootedLocation hP_star.isRootedLocation hpart_sub hpart_le
            hC)
          newEdge_star) :
    HasPlaceHeart P_star (G_of '' ℒ) P' := by
  classical
  have hℒ := hP'.isRootedLocation
  have hℒ_star := hP_star.isRootedLocation
  obtain ⟨hinj_G, hℒ'⟩ :=
    lemma_5_5_claim_4 hℒ hP_star hpart_sub hpart_disj hpart_union hpart_le G_of hG_of
  have hcore_eq : rootedLocationCore P.G ℒ = rootedLocationCore P_star.G (G_of '' ℒ) :=
    lemma_5_5_claim_5 hℒ hP_star hpart_sub hpart_disj hpart_union hpart_le G_of hG_of
  -- Every edge in `rootedLocationCore P.G ℒ` also belongs to `rootedLocationCore P.G ℒ_star`.
  have hcore_sub_star :
      (rootedLocationCore P.G ℒ).edgeSet ⊆ (rootedLocationCore P.G ℒ_star).edgeSet := by
    intro e he
    rw [mem_rootedLocationCore_edgeSet_iff] at he ⊢
    refine ⟨he.1, fun A hA heA ↦ ?_⟩
    have hA_union : A ∈ ⋃ C ∈ ℒ, partR C := hpart_union.symm ▸ hA
    rw [Set.mem_iUnion₂] at hA_union
    rcases hA_union with ⟨C, hC, hA_C⟩
    exact he.2 C hC ((hpart_le hC hA_C).1.edgeSet_subset heA)
  let newEdge' : RootedHypergraph α β → β := fun B ↦
    if h : ∃ C ∈ ℒ, G_of C = B then newEdge h.choose else newEdge B
  have hnewEdge'_eq : ∀ ⦃C⦄, C ∈ ℒ → newEdge' (G_of C) = newEdge C := by
    intro C hC
    have hex : ∃ C' ∈ ℒ, G_of C' = G_of C := ⟨C, hC, rfl⟩
    simp only [newEdge', hex, ↓reduceDIte]
    exact congrArg newEdge (hinj_G hex.choose_spec.1 hC hex.choose_spec.2)
  have himg_eq : newEdge' '' (G_of '' ℒ) = newEdge '' ℒ := by
    ext e
    simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨C, hC, rfl⟩, rfl⟩
      exact ⟨C, hC, (hnewEdge'_eq hC).symm⟩
    · rintro ⟨C, hC, rfl⟩
      exact ⟨G_of C, ⟨C, hC, rfl⟩, hnewEdge'_eq hC⟩
  refine ⟨newEdge', ?_⟩
  refine
    { isRootedLocation := hℒ'
      injOn_newEdge := by
        rintro _ ⟨C₁, h₁, rfl⟩ _ ⟨C₂, h₂, rfl⟩ hEq
        rw [hnewEdge'_eq h₁, hnewEdge'_eq h₂] at hEq
        exact congrArg G_of (hP'.injOn_newEdge h₁ h₂ hEq)
      newEdge_notMem_core := by
        rintro _ ⟨C, hC, rfl⟩
        rw [← hcore_eq, hnewEdge'_eq hC]
        exact hP'.newEdge_notMem_core hC
      vertexSet_eq := hP'.vertexSet_eq.trans (congrArg Hypergraph.vertexSet hcore_eq)
      edgeSet_eq := by
        rw [hP'.edgeSet_eq, hcore_eq, himg_eq]
      roots_eq := hP'.roots_eq.trans hP_star.roots_eq.symm
      ends_core := fun f hf ↦ by
        rw [← hcore_eq] at hf
        rw [hP'.ends_core hf, hP_star.ends_core (hcore_sub_star hf)]
      ends_newEdge := by
        rintro _ ⟨C, hC, rfl⟩
        rw [hnewEdge'_eq hC, hP'.ends_newEdge hC, hG_of hC]
        rfl
      dom_eq := by
        rw [hP'.dom_eq, ← hcore_eq, himg_eq]
        congr 1
        ext e
        simp only [Set.mem_inter_iff]
        refine and_congr_right fun he ↦ ?_
        rw [hP_star.dom_eq]
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_image]
        exact ⟨fun hd ↦ Or.inl ⟨hcore_sub_star he, hd⟩,
          fun h ↦ h.elim (fun h1 ↦ h1.2)
            (fun ⟨A, hA, hEq⟩ ↦ (hP_star.newEdge_notMem_core hA (hEq ▸ hcore_sub_star he)).elim)⟩
      μ_core := fun f hf ↦ by
        rw [← hcore_eq] at hf
        have hf_core := hf.1
        have hf_dom_star := hf.2
        rw [hP_star.dom_eq] at hf_dom_star
        rcases hf_dom_star with ⟨hf_star_core, hf_dom⟩ | ⟨A, hA, rfl⟩
        · rw [hP'.μ_core ⟨hf_core, hf_dom⟩, hP_star.μ_core ⟨hf_star_core, hf_dom⟩]
        · exact (hP_star.newEdge_notMem_core hA (hcore_sub_star hf_core)).elim
      μ_newEdge := by
        rintro _ ⟨C, hC, rfl⟩
        rw [hnewEdge'_eq hC, hP'.μ_newEdge hC, hG_of hC]
        rfl
      Δ_core := fun f hf ↦ by
        rw [← hcore_eq] at hf
        rw [hP'.Δ_core hf, hP_star.Δ_core (hcore_sub_star hf)]
      Δ_newEdge := by
        rintro _ ⟨C, hC, rfl⟩
        rw [hnewEdge'_eq hC, hP'.Δ_newEdge hC, hG_of hC]
        have hclaim3 := lemma_5_5_claim_3 hℒ hP_star hpart_sub hpart_union hpart_le hC
        exact (theorem_5_4_place hclaim3).2
      φ_core := fun f hf ↦ by
        rw [← hcore_eq] at hf
        rw [hP'.φ_core hf, hP_star.φ_core (hcore_sub_star hf)]
      φ_newEdge := by
        rintro _ ⟨C, hC, rfl⟩
        rw [hnewEdge'_eq hC, hP'.φ_newEdge hC] }

/-- **Graph Minors XVIII, (5.5)** (page 95):
"Let $P = (G, \mu, \Delta, \phi)$ be an $\Omega$-patchwork, let $w \ge 0$, and let
$\mathscr{L}, \mathscr{L}^*$ be rooted locations in $G$, such that $\mathscr{L}^{*-}$ is an
enlargement of $\mathscr{L}^-$ by tree-width $\le w$. Then $P | \mathscr{L}^*$ is an
enlargement of $P | \mathscr{L}$ by tree-width $\le w$." -/
theorem theorem_5_5_proof {P P' P_star : PartialPatchwork Ω α β}
    {ℒ ℒ_star : Set (RootedHypergraph α β)} {w : ℕ}
    (hP' : HasPlaceHeart P ℒ P')
    (hP_star : HasPlaceHeart P ℒ_star P_star)
    (henl : IsLocationEnlargementByTreeWidth P.G.toHypergraph
      (rootedLocationToLocation P.G ℒ) (rootedLocationToLocation P.G ℒ_star) (w : ℚ)) :
    IsPlaceEnlargementByTreeWidth w P' P_star := by
  classical
  obtain ⟨newEdge, hheart⟩ := hP'
  obtain ⟨newEdge_star, hheart_star⟩ := hP_star
  obtain ⟨_, part_loc, hvia, htw⟩ := henl
  let G := P.G
  have hℒ := hheart.isRootedLocation
  have hℒ_star := hheart_star.isRootedLocation
  let toLoc : RootedHypergraph α β → Hypergraph α β × Hypergraph α β :=
    fun A ↦ (A.toHypergraph, complementHypergraph G A)
  -- For each `p ∈ rootedLocationToLocation G ℒ`, choose a representative `rep p ∈ ℒ` with
  -- `toLoc (rep p) = p`.
  let rep : Hypergraph α β × Hypergraph α β → RootedHypergraph α β := fun p ↦
    if hp : ∃ C ∈ ℒ, toLoc C = p then hp.choose else G
  have hrep_spec : ∀ {C : RootedHypergraph α β}, C ∈ ℒ →
      rep (toLoc C) ∈ ℒ ∧ toLoc (rep (toLoc C)) = toLoc C := by
    intro C hC
    have hex : ∃ C' ∈ ℒ, toLoc C' = toLoc C := ⟨C, hC, rfl⟩
    simp only [rep, hex, ↓reduceDIte]
    exact hex.choose_spec
  let partR : RootedHypergraph α β → Set (RootedHypergraph α β) := fun C ↦
    if C = rep (toLoc C) then {A ∈ ℒ_star | toLoc A ∈ part_loc (toLoc C)} else ∅
  have hpart_sub : ∀ ⦃C⦄, C ∈ ℒ → partR C ⊆ ℒ_star := by
    intro C _ A hA
    dsimp only [partR] at hA
    split_ifs at hA
    · exact hA.1
    · exact hA.elim
  have hpart_disj : ∀ ⦃C₁⦄, C₁ ∈ ℒ → ∀ ⦃C₂⦄, C₂ ∈ ℒ → C₁ ≠ C₂ →
      Disjoint (partR C₁) (partR C₂) := by
    intro C₁ h₁ C₂ h₂ hne
    rw [Set.disjoint_left]
    intro A hA₁ hA₂
    dsimp only [partR] at hA₁ hA₂
    split_ifs at hA₁ with hrep₁ <;> split_ifs at hA₂ with hrep₂
    · have hp_ne : toLoc C₁ ≠ toLoc C₂ := by
        intro hp_eq
        apply hne
        rw [hrep₁, hrep₂, hp_eq]
      exact Set.disjoint_left.1
        (hvia.part_disjoint ⟨C₁, h₁, rfl⟩ ⟨C₂, h₂, rfl⟩ hp_ne) hA₁.2 hA₂.2
    · exact hA₂
    · exact hA₁
    · exact hA₁
  have hpart_union : (⋃ C ∈ ℒ, partR C) = ℒ_star := by
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun C hC ↦ hpart_sub hC
    · intro A hA
      have hlocA : toLoc A ∈ rootedLocationToLocation G ℒ_star := ⟨A, hA, rfl⟩
      rw [← hvia.biUnion_eq, Set.mem_iUnion₂] at hlocA
      rcases hlocA with ⟨p, ⟨C₀, hC₀, rfl⟩, hA_part⟩
      let C := rep (toLoc C₀)
      have ⟨hC_ℒ, hC_eq⟩ := hrep_spec hC₀
      have hC_rep : C = rep (toLoc C) := by
        dsimp only [C]
        rw [hC_eq]
      refine Set.mem_iUnion₂.2 ⟨C, hC_ℒ, ?_⟩
      dsimp only [partR]
      split_ifs
      exact ⟨hA, hC_eq ▸ hA_part⟩
  have hpart_le : ∀ ⦃C⦄, C ∈ ℒ → ∀ ⦃A⦄, A ∈ partR C →
      A.toHypergraph ≤ C.toHypergraph ∧
      complementHypergraph G C ≤ complementHypergraph G A := by
    intro C hC A hA
    dsimp only [partR] at hA
    split_ifs at hA with hrep
    · exact hvia.le_of_mem_part ⟨C, hC, rfl⟩ hA.2
    · exact hA.elim
  have hpart_case : ∀ ⦃C⦄, C ∈ ℒ →
      rootedLocationToLocation G (partR C) =
        part_loc (C.toHypergraph, complementHypergraph G C) ∨
      (partR C = ∅ ∧ C.edgeSet = ∅ ∧ C.vertexSet = C.rootSet) := by
    intro C hC
    by_cases hrep : C = rep (toLoc C)
    · left
      have hpartR_eq : partR C = {A ∈ ℒ_star | toLoc A ∈ part_loc (toLoc C)} := by
        dsimp only [partR]
        split_ifs
        rfl
      ext q
      simp only [rootedLocationToLocation, hpartR_eq, Set.mem_image, Set.mem_sep_iff]
      constructor
      · rintro ⟨A, ⟨_, hq⟩, rfl⟩
        exact hq
      · intro hq
        have hq_star := hvia.part_subset ⟨C, hC, rfl⟩ hq
        rcases hq_star with ⟨A, hA_star, rfl⟩
        exact ⟨A, ⟨hA_star, hq⟩, rfl⟩
    · right
      have hempty : partR C = ∅ := by simp [partR, hrep]
      have ⟨hrep_ℒ, hrep_eq⟩ := hrep_spec hC
      have hH_eq : C.toHypergraph = (rep (toLoc C)).toHypergraph :=
        (congrArg Prod.fst hrep_eq).symm
      obtain ⟨hE, hV⟩ := eq_rootSet_of_toHypergraph_eq_of_ne hℒ hC hrep_ℒ hrep hH_eq
      exact ⟨hempty, hE, hV⟩
  let G_of : RootedHypergraph α β → RootedHypergraph α β := fun C ↦
    if hC : C ∈ ℒ then
      mkPlaceHeartHypergraph C (isRootedLocation_partR hℒ hℒ_star hpart_sub hpart_le hC)
        newEdge_star
    else G
  have hG_of : ∀ ⦃C⦄ (hC : C ∈ ℒ),
      G_of C =
        mkPlaceHeartHypergraph C
          (isRootedLocation_partR hℒ hℒ_star hpart_sub hpart_le hC)
          newEdge_star := by
    intro C hC
    simp only [G_of, hC, ↓reduceDIte]
  obtain ⟨_, hℒ'⟩ :=
    lemma_5_5_claim_4 hℒ hheart_star hpart_sub hpart_disj hpart_union hpart_le G_of hG_of
  have hheart' :=
    lemma_5_5_claim_6 hheart hheart_star hpart_sub hpart_disj hpart_union hpart_le G_of hG_of
  refine ⟨G_of '' ℒ, hℒ', hheart', ?_⟩
  rintro _ ⟨C, hC, rfl⟩
  rw [hG_of hC]
  have hclaim3 := lemma_5_5_claim_3 hℒ hheart_star hpart_sub hpart_union hpart_le hC
  exact lemma_5_5_claim_1 hℒ hℒ_star hvia htw hpart_sub hpart_le hpart_case hC hclaim3

end GraphMinor.GM18
end
