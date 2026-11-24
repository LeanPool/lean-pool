/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section2
public import LeanPool.GraphMinor.GM04.Patchwork.Expansion

/-!
# Tools for the sets of patchworks of Graph Minors XX

The paper changes one part of a patchwork at a time and keeps the rest. This file provides the
matching tools:
- `Patchwork.IsRealization.congr`: a realization depends only on `V(G)`, `E(G)` and `Δ`.
- `SameBase P Q`: `P` and `Q` have the same hypergraph, and the same `dom(μ)`, `μ` and `Δ`.
- `Patchwork.relabel`: the same patchwork with new labels `φ`.
- `Patchwork.reroot`: the same patchwork with a new march of roots.
- `realizable_transfer`: a realizable expansion stays one when the roots and labels of
  the two patchworks change, if the conditions on roots and labels still hold.
- `completions`, and `wellBehaved_of_encoding`, the form of (4.2) used in the proofs.
- `Discrete`, a set ordered by equality, and `wqo_disjointUnion`, that `Ω₁ ∪ Ω₂` is a
  well-quasi-order.
- `WellBehaved.union`: the union of two well-behaved sets is well-behaved.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set GraphMinor.GM18 GraphMinor.GM10 Hypergraph GraphMinor.GM04

universe u v w

variable {α : Type u} {β : Type v} {Ω Ω' Ω₁ Ω₂ : Type*}

/-- `P` and `Q` have the same hypergraph, and the same `dom(μ)`, `μ` and `Δ`: they differ at most in
their roots and labels. -/
structure SameBase (P : Patchwork Ω α β) (Q : Patchwork Ω' α β) : Prop where
  hyper : Q.G.toHypergraph = P.G.toHypergraph
  dom_eq : Q.dom = P.dom
  μ_eq : ∀ ⦃e⦄, e ∈ P.dom → Q.μ e = P.μ e
  Δ_eq : ∀ ⦃e⦄, e ∈ P.G.edgeSet → Q.Δ e = P.Δ e

theorem SameBase.refl (P : Patchwork Ω α β) : SameBase P P := ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦
  rfl⟩

theorem SameBase.vertexSet_eq {P : Patchwork Ω α β} {Q : Patchwork Ω' α β} (h : SameBase P Q) :
    Q.G.vertexSet = P.G.vertexSet := congrArg Hypergraph.vertexSet h.hyper

theorem SameBase.edgeSet_eq {P : Patchwork Ω α β} {Q : Patchwork Ω' α β} (h : SameBase P Q) :
    Q.G.edgeSet = P.G.edgeSet := congrArg Hypergraph.edgeSet h.hyper

theorem SameBase.inc_eq {P : Patchwork Ω α β} {Q : Patchwork Ω' α β} (h : SameBase P Q) :
    Q.G.Inc = P.G.Inc := congrArg Hypergraph.Inc h.hyper

theorem SameBase.symm {P : Patchwork Ω α β} {Q : Patchwork Ω' α β} (h : SameBase P Q) :
    SameBase Q P where
  hyper := h.hyper.symm
  dom_eq := h.dom_eq.symm
  μ_eq _ he := (h.μ_eq (h.dom_eq ▸ he)).symm
  Δ_eq _ he := (h.Δ_eq (h.edgeSet_eq ▸ he)).symm

theorem SameBase.trans {P : Patchwork Ω α β} {Q : Patchwork Ω' α β} {R : Patchwork Ω₁ α β}
    (h : SameBase P Q) (h' : SameBase Q R) : SameBase P R where
  hyper := h'.hyper.trans h.hyper
  dom_eq := h'.dom_eq.trans h.dom_eq
  μ_eq _ he := (h'.μ_eq (h.dom_eq ▸ he)).trans (h.μ_eq he)
  Δ_eq _ he := (h'.Δ_eq (h.edgeSet_eq ▸ he)).trans (h.Δ_eq he)

theorem IsCompletionOf.sameBase {P : Patchwork Ω α β} {Q : Patchwork Ω' α β}
    (h : IsCompletionOf P Q) : SameBase P Q :=
  ⟨congrArg RootedHypergraph.toHypergraph h.G_eq, h.dom_eq, h.μ_eq, h.Δ_eq⟩

/-- The patchwork `P` with labels `φ`. -/
def _root_.GraphMinor.GM04.Patchwork.relabel (P : Patchwork Ω α β) (φ : β → Ω') :
    Patchwork Ω' α β where
  G := P.G
  dom := P.dom
  μ := P.μ
  Δ := P.Δ
  φ := φ
  dom_subset := P.dom_subset
  μ_nodup := P.μ_nodup
  μ_set := P.μ_set
  Δ_verts := P.Δ_verts
  Δ_free := P.Δ_free

theorem isCompletionOf_relabel (P : Patchwork Ω α β) (φ : β → Ω') :
    IsCompletionOf P (P.relabel φ) :=
  ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- The rooted hypergraph `G` with roots the march `r`. -/
def _root_.GraphMinor.RootedHypergraph.reroot (G : RootedHypergraph α β) (r : List α)
    (hr : r.Nodup) (hs : ∀ v ∈ r, v ∈ G.vertexSet) : RootedHypergraph α β where
  toHypergraph := G.toHypergraph
  roots := r
  roots_nodup := hr
  roots_subset := hs

/-- The patchwork `P` with roots the march `r`. -/
def _root_.GraphMinor.GM04.Patchwork.reroot (P : Patchwork Ω α β) (r : List α) (hr : r.Nodup)
    (hs : ∀ v ∈ r, v ∈ P.G.vertexSet) : Patchwork Ω α β where
  G := P.G.reroot r hr hs
  dom := P.dom
  μ := P.μ
  Δ := P.Δ
  φ := P.φ
  dom_subset := P.dom_subset
  μ_nodup := P.μ_nodup
  μ_set := P.μ_set
  Δ_verts := P.Δ_verts
  Δ_free := P.Δ_free

theorem _root_.GraphMinor.GM04.Patchwork.IsRealization.congr {P : Patchwork Ω α β}
    {Q : Patchwork Ω' α β} {H : (⊤ : SimpleGraph α).Subgraph} (hH : P.IsRealization H)
    (hV : Q.G.vertexSet = P.G.vertexSet) (hE : Q.G.edgeSet = P.G.edgeSet)
    (hΔ : ∀ e ∈ P.G.edgeSet, Q.Δ e = P.Δ e) : Q.IsRealization H := by
  obtain ⟨δ, hδ, rfl⟩ := hH
  refine ⟨δ, fun e he ↦ ?_, ?_⟩
  · rw [hE] at he
    change δ e ∈ (Q.Δ e).groupings
    rw [hΔ e he]
    exact hδ e he
  · simp only [realizationOf, hV, hE]

theorem SameBase.realization {P : Patchwork Ω α β} {Q : Patchwork Ω' α β} (h : SameBase P Q)
    (F : Set β) {H : (⊤ : SimpleGraph α).Subgraph} (hH : (P.deleteEdges F).IsRealization H) :
    (Q.deleteEdges F).IsRealization H := by
  obtain ⟨δ, hδ, rfl⟩ := hH
  refine ⟨δ, fun e he ↦ ?_, ?_⟩
  · have he' : e ∈ P.G.edgeSet \ F := by
      have : e ∈ Q.G.edgeSet \ F := he
      rwa [h.edgeSet_eq] at this
    have := hδ e he'
    change δ e ∈ Q.Δ e
    rw [h.Δ_eq he'.1]
    exact this
  · have : (Q.deleteEdges F).G.toHypergraph = (P.deleteEdges F).G.toHypergraph := by
      change Q.G.toHypergraph.deleteEdges F = P.G.toHypergraph.deleteEdges F
      rw [h.hyper]
    rw [this]

/-- A realizable expansion of `P` in `P'` is a realizable expansion of `Q` in `Q'`, if `Q`, `Q'`
differ from `P`, `P'` only in roots and labels, and the conditions on roots and labels hold for
`Q` and `Q'`. -/
theorem realizable_transfer [Preorder Ω₁] [Preorder Ω₂]
    {P P' : Patchwork Ω₁ α β} {Q Q' : Patchwork Ω₂ α β} {ηv : α → Set α} {ηe : β → β}
    (h : IsRealizableExpansion P P' ηv ηe) (hP : SameBase P Q) (hP' : SameBase P' Q')
    (hφ : ∀ e ∈ Q.G.edgeSet, Q.φ e ≤ Q'.φ (ηe e))
    (hlen : Q.G.roots.length = Q'.G.roots.length)
    (hroots : ∀ (i : ℕ) (hi : i < Q.G.roots.length) (hi' : i < Q'.G.roots.length),
      Q'.G.roots[i] ∈ ηv Q.G.roots[i]) :
    IsRealizableExpansion Q Q' ηv ηe := by
  obtain ⟨hη, H, hH, hcomp⟩ := h
  have hV := hP.vertexSet_eq
  have hE := hP.edgeSet_eq
  have hV' := hP'.vertexSet_eq
  have hE' := hP'.edgeSet_eq
  have hD := hP.dom_eq
  have hD' := hP'.dom_eq
  have hI := hP.inc_eq
  have hI' := hP'.inc_eq
  refine ⟨?_, H, ?_, ?_⟩
  · refine
    { vertex_nonempty := fun v hv ↦ hη.vertex_nonempty v (hV ▸ hv)
      vertex_subset := fun v hv ↦ hV' ▸ hη.vertex_subset v (hV ▸ hv)
      edge_mem := fun e he ↦ hE' ▸ hη.edge_mem e (hE ▸ he)
      vertex_disjoint := fun v₁ h₁ v₂ h₂ hne ↦ hη.vertex_disjoint v₁ (hV ▸ h₁) v₂ (hV ▸ h₂) hne
      edge_injOn := hE ▸ hη.edge_injOn
      mem_dom_iff := fun e he ↦ by rw [hD, hD']; exact hη.mem_dom_iff e (hE ▸ he)
      ends_nonempty := fun e he hd v hv ↦ by
        rw [hI] at hv
        simp only [hI']
        exact hη.ends_nonempty e (hE ▸ he) (hD ▸ hd) v hv
      μ_length := fun e he ↦ by
        have he₁ : e ∈ P.dom := hD ▸ he
        have he₂ : ηe e ∈ P'.dom := (hη.mem_dom_iff e (P.dom_subset he₁)).mp he₁
        rw [hP.μ_eq he₁, hP'.μ_eq he₂]
        exact hη.μ_length e he₁
      μ_mem := fun e he i hi hi' ↦ by
        have he₁ : e ∈ P.dom := hD ▸ he
        have he₂ : ηe e ∈ P'.dom := (hη.mem_dom_iff e (P.dom_subset he₁)).mp he₁
        simp only [hP.μ_eq he₁, hP'.μ_eq he₂] at hi hi' ⊢
        exact hη.μ_mem e he₁ i hi hi'
      roots_length := hlen
      roots_mem := hroots
      maps_Δ := fun e he ↦ by
        have he₁ : e ∈ P.dom := hD ▸ he
        have he₂ : ηe e ∈ P'.dom := (hη.mem_dom_iff e (P.dom_subset he₁)).mp he₁
        rw [hP.μ_eq he₁, hP'.μ_eq he₂, hP.Δ_eq (P.dom_subset he₁), hP'.Δ_eq (P'.dom_subset he₂)]
        exact hη.maps_Δ e he₁
      φ_le := hφ }
  · rw [hE]
    exact hP'.realization _ hH
  · intro v hv
    exact hcomp v (hV ▸ hv)

/-- All `Ω`-completions of members of `𝓕`. -/
def completions (Ω : Type*) (𝓕 : Set (UnlabeledPatchwork α β)) : Set (Patchwork Ω α β) :=
  {Q | ∃ P ∈ 𝓕, IsCompletionOf P Q}

/-- Graph Minors XX, (4.2) (page 331), in the form used in the proofs: instead of an encoding `γ` we
have a relation `R`, which lets the choice of `γ(Q)` be made in the proof that `R` is total. -/
theorem wellBehaved_of_encoding {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)} (h₁ : WellBehaved 𝓕₁)
    (h : ∀ (Ω₂ : Type (max u v)) [Preorder Ω₂], WellQuasiOrderedLE Ω₂ →
      ∃ (Ω₁ : Type (max u v)) (_ : Preorder Ω₁) (_ : WellQuasiOrderedLE Ω₁)
        (R : Patchwork Ω₂ α β → Patchwork Ω₁ α β → Prop),
        (∀ Q ∈ completions Ω₂ 𝓕₂, ∃ Q' ∈ completions Ω₁ 𝓕₁, R Q Q') ∧
        ∀ Q ∈ completions Ω₂ 𝓕₂, ∀ Q' ∈ completions Ω₂ 𝓕₂, ∀ S S', R Q S → R Q' S' →
          Simulated S S' → Simulated Q Q') :
    WellBehaved 𝓕₂ := by
  intro Ω₂ _ hΩ₂ Q hQ
  obtain ⟨Ω₁, _, hΩ₁, R, hR, henc⟩ := h Ω₂ hΩ₂
  choose S hS hQS using fun i ↦ hR (Q i) (hQ i)
  obtain ⟨i, j, hij, hsim⟩ := h₁ Ω₁ hΩ₁ S hS
  exact ⟨i, j, hij, henc _ (hQ i) _ (hQ j) _ _ (hQS i) (hQS j) hsim⟩

/-- Graph Minors XX, (4.2) (page 331): "Let $\mathcal{F}_1, \mathcal{F}_2$ be sets of patchworks
where $\mathcal{F}_1$ is
well-behaved. Suppose that for every well-quasi-order $\Omega_2$ there is a well-quasi-order
$\Omega_1$ and an encoding of the set of all $\Omega_2$-completions of members of
$\mathcal{F}_2$ in the set of all $\Omega_1$-completions of members of $\mathcal{F}_1$. Then
$\mathcal{F}_2$ is well-behaved." -/
theorem theorem_4_2_proof {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)} (h₁ : WellBehaved 𝓕₁)
    (h : ∀ (Ω₂ : Type (max u v)) [Preorder Ω₂], WellQuasiOrderedLE Ω₂ →
      ∃ (Ω₁ : Type (max u v)) (_ : Preorder Ω₁) (_ : WellQuasiOrderedLE Ω₁)
        (γ : Patchwork Ω₂ α β → Patchwork Ω₁ α β),
        IsEncoding (completions Ω₁ 𝓕₁) (completions Ω₂ 𝓕₂) γ) :
    WellBehaved 𝓕₂ := by
  refine wellBehaved_of_encoding h₁ fun Ω₂ _ hΩ₂ ↦ ?_
  obtain ⟨Ω₁, i₁, i₂, γ, hγ₁, hγ₂⟩ := h Ω₂ hΩ₂
  refine ⟨Ω₁, i₁, i₂, fun Q S ↦ γ Q = S, fun Q hQ ↦ ⟨_, hγ₁ Q hQ, rfl⟩, ?_⟩
  rintro Q hQ Q' hQ' _ _ rfl rfl hsim
  exact hγ₂ Q hQ Q' hQ' hsim

/-- A set ordered by equality, such as the two-element antichain of the proof of (4.1). -/
def Discrete (X : Type*) := X

instance {X : Type*} : Preorder (Discrete X) where
  le := Eq
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans

theorem wqo_discrete (X : Type*) [Finite X] : WellQuasiOrderedLE (Discrete X) := by
  have : Finite (Discrete X) := ‹Finite X›
  exact ⟨Finite.wellQuasiOrdered _⟩

/-- From a function `ℕ → Prop`, one of the value sets is infinite: either `p` holds infinitely often
or it fails infinitely often. -/
theorem exists_strictMono_of_or (p q : ℕ → Prop) (h : ∀ n, p n ∨ q n) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ((∀ n, p (g n)) ∨ ∀ n, q (g n)) := by
  by_cases hp : ∀ N, ∃ n > N, p n
  · obtain ⟨g, hg, hpg⟩ := Nat.exists_strictMono_subsequence hp
    exact ⟨g, hg, Or.inl hpg⟩
  · push Not at hp
    obtain ⟨N, hN⟩ := hp
    obtain ⟨g, hg, hqg⟩ := Nat.exists_strictMono_subsequence (P := q)
      fun M ↦ ⟨max M N + 1, by omega, (h _).resolve_left (hN _ (by omega))⟩
    exact ⟨g, hg, Or.inr hqg⟩

/-- `Ω₁ ∪ Ω₂` is a well-quasi-order when `Ω₁` and `Ω₂` are. -/
theorem wqo_disjointUnion {Ω₁ Ω₂ : Type*} [Preorder Ω₁] [Preorder Ω₂] (h₁ : WellQuasiOrderedLE Ω₁)
    (h₂ : WellQuasiOrderedLE Ω₂) : WellQuasiOrderedLE (DisjointUnionQuasiOrder Ω₁ Ω₂) := by
  refine ⟨fun f ↦ ?_⟩
  obtain ⟨g, hg, hor⟩ := exists_strictMono_of_or (fun n ↦ ∃ a, f n = Sum.inl a)
    (fun n ↦ ∃ b, f n = Sum.inr b) fun n ↦ by
      have h : ∀ x : Ω₁ ⊕ Ω₂, (∃ a, x = Sum.inl a) ∨ ∃ b, x = Sum.inr b := by
        rintro (a | b)
        · exact Or.inl ⟨a, rfl⟩
        · exact Or.inr ⟨b, rfl⟩
      exact h (f n)
  rcases hor with h | h
  · choose a ha using h
    obtain ⟨i, j, hij, hle⟩ := h₁.wqo a
    exact ⟨g i, g j, hg hij, by rw [ha, ha]; exact DisjointUnionLE.inl hle⟩
  · choose a ha using h
    obtain ⟨i, j, hij, hle⟩ := h₂.wqo a
    exact ⟨g i, g j, hg hij, by rw [ha, ha]; exact DisjointUnionLE.inr hle⟩

/-- The union of two well-behaved sets of patchworks is well-behaved (used in the proofs of (4.3)
and
(4.8)). A sequence of completions has a subsequence of completions of members of one of the two. -/
theorem WellBehaved.union {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)} (h₁ : WellBehaved 𝓕₁)
    (h₂ : WellBehaved 𝓕₂) : WellBehaved (𝓕₁ ∪ 𝓕₂) := by
  intro Ω _ hΩ Q hQ
  obtain ⟨g, hg, hor⟩ := exists_strictMono_of_or (fun n ↦ ∃ P ∈ 𝓕₁, IsCompletionOf P (Q n))
    (fun n ↦ ∃ P ∈ 𝓕₂, IsCompletionOf P (Q n)) fun n ↦ by
      obtain ⟨P, hP | hP, hc⟩ := hQ n
      · exact Or.inl ⟨P, hP, hc⟩
      · exact Or.inr ⟨P, hP, hc⟩
  rcases hor with h | h
  · obtain ⟨i, j, hij, hs⟩ := h₁ Ω hΩ (fun n ↦ Q (g n)) h
    exact ⟨g i, g j, hg hij, hs⟩
  · obtain ⟨i, j, hij, hs⟩ := h₂ Ω hΩ (fun n ↦ Q (g n)) h
    exact ⟨g i, g j, hg hij, hs⟩

/-- A subset of a well-behaved set is well-behaved. -/
theorem WellBehaved.mono {𝓕₁ 𝓕₂ : Set (UnlabeledPatchwork α β)} (h₁ : WellBehaved 𝓕₁)
    (hs : 𝓕₂ ⊆ 𝓕₁) : WellBehaved 𝓕₂ := fun Ω _ hΩ Q hQ ↦
  h₁ Ω hΩ Q fun i ↦ (hQ i).imp fun _ h ↦ ⟨hs h.1, h.2⟩

/-- The union of finitely many well-behaved sets is well-behaved. -/
theorem WellBehaved.iUnion_lt {𝓕 : ℕ → Set (UnlabeledPatchwork α β)} (n : ℕ)
    (h : ∀ i < n, WellBehaved (𝓕 i)) : WellBehaved (⋃ i, ⋃ _ : i < n, 𝓕 i) := by
  induction n with
  | zero =>
    intro Ω _ _ Q hQ
    obtain ⟨P, hP, _⟩ := hQ 0
    simp at hP
  | succ n ih =>
    refine ((ih fun i hi ↦ h i (Nat.lt_succ_of_lt hi)).union (h n n.lt_succ_self)).mono ?_
    intro P hP
    simp only [mem_iUnion, exists_prop] at hP
    obtain ⟨i, hi, hP⟩ := hP
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact Or.inl (by simp only [mem_iUnion, exists_prop]; exact ⟨i, hi, hP⟩)
    · exact Or.inr hP

end GraphMinor.GM20
