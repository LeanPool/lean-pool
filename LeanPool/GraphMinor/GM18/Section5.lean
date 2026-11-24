/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM18.Section5Part1
public import LeanPool.GraphMinor.GM18.Section5Part2
import LeanPool.GraphMinor.GM04.Patchwork.Expansion
import LeanPool.GraphMinor.GM04.Patchwork.Stars

/-!
# Graph Minors XVIII, Section 5 (continued): Theorems (5.6) and (5.7)

This file completes the formalization of Section 5 ("Patchworks and places", pages 91–100) of
Robertson and Seymour, *Graph Minors. XVIII. Tree-decompositions and well-quasi-ordering*,
J. Combin. Theory Ser. B 89 (2003), 77–108:

- `theorem_5_6` (5.6, page 98): gluing realizable expansions of partial `Ω`-patchworks across
  separations `(A₁, B₁)` and `(A₂, B₂)`.
- `theorem_5_7` (5.7, pages 99–100): simulation between partial `Ω`-patchworks `P₁, P₂` from a
  realizable expansion between the hearts `Q₁, Q₂` of places `(P₁, ℒ₁), (P₂, ℒ₂)` that maps new
  edges to new edges and simulates the corresponding restrictions `P₁ | A₁` in `P₂ | A₂`.
-/

public section

namespace GraphMinor.GM18

open SimpleGraph Hypergraph

universe u v w

variable {α β Ω : Type*}

/-! ## Theorem (5.6): Gluing realizable expansions of partial patchworks -/

/-- **Graph Minors XVIII, (5.6)** (page 98):
"**5.6.** *Let $P_1, P_2$ be partial $\Omega$-patchworks, and let $(A_1, B_1)$, $(A_2, B_2)$ be
separations of $\|P_1\|, \|P_2\|$ respectively. Let $\eta'$ be a realizable expansion of $P_1|A_1$
in $P_2|A_2$ (whence $|\bar{\pi}(A_1)| = |\bar{\pi}(A_2)| = k$, say) and let $\eta''$ be a
realizable expansion of $P_1|B_1$ in $P_2|B_2$ such that for $1 \le i \le k$, $\eta''(v)$ contains
the $i$th term of $\pi(A_2)$, where $v$ is the $i$th term of $\pi(A_1)$. Define $\eta$ by:*
$$
\eta(v) = \begin{cases}
\eta'(v), & v \in V(A_1) \setminus V(B_1), \\
\eta''(v), & v \in V(B_1) \setminus V(A_1), \\
\eta'(v) \cup \eta''(v), & v \in V(A_1 \cap B_1),
\end{cases}
$$
$$
\eta(e) = \begin{cases}
\eta'(e), & e \in E(A_1), \\
\eta''(e), & e \in E(B_1).
\end{cases}
$$
*Then $\eta$ is a realizable expansion of $P_1$ in $P_2$.*"

In our representation `PartialPatchwork Ω α β = GM04.Patchwork (WithBot Ω) α β`, the adjoined
minimum element `* = ⊥` of the paper's proof is already built into `WithBot Ω`, so (5.6) follows
directly from `GM04.theorem_8_1_proof`. -/
theorem theorem_5_6_proof [Preorder Ω] {α₁ β₁ α₂ β₂ : Type*}
    {P₁ : PartialPatchwork Ω α₁ β₁} {P₂ : PartialPatchwork Ω α₂ β₂}
    {A₁ B₁ : RootedHypergraph α₁ β₁} {A₂ B₂ : RootedHypergraph α₂ β₂}
    (hsep₁ : P₁.G.IsSeparation A₁ B₁) (hsep₂ : P₂.G.IsSeparation A₂ B₂)
    {η'v η''v : α₁ → Set α₂} {η'e η''e : β₁ → β₂}
    (hη' : GM04.IsRealizableExpansion (P₁.restrict A₁) (P₂.restrict A₂) η'v η'e)
    (hη'' : GM04.IsRealizableExpansion (P₁.restrict B₁) (P₂.restrict B₂) η''v η''e)
    (hroots_mem : ∀ (i : ℕ) (hi₁ : i < A₁.roots.length) (hi₂ : i < A₂.roots.length),
      A₂.roots[i] ∈ η''v A₁.roots[i]) :
    GM04.IsRealizableExpansion P₁ P₂
      (GM04.glueVertex A₁ B₁ η'v η''v) (GM04.glueEdge A₁ η'e η''e) :=
  GM04.theorem_8_1_proof hsep₁ hsep₂ hη' hη'' hroots_mem

/-! ## Helper lemmas for the proof of (5.7) -/

private theorem getElem_congr_list {l₁ l₂ : List α} (h : l₁ = l₂) (i : ℕ) (hi₁ : i < l₁.length) :
    l₁[i] = l₂[i]'(h ▸ hi₁) := by
  subst h; rfl

private theorem realizationOf_congr {G₁ G₂ : Hypergraph α β}
    (hV : G₁.vertexSet = G₂.vertexSet) (hE : G₁.edgeSet = G₂.edgeSet)
    (δ : β → (⊤ : SimpleGraph α).Subgraph) :
    GM04.realizationOf G₁ δ = GM04.realizationOf G₂ δ := by
  ext u v
  · simp [GM04.realizationOf, hV, hE]
  · simp [GM04.realizationOf, hE]

/-- A bijection `π : β₁ → β₂` between the edge sets of two patchworks `P₁, P₂` on the same vertex
type `α` that preserves vertices, roots, incidences, `dom`, `μ`, `Δ`, and satisfies
`P₁.φ e ≤ P₂.φ (π e)` induces a realizable expansion `(fun v ↦ {v}, π)` of `P₁` in `P₂`. -/
theorem isRealizableExpansion_of_edge_bij [Preorder Ω] {β₁ β₂ : Type*}
    (P₁ : GM04.Patchwork Ω α β₁) (P₂ : GM04.Patchwork Ω α β₂)
    (π : β₁ → β₂)
    (hV : P₁.G.vertexSet = P₂.G.vertexSet)
    (hroots : P₁.G.roots = P₂.G.roots)
    (hE : π '' P₁.G.edgeSet = P₂.G.edgeSet)
    (hinj : Set.InjOn π P₁.G.edgeSet)
    (hends : ∀ e ∈ P₁.G.edgeSet, P₁.G.ends e = P₂.G.ends (π e))
    (hdom : ∀ e ∈ P₁.G.edgeSet, e ∈ P₁.dom ↔ π e ∈ P₂.dom)
    (hμ : ∀ e ∈ P₁.dom, P₁.μ e = P₂.μ (π e))
    (hΔ : ∀ e ∈ P₁.dom, P₁.Δ e = P₂.Δ (π e))
    (hφ : ∀ e ∈ P₁.G.edgeSet, P₁.φ e ≤ P₂.φ (π e)) :
    GM04.IsRealizableExpansion P₁ P₂ (fun v ↦ {v}) π := by
  have hexp : GM04.IsExpansion P₁ P₂ (fun v ↦ {v}) π :=
    { vertex_nonempty := fun v _ ↦ Set.singleton_nonempty v
      vertex_subset := fun _ hv _ h ↦ h.symm ▸ (hV ▸ hv)
      edge_mem := fun e he ↦ hE ▸ ⟨e, he, rfl⟩
      vertex_disjoint := fun _ _ _ _ hne ↦ Set.disjoint_singleton.2 hne
      edge_injOn := hinj
      mem_dom_iff := hdom
      ends_nonempty := fun e he _ v hinc ↦
        ⟨v, rfl, (hends e he ▸ hinc : v ∈ P₂.G.ends (π e))⟩
      μ_length := fun e hd ↦ congrArg List.length (hμ e hd)
      μ_mem := fun e hd i hi _ ↦ by
        rw [← getElem_congr_list (hμ e hd) i hi]
        rfl
      roots_length := congrArg List.length hroots
      roots_mem := fun i hi _ ↦ by
        rw [← getElem_congr_list hroots i hi]
        rfl
      maps_Δ := fun e hd δ hδ ↦ by
        have he : e ∈ P₁.G.edgeSet := P₁.dom_subset hd
        have hverts : δ.verts ⊆ {x | x ∈ P₁.μ e} := by
          rw [((P₁.Δ e).verts_eq δ hδ).trans (P₁.Δ_verts e he), P₁.μ_set e hd]
        change GM04.marchMapSubgraph (P₁.μ e) (P₂.μ (π e)) δ ∈ (P₂.Δ (π e)).groupings
        rw [← hμ e hd, ← hΔ e hd, GM04.marchMapSubgraph_id hverts]
        exact hδ
      φ_le := hφ }
  obtain ⟨H, ⟨δ, hδ, hH⟩, hcomp⟩ := (GM04.IsRealizableExpansion.id P₂).2
  have himg : π '' P₁.G.edgeSet = id '' P₂.G.edgeSet := hE.trans (Set.image_id P₂.G.edgeSet).symm
  refine ⟨hexp, H, ⟨⟨δ, ?_, ?_⟩, fun v hv ↦ hcomp v (hV ▸ hv)⟩⟩
  · rw [himg]; exact hδ
  · rw [himg]; exact hH

/-- A subset of a rooted location in `G` is again a rooted location in `G`. -/
theorem IsRootedLocation.mono {G : RootedHypergraph α β}
    {ℒ ℒ' : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ) (hsub : ℒ' ⊆ ℒ) :
    IsRootedLocation G ℒ' where
  isComplemented _ hA := hℒ.isComplemented (hsub hA)
  le_complement _ h₁ _ h₂ hne := hℒ.le_complement (hsub h₁) (hsub h₂) hne

/-- The core of an empty rooted location in `G` is `G.toHypergraph`. -/
theorem rootedLocationCore_empty (G : RootedHypergraph α β) :
    rootedLocationCore G ∅ = G.toHypergraph := by
  have hℒ : IsRootedLocation G ∅ :=
    ⟨fun _ h ↦ h.elim, fun _ h ↦ h.elim⟩
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (locationCore_le hℒ.isLocation) le_rfl ?_ ?_
  · ext v
    rw [mem_rootedLocationCore_vertexSet_iff hℒ]
    exact ⟨fun h ↦ h.1, fun hv ↦ ⟨hv, fun _ h ↦ h.elim⟩⟩
  · ext e
    rw [mem_rootedLocationCore_edgeSet_iff]
    exact ⟨fun h ↦ h.1, fun he ↦ ⟨he, fun _ h ↦ h.elim⟩⟩

/-- A heart of `(P, ∅)` is equivalent to `P`. -/
theorem IsPlaceHeart.equiv_of_empty {P Q : PartialPatchwork Ω α β}
    {newEdge : RootedHypergraph α β → β}
    (hQ : IsPlaceHeart P ∅ newEdge Q) :
    PatchworkEquiv Q P where
  G_eq := by
    refine RootedHypergraph.ext ?_ hQ.roots_eq
    have hcore := rootedLocationCore_empty P.G
    refine hypergraph_ext_of_ends_eq ?_ ?_ ?_
    · rw [hQ.vertexSet_eq, hcore]
    · rw [hQ.edgeSet_eq, hcore, Set.image_empty, Set.union_empty]
    · intro e he
      rw [hQ.edgeSet_eq, Set.image_empty, Set.union_empty] at he
      exact hQ.ends_core he
  dom_eq := by
    rw [hQ.dom_eq, rootedLocationCore_empty, Set.image_empty, Set.union_empty]
    exact Set.inter_eq_self_of_subset_right P.dom_subset
  μ_eq e he := by
    rw [hQ.dom_eq, Set.image_empty, Set.union_empty] at he
    exact hQ.μ_core he
  Δ_eq e he := by
    rw [hQ.edgeSet_eq, Set.image_empty, Set.union_empty] at he
    exact hQ.Δ_core he
  φ_eq e he := by
    rw [hQ.edgeSet_eq, Set.image_empty, Set.union_empty] at he
    exact hQ.φ_core he

/-- Given a rooted location `ℒ` in `P.G`, a member `A₀ ∈ ℒ`, and a heart `Q'` of `(P, ℒ \ {A₀})`
using `newEdge`, `A₀` is a complemented rooted subhypergraph of `Q'.G`. -/
theorem isComplemented_heart_diff {P Q' : PartialPatchwork Ω α β}
    {ℒ : Set (RootedHypergraph α β)} {A₀ : RootedHypergraph α β}
    {newEdge : RootedHypergraph α β → β}
    (hℒ : IsRootedLocation P.G ℒ) (hA₀ : A₀ ∈ ℒ)
    (hQ' : IsPlaceHeart P (ℒ \ {A₀}) newEdge Q') :
    IsComplemented Q'.G A₀ := by
  have hℒ' := hQ'.isRootedLocation
  have hA₀_comp := hℒ.isComplemented hA₀
  have hA₀_core_V : A₀.vertexSet ⊆ (rootedLocationCore P.G (ℒ \ {A₀})).vertexSet := by
    intro v hv
    rw [mem_rootedLocationCore_vertexSet_iff hℒ']
    refine ⟨hA₀_comp.le.vertexSet_subset hv, fun A hA hvA ↦ ?_⟩
    have hne : A₀ ≠ A := fun hEq ↦ hA.2 (Set.mem_singleton_iff.2 hEq.symm)
    have hle := hℒ.le_complement hA₀ hA.1 hne
    exact (hle.vertexSet_subset hv).resolve_left fun h ↦ h.2 hvA
  have hA₀_core_E : A₀.edgeSet ⊆ (rootedLocationCore P.G (ℒ \ {A₀})).edgeSet := by
    intro e he
    rw [mem_rootedLocationCore_edgeSet_iff]
    refine ⟨hA₀_comp.le.edgeSet_subset he, fun A hA ↦ ?_⟩
    have hne : A₀ ≠ A := fun hEq ↦ hA.2 (Set.mem_singleton_iff.2 hEq.symm)
    exact ((hℒ.le_complement hA₀ hA.1 hne).edgeSet_subset he).2
  have hle : A₀.toHypergraph ≤ Q'.G.toHypergraph :=
    { vertexSet_subset := by
        rw [hQ'.vertexSet_eq]
        exact hA₀_core_V
      edgeSet_subset := by
        rw [hQ'.edgeSet_eq]
        exact fun e he ↦ Or.inl (hA₀_core_E he)
      ends_eq := fun e he ↦ by
        rw [hQ'.ends_core (hA₀_core_E he)]
        exact hA₀_comp.le.ends_eq e he }
  refine ⟨hle, ?_, ?_⟩
  · intro v hvA₀ hv_root
    change v ∈ Q'.G.roots at hv_root
    rw [hQ'.roots_eq] at hv_root
    exact hA₀_comp.roots_mem hvA₀ hv_root
  · intro v e hvA₀ he_diff hinc
    have he_Q' := he_diff.1
    rw [hQ'.edgeSet_eq] at he_Q'
    rcases he_Q' with he_core | ⟨A, hA, rfl⟩
    · have heG : e ∈ P.G.edgeSet := (mem_rootedLocationCore_edgeSet_iff.1 he_core).1
      have hincG : P.G.Inc e v := by
        change v ∈ P.G.ends e
        rw [← hQ'.ends_core he_core]
        exact hinc
      exact hA₀_comp.inc_diff_mem hvA₀ ⟨heG, he_diff.2⟩ hincG
    · have hvA : v ∈ A.rootSet := by
        rw [← hQ'.ends_newEdge hA]
        exact hinc
      have hvA_V : v ∈ A.vertexSet := A.roots_subset v hvA
      have hne : A ≠ A₀ := fun hEq ↦ hA.2 (Set.mem_singleton_iff.2 hEq)
      have hle_comp := hℒ.le_complement hA.1 hA₀ hne
      exact (hle_comp.vertexSet_subset hvA_V).resolve_left fun h ↦ h.2 hvA₀

/-- In the setup of `isComplemented_heart_diff`, `Q'.restrict A₀` is equivalent to `P.restrict A₀`.
-/
theorem restrict_left_equiv_of_heart_diff {P Q' : PartialPatchwork Ω α β}
    {ℒ : Set (RootedHypergraph α β)} {A₀ : RootedHypergraph α β}
    {newEdge : RootedHypergraph α β → β}
    (hℒ : IsRootedLocation P.G ℒ) (hA₀ : A₀ ∈ ℒ)
    (hfresh : ∀ ⦃A⦄, A ∈ ℒ → newEdge A ∉ P.G.edgeSet)
    (hQ' : IsPlaceHeart P (ℒ \ {A₀}) newEdge Q') :
    PatchworkEquiv (Q'.restrict A₀) (P.restrict A₀) := by
  have hcomp := isComplemented_heart_diff hℒ hA₀ hQ'
  have hle_Q' : A₀.toHypergraph ≤ Q'.G.toHypergraph := hcomp.le
  have hle_P : A₀.toHypergraph ≤ P.G.toHypergraph := (hℒ.isComplemented hA₀).le
  have hA₀_core_E : A₀.edgeSet ⊆ (rootedLocationCore P.G (ℒ \ {A₀})).edgeSet := by
    intro e he
    rw [mem_rootedLocationCore_edgeSet_iff]
    refine ⟨hle_P.edgeSet_subset he, fun A hA ↦ ?_⟩
    have hne : A₀ ≠ A := fun hEq ↦ hA.2 (Set.mem_singleton_iff.2 hEq.symm)
    exact ((hℒ.le_complement hA₀ hA.1 hne).edgeSet_subset he).2
  refine
    { G_eq := rfl
      dom_eq := by
        rw [Q'.restrict_dom hle_Q', P.restrict_dom hle_P, hQ'.dom_eq]
        ext e
        simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_image]
        refine ⟨?_, fun ⟨hd, heA₀⟩ ↦ ⟨Or.inl ⟨hA₀_core_E heA₀, hd⟩, heA₀⟩⟩
        rintro ⟨⟨_, hd⟩ | ⟨A, hA, rfl⟩, heA₀⟩
        · exact ⟨hd, heA₀⟩
        · exact (hfresh hA.1 (hle_P.edgeSet_subset heA₀)).elim
      μ_eq := fun e he ↦ by
        rw [Q'.restrict_dom hle_Q'] at he
        exact hQ'.μ_core ⟨hA₀_core_E he.2, by
          rw [hQ'.dom_eq] at he
          rcases he.1 with ⟨_, hd⟩ | ⟨A, hA, rfl⟩
          · exact hd
          · exact (hfresh hA.1 (hle_P.edgeSet_subset he.2)).elim⟩
      Δ_eq := fun e he ↦ by
        rw [Q'.restrict_Δ hle_Q' he, P.restrict_Δ hle_P he, hQ'.Δ_core (hA₀_core_E he)]
      φ_eq := fun e he ↦ hQ'.φ_core (hA₀_core_E he) }

/-- In the setup of `isComplemented_heart_diff`, let `B₀ = complement Q'.G A₀ hcomp`. Then
`B₀.vertexSet = Q.G.vertexSet`, `B₀.edgeSet = Q.G.edgeSet \ {newEdge A₀}`, `B₀.roots = Q.G.roots`,
`B₀.toHypergraph ≤ Q.G.toHypergraph`, and `PatchworkEquiv (Q.restrict B₀) (Q'.restrict B₀)`
(claim `Q_i \ e_i(A_i) = Q_i' | B_i` on page 99). -/
theorem complement_heart_diff_props {P Q Q' : PartialPatchwork Ω α β}
    {ℒ : Set (RootedHypergraph α β)} {A₀ : RootedHypergraph α β}
    {newEdge : RootedHypergraph α β → β}
    (hQ : IsPlaceHeart P ℒ newEdge Q) (hA₀ : A₀ ∈ ℒ)
    (hfresh : ∀ ⦃A⦄, A ∈ ℒ → newEdge A ∉ P.G.edgeSet)
    (hQ' : IsPlaceHeart P (ℒ \ {A₀}) newEdge Q') :
    let B₀ := complement Q'.G A₀ (isComplemented_heart_diff hQ.isRootedLocation hA₀ hQ')
    B₀.vertexSet = Q.G.vertexSet ∧
    B₀.edgeSet = Q.G.edgeSet \ {newEdge A₀} ∧
    B₀.roots = Q.G.roots ∧
    B₀.toHypergraph ≤ Q.G.toHypergraph ∧
    PatchworkEquiv (Q.restrict B₀) (Q'.restrict B₀) := by
  intro B₀
  have hℒ := hQ.isRootedLocation
  have hℒ' := hQ'.isRootedLocation
  have hcomp := isComplemented_heart_diff hℒ hA₀ hQ'
  have hle_B₀_Q' : B₀.toHypergraph ≤ Q'.G.toHypergraph :=
    hcomp.isSeparation.isSeparation.right_le
  have hV_eq : B₀.vertexSet = Q.G.vertexSet := by
    rw [hQ.vertexSet_eq]
    change (Q'.G.vertexSet \ A₀.vertexSet) ∪ A₀.rootSet =
      (rootedLocationCore P.G ℒ).vertexSet
    rw [hQ'.vertexSet_eq]
    ext v
    simp only [Set.mem_union, Set.mem_sdiff]
    rw [mem_rootedLocationCore_vertexSet_iff hℒ', mem_rootedLocationCore_vertexSet_iff hℒ]
    constructor
    · rintro (⟨⟨hvG, hall'⟩, hnotA₀⟩ | hv_root₀)
      · refine ⟨hvG, fun A hA hvA ↦ ?_⟩
        by_cases hEq : A = A₀
        · subst hEq; exact (hnotA₀ hvA).elim
        · exact hall' A ⟨hA, hEq⟩ hvA
      · have hvA₀ : v ∈ A₀.vertexSet := A₀.roots_subset v hv_root₀
        have hvG : v ∈ P.G.vertexSet := (hℒ.isComplemented hA₀).le.vertexSet_subset hvA₀
        refine ⟨hvG, fun A hA hvA ↦ ?_⟩
        by_cases hEq : A = A₀
        · subst hEq; exact hv_root₀
        · have hle := hℒ.le_complement hA₀ hA (Ne.symm hEq)
          exact (hle.vertexSet_subset hvA₀).resolve_left fun h ↦ h.2 hvA
    · rintro ⟨hvG, hall⟩
      by_cases hvA₀ : v ∈ A₀.vertexSet
      · exact Or.inr (hall A₀ hA₀ hvA₀)
      · exact Or.inl ⟨⟨hvG, fun A hA ↦ hall A hA.1⟩, hvA₀⟩
  have hE_eq : B₀.edgeSet = Q.G.edgeSet \ {newEdge A₀} := by
    change Q'.G.edgeSet \ A₀.edgeSet = Q.G.edgeSet \ {newEdge A₀}
    rw [hQ'.edgeSet_eq, hQ.edgeSet_eq]
    ext e
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
    rw [mem_rootedLocationCore_edgeSet_iff, mem_rootedLocationCore_edgeSet_iff]
    constructor
    · rintro ⟨⟨heG, hall'⟩ | ⟨A, ⟨hA, hneA⟩, rfl⟩, hnotA₀⟩
      · refine ⟨Or.inl ⟨heG, fun A hA ↦ ?_⟩, fun hEq ↦ hfresh hA₀ (hEq ▸ heG)⟩
        by_cases hEq : A = A₀
        · subst hEq; exact hnotA₀
        · exact hall' A ⟨hA, hEq⟩
      · exact ⟨Or.inr ⟨A, hA, rfl⟩, fun hEq ↦ hneA (hQ.injOn_newEdge hA hA₀ hEq)⟩
    · rintro ⟨⟨heG, hall⟩ | ⟨A, hA, rfl⟩, hne_e₀⟩
      · exact ⟨Or.inl ⟨heG, fun A hA' ↦ hall A hA'.1⟩, hall A₀ hA₀⟩
      · have hneA : A ≠ A₀ := fun hEq ↦ hne_e₀ (congrArg newEdge hEq)
        exact ⟨Or.inr ⟨A, ⟨hA, hneA⟩, rfl⟩,
          fun heA₀ ↦ hfresh hA ((hℒ.isComplemented hA₀).le.edgeSet_subset heA₀)⟩
  have hroots_eq : B₀.roots = Q.G.roots :=
    hQ'.roots_eq.trans hQ.roots_eq.symm
  have hcore_sub : (rootedLocationCore P.G ℒ).edgeSet ⊆
      (rootedLocationCore P.G (ℒ \ {A₀})).edgeSet := by
    intro e he
    rw [mem_rootedLocationCore_edgeSet_iff] at he ⊢
    exact ⟨he.1, fun A hA ↦ he.2 A hA.1⟩
  have hle_B₀_Q : B₀.toHypergraph ≤ Q.G.toHypergraph :=
    { vertexSet_subset := hV_eq.le
      edgeSet_subset := hE_eq.le.trans Set.sdiff_subset
      ends_eq := fun e he ↦ by
        rw [← hle_B₀_Q'.ends_eq e he]
        have he_Q : e ∈ Q.G.edgeSet ∧ e ≠ newEdge A₀ := by simpa [hE_eq] using he
        rcases (hQ.edgeSet_eq ▸ he_Q.1) with he_core | ⟨A, hA, rfl⟩
        · rw [hQ.ends_core he_core, hQ'.ends_core (hcore_sub he_core)]
        · have hneA : A ≠ A₀ := fun hEq ↦ he_Q.2 (congrArg newEdge hEq)
          rw [hQ.ends_newEdge hA, hQ'.ends_newEdge ⟨hA, hneA⟩] }
  refine ⟨hV_eq, hE_eq, hroots_eq, hle_B₀_Q, ?_⟩
  refine
    { G_eq := rfl
      dom_eq := by
        rw [Q.restrict_dom hle_B₀_Q, Q'.restrict_dom hle_B₀_Q', hQ.dom_eq, hQ'.dom_eq]
        ext e
        simp only [Set.mem_inter_iff]
        refine and_congr_left fun heB₀ ↦ ?_
        have he_Q : e ∈ Q.G.edgeSet ∧ e ≠ newEdge A₀ := by simpa [hE_eq] using heB₀
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_image, Set.mem_sdiff,
          Set.mem_singleton_iff]
        constructor
        · rintro (⟨he_core, hd⟩ | ⟨A, hA, rfl⟩)
          · exact Or.inl ⟨hcore_sub he_core, hd⟩
          · have hneA : A ≠ A₀ := fun hEq ↦ he_Q.2 (congrArg newEdge hEq)
            exact Or.inr ⟨A, ⟨hA, hneA⟩, rfl⟩
        · rintro (⟨_, hd⟩ | ⟨A, ⟨hA, _⟩, rfl⟩)
          · rcases (hQ.edgeSet_eq ▸ he_Q.1) with he_core | ⟨A, hA, rfl⟩
            · exact Or.inl ⟨he_core, hd⟩
            · exact Or.inr ⟨A, hA, rfl⟩
          · exact Or.inr ⟨A, hA, rfl⟩
      μ_eq := fun e he ↦ by
        rw [Q.restrict_dom hle_B₀_Q] at he
        have he_Q : e ∈ Q.G.edgeSet ∧ e ≠ newEdge A₀ := by simpa [hE_eq] using he.2
        have hdom := he.1
        rw [hQ.dom_eq] at hdom
        change Q.μ e = Q'.μ e
        rcases hdom with ⟨he_core, hd⟩ | ⟨A, hA, rfl⟩
        · rw [hQ.μ_core ⟨he_core, hd⟩, hQ'.μ_core ⟨hcore_sub he_core, hd⟩]
        · have hneA : A ≠ A₀ := fun hEq ↦ he_Q.2 (congrArg newEdge hEq)
          rw [hQ.μ_newEdge hA, hQ'.μ_newEdge ⟨hA, hneA⟩]
      Δ_eq := fun e heB₀ ↦ by
        rw [Q.restrict_Δ hle_B₀_Q heB₀, Q'.restrict_Δ hle_B₀_Q' heB₀]
        have he_Q : e ∈ Q.G.edgeSet ∧ e ≠ newEdge A₀ := by simpa [hE_eq] using heB₀
        rcases (hQ.edgeSet_eq ▸ he_Q.1) with he_core | ⟨A, hA, rfl⟩
        · rw [hQ.Δ_core he_core, hQ'.Δ_core (hcore_sub he_core)]
        · have hneA : A ≠ A₀ := fun hEq ↦ he_Q.2 (congrArg newEdge hEq)
          rw [hQ.Δ_newEdge hA, hQ'.Δ_newEdge ⟨hA, hneA⟩]
      φ_eq := fun e heB₀ ↦ by
        have he_Q : e ∈ Q.G.edgeSet ∧ e ≠ newEdge A₀ := by simpa [hE_eq] using heB₀
        change Q.φ e = Q'.φ e
        rcases (hQ.edgeSet_eq ▸ he_Q.1) with he_core | ⟨A, hA, rfl⟩
        · rw [hQ.φ_core he_core, hQ'.φ_core (hcore_sub he_core)]
        · have hneA : A ≠ A₀ := fun hEq ↦ he_Q.2 (congrArg newEdge hEq)
          rw [hQ.φ_newEdge hA, hQ'.φ_newEdge ⟨hA, hneA⟩] }

open Classical in
/-- Rooted hypergraph with a single edge `e₀` and vertex set and ends equal to `{v | v ∈ r}`
(used in Case 1 of (5.7), page 99). -/
@[expose] noncomputable def singleEdgeRootedHypergraph (e₀ : β) (r : List α) (hr : r.Nodup) :
    RootedHypergraph α β where
  toHypergraph :=
    { vertexSet := {v | v ∈ r}
      edgeSet := {e₀}
      Inc e v := e = e₀ ∧ v ∈ r
      vertex_mem_of_inc _ _ h := h.2
      edge_mem_of_inc _ _ h := h.1
      vertexSet_finite := r.toFinset.finite_toSet.subset fun _ h ↦ List.mem_toFinset.2 h
      edgeSet_finite := Set.finite_singleton e₀ }
  roots := r
  roots_nodup := hr
  roots_subset _ hv := hv

/-- In Case 1 of (5.7), `(K, B₂)` is a separation of `Q₂.G`, where
`K = singleEdgeRootedHypergraph (newEdge₂ A₂) A₂.roots A₂.roots_nodup` and
`B₂ = complement Q₂'.G A₂ ...`. -/
theorem isSeparation_singleEdge_complement_of_heart_diff {P₂ Q₂ Q₂' : PartialPatchwork Ω α β}
    {ℒ₂ : Set (RootedHypergraph α β)} {A₂ : RootedHypergraph α β}
    {newEdge₂ : RootedHypergraph α β → β}
    (hQ₂ : IsPlaceHeart P₂ ℒ₂ newEdge₂ Q₂) (hA₂ : A₂ ∈ ℒ₂)
    (hfresh₂ : ∀ ⦃A⦄, A ∈ ℒ₂ → newEdge₂ A ∉ P₂.G.edgeSet)
    (hQ₂' : IsPlaceHeart P₂ (ℒ₂ \ {A₂}) newEdge₂ Q₂') :
    Q₂.G.IsSeparation
      (singleEdgeRootedHypergraph (newEdge₂ A₂) A₂.roots A₂.roots_nodup)
      (complement Q₂'.G A₂ (isComplemented_heart_diff hQ₂.isRootedLocation hA₂ hQ₂')) := by
  let K := singleEdgeRootedHypergraph (newEdge₂ A₂) A₂.roots A₂.roots_nodup
  let B₂ := complement Q₂'.G A₂ (isComplemented_heart_diff hQ₂.isRootedLocation hA₂ hQ₂')
  obtain ⟨hV_eq, hE_eq, hroots_eq, hle_B₂, _⟩ :=
    complement_heart_diff_props hQ₂ hA₂ hfresh₂ hQ₂'
  have he₂_mem : newEdge₂ A₂ ∈ Q₂.G.edgeSet := by
    rw [hQ₂.edgeSet_eq]
    exact Or.inr ⟨A₂, hA₂, rfl⟩
  have hends_e₂ : Q₂.G.ends (newEdge₂ A₂) = A₂.rootSet := hQ₂.ends_newEdge hA₂
  have hroot_sub : A₂.rootSet ⊆ Q₂.G.vertexSet := by
    rw [hQ₂.vertexSet_eq]
    exact mem_rootSet_subset_rootedLocationCore hQ₂.isRootedLocation hA₂
  have hle_K : K.toHypergraph ≤ Q₂.G.toHypergraph :=
    { vertexSet_subset := hroot_sub
      edgeSet_subset := Set.singleton_subset_iff.2 he₂_mem
      ends_eq := fun e he ↦ by
        have he_eq : e = newEdge₂ A₂ := Set.mem_singleton_iff.1 he
        subst he_eq
        rw [hends_e₂]
        ext v
        exact ⟨fun hv ↦ ⟨rfl, hv⟩, fun h ↦ h.2⟩ }
  refine
    { isSeparation :=
        { left_le := hle_K
          right_le := hle_B₂
          union_eq := by
            refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
              (GM10.union_le hle_K hle_B₂) le_rfl ?_ ?_
            · change A₂.rootSet ∪ B₂.vertexSet = Q₂.G.vertexSet
              rw [hV_eq]
              exact Set.union_eq_self_of_subset_left hroot_sub
            · change ({newEdge₂ A₂} : Set β) ∪ B₂.edgeSet = Q₂.G.edgeSet
              rw [hE_eq]
              exact Set.union_sdiff_cancel (Set.singleton_subset_iff.2 he₂_mem)
          edgeSet_inter_eq := by
            change ({newEdge₂ A₂} : Set β) ∩ B₂.edgeSet = ∅
            rw [hE_eq]
            ext e
            simp }
      roots_right := hroots_eq
      rootSet_left := by
        change A₂.rootSet = A₂.rootSet ∩ B₂.vertexSet
        rw [hV_eq]
        exact (Set.inter_eq_self_of_subset_left hroot_sub).symm }

/-- In Case 2 of (5.7), if `(ηv, ηe)` is a realizable expansion of `Q₁` in `Q₂` with
`ηe (newEdge₁ A₁) = newEdge₂ A₂`, then `(ηv, ηe)` is also a realizable expansion of
`Q₁.restrict B₁` in `Q₂.restrict B₂`. -/
theorem isRealizableExpansion_restrict_complement_of_heart_diff [Preorder Ω]
    {α₁ β₁ α₂ β₂ : Type*}
    {P₁ Q₁ Q₁' : PartialPatchwork Ω α₁ β₁}
    {P₂ Q₂ Q₂' : PartialPatchwork Ω α₂ β₂}
    {ℒ₁ : Set (RootedHypergraph α₁ β₁)} {ℒ₂ : Set (RootedHypergraph α₂ β₂)}
    {A₁ : RootedHypergraph α₁ β₁} {A₂ : RootedHypergraph α₂ β₂}
    {newEdge₁ : RootedHypergraph α₁ β₁ → β₁} {newEdge₂ : RootedHypergraph α₂ β₂ → β₂}
    (hQ₁ : IsPlaceHeart P₁ ℒ₁ newEdge₁ Q₁) (hA₁ : A₁ ∈ ℒ₁)
    (hfresh₁ : ∀ ⦃A⦄, A ∈ ℒ₁ → newEdge₁ A ∉ P₁.G.edgeSet)
    (hQ₁' : IsPlaceHeart P₁ (ℒ₁ \ {A₁}) newEdge₁ Q₁')
    (hQ₂ : IsPlaceHeart P₂ ℒ₂ newEdge₂ Q₂) (hA₂ : A₂ ∈ ℒ₂)
    (hfresh₂ : ∀ ⦃A⦄, A ∈ ℒ₂ → newEdge₂ A ∉ P₂.G.edgeSet)
    (hQ₂' : IsPlaceHeart P₂ (ℒ₂ \ {A₂}) newEdge₂ Q₂')
    {ηv : α₁ → Set α₂} {ηe : β₁ → β₂}
    (hη : GM04.IsRealizableExpansion Q₁ Q₂ ηv ηe)
    (he_map : ηe (newEdge₁ A₁) = newEdge₂ A₂) :
    let B₁ := complement Q₁'.G A₁ (isComplemented_heart_diff hQ₁.isRootedLocation hA₁ hQ₁')
    let B₂ := complement Q₂'.G A₂ (isComplemented_heart_diff hQ₂.isRootedLocation hA₂ hQ₂')
    GM04.IsRealizableExpansion (Q₁.restrict B₁) (Q₂.restrict B₂) ηv ηe := by
  intro B₁ B₂
  obtain ⟨hV₁, hE₁, hroots₁, hle₁, _⟩ := complement_heart_diff_props hQ₁ hA₁ hfresh₁ hQ₁'
  obtain ⟨hV₂, hE₂, hroots₂, hle₂, _⟩ := complement_heart_diff_props hQ₂ hA₂ hfresh₂ hQ₂'
  obtain ⟨hexp, H, ⟨⟨δ, hδ, hH⟩, hcomp⟩⟩ := hη
  have he₁_mem : newEdge₁ A₁ ∈ Q₁.G.edgeSet := by
    rw [hQ₁.edgeSet_eq]; exact Or.inr ⟨A₁, hA₁, rfl⟩
  have hmap_B₁ : ∀ e ∈ B₁.edgeSet, ηe e ∈ B₂.edgeSet := by
    intro e he
    rw [hE₁] at he
    rw [hE₂]
    refine ⟨hexp.edge_mem e he.1, fun hEq ↦ he.2 ?_⟩
    exact hexp.edge_injOn he.1 he₁_mem (hEq.trans he_map.symm)
  have hexp_B : GM04.IsExpansion (Q₁.restrict B₁) (Q₂.restrict B₂) ηv ηe :=
    { vertex_nonempty := fun v hv ↦ hexp.vertex_nonempty v (hV₁ ▸ hv)
      vertex_subset := fun v hv ↦ hV₂.symm ▸ hexp.vertex_subset v (hV₁ ▸ hv)
      edge_mem := hmap_B₁
      vertex_disjoint := fun v₁ hv₁ v₂ hv₂ hne ↦
        hexp.vertex_disjoint v₁ (hV₁ ▸ hv₁) v₂ (hV₁ ▸ hv₂) hne
      edge_injOn := hexp.edge_injOn.mono hle₁.edgeSet_subset
      mem_dom_iff := fun e he ↦ by
        rw [Q₁.restrict_dom hle₁, Q₂.restrict_dom hle₂]
        have heQ₁ : e ∈ Q₁.G.edgeSet := hle₁.edgeSet_subset he
        have heB₂ : ηe e ∈ B₂.edgeSet := hmap_B₁ e he
        exact ⟨fun h ↦ ⟨(hexp.mem_dom_iff e heQ₁).1 h.1, heB₂⟩,
          fun h ↦ ⟨(hexp.mem_dom_iff e heQ₁).2 h.1, he⟩⟩
      ends_nonempty := fun e he hnd v hinc ↦ by
        have heQ₁ : e ∈ Q₁.G.edgeSet := hle₁.edgeSet_subset he
        have hndQ₁ : e ∉ Q₁.dom := fun hd ↦ hnd ((Q₁.restrict_dom hle₁).symm ▸ ⟨hd, he⟩)
        have hincQ₁ : Q₁.G.Inc e v := GM10.inc_of_le hle₁ hinc
        obtain ⟨v', hv', hincQ₂⟩ := hexp.ends_nonempty e heQ₁ hndQ₁ v hincQ₁
        have hincB₂ : B₂.Inc (ηe e) v' := by
          change v' ∈ B₂.ends (ηe e)
          rw [← hle₂.ends_eq (ηe e) (hmap_B₁ e he)]
          exact hincQ₂
        exact ⟨v', hv', hincB₂⟩
      μ_length := fun e he ↦ by
        rw [Q₁.restrict_dom hle₁] at he
        exact hexp.μ_length e he.1
      μ_mem := fun e he i hi hi' ↦ by
        rw [Q₁.restrict_dom hle₁] at he
        exact hexp.μ_mem e he.1 i hi hi'
      roots_length := by
        change B₁.roots.length = B₂.roots.length
        rw [hroots₁, hroots₂]
        exact hexp.roots_length
      roots_mem := fun i hi hi' ↦ by
        change B₂.roots[i] ∈ ηv B₁.roots[i]
        rw [getElem_congr_list hroots₂ i hi', getElem_congr_list hroots₁ i hi]
        exact hexp.roots_mem i (hroots₁ ▸ hi) (hroots₂ ▸ hi')
      maps_Δ := fun e he ↦ by
        rw [Q₁.restrict_dom hle₁] at he
        have heB₂ : ηe e ∈ B₂.edgeSet := hmap_B₁ e he.2
        change Set.MapsTo (GM04.marchMapSubgraph (Q₁.μ e) (Q₂.μ (ηe e)))
          ((Q₁.restrict B₁).Δ e).groupings ((Q₂.restrict B₂).Δ (ηe e)).groupings
        rw [Q₁.restrict_Δ hle₁ he.2, Q₂.restrict_Δ hle₂ heB₂]
        exact hexp.maps_Δ e he.1
      φ_le := fun e he ↦ hexp.φ_le e (hle₁.edgeSet_subset he) }
  have hdel_edgeSet :
      ((Q₂.restrict B₂).deleteEdges (ηe '' B₁.edgeSet)).G.edgeSet =
        (Q₂.deleteEdges (ηe '' Q₁.G.edgeSet)).G.edgeSet := by
    change B₂.edgeSet \ (ηe '' B₁.edgeSet) = Q₂.G.edgeSet \ (ηe '' Q₁.G.edgeSet)
    rw [hE₁, hE₂]
    ext e'
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨he'Q₂, hne_e₂⟩, hnot_img⟩
      refine ⟨he'Q₂, ?_⟩
      rintro ⟨e, heQ₁, rfl⟩
      by_cases hEq : e = newEdge₁ A₁
      · subst hEq; exact hne_e₂ he_map
      · exact hnot_img ⟨e, ⟨heQ₁, hEq⟩, rfl⟩
    · rintro ⟨he'Q₂, hnot_img⟩
      refine ⟨⟨he'Q₂, ?_⟩, ?_⟩
      · rintro rfl
        exact hnot_img ⟨newEdge₁ A₁, he₁_mem, he_map⟩
      · rintro ⟨e, ⟨heQ₁, _⟩, rfl⟩
        exact hnot_img ⟨e, heQ₁, rfl⟩
  refine ⟨hexp_B, H, ⟨⟨δ, fun e' he' ↦ ?_, ?_⟩, fun v hv ↦ hcomp v (hV₁ ▸ hv)⟩⟩
  · have he'B₂ : e' ∈ B₂.edgeSet := he'.1
    have he'_del : e' ∈ (Q₂.deleteEdges (ηe '' Q₁.G.edgeSet)).G.edgeSet :=
      hdel_edgeSet ▸ he'
    change δ e' ∈ (Q₂.restrict B₂).Δ e'
    rw [Q₂.restrict_Δ hle₂ he'B₂]
    exact hδ e' he'_del
  · rw [hH]
    exact realizationOf_congr
      (G₁ := (Q₂.deleteEdges (ηe '' Q₁.G.edgeSet)).G.toHypergraph)
      (G₂ := ((Q₂.restrict B₂).deleteEdges (ηe '' B₁.edgeSet)).G.toHypergraph)
      hV₂.symm hdel_edgeSet.symm δ

private theorem roots_mem_of_placeHeart_expansion [Preorder Ω]
    {P₁ Q₁ : PartialPatchwork Ω α₁ β₁} {P₂ Q₂ : PartialPatchwork Ω α₂ β₂}
    {ℒ₁ : Set (RootedHypergraph α₁ β₁)} {ℒ₂ : Set (RootedHypergraph α₂ β₂)}
    {newEdge₁ : RootedHypergraph α₁ β₁ → β₁} {newEdge₂ : RootedHypergraph α₂ β₂ → β₂}
    (hQ₁ : IsPlaceHeart P₁ ℒ₁ newEdge₁ Q₁) (hQ₂ : IsPlaceHeart P₂ ℒ₂ newEdge₂ Q₂)
    {A₁ : RootedHypergraph α₁ β₁} {A₂ : RootedHypergraph α₂ β₂}
    (hA₁ : A₁ ∈ ℒ₁) (hA₂ : A₂ ∈ ℒ₂)
    {ηv : α₁ → Set α₂} {ηe : β₁ → β₂}
    (hη : GM04.IsRealizableExpansion Q₁ Q₂ ηv ηe)
    (he₀_eq : ηe (newEdge₁ A₁) = newEdge₂ A₂) :
    ∀ (i : ℕ) (hi₁ : i < A₁.roots.length) (hi₂ : i < A₂.roots.length),
      A₂.roots[i] ∈ ηv A₁.roots[i] := by
  intro i hi₁ hi₂
  have he₁_dom : newEdge₁ A₁ ∈ Q₁.dom := by
    rw [hQ₁.dom_eq]; exact Or.inr ⟨A₁, hA₁, rfl⟩
  have hμ₁ : Q₁.μ (newEdge₁ A₁) = A₁.roots := hQ₁.μ_newEdge hA₁
  have hμ₂ : Q₂.μ (newEdge₂ A₂) = A₂.roots := hQ₂.μ_newEdge hA₂
  have hi₁' : i < (Q₁.μ (newEdge₁ A₁)).length := hμ₁.symm ▸ hi₁
  have hi₂' : i < (Q₂.μ (ηe (newEdge₁ A₁))).length := by
    rw [he₀_eq, hμ₂]; exact hi₂
  have hmem := hη.1.μ_mem (newEdge₁ A₁) he₁_dom i hi₁' hi₂'
  simpa [he₀_eq, hμ₁, hμ₂] using hmem

private theorem simulated_of_empty_placeHeart [Preorder Ω]
    {P₁ Q₁ : PartialPatchwork Ω α₁ β₁} {P₂ Q₂ : PartialPatchwork Ω α₂ β₂}
    {ℒ₁ : Set (RootedHypergraph α₁ β₁)} {ℒ₂ : Set (RootedHypergraph α₂ β₂)}
    {newEdge₁ : RootedHypergraph α₁ β₁ → β₁} {newEdge₂ : RootedHypergraph α₂ β₂ → β₂}
    (hQ₁ : IsPlaceHeart P₁ ℒ₁ newEdge₁ Q₁) (hQ₂ : IsPlaceHeart P₂ ℒ₂ newEdge₂ Q₂)
    (hcard : ℒ₂.ncard = 0)
    {ηv : α₁ → Set α₂} {ηe : β₁ → β₂}
    (hη : GM04.IsRealizableExpansion Q₁ Q₂ ηv ηe)
    (hsim : ∀ ⦃A₁ : RootedHypergraph α₁ β₁⦄, A₁ ∈ ℒ₁ →
      ∃ A₂ ∈ ℒ₂, ηe (newEdge₁ A₁) = newEdge₂ A₂ ∧
        GM04.Simulated (P₁.restrict A₁) (P₂.restrict A₂)) :
    GM04.Simulated P₁ P₂ := by
  have hℒ₂_empty : ℒ₂ = ∅ :=
    (Set.ncard_eq_zero hQ₂.isRootedLocation.finite).1 hcard
  subst hℒ₂_empty
  have hℒ₁_empty : ℒ₁ = ∅ := by
    ext A₁
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hA₁
    obtain ⟨_, h, _⟩ := hsim hA₁
    exact h
  subst hℒ₁_empty
  exact ⟨ηv, ηe,
    PatchworkEquiv.isRealizableExpansion_congr hQ₁.equiv_of_empty hQ₂.equiv_of_empty hη⟩

/-- Version of `(5.7)` under the freshness condition `∀ A ∈ ℒ_i, newEdge_i A ∉ P_i.G.edgeSet`,
proved by induction on `|ℒ₂|` following pages 99–100. -/
theorem theorem_5_7_of_notMem_edgeSet [Preorder Ω] {α₁ β₁ α₂ β₂ : Type*}
    {P₁ Q₁ : PartialPatchwork Ω α₁ β₁} {P₂ Q₂ : PartialPatchwork Ω α₂ β₂}
    {ℒ₁ : Set (RootedHypergraph α₁ β₁)} {ℒ₂ : Set (RootedHypergraph α₂ β₂)}
    {newEdge₁ : RootedHypergraph α₁ β₁ → β₁} {newEdge₂ : RootedHypergraph α₂ β₂ → β₂}
    (hQ₁ : IsPlaceHeart P₁ ℒ₁ newEdge₁ Q₁)
    (hQ₂ : IsPlaceHeart P₂ ℒ₂ newEdge₂ Q₂)
    (hfresh₁ : ∀ ⦃A₁⦄, A₁ ∈ ℒ₁ → newEdge₁ A₁ ∉ P₁.G.edgeSet)
    (hfresh₂ : ∀ ⦃A₂⦄, A₂ ∈ ℒ₂ → newEdge₂ A₂ ∉ P₂.G.edgeSet)
    {ηv : α₁ → Set α₂} {ηe : β₁ → β₂}
    (hη : GM04.IsRealizableExpansion Q₁ Q₂ ηv ηe)
    (hpre : ∀ ⦃e : β₁⦄ ⦃A₂ : RootedHypergraph α₂ β₂⦄,
      e ∈ Q₁.G.edgeSet → A₂ ∈ ℒ₂ → ηe e = newEdge₂ A₂ → ∃ A₁ ∈ ℒ₁, e = newEdge₁ A₁)
    (hsim : ∀ ⦃A₁ : RootedHypergraph α₁ β₁⦄, A₁ ∈ ℒ₁ →
      ∃ A₂ ∈ ℒ₂, ηe (newEdge₁ A₁) = newEdge₂ A₂ ∧
        GM04.Simulated (P₁.restrict A₁) (P₂.restrict A₂)) :
    GM04.Simulated P₁ P₂ := by
  classical
  suffices hind : ∀ (n : ℕ)
      {P₁ Q₁ : PartialPatchwork Ω α₁ β₁} {P₂ Q₂ : PartialPatchwork Ω α₂ β₂}
      {ℒ₁ : Set (RootedHypergraph α₁ β₁)} {ℒ₂ : Set (RootedHypergraph α₂ β₂)}
      (hcard : ℒ₂.ncard = n)
      (hQ₁ : IsPlaceHeart P₁ ℒ₁ newEdge₁ Q₁)
      (hQ₂ : IsPlaceHeart P₂ ℒ₂ newEdge₂ Q₂)
      (hfresh₁ : ∀ ⦃A₁⦄, A₁ ∈ ℒ₁ → newEdge₁ A₁ ∉ P₁.G.edgeSet)
      (hfresh₂ : ∀ ⦃A₂⦄, A₂ ∈ ℒ₂ → newEdge₂ A₂ ∉ P₂.G.edgeSet)
      {ηv : α₁ → Set α₂} {ηe : β₁ → β₂}
      (hη : GM04.IsRealizableExpansion Q₁ Q₂ ηv ηe)
      (hpre : ∀ ⦃e : β₁⦄ ⦃A₂ : RootedHypergraph α₂ β₂⦄,
        e ∈ Q₁.G.edgeSet → A₂ ∈ ℒ₂ → ηe e = newEdge₂ A₂ → ∃ A₁ ∈ ℒ₁, e = newEdge₁ A₁)
      (hsim : ∀ ⦃A₁ : RootedHypergraph α₁ β₁⦄, A₁ ∈ ℒ₁ →
        ∃ A₂ ∈ ℒ₂, ηe (newEdge₁ A₁) = newEdge₂ A₂ ∧
          GM04.Simulated (P₁.restrict A₁) (P₂.restrict A₂)),
      GM04.Simulated P₁ P₂ by
    exact hind ℒ₂.ncard rfl hQ₁ hQ₂ hfresh₁ hfresh₂ hη hpre hsim
  intro n
  induction n with
  | zero =>
    intro P₁ Q₁ P₂ Q₂ ℒ₁ ℒ₂ hcard hQ₁ hQ₂ _ _ ηv ηe hη _ hsim
    exact simulated_of_empty_placeHeart hQ₁ hQ₂ hcard hη hsim
  | succ m ih =>
    intro P₁ Q₁ P₂ Q₂ ℒ₁ ℒ₂ hcard hQ₁ hQ₂ hfresh₁ hfresh₂ ηv ηe hη hpre hsim
    have hℒ₂_nonempty : ℒ₂.Nonempty :=
      (Set.ncard_pos hQ₂.isRootedLocation.finite).1 (by omega)
    obtain ⟨A₂, hA₂⟩ := hℒ₂_nonempty
    let ℒ₂' : Set (RootedHypergraph α₂ β₂) := ℒ₂ \ {A₂}
    have hcard' : ℒ₂'.ncard = m := by
      have hdiff : ℒ₂'.ncard = ℒ₂.ncard - 1 := Set.ncard_sdiff_singleton_of_mem hA₂
      omega
    have hℒ₂' : IsRootedLocation P₂.G ℒ₂' :=
      hQ₂.isRootedLocation.mono Set.sdiff_subset
    have hinj₂' : Set.InjOn newEdge₂ ℒ₂' :=
      hQ₂.injOn_newEdge.mono Set.sdiff_subset
    have hfresh₂' : ∀ ⦃A⦄, A ∈ ℒ₂' → newEdge₂ A ∉ P₂.G.edgeSet :=
      fun _ hA ↦ hfresh₂ hA.1
    have hnotMem₂' : ∀ ⦃A⦄, A ∈ ℒ₂' → newEdge₂ A ∉ (rootedLocationCore P₂.G ℒ₂').edgeSet :=
      fun _ hA hc ↦ hfresh₂' hA (mem_rootedLocationCore_edgeSet_iff.1 hc).1
    let Q₂' := mkPlaceHeart P₂ hℒ₂' newEdge₂ hinj₂' hnotMem₂'
    have hQ₂' : IsPlaceHeart P₂ ℒ₂' newEdge₂ Q₂' :=
      isPlaceHeart_mkPlaceHeart P₂ hℒ₂' newEdge₂ hinj₂' hnotMem₂'
    have hcomp₂ := isComplemented_heart_diff hQ₂.isRootedLocation hA₂ hQ₂'
    let B₂ := complement Q₂'.G A₂ hcomp₂
    obtain ⟨hV₂, hE₂, hroots₂, hle_B₂, hequiv_B₂⟩ :=
      complement_heart_diff_props hQ₂ hA₂ hfresh₂ hQ₂'
    have hequiv_A₂ := restrict_left_equiv_of_heart_diff hQ₂.isRootedLocation hA₂ hfresh₂ hQ₂'
    by_cases hhit : ∃ e ∈ Q₁.G.edgeSet, ηe e = newEdge₂ A₂
    · -- Case 2: `newEdge₂ A₂ = ηe (newEdge₁ A₁)` for some `A₁ ∈ ℒ₁`.
      rcases hhit with ⟨e₀, he₀, he₀_eq⟩
      obtain ⟨A₁, hA₁, rfl⟩ := hpre he₀ hA₂ he₀_eq
      obtain ⟨A₂_star, hA₂_star, hA₂_star_eq, hsim_A₁⟩ := hsim hA₁
      have hA₂_eq : A₂_star = A₂ :=
        hQ₂.injOn_newEdge hA₂_star hA₂ (hA₂_star_eq.symm.trans he₀_eq)
      subst A₂_star
      let ℒ₁' : Set (RootedHypergraph α₁ β₁) := ℒ₁ \ {A₁}
      have hℒ₁' : IsRootedLocation P₁.G ℒ₁' :=
        hQ₁.isRootedLocation.mono Set.sdiff_subset
      have hinj₁' : Set.InjOn newEdge₁ ℒ₁' :=
        hQ₁.injOn_newEdge.mono Set.sdiff_subset
      have hfresh₁' : ∀ ⦃A⦄, A ∈ ℒ₁' → newEdge₁ A ∉ P₁.G.edgeSet :=
        fun _ hA ↦ hfresh₁ hA.1
      have hnotMem₁' : ∀ ⦃A⦄, A ∈ ℒ₁' → newEdge₁ A ∉ (rootedLocationCore P₁.G ℒ₁').edgeSet :=
        fun _ hA hc ↦ hfresh₁' hA (mem_rootedLocationCore_edgeSet_iff.1 hc).1
      let Q₁' := mkPlaceHeart P₁ hℒ₁' newEdge₁ hinj₁' hnotMem₁'
      have hQ₁' : IsPlaceHeart P₁ ℒ₁' newEdge₁ Q₁' :=
        isPlaceHeart_mkPlaceHeart P₁ hℒ₁' newEdge₁ hinj₁' hnotMem₁'
      have hcomp₁ := isComplemented_heart_diff hQ₁.isRootedLocation hA₁ hQ₁'
      let B₁ := complement Q₁'.G A₁ hcomp₁
      obtain ⟨_, hE₁, _, _, hequiv_B₁⟩ :=
        complement_heart_diff_props hQ₁ hA₁ hfresh₁ hQ₁'
      have hequiv_A₁ := restrict_left_equiv_of_heart_diff hQ₁.isRootedLocation hA₁ hfresh₁ hQ₁'
      obtain ⟨η'v, η'e, hη'_P⟩ := hsim_A₁
      have hη' : GM04.IsRealizableExpansion (Q₁'.restrict A₁) (Q₂'.restrict A₂) η'v η'e :=
        PatchworkEquiv.isRealizableExpansion_congr hequiv_A₁.symm hequiv_A₂.symm hη'_P
      have hη''_Q : GM04.IsRealizableExpansion (Q₁.restrict B₁) (Q₂.restrict B₂) ηv ηe :=
        isRealizableExpansion_restrict_complement_of_heart_diff
          hQ₁ hA₁ hfresh₁ hQ₁' hQ₂ hA₂ hfresh₂ hQ₂' hη he₀_eq
      have hη'' : GM04.IsRealizableExpansion (Q₁'.restrict B₁) (Q₂'.restrict B₂) ηv ηe :=
        PatchworkEquiv.isRealizableExpansion_congr hequiv_B₁ hequiv_B₂ hη''_Q
      have hroots_mem := roots_mem_of_placeHeart_expansion hQ₁ hQ₂ hA₁ hA₂ hη he₀_eq
      have hη₀ := theorem_5_6_proof hcomp₁.isSeparation hcomp₂.isSeparation hη' hη'' hroots_mem
      refine ih hcard' hQ₁' hQ₂' hfresh₁' hfresh₂' hη₀ ?_ ?_
      · intro e A₂' he_Q₁' hA₂' hEq_e
        by_cases he_A₁ : e ∈ A₁.edgeSet
        · exfalso
          have hglue : GM04.glueEdge A₁ η'e ηe e = η'e e := GM04.glueEdge_of_mem_left he_A₁
          have he'_A₂ : η'e e ∈ A₂.edgeSet := hη'.1.edge_mem e he_A₁
          rw [hglue] at hEq_e
          rw [hEq_e] at he'_A₂
          exact hfresh₂' hA₂' ((hQ₂.isRootedLocation.isComplemented hA₂).le.edgeSet_subset he'_A₂)
        · have hglue : GM04.glueEdge A₁ η'e ηe e = ηe e := GM04.glueEdge_of_notMem_left he_A₁
          rw [hglue] at hEq_e
          have he_B₁ : e ∈ B₁.edgeSet := ⟨he_Q₁', he_A₁⟩
          have he_Q₁ : e ∈ Q₁.G.edgeSet ∧ e ≠ newEdge₁ A₁ := by
            simpa using (hE₁ ▸ he_B₁ : e ∈ Q₁.G.edgeSet \ {newEdge₁ A₁})
          obtain ⟨A₁', hA₁', rfl⟩ := hpre he_Q₁.1 hA₂'.1 hEq_e
          have hne_A₁' : A₁' ≠ A₁ := fun hEq ↦ he_Q₁.2 (congrArg newEdge₁ hEq)
          exact ⟨A₁', ⟨hA₁', hne_A₁'⟩, rfl⟩
      · intro A₁' hA₁'
        have hnot_A₁ : newEdge₁ A₁' ∉ A₁.edgeSet := fun heA₁ ↦
          hfresh₁' hA₁' ((hQ₁.isRootedLocation.isComplemented hA₁).le.edgeSet_subset heA₁)
        have hglue : GM04.glueEdge A₁ η'e ηe (newEdge₁ A₁') = ηe (newEdge₁ A₁') :=
          GM04.glueEdge_of_notMem_left hnot_A₁
        obtain ⟨A₂', hA₂', hEq_e₂, hsim_A₁'⟩ := hsim hA₁'.1
        have hne_A₂' : A₂' ≠ A₂ := by
          rintro rfl
          have he₁'_Q₁ : newEdge₁ A₁' ∈ Q₁.G.edgeSet := by
            rw [hQ₁.edgeSet_eq]; exact Or.inr ⟨A₁', hA₁'.1, rfl⟩
          have he₁_Q₁ : newEdge₁ A₁ ∈ Q₁.G.edgeSet := by
            rw [hQ₁.edgeSet_eq]; exact Or.inr ⟨A₁, hA₁, rfl⟩
          have hEq_new : newEdge₁ A₁' = newEdge₁ A₁ :=
            hη.1.edge_injOn he₁'_Q₁ he₁_Q₁ (hEq_e₂.trans he₀_eq.symm)
          exact hA₁'.2 (Set.mem_singleton_iff.2 (hQ₁.injOn_newEdge hA₁'.1 hA₁ hEq_new))
        exact ⟨A₂', ⟨hA₂', hne_A₂'⟩, hglue.trans hEq_e₂, hsim_A₁'⟩
    · -- Case 1: `∀ e ∈ Q₁.G.edgeSet, ηe e ≠ newEdge₂ A₂`.
      push Not at hhit
      let K := singleEdgeRootedHypergraph (newEdge₂ A₂) A₂.roots A₂.roots_nodup
      have hsep_K : Q₂.G.IsSeparation K B₂ :=
        isSeparation_singleEdge_complement_of_heart_diff hQ₂ hA₂ hfresh₂ hQ₂'
      have hsep'_A₂ : Q₂'.G.IsSeparation A₂ B₂ := hcomp₂.isSeparation
      have hle_B₂_Q₂' : B₂.toHypergraph ≤ Q₂'.G.toHypergraph :=
        hsep'_A₂.isSeparation.right_le
      have hB₂_dom : ∀ e ∈ B₂.edgeSet, e ∈ Q₂.dom ↔ e ∈ Q₂'.dom := by
        intro e heB₂
        have hEq := congrArg (e ∈ ·) hequiv_B₂.dom_eq
        rw [Q₂.restrict_dom hle_B₂, Q₂'.restrict_dom hle_B₂_Q₂'] at hEq
        exact ⟨fun h ↦ (hEq.mp ⟨h, heB₂⟩).1, fun h ↦ (hEq.mpr ⟨h, heB₂⟩).1⟩
      have hB₂_μ : ∀ e ∈ B₂.edgeSet, e ∈ Q₂.dom → Q₂.μ e = Q₂'.μ e := by
        intro e heB₂ hd
        have he'd : e ∈ (Q₂.restrict B₂).dom := by
          rw [Q₂.restrict_dom hle_B₂]
          exact ⟨hd, heB₂⟩
        exact hequiv_B₂.μ_eq he'd
      have hB₂_Δ : ∀ e ∈ B₂.edgeSet, Q₂.Δ e = Q₂'.Δ e := by
        intro e heB₂
        have h := hequiv_B₂.Δ_eq heB₂
        rwa [Q₂.restrict_Δ hle_B₂ heB₂, Q₂'.restrict_Δ hle_B₂_Q₂' heB₂] at h
      have hB₂_φ : ∀ e ∈ B₂.edgeSet, Q₂.φ e ≤ Q₂'.φ e :=
        fun _ heB₂ ↦ (hequiv_B₂.φ_eq heB₂).le
      have hfeas_sub :
          (feasibleGroupings (Q₂.restrict K)).groupings ⊆
            (feasibleGroupings (Q₂'.restrict A₂)).groupings := by
        have hle_K : K.toHypergraph ≤ Q₂.G.toHypergraph :=
          hsep_K.isSeparation.left_le
        have hfeas_K :
            (feasibleGroupings (Q₂.restrict K)).groupings =
              (Q₂.Δ (newEdge₂ A₂)).groupings := by
          ext δ
          have hiff := isFeasibleGrouping_singleEdge_iff
            (P' := Q₂.restrict K) (e₀ := newEdge₂ A₂)
            rfl rfl
            (by
              ext v
              exact ⟨fun h ↦ h.2, fun hv ↦ ⟨rfl, hv⟩⟩)
            δ
          change IsFeasibleGrouping (Q₂.restrict K) δ ↔ δ ∈ Q₂.Δ (newEdge₂ A₂)
          rw [hiff]
          have heK : newEdge₂ A₂ ∈ K.edgeSet := Set.mem_singleton _
          change δ ∈ (Q₂.restrict K).Δ (newEdge₂ A₂) ↔ δ ∈ Q₂.Δ (newEdge₂ A₂)
          rw [Q₂.restrict_Δ hle_K heK]
        have hΔ_eq :
            (Q₂.Δ (newEdge₂ A₂)).groupings =
              (feasibleGroupings (P₂.restrict A₂)).groupings :=
          congrArg GM04.Patch.groupings (hQ₂.Δ_newEdge hA₂)
        have hequiv_gr :
            (feasibleGroupings (P₂.restrict A₂)).groupings =
              (feasibleGroupings (Q₂'.restrict A₂)).groupings :=
          congrArg GM04.Patch.groupings hequiv_A₂.symm.feasibleGroupings_eq
        rw [hfeas_K, hΔ_eq, hequiv_gr]
      have hη_edge_B₂ : ∀ e ∈ Q₁.G.edgeSet, ηe e ∈ B₂.edgeSet := by
        intro e he
        rw [hE₂]
        exact ⟨hη.1.edge_mem e he, hhit e he⟩
      have hη_vert_B₂ : ∀ v ∈ Q₁.G.vertexSet, (ηv v ∩ B₂.vertexSet).Nonempty := by
        intro v hv
        rw [hV₂, Set.inter_eq_self_of_subset_left (hη.1.vertex_subset v hv)]
        exact hη.1.vertex_nonempty v hv
      obtain ⟨η₀v, hη₀, _⟩ :=
        theorem_5_3_proof hsep_K hsep'_A₂ rfl hB₂_dom hB₂_μ hB₂_Δ hB₂_φ hfeas_sub
          hη hη_edge_B₂ hη_vert_B₂
      refine ih hcard' hQ₁ hQ₂' hfresh₁ hfresh₂' hη₀ ?_ ?_
      · intro e A₂' he hA₂' hEq_e
        exact hpre he hA₂'.1 hEq_e
      · intro A₁ hA₁
        obtain ⟨A₂', hA₂', hEq_e₂, hsim_A₁⟩ := hsim hA₁
        have hne_A₂' : A₂' ≠ A₂ := by
          rintro rfl
          have he₁_Q₁ : newEdge₁ A₁ ∈ Q₁.G.edgeSet := by
            rw [hQ₁.edgeSet_eq]; exact Or.inr ⟨A₁, hA₁, rfl⟩
          exact hhit (newEdge₁ A₁) he₁_Q₁ hEq_e₂
        exact ⟨A₂', ⟨hA₂', hne_A₂'⟩, hEq_e₂, hsim_A₁⟩

/-- Injectivity of `mapInlRooted γ`. -/
theorem mapInlRooted_injective (γ : Type*) :
    Function.Injective (mapInlRooted γ : RootedHypergraph α β → RootedHypergraph α (β ⊕ γ)) := by
  intro A B hEq
  refine RootedHypergraph.ext ?_ (congrArg (fun G : RootedHypergraph α (β ⊕ γ) ↦ G.roots) hEq)
  refine Hypergraph.ext
    (congrArg (fun G : RootedHypergraph α (β ⊕ γ) ↦ G.vertexSet) hEq) ?_ ?_
  · ext e
    have hE := congrArg (fun G : RootedHypergraph α (β ⊕ γ) ↦ Sum.inl e ∈ G.edgeSet) hEq
    simpa [mapInlRooted, mapInlH] using hE
  · funext e v
    have hI := congrArg (fun G : RootedHypergraph α (β ⊕ γ) ↦ G.Inc (Sum.inl e) v) hEq
    simpa [mapInlRooted, mapInlH] using hI

/-- `mapInlRooted γ` maps a rooted location in `G` to a rooted location in `mapInlRooted γ G`. -/
theorem isRootedLocation_mapInl (γ : Type*) {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ) :
    IsRootedLocation (mapInlRooted γ G) (mapInlRooted γ '' ℒ) := by
  have hcomp_mapInl : ∀ {A : RootedHypergraph α β},
      IsComplemented G A → IsComplemented (mapInlRooted γ G) (mapInlRooted γ A) := by
    intro A hcomp
    refine
      { le :=
          { vertexSet_subset := hcomp.le.vertexSet_subset
            edgeSet_subset := Set.image_mono hcomp.le.edgeSet_subset
            ends_eq := by
              rintro _ ⟨e, he, rfl⟩
              exact hcomp.le.ends_eq e he }
        roots_mem := hcomp.roots_mem
        inc_diff_mem := by
          rintro v _ hvA ⟨⟨e, heG, rfl⟩, hnotA⟩ hinc
          have henotA : e ∉ A.edgeSet := fun heA ↦ hnotA ⟨e, heA, rfl⟩
          exact hcomp.inc_diff_mem hvA ⟨heG, henotA⟩ hinc }
  refine
    { isComplemented := by
        rintro _ ⟨A, hA, rfl⟩
        exact hcomp_mapInl (hℒ.isComplemented hA)
      le_complement := by
        rintro _ ⟨A₁, h₁, rfl⟩ _ ⟨A₂, h₂, rfl⟩ hne
        have hne_A : A₁ ≠ A₂ := fun hEq ↦ hne (congrArg (mapInlRooted γ) hEq)
        have hle := hℒ.le_complement h₁ h₂ hne_A
        refine
          { vertexSet_subset := hle.vertexSet_subset
            edgeSet_subset := by
              rintro _ ⟨e, he₁, rfl⟩
              have he_comp := hle.edgeSet_subset he₁
              exact ⟨⟨e, he_comp.1, rfl⟩, fun ⟨e', he₂, hEq⟩ ↦
                he_comp.2 (Sum.inl.inj hEq ▸ he₂)⟩
            ends_eq := by
              rintro _ ⟨e, he₁, rfl⟩
              have he_comp := hle.edgeSet_subset he₁
              have he_comp_inl :
                  Sum.inl e ∈ (mapInlRooted γ G).edgeSet \ (mapInlRooted γ A₂).edgeSet :=
                ⟨⟨e, he_comp.1, rfl⟩, fun ⟨_, he₂, hEq⟩ ↦
                  he_comp.2 (Sum.inl.inj hEq ▸ he₂)⟩
              have hends := hle.ends_eq e he₁
              ext v
              have hv : v ∈ (complement G A₂ (hℒ.isComplemented h₂)).ends e ↔ v ∈ A₁.ends e :=
                Set.ext_iff.1 hends v
              exact ⟨fun ⟨_, hinc⟩ ↦ hv.1 ⟨he_comp, hinc⟩,
                fun hinc₁ ↦ ⟨he_comp_inl, (hv.2 hinc₁).2⟩⟩ } }

/-- The vertex set and edge set of `rootedLocationCore (mapInlRooted γ G) (mapInlRooted γ '' ℒ)`. -/
theorem rootedLocationCore_mapInl_sets (γ : Type*) {G : RootedHypergraph α β}
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation G ℒ) :
    (rootedLocationCore (mapInlRooted γ G) (mapInlRooted γ '' ℒ)).vertexSet =
      (rootedLocationCore G ℒ).vertexSet ∧
    (rootedLocationCore (mapInlRooted γ G) (mapInlRooted γ '' ℒ)).edgeSet =
      Sum.inl '' (rootedLocationCore G ℒ).edgeSet := by
  have hℒ_plus := isRootedLocation_mapInl γ hℒ
  refine ⟨?_, ?_⟩
  · ext v
    rw [mem_rootedLocationCore_vertexSet_iff hℒ_plus, mem_rootedLocationCore_vertexSet_iff hℒ]
    simp only [mapInlRooted, mapInlH, Set.forall_mem_image]
    rfl
  · ext x
    rw [mem_rootedLocationCore_edgeSet_iff]
    simp only [mapInlRooted, mapInlH, Set.mem_image]
    constructor
    · rintro ⟨⟨e, heG, rfl⟩, hall⟩
      refine ⟨e, ?_, rfl⟩
      rw [mem_rootedLocationCore_edgeSet_iff]
      exact ⟨heG, fun A hA heA ↦ hall (mapInlRooted γ A) ⟨A, hA, rfl⟩ ⟨e, heA, rfl⟩⟩
    · rintro ⟨e, he_core, rfl⟩
      rw [mem_rootedLocationCore_edgeSet_iff] at he_core
      refine ⟨⟨e, he_core.1, rfl⟩, ?_⟩
      rintro _ ⟨A, hA, rfl⟩ ⟨e', he'A, hEq⟩
      cases Sum.inl.inj hEq
      exact he_core.2 A hA he'A

/-- `feasibleGroupings` is preserved under `mapInlPatchwork` and `mapInlRooted`. -/
theorem feasibleGroupings_restrict_mapInl (γ : Type*) (d : β) (P : PartialPatchwork Ω α β)
    {ℒ : Set (RootedHypergraph α β)} (hℒ : IsRootedLocation P.G ℒ)
    {A : RootedHypergraph α β} (hA : A ∈ ℒ) :
    feasibleGroupings ((mapInlPatchwork γ P).restrict (mapInlRooted γ A)) =
      feasibleGroupings (P.restrict A) := by
  have hleA : A.toHypergraph ≤ P.G.toHypergraph := (hℒ.isComplemented hA).le
  have hleA_plus : (mapInlRooted γ A).toHypergraph ≤ (mapInlPatchwork γ P).G.toHypergraph :=
    ((isRootedLocation_mapInl γ hℒ).isComplemented ⟨A, hA, rfl⟩).le
  exact feasibleGroupings_eq_of_edge_bij
    ((mapInlPatchwork γ P).restrict (mapInlRooted γ A)).toUnlabeled
    (P.restrict A).toUnlabeled
    (Sum.elim id (fun _ ↦ d))
    rfl rfl
    (by
      ext e
      simp only [Set.mem_image, mapInlRooted, mapInlH]
      exact ⟨fun ⟨_, ⟨e', he', rfl⟩, hEq⟩ ↦ hEq ▸ he', fun he ↦ ⟨Sum.inl e, ⟨e, he, rfl⟩, rfl⟩⟩)
    (by rintro _ ⟨e₁, _, rfl⟩ _ ⟨e₂, _, rfl⟩ hEq; exact congrArg Sum.inl hEq)
    (by
      rintro _ ⟨e, heA, rfl⟩
      have heA_plus : Sum.inl e ∈ (mapInlRooted γ A).edgeSet := ⟨e, heA, rfl⟩
      change (P.restrict A).Δ e = ((mapInlPatchwork γ P).restrict (mapInlRooted γ A)).Δ (Sum.inl e)
      rw [P.restrict_Δ hleA heA, (mapInlPatchwork γ P).restrict_Δ hleA_plus heA_plus]
      rfl)

private theorem placeHeart_expansion_to_original [Preorder Ω] {α β : Type*}
    {P Q : PartialPatchwork Ω α β} {ℒ : Set (RootedHypergraph α β)}
    {newEdge : RootedHypergraph α β → β} (hQ : IsPlaceHeart P ℒ newEdge Q)
    {Q_plus : PartialPatchwork Ω α (β ⊕ RootedHypergraph α β)}
    {newEdge_plus : RootedHypergraph α (β ⊕ RootedHypergraph α β) →
      β ⊕ RootedHypergraph α β}
    (hQ_plus : IsPlaceHeart (mapInlPatchwork (RootedHypergraph α β) P)
      (mapInlRooted (RootedHypergraph α β) '' ℒ) newEdge_plus Q_plus)
    (hnewEdge_eq : ∀ {A : RootedHypergraph α β}, A ∈ ℒ →
      newEdge_plus (mapInlRooted (RootedHypergraph α β) A) = Sum.inr A)
    :
    let γ := RootedHypergraph α β
    let π : β ⊕ γ → β := Sum.elim id newEdge
    GM04.IsRealizableExpansion Q_plus Q (fun v ↦ {v}) π := by
  classical
  intro γ π
  let P_plus := mapInlPatchwork γ P
  let ℒ_plus := mapInlRooted γ '' ℒ
  let d : β := newEdge P.G
  have hcoreV : (rootedLocationCore P_plus.G ℒ_plus).vertexSet =
      (rootedLocationCore P.G ℒ).vertexSet :=
    (rootedLocationCore_mapInl_sets γ hQ.isRootedLocation).1
  have hcoreE : (rootedLocationCore P_plus.G ℒ_plus).edgeSet =
      Sum.inl '' (rootedLocationCore P.G ℒ).edgeSet :=
    (rootedLocationCore_mapInl_sets γ hQ.isRootedLocation).2
  refine isRealizableExpansion_of_edge_bij Q_plus Q π
    (by rw [hQ_plus.vertexSet_eq, hQ.vertexSet_eq, hcoreV])
    (by rw [hQ_plus.roots_eq, hQ.roots_eq]; rfl)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hQ_plus.edgeSet_eq, hQ.edgeSet_eq, hcoreE]
    ext e
    simp only [Set.mem_image, Set.mem_union]
    constructor
    · rintro ⟨x, ⟨e', he', rfl⟩ | ⟨_, ⟨A, hA, rfl⟩, rfl⟩, rfl⟩
      · exact Or.inl he'
      · rw [hnewEdge_eq hA]; exact Or.inr ⟨A, hA, rfl⟩
    · rintro (he | ⟨A, hA, rfl⟩)
      · exact ⟨Sum.inl e, Or.inl ⟨e, he, rfl⟩, rfl⟩
      · exact ⟨Sum.inr A, Or.inr ⟨mapInlRooted γ A, ⟨A, hA, rfl⟩, hnewEdge_eq hA⟩, rfl⟩
  · intro x₁ hx₁ x₂ hx₂ hEq
    rw [hQ_plus.edgeSet_eq, hcoreE] at hx₁ hx₂
    rcases hx₁ with ⟨e₁, he₁, rfl⟩ | ⟨_, ⟨A₁, hA₁, rfl⟩, rfl⟩ <;>
      rcases hx₂ with ⟨e₂, he₂, rfl⟩ | ⟨_, ⟨A₂, hA₂, rfl⟩, rfl⟩
    · exact congrArg Sum.inl hEq
    · rw [hnewEdge_eq hA₂] at hEq
      change e₁ = newEdge A₂ at hEq
      exact (hQ.newEdge_notMem_core hA₂ (hEq ▸ he₁)).elim
    · rw [hnewEdge_eq hA₁] at hEq
      change newEdge A₁ = e₂ at hEq
      exact (hQ.newEdge_notMem_core hA₁ (hEq.symm ▸ he₂)).elim
    · rw [hnewEdge_eq hA₁, hnewEdge_eq hA₂] at hEq ⊢
      exact congrArg Sum.inr (hQ.injOn_newEdge hA₁ hA₂ hEq)
  · intro x hx
    rw [hQ_plus.edgeSet_eq, hcoreE] at hx
    rcases hx with ⟨e, he, rfl⟩ | ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    · have he_plus : Sum.inl e ∈ (rootedLocationCore P_plus.G ℒ_plus).edgeSet :=
        hcoreE ▸ ⟨e, he, rfl⟩
      dsimp only [π, Sum.elim_inl, id_eq]
      rw [hQ_plus.ends_core he_plus, hQ.ends_core he]
      rfl
    · have h₁ := hQ_plus.ends_newEdge ⟨A, hA, rfl⟩
      rw [hnewEdge_eq hA] at h₁ ⊢
      dsimp only [π, Sum.elim_inr]
      rw [h₁, hQ.ends_newEdge hA]
      rfl
  · intro x hx
    rw [hQ_plus.edgeSet_eq, hcoreE] at hx
    rw [hQ_plus.dom_eq, hQ.dom_eq, hcoreE]
    rcases hx with ⟨e, he, rfl⟩ | ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    · simp only [π, Sum.elim_inl, Set.mem_union, Set.mem_inter_iff, Set.mem_image]
      constructor
      · rintro (⟨_, ⟨_, hd, hEq⟩⟩ | ⟨_, ⟨A, hA, rfl⟩, hEq⟩)
        · cases Sum.inl.inj hEq; exact Or.inl ⟨he, hd⟩
        · rw [hnewEdge_eq hA] at hEq; exact nomatch hEq
      · rintro (⟨_, hd⟩ | ⟨A, hA, hEq⟩)
        · exact Or.inl ⟨⟨e, he, rfl⟩, ⟨e, hd, rfl⟩⟩
        · exact (hQ.newEdge_notMem_core hA (hEq ▸ he)).elim
    · rw [hnewEdge_eq hA]
      simp only [π, Sum.elim_inr, Set.mem_union, Set.mem_image]
      exact ⟨fun _ ↦ Or.inr ⟨A, hA, rfl⟩,
        fun _ ↦ Or.inr ⟨mapInlRooted γ A, ⟨A, hA, rfl⟩, hnewEdge_eq hA⟩⟩
  · intro x hx
    rw [hQ_plus.dom_eq, hcoreE] at hx
    rcases hx with ⟨⟨e, he, rfl⟩, ⟨_, hd, hEq⟩⟩ | ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    · cases Sum.inl.inj hEq
      have he_plus : Sum.inl e ∈ (rootedLocationCore P_plus.G ℒ_plus).edgeSet :=
        hcoreE ▸ ⟨e, he, rfl⟩
      dsimp only [π, Sum.elim_inl, id_eq]
      rw [hQ_plus.μ_core ⟨he_plus, ⟨e, hd, rfl⟩⟩, hQ.μ_core ⟨he, hd⟩]
      rfl
    · have h₁ := hQ_plus.μ_newEdge ⟨A, hA, rfl⟩
      rw [hnewEdge_eq hA] at h₁ ⊢
      dsimp only [π, Sum.elim_inr]
      rw [h₁, hQ.μ_newEdge hA]
      rfl
  · intro x hx
    rw [hQ_plus.dom_eq, hcoreE] at hx
    rcases hx with ⟨⟨e, he, rfl⟩, ⟨_, hd, hEq⟩⟩ | ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    · cases Sum.inl.inj hEq
      have he_plus : Sum.inl e ∈ (rootedLocationCore P_plus.G ℒ_plus).edgeSet :=
        hcoreE ▸ ⟨e, he, rfl⟩
      dsimp only [π, Sum.elim_inl, id_eq]
      rw [hQ_plus.Δ_core he_plus, hQ.Δ_core he]
      rfl
    · have h₁ := hQ_plus.Δ_newEdge ⟨A, hA, rfl⟩
      rw [hnewEdge_eq hA] at h₁ ⊢
      dsimp only [π, Sum.elim_inr]
      rw [h₁, hQ.Δ_newEdge hA]
      exact feasibleGroupings_restrict_mapInl γ d P hQ.isRootedLocation hA
  · intro x hx
    rw [hQ_plus.edgeSet_eq, hcoreE] at hx
    rcases hx with ⟨e, he, rfl⟩ | ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    · have he_plus : Sum.inl e ∈ (rootedLocationCore P_plus.G ℒ_plus).edgeSet :=
        hcoreE ▸ ⟨e, he, rfl⟩
      dsimp only [π, Sum.elim_inl, id_eq]
      rw [hQ_plus.φ_core he_plus, hQ.φ_core he]
      exact le_rfl
    · have h₁ := hQ_plus.φ_newEdge ⟨A, hA, rfl⟩
      rw [hnewEdge_eq hA] at h₁ ⊢
      rw [h₁]
      exact bot_le

private theorem placeHeart_expansion_from_original [Preorder Ω] {α β : Type*}
    {P Q : PartialPatchwork Ω α β} {ℒ : Set (RootedHypergraph α β)}
    {newEdge : RootedHypergraph α β → β} (hQ : IsPlaceHeart P ℒ newEdge Q)
    {Q_plus : PartialPatchwork Ω α (β ⊕ RootedHypergraph α β)}
    {newEdge_plus : RootedHypergraph α (β ⊕ RootedHypergraph α β) →
      β ⊕ RootedHypergraph α β}
    (hQ_plus : IsPlaceHeart (mapInlPatchwork (RootedHypergraph α β) P)
      (mapInlRooted (RootedHypergraph α β) '' ℒ) newEdge_plus Q_plus)
    (hnewEdge_eq : ∀ {A : RootedHypergraph α β}, A ∈ ℒ →
      newEdge_plus (mapInlRooted (RootedHypergraph α β) A) = Sum.inr A)
    {ι : β → β ⊕ RootedHypergraph α β}
    (hι_core : ∀ {e}, e ∈ (rootedLocationCore P.G ℒ).edgeSet → ι e = Sum.inl e)
    (hι_new : ∀ {A}, A ∈ ℒ → ι (newEdge A) = Sum.inr A) :
    GM04.IsRealizableExpansion Q Q_plus (fun v ↦ {v}) ι := by
  classical
  let γ := RootedHypergraph α β
  let P_plus := mapInlPatchwork γ P
  let ℒ_plus := mapInlRooted γ '' ℒ
  let d : β := newEdge P.G
  have hcoreV : (rootedLocationCore P_plus.G ℒ_plus).vertexSet =
      (rootedLocationCore P.G ℒ).vertexSet :=
    (rootedLocationCore_mapInl_sets γ hQ.isRootedLocation).1
  have hcoreE : (rootedLocationCore P_plus.G ℒ_plus).edgeSet =
      Sum.inl '' (rootedLocationCore P.G ℒ).edgeSet :=
    (rootedLocationCore_mapInl_sets γ hQ.isRootedLocation).2
  refine isRealizableExpansion_of_edge_bij Q Q_plus ι
    (by rw [hQ.vertexSet_eq, hQ_plus.vertexSet_eq, hcoreV])
    (by rw [hQ.roots_eq, hQ_plus.roots_eq]; rfl)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hQ.edgeSet_eq, hQ_plus.edgeSet_eq, hcoreE]
    ext x
    simp only [Set.mem_image, Set.mem_union]
    constructor
    · rintro ⟨e, he | ⟨A, hA, rfl⟩, rfl⟩
      · rw [hι_core he]; exact Or.inl ⟨e, he, rfl⟩
      · rw [hι_new hA]
        exact Or.inr ⟨mapInlRooted γ A, ⟨A, hA, rfl⟩, hnewEdge_eq hA⟩
    · rintro (⟨e, he, rfl⟩ | ⟨_, ⟨A, hA, rfl⟩, rfl⟩)
      · exact ⟨e, Or.inl he, hι_core he⟩
      · rw [hnewEdge_eq hA]
        exact ⟨newEdge A, Or.inr ⟨A, hA, rfl⟩, hι_new hA⟩
  · intro e₁ he₁ e₂ he₂ hEq
    rw [hQ.edgeSet_eq] at he₁ he₂
    rcases he₁ with he₁ | ⟨A₁, hA₁, rfl⟩ <;> rcases he₂ with he₂ | ⟨A₂, hA₂, rfl⟩
    · rw [hι_core he₁, hι_core he₂] at hEq; exact Sum.inl.inj hEq
    · rw [hι_core he₁, hι_new hA₂] at hEq; exact nomatch hEq
    · rw [hι_new hA₁, hι_core he₂] at hEq; exact nomatch hEq
    · rw [hι_new hA₁, hι_new hA₂] at hEq
      exact congrArg newEdge (Sum.inr.inj hEq)
  · intro e he
    rw [hQ.edgeSet_eq] at he
    rcases he with he | ⟨A, hA, rfl⟩
    · rw [hι_core he]
      have he_plus : Sum.inl e ∈ (rootedLocationCore P_plus.G ℒ_plus).edgeSet :=
        hcoreE ▸ ⟨e, he, rfl⟩
      rw [hQ.ends_core he, hQ_plus.ends_core he_plus]
      rfl
    · rw [hι_new hA, hQ.ends_newEdge hA]
      have h₂ := hQ_plus.ends_newEdge ⟨A, hA, rfl⟩
      rw [hnewEdge_eq hA] at h₂
      rw [h₂]
      rfl
  · intro e he
    rw [hQ.edgeSet_eq] at he
    rw [hQ.dom_eq, hQ_plus.dom_eq, hcoreE]
    rcases he with he | ⟨A, hA, rfl⟩
    · rw [hι_core he]
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_image]
      constructor
      · rintro (⟨_, hd⟩ | ⟨A, hA, hEq⟩)
        · exact Or.inl ⟨⟨e, he, rfl⟩, ⟨e, hd, rfl⟩⟩
        · exact (hQ.newEdge_notMem_core hA (hEq ▸ he)).elim
      · rintro (⟨_, ⟨_, hd, hEq⟩⟩ | ⟨_, ⟨A, hA, rfl⟩, hEq⟩)
        · cases Sum.inl.inj hEq; exact Or.inl ⟨he, hd⟩
        · rw [hnewEdge_eq hA] at hEq; exact nomatch hEq
    · rw [hι_new hA]
      simp only [Set.mem_union, Set.mem_image]
      exact ⟨fun _ ↦ Or.inr ⟨mapInlRooted γ A, ⟨A, hA, rfl⟩, hnewEdge_eq hA⟩,
        fun _ ↦ Or.inr ⟨A, hA, rfl⟩⟩
  · intro e hd
    rw [hQ.dom_eq] at hd
    rcases hd with ⟨he, hd⟩ | ⟨A, hA, rfl⟩
    · rw [hι_core he]
      have he_plus : Sum.inl e ∈ (rootedLocationCore P_plus.G ℒ_plus).edgeSet :=
        hcoreE ▸ ⟨e, he, rfl⟩
      rw [hQ.μ_core ⟨he, hd⟩, hQ_plus.μ_core ⟨he_plus, ⟨e, hd, rfl⟩⟩]
      rfl
    · rw [hι_new hA, hQ.μ_newEdge hA]
      have h₂ := hQ_plus.μ_newEdge ⟨A, hA, rfl⟩
      rw [hnewEdge_eq hA] at h₂
      rw [h₂]
      rfl
  · intro e hd
    rw [hQ.dom_eq] at hd
    rcases hd with ⟨he, hd⟩ | ⟨A, hA, rfl⟩
    · rw [hι_core he]
      have he_plus : Sum.inl e ∈ (rootedLocationCore P_plus.G ℒ_plus).edgeSet :=
        hcoreE ▸ ⟨e, he, rfl⟩
      rw [hQ.Δ_core he, hQ_plus.Δ_core he_plus]
      rfl
    · rw [hι_new hA, hQ.Δ_newEdge hA]
      have h₂ := hQ_plus.Δ_newEdge ⟨A, hA, rfl⟩
      rw [hnewEdge_eq hA] at h₂
      rw [h₂]
      exact (feasibleGroupings_restrict_mapInl γ d P hQ.isRootedLocation hA).symm
  · intro e he
    rw [hQ.edgeSet_eq] at he
    rcases he with he | ⟨A, hA, rfl⟩
    · rw [hι_core he]
      have he_plus : Sum.inl e ∈ (rootedLocationCore P_plus.G ℒ_plus).edgeSet :=
        hcoreE ▸ ⟨e, he, rfl⟩
      rw [hQ.φ_core he, hQ_plus.φ_core he_plus]
      exact le_rfl
    · rw [hι_new hA, hQ.φ_newEdge hA]
      exact bot_le

/-- **Graph Minors XVIII, (5.7)** (page 99):
"For $i = 1, 2$ let $(P_i, \mathcal{L}_i)$ be an $\Omega$-place with heart $Q_i$, using new
elements $e_i(A)$ ($A \in \mathcal{L}_i$). Suppose that $\eta$ is a realizable expansion of
$Q_1$ in $Q_2$ such that* - *if $e \in E(Q_1)$ and $\eta(e) = e_2(A_2)$ for some $A_2 \in
\mathcal{L}_2$ then $e = e_1(A_1)$ for some $A_1 \in \mathcal{L}_1$,* - *for each $A_1 \in
\mathcal{L}_1$ there exists $A_2 \in \mathcal{L}_2$ such that $\eta(e_1(A_1)) = e_2(A_2)$
and $P_1|A_1$ is simulated in $P_2|A_2$.* *Then $P_1$ is simulated in $P_2$." -/
theorem theorem_5_7_proof [Preorder Ω] {α₁ β₁ α₂ β₂ : Type*}
    {P₁ Q₁ : PartialPatchwork Ω α₁ β₁} {P₂ Q₂ : PartialPatchwork Ω α₂ β₂}
    {ℒ₁ : Set (RootedHypergraph α₁ β₁)} {ℒ₂ : Set (RootedHypergraph α₂ β₂)}
    {newEdge₁ : RootedHypergraph α₁ β₁ → β₁} {newEdge₂ : RootedHypergraph α₂ β₂ → β₂}
    (hQ₁ : IsPlaceHeart P₁ ℒ₁ newEdge₁ Q₁)
    (hQ₂ : IsPlaceHeart P₂ ℒ₂ newEdge₂ Q₂)
    {ηv : α₁ → Set α₂} {ηe : β₁ → β₂}
    (hη : GM04.IsRealizableExpansion Q₁ Q₂ ηv ηe)
    (hpre : ∀ ⦃e : β₁⦄ ⦃A₂ : RootedHypergraph α₂ β₂⦄,
      e ∈ Q₁.G.edgeSet → A₂ ∈ ℒ₂ → ηe e = newEdge₂ A₂ → ∃ A₁ ∈ ℒ₁, e = newEdge₁ A₁)
    (hsim : ∀ ⦃A₁ : RootedHypergraph α₁ β₁⦄, A₁ ∈ ℒ₁ →
      ∃ A₂ ∈ ℒ₂, ηe (newEdge₁ A₁) = newEdge₂ A₂ ∧
        GM04.Simulated (P₁.restrict A₁) (P₂.restrict A₂)) :
    GM04.Simulated P₁ P₂ := by
  classical
  -- Note that `β₁` and `β₂` are inhabited by `newEdge₁ P₁.G` and `newEdge₂ P₂.G`.
  let d₁ : β₁ := newEdge₁ P₁.G
  let d₂ : β₂ := newEdge₂ P₂.G
  let γ₁ := RootedHypergraph α₁ β₁
  let γ₂ := RootedHypergraph α₂ β₂
  let P₁_plus := mapInlPatchwork γ₁ P₁
  let P₂_plus := mapInlPatchwork γ₂ P₂
  let ℒ₁_plus := mapInlRooted γ₁ '' ℒ₁
  let ℒ₂_plus := mapInlRooted γ₂ '' ℒ₂
  let newEdge₁_plus : RootedHypergraph α₁ (β₁ ⊕ γ₁) → β₁ ⊕ γ₁ := fun B ↦
    if h : ∃ A ∈ ℒ₁, mapInlRooted γ₁ A = B then Sum.inr h.choose else Sum.inr P₁.G
  let newEdge₂_plus : RootedHypergraph α₂ (β₂ ⊕ γ₂) → β₂ ⊕ γ₂ := fun B ↦
    if h : ∃ A ∈ ℒ₂, mapInlRooted γ₂ A = B then Sum.inr h.choose else Sum.inr P₂.G
  have hnewEdge₁_eq : ∀ {A : RootedHypergraph α₁ β₁}, A ∈ ℒ₁ →
      newEdge₁_plus (mapInlRooted γ₁ A) = Sum.inr A := by
    intro A hA
    have hex : ∃ A' ∈ ℒ₁, mapInlRooted γ₁ A' = mapInlRooted γ₁ A := ⟨A, hA, rfl⟩
    simp only [newEdge₁_plus, hex, ↓reduceDIte]
    exact congrArg Sum.inr (mapInlRooted_injective γ₁ hex.choose_spec.2)
  have hnewEdge₂_eq : ∀ {A : RootedHypergraph α₂ β₂}, A ∈ ℒ₂ →
      newEdge₂_plus (mapInlRooted γ₂ A) = Sum.inr A := by
    intro A hA
    have hex : ∃ A' ∈ ℒ₂, mapInlRooted γ₂ A' = mapInlRooted γ₂ A := ⟨A, hA, rfl⟩
    simp only [newEdge₂_plus, hex, ↓reduceDIte]
    exact congrArg Sum.inr (mapInlRooted_injective γ₂ hex.choose_spec.2)
  have hℒ₁_plus : IsRootedLocation P₁_plus.G ℒ₁_plus :=
    isRootedLocation_mapInl γ₁ hQ₁.isRootedLocation
  have hℒ₂_plus : IsRootedLocation P₂_plus.G ℒ₂_plus :=
    isRootedLocation_mapInl γ₂ hQ₂.isRootedLocation
  have hinj₁_plus : Set.InjOn newEdge₁_plus ℒ₁_plus := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hEq
    rw [hnewEdge₁_eq hA, hnewEdge₁_eq hB] at hEq
    exact congrArg (mapInlRooted γ₁) (Sum.inr.inj hEq)
  have hinj₂_plus : Set.InjOn newEdge₂_plus ℒ₂_plus := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hEq
    rw [hnewEdge₂_eq hA, hnewEdge₂_eq hB] at hEq
    exact congrArg (mapInlRooted γ₂) (Sum.inr.inj hEq)
  have hfresh₁_plus : ∀ ⦃B⦄, B ∈ ℒ₁_plus → newEdge₁_plus B ∉ P₁_plus.G.edgeSet := by
    rintro _ ⟨A, hA, rfl⟩
    rw [hnewEdge₁_eq hA]
    rintro ⟨e, _, hEq⟩
    exact nomatch hEq
  have hfresh₂_plus : ∀ ⦃B⦄, B ∈ ℒ₂_plus → newEdge₂_plus B ∉ P₂_plus.G.edgeSet := by
    rintro _ ⟨A, hA, rfl⟩
    rw [hnewEdge₂_eq hA]
    rintro ⟨e, _, hEq⟩
    exact nomatch hEq
  have hnotMem₁_plus : ∀ ⦃B⦄, B ∈ ℒ₁_plus →
      newEdge₁_plus B ∉ (rootedLocationCore P₁_plus.G ℒ₁_plus).edgeSet :=
    fun _ hB hc ↦ hfresh₁_plus hB (mem_rootedLocationCore_edgeSet_iff.1 hc).1
  have hnotMem₂_plus : ∀ ⦃B⦄, B ∈ ℒ₂_plus →
      newEdge₂_plus B ∉ (rootedLocationCore P₂_plus.G ℒ₂_plus).edgeSet :=
    fun _ hB hc ↦ hfresh₂_plus hB (mem_rootedLocationCore_edgeSet_iff.1 hc).1
  let Q₁_plus := mkPlaceHeart P₁_plus hℒ₁_plus newEdge₁_plus hinj₁_plus hnotMem₁_plus
  let Q₂_plus := mkPlaceHeart P₂_plus hℒ₂_plus newEdge₂_plus hinj₂_plus hnotMem₂_plus
  have hQ₁_plus : IsPlaceHeart P₁_plus ℒ₁_plus newEdge₁_plus Q₁_plus :=
    isPlaceHeart_mkPlaceHeart P₁_plus hℒ₁_plus newEdge₁_plus hinj₁_plus hnotMem₁_plus
  have hQ₂_plus : IsPlaceHeart P₂_plus ℒ₂_plus newEdge₂_plus Q₂_plus :=
    isPlaceHeart_mkPlaceHeart P₂_plus hℒ₂_plus newEdge₂_plus hinj₂_plus hnotMem₂_plus
  let π₁ : β₁ ⊕ γ₁ → β₁ := Sum.elim id newEdge₁
  let ι₂ : β₂ → β₂ ⊕ γ₂ := fun e ↦
    if h : ∃ A ∈ ℒ₂, newEdge₂ A = e then Sum.inr h.choose else Sum.inl e
  have hι₂_core : ∀ {e}, e ∈ (rootedLocationCore P₂.G ℒ₂).edgeSet → ι₂ e = Sum.inl e := by
    intro e he
    have hnot : ¬ ∃ A ∈ ℒ₂, newEdge₂ A = e := by
      rintro ⟨A, hA, rfl⟩; exact hQ₂.newEdge_notMem_core hA he
    simp only [ι₂, hnot, ↓reduceDIte]
  have hι₂_new : ∀ {A}, A ∈ ℒ₂ → ι₂ (newEdge₂ A) = Sum.inr A := by
    intro A hA
    have hex : ∃ A' ∈ ℒ₂, newEdge₂ A' = newEdge₂ A := ⟨A, hA, rfl⟩
    simp only [ι₂, hex, ↓reduceDIte]
    exact congrArg Sum.inr (hQ₂.injOn_newEdge hex.choose_spec.1 hA hex.choose_spec.2)
  have hη_Q₁_plus := placeHeart_expansion_to_original hQ₁ hQ₁_plus hnewEdge₁_eq
  have hη_Q₂_plus := placeHeart_expansion_from_original hQ₂ hQ₂_plus hnewEdge₂_eq
    hι₂_core hι₂_new
  -- Compose `Q₁_plus → Q₁ → Q₂ → Q₂_plus`.
  have hη_plus := (hη_Q₁_plus.comp hη).comp hη_Q₂_plus
  have hsim_plus : ∀ ⦃B₁⦄, B₁ ∈ ℒ₁_plus →
      ∃ B₂ ∈ ℒ₂_plus,
         GM04.compEdge (GM04.compEdge π₁ ηe) ι₂ (newEdge₁_plus B₁) = newEdge₂_plus B₂ ∧
        GM04.Simulated (P₁_plus.restrict B₁) (P₂_plus.restrict B₂) := by
    rintro _ ⟨A₁, hA₁, rfl⟩
    obtain ⟨A₂, hA₂, hEq_e, hsim_A₁⟩ := hsim hA₁
    refine ⟨mapInlRooted γ₂ A₂, ⟨A₂, hA₂, rfl⟩, ?_, ?_⟩
    · rw [hnewEdge₁_eq hA₁, hnewEdge₂_eq hA₂]
      simp only [GM04.compEdge_apply, π₁, Sum.elim_inr]
      rw [hEq_e, hι₂_new hA₂]
    · have hle₁ : A₁.toHypergraph ≤ P₁.G.toHypergraph := (hQ₁.isRootedLocation.isComplemented
      hA₁).le
      have hle₁_plus : (mapInlRooted γ₁ A₁).toHypergraph ≤ P₁_plus.G.toHypergraph :=
        (hℒ₁_plus.isComplemented ⟨A₁, hA₁, rfl⟩).le
      have hle₂ : A₂.toHypergraph ≤ P₂.G.toHypergraph := (hQ₂.isRootedLocation.isComplemented
        hA₂).le
      have hle₂_plus : (mapInlRooted γ₂ A₂).toHypergraph ≤ P₂_plus.G.toHypergraph :=
        (hℒ₂_plus.isComplemented ⟨A₂, hA₂, rfl⟩).le
      have hsim₁ : GM04.Simulated (P₁_plus.restrict (mapInlRooted γ₁ A₁)) (P₁.restrict A₁) := by
        refine ⟨fun v ↦ {v}, Sum.elim id (fun _ ↦ d₁),
          isRealizableExpansion_of_edge_bij
            (P₁_plus.restrict (mapInlRooted γ₁ A₁)) (P₁.restrict A₁)
            (Sum.elim id (fun _ ↦ d₁)) rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
        · ext e
          simp only [Set.mem_image, mapInlRooted, mapInlH]
          exact ⟨fun ⟨_, ⟨e', he', rfl⟩, hEq⟩ ↦ hEq ▸ he', fun he ↦ ⟨Sum.inl e, ⟨e, he, rfl⟩, rfl⟩⟩
        · rintro _ ⟨e₁, _, rfl⟩ _ ⟨e₂, _, rfl⟩ hEq; exact congrArg Sum.inl hEq
        · rintro _ ⟨e, _, rfl⟩; rfl
        · rintro _ ⟨e, heA₁, rfl⟩
          rw [P₁_plus.restrict_dom hle₁_plus, P₁.restrict_dom hle₁]
          simp only [P₁_plus, mapInlPatchwork, mapInlRooted, mapInlH, Set.mem_inter_iff,
            Set.mem_image, Sum.inl.injEq, exists_eq_right, Sum.elim_inl, id_eq]
        · intro x hx
          rw [P₁_plus.restrict_dom hle₁_plus] at hx
          rcases hx with ⟨⟨e, _, rfl⟩, _⟩
          rfl
        · intro x hx
          rw [P₁_plus.restrict_dom hle₁_plus] at hx
          rcases hx with ⟨⟨e, _, rfl⟩, ⟨_, heA₁, hEq⟩⟩
          cases Sum.inl.inj hEq
          have heA₁_in : Sum.inl e ∈ (mapInlRooted γ₁ A₁).edgeSet := ⟨e, heA₁, rfl⟩
          change (P₁_plus.restrict (mapInlRooted γ₁ A₁)).Δ (Sum.inl e) = (P₁.restrict A₁).Δ e
          rw [P₁_plus.restrict_Δ hle₁_plus heA₁_in, P₁.restrict_Δ hle₁ heA₁]
          rfl
        · rintro _ ⟨e, _, rfl⟩; exact le_rfl
      have hsim₂ : GM04.Simulated (P₂.restrict A₂) (P₂_plus.restrict (mapInlRooted γ₂ A₂)) := by
        refine ⟨fun v ↦ {v}, Sum.inl,
          isRealizableExpansion_of_edge_bij
            (P₂.restrict A₂) (P₂_plus.restrict (mapInlRooted γ₂ A₂))
            Sum.inl rfl rfl rfl (fun _ _ _ _ h ↦ Sum.inl.inj h) (fun _ _ ↦ rfl)
            (fun e _ ↦ by
              rw [P₂.restrict_dom hle₂, P₂_plus.restrict_dom hle₂_plus]
              simp only [P₂_plus, mapInlPatchwork, mapInlRooted, mapInlH, Set.mem_inter_iff,
                Set.mem_image, Sum.inl.injEq, exists_eq_right])
            (fun _ _ ↦ rfl)
            (fun e hd ↦ by
              rw [P₂.restrict_dom hle₂] at hd
              have heA₂_plus : Sum.inl e ∈ (mapInlRooted γ₂ A₂).edgeSet := ⟨e, hd.2, rfl⟩
              rw [P₂.restrict_Δ hle₂ hd.2, P₂_plus.restrict_Δ hle₂_plus heA₂_plus]
              rfl)
            (fun _ _ ↦ le_rfl)⟩
      exact (hsim₁.trans hsim_A₁).trans hsim₂
  have hpre_plus : ∀ ⦃x : β₁ ⊕ γ₁⦄ ⦃B₂ : RootedHypergraph α₂ (β₂ ⊕ γ₂)⦄,
      x ∈ Q₁_plus.G.edgeSet → B₂ ∈ ℒ₂_plus →
        GM04.compEdge (GM04.compEdge π₁ ηe) ι₂ x = newEdge₂_plus B₂ →
      ∃ B₁ ∈ ℒ₁_plus, x = newEdge₁_plus B₁ := by
    rintro x _ hx ⟨A₂, hA₂, rfl⟩ hEq
    rw [hnewEdge₂_eq hA₂] at hEq
    simp only [GM04.compEdge_apply] at hEq
    have hπ₁_mem : π₁ x ∈ Q₁.G.edgeSet := hη_Q₁_plus.1.edge_mem x hx
    have hηe_mem : ηe (π₁ x) ∈ Q₂.G.edgeSet := hη.1.edge_mem (π₁ x) hπ₁_mem
    have hηe_eq : ηe (π₁ x) = newEdge₂ A₂ := by
      rw [hQ₂.edgeSet_eq] at hηe_mem
      rcases hηe_mem with he_core | ⟨A₂', hA₂', hEq'⟩
      · rw [hι₂_core he_core] at hEq
        exact nomatch hEq
      · rw [← hEq', hι₂_new hA₂'] at hEq
        exact hEq'.symm.trans (congrArg newEdge₂ (Sum.inr.inj hEq))
    obtain ⟨A₁, hA₁, hπ₁_eq⟩ := hpre hπ₁_mem hA₂ hηe_eq
    refine ⟨mapInlRooted γ₁ A₁, ⟨A₁, hA₁, rfl⟩, ?_⟩
    rw [hnewEdge₁_eq hA₁]
    have he₁_plus : Sum.inr A₁ ∈ Q₁_plus.G.edgeSet := by
      rw [hQ₁_plus.edgeSet_eq]
      exact Or.inr ⟨mapInlRooted γ₁ A₁, ⟨A₁, hA₁, rfl⟩, hnewEdge₁_eq hA₁⟩
    exact hη_Q₁_plus.1.edge_injOn hx he₁_plus hπ₁_eq
  have hsim_P_plus : GM04.Simulated P₁_plus P₂_plus :=
    theorem_5_7_of_notMem_edgeSet hQ₁_plus hQ₂_plus hfresh₁_plus hfresh₂_plus
      hη_plus hpre_plus hsim_plus
  have hsim_P₁ : GM04.Simulated P₁ P₁_plus :=
    ⟨fun v ↦ {v}, Sum.inl,
      isRealizableExpansion_of_edge_bij P₁ P₁_plus Sum.inl rfl rfl rfl
        (fun _ _ _ _ h ↦ Sum.inl.inj h) (fun _ _ ↦ rfl)
        (fun e _ ↦ ⟨fun hd ↦ ⟨e, hd, rfl⟩, fun ⟨_, hd, hEq⟩ ↦ Sum.inl.inj hEq ▸ hd⟩)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ le_rfl)⟩
  have hsim_P₂ : GM04.Simulated P₂_plus P₂ := by
    refine ⟨fun v ↦ {v}, Sum.elim id (fun _ ↦ d₂),
      isRealizableExpansion_of_edge_bij P₂_plus P₂ (Sum.elim id (fun _ ↦ d₂)) rfl rfl ?_ ?_
        ?_ ?_ ?_ ?_ ?_⟩
    · ext e
      simp only [Set.mem_image, P₂_plus, mapInlPatchwork, mapInlRooted, mapInlH]
      exact ⟨fun ⟨_, ⟨e', he', rfl⟩, hEq⟩ ↦ hEq ▸ he', fun he ↦ ⟨Sum.inl e, ⟨e, he, rfl⟩, rfl⟩⟩
    · rintro _ ⟨e₁, _, rfl⟩ _ ⟨e₂, _, rfl⟩ hEq; exact congrArg Sum.inl hEq
    · rintro _ ⟨e, _, rfl⟩; rfl
    · rintro _ ⟨e, _, rfl⟩
      simp only [P₂_plus, mapInlPatchwork, Set.mem_image, Sum.inl.injEq, exists_eq_right,
        Sum.elim_inl, id_eq]
    · rintro _ ⟨e, _, rfl⟩; rfl
    · rintro _ ⟨e, _, rfl⟩; rfl
    · rintro _ ⟨e, _, rfl⟩; exact le_rfl
  exact (hsim_P₁.trans hsim_P_plus).trans hsim_P₂

end GraphMinor.GM18
end
