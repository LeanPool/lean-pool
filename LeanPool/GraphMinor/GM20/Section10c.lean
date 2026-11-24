/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section9h

/-!
# Graph Minors XX, Section 10, (10.4)

This file deduces (10.4) from (7.3), (9.1), (10.2) and (10.3). If `sk(G)` has no `K_p` minor then no
tangle controls one, so (10.3) applies to every tangle, and (10.2) and (9.1) give a well-behaved set
that contains a heart.
The deductions using other proved results are in `Section10cProved`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM18 GraphMinor.GM10 Hypergraph
  GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

/-- The complete graph on `p` vertices, as a hypergraph. -/
def completeHypergraph (p : ℕ) : Hypergraph (Fin p) (Sym2 (Fin p)) where
  vertexSet := univ
  edgeSet := {e | ¬ e.IsDiag}
  Inc e v := ¬ e.IsDiag ∧ v ∈ e
  vertex_mem_of_inc _ _ _ := trivial
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := finite_univ
  edgeSet_finite := toFinite _

/-- `sk(G)` has a `K_p` minor: there are `p` non-null connected subgraphs of `sk(G)`, mutually
disjoint, with an edge of `sk(G)` between any two of them. A connected subgraph is given by its
vertex set `a i`. -/
def HasCliqueMinor (G : Hypergraph α β) (p : ℕ) : Prop :=
  ∃ a : Fin p → Set α, (∀ i, (a i).Nonempty ∧ a i ⊆ G.vertexSet ∧ ∀ x ∈ a i, ∀ y ∈ a i,
      Relation.ReflTransGen (fun u v ↦ G.skeleton.Adj u v ∧ u ∈ a i ∧ v ∈ a i) x y) ∧
    (∀ i j, i ≠ j → Disjoint (a i) (a j)) ∧
    ∀ i j, i ≠ j → ∃ x ∈ a i, ∃ y ∈ a j, G.skeleton.Adj x y

theorem isGraph_completeHypergraph (p : ℕ) : (completeHypergraph p).IsGraph := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    have hends : (completeHypergraph p).ends s(a, b) = {a, b} := by
      ext v
      constructor
      · intro h
        simpa using h.2
      · intro h
        exact ⟨he, by simpa using h⟩
    rw [hends]
    exact ⟨⟨a, mem_insert _ _⟩, Set.ncard_insert_le _ _ |>.trans (by simp)⟩

/-- If a tangle controls a `K_p` minor of `sk(G)` then `sk(G)` has a `K_p` minor. -/
theorem hasCliqueMinor_of_controlsMinor {G : Hypergraph α β} {p : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h : ControlsMinor G 𝒯 (completeHypergraph p)) :
    HasCliqueMinor G p := by
  obtain ⟨-, av, ae', ae, h₁, h₂, h₃, -, h₅, -, -⟩ := h
  refine ⟨av, fun i ↦ ⟨(h₁ i trivial).1, (h₁ i trivial).2.1, fun x hx y hy ↦ ?_⟩,
    fun i j hij ↦ h₂ i trivial j trivial hij,
    fun i j hij ↦ ?_⟩
  · obtain ⟨-, -, h₆, h₇, h₈⟩ := h₁ i trivial
    refine Relation.ReflTransGen.mono (fun u v huv ↦ ?_) _ _ (h₈ x hx y hy)
    exact ⟨h₆ huv, h₇ u v huv⟩
  · have hdiag : ¬ s(i, j).IsDiag := by simpa using hij
    have hmem : s(i, j) ∈ (completeHypergraph p).edgeSet := hdiag
    obtain ⟨x, hx, y, hy, hxy⟩ := h₅ _ hmem i j hij ⟨hdiag, by simp⟩ ⟨hdiag, by simp⟩
    have hadj : s(x, y) ∈ G.skeleton.edgeSet := hxy ▸ h₃ _ hmem
    exact ⟨x, hx, y, hy, hadj⟩

/-- The statement of (10.3) of Graph Minors XX. -/
def Theorem103Statement : Prop :=
  ∀ {α' β' : Type} (H : Hypergraph α' β'), H.IsGraph → ∃ (θ : ℕ) (𝒮 : Set GradedSurface), 1 ≤ θ ∧
    𝒮.Finite ∧ ∀ {α : Type u} {β : Type v} [Infinite β] (P : UnlabeledPatchwork α β), IsFree P →
      P.G.roots = [] → ∀ (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle P.G.toHypergraph θ' 𝒯 → θ ≤ θ' → ¬ ControlsMinor P.G.toHypergraph 𝒯 H →
      ∃ W ⊆ P.G.vertexSet, W.ncard < θ ∧ ∃ ℒ : Set (RootedHypergraph α β),
        IsFine (P.G.slash W) ℒ ∧ (∃ X ∈ 𝒮, IsShelled X (P.slash W) ℒ) ∧
        IsLinkedTo (P.G.slash W) (quotientTangle P.G.toHypergraph 𝒯 W) ℒ

theorem wellBehaved_empty : WellBehaved (∅ : Set (UnlabeledPatchwork α β)) := by
  intro Ω _ _ Q hQ
  obtain ⟨P, hP, -⟩ := hQ 0
  exact hP.elim

theorem wellBehaved_biUnion {ι : Type*} {𝒮 : Set ι} (h𝒮 : 𝒮.Finite)
    {𝓕 : ι → Set (UnlabeledPatchwork α β)} (h : ∀ X ∈ 𝒮, WellBehaved (𝓕 X)) :
    WellBehaved (⋃ X ∈ 𝒮, 𝓕 X) := by
  induction 𝒮, h𝒮 using Set.Finite.induction_on with
  | empty => simpa using wellBehaved_empty
  | @insert a s _ _ ih =>
    rw [Set.biUnion_insert]
    exact (h a (mem_insert _ _)).union (ih fun X hX ↦ h X (mem_insert_of_mem _ hX))

theorem isFree_slash {Ω : Type*} {P : Patchwork Ω α β} (hfree : IsFree P) (W : Set α) :
    IsFree (P.slash W) := by
  intro e he δ hδ hV
  exact ⟨hδ, hV, hfree e he _ (isGrouping_sup_emptySubgraph hδ) (by
    ext x
    simp only [SimpleGraph.Subgraph.verts_sup, emptySubgraph_verts, hV]
    change (x ∈ (P.Δ e).verts \ W ∨ x ∈ W ∩ (P.Δ e).verts) ↔ x ∈ (P.Δ e).verts
    by_cases hx : x ∈ W <;> simp [hx])⟩


end GraphMinor.GM20
