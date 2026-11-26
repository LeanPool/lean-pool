/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Decomposition.Contraction
public import LeanPool.GraphMinor.GM04.Main

/-!
# Numbered decomposition results of Graph Minors IV

The edge separation and contraction results already follow from the decomposition API.
The tree lemma and Thomas's theorem supply the inputs to the linked and rotund results.
-/

public section

namespace GraphMinor.GM04

open _root_.GraphMinor.Hypergraph

universe u v w

/-- Graph Minors IV, (3.1), page 234: an edge of a tree-decomposition gives a separation. -/
theorem theorem_3_1_proof {α : Type u} {β : Type v} {ι : Type w}
    {G : RootedHypergraph α β} {T : RootedTree ι} {τ : ι → RootedHypergraph α β}
    (h : IsTreeDecomposition G T τ) {f : ι} (hf : f ∈ T.edges) :
    G.IsSeparation (cross τ (T.subtreeAt f) f) (cross τ (T.rootSide f) T.root) :=
  h.isSeparation_edge hf

/-- Graph Minors IV, (3.2), page 234: contracting the tree and taking the union of each
component's bags preserves a tree-decomposition. -/
theorem theorem_3_2_proof {α : Type u} {β : Type v} {ι : Type w}
    {G : RootedHypergraph α β} {T : RootedTree ι} {τ : ι → RootedHypergraph α β}
    (h : IsTreeDecomposition G T τ) {F : Set ι} (hF : F ⊆ T.edges)
    {S : RootedTree ι} (hS : T.IsContraction F S) (σ : ι → RootedHypergraph α β)
    (hσ : ∀ s ∈ S.verts, σ s = cross τ (T.componentAt F s) s) :
    IsTreeDecomposition G S σ :=
  h.contraction hF hS σ hσ

/-- Graph Minors IV, (3.3), page 235, using the proved tree lemma (2.2). -/
theorem theorem_3_3_proved {α : Type u} {β : Type v} {ι : Type w}
    {R : Set (RootedHypergraph α β)}
    {sim : RootedHypergraph α β → RootedHypergraph α β → Prop}
    (hA1 : Axiom1 R) (hA2 : Axiom2 R sim)
    (𝒮 : Set (RootedTree ι × (ι → RootedHypergraph α β))) (h𝒮 : IsGood R sim 𝒮)
    (T : ℕ → RootedTree ι) (τ : ℕ → ι → RootedHypergraph α β)
    (hdec : ∀ i, IsTreeDecomposition (cross (τ i) (T i).verts (T i).root) (T i) (τ i))
    (hlinked : ∀ i, IsLinked sim (T i) (τ i) (T i).edges)
    (hbr : ∀ i, ∀ s ∈ (T i).verts, ((T i).starAt s, branching (T i) (τ i) s) ∈ 𝒮) :
    ∃ i i', i < i' ∧
      sim (cross (τ i) (T i).verts (T i).root) (cross (τ i') (T i').verts (T i').root) :=
  theorem_3_3_proof lemma_2_2 hA1 hA2 𝒮 h𝒮 T τ hdec hlinked hbr

/-- Graph Minors IV, (4.2), page 238, using the proved tree lemma (2.2). -/
theorem theorem_4_2_proved {α : Type u} {β : Type v} {ι : Type w}
    {R : Set (RootedHypergraph α β)}
    {sim : RootedHypergraph α β → RootedHypergraph α β → Prop}
    (hA1 : Axiom1 R) (hA2 : Axiom2 R sim) (hA3 : Axiom3 R sim)
    (𝒮 : Set (RootedTree ι × (ι → RootedHypergraph α β))) (h𝒮 : IsGood R sim 𝒮)
    (hsym : IsSymmetric 𝒮) (T : ℕ → RootedTree ι) (τ : ℕ → ι → RootedHypergraph α β)
    (hdec : ∀ i, IsTreeDecomposition (cross (τ i) (T i).verts (T i).root) (T i) (τ i))
    (hrot : ∀ i, IsRotund (T i) (τ i) (T i).edges)
    (hbr : ∀ i, ∀ s ∈ (T i).verts, ((T i).starAt s, branching (T i) (τ i) s) ∈ 𝒮) :
    ∃ i i', i < i' ∧
      sim (cross (τ i) (T i).verts (T i).root) (cross (τ i') (T i').verts (T i').root) :=
  theorem_4_2_proof lemma_2_2 hA1 hA2 hA3 𝒮 h𝒮 hsym T τ hdec hrot hbr

/-- Graph Minors IV, (5.1), page 238: Thomas's path-or-small-separator decomposition. -/
theorem theorem_5_1_proof : ThomasStatement.{u, v} := thomas_5_1

/-- Graph Minors IV, (5.2), page 239: a rooted hypergraph has a rotund decomposition
of the same width. -/
theorem theorem_5_2_proved {α : Type u} {β : Type v}
    (G : RootedHypergraph α β) (w : ℕ) (h : TreeWidthLE G w) :
    ∃ (T : RootedTree ℕ) (τ : ℕ → RootedHypergraph α β),
      IsTreeDecomposition G T τ ∧ WidthLE T τ w ∧ IsRotund T τ T.edges :=
  theorem_5_2_proof theorem_5_1_proof G w h

/-- Graph Minors IV, (5.3), page 240: Axioms 1–4 imply well-quasi-ordering
on each class of bounded tree-width. -/
theorem theorem_5_3_proved : Theorem53Statement.{u, v} :=
  theorem_5_3_proof lemma_2_2 theorem_5_1_proof

end GraphMinor.GM04
