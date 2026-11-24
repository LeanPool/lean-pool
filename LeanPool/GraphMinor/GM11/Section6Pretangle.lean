/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
public import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XI, (6.2): a lemma on pretangles

This file proves (6.2) of Graph Minors XI: if `(A, B)` is in a pretangle `𝒯`, then finitely many
members of `𝒯`, with their separating sets inside `V(A ∩ B)`, cannot cover `B`. The proof grows
`A` one step at a time and stays in `𝒯` by the first two tangle axioms, as the paper does.
-/

public section

namespace GraphMinor.GM11

open Hypergraph GraphMinor.GM10

variable {α β : Type*}

/-- The induction of (6.2): adding the members of a list to `(A, B)` one at a time stays in `𝒯`. -/
private theorem exists_mem_of_list {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsPretangle G θ 𝒯)
    {W : Set α} (hWfin : W.Finite) (hW : W.ncard < θ)
    (L : List (Hypergraph α β × Hypergraph α β)) (hL : ∀ p ∈ L, p ∈ 𝒯)
    (hLW : ∀ p ∈ L, (p.1 ∩ p.2).vertexSet ⊆ W) :
    ∀ {A B : Hypergraph α β}, (A, B) ∈ 𝒯 → (A ∩ B).vertexSet ⊆ W →
      ∃ A' B', (A', B') ∈ 𝒯 ∧ A.vertexSet ⊆ A'.vertexSet ∧ A.edgeSet ⊆ A'.edgeSet ∧
        (∀ p ∈ L, p.1.vertexSet ⊆ A'.vertexSet ∧ p.1.edgeSet ⊆ A'.edgeSet) := by
  induction L with
  | nil =>
    intro A B h _
    exact ⟨A, B, h, Set.Subset.rfl, Set.Subset.rfl, by simp⟩
  | cons p L ih =>
    intro A B h hABW
    have hp : p ∈ 𝒯 := hL p (by simp)
    have hsep₁ := h𝒯.isSeparation h
    have hsep₂ : G.IsSeparation p.1 p.2 := h𝒯.isSeparation (A := p.1) (B := p.2) hp
    have hsep : G.IsSeparation (A ∪ p.1) (B ∩ p.2) := hsep₁.union_inter hsep₂
    have hsubW : ((A ∪ p.1) ∩ (B ∩ p.2)).vertexSet ⊆ W := by
      rintro v ⟨hv | hv, hvB, hvp⟩
      · exact hABW ⟨hv, hvB⟩
      · exact hLW p (by simp) ⟨hv, hvp⟩
    have hord : separationOrder (A ∪ p.1) (B ∩ p.2) < θ :=
      lt_of_le_of_lt (Set.ncard_le_ncard hsubW hWfin) hW
    have hmem : (A ∪ p.1, B ∩ p.2) ∈ 𝒯 := by
      rcases h𝒯.axiom1 hsep hord with h' | h'
      · exact h'
      · exact absurd hsep.union_eq (h𝒯.axiom2 h (show (p.1, p.2) ∈ 𝒯 from hp) h')
    obtain ⟨A', B', hmem', hV, hE, hrest⟩ := ih (fun q hq => hL q (by simp [hq]))
      (fun q hq => hLW q (by simp [hq])) hmem hsubW
    refine ⟨A', B', hmem', fun v hv => hV (Or.inl hv), fun e he => hE (Or.inl he), ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨fun v hv => hV (Or.inr hv), fun e he => hE (Or.inr he)⟩
    · exact hrest q hq

/-- Graph Minors XI, (6.2) (page 89):
"(6.2) *Let $\mathscr{T}$ be a pretangle in a hypergraph $G$, and let $(A, B) \in \mathscr{T}$. Then
there do not exist $(A_1, B_2), \dots, (A_k, B_k) \in \mathscr{T}$ such that
$V(A_i \cap B_i) \subseteq V(A \cap B)$ ($1 \le i \le k$) and $B \subseteq A_1 \cup \cdots \cup
A_k$.*"
(Here $(A_1, B_2)$ in the paper is a misprint for $(A_1, B_1)$.) -/
theorem theorem_6_2_proof {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsPretangle G θ 𝒯)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯)
    (L : List (Hypergraph α β × Hypergraph α β)) (hL : ∀ p ∈ L, p ∈ 𝒯)
    (hLW : ∀ p ∈ L, (p.1 ∩ p.2).vertexSet ⊆ (A ∩ B).vertexSet)
    (hV : ∀ v ∈ B.vertexSet, ∃ p ∈ L, v ∈ p.1.vertexSet)
    (hE : ∀ e ∈ B.edgeSet, ∃ p ∈ L, e ∈ p.1.edgeSet) : False := by
  have hsep := h𝒯.isSeparation hAB
  have hWfin : (A ∩ B).vertexSet.Finite :=
    (G.vertexSet_finite.subset hsep.left_le.vertexSet_subset).subset Set.inter_subset_left
  obtain ⟨A', B', hmem, hAV, hAE, hrest⟩ := exists_mem_of_list h𝒯 hWfin (h𝒯.order_lt hAB) L hL hLW
    hAB subset_rfl
  have hsep' := h𝒯.isSeparation hmem
  have hEq : A' = G := by
    refine eq_of_le_of_vertexSet_eq_of_edgeSet_eq hsep'.left_le le_rfl ?_ ?_
    · refine hsep'.left_le.vertexSet_subset.antisymm ?_
      intro v hv
      have hv' : v ∈ (A ∪ B).vertexSet := hsep.union_eq ▸ hv
      rcases hv' with h | h
      · exact hAV h
      · obtain ⟨p, hp, hvp⟩ := hV v h
        exact (hrest p hp).1 hvp
    · refine hsep'.left_le.edgeSet_subset.antisymm ?_
      intro e he
      have he' : e ∈ (A ∪ B).edgeSet := hsep.union_eq ▸ he
      rcases he' with h | h
      · exact hAE h
      · obtain ⟨p, hp, hep⟩ := hE e h
        exact (hrest p hp).2 hep
  apply h𝒯.axiom2 hmem hmem hmem
  rw [hEq, union_self, union_self]

end GraphMinor.GM11
