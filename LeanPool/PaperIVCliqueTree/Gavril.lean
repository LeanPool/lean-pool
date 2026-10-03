/-
Copyright (c) 2026 Juan Pablo Traverso Giannini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Giannini
-/
module

public import LeanPool.PaperIVCliqueTree.SubtreeRepresentation

/-!
# Gavril's characterization of finite chordal graphs

For the converse, prune leaves of the host tree until some represented subtree
is a singleton. Its vertex is simplicial. Repeating this argument on any finite
subfamily gives a perfect elimination order through the existing PEO engine.
-/

@[expose] public section

namespace SimpleGraph

private theorem subtree_family_simplicial_aux : ∀ n : ℕ,
    ∀ {N : Type} [Fintype N] (T : SimpleGraph N), Fintype.card N = n → T.IsTree →
    ∀ {V : Type*} (G : SimpleGraph V) (F : Finset V), F.Nonempty →
    ∀ (S : V → Set N), (∀ i ∈ F, (T.induce (S i)).Connected) →
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → (G.Adj i j ↔ (S i ∩ S j).Nonempty)) →
      ∃ z ∈ F, ∀ a ∈ F, ∀ b ∈ F, G.Adj z a → G.Adj z b → a ≠ b → G.Adj a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N _ T hcard hT V G F hF S hc ha
    classical
    rcases subsingleton_or_nontrivial N with hsmall | hlarge
    · let _ := hsmall
      obtain ⟨z, hz⟩ := hF
      refine ⟨z, hz, fun a hfa b hfb _ _ hab => ?_⟩
      obtain ⟨x⟩ := (hc a hfa).nonempty
      obtain ⟨y⟩ := (hc b hfb).nonempty
      exact (ha a hfa b hfb hab).mpr
        ⟨x.val, x.property, Subsingleton.elim y.val x.val ▸ y.property⟩
    · let _ := hlarge
      obtain ⟨leaf, hdegree⟩ := hT.exists_vert_degree_one_of_nontrivial
      obtain ⟨neighbour, hadj, hunique⟩ := degree_eq_one_iff_existsUnique_adj.mp hdegree
      by_cases hsingle : ∃ z ∈ F, ¬ ∃ x ∈ S z, x ≠ leaf
      · obtain ⟨z, hz, hsingle⟩ := hsingle
        refine ⟨z, hz, fun a hfa b hfb hza hzb hab => ?_⟩
        obtain ⟨x, hxz, hxa⟩ := (ha z hz a hfa hza.ne).mp hza
        obtain ⟨y, hyz, hyb⟩ := (ha z hz b hfb hzb.ne).mp hzb
        have hx : x = leaf := by
          by_contra hne
          exact hsingle ⟨x, hxz, hne⟩
        have hy : y = leaf := by
          by_contra hne
          exact hsingle ⟨y, hyz, hne⟩
        exact (ha a hfa b hfb hab).mpr ⟨leaf, hx ▸ hxa, hy ▸ hyb⟩
      · have hother : ∀ i ∈ F, ∃ x ∈ S i, x ≠ leaf := by
          intro i hi
          by_contra h
          exact hsingle ⟨i, hi, h⟩
        let T' := T.induce ({leaf}ᶜ : Set N)
        have ht : T'.IsTree :=
          ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hdegree,
            hT.isAcyclic.induce _⟩
        have hlt : Fintype.card ({leaf}ᶜ : Set N) < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (by simp : leaf ∉ ({leaf}ᶜ : Set N))
        refine ih _ hlt T' rfl ht G F hF (fun i => prunedSet (S i) leaf)
          (fun i hi => connected_prunedSet hadj hunique (hc i hi) (hother i hi)) ?_
        intro i hi j hj hij
        exact (ha i hi j hj hij).trans
          (prunedSet_inter_nonempty_iff hadj hunique (hc i hi) (hc j hj)
            (hother i hi) (hother j hj)).symm

variable {V : Type*} {G : SimpleGraph V}

/-- Any finite graph represented exactly by subtrees of a finite tree is chordal. -/
theorem SubtreeRepresentation.isChordal [Finite V] (R : SubtreeRepresentation G) :
    G.IsChordal := by
  obtain ⟨ord, hord⟩ := exists_isPEO_of_simplicial_in_finset (G := G) (by
    intro F hF
    exact subtree_family_simplicial_aux (Fintype.card R.Node) R.tree rfl R.isTree
      G F hF R.subtree (fun i _ => R.connected i) (fun i _ j _ hij => R.adjacency i j hij))
  exact hord.isChordal

variable {V : Type} {G : SimpleGraph V}

/-- Gavril's characterization: finite chordal graphs are exactly finite-tree subtree graphs. -/
theorem isChordal_iff_nonempty_subtreeRepresentation [Finite V] :
    G.IsChordal ↔ Nonempty (SubtreeRepresentation G) :=
  ⟨IsChordal.nonempty_subtreeRepresentation, fun ⟨R⟩ => R.isChordal⟩

end SimpleGraph
