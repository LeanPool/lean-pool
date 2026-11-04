/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Tactic
public import LeanPool.ClassicalGraphColouring.Konig.Basic
public import LeanPool.ClassicalGraphColouring.Galvin.Orientation

/-!
# Galvin's theorem, the Dinitz problem and stable matchings

* `Galvin.gale_shapley`: **Gale–Shapley (1962).** Let `E` be a bipartite acceptability relation
  between finite sets `M` and `W`, and let every element rank its potential partners by an
  injective rank function (smaller rank = preferred). Then there is a *stable matching*: a
  matching `μ ⊆ E` such that every acceptable pair `(m, w)` outside `μ` is blocked, i.e. `m` is
  matched to someone it prefers to `w`, or `w` is matched to someone it prefers to `m`.
* `Galvin.galvin`: **Galvin (1995).** The list chromatic index of a finite bipartite graph equals
  its maximum degree: if every edge `e` of a bipartite graph `G` has a list of at least `Δ(G)`
  colours, there is a proper edge colouring (a colouring of Mathlib's `SimpleGraph.lineGraph`)
  choosing the colour of every edge from its list.
* `Galvin.dinitz`: **the Dinitz problem.** If every cell of an `n × n` array has a list of at least
  `n` symbols, one can choose a symbol from each list so that the symbols in every row and in every
  column are distinct.
-/

@[expose] public section

namespace Galvin

/-- **Gale–Shapley (1962).** For a bipartite acceptability relation `E` between finite sets `M`
and `W`, with strict preferences given by injective rank functions (`rm m w < rm m w'` means that
`m` prefers `w` to `w'`), there is a stable matching. -/
theorem gale_shapley {M W : Type*} [Finite M] [Finite W] (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∃ μ : M → W → Prop, (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m) := by
  exact exists_isStable rm rw hrm hrw _ E rfl

/-- **Galvin's theorem (1995).** If every edge of a finite bipartite graph `G` has a list of at
least `Δ(G)` colours, then `G` has a proper edge colouring choosing every colour from the list of
its edge. -/
theorem galvin {V Color : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Colorable 2) (lists : G.edgeSet → Finset Color)
    (hLists : ∀ e, G.maxDegree ≤ (lists e).card) :
    ∃ coloring : G.lineGraph.Coloring Color, ∀ e, coloring e ∈ lists e := by
  classical
  obtain ⟨c⟩ := hG
  obtain ⟨φ⟩ := Konig.lineGraph_colorable_of_colorable_two G ⟨c⟩
  exact exists_listColoring G.lineGraph (arc c φ) (hasKernels_arc c φ) lists
    fun e => lt_of_lt_of_le (card_arc_lt c φ e) (hLists e)

/-- **The Dinitz problem** (Galvin 1995). If every cell of an `n × n` array has a list of at least
`n` symbols, there is a choice of one symbol from each list with all symbols in each row distinct
and all symbols in each column distinct. -/
theorem dinitz {Symbol : Type*} (n : ℕ) (lists : Fin n → Fin n → Finset Symbol)
    (hLists : ∀ i j, n ≤ (lists i j).card) :
    ∃ f : Fin n → Fin n → Symbol, (∀ i j, f i j ∈ lists i j) ∧
      (∀ i j j', j ≠ j' → f i j ≠ f i j') ∧ (∀ i i' j, i ≠ i' → f i j ≠ f i' j) := by
  classical
  let G := completeBipartiteGraph (Fin n) (Fin n)
  have hG : G.Colorable 2 :=
    ⟨SimpleGraph.Coloring.mk (fun v => Sum.elim (fun _ => 0) (fun _ => 1) v) (by
      rintro (i | i) (j | j) h <;> simp [G] at h ⊢)⟩
  have hdeg : G.maxDegree ≤ n := by
    refine G.maxDegree_le_of_forall_degree_le n fun v => ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    rcases v with i | i
    · calc (G.neighborFinset (Sum.inl i)).card
            ≤ (Finset.univ.image (Sum.inr : Fin n → _)).card :=
            Finset.card_le_card fun w hw => by
              rcases w with j | j <;> simp [G] at hw ⊢
        _ ≤ n := Finset.card_image_le.trans (by simp)
    · calc (G.neighborFinset (Sum.inr i)).card
            ≤ (Finset.univ.image (Sum.inl : Fin n → _)).card :=
            Finset.card_le_card fun w hw => by
              rcases w with j | j <;> simp [G] at hw ⊢
        _ ≤ n := Finset.card_image_le.trans (by simp)
  let cell : Fin n ⊕ Fin n → Fin n ⊕ Fin n → Finset Symbol := fun a b =>
    match a, b with
    | Sum.inl i, Sum.inr j => lists i j
    | Sum.inr j, Sum.inl i => lists i j
    | _, _ => ∅
  have hcell : ∀ a b, cell a b = cell b a := by
    rintro (i | i) (j | j) <;> rfl
  let L : G.edgeSet → Finset Symbol := fun e => Sym2.lift ⟨cell, hcell⟩ e
  have hL : ∀ e, G.maxDegree ≤ (L e).card := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
    refine hdeg.trans ?_
    rcases a with i | i <;> rcases b with j | j <;>
      simp [G, L, cell, Sym2.lift_mk, hLists] at he ⊢
  obtain ⟨col, hcol⟩ := galvin G hG L hL
  have hadj : ∀ i j, G.Adj (Sum.inl i) (Sum.inr j) := fun i j => by simp [G]
  let edge : Fin n → Fin n → G.edgeSet := fun i j => ⟨s(Sum.inl i, Sum.inr j), hadj i j⟩
  refine ⟨fun i j => col (edge i j), fun i j => ?_, fun i j j' hjj => ?_, fun i i' j hii => ?_⟩
  · simpa [L, edge, cell, Sym2.lift_mk] using hcol (edge i j)
  · refine col.valid ?_
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨fun h => hjj ?_, Sum.inl i, by simp [edge], by simp [edge]⟩
    simpa [edge] using congrArg Subtype.val h
  · refine col.valid ?_
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨fun h => hii ?_, Sum.inr j, by simp [edge], by simp [edge]⟩
    simpa [edge] using congrArg Subtype.val h

end Galvin
