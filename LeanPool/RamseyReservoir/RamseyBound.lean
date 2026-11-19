/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Ramsey bounds

`SimpleGraph.RamseyBound n r s` says that every graph on `n` vertices contains an `r`-clique or an
independent set of size `s` (an `s`-clique of the complement). In the language of edge
two-colourings of `K_n` (red `G`, blue `Gᶜ`), every colouring has a red `K_r` or a blue `K_s`, so
the Ramsey number `R(r, s)` is the least `n` with `RamseyBound n r s`.

The predicate is stated on `Fin n`; `SimpleGraph.RamseyBound.exists_isNClique_subset` transfers it
to any finite vertex set of size at least `n` in any graph. Working with bounds rather than with
the Ramsey number itself keeps this file independent of any particular definition of `R(r, s)`.

## Main definitions

* `SimpleGraph.RamseyBound n r s`: every graph on `Fin n` has an `r`-clique or an independent
  `s`-set.

## Main statements

* `SimpleGraph.RamseyBound.exists_isNClique_subset`: the bound applies inside any finite set of at
  least `n` vertices of any graph.
* `SimpleGraph.RamseyBound.mono`, `SimpleGraph.RamseyBound.symm`: monotonicity in `n` and symmetry
  in `(r, s)`.
* `SimpleGraph.ramseyBound_zero_left`, `SimpleGraph.ramseyBound_one_left` and their mirror images:
  the trivial bounds.
-/

@[expose] public section

open Finset

namespace SimpleGraph

/-- `RamseyBound n r s`: every graph on `n` vertices has an `r`-clique or an independent set of
size `s`. -/
def RamseyBound (n r s : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), (∃ t, G.IsNClique r t) ∨ ∃ t, Gᶜ.IsNClique s t

variable {V : Type*} {n m r s : ℕ}

/-- The complement of a pulled-back graph along an injection is the pulled-back complement. -/
private theorem compl_comap_embedding (G : SimpleGraph V) (f : Fin n ↪ V) :
    (G.comap f)ᶜ = Gᶜ.comap f := by
  ext a b
  simp [f.injective.ne_iff]

/-- A clique of a pulled-back graph pushes forward to a clique of the same size. -/
private theorem isNClique_map_of_comap {G : SimpleGraph V} {f : Fin n ↪ V} {k : ℕ}
    {t : Finset (Fin n)} (ht : (G.comap f).IsNClique k t) : G.IsNClique k (t.map f) := by
  have := ht.map (f := f)
  exact this.mono (map_comap_le _ _)

/-- **Transfer.** If `RamseyBound n r s`, then every set of at least `n` vertices of any graph
contains an `r`-clique or an independent `s`-set. -/
theorem RamseyBound.exists_isNClique_subset (h : RamseyBound n r s) (G : SimpleGraph V)
    {X : Finset V} (hX : n ≤ #X) :
    (∃ t ⊆ X, G.IsNClique r t) ∨ ∃ t ⊆ X, Gᶜ.IsNClique s t := by
  classical
  obtain ⟨Y, hYX, hY⟩ := exists_subset_card_eq hX
  let e : Fin n ↪ V := ⟨fun i => (Y.equivFin.symm (Fin.cast hY.symm i) : V),
    fun i j hij => by simpa using Subtype.ext hij⟩
  have he : ∀ t : Finset (Fin n), t.map e ⊆ X := fun t x hx => by
    obtain ⟨i, -, rfl⟩ := mem_map.mp hx
    exact hYX (Y.equivFin.symm _).2
  rcases h (G.comap e) with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact .inl ⟨_, he t, isNClique_map_of_comap ht⟩
  · rw [compl_comap_embedding] at ht
    exact .inr ⟨_, he t, isNClique_map_of_comap ht⟩

/-- The graph form of the transfer: a graph on at least `n` vertices contains an `r`-clique or an
independent `s`-set. -/
theorem RamseyBound.not_cliqueFree_or [Fintype V] (h : RamseyBound n r s) (G : SimpleGraph V)
    (hV : n ≤ Fintype.card V) : ¬G.CliqueFree r ∨ ¬Gᶜ.CliqueFree s := by
  rcases h.exists_isNClique_subset G (X := univ) (by simpa using hV) with ⟨t, -, ht⟩ | ⟨t, -, ht⟩
  exacts [.inl ht.not_cliqueFree, .inr ht.not_cliqueFree]

/-- More vertices: a Ramsey bound `n` for `(r, s)` gives every `m ≥ n`. -/
theorem RamseyBound.mono (h : RamseyBound n r s) (hnm : n ≤ m) : RamseyBound m r s := fun G => by
  rcases h.exists_isNClique_subset G (X := univ) (by simpa using hnm) with
    ⟨t, -, ht⟩ | ⟨t, -, ht⟩
  exacts [.inl ⟨t, ht⟩, .inr ⟨t, ht⟩]

/-- Ramsey bounds are symmetric in the two colours. -/
theorem RamseyBound.symm (h : RamseyBound n r s) : RamseyBound n s r := fun G => by
  simpa using (h Gᶜ).symm

/-- `RamseyBound n r s ↔ RamseyBound n s r`. -/
theorem ramseyBound_comm : RamseyBound n r s ↔ RamseyBound n s r := ⟨.symm, .symm⟩

/-- Every graph contains the empty clique. -/
theorem ramseyBound_zero_left (n s : ℕ) : RamseyBound n 0 s := fun _ => .inl ⟨∅, by simp⟩

/-- Every graph, on any number `n` of vertices, has an independent `0`-set. -/
theorem ramseyBound_zero_right (n r : ℕ) : RamseyBound n r 0 := (ramseyBound_zero_left n r).symm

/-- Every nonempty graph contains a `1`-clique. -/
theorem ramseyBound_one_left (hn : 0 < n) (s : ℕ) : RamseyBound n 1 s := fun _ =>
  .inl ⟨{⟨0, hn⟩}, by simp⟩

/-- For `n ≥ 1`, every graph on `n` vertices has an independent `1`-set. -/
theorem ramseyBound_one_right (hn : 0 < n) (r : ℕ) : RamseyBound n r 1 :=
  (ramseyBound_one_left hn r).symm

/-- A Ramsey bound for positive `r` and `s` is positive: the graph with no vertices has neither a
`1`-clique nor an independent `1`-set. -/
theorem RamseyBound.pos (h : RamseyBound n r s) (hr : 0 < r) (hs : 0 < s) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases h ⊥ with ⟨t, ht⟩ | ⟨t, ht⟩ <;>
    · have := ht.card_eq
      rw [Subsingleton.elim t ∅, card_empty] at this
      omega
  · exact hn

end SimpleGraph
