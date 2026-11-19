/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.RamseyNumber
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Ramsey bounds

`SimpleGraph.RamseyBound n r s` says that every graph on `n` vertices contains an `r`-clique or an
independent set of size `s` (an `s`-clique of the complement). In the language of edge
two-colourings of `K_n` (red `G`, blue `Gᶜ`), every colouring has a red `K_r` or a blue `K_s`.

This is the graph-and-complement form of the two-colour Ramsey property of
`LeanPool.FiniteRamsey`, which is stated for edge labellings of the complete graph. The two agree
(`SimpleGraph.ramseyBound_iff_ramseyProperty`), so `R(r, s)` is FiniteRamsey's
`SimpleGraph.ramseyNumber ![r, s]`, the least `n` with `RamseyBound n r s`
(`SimpleGraph.ramseyBound_iff_ramseyNumber_le`). The basic algebra of the predicate (monotonicity,
symmetry, the trivial bounds and the Erdős–Szekeres recursion) is transported from FiniteRamsey
through this bridge. The graph form is what the reservoir arguments of this project use: it states
the bound for `G` and `Gᶜ` directly, and `SimpleGraph.RamseyBound.exists_isNClique_subset`
transfers it to any finite vertex set of size at least `n` in any graph.

## Main definitions

* `SimpleGraph.RamseyBound n r s`: every graph on `Fin n` has an `r`-clique or an independent
  `s`-set.

## Main statements

* `SimpleGraph.ramseyBound_iff_ramseyProperty`, `SimpleGraph.ramseyBound_iff_ramseyNumber_le`:
  the bridge to FiniteRamsey's `RamseyProperty` and `ramseyNumber`.
* `SimpleGraph.RamseyBound.exists_isNClique_subset`: the bound applies inside any finite set of at
  least `n` vertices of any graph.
* `SimpleGraph.RamseyBound.mono`, `SimpleGraph.RamseyBound.mono_sizes`,
  `SimpleGraph.RamseyBound.symm`: monotonicity in `n` and in `(r, s)`, and symmetry in `(r, s)`.
* `SimpleGraph.ramseyBound_zero_left`, `SimpleGraph.ramseyBound_one_left` and their mirror images:
  the trivial bounds.
* `SimpleGraph.RamseyBound.add`: the Erdős–Szekeres recursion
  `R(r + 1, s + 1) ≤ R(r, s + 1) + R(r + 1, s)`.
-/

@[expose] public section

open Finset

namespace SimpleGraph

/-- `RamseyBound n r s`: every graph on `n` vertices has an `r`-clique or an independent set of
size `s`. -/
def RamseyBound (n r s : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), (∃ t, G.IsNClique r t) ∨ ∃ t, Gᶜ.IsNClique s t

variable {V : Type*} {n m r s : ℕ}

/-! ### The bridge to FiniteRamsey -/

/-- The two-colouring of the complete graph whose red edges are those of `G`. -/
private def redColoring (G : SimpleGraph V) [DecidableRel G.Adj] : TwoColoring V :=
  EdgeLabeling.mk (fun x y _ => decide (G.Adj x y)) (by simp [G.adj_comm])

private theorem labelGraph_redColoring_true (G : SimpleGraph V) [DecidableRel G.Adj] :
    (redColoring G).labelGraph true = G := by
  ext x y
  simpa [redColoring, EdgeLabeling.get_mk, imp_false] using G.ne_of_adj

private theorem labelGraph_redColoring_false (G : SimpleGraph V) [DecidableRel G.Adj] :
    (redColoring G).labelGraph false = Gᶜ := by
  ext x y
  simp [redColoring, EdgeLabeling.get_mk]

/-- In a two-colouring, the blue graph is the complement of the red graph. -/
private theorem compl_labelGraph_true (C : TwoColoring V) :
    (C.labelGraph true)ᶜ = C.labelGraph false := by
  ext x y
  by_cases h : x = y
  · simp [h]
  · simp [h]

/-- **The bridge.** `RamseyBound` is FiniteRamsey's two-colour Ramsey property, with the red graph
of a colouring in place of `G` and the blue graph in place of `Gᶜ`. -/
theorem ramseyBound_iff_ramseyProperty : RamseyBound n r s ↔ RamseyProperty n r s := by
  classical
  refine ⟨fun h C => ?_, fun h G => ?_⟩
  · simpa only [compl_labelGraph_true] using h (C.labelGraph true)
  · simpa only [HasRedClique, HasBlueClique, RedClique, BlueClique, labelGraph_redColoring_true,
      labelGraph_redColoring_false] using h (redColoring G)

/-- **`R(r, s)` is the least Ramsey bound.** `RamseyBound n r s` holds exactly when FiniteRamsey's
Ramsey number `ramseyNumber ![r, s]` is at most `n`. -/
theorem ramseyBound_iff_ramseyNumber_le : RamseyBound n r s ↔ ramseyNumber ![r, s] ≤ n :=
  ramseyBound_iff_ramseyProperty.trans ramseyProperty_iff_ramseyNumber_le

/-- The Ramsey number is a Ramsey bound. -/
theorem ramseyBound_ramseyNumber (r s : ℕ) : RamseyBound (ramseyNumber ![r, s]) r s :=
  ramseyBound_iff_ramseyNumber_le.mpr le_rfl

/-! ### Transfer to arbitrary vertex sets -/

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

/-! ### Basic algebra, transported from FiniteRamsey -/

/-- More vertices: a Ramsey bound `n` for `(r, s)` gives every `m ≥ n`. -/
theorem RamseyBound.mono (h : RamseyBound n r s) (hnm : n ≤ m) : RamseyBound m r s :=
  ramseyBound_iff_ramseyProperty.mpr <|
    ramseyProperty_mono_vertices hnm (ramseyBound_iff_ramseyProperty.mp h)

/-- Smaller targets: a Ramsey bound for `(r, s)` is one for `(r', s')` when `r' ≤ r`, `s' ≤ s`. -/
theorem RamseyBound.mono_sizes {r' s' : ℕ} (h : RamseyBound n r s) (hr : r' ≤ r) (hs : s' ≤ s) :
    RamseyBound n r' s' :=
  ramseyBound_iff_ramseyProperty.mpr <|
    ramseyProperty_mono_cliqueSizes hr hs (ramseyBound_iff_ramseyProperty.mp h)

/-- Ramsey bounds are symmetric in the two colours. -/
theorem RamseyBound.symm (h : RamseyBound n r s) : RamseyBound n s r :=
  ramseyBound_iff_ramseyProperty.mpr <| ramseyProperty_swap (ramseyBound_iff_ramseyProperty.mp h)

/-- `RamseyBound n r s ↔ RamseyBound n s r`. -/
theorem ramseyBound_comm : RamseyBound n r s ↔ RamseyBound n s r := ⟨.symm, .symm⟩

/-- Every graph contains the empty clique. -/
theorem ramseyBound_zero_left (n s : ℕ) : RamseyBound n 0 s :=
  ramseyBound_iff_ramseyProperty.mpr (ramseyProperty_red_zero n s)

/-- Every graph, on any number `n` of vertices, has an independent `0`-set. -/
theorem ramseyBound_zero_right (n r : ℕ) : RamseyBound n r 0 :=
  ramseyBound_iff_ramseyProperty.mpr (ramseyProperty_blue_zero n r)

/-- Every nonempty graph contains a `1`-clique. -/
theorem ramseyBound_one_left (hn : 0 < n) (s : ℕ) : RamseyBound n 1 s :=
  (ramseyBound_iff_ramseyProperty.mpr (ramseyProperty_one_red s)).mono hn

/-- For `n ≥ 1`, every graph on `n` vertices has an independent `1`-set. -/
theorem ramseyBound_one_right (hn : 0 < n) (r : ℕ) : RamseyBound n r 1 :=
  (ramseyBound_one_left hn r).symm

/-- A Ramsey bound for positive `r` and `s` is positive: the graph with no vertices has neither a
`1`-clique nor an independent `1`-set. -/
theorem RamseyBound.pos (h : RamseyBound n r s) (hr : 0 < r) (hs : 0 < s) : 0 < n :=
  Nat.pos_of_ne_zero fun hn => not_ramseyProperty_zero_of_pos hr hs
    (hn ▸ ramseyBound_iff_ramseyProperty.mp h)

/-- **The Erdős–Szekeres recursion.** `R(r + 1, s + 1) ≤ R(r, s + 1) + R(r + 1, s)`. -/
theorem RamseyBound.add {a b : ℕ} (ha : RamseyBound a r (s + 1)) (hb : RamseyBound b (r + 1) s)
    (hab : 0 < a + b) : RamseyBound (a + b) (r + 1) (s + 1) :=
  ramseyBound_iff_ramseyProperty.mpr <| ramseyProperty_recursive a b r s hab
    (ramseyBound_iff_ramseyProperty.mp ha) (ramseyBound_iff_ramseyProperty.mp hb)

end SimpleGraph
