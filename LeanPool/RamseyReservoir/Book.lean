/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.RamseyReservoir.Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Books

A *book* with spine size `m` and `t` pages is an `m`-clique together with `t` further vertices
adjacent to all of it; that is, a reservoir with an `m`-vertex spine and `t` pool vertices. Books
with a two-vertex spine are edges with many common neighbours, and they are the basic objects of
the book method in Ramsey theory.

This file proves the double-counting identity linking codegrees and triangles, the resulting
averaging lower bounds for books, and the Ramsey forcing principle for books: a book whose pool is
large enough for the missing clique sizes yields a red or a blue clique.

## Main definitions

* `SimpleGraph.ContainsBook m t`: `G` has a book with an `m`-vertex spine and at least `t` pages.

## Main statements

* `SimpleGraph.containsBook_two_iff`: a book with a two-vertex spine is an edge whose endpoints
  have at least `t` common neighbours.
* `SimpleGraph.sum_card_commonNeighbors_eq`: summing the codegree over ordered adjacent pairs
  counts each triangle six times.
* `SimpleGraph.containsBook_two_of_mul_card_edgeFinset_le`: if `t · e ≤ 3 · T` (with `e` edges
  and `T` triangles), some edge spans a book with `t` pages.
* `SimpleGraph.exists_adj_four_mul_card_edgeFinset_le`: some edge `uv` has
  `4e ≤ n (codeg(u, v) + n)`, that is a book with at least `4e/n - n` pages. In particular
  `n² < 4e` forces a triangle (Mantel's theorem).
* `SimpleGraph.Reservoir.exists_of_ramseyBound`, `SimpleGraph.ContainsBook.not_cliqueFree_or`:
  **book forcing**. A book whose pool is large enough for the remaining clique sizes yields an
  `r`-clique of `G` or an `s`-clique of `Gᶜ`.
* `SimpleGraph.not_cliqueFree_or_of_mul_card_edgeFinset_le`: triangle density forces, in a graph
  with no `(r + 2)`-clique, an independent set of size `s` whenever `RamseyBound t r s`.

## Implementation notes

Codegrees are Mathlib's `Fintype.card (G.commonNeighbors u v)`.

## References

* [W. Mantel, *Vraagstuk XXVIII*][Mantel1907]
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Books and reservoirs -/

/-- `G` has a book with an `m`-vertex spine and at least `t` pages: an `m`-clique and `t` further
vertices adjacent to all of it. -/
def ContainsBook (G : SimpleGraph V) (m t : ℕ) : Prop :=
  ∃ R : G.Reservoir, #R.spine = m ∧ t ≤ #R.pool

/-- Fewer pages: a book with `t` pages has `t' ≤ t` pages. -/
theorem ContainsBook.mono {m t t' : ℕ} (h : G.ContainsBook m t) (ht : t' ≤ t) :
    G.ContainsBook m t' :=
  let ⟨R, hm, hp⟩ := h
  ⟨R, hm, ht.trans hp⟩

/-- A shorter spine: a book with an `m`-vertex spine has an `m'`-vertex spine for `m' ≤ m`, with
the same pages. -/
theorem ContainsBook.mono_spine {m m' t : ℕ} (h : G.ContainsBook m t) (hm : m' ≤ m) :
    G.ContainsBook m' t := by
  obtain ⟨R, rfl, hp⟩ := h
  obtain ⟨s, hs, rfl⟩ := exists_subset_card_eq hm
  exact ⟨⟨s, R.pool, R.isClique_spine.subset (by simpa using hs), R.disjoint.mono_left hs,
    fun x hx y hy => R.adj x (hs hx) y hy⟩, rfl, hp⟩

/-- A book of `G` is a book of every supergraph of `G`. -/
theorem ContainsBook.mono_graph {H : SimpleGraph V} {m t : ℕ} (h : G.ContainsBook m t)
    (hGH : G ≤ H) : H.ContainsBook m t :=
  let ⟨R, hm, hp⟩ := h
  ⟨⟨R.spine, R.pool, R.isClique_spine.mono hGH, R.disjoint, fun x hx y hy => hGH (R.adj x hx y hy)⟩,
    hm, hp⟩

/-- A large enough pool yields a red or blue clique. -/
theorem Reservoir.exists_of_ramseyBound (R : G.Reservoir) {n r s : ℕ}
    (h : RamseyBound n (r - #R.spine) s) (hn : n ≤ #R.pool) :
    (∃ t, G.IsNClique r t) ∨ ∃ t, Gᶜ.IsNClique s t := by
  classical
  let S : G.Bireservoir := ⟨R.spine, ∅, R.pool, R.isClique_spine, by simp, R.disjoint,
    disjoint_empty_left _, R.adj, by simp⟩
  exact S.exists_of_ramseyBound (by simpa [S] using h) hn

/-- **Book forcing.** If `G` has a book with an `m`-vertex spine and `n` pages, and
`RamseyBound n (r - m) s`, then `G` has an `r`-clique or `Gᶜ` has an `s`-clique. -/
theorem ContainsBook.not_cliqueFree_or {m n r s : ℕ} (hB : G.ContainsBook m n)
    (h : RamseyBound n (r - m) s) : ¬G.CliqueFree r ∨ ¬Gᶜ.CliqueFree s := by
  obtain ⟨R, rfl, hn⟩ := hB
  rcases R.exists_of_ramseyBound h hn with ⟨t, ht⟩ | ⟨t, ht⟩
  exacts [.inl ht.not_cliqueFree, .inr ht.not_cliqueFree]

variable [Fintype V] [DecidableRel G.Adj]

/-- The codegree as the size of a filtered `Finset`. -/
theorem card_commonNeighbors_eq_card_filter (u v : V) :
    Fintype.card (G.commonNeighbors u v) = #{w | G.Adj u w ∧ G.Adj v w} := by
  rw [← Set.toFinset_card]
  congr 1
  ext w
  simp [mem_commonNeighbors]

/-- A book with a two-vertex spine is an edge with at least `t` common neighbours. -/
theorem containsBook_two_iff {t : ℕ} :
    G.ContainsBook 2 t ↔ ∃ u v, G.Adj u v ∧ t ≤ Fintype.card (G.commonNeighbors u v) := by
  classical
  constructor
  · rintro ⟨R, hR, ht⟩
    obtain ⟨u, v, huv, hs⟩ := card_eq_two.mp hR
    have hu : u ∈ R.spine := by simp [hs]
    have hv : v ∈ R.spine := by simp [hs]
    refine ⟨u, v, R.isClique_spine hu hv huv, ht.trans ?_⟩
    rw [card_commonNeighbors_eq_card_filter]
    exact card_le_card fun w hw => mem_filter.mpr ⟨mem_univ _, R.adj u hu w hw, R.adj v hv w hw⟩
  · rintro ⟨u, v, huv, ht⟩
    refine ⟨⟨{u, v}, {w | G.Adj u w ∧ G.Adj v w}, ?_, ?_, ?_⟩, card_pair huv.ne, ?_⟩
    · rw [coe_pair]
      exact isClique_pair.mpr fun _ => huv
    · rw [Finset.disjoint_left]
      intro w hw hw'
      rw [mem_filter] at hw'
      rcases mem_insert.mp hw with rfl | hw
      · exact G.irrefl hw'.2.1
      · rw [mem_singleton.mp hw] at hw'
        exact G.irrefl hw'.2.2
    · intro x hx y hy
      rw [mem_filter] at hy
      rcases mem_insert.mp hx with rfl | hx
      · exact hy.2.1
      · rw [mem_singleton.mp hx]
        exact hy.2.2
    · rwa [← card_commonNeighbors_eq_card_filter]

/-! ### Codegrees and triangles -/

/-- The ordered triangles of `G`: triples of pairwise adjacent vertices. -/
def orderedTriangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V × V) :=
  {x | G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2}

/-- Summing codegrees over ordered adjacent pairs counts ordered triangles. -/
theorem sum_card_commonNeighbors_eq_card_orderedTriangles :
    ∑ u, ∑ v ∈ G.neighborFinset u, Fintype.card (G.commonNeighbors u v) =
      #G.orderedTriangles := by
  simp only [orderedTriangles, card_filter, Fintype.sum_prod_type,
    card_commonNeighbors_eq_card_filter]
  refine sum_congr rfl fun u _ => ?_
  rw [neighborFinset_eq_filter, sum_filter]
  refine sum_congr rfl fun v _ => ?_
  split_ifs with h <;> simp [h]

omit [Fintype V] in
/-- A `3`-set has six ordered triples of distinct elements. -/
private theorem card_distinct_triples [DecidableEq V] (s : Finset V) :
    #{x ∈ s ×ˢ s ×ˢ s | x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2} =
      #s * ((#s - 1) * (#s - 1) - (#s - 1)) := by
  rw [card_filter, sum_product, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun x hx => ?_
  rw [← card_erase_of_mem hx, ← offDiag_card, ← card_filter]
  congr 1
  ext ⟨y, z⟩
  simp only [mem_filter, mem_product, mem_offDiag, mem_erase]
  constructor
  · rintro ⟨⟨hy, hz⟩, hxy, hxz, hyz⟩
    exact ⟨⟨Ne.symm hxy, hy⟩, ⟨Ne.symm hxz, hz⟩, hyz⟩
  · rintro ⟨⟨hxy, hy⟩, ⟨hxz, hz⟩, hyz⟩
    exact ⟨⟨hy, hz⟩, Ne.symm hxy, Ne.symm hxz, hyz⟩

/-- Each triangle gives six ordered triangles. -/
theorem card_orderedTriangles [DecidableEq V] :
    #G.orderedTriangles = 6 * #(G.cliqueFinset 3) := by
  rw [card_eq_sum_card_fiberwise (f := fun x : V × V × V => ({x.1, x.2.1, x.2.2} : Finset V))
    (t := G.cliqueFinset 3)]
  · rw [mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun s hs => ?_
    have hs := mem_cliqueFinset_iff.mp hs
    have h6 := card_distinct_triples s
    rw [hs.card_eq, show 3 * ((3 - 1) * (3 - 1) - (3 - 1)) = 6 from rfl] at h6
    rw [← h6]
    congr 1
    ext ⟨x, y, z⟩
    simp only [orderedTriangles, mem_filter, mem_univ, true_and, mem_product]
    constructor
    · rintro ⟨⟨hxy, hxz, hyz⟩, rfl⟩
      exact ⟨⟨by simp, by simp, by simp⟩, hxy.ne, hxz.ne, hyz.ne⟩
    · rintro ⟨⟨hx, hy, hz⟩, hxy, hxz, hyz⟩
      refine ⟨⟨hs.isClique hx hy hxy, hs.isClique hx hz hxz, hs.isClique hy hz hyz⟩, ?_⟩
      refine eq_of_subset_of_card_le (by simp [insert_subset_iff, hx, hy, hz]) ?_
      rw [hs.card_eq, card_insert_of_notMem (by simp [hxy, hxz]),
        card_pair hyz]
  · intro x hx
    have hx := mem_coe.mp hx
    simp only [orderedTriangles, mem_filter, mem_univ, true_and] at hx
    change {x.1, x.2.1, x.2.2} ∈ (G.cliqueFinset 3 : Set (Finset V))
    rw [mem_coe, mem_cliqueFinset_iff, is3Clique_iff]
    exact ⟨_, _, _, hx.1, hx.2.1, hx.2.2, rfl⟩

/-- **Codegrees count triangles.** Summing the codegree over ordered adjacent pairs counts each
triangle six times. -/
theorem sum_card_commonNeighbors_eq [DecidableEq V] :
    ∑ u, ∑ v ∈ G.neighborFinset u, Fintype.card (G.commonNeighbors u v) =
      6 * #(G.cliqueFinset 3) := by
  rw [sum_card_commonNeighbors_eq_card_orderedTriangles, card_orderedTriangles]

/-- The number of ordered adjacent pairs is twice the number of edges. -/
private theorem sum_card_neighborFinset : ∑ u, #(G.neighborFinset u) = 2 * #G.edgeFinset := by
  simp_rw [card_neighborFinset_eq_degree]
  exact G.sum_degrees_eq_twice_card_edges

/-- If every ordered adjacent pair satisfies `t ≤ f u v`, summing gives `t · 2e`; contrapositively,
a sum of at least `t · 2e` over a nonempty edge set has an adjacent pair with `t ≤ f u v`. -/
private theorem exists_adj_le_of_le_sum (f : V → V → ℕ) {t : ℕ}
    (hE : G.edgeFinset.Nonempty)
    (h : t * (2 * #G.edgeFinset) ≤ ∑ u, ∑ v ∈ G.neighborFinset u, f u v) :
    ∃ u v, G.Adj u v ∧ t ≤ f u v := by
  by_contra! hlt
  have hsum : ∑ u, ∑ v ∈ G.neighborFinset u, f u v < ∑ u, ∑ v ∈ G.neighborFinset u, t := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ a b =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      refine sum_lt_sum (fun u _ => sum_le_sum fun v hv => (hlt u v ?_).le) ⟨a, mem_univ _,
        sum_lt_sum (fun v hv => (hlt a v ?_).le) ⟨b, by simpa using he, hlt a b he⟩⟩
      · simpa using hv
      · simpa using hv
  simp_rw [sum_const, smul_eq_mul, ← sum_mul, sum_card_neighborFinset] at hsum
  rw [mul_comm] at h
  omega

/-- **Books from triangles.** If `t · e ≤ 3 · T`, where `e` is the number of edges and `T` the
number of triangles, then some edge spans a book with `t` pages. -/
theorem containsBook_two_of_mul_card_edgeFinset_le [DecidableEq V] {t : ℕ}
    (hE : G.edgeFinset.Nonempty) (h : t * #G.edgeFinset ≤ 3 * #(G.cliqueFinset 3)) :
    G.ContainsBook 2 t := by
  refine containsBook_two_iff.mpr (exists_adj_le_of_le_sum _ hE ?_)
  rw [sum_card_commonNeighbors_eq]
  linarith

/-- Two vertices have at least `deg u + deg v - n` common neighbours. -/
theorem degree_add_degree_le_card_commonNeighbors_add (u v : V) :
    G.degree u + G.degree v ≤ Fintype.card (G.commonNeighbors u v) + Fintype.card V := by
  classical
  have h1 := card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have h2 : #(G.neighborFinset u ∪ G.neighborFinset v) ≤ Fintype.card V := card_le_univ _
  have h3 : G.neighborFinset u ∩ G.neighborFinset v =
      ({w | G.Adj u w ∧ G.Adj v w} : Finset V) := by
    ext; simp
  rw [card_commonNeighbors_eq_card_filter, ← card_neighborFinset_eq_degree,
    ← card_neighborFinset_eq_degree, ← h3]
  omega

/-- Summing a function of the second endpoint over ordered adjacent pairs weights it by degree. -/
private theorem sum_sum_neighborFinset (f : V → ℕ) :
    ∑ u, ∑ v ∈ G.neighborFinset u, f v = ∑ v, G.degree v * f v := by
  simp_rw [neighborFinset_eq_filter, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [← sum_filter, sum_const, smul_eq_mul, ← card_neighborFinset_eq_degree,
    neighborFinset_eq_filter]
  congr 2
  ext
  simp [G.adj_comm]

/-- **Books from edge density.** If `G` has `e > 0` edges on `n` vertices, some edge `uv` satisfies
`4e ≤ n · (codeg(u, v) + n)`: it spans a book with at least `4e/n - n` pages. -/
theorem exists_adj_four_mul_card_edgeFinset_le (hE : G.edgeFinset.Nonempty) :
    ∃ u v, G.Adj u v ∧
      4 * #G.edgeFinset ≤ Fintype.card V * (Fintype.card (G.commonNeighbors u v) +
        Fintype.card V) := by
  set n := Fintype.card V
  set e := #G.edgeFinset
  -- Some ordered adjacent pair has `4e ≤ n (deg u + deg v)`.
  have hsq : (2 * e) ^ 2 ≤ n * ∑ u, G.degree u ^ 2 := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    simpa using sq_sum_le_card_mul_sum_sq (s := univ) (f := fun u => G.degree u)
  have hpair : ∑ u, ∑ v ∈ G.neighborFinset u, (G.degree u + G.degree v) =
      2 * ∑ u, G.degree u ^ 2 := by
    simp_rw [sum_add_distrib, sum_sum_neighborFinset, sum_const, smul_eq_mul,
      card_neighborFinset_eq_degree, ← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun u _ => by ring
  obtain ⟨u, v, huv, h⟩ := exists_adj_le_of_le_sum (t := 4 * e)
    (fun u v => n * (G.degree u + G.degree v)) hE (by
      simp_rw [← mul_sum]
      rw [hpair]
      change 4 * e * (2 * e) ≤ _
      nlinarith)
  exact ⟨u, v, huv, h.trans (Nat.mul_le_mul_left n
    (degree_add_degree_le_card_commonNeighbors_add (G := G) u v))⟩

/-- **Mantel's theorem, book form.** A graph on `n` vertices with more than `n² / 4` edges has an
edge whose endpoints have a common neighbour. -/
theorem exists_adj_card_commonNeighbors_pos (h : Fintype.card V ^ 2 < 4 * #G.edgeFinset) :
    ∃ u v, G.Adj u v ∧ 0 < Fintype.card (G.commonNeighbors u v) := by
  have hE : G.edgeFinset.Nonempty := card_pos.mp (by omega)
  obtain ⟨u, v, huv, h'⟩ := exists_adj_four_mul_card_edgeFinset_le hE
  refine ⟨u, v, huv, Nat.pos_of_ne_zero fun h0 => ?_⟩
  rw [h0, zero_add, ← sq] at h'
  omega

/-- **Book forcing from triangle density.** If `G` has no `(r + 2)`-clique, at least one edge, and
`t · e ≤ 3 · T` (with `e` edges and `T` triangles), then `RamseyBound t r s` gives an independent
set of size `s`. -/
theorem not_cliqueFree_or_of_mul_card_edgeFinset_le [DecidableEq V] {t r s : ℕ}
    (hE : G.edgeFinset.Nonempty) (h : t * #G.edgeFinset ≤ 3 * #(G.cliqueFinset 3))
    (hR : RamseyBound t r s) : ¬G.CliqueFree (r + 2) ∨ ¬Gᶜ.CliqueFree s :=
  (containsBook_two_of_mul_card_edgeFinset_le hE h).not_cliqueFree_or (by simpa using hR)

end SimpleGraph
