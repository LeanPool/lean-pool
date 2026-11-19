/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Reservoirs: a clique together with a pool of common neighbours

A *reservoir* of a simple graph `G` is a clique `spine` together with a finite set `pool`, disjoint
from it, all of whose vertices are adjacent to every vertex of the spine. This is the invariant
behind greedy clique-building arguments: the Erdős–Szekeres bound, book arguments, and the book
algorithm of Campos, Griffiths, Morris and Sahasrabudhe all repeatedly move a pool vertex onto the
spine and shrink the pool to that vertex's neighbours.

Any clique inside the pool glues to the spine, so a reservoir whose pool contains an `n`-clique
witnesses a `(#spine + n)`-clique of `G`. Applied to the complement `Gᶜ`, the same structure
describes independent sets, so the API is colour-symmetric for edge two-colourings (red `G`, blue
`Gᶜ`).

## Main definitions

* `SimpleGraph.Reservoir G`: a clique of `G` and a disjoint pool of common neighbours.
* `SimpleGraph.Reservoir.ofPool`: the reservoir with empty spine.
* `SimpleGraph.Reservoir.pivot`: move a pool vertex `v` onto the spine and keep only the pool
  vertices adjacent to `v`.
* `SimpleGraph.Reservoir.Reaches`: the reflexive-transitive closure of pivoting.

## Main statements

* `SimpleGraph.Reservoir.isNClique_union`: a clique in the pool glues to the spine.
* `SimpleGraph.Reservoir.card_pivot_pool`: pivoting at `v` loses exactly the pool vertices not
  adjacent to `v`.
* `SimpleGraph.Reservoir.exists_isNClique_of_card_nonadj_le`: **greedy clique**. If every pool
  vertex has at most `d` non-neighbours in the pool (counting itself) and `j * d < #pool`, the pool
  contains a `(j + 1)`-clique.
* `SimpleGraph.exists_isNClique_of_minDegree`: a graph on `n` vertices with minimum degree `δ` and
  `j * (n - δ) < n` contains a `(j + 1)`-clique. In particular `δ > (1 - 1/k) n` forces a
  `(k + 1)`-clique.

## Implementation notes

`pivot` filters the pool by `G.Adj v`. Since `G` is loopless, `v` itself leaves the pool.
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A *reservoir* of `G`: a clique `spine` and a disjoint finite `pool` all of whose vertices are
adjacent to every spine vertex. -/
structure Reservoir where
  /-- The clique built so far. -/
  spine : Finset V
  /-- The common neighbours of the spine still available. -/
  pool : Finset V
  isClique_spine : G.IsClique (spine : Set V)
  disjoint : Disjoint spine pool
  adj : ∀ x ∈ spine, ∀ y ∈ pool, G.Adj x y

namespace Reservoir

variable {G}

/-- A clique glued to a set of common neighbours is a clique. -/
theorem _root_.SimpleGraph.IsClique.union_of_forall_adj {s t : Set V} (hs : G.IsClique s)
    (ht : G.IsClique t) (h : ∀ x ∈ s, ∀ y ∈ t, G.Adj x y) : G.IsClique (s ∪ t) := by
  rintro x (hx | hx) y (hy | hy) hxy
  exacts [hs hx hy hxy, h x hx y hy, (h y hy x hx).symm, ht hx hy hxy]

/-- The reservoir with empty spine and pool `X`. -/
def ofPool (X : Finset V) : G.Reservoir where
  spine := ∅
  pool := X
  isClique_spine := by simp
  disjoint := disjoint_empty_left _
  adj := by simp

/-- The starting reservoir has an empty spine. -/
@[simp] theorem ofPool_spine (X : Finset V) : (ofPool (G := G) X).spine = ∅ := rfl

/-- The starting reservoir's pool is the given set. -/
@[simp] theorem ofPool_pool (X : Finset V) : (ofPool (G := G) X).pool = X := rfl

variable (R : G.Reservoir)

/-- Pool vertices are not on the spine. -/
theorem not_mem_spine_of_mem_pool {v : V} (hv : v ∈ R.pool) : v ∉ R.spine :=
  fun h => Finset.disjoint_left.mp R.disjoint h hv

/-- The spine is a clique of size `#spine`. -/
theorem isNClique_spine : G.IsNClique #R.spine R.spine := ⟨R.isClique_spine, rfl⟩

/-- **Gluing.** A clique `t` inside the pool extends the spine. -/
theorem isNClique_union [DecidableEq V] {t : Finset V} {n : ℕ} (ht : G.IsNClique n t)
    (hsub : t ⊆ R.pool) : G.IsNClique (#R.spine + n) (R.spine ∪ t) := by
  refine ⟨?_, ?_⟩
  · rw [coe_union]
    exact R.isClique_spine.union_of_forall_adj ht.isClique fun x hx y hy => R.adj x hx y (hsub hy)
  · rw [card_union_of_disjoint (R.disjoint.mono_right hsub), ht.card_eq]

/-- If `G` has no `(#spine + n)`-clique, the pool contains no `n`-clique. -/
theorem not_isNClique_of_cliqueFree {n : ℕ} (hG : G.CliqueFree (#R.spine + n)) {t : Finset V}
    (hsub : t ⊆ R.pool) : ¬G.IsNClique n t := by
  classical
  exact fun ht => hG _ (R.isNClique_union ht hsub)

/-- A reservoir witnesses a clique of every size up to `#spine + 1` when its pool is nonempty. -/
theorem exists_isNClique_succ (hR : R.pool.Nonempty) :
    ∃ s, G.IsNClique (#R.spine + 1) s := by
  classical
  obtain ⟨v, hv⟩ := hR
  exact ⟨_, R.isNClique_union (isNClique_singleton.mpr rfl) (singleton_subset_iff.mpr hv)⟩

section Pivot

variable [DecidableRel G.Adj] [DecidableEq V]

/-- Move the pool vertex `v` onto the spine and keep only the pool vertices adjacent to `v`. -/
def pivot (v : V) (hv : v ∈ R.pool) : G.Reservoir where
  spine := insert v R.spine
  pool := {w ∈ R.pool | G.Adj v w}
  isClique_spine := by
    rw [coe_insert]
    exact R.isClique_spine.insert fun b hb _ => (R.adj b hb v hv).symm
  disjoint := by
    rw [disjoint_insert_left]
    refine ⟨fun h => G.irrefl (mem_filter.mp h).2, ?_⟩
    exact R.disjoint.mono_right (filter_subset _ _)
  adj := by
    intro x hx y hy
    rw [mem_filter] at hy
    rcases mem_insert.mp hx with rfl | hx
    · exact hy.2
    · exact R.adj x hx y hy.1

variable {v : V} (hv : v ∈ R.pool)

/-- A pivot adds the pivot vertex to the spine. -/
@[simp] theorem pivot_spine : (R.pivot v hv).spine = insert v R.spine := rfl

/-- A pivot keeps the pivot's neighbours in the pool. -/
@[simp] theorem pivot_pool : (R.pivot v hv).pool = {w ∈ R.pool | G.Adj v w} := rfl

/-- A pivot grows the spine by one. -/
theorem card_pivot_spine : #(R.pivot v hv).spine = #R.spine + 1 :=
  card_insert_of_notMem (R.not_mem_spine_of_mem_pool hv)

/-- A pivot shrinks the pool. -/
theorem pivot_pool_subset : (R.pivot v hv).pool ⊆ R.pool := filter_subset _ _

/-- The pool after pivoting at `v` is the neighbourhood of `v` inside the pool. -/
theorem pivot_pool_eq_inter [Fintype (G.neighborSet v)] :
    (R.pivot v hv).pool = R.pool ∩ G.neighborFinset v := by
  ext w
  simp

/-- **Loss of a pivot.** Pivoting at `v` loses exactly the pool vertices not adjacent to `v`
(including `v` itself). -/
theorem card_pivot_pool : #(R.pivot v hv).pool + #{w ∈ R.pool | ¬G.Adj v w} = #R.pool :=
  card_filter_add_card_filter_not _

end Pivot

section Step

variable [DecidableEq V] [DecidableRel G.Adj]

/-- One pivot step. -/
def Step (R R' : G.Reservoir) : Prop :=
  ∃ v ∈ R.pool, R'.spine = insert v R.spine ∧ R'.pool = {w ∈ R.pool | G.Adj v w}

/-- `R` reaches `R'` by a finite sequence of pivots. -/
def Reaches : G.Reservoir → G.Reservoir → Prop := Relation.ReflTransGen Step

/-- A pivot is a step. -/
theorem step_pivot {v : V} (hv : v ∈ R.pool) : Step R (R.pivot v hv) := ⟨v, hv, rfl, rfl⟩

/-- A step grows the spine by one. -/
theorem Step.card_spine {R R' : G.Reservoir} (h : Step R R') : #R'.spine = #R.spine + 1 := by
  obtain ⟨v, hv, hs, -⟩ := h
  rw [hs, card_insert_of_notMem (R.not_mem_spine_of_mem_pool hv)]

/-- A step strictly shrinks the pool. -/
theorem Step.pool_ssubset {R R' : G.Reservoir} (h : Step R R') : R'.pool ⊂ R.pool := by
  obtain ⟨v, hv, -, hp⟩ := h
  rw [hp]
  exact (filter_ssubset).mpr ⟨v, hv, G.irrefl⟩

/-- Spines only grow along a run of steps. -/
theorem Reaches.spine_subset {R R' : G.Reservoir} (h : Reaches R R') : R.spine ⊆ R'.spine := by
  induction h with
  | refl => exact Subset.rfl
  | tail _ h ih =>
    obtain ⟨v, -, hs, -⟩ := h
    exact ih.trans (hs ▸ subset_insert _ _)

/-- Pools only shrink along a run of steps. -/
theorem Reaches.pool_subset {R R' : G.Reservoir} (h : Reaches R R') : R'.pool ⊆ R.pool := by
  induction h with
  | refl => exact Subset.rfl
  | tail _ h ih => exact h.pool_ssubset.subset.trans ih

/-- Along a run of pivots, the spine grows by the number of steps while the pool shrinks by at
least as much: `#spine + #pool` never increases. -/
theorem Reaches.card_add_card_le {R R' : G.Reservoir} (h : Reaches R R') :
    #R'.spine + #R'.pool ≤ #R.spine + #R.pool := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih =>
    have := card_lt_card h.pool_ssubset
    rw [h.card_spine]
    omega

end Step

/-! ### Greedy cliques -/

/-- **Greedy clique.** Suppose every vertex of the pool has at most `d` non-neighbours in the pool
(counting itself). If `j * d < #pool`, then `j` pivots are possible, so the pool contains a
`(j + 1)`-clique, and `G` contains a `(#spine + j + 1)`-clique. -/
theorem exists_isNClique_of_card_nonadj_le [DecidableRel G.Adj] {d : ℕ}
    (hd : ∀ v ∈ R.pool, #{w ∈ R.pool | ¬G.Adj v w} ≤ d) (j : ℕ) (hj : j * d < #R.pool) :
    ∃ s, G.IsNClique (#R.spine + (j + 1)) s := by
  classical
  induction j generalizing R with
  | zero =>
    exact R.exists_isNClique_succ (card_pos.mp (by simpa using hj))
  | succ j ih =>
    obtain ⟨v, hv⟩ := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hj)
    have hloss := R.card_pivot_pool hv
    have hv' := hd v hv
    have hsub := R.pivot_pool_subset hv
    have hd' : ∀ w ∈ (R.pivot v hv).pool,
        #{u ∈ (R.pivot v hv).pool | ¬G.Adj w u} ≤ d := fun w hw =>
      (card_le_card (filter_subset_filter _ hsub)).trans (hd w (hsub hw))
    have hj' : j * d < #(R.pivot v hv).pool := by
      rw [Nat.succ_mul] at hj
      generalize j * d = m at hj ⊢
      omega
    obtain ⟨s, hs⟩ := ih (R.pivot v hv) hd' hj'
    rw [card_pivot_spine] at hs
    exact ⟨s, by rwa [show #R.spine + (j + 1 + 1) = #R.spine + 1 + (j + 1) by omega]⟩

end Reservoir

/-- **Minimum degree forces cliques.** In a graph on `n` vertices with minimum degree `δ`, if
`j * (n - δ) < n` then there is a `(j + 1)`-clique. For `j = k` this says that
`δ > (1 - 1/k) n` forces a `(k + 1)`-clique. -/
theorem exists_isNClique_of_minDegree [Fintype V] [DecidableRel G.Adj] {j : ℕ}
    (hj : j * (Fintype.card V - G.minDegree) < Fintype.card V) :
    ∃ s, G.IsNClique (j + 1) s := by
  have hd : ∀ v ∈ (Reservoir.ofPool (G := G) univ).pool,
      #{w ∈ (Reservoir.ofPool (G := G) univ).pool | ¬G.Adj v w} ≤
        Fintype.card V - G.minDegree := by
    intro v _
    have hdeg : #{w ∈ (univ : Finset V) | G.Adj v w} = G.degree v := by
      rw [← card_neighborFinset_eq_degree]
      congr 1
      ext; simp
    have h := card_filter_add_card_filter_not (s := (univ : Finset V)) (G.Adj v)
    rw [hdeg, card_univ] at h
    have := G.minDegree_le_degree v
    rw [Reservoir.ofPool_pool]
    omega
  simpa using (Reservoir.ofPool (G := G) univ).exists_isNClique_of_card_nonadj_le hd j
    (by simpa using hj)

end SimpleGraph
