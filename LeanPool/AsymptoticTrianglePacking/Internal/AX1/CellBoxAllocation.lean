/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **box (interval-cell) allocation** of the coarse-cell route, and why it is
infeasible at general densities

The coarse-cell route to `Nibble.AX1.BlockCoverResidualCoupled` needs, for every cluster pair, an
allocation of the cell grid of the pair among the cluster triples through it, coherent along the
three cluster axes.  `Nibble.CoarseCellLatinFill` supplies the *filling* of one **product box**
`I_S × I_T × I_Y` (a set of coarse cells per cluster) with no waste; what is left is the
**allocation** of the boxes.

Two copies of cluster triples that share the cluster pair `{S,T}` occupy the rectangles
`I_S × I_T` and `I_S' × I_T'` of the `(S,T)` cell grid, and these must be disjoint, i.e.

    Disjoint I_S I_S' ∨ Disjoint I_T I_T'                      (`Nibble.AX1.BoxCompat`)

The shape of a box is *forced* by the densities: with `p`, `q`, `s` blocks per coarse cell of
`S`, `T`, `Y` (so `p : q : s = 1/d(T,Y) : 1/d(S,Y) : 1/d(S,T)`, the block sizes being
`τ·(opposite density)`), a box occupies `q·s` cells of `S` and `p·s` cells of `T`, so the aspect
ratio of the `(S,T)` rectangle is `q : p = d(T,Y) : d(S,Y)` — it is dictated by the *other* two
pairs, and ranges over `[δ, 1/δ]`.

`Nibble.AX1.box_allocation_infeasible` is the resulting obstruction in its sharpest form: with `P`
coarse cells per cluster, a triple `(S,T,Y)` with `d(T,Y) = 1`, `d(S,Y) = 1/P` and a triple
`(S,T,Y')` with `d(T,Y') = 1/P`, `d(S,Y') = 1` demand rectangles of shapes `P × 1` and `1 × P` in
the `(S,T)` grid; their total area `2P` is a vanishing fraction of the capacity `P²`, yet no
placement is compatible.  Interval (box) cells therefore cannot realise the LP allocation at
general densities, whatever the accuracy asked for — this is the "over-determination" the shape
gate `Nibble.CoarseCellShapeGate` describes, in allocation form.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.NormNum

/-! # CellBoxAllocation -/

@[expose] public section

open Finset

namespace Nibble.AX1

/-- **Compatibility of two boxes in the grid of one cluster pair**: the two rectangles
`I ×ˢ J` and `I' ×ˢ J'` are disjoint exactly when the boxes are disjoint in one of the two
clusters. -/
def BoxCompat {P : ℕ} (I I' J J' : Finset (Fin P)) : Prop := Disjoint I I' ∨ Disjoint J J'

theorem boxCompat_iff_disjoint_product {P : ℕ} (I I' J J' : Finset (Fin P))
    (_hI : I.Nonempty) (_hI' : I'.Nonempty) (_hJ : J.Nonempty) (_hJ' : J'.Nonempty) :
    BoxCompat I I' J J' ↔ Disjoint (I ×ˢ J) (I' ×ˢ J') := by
  constructor
  · rintro (h | h)
    · rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ hx hy
      exact (Finset.disjoint_left.mp h) (Finset.mem_product.mp hx).1
        (Finset.mem_product.mp hy).1
    · rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ hx hy
      exact (Finset.disjoint_left.mp h) (Finset.mem_product.mp hx).2
        (Finset.mem_product.mp hy).2
  · intro h
    by_contra hc
    simp only [BoxCompat, not_or] at hc
    obtain ⟨h1, h2⟩ := hc
    rw [Finset.not_disjoint_iff] at h1 h2
    obtain ⟨x, hx, hx'⟩ := h1
    obtain ⟨y, hy, hy'⟩ := h2
    refine (Finset.disjoint_left.mp h) (a := (x, y)) (Finset.mem_product.mpr ⟨hx, hy⟩) ?_
    exact Finset.mem_product.mpr ⟨hx', hy'⟩

/-- **The box allocation is infeasible at general densities.**  A `P × 1` box and a `1 × P` box in
the same cluster-pair grid — the shapes forced by two cluster triples through the pair whose two
other densities are opposite extremes — cannot be placed compatibly, although their total area
`2·P` is a `2/P` fraction of the capacity `P²`. -/
theorem box_allocation_infeasible {P : ℕ} (I I' J J' : Finset (Fin P))
    (hI : #I = P) (hJ : #J = 1) (hI' : #I' = 1) (hJ' : #J' = P) :
    ¬ BoxCompat I I' J J' := by
  have hcard : Fintype.card (Fin P) = P := Fintype.card_fin P
  have hIu : I = univ := by
    apply Finset.eq_univ_of_card
    rw [hI, hcard]
  have hJ'u : J' = univ := by
    apply Finset.eq_univ_of_card
    rw [hJ', hcard]
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [hI']; norm_num : 0 < #I')
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [hJ]; norm_num : 0 < #J)
  rintro (h | h)
  · exact (Finset.disjoint_left.mp h) (hIu ▸ Finset.mem_univ x) hx
  · exact (Finset.disjoint_left.mp h) hy (hJ'u ▸ Finset.mem_univ y)

/-! ### Axiom check -/

section AxCheck




end AxCheck

end Nibble.AX1
