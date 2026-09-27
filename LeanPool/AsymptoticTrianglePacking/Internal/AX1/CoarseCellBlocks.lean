/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — coarse cells, the blocks they carry, and the disjointness engine

The geometric layer of the coarse-cell route to `Nibble.AX1.BlockCoverResidualCoupled`.  A cluster
`S` is cut into coarse cells `Nibble.AX1.blockOf S l i` of length `l`; a member of the block family
occupies a *set* `I` of coarse cells of its cluster (the box of `Nibble.AX1.BoxAllocationResidual`)
and its actual vertex block is an arbitrary subset of the prescribed size of the union of those
cells.

* `Nibble.AX1.cellUnion` — the union of the cells of an index set, its size and its subset and
  disjointness properties;
* `Nibble.AX1.takeSub` — a chosen subset of a prescribed size;
* `Nibble.AX1.cellBlock` — the vertex block of a member: the prescribed number of vertices inside
  the union of its cells;
* `Nibble.AX1.tripleRect_disjoint_of_shared_pairs` — **the disjointness engine**: two members whose
  three blocks lie in three clusters of a partition have disjoint vertex-pair rectangles as soon as,
  for every cluster pair they share, one of the two blocks of the pair is disjoint from the
  corresponding block of the other member.  This is what turns the cell-rectangle disjointness of
  the allocation into the disjointness clause of the residual.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BlockSplit
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRectPack
public import Mathlib.Algebra.Field.ZMod

/-! # CoarseCellBlocks -/

@[expose] public section

open Finset

namespace Nibble.AX1

/-! ### A subset of a prescribed size -/

variable {V : Type} [DecidableEq V]

/-- A chosen subset of `A` with `n` elements (all of `A` if `n` is too large). -/
noncomputable def takeSub (A : Finset V) (n : ℕ) : Finset V :=
  if h : n ≤ #A then (Finset.exists_subset_card_eq h).choose else A

omit [DecidableEq V] in
theorem takeSub_subset (A : Finset V) (n : ℕ) : takeSub A n ⊆ A := by
  unfold takeSub
  split
  · exact (Finset.exists_subset_card_eq ‹_›).choose_spec.1
  · exact Finset.Subset.refl _

omit [DecidableEq V] in
theorem card_takeSub {A : Finset V} {n : ℕ} (h : n ≤ #A) : #(takeSub A n) = n := by
  unfold takeSub
  rw [dite_eq_left h]
  exact (Finset.exists_subset_card_eq h).choose_spec.2

/-! ### The union of a set of coarse cells -/

/-- **The union of the coarse cells of `S` indexed by `I`**, at cell length `l`. -/
noncomputable def cellUnion (S : Finset V) (l : ℕ) {P : ℕ} (I : Finset (Fin P)) : Finset V :=
  I.biUnion (fun i => blockOf S l (i : ℕ))

theorem cellUnion_subset (S : Finset V) (l : ℕ) {P : ℕ} (I : Finset (Fin P)) :
    cellUnion S l I ⊆ S := by
  intro v hv
  rw [cellUnion, Finset.mem_biUnion] at hv
  obtain ⟨i, -, hi⟩ := hv
  exact blockOf_subset S l (i : ℕ) hi

theorem card_cellUnion (S : Finset V) {l P : ℕ} (hl : 0 < l) (I : Finset (Fin P))
    (hfit : P * l ≤ #S) : #(cellUnion S l I) = #I * l := by
  classical
  have hcell : ∀ i : Fin P, #(blockOf S l (i : ℕ)) = l := by
    intro i
    refine card_blockOf S hl (le_trans (Nat.mul_le_mul_right l ?_) hfit)
    exact i.isLt
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (blockOf S l (i : ℕ)) (blockOf S l (j : ℕ)) := by
    intro i _ j _ hij
    exact blockOf_disjoint S l (fun h => hij (Fin.ext h))
  rw [cellUnion, Finset.card_biUnion hdisj,
    Finset.sum_congr rfl (fun i _ => hcell i), Finset.sum_const, smul_eq_mul]

theorem cellUnion_disjoint (S : Finset V) (l : ℕ) {P : ℕ} {I J : Finset (Fin P)}
    (h : Disjoint I J) : Disjoint (cellUnion S l I) (cellUnion S l J) := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [cellUnion, Finset.mem_biUnion] at hv hv'
  obtain ⟨i, hi, hvi⟩ := hv
  obtain ⟨j, hj, hvj⟩ := hv'
  have hij : (i : ℕ) ≠ (j : ℕ) := by
    intro hcon
    have : i = j := Fin.ext hcon
    exact (Finset.disjoint_left.mp h hi) (this ▸ hj)
  exact (Finset.disjoint_left.mp (blockOf_disjoint S l hij)) hvi hvj

/-- **The vertex block of a member**: `n` vertices inside the union of its coarse cells. -/
noncomputable def cellBlock (S : Finset V) (l : ℕ) {P : ℕ} (I : Finset (Fin P)) (n : ℕ) :
    Finset V := takeSub (cellUnion S l I) n

theorem cellBlock_subset_cellUnion (S : Finset V) (l : ℕ) {P : ℕ} (I : Finset (Fin P)) (n : ℕ) :
    cellBlock S l I n ⊆ cellUnion S l I := takeSub_subset _ _

theorem cellBlock_subset (S : Finset V) (l : ℕ) {P : ℕ} (I : Finset (Fin P)) (n : ℕ) :
    cellBlock S l I n ⊆ S :=
  Finset.Subset.trans (cellBlock_subset_cellUnion S l I n) (cellUnion_subset S l I)

theorem card_cellBlock (S : Finset V) {l P : ℕ} (hl : 0 < l) (I : Finset (Fin P)) {n : ℕ}
    (hfit : P * l ≤ #S) (hn : n ≤ #I * l) : #(cellBlock S l I n) = n := by
  refine card_takeSub ?_
  rw [card_cellUnion S hl I hfit]
  exact hn

/-! ### The disjointness engine -/

variable [Fintype V]

/-- The two positions of a vertex pair inside the rectangle of a member. -/
theorem exists_positions_of_mem_tripleRect {f : ZMod 3 → Finset V} {x y : V}
    (h : (x, y) ∈ tripleRect (f 0) (f 1) (f 2)) :
    ∃ a b : ZMod 3, a ≠ b ∧ x ∈ f a ∧ y ∈ f b := by
  rw [mem_tripleRect_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, 1, by decide +kernel, h1, h2⟩
  · exact ⟨1, 0, by decide +kernel, h1, h2⟩
  · exact ⟨0, 2, by decide +kernel, h1, h2⟩
  · exact ⟨2, 0, by decide +kernel, h1, h2⟩
  · exact ⟨1, 2, by decide +kernel, h1, h2⟩
  · exact ⟨2, 1, by decide +kernel, h1, h2⟩

/-- **The disjointness engine.**  Two members whose blocks sit inside clusters of a partition have
disjoint vertex-pair rectangles as soon as, whenever they share a cluster pair, one of the two
blocks carrying it is disjoint from the corresponding block of the other member. -/
theorem tripleRect_disjoint_of_shared_pairs
    {clA clB blkA blkB : ZMod 3 → Finset V}
    (hA : ∀ a, blkA a ⊆ clA a) (hB : ∀ a, blkB a ⊆ clB a)
    (hpart : ∀ a b : ZMod 3, ∀ v : V, v ∈ clA a → v ∈ clB b → clA a = clB b)
    (hdisj : ∀ a b a' b' : ZMod 3, a ≠ b → a' ≠ b' → clA a = clB a' → clA b = clB b' →
      Disjoint (blkA a) (blkB a') ∨ Disjoint (blkA b) (blkB b')) :
    Disjoint (tripleRect (blkA 0) (blkA 1) (blkA 2)) (tripleRect (blkB 0) (blkB 1) (blkB 2)) := by
  classical
  rw [Finset.disjoint_left]
  rintro ⟨x, y⟩ hp hq
  obtain ⟨a, b, hab, hxa, hyb⟩ := exists_positions_of_mem_tripleRect hp
  obtain ⟨a', b', hab', hxa', hyb'⟩ := exists_positions_of_mem_tripleRect hq
  have hca : clA a = clB a' := hpart a a' x (hA a hxa) (hB a' hxa')
  have hcb : clA b = clB b' := hpart b b' y (hA b hyb) (hB b' hyb')
  rcases hdisj a b a' b' hab hab' hca hcb with h | h
  · exact (Finset.disjoint_left.mp h hxa) hxa'
  · exact (Finset.disjoint_left.mp h hyb) hyb'

end Nibble.AX1
