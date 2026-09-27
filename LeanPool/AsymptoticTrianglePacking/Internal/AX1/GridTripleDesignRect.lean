/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the global block design at the level of **vertices**

`Nibble.GridTripleDesign` solves the allocation problem at the level of block *indices*: the
quadratic shift `triShift s v = v ^ 2 - v * s` gives every cluster triple, in each of its three
cluster pairs, a diagonal that no other cluster triple through that pair uses.  This file transfers
that statement to the vertex level, in the form the assembly of
`Nibble.AX1.BlockCoverResidual` (`Nibble.CoreGapBlockCover`) asks for: the **vertex-pair rectangles
`Nibble.AX1.tripleRect` of the sub-triples of the design are pairwise disjoint**.

The only input is a family of blocks indexed by *cells* — a pair (cluster index, block index) —
which are pairwise disjoint (this packages both "distinct clusters are disjoint" and "distinct
blocks of one cluster are disjoint"); the sub-triple of the cluster triple `T` (a `3`-element set of
cluster indices) with offset `j` uses, in the cluster `v ∈ T`, any subset of the block of the cell
`(v, triBlock (∑ T) v j)`.

* `Nibble.AX1.triCells` — the three cells used by a sub-triple of the design;
* `Nibble.AX1.triCells_inter_subsingleton` — two distinct sub-triples of the design share at most
  one cell.  This is the whole content of the design: for two sub-triples of the *same* cluster
  triple it is the injectivity of `j ↦ triBlock s v j`, and for two *different* cluster triples it
  is the fact that a common cluster pair forces the vertex sums, hence the triples, to agree;
* `Nibble.AX1.tripleRect_disjoint_of_design` — hence their rectangles are disjoint, which is
  exactly the hypothesis of `Nibble.AX1.tripleGraph_edgeDisjoint_of_rect_disjoint` and of
  `Nibble.AX1.sum_area_le_of_rect_disjoint`.

No probability, no graph theory, no regularity: the whole file is finite combinatorics over a prime
field.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.GridTripleDesign
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapRectPack

/-! # GridTripleDesignRect -/

@[expose] public section

open Finset

namespace Nibble.AX1

/-- A `3`-element set containing two distinct elements `a`, `b` is `{a, b, x}` for a unique third
element `x`. -/
theorem exists_third_of_card_three {α : Type} [DecidableEq α] {T : Finset α} (hT : #T = 3)
    {a b : α} (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) :
    ∃ x, T = {a, b, x} ∧ x ≠ a ∧ x ≠ b := by
  have hsub : ({a, b} : Finset α) ⊆ T := by
    intro y hy; simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl <;> assumption
  have hcard : #(T \ ({a, b} : Finset α)) = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hT,
      card_insert_of_notMem (by simpa using hab), card_singleton]
  obtain ⟨x, hx⟩ := card_eq_one.1 hcard
  have hxT : x ∈ T \ ({a, b} : Finset α) := by rw [hx]; exact mem_singleton_self x
  simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hxT
  refine ⟨x, (Finset.eq_of_subset_of_card_le ?_ ?_).symm, hxT.2.1, hxT.2.2⟩
  · intro y hy; simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> [exact ha; exact hb; exact hxT.1]
  · rw [hT, card_insert_of_notMem (by simp [hab, Ne.symm hxT.2.1]),
      card_insert_of_notMem (by simp [Ne.symm hxT.2.2]), card_singleton]

variable {q : ℕ}

/-- **The cells used by one sub-triple of the design**: the cluster triple `T` (a set of cluster
indices) with offset `j` occupies, in the cluster `v ∈ T`, the block `triBlock (∑ T) v j`. -/
def triCells (T : Finset (ZMod q)) (j : ZMod q) : Finset (ZMod q × ZMod q) :=
  T.image fun c => (c, triBlock (∑ v ∈ T, v) c j)

theorem mem_triCells {T : Finset (ZMod q)} {j v : ZMod q} (hv : v ∈ T) :
    (v, triBlock (∑ u ∈ T, u) v j) ∈ triCells T j :=
  mem_image_of_mem _ hv

theorem sum_triple {a b x : ZMod q} (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    ∑ v ∈ ({a, b, x} : Finset (ZMod q)), v = a + b + x := by
  rw [sum_insert (by simp [hab, Ne.symm hxa]), sum_insert (by simp [Ne.symm hxb]),
    sum_singleton, add_assoc]

variable [Fact (Nat.Prime q)]

/-- **Two distinct sub-triples of the design share at most one cell.**

If the cluster triples differ, or if they agree but the offsets differ, then no two cells can be
common: two common cells lie in two distinct clusters `a ≠ b`, and the identity
`triShift s b - triShift s a = (b - a) * (a + b - s)` then forces the two vertex sums to be equal,
hence the offsets to be equal and (both triples being `{a, b, ·}` with the same sum) the triples to
be equal. -/
theorem triCells_inter_subsingleton {T T' : Finset (ZMod q)} {j j' : ZMod q}
    (hT : #T = 3) (hT' : #T' = 3) (hne : ¬ (T = T' ∧ j = j'))
    {c d : ZMod q × ZMod q} (hc : c ∈ triCells T j) (hc' : c ∈ triCells T' j')
    (hd : d ∈ triCells T j) (hd' : d ∈ triCells T' j') : c = d := by
  by_contra hcd
  simp only [triCells, mem_image, Prod.ext_iff] at hc hc' hd hd'
  obtain ⟨a, haT, ha1, ha2⟩ := hc
  obtain ⟨a', ha'T, ha1', ha2'⟩ := hc'
  obtain ⟨b, hbT, hb1, hb2⟩ := hd
  obtain ⟨b', hb'T, hb1', hb2'⟩ := hd'
  subst ha1; subst hb1; subst ha1'; subst hb1'
  have hab : c.1 ≠ d.1 := by
    intro h
    exact hcd (Prod.ext h (by rw [← ha2, ← hb2, h]))
  have hs : (∑ v ∈ T, v) = ∑ v ∈ T', v := by
    have e1 : j + triShift (∑ v ∈ T, v) c.1 = j' + triShift (∑ v ∈ T', v) c.1 := by
      have := ha2.trans ha2'.symm; simpa [triBlock] using this
    have e2 : j + triShift (∑ v ∈ T, v) d.1 = j' + triShift (∑ v ∈ T', v) d.1 := by
      have := hb2.trans hb2'.symm; simpa [triBlock] using this
    have e3 : triShift (∑ v ∈ T, v) d.1 - triShift (∑ v ∈ T, v) c.1
        = triShift (∑ v ∈ T', v) d.1 - triShift (∑ v ∈ T', v) c.1 := by
      linear_combination e2 - e1
    rw [triShift_diff, triShift_diff] at e3
    have hz : (d.1 - c.1) * ((∑ v ∈ T', v) - ∑ v ∈ T, v) = 0 := by linear_combination e3
    rcases mul_eq_zero.1 hz with h' | h'
    · exact absurd (sub_eq_zero.1 h').symm hab
    · exact (sub_eq_zero.1 h').symm
  have hj : j = j' := by
    have h := ha2.trans ha2'.symm
    simp only [triBlock, hs, add_right_cancel_iff] at h
    exact h
  obtain ⟨x, hTx, hxa, hxb⟩ := exists_third_of_card_three hT haT hbT hab
  obtain ⟨x', hTx', hxa', hxb'⟩ := exists_third_of_card_three hT' ha'T hb'T hab
  rw [hTx, hTx', sum_triple hab hxa hxb, sum_triple hab hxa' hxb'] at hs
  have hxx : x = x' := by linear_combination hs
  exact hne ⟨by rw [hTx, hTx', hxx], hj⟩

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A vertex pair of the rectangle of a sub-triple whose three parts sit in the blocks of three
distinct cells joins the blocks of two distinct cells. -/
theorem tripleRect_cells {ι : Type} [DecidableEq ι] (blk : ι → Finset V) (S : Finset ι)
    {A B C : Finset V} {cA cB cC : ι} (hA : A ⊆ blk cA) (hB : B ⊆ blk cB) (hC : C ⊆ blk cC)
    (hcA : cA ∈ S) (hcB : cB ∈ S) (hcC : cC ∈ S)
    (hAB : cA ≠ cB) (hAC : cA ≠ cC) (hBC : cB ≠ cC)
    {p : V × V} (hp : p ∈ tripleRect A B C) :
    ∃ c d, c ∈ S ∧ d ∈ S ∧ c ≠ d ∧ p.1 ∈ blk c ∧ p.2 ∈ blk d := by
  obtain ⟨y, z⟩ := p
  rw [mem_tripleRect_iff] at hp
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨cA, cB, hcA, hcB, hAB, hA h1, hB h2⟩
  · exact ⟨cB, cA, hcB, hcA, hAB.symm, hB h1, hA h2⟩
  · exact ⟨cA, cC, hcA, hcC, hAC, hA h1, hC h2⟩
  · exact ⟨cC, cA, hcC, hcA, hAC.symm, hC h1, hA h2⟩
  · exact ⟨cB, cC, hcB, hcC, hBC, hB h1, hC h2⟩
  · exact ⟨cC, cB, hcC, hcB, hBC.symm, hC h1, hB h2⟩

/-- **The rectangles of the design are pairwise disjoint.**

`blk` assigns to each cell — a pair (cluster index, block index) — a block of vertices, distinct
cells getting disjoint blocks.  Two distinct sub-triples of the design (different cluster triples,
or the same cluster triple with different offsets) have disjoint vertex-pair rectangles, whatever
subsets of the three blocks are used as the parts `A`, `B`, `C`.

Combined with `Nibble.AX1.tripleGraph_edgeDisjoint_of_rect_disjoint` and
`Nibble.AX1.sum_area_le_of_rect_disjoint` this is the edge-disjointness requirement of
`Nibble.AX1.BlockCoverResidual` for the whole family of cluster triples at once. -/
theorem tripleRect_disjoint_of_design (blk : ZMod q × ZMod q → Finset V)
    (hblk : ∀ c d, c ≠ d → Disjoint (blk c) (blk d))
    {T T' : Finset (ZMod q)} {j j' : ZMod q} (hT : #T = 3) (hT' : #T' = 3)
    (hne : ¬ (T = T' ∧ j = j'))
    {u w x u' w' x' : ZMod q}
    (huT : u ∈ T) (hwT : w ∈ T) (hxT : x ∈ T) (huw : u ≠ w) (hux : u ≠ x) (hwx : w ≠ x)
    (huT' : u' ∈ T') (hwT' : w' ∈ T') (hxT' : x' ∈ T')
    (huw' : u' ≠ w') (hux' : u' ≠ x') (hwx' : w' ≠ x')
    {A B C A' B' C' : Finset V}
    (hA : A ⊆ blk (u, triBlock (∑ v ∈ T, v) u j))
    (hB : B ⊆ blk (w, triBlock (∑ v ∈ T, v) w j))
    (hC : C ⊆ blk (x, triBlock (∑ v ∈ T, v) x j))
    (hA' : A' ⊆ blk (u', triBlock (∑ v ∈ T', v) u' j'))
    (hB' : B' ⊆ blk (w', triBlock (∑ v ∈ T', v) w' j'))
    (hC' : C' ⊆ blk (x', triBlock (∑ v ∈ T', v) x' j')) :
    Disjoint (tripleRect A B C) (tripleRect A' B' C') := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨c, d, hc, hd, hcd, hp1, hp2⟩ :=
    tripleRect_cells blk (triCells T j) hA hB hC (mem_triCells huT) (mem_triCells hwT)
      (mem_triCells hxT) (by simp [Prod.ext_iff, huw]) (by simp [Prod.ext_iff, hux])
      (by simp [Prod.ext_iff, hwx]) hp
  obtain ⟨c', d', hc', hd', _, hp1', hp2'⟩ :=
    tripleRect_cells blk (triCells T' j') hA' hB' hC' (mem_triCells huT') (mem_triCells hwT')
      (mem_triCells hxT') (by simp [Prod.ext_iff, huw']) (by simp [Prod.ext_iff, hux'])
      (by simp [Prod.ext_iff, hwx']) hp'
  have hcc : c = c' := by
    by_contra h
    exact Finset.disjoint_left.1 (hblk c c' h) hp1 hp1'
  have hdd : d = d' := by
    by_contra h
    exact Finset.disjoint_left.1 (hblk d d' h) hp2 hp2'
  exact hcd (triCells_inter_subsingleton hT hT' hne hc (hcc ▸ hc') hd (hdd ▸ hd'))

end Nibble.AX1
