/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — auxiliaries for the block cover at uniform cluster densities

Three small tools used by `Nibble.CoreGapBlockCoverUniform`:

* `Nibble.AX1.pick3` — an ordered triple of the three elements of a `3`-element finset, so that a
  family of triangles can be re-indexed by `ℕ` as the residual requires;
* `Nibble.AX1.tripleRect_disjoint_of_cells_inter` — **the cell-disjointness engine**: if the blocks
  attached to distinct cells are disjoint and two members share at most one cell, then their
  vertex-pair rectangles are disjoint;
* `Nibble.AX1.nu3star_le_card_sq` — the crude bound `ν₃*(H) ≤ |V(H)|²`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.GridTripleDesignRect
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterFracUpper

/-! # BlockCoverUniformAux -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

/-! ### Naming the three elements of a triangle -/

/-- An ordered triple listing the three elements of `t`, when `t` has exactly three of them. -/
noncomputable def pick3 {ι : Type} [Nonempty ι] [DecidableEq ι] (t : Finset ι) : ι × ι × ι :=
  open Classical in
  if h : ∃ x y z : ι, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ t = {x, y, z} then
    (h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose)
  else (Classical.arbitrary ι, Classical.arbitrary ι, Classical.arbitrary ι)

theorem pick3_spec {ι : Type} [Nonempty ι] [DecidableEq ι] {t : Finset ι} (h3 : #t = 3) :
    (pick3 t).1 ≠ (pick3 t).2.1 ∧ (pick3 t).1 ≠ (pick3 t).2.2 ∧
      (pick3 t).2.1 ≠ (pick3 t).2.2 ∧ t = {(pick3 t).1, (pick3 t).2.1, (pick3 t).2.2} := by
  have h : ∃ x y z : ι, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ t = {x, y, z} := Finset.card_eq_three.mp h3
  rw [pick3, dite_eq_left h]
  exact h.choose_spec.choose_spec.choose_spec

theorem pick3_mem {ι : Type} [Nonempty ι] [DecidableEq ι] {t : Finset ι} (h3 : #t = 3) :
    (pick3 t).1 ∈ t ∧ (pick3 t).2.1 ∈ t ∧ (pick3 t).2.2 ∈ t := by
  obtain ⟨-, -, -, ht⟩ := pick3_spec h3
  have hsub : ({(pick3 t).1, (pick3 t).2.1, (pick3 t).2.2} : Finset ι) ⊆ t := ht.ge
  exact ⟨hsub (by simp), hsub (by simp), hsub (by simp)⟩

/-! ### Cell disjointness gives rectangle disjointness -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The rectangles of two members that share at most one cell are disjoint.**  `blk` assigns a
block of vertices to each cell, distinct cells getting disjoint blocks; a member is given by three
distinct cells, and its three parts are subsets of the corresponding blocks. -/
theorem tripleRect_disjoint_of_cells_inter {ι : Type} [DecidableEq ι] (blk : ι → Finset V)
    (hblk : ∀ c d, c ≠ d → Disjoint (blk c) (blk d))
    {t t' : Finset ι} (hint : #(t ∩ t') ≤ 1)
    {cA cB cC cA' cB' cC' : ι}
    (hcA : cA ∈ t) (hcB : cB ∈ t) (hcC : cC ∈ t)
    (hAB : cA ≠ cB) (hAC : cA ≠ cC) (hBC : cB ≠ cC)
    (hcA' : cA' ∈ t') (hcB' : cB' ∈ t') (hcC' : cC' ∈ t')
    (hAB' : cA' ≠ cB') (hAC' : cA' ≠ cC') (hBC' : cB' ≠ cC')
    {A B C A' B' C' : Finset V}
    (hA : A ⊆ blk cA) (hB : B ⊆ blk cB) (hC : C ⊆ blk cC)
    (hA' : A' ⊆ blk cA') (hB' : B' ⊆ blk cB') (hC' : C' ⊆ blk cC') :
    Disjoint (tripleRect A B C) (tripleRect A' B' C') := by
  classical
  rw [Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨c, d, hc, hd, hcd, hp1, hp2⟩ :=
    tripleRect_cells blk t hA hB hC hcA hcB hcC hAB hAC hBC hp
  obtain ⟨c', d', hc', hd', -, hp1', hp2'⟩ :=
    tripleRect_cells blk t' hA' hB' hC' hcA' hcB' hcC' hAB' hAC' hBC' hp'
  have hcc : c = c' := by
    by_contra h
    exact Finset.disjoint_left.1 (hblk c c' h) hp1 hp1'
  have hdd : d = d' := by
    by_contra h
    exact Finset.disjoint_left.1 (hblk d d' h) hp2 hp2'
  have hcmem : c ∈ t ∩ t' := Finset.mem_inter.mpr ⟨hc, hcc ▸ hc'⟩
  have hdmem : d ∈ t ∩ t' := Finset.mem_inter.mpr ⟨hd, hdd ▸ hd'⟩
  have : ({c, d} : Finset ι) ⊆ t ∩ t' := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard : 2 ≤ #(t ∩ t') := by
    have := Finset.card_le_card this
    rwa [Finset.card_insert_of_notMem (by simpa using hcd), Finset.card_singleton] at this
  omega

/-! ### A crude bound for the fractional triangle packing number -/

theorem nu3star_le_card_sq {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] : nu3star H ≤ (Fintype.card W : ℝ) ^ 2 := by
  classical
  have hsub : H.cliqueFinset 2 ⊆ (Finset.univ : Finset W).powersetCard 2 := by
    intro t ht
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq⟩
  have hcard : (#(H.cliqueFinset 2) : ℝ) ≤ (Fintype.card W : ℝ) ^ 2 := by
    have h1 : #(H.cliqueFinset 2) ≤ (Fintype.card W).choose 2 := by
      have := Finset.card_le_card hsub
      rwa [Finset.card_powersetCard, Finset.card_univ] at this
    have h2 : (Fintype.card W).choose 2 ≤ (Fintype.card W) ^ 2 := by
      rw [Nat.choose_two_right]
      calc Fintype.card W * (Fintype.card W - 1) / 2
          ≤ Fintype.card W * (Fintype.card W - 1) := Nat.div_le_self _ _
        _ ≤ Fintype.card W * Fintype.card W := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = (Fintype.card W) ^ 2 := by ring
    exact_mod_cast le_trans h1 h2
  have h3 : (0:ℝ) ≤ (#(H.cliqueFinset 2) : ℝ) := by positivity
  have := Nibble.YusterE.nu3star_le (G := H)
  linarith

end Nibble.AX1
