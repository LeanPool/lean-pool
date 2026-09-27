/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the sub-block grid inside **one** cluster triple

This file carries out the first of the two missing ingredients recorded in
`Nibble.CoreGapGridResidual`: inside a single triple `(U, W, X)` of pairwise `ε₁`-uniform clusters
of densities at least `δ`, it *constructs* the rectangular diagonal family of sub-triples and proves
every clause of `Nibble.AX1.IsSubTripleDesign` that concerns the triple alone.

* `Nibble.AX1.IsSubTripleShape` — the "local" clauses of a design: pairwise disjointness,
  `ε₂`-uniformity and density at least `2ε₂` of the three pairs of each sub-triple, the six
  scale-equalisation inequalities, and edge-disjointness of the family.
* `Nibble.AX1.isSubTripleDesign_of_shape` — a shape plus the "global" clauses (the scale being at
  least `d₀`, the slack, the edge counts and the covering bound) is a design.
* `Nibble.AX1.subTripleShape_grid` — **the construction**: the blocks
  `Nibble.AX1.blockOf` of sizes `sA ≈ τ·d(W,X)`, `sB ≈ τ·d(U,X)`, `sC ≈ τ·d(U,W)` — proportional to
  the *opposite* densities — arranged on the rectangular diagonal grid of
  `Nibble.AX1.rectDesign_pairwise_edgeDisjoint`, form a shape with common triangle-degree scale
  `d = τ·d(U,W)·d(U,X)·d(W,X)`.

Uniformity passes to the blocks by `Nibble.AX1.isUniform_subblock`, their densities are within `ε₁`
of the cluster densities by `Nibble.AX1.edgeDensity_sub_lt_of_isUniform`, and the three
triangle-degree scales are equalised by `Nibble.AX1.scale_window`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapDesign
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapSubblock
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.GridScale
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.GridDesignRect
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BlockSplit

/-! # CoreGapTripleShape -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The local clauses of a sub-triple design.**  Everything in
`Nibble.AX1.IsSubTripleDesign` that refers only to the sub-triples themselves: the three parts of
each sub-triple are disjoint, pairwise `ε₂`-uniform and of density at least `2ε₂`, the three
triangle-degree scales of each sub-triple agree with a common `d i` to within `μ₂`, and the
tripartite graphs of the family are pairwise edge-disjoint. -/
def IsSubTripleShape (G : SimpleGraph V) [DecidableRel G.Adj] (ε₂ μ₂ : ℝ) (k : ℕ)
    (A B C : ℕ → Finset V) (d : ℕ → ℝ) : Prop :=
  (∀ i < k, Disjoint (A i) (B i)) ∧
  (∀ i < k, Disjoint (A i) (C i)) ∧
  (∀ i < k, Disjoint (B i) (C i)) ∧
  (∀ i < k, G.IsUniform ε₂ (A i) (B i)) ∧
  (∀ i < k, G.IsUniform ε₂ (A i) (C i)) ∧
  (∀ i < k, G.IsUniform ε₂ (B i) (C i)) ∧
  (∀ i < k, 2 * ε₂ ≤ (G.edgeDensity (A i) (B i) : ℝ)) ∧
  (∀ i < k, 2 * ε₂ ≤ (G.edgeDensity (A i) (C i) : ℝ)) ∧
  (∀ i < k, 2 * ε₂ ≤ (G.edgeDensity (B i) (C i) : ℝ)) ∧
  (∀ i < k, (1 - μ₂) * d i ≤ ((G.edgeDensity (A i) (C i) : ℝ) - ε₂)
    * ((G.edgeDensity (B i) (C i) : ℝ) - 2 * ε₂) * (#(C i) : ℝ)) ∧
  (∀ i < k, ((G.edgeDensity (A i) (C i) : ℝ) + ε₂)
    * ((G.edgeDensity (B i) (C i) : ℝ) + 2 * ε₂) * (#(C i) : ℝ) ≤ (1 + μ₂) * d i) ∧
  (∀ i < k, (1 - μ₂) * d i ≤ ((G.edgeDensity (A i) (B i) : ℝ) - ε₂)
    * ((G.edgeDensity (B i) (C i) : ℝ) - 2 * ε₂) * (#(B i) : ℝ)) ∧
  (∀ i < k, ((G.edgeDensity (A i) (B i) : ℝ) + ε₂)
    * ((G.edgeDensity (B i) (C i) : ℝ) + 2 * ε₂) * (#(B i) : ℝ) ≤ (1 + μ₂) * d i) ∧
  (∀ i < k, (1 - μ₂) * d i ≤ ((G.edgeDensity (A i) (B i) : ℝ) - ε₂)
    * ((G.edgeDensity (A i) (C i) : ℝ) - 2 * ε₂) * (#(A i) : ℝ)) ∧
  (∀ i < k, ((G.edgeDensity (A i) (B i) : ℝ) + ε₂)
    * ((G.edgeDensity (A i) (C i) : ℝ) + 2 * ε₂) * (#(A i) : ℝ) ≤ (1 + μ₂) * d i) ∧
  (∀ i < k, ∀ j < k, i ≠ j → ∀ x y,
    (tripleGraph G (A i) (B i) (C i)).Adj x y → ¬ (tripleGraph G (A j) (B j) (C j)).Adj x y)

/-- **A shape together with the global clauses is a design.** -/
theorem isSubTripleDesign_of_shape (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε μ η d₀ ε₂ μ₂ t : ℝ} {k : ℕ} {A B C : ℕ → Finset V} {d Elo : ℕ → ℝ}
    (hshape : IsSubTripleShape G ε₂ μ₂ k A B C d)
    (hε₂ : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) (ht : 0 < t) (hη : 0 ≤ η) (hμ₂ : μ₂ ≤ μ)
    (hd₀ : ∀ i < k, d₀ ≤ d i) (hdnn : ∀ i < k, 0 ≤ d i)
    (hslack : ∀ i < k, 2 * t ≤ (μ - μ₂) * d i)
    (hElo : ∀ i < k, Elo i ≤ (#((tripleGraph G (A i) (B i) (C i)).cliqueFinset 2) : ℝ))
    (hexc : ∀ i < k, (2 * designBad ε₂ (A i) (B i) (C i) / t) * (Fintype.card V : ℝ)
      ≤ η * (Elo i - designBad ε₂ (A i) (B i) (C i)))
    (hcover : nu3star G ≤ (∑ i ∈ Finset.range k,
      (Elo i - designBad ε₂ (A i) (B i) (C i)) / 3) + ε * (Fintype.card V : ℝ) ^ 2) :
    IsSubTripleDesign G ε μ η d₀ ε₂ μ₂ t k A B C d Elo := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hshape
  exact ⟨hε₂, hε₂1, ht, hη, hμ₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    hd₀, hdnn, hslack, h16, hElo, hexc, hcover⟩

/-! ### The construction inside one cluster triple -/

omit [Fintype V] in
/-- **The sub-block grid of one cluster triple is a shape.**

The clusters `U`, `W`, `X` are pairwise `ε₁`-uniform of densities `x = d(U,W)`, `y = d(U,X)`,
`z = d(W,X)` in `[δ, 1]`.  Split `U` into `nA` blocks of size `sA ≈ τ·z`, `W` into `nB` blocks of
size `sB ≈ τ·y` and `X` into `nC` blocks of size `sC ≈ τ·x` — each block size proportional to the
density of the *opposite* pair, and each block of relative size at least `α` in its cluster — and
take the `nB·nC` diagonal sub-triples of `Nibble.AX1.rectDesign_pairwise_edgeDisjoint`.  Then, at
uniformity scale `ε₂ = ε₁/α`, this family is a shape with the single triangle-degree scale
`d = τ·x·y·z`. -/
theorem subTripleShape_grid (G : SimpleGraph V) [DecidableRel G.Adj] {U W X : Finset V}
    {δ μ₂ ε₁ α τ : ℝ} {sA sB sC nA nB nC : ℕ}
    (hUW : Disjoint U W) (hUX : Disjoint U X) (hWX : Disjoint W X)
    (huUW : G.IsUniform ε₁ U W) (huUX : G.IsUniform ε₁ U X) (huWX : G.IsUniform ε₁ W X)
    (hε₁ : 0 < ε₁) (hαε : ε₁ ≤ α) (hα2 : 2 * α ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hμ0 : 0 < μ₂) (hμ1 : μ₂ ≤ 1)
    (hx : δ ≤ (G.edgeDensity U W : ℝ)) (hy : δ ≤ (G.edgeDensity U X : ℝ))
    (hz : δ ≤ (G.edgeDensity W X : ℝ))
    (hErr : ε₁ + 2 * (ε₁ / α) ≤ μ₂ * δ ^ 3 / 12)
    (hdense : 2 * (ε₁ / α) + ε₁ ≤ δ)
    (hτ : 2 / (μ₂ * δ ^ 3) ≤ τ)
    (hsA : |(sA : ℝ) - τ * (G.edgeDensity W X : ℝ)| ≤ 1)
    (hsB : |(sB : ℝ) - τ * (G.edgeDensity U X : ℝ)| ≤ 1)
    (hsC : |(sC : ℝ) - τ * (G.edgeDensity U W : ℝ)| ≤ 1)
    (hsA0 : 0 < sA) (hsB0 : 0 < sB) (hsC0 : 0 < sC)
    (hfitA : nA * sA ≤ #U) (hfitB : nB * sB ≤ #W) (hfitC : nC * sC ≤ #X)
    (hrelA : α * (#U : ℝ) ≤ (sA : ℝ)) (hrelB : α * (#W : ℝ) ≤ (sB : ℝ))
    (hrelC : α * (#X : ℝ) ≤ (sC : ℝ))
    (hBA : nB ≤ nA) (hCA : nC ≤ nA) :
    IsSubTripleShape G (ε₁ / α) μ₂ (nB * nC)
      (fun i => blockOf U sA (rectIdxA nA nC i))
      (fun i => blockOf W sB (rectIdxB nC i))
      (fun i => blockOf X sC (rectIdxC nC i))
      (fun _ => τ * ((G.edgeDensity U W : ℝ) * (G.edgeDensity U X : ℝ)
        * (G.edgeDensity W X : ℝ))) := by
  classical
  set x : ℝ := (G.edgeDensity U W : ℝ) with hxdef
  set y : ℝ := (G.edgeDensity U X : ℝ) with hydef
  set z : ℝ := (G.edgeDensity W X : ℝ) with hzdef
  have hx1 : x ≤ 1 := by rw [hxdef]; exact_mod_cast G.edgeDensity_le_one U W
  have hy1 : y ≤ 1 := by rw [hydef]; exact_mod_cast G.edgeDensity_le_one U X
  have hz1 : z ≤ 1 := by rw [hzdef]; exact_mod_cast G.edgeDensity_le_one W X
  have hε₂ : 0 < ε₁ / α := div_pos hε₁ (lt_of_lt_of_le hε₁ hαε)
  -- block index bounds
  have hnCpos : ∀ i, i < nB * nC → 0 < nC := by
    intro i hi
    rcases Nat.eq_zero_or_pos nC with rfl | h
    · simp at hi
    · exact h
  have hnBpos : ∀ i, i < nB * nC → 0 < nB := by
    intro i hi
    rcases Nat.eq_zero_or_pos nB with rfl | h
    · simp at hi
    · exact h
  -- the blocks and their cardinalities
  have hcardA : ∀ i < nB * nC, #(blockOf U sA (rectIdxA nA nC i)) = sA := by
    intro i hi
    have hnC := hnCpos i hi
    have hnA : 0 < nA := lt_of_lt_of_le hnC hCA
    have ha : rectIdxA nA nC i < nA := rectIdxA_lt hnA i
    refine card_blockOf U hsA0 (le_trans ?_ hfitA)
    exact Nat.mul_le_mul_right _ ha
  have hcardB : ∀ i < nB * nC, #(blockOf W sB (rectIdxB nC i)) = sB := by
    intro i hi
    have hb : rectIdxB nC i < nB := rectIdxB_lt hi
    refine card_blockOf W hsB0 (le_trans ?_ hfitB)
    exact Nat.mul_le_mul_right _ hb
  have hcardC : ∀ i < nB * nC, #(blockOf X sC (rectIdxC nC i)) = sC := by
    intro i hi
    have hc : rectIdxC nC i < nC := rectIdxC_lt (hnCpos i hi) i
    refine card_blockOf X hsC0 (le_trans ?_ hfitC)
    exact Nat.mul_le_mul_right _ hc
  -- uniformity of the block pairs
  have huAB : ∀ i < nB * nC, G.IsUniform (ε₁ / α)
      (blockOf U sA (rectIdxA nA nC i)) (blockOf W sB (rectIdxB nC i)) := by
    intro i hi
    refine isUniform_subblock G huUW hε₁ (blockOf_subset U sA _) (blockOf_subset W sB _)
      hαε hα2 ?_ ?_
    · rw [hcardA i hi]; exact hrelA
    · rw [hcardB i hi]; exact hrelB
  have huAC : ∀ i < nB * nC, G.IsUniform (ε₁ / α)
      (blockOf U sA (rectIdxA nA nC i)) (blockOf X sC (rectIdxC nC i)) := by
    intro i hi
    refine isUniform_subblock G huUX hε₁ (blockOf_subset U sA _) (blockOf_subset X sC _)
      hαε hα2 ?_ ?_
    · rw [hcardA i hi]; exact hrelA
    · rw [hcardC i hi]; exact hrelC
  have huBC : ∀ i < nB * nC, G.IsUniform (ε₁ / α)
      (blockOf W sB (rectIdxB nC i)) (blockOf X sC (rectIdxC nC i)) := by
    intro i hi
    refine isUniform_subblock G huWX hε₁ (blockOf_subset W sB _) (blockOf_subset X sC _)
      hαε hα2 ?_ ?_
    · rw [hcardB i hi]; exact hrelB
    · rw [hcardC i hi]; exact hrelC
  -- the block densities are within `ε₁` of the cluster densities
  have hdAB : ∀ i < nB * nC,
      |(G.edgeDensity (blockOf U sA (rectIdxA nA nC i)) (blockOf W sB (rectIdxB nC i)) : ℝ)
        - x| ≤ ε₁ := by
    intro i hi
    refine le_of_lt (edgeDensity_sub_lt_of_isUniform G huUW (blockOf_subset U sA _)
      (blockOf_subset W sB _) hαε ?_ ?_)
    · rw [hcardA i hi]; exact hrelA
    · rw [hcardB i hi]; exact hrelB
  have hdAC : ∀ i < nB * nC,
      |(G.edgeDensity (blockOf U sA (rectIdxA nA nC i)) (blockOf X sC (rectIdxC nC i)) : ℝ)
        - y| ≤ ε₁ := by
    intro i hi
    refine le_of_lt (edgeDensity_sub_lt_of_isUniform G huUX (blockOf_subset U sA _)
      (blockOf_subset X sC _) hαε ?_ ?_)
    · rw [hcardA i hi]; exact hrelA
    · rw [hcardC i hi]; exact hrelC
  have hdBC : ∀ i < nB * nC,
      |(G.edgeDensity (blockOf W sB (rectIdxB nC i)) (blockOf X sC (rectIdxC nC i)) : ℝ)
        - z| ≤ ε₁ := by
    intro i hi
    refine le_of_lt (edgeDensity_sub_lt_of_isUniform G huWX (blockOf_subset W sB _)
      (blockOf_subset X sC _) hαε ?_ ?_)
    · rw [hcardB i hi]; exact hrelB
    · rw [hcardC i hi]; exact hrelC
  -- densities of the blocks are at least `2ε₂`
  have hlow : ∀ (u v : ℝ), δ ≤ v → |u - v| ≤ ε₁ → 2 * (ε₁ / α) ≤ u := by
    intro u v hv habs
    have := (abs_le.mp habs).1
    linarith
  refine ⟨?_, ?_, ?_, huAB, huAC, huBC, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i _ => Finset.disjoint_of_subset_left (blockOf_subset U sA _)
      (Finset.disjoint_of_subset_right (blockOf_subset W sB _) hUW)
  · exact fun i _ => Finset.disjoint_of_subset_left (blockOf_subset U sA _)
      (Finset.disjoint_of_subset_right (blockOf_subset X sC _) hUX)
  · exact fun i _ => Finset.disjoint_of_subset_left (blockOf_subset W sB _)
      (Finset.disjoint_of_subset_right (blockOf_subset X sC _) hWX)
  · exact fun i hi => hlow _ _ hx (hdAB i hi)
  · exact fun i hi => hlow _ _ hy (hdAC i hi)
  · exact fun i hi => hlow _ _ hz (hdBC i hi)
  -- the three scale windows
  · intro i hi
    rw [hcardC i hi]
    exact (scale_window (x := y) (y := z) (z := x) (δ := δ) (μ := μ₂) (ε := ε₁ / α) (e := ε₁)
      hδ0 hδ1 hy hy1 hz hz1 hx hx1 (hdAC i hi) (hdBC i hi) hsC hε₁.le hε₂ hμ0 hμ1 hErr hτ
      (by ring)).1
  · intro i hi
    rw [hcardC i hi]
    exact (scale_window (x := y) (y := z) (z := x) (δ := δ) (μ := μ₂) (ε := ε₁ / α) (e := ε₁)
      hδ0 hδ1 hy hy1 hz hz1 hx hx1 (hdAC i hi) (hdBC i hi) hsC hε₁.le hε₂ hμ0 hμ1 hErr hτ
      (by ring)).2
  · intro i hi
    rw [hcardB i hi]
    exact (scale_window (x := x) (y := z) (z := y) (δ := δ) (μ := μ₂) (ε := ε₁ / α) (e := ε₁)
      hδ0 hδ1 hx hx1 hz hz1 hy hy1 (hdAB i hi) (hdBC i hi) hsB hε₁.le hε₂ hμ0 hμ1 hErr hτ
      (by ring)).1
  · intro i hi
    rw [hcardB i hi]
    exact (scale_window (x := x) (y := z) (z := y) (δ := δ) (μ := μ₂) (ε := ε₁ / α) (e := ε₁)
      hδ0 hδ1 hx hx1 hz hz1 hy hy1 (hdAB i hi) (hdBC i hi) hsB hε₁.le hε₂ hμ0 hμ1 hErr hτ
      (by ring)).2
  · intro i hi
    rw [hcardA i hi]
    exact (scale_window (x := x) (y := y) (z := z) (δ := δ) (μ := μ₂) (ε := ε₁ / α) (e := ε₁)
      hδ0 hδ1 hx hx1 hy hy1 hz hz1 (hdAB i hi) (hdAC i hi) hsA hε₁.le hε₂ hμ0 hμ1 hErr hτ
      rfl).1
  · intro i hi
    rw [hcardA i hi]
    exact (scale_window (x := x) (y := y) (z := z) (δ := δ) (μ := μ₂) (ε := ε₁ / α) (e := ε₁)
      hδ0 hδ1 hx hx1 hy hy1 hz hz1 (hdAB i hi) (hdAC i hi) hsA hε₁.le hε₂ hμ0 hμ1 hErr hτ
      rfl).2
  -- edge-disjointness of the diagonal family
  · intro i hi j hj hij p q hp
    exact rectDesign_pairwise_edgeDisjoint G (blockOf U sA) (blockOf W sB) (blockOf X sC)
      hBA hCA (fun a _ b _ hab => blockOf_disjoint U sA hab)
      (fun a _ b _ hab => blockOf_disjoint W sB hab)
      (fun a _ b _ hab => blockOf_disjoint X sC hab)
      (fun a _ b _ => Finset.disjoint_of_subset_left (blockOf_subset U sA _)
        (Finset.disjoint_of_subset_right (blockOf_subset W sB _) hUW))
      (fun a _ b _ => Finset.disjoint_of_subset_left (blockOf_subset U sA _)
        (Finset.disjoint_of_subset_right (blockOf_subset X sC _) hUX))
      (fun a _ b _ => Finset.disjoint_of_subset_left (blockOf_subset W sB _)
        (Finset.disjoint_of_subset_right (blockOf_subset X sC _) hWX))
      hi hj hij p q hp

end Nibble.AX1
