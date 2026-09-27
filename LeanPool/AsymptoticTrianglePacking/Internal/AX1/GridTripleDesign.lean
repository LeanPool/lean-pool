/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **global (multi-triple) block design**

`Nibble.AX1.gridShift` (`Nibble.GridShiftUnique`) and `Nibble.AX1.gridUW_bijective`
(`Nibble.GridShiftBalance`) organise the block sub-triples *inside one cluster triple*, and
`Nibble.AX1.lineTriple` (`Nibble.GridLineDesign`) isolates the unit of allocation, a whole
**diagonal** of a cluster pair.  What `Nibble.AX1.BlockCoverResidual`
(`Nibble.CoreGapBlockCover`) is missing beyond that is a *simultaneously consistent* choice of
diagonals: a cluster pair `{a, b}` is shared by many cluster triples `{a, b, x}`, and the diagonal
that a triple uses in the pair `{a, b}` is not free — it is determined by the shifts the triple
gives to its three clusters, which have to work for all three of its pairs at once.

This file solves that allocation problem outright, deterministically and in closed form.

## The design

Index the clusters by distinct elements of a prime field `ZMod q` and the blocks of every cluster
by `ZMod q` as well.  To the cluster triple with **vertex sum** `s = u + w + x` associate the
*quadratic shift*

`triShift s v = v ^ 2 - v * s`

and let its `j`-th block sub-triple (`j ∈ ZMod q`) use, in cluster `v`, the block

`triBlock s v j = j + triShift s v`.

For a fixed triple, `j ↦ triBlock s v j` is a bijection of the blocks of `v`
(`Nibble.AX1.triBlock_bijective`): each cluster is covered exactly once, so the `q` sub-triples of
a triple tile the three cluster pairs along one diagonal each, as in the line design.

The point of the quadratic shift is the identity

`triShift s b - triShift s a = (b - a) * (a + b - s)`  (`Nibble.AX1.triShift_diff`),

so in the pair `{a, b}` the triple occupies the diagonal of offset `(b - a) * (a + b - s)`, which,
for `a ≠ b`, is an *injective* function of `s`.  Consequently two distinct cluster triples through
the same cluster pair always sit on different diagonals of that pair, and therefore never share a
block pair — for **all three** of their pairs at once, because the vertex sum `s` is symmetric in
the triple (`Nibble.AX1.triPairSet_disjoint`, `Nibble.AX1.triPairSet_disjoint_of_third`).

## Contents

* `Nibble.AX1.triShift`, `Nibble.AX1.triBlock` — the design;
* `Nibble.AX1.triShift_diff` — the diagonal offset of the pair `{a, b}` in the triple of sum `s`;
* `Nibble.AX1.triBlock_bijective` — each cluster is covered exactly once by the `q` sub-triples;
* `Nibble.AX1.triBlock_eq_lineTriple` — the sub-triples of a fixed triple form a line, so the
  single-triple statements of `Nibble.GridLineDesign` and `Nibble.GridShiftBalance` apply verbatim;
* `Nibble.AX1.triPairSet` and `Nibble.AX1.card_triPairSet` — the `q` block pairs a triple uses in
  one of its pairs;
* `Nibble.AX1.triPairSet_disjoint`, `Nibble.AX1.triPairSet_disjoint_of_third` — the disjointness
  across triples;
* `Nibble.AX1.card_triPairSet_biUnion` — hence `q * (number of triples through the pair)` distinct
  block pairs are used in a cluster pair, out of the `q ^ 2` available: the allocation is feasible
  as soon as `q` is at least the number of clusters.

Everything here is at the level of block *indices*: no probability, no graph theory, and no
choice of an ordering of the clusters.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.GridLineDesign
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.LinearCombination

/-! # GridTripleDesign -/

@[expose] public section

namespace Nibble.AX1

open Finset

variable {q : ℕ}

/-- **The quadratic shift** of the cluster `v` in the cluster triple of vertex sum `s`. -/
def triShift (s v : ZMod q) : ZMod q := v ^ 2 - v * s

/-- **The block used in cluster `v` by the `j`-th sub-triple** of the cluster triple of vertex
sum `s`. -/
def triBlock (s v j : ZMod q) : ZMod q := j + triShift s v

/-- **The diagonal offset**: in the cluster pair `{a, b}`, the triple of vertex sum `s` occupies
the diagonal `{(k, k + (b - a) * (a + b - s))}`.  For `a ≠ b` this offset is an injective function
of `s`, which is the whole point of the design. -/
theorem triShift_diff (s a b : ZMod q) :
    triShift s b - triShift s a = (b - a) * (a + b - s) := by
  simp only [triShift]; ring

/-- For the triple `{u, w, x}` the offset of the pair `{u, w}` is `-(w - u) * x`: it depends on the
pair and on the *third* vertex only. -/
theorem triShift_diff_third (u w x : ZMod q) :
    triShift (u + w + x) w - triShift (u + w + x) u = -((w - u) * x) := by
  simp only [triShift]; ring

@[simp] theorem triBlock_zero_shift (s v : ZMod q) : triBlock s v 0 = triShift s v := by
  simp [triBlock]

/-- Inside one cluster triple, the `q` sub-triples cover every block of every one of the three
clusters exactly once. -/
theorem triBlock_bijective (s v : ZMod q) : Function.Bijective (triBlock s v) :=
  ⟨fun j j' h => by simpa [triBlock] using h,
   fun k => ⟨k - triShift s v, by simp [triBlock]⟩⟩

/-- The sub-triples of a fixed cluster triple form a *line* in the sense of
`Nibble.AX1.lineTriple`, re-based at the first cluster: all single-triple facts proved for the
line design apply. -/
theorem triBlock_eq_lineTriple (s u w x j : ZMod q) :
    (triBlock s u j, triBlock s w j, triBlock s x j)
      = lineTriple (triShift s w - triShift s u) (triShift s x - triShift s u)
          (triBlock s u j) := by
  simp only [lineTriple, triBlock, Prod.mk.injEq, true_and]
  exact ⟨by ring, by ring⟩

variable [NeZero q]

/-- **The block pairs a cluster triple uses in one of its cluster pairs**: the diagonal of offset
`(b - a) * (a + b - s)`. -/
def triPairSet (s a b : ZMod q) : Finset (ZMod q × ZMod q) :=
  (univ : Finset (ZMod q)).image fun j => (triBlock s a j, triBlock s b j)

theorem mem_triPairSet {s a b : ZMod q} {p : ZMod q × ZMod q} :
    p ∈ triPairSet s a b ↔ ∃ j, (triBlock s a j, triBlock s b j) = p := by
  simp [triPairSet]

/-- A block pair of the diagonal is determined by its first coordinate. -/
theorem triPairSet_snd_eq {s a b : ZMod q} {p : ZMod q × ZMod q} (hp : p ∈ triPairSet s a b) :
    p.2 = p.1 + (triShift s b - triShift s a) := by
  obtain ⟨j, rfl⟩ := mem_triPairSet.1 hp
  simp only [triBlock]; ring

/-- Each cluster triple uses exactly `q` block pairs in each of its three cluster pairs. -/
theorem card_triPairSet (s a b : ZMod q) : #(triPairSet s a b) = q := by
  rw [triPairSet, card_image_of_injective _ (fun j j' h => by
    simpa [triBlock, Prod.ext_iff] using h), card_univ, ZMod.card]

variable [Fact (Nat.Prime q)]

/-- **The allocation is consistent**: two cluster triples with different vertex sums use *disjoint*
sets of block pairs in every cluster pair `{a, b}` they share.  Since the vertex sum is symmetric,
this holds simultaneously for all three pairs of each triple. -/
theorem triPairSet_disjoint {s s' a b : ZMod q} (hab : a ≠ b) (hs : s ≠ s') :
    Disjoint (triPairSet s a b) (triPairSet s' a b) := by
  rw [Finset.disjoint_left]
  rintro p hp hp'
  have h := (triPairSet_snd_eq hp).symm.trans (triPairSet_snd_eq hp')
  rw [add_right_inj, triShift_diff, triShift_diff] at h
  have hz : (b - a) * (s' - s) = 0 := by linear_combination h
  rcases mul_eq_zero.1 hz with h' | h'
  · exact hab (sub_eq_zero.1 h').symm
  · exact hs (sub_eq_zero.1 h').symm

/-- The form used in the assembly: two cluster triples through the same cluster pair `{a, b}`,
with different third clusters, never share a block pair. -/
theorem triPairSet_disjoint_of_third {a b x x' : ZMod q} (hab : a ≠ b) (hx : x ≠ x') :
    Disjoint (triPairSet (a + b + x) a b) (triPairSet (a + b + x') a b) :=
  triPairSet_disjoint hab fun h => hx (by
    have := add_left_cancel h; exact this)

/-- **Feasibility of the allocation**: if `S` is a set of third clusters, the triples
`{a, b, x}`, `x ∈ S`, together use `q * #S` distinct block pairs of the cluster pair `{a, b}`, out
of the `q ^ 2` block pairs available.  So the design fits as long as the number of cluster triples
through a pair is at most the number `q` of blocks per cluster. -/
theorem card_triPairSet_biUnion {a b : ZMod q} (hab : a ≠ b) (S : Finset (ZMod q)) :
    #(S.biUnion fun x => triPairSet (a + b + x) a b) = q * #S := by
  rw [card_biUnion, Finset.sum_congr rfl fun x _ => card_triPairSet _ _ _, sum_const,
    smul_eq_mul, mul_comm]
  intro x _ y _ hxy
  exact triPairSet_disjoint_of_third hab hxy

/-- The block pairs used in a cluster pair are of course among all `q ^ 2` of them, so the count
above is a genuine packing bound: the design never overflows a cluster pair. -/
theorem card_triPairSet_biUnion_le {a b : ZMod q} (hab : a ≠ b) (S : Finset (ZMod q)) :
    #(S.biUnion fun x => triPairSet (a + b + x) a b) ≤ q ^ 2 := by
  have hS : #S ≤ q := by
    have : #S ≤ Fintype.card (ZMod q) := card_le_univ S
    simpa [ZMod.card] using this
  rw [card_triPairSet_biUnion hab, sq]
  exact Nat.mul_le_mul_left _ hS

end Nibble.AX1
