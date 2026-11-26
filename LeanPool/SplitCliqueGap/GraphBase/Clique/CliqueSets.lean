/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GraphBase.Clique.Partition

/-!
# Fractional clique partitions, summed over `cliqueSets`

A fractional clique partition vanishes outside `G.cliqueSets`, so its edge constraints and its
total weight may be
computed over `G.cliqueSets` instead of over all vertex sets. This file gives that form of the API.
-/

@[expose] public section

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem IsFracCliquePartition.eq_zero_of_notMem {x : Finset V → ℝ} (hx : G.IsFracCliquePartition x)
    {Q : Finset V} (hQ : Q ∉ G.cliqueSets) : x Q = 0 := by
  by_contra h
  exact hQ (mem_cliqueSets.mpr (hx.support Q h))

/-- Sums of `x` over a filter of all vertex sets may be taken over `cliqueSets`. -/
theorem IsFracCliquePartition.sum_filter_cliqueSets {x : Finset V → ℝ} (hx :
  G.IsFracCliquePartition x)
    (p : Finset V → Prop) [DecidablePred p] :
    ∑ Q ∈ G.cliqueSets with p Q, x Q = ∑ Q ∈ univ.filter p, x Q := by
  rw [sum_filter, sum_filter]
  exact sum_subset (subset_univ _) fun Q _ hQ => by simp [hx.eq_zero_of_notMem hQ]

theorem IsFracCliquePartition.edge_cliqueSets {x : Finset V → ℝ} (hx : G.IsFracCliquePartition x)
    {u v : V} (huv : G.Adj u v) : ∑ Q ∈ G.cliqueSets with (u ∈ Q ∧ v ∈ Q), x Q = 1 := by
  rw [hx.sum_filter_cliqueSets]
  exact hx.edge u v huv

/-- Constructing a fractional clique partition from edge constraints over `cliqueSets`. -/
theorem IsFracCliquePartition.of_cliqueSets {x : Finset V → ℝ} (h0 : ∀ Q, 0 ≤ x Q)
    (hs : ∀ Q, x Q ≠ 0 → 2 ≤ Q.card ∧ G.IsClique (Q : Set V))
    (he : ∀ u v, G.Adj u v → ∑ Q ∈ G.cliqueSets with (u ∈ Q ∧ v ∈ Q), x Q = 1) :
    G.IsFracCliquePartition x := by
  have hzero : ∀ Q, Q ∉ G.cliqueSets → x Q = 0 := fun Q hQ => by
    by_contra h
    exact hQ (mem_cliqueSets.mpr (hs Q h))
  refine ⟨h0, hs, fun u v huv => ?_⟩
  rw [← he u v huv, sum_filter, sum_filter]
  exact (sum_subset (subset_univ _) fun Q _ hQ => by simp [hzero Q hQ]).symm

theorem fracCliquePartitionNumber_le_sum_cliqueSets {x : Finset V → ℝ} (hx :
  G.IsFracCliquePartition x) :
    G.fracCliquePartitionNumber ≤ ∑ Q ∈ G.cliqueSets, x Q := by
  rw [hx.sum_cliqueSets]
  exact fracCliquePartitionNumber_le hx

theorem fracCliquePartitionNumber_eq_of_cliqueSets {r : ℝ}
    (hlow : ∀ x, G.IsFracCliquePartition x → r ≤ ∑ Q ∈ G.cliqueSets, x Q)
    {x : Finset V → ℝ} (hx : G.IsFracCliquePartition x) (hxr : ∑ Q ∈ G.cliqueSets, x Q = r) :
    G.fracCliquePartitionNumber = r :=
  fracCliquePartitionNumber_eq_of (fun y hy => (hlow y hy).trans_eq hy.sum_cliqueSets)
    hx (hx.sum_cliqueSets ▸ hxr)

theorem le_fracCliquePartitionNumber_of_cliqueSets {r : ℝ}
    (h : ∀ x, G.IsFracCliquePartition x → r ≤ ∑ Q ∈ G.cliqueSets, x Q) : r
      ≤ G.fracCliquePartitionNumber :=
  le_fracCliquePartitionNumber fun x hx => (h x hx).trans_eq hx.sum_cliqueSets

end SimpleGraph
