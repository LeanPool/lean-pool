/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — two counting bounds for the cluster-triple LP

The coarse-cell reduction of `Nibble.AX1.BlockCoverResidualCoupled` needs to control two totals of a
feasible point `y` of the cluster-triple LP (`Nibble.ClusterTripleLP`):

* `Nibble.AX1.clusterLPValue_le_sq` — its **value** is at most `|V|²/6`, since every triple is
  charged to its six ordered cluster pairs and the capacities add up to at most `|V|²`;
* `Nibble.AX1.sum_sparse_triples_le` — the weight carried by the triples that use a cluster pair of
  density below `δ` is at most `δ|V|²/2`: these are the triples the construction discards, and this
  is the only place where the hypothesis `δ ≤ ε` of the residual is consumed.

Both come from the same fibre identity `Nibble.AX1.sum_pair_fibers`, which rewrites a sum of the LP
pair sums over any set of ordered cluster pairs as a sum over triples weighted by the number of
pairs of the set they contain.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.ClusterTripleLP

/-! # ClusterTripleLPCount -/

@[expose] public section

open Finset SimpleGraph

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The fibre identity.**  Summing the LP mass through the pairs of a set `F` of ordered cluster
pairs charges every triple with the number of pairs of `F` it contains. -/
theorem sum_pair_fibers (P : Finpartition (univ : Finset V))
    (y : Finset {S : Finset V // S ∈ P.parts} → ℝ)
    (F : Finset ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts})) :
    ∑ p ∈ F, ∑ th ∈ triplesThrough P p.1 p.2, y th
      = ∑ th, y th * (#(F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th)) : ℝ) := by
  classical
  have h1 : ∀ p ∈ F, ∑ th ∈ triplesThrough P p.1 p.2, y th
      = ∑ th, (if p.1 ∈ th ∧ p.2 ∈ th then y th else 0) := by
    intro p _
    rw [triplesThrough, Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun th _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The sizes of two clusters multiply out to at most `|V|²` over all ordered pairs. -/
theorem sum_card_mul_card_le (P : Finpartition (univ : Finset V)) :
    ∑ p ∈ (univ : Finset ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts})),
        (#(p.1 : Finset V) : ℝ) * (#(p.2 : Finset V) : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hsum : ∑ S : {S : Finset V // S ∈ P.parts}, (#(S : Finset V) : ℝ)
      = (Fintype.card V : ℝ) := by
    have h : ∑ S ∈ P.parts, #S = Fintype.card V := by
      rw [P.sum_card_parts, Finset.card_univ]
    have h2 : ∑ S : {S : Finset V // S ∈ P.parts}, (#(S : Finset V) : ℝ)
        = ∑ S ∈ P.parts, (#S : ℝ) := by
      rw [← Finset.sum_attach P.parts (fun S => (#S : ℝ))]
      rfl
    rw [h2]
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h
  have hprod : ∑ p ∈ (univ : Finset ({S : Finset V // S ∈ P.parts} ×
        {S : Finset V // S ∈ P.parts})), (#(p.1 : Finset V) : ℝ) * (#(p.2 : Finset V) : ℝ)
      = (∑ S : {S : Finset V // S ∈ P.parts}, (#(S : Finset V) : ℝ)) *
          (∑ T : {S : Finset V // S ∈ P.parts}, (#(T : Finset V) : ℝ)) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
  rw [hprod, hsum]
  exact le_of_eq (by ring)

/-- The pair capacities of a subset of ordered pairs, bounded by a density bound. -/
private theorem sum_cap_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V))
    (F : Finset ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts})) {d : ℝ}
    (hd : ∀ p ∈ F, (G.edgeDensity (p.1 : Finset V) (p.2 : Finset V) : ℝ) ≤ d) (hd0 : 0 ≤ d) :
    ∑ p ∈ F, clusterPairCap G (p.1 : Finset V) (p.2 : Finset V)
      ≤ d * (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hstep : ∀ p ∈ F, clusterPairCap G (p.1 : Finset V) (p.2 : Finset V)
      ≤ d * ((#(p.1 : Finset V) : ℝ) * (#(p.2 : Finset V) : ℝ)) := by
    intro p hp
    rw [clusterPairCap, mul_assoc]
    exact mul_le_mul_of_nonneg_right (hd p hp) (by positivity)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hd0
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    (fun p _ _ => by positivity)) ?_
  exact sum_card_mul_card_le P

/-- The ordered pairs of distinct clusters inside a triple: the off-diagonal of the triple. -/
private theorem filter_pairs_eq_offDiag (P : Finpartition (univ : Finset V))
    (th : Finset {S : Finset V // S ∈ P.parts}) :
    ((univ : Finset ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts})).filter
        (fun p => p.1 ≠ p.2)).filter (fun p => p.1 ∈ th ∧ p.2 ∈ th) = th.offDiag := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
  tauto

/-- **The value of a feasible point of the cluster-triple LP is at most `|V|²/6`.** -/
theorem clusterLPValue_le_sq (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ)
    {y : Finset {S : Finset V // S ∈ P.parts} → ℝ} (hy : IsClusterTripleLP G P ep de y) :
    6 * clusterLPValue y ≤ (Fintype.card V : ℝ) ^ 2 := by
  classical
  set F := (univ : Finset ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts})).filter
    (fun p => p.1 ≠ p.2) with hFdef
  -- every triple in the support has exactly six ordered pairs
  have hcount : ∀ th, y th * 6 ≤ y th * (#(F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th)) : ℝ) := by
    intro th
    by_cases hz : y th = 0
    · simp [hz]
    · have htri := hy.2.1 th hz
      have hcard : #th = 3 := (SimpleGraph.mem_cliqueFinset_iff.mp htri).card_eq
      have heq : #(F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th)) = 6 := by
        rw [hFdef, filter_pairs_eq_offDiag, Finset.offDiag_card, hcard]
      rw [heq]
      norm_num
  have hsum : 6 * clusterLPValue y ≤ ∑ p ∈ F, ∑ th ∈ triplesThrough P p.1 p.2, y th := by
    rw [sum_pair_fibers P y F, clusterLPValue, Finset.mul_sum]
    refine Finset.sum_le_sum fun th _ => ?_
    have := hcount th
    linarith only [this]
  refine le_trans hsum ?_
  refine le_trans (Finset.sum_le_sum (fun p hp => hy.2.2 p.1 p.2 ?_)) ?_
  · exact (Finset.mem_filter.mp hp).2
  · refine sum_cap_le G P F (d := 1) (fun p _ => ?_) zero_le_one |>.trans_eq (by ring)
    exact_mod_cast G.edgeDensity_le_one (p.1 : Finset V) (p.2 : Finset V)

/-- The triples of the LP that use a cluster pair of density below `δ`. -/
noncomputable def sparseTriples (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (δ : ℝ) :
    Finset (Finset {S : Finset V // S ∈ P.parts}) :=
  univ.filter (fun th => ∃ S ∈ th, ∃ T ∈ th, S ≠ T ∧
    (G.edgeDensity (S : Finset V) (T : Finset V) : ℝ) < δ)

/-- **The mass of the triples using a sparse cluster pair is at most `δ|V|²/2`.**  Every such triple
contains at least two ordered pairs of density below `δ`, and the capacities of those pairs add up
to at most `δ|V|²`. -/
theorem sum_sparse_triples_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    {y : Finset {S : Finset V // S ∈ P.parts} → ℝ} (hy : IsClusterTripleLP G P ep de y) :
    2 * ∑ th ∈ sparseTriples G P δ, y th ≤ δ * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set F := (univ : Finset ({S : Finset V // S ∈ P.parts} × {S : Finset V // S ∈ P.parts})).filter
    (fun p => p.1 ≠ p.2 ∧ (G.edgeDensity (p.1 : Finset V) (p.2 : Finset V) : ℝ) < δ) with hFdef
  -- a sparse triple contains at least two ordered sparse pairs
  have hcount : ∀ th ∈ sparseTriples G P δ,
      2 ≤ (#(F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th)) : ℝ) := by
    intro th hth
    obtain ⟨S, hS, T, hT, hST, hd⟩ := (Finset.mem_filter.mp hth).2
    have hd' : (G.edgeDensity (T : Finset V) (S : Finset V) : ℝ) < δ := by
      rwa [SimpleGraph.edgeDensity_comm]
    have hmem1 : (S, T) ∈ F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th) := by
      simp only [hFdef, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hST, hd⟩, hS, hT⟩
    have hmem2 : (T, S) ∈ F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th) := by
      simp only [hFdef, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hST.symm, hd'⟩, hT, hS⟩
    have hsub : ({(S, T), (T, S)} : Finset _) ⊆ F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th) := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact hmem1
      · rw [Finset.mem_singleton.mp hp']
        exact hmem2
    have hcard2 : #({(S, T), (T, S)} : Finset _) = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Prod.ext_iff]; tauto), Finset.card_singleton]
    have := Finset.card_le_card hsub
    rw [hcard2] at this
    exact_mod_cast this
  have hynn : ∀ th, 0 ≤ y th := hy.1
  have hstep : 2 * ∑ th ∈ sparseTriples G P δ, y th
      ≤ ∑ th, y th * (#(F.filter (fun p => p.1 ∈ th ∧ p.2 ∈ th)) : ℝ) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun th hth => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (sparseTriples G P δ))
        (fun th _ _ => mul_nonneg (hynn th) (by positivity)))
    have h := hcount th hth
    have := mul_le_mul_of_nonneg_left h (hynn th)
    linarith only [this]
  rw [← sum_pair_fibers P y F] at hstep
  refine le_trans hstep ?_
  refine le_trans (Finset.sum_le_sum (fun p hp => hy.2.2 p.1 p.2 ?_)) ?_
  · exact (Finset.mem_filter.mp hp).2.1
  · exact sum_cap_le G P F (fun p hp => le_of_lt (Finset.mem_filter.mp hp).2.2) hδ0

end Nibble.AX1
