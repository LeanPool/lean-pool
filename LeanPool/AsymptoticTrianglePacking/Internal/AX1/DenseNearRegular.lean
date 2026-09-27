/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — ② dense-regime global near-regularity of the triangle hypergraph

The corrected nibble needs a GLOBAL per-edge degree bound `∀ e, degree ≤ (1+μ)d` (not just majority),
because an exceptional high-degree vertex would inflate the variance parameter Δ. In Paper III's regime
this is FREE: at `δ(G) ≥ (9/10+ε)n` the triangle-per-edge count `|N(u)∩N(v)|` is globally in
`[(4/5+2ε)n, n]` — no exceptional set, no Szemerédi, no regularization. The window `[(1-μ)d,(1+μ)d]` at
`d ≈ (9/10)n` is covered with `μ ≈ 1/9 = 1 − 8/9`.

* `triangleSub_degree_eq_inter` — `degree_H({u,v}) = |N(u)∩N(v)|`.
* `triangleSub_degree_le_card` — global ceiling `degree ≤ |V|`.
* `triangleSub_degree_ge_of_minDeg` — floor `2·D − |V| ≤ degree` from a global min-degree `D`.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterSubDegreeChar
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.YusterSubRegular

/-! # DenseNearRegular -/

@[expose] public section

open Finset SimpleGraph Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The triangle-hypergraph degree of an edge `{u,v}` is the number of common neighbours. -/
theorem triangleSub_degree_eq_inter (E : EdgeV G) (u v : V) (huv : E.val = ({u, v} : Finset V)) :
    Hypergraph.degree (triangleHypergraphSub G) E
      = (G.neighborFinset u ∩ G.neighborFinset v).card := by
  have hE2 := SimpleGraph.mem_cliqueFinset_iff.mp E.2
  rw [huv] at hE2
  have huv_ne : u ≠ v := by
    rintro rfl
    have := hE2.card_eq
    simp at this
  have huv_adj : G.Adj u v :=
    hE2.1 (by simp : u ∈ ({u, v} : Finset V)) (by simp : v ∈ ({u, v} : Finset V)) huv_ne
  rw [triangleHypergraphSub_degree_eq_commonNbr]
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
    SimpleGraph.mem_neighborFinset, huv]
  constructor
  · rintro ⟨_, htri⟩
    rw [show insert c ({u, v} : Finset V) = ({c, u, v} : Finset V) from rfl,
      SimpleGraph.is3Clique_triple_iff] at htri
    exact ⟨htri.1.symm, htri.2.1.symm⟩
  · rintro ⟨hu, hv⟩
    have hcu : c ≠ u := by rintro rfl; simp at hu
    have hcv : c ≠ v := by rintro rfl; simp at hv
    refine ⟨by simp [hcu, hcv], ?_⟩
    rw [show insert c ({u, v} : Finset V) = ({c, u, v} : Finset V) from rfl,
      SimpleGraph.is3Clique_triple_iff]
    exact ⟨hu.symm, hv.symm, huv_adj⟩

/-- Every edge is a pair. -/
private theorem edgeV_eq_pair (E : EdgeV G) : ∃ u v : V, E.val = ({u, v} : Finset V) := by
  have h2 := (SimpleGraph.mem_cliqueFinset_iff.mp E.2).card_eq
  obtain ⟨u, v, _, huv⟩ := Finset.card_eq_two.mp h2
  exact ⟨u, v, huv⟩

/-- **② ceiling (global upper bound).** Every edge lies in at most `|V|` triangles. -/
theorem triangleSub_degree_le_card (E : EdgeV G) :
    Hypergraph.degree (triangleHypergraphSub G) E ≤ Fintype.card V := by
  obtain ⟨u, v, huv⟩ := edgeV_eq_pair G E
  rw [triangleSub_degree_eq_inter G E u v huv]
  calc (G.neighborFinset u ∩ G.neighborFinset v).card
      ≤ (Finset.univ : Finset V).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card V := Finset.card_univ

/-- **② floor (from a global min-degree bound).** If every vertex of `G` has degree `≥ D`, then every
edge lies in at least `2D − |V|` triangles (common-neighbourhood inclusion–exclusion). -/
theorem triangleSub_degree_ge_of_minDeg (E : EdgeV G) {D : ℕ} (hD : ∀ x, D ≤ G.degree x) :
    2 * D - Fintype.card V ≤ Hypergraph.degree (triangleHypergraphSub G) E := by
  obtain ⟨u, v, huv⟩ := edgeV_eq_pair G E
  rw [triangleSub_degree_eq_inter G E u v huv]
  have hincl : G.degree u + G.degree v - Fintype.card V
      ≤ (G.neighborFinset u ∩ G.neighborFinset v).card := by
    have h := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
    have hle : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    rw [← G.card_neighborFinset_eq_degree, ← G.card_neighborFinset_eq_degree v]
    omega
  have hDu := hD u
  have hDv := hD v
  omega

/-- **② global near-regularity window (packaged).** With a global min-degree `D` satisfying `|V| ≤ 2D`
(dense regime), every edge's triangle-degree lies in the window `[(1−μ)d, (1+μ)d]` provided the window
covers `[2D−|V|, |V|]`. This is the global (no exceptional set) near-regularity the corrected nibble
consumes; at `δ ≥ (9/10+ε)|V|`, taking `D = (9/10+ε)|V|`, `d = (9/10)|V|`, `μ = 1/9` satisfies the
hypotheses. -/
theorem triangleSub_degree_window (E : EdgeV G) (D : ℕ) (hD : ∀ x, D ≤ G.degree x)
    (h2D : Fintype.card V ≤ 2 * D) {μ d : ℝ}
    (hlo : (1 - μ) * d ≤ 2 * (D : ℝ) - (Fintype.card V : ℝ))
    (hhi : (Fintype.card V : ℝ) ≤ (1 + μ) * d) :
    (1 - μ) * d ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ∧
      (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d := by
  have hfloor := triangleSub_degree_ge_of_minDeg G E hD
  have hceil := triangleSub_degree_le_card G E
  have hcast : ((2 * D - Fintype.card V : ℕ) : ℝ) = 2 * (D : ℝ) - (Fintype.card V : ℝ) := by
    rw [Nat.cast_sub h2D]; push_cast; ring
  have hfloor' : 2 * (D : ℝ) - (Fintype.card V : ℝ)
      ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) := by
    rw [← hcast]; exact_mod_cast hfloor
  refine ⟨le_trans hlo hfloor', ?_⟩
  calc (Hypergraph.degree (triangleHypergraphSub G) E : ℝ)
      ≤ (Fintype.card V : ℝ) := by exact_mod_cast hceil
    _ ≤ (1 + μ) * d := hhi

/-- Dense-regime package for the corrected nibble input. A global degree window on every graph edge,
the trivial edge-hypergraph codegree bound, and a linear base-size estimate assemble the exact local
data required by `NearRegObligationLinearSized`. -/
theorem triangleSub_linearSized_data_of_window {μ η d L : ℝ}
    (hη : 0 ≤ η) (hcodeg : 1 ≤ μ * d) (hbase : (Fintype.card V : ℝ) ≤ L * d)
    (hwindow : ∀ E : EdgeV G,
      (1 - μ) * d ≤ (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ∧
        (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d) :
    NearlyRegularMost (triangleHypergraphSub G) d μ η ∧
      CodegreeBounded (triangleHypergraphSub G) (μ * d) ∧
      (∀ E : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d) ∧
      (Fintype.card V : ℝ) ≤ L * d := by
  refine ⟨?_, triangleHypergraphSub_codegreeBounded G hcodeg, ?_, hbase⟩
  · exact triangleHypergraphSub_nearlyRegularMost_of_bounds G ∅
      (by
        rw [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg hη (Nat.cast_nonneg _))
      (fun E _ => (hwindow E).1)
      (fun E _ => (hwindow E).2)
  · intro E
    exact (hwindow E).2

/-- Dense-regime package specialized to a minimum-degree floor `D`: the inclusion-exclusion window
`triangleSub_degree_window` feeds the local linear-sized corrected nibble data. -/
theorem triangleSub_linearSized_data_of_minDeg (D : ℕ) (hD : ∀ x, D ≤ G.degree x)
    (h2D : Fintype.card V ≤ 2 * D) {μ η d L : ℝ}
    (hη : 0 ≤ η) (hcodeg : 1 ≤ μ * d) (hbase : (Fintype.card V : ℝ) ≤ L * d)
    (hlo : (1 - μ) * d ≤ 2 * (D : ℝ) - (Fintype.card V : ℝ))
    (hhi : (Fintype.card V : ℝ) ≤ (1 + μ) * d) :
    NearlyRegularMost (triangleHypergraphSub G) d μ η ∧
      CodegreeBounded (triangleHypergraphSub G) (μ * d) ∧
      (∀ E : EdgeV G, (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + μ) * d) ∧
      (Fintype.card V : ℝ) ≤ L * d := by
  exact triangleSub_linearSized_data_of_window G hη hcodeg hbase
    (fun E => triangleSub_degree_window G E D hD h2D hlo hhi)

end Nibble.YusterE
