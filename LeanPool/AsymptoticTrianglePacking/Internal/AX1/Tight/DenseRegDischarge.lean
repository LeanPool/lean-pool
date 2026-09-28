/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Dense near-regularity of the triangle hypergraph (proved core of the `hReg` /
AX1-second-stage obligation)

`Nibble.AX1.NearRegObligationLinearSized` is stated for ALL graphs, which is too strong (sparse
graphs give the triangle hypergraph too many codegree-0 edges for a fixed exceptional fraction).
The mathematically true and needed content is the DENSE case: for `δ(G) ≥ (9/10)·n` the triangle
hypergraph is genuinely near-`d`-regular with `d = n`, band `μ = 1/5`, and an EMPTY exceptional set
(`η = 0`).  This file discharges exactly that, unconditionally, via
`Nibble.YusterE.triangleSub_linearSized_data_of_minDeg`.

It is the proved ingredient the AX1 reduction needs once it is repaired with a density case-split
(`NibbleGapReduction` currently applies the obligation to an arbitrary `G` — the confirmed gap).
Kept non-destructive: nothing existing is modified.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.DenseNearRegular

/-! # Tight.DenseRegDischarge -/

@[expose] public section

open Finset Hypergraph

namespace Nibble.YusterE

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Dense near-regularity, concrete window.**  For a graph whose minimum degree `D` satisfies
`9n ≤ 10D` (i.e. `δ(G) ≥ (9/10)n`) and `n ≥ 5`, the triangle hypergraph is nearly `d`-regular with
`d = n`, `μ = 1/5`, EMPTY exceptional set, codegree `≤ μd`, global ceiling `≤ (1+μ)d`, and the
linear
size bound `n ≤ 1·d`.  This is exactly the local data of `NearRegObligationLinearSized` with
`μ = 1/5, η = 0, L = 1, d = n`. -/
theorem triangleSub_dense_data (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hD : ∀ x, D ≤ G.degree x) (hDense : 9 * Fintype.card V ≤ 10 * D)
    (hn5 : 5 ≤ Fintype.card V) :
    NearlyRegularMost (triangleHypergraphSub G) (Fintype.card V : ℝ) (1 / 5) 0 ∧
      CodegreeBounded (triangleHypergraphSub G) ((1 / 5) * (Fintype.card V : ℝ)) ∧
      (∀ E : EdgeV G,
        (Hypergraph.degree (triangleHypergraphSub G) E : ℝ) ≤ (1 + 1 / 5) * (Fintype.card V : ℝ)) ∧
      (Fintype.card V : ℝ) ≤ 1 * (Fintype.card V : ℝ) := by
  have h5 : (5 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn5
  have hDR : (9 : ℝ) * (Fintype.card V : ℝ) ≤ 10 * (D : ℝ) := by exact_mod_cast hDense
  have h2D : Fintype.card V ≤ 2 * D := by
    have : (Fintype.card V : ℝ) ≤ 2 * (D : ℝ) := by linarith
    exact_mod_cast this
  refine triangleSub_linearSized_data_of_minDeg G D hD h2D (le_refl 0) ?_ ?_ ?_ ?_
  · -- hcodeg : 1 ≤ μ d = n/5
    nlinarith
  · -- hbase : n ≤ L d = 1·n
    rw [one_mul]
  · -- hlo : (1-μ) d = (4/5) n ≤ 2D - n
    nlinarith
  · -- hhi : n ≤ (1+μ) d = (6/5) n
    nlinarith

end Nibble.YusterE
