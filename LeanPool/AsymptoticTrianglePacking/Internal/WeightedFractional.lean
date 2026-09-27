/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Weighted hypergraph incidences

The fractional-rounding proof in Paper III uses edge weights rather than the unweighted
near-regular hypotheses of `nearRegularNibbleTheorem`. These definitions retain the exact
finite-set model of the frozen proof. The rounding theorem itself is not asserted here.
-/

@[expose] public section

open Finset

namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Total edge weight incident with a vertex. -/
def weightedLoad (H : Finset (Finset V)) (w : Finset V → ℝ) (v : V) : ℝ :=
  ∑ e ∈ H.filter (fun e => v ∈ e), w e

/-- Total edge weight incident with both vertices. -/
def weightedCodegree (H : Finset (Finset V)) (w : Finset V → ℝ) (u v : V) : ℝ :=
  ∑ e ∈ H.filter (fun e => u ∈ e ∧ v ∈ e), w e

/-- Weighted handshake for an `r`-uniform finite hypergraph. -/
theorem sum_weightedLoad (H : Finset (Finset V)) (w : Finset V → ℝ) {r : ℕ}
    (hr : IsUniform H r) :
    ∑ v : V, weightedLoad H w v = (r : ℝ) * ∑ e ∈ H, w e := by
  classical
  simp_rw [weightedLoad, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, hr e he, nsmul_eq_mul]

/-- Exact bounded-edge weighted-rounding target from the Paper III freeze.
This is a specification, not a proof or a public result. -/
def BoundedEdgeWeightedRounding : Prop :=
  ∀ (r : ℕ), 2 ≤ r → ∀ (β : ℝ), 0 < β →
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (H : Finset (Finset W)) (w : Finset W → ℝ),
        (∀ e ∈ H, e.Nonempty ∧ e.card ≤ r) →
        (∀ e, 0 ≤ w e) →
        (∀ v : W, weightedLoad H w v ≤ 1) →
        (∀ u v : W, u ≠ v → weightedCodegree H w u v ≤ γ) →
        ∃ M : Finset (Finset W), IsMatching H M ∧
          (1 - β) * (∑ e ∈ H, w e) - β * (Fintype.card W : ℝ) - C ≤ (M.card : ℝ)

end Hypergraph
