/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.CutPartnerCount
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dense-graph estimates for Dross cuts

The K₄ partner count and the triangle-through-edge count are bounded using
minimum degree. Finite convex averaging supplies the cut-level estimate.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Convex averaging (finite Jensen for `T ↦ T(T − c₀)`).** For a nonempty finite `A`, the sum
of `T e (T e − c₀)` dominates `|A|` times `T_A (T_A − c₀)` with `T_A` the average. (Proved via
Cauchy–Schwarz; the linear part cancels exactly.) -/
public theorem convex_avg {α : Type*} {A : Finset α} (hA : A.Nonempty) (T : α → ℝ) (c₀ : ℝ) :
    (A.card : ℝ) * ((∑ e ∈ A, T e / A.card) * ((∑ e ∈ A, T e / A.card) - c₀))
      ≤ ∑ e ∈ A, T e * (T e - c₀) := by
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast (Finset.card_pos.mpr hA)
  have havg_sq := (sum_div_card_sq_le_sum_sq_div_card (s := A) (f := T))
  have havg : (∑ e ∈ A, T e / A.card) = (∑ e ∈ A, T e) / A.card := by rw [Finset.sum_div]
  have hlin : (A.card : ℝ) * ((∑ e ∈ A, T e) / A.card) = ∑ e ∈ A, T e := by field_simp
  have hquad : (A.card : ℝ) * (((∑ e ∈ A, T e) / A.card) ^ 2) ≤ ∑ e ∈ A, T e ^ 2 := by
    calc _ ≤ (A.card : ℝ) * ((∑ e ∈ A, T e ^ 2) / A.card) :=
            mul_le_mul_of_nonneg_left havg_sq hcard.le
      _ = _ := by field_simp
  have hlhs : (A.card : ℝ) * ((∑ e ∈ A, T e / A.card) * ((∑ e ∈ A, T e / A.card) - c₀))
      = (A.card : ℝ) * (((∑ e ∈ A, T e) / A.card) ^ 2) - c₀ * (∑ e ∈ A, T e) := by
    rw [havg]
    calc _ = (A.card : ℝ) * (((∑ e ∈ A, T e) / A.card) ^ 2)
              - c₀ * ((A.card : ℝ) * ((∑ e ∈ A, T e) / A.card)) := by ring
      _ = _ := by rw [hlin]
  have hexpand : (∑ e ∈ A, T e * (T e - c₀)) = (∑ e ∈ A, T e ^ 2) - c₀ * (∑ e ∈ A, T e) := by
    simp_rw [mul_sub, mul_comm (T _) c₀, ← pow_two]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hlhs, hexpand]; linarith

/-- **Codegree lower bound.** In a dense graph (`δ ≥ (9/10)n`), adjacent vertices have at least
`(8/10)n` common neighbours — Dross's `Tₑ ≥ n − 2δn` bound (`δ = 1/10`). -/
public theorem codeg_ge_of_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (u v : V) :
    8 * Fintype.card V ≤ 10 * codeg G u v := by
  have hdu : 9 * Fintype.card V ≤ 10 * G.degree u :=
    le_trans h (by simpa using Nat.mul_le_mul_left 10 (G.minDegree_le_degree u))
  have hdv : 9 * Fintype.card V ≤ 10 * G.degree v :=
    le_trans h (by simpa using Nat.mul_le_mul_left 10 (G.minDegree_le_degree v))
  have hun : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V :=
    le_trans (Finset.card_le_univ _) (le_of_eq Finset.card_univ)
  have hsum := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hsum
  rw [codeg]
  omega

/-- **A6 in real form, per edge.** For an edge `uv`, the K₄ count through it dominates
`Tₑ(Tₑ − n/10)/2` (`Tₑ = triThrough`). Combines A6 (`k4_lower_bound`), `triThrough_edge`, and
the codegree bound, with the Nat→ℝ casting justified by `codeg ≥ d`. -/
public theorem numK4_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) {u v : V} (huv : G.Adj u v) :
    (triThrough G (s(u, v)) : ℝ) * ((triThrough G (s(u, v)) : ℝ) - (Fintype.card V : ℝ) / 10)
      ≤ 2 * (numK4Through G u v : ℝ) := by
  set d := Fintype.card V - G.minDegree with hd
  have hddef : ∀ w, Fintype.card V - G.degree w ≤ d :=
    fun w => Nat.sub_le_sub_left (G.minDegree_le_degree w) _
  have hA6 := k4_lower_bound G (u := u) (v := v) d hddef
  have hcodeg := codeg_ge_of_dense G h u v
  have hmc : G.minDegree ≤ Fintype.card V :=
    le_trans (G.minDegree_le_degree u)
      (by rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_univ _)
  have hd_le : 10 * d ≤ Fintype.card V := by omega
  have hcd : d ≤ codeg G u v := by omega
  rw [triThrough_edge G huv]
  rw [← Nat.cast_le (α := ℝ)] at hA6
  push_cast [Nat.cast_sub hcd] at hA6
  have hd_real : (d : ℝ) ≤ (Fintype.card V : ℝ) / 10 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
    calc (d : ℝ) * 10 = ((10 * d : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Fintype.card V : ℝ) := by exact_mod_cast hd_le
  have hnn : (0 : ℝ) ≤ (codeg G u v : ℝ) := by positivity
  nlinarith [hA6, mul_nonneg hnn (show (0 : ℝ) ≤ (Fintype.card V : ℝ) / 10 - d by linarith)]

/-- **A6 in real form, per edge, with an arbitrary deficiency `δ`.** Generalises `numK4_lower`:
for any `δ` bounding the max non-degree ratio (`n − minDegree ≤ δ·n`),
`Tₑ(Tₑ − δn) ≤ 2·numK4Through`.
Used with the tighter `δ = 1/10 − ε` in the ε-reparametrisation. -/
public theorem numK4_lower_delta (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) (δ : ℝ)
    (hδ_deg : (Fintype.card V : ℝ) - G.minDegree ≤ δ * Fintype.card V)
    {u v : V} (huv : G.Adj u v) :
    (triThrough G (s(u, v)) : ℝ) * ((triThrough G (s(u, v)) : ℝ) - δ * (Fintype.card V : ℝ))
      ≤ 2 * (numK4Through G u v : ℝ) := by
  set d := Fintype.card V - G.minDegree with hd
  have hddef : ∀ w, Fintype.card V - G.degree w ≤ d :=
    fun w => Nat.sub_le_sub_left (G.minDegree_le_degree w) _
  have hA6 := k4_lower_bound G (u := u) (v := v) d hddef
  have hcodeg := codeg_ge_of_dense G h u v
  have hmc : G.minDegree ≤ Fintype.card V :=
    le_trans (G.minDegree_le_degree u)
      (by rw [← G.card_neighborFinset_eq_degree]; exact Finset.card_le_univ _)
  have hd_le : 10 * d ≤ Fintype.card V := by omega
  have hcd : d ≤ codeg G u v := by omega
  rw [triThrough_edge G huv]
  rw [← Nat.cast_le (α := ℝ)] at hA6
  push_cast [Nat.cast_sub hcd] at hA6
  have hd_real : (d : ℝ) ≤ δ * (Fintype.card V : ℝ) := by
    rw [hd, Nat.cast_sub hmc]; exact hδ_deg
  have hnn : (0 : ℝ) ≤ (codeg G u v : ℝ) := by positivity
  nlinarith [hA6, mul_nonneg hnn (show (0 : ℝ) ≤ δ * (Fintype.card V : ℝ) - d by linarith)]

/-- **Per-edge `Tₑ` bounds.** In a dense graph, every edge lies in between `(8/10)n` and `n`
triangles. -/
public theorem triThrough_bounds (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree) {u v : V} (huv : G.Adj u v) :
    (8 / 10) * (Fintype.card V : ℝ) ≤ (triThrough G (s(u, v)) : ℝ)
      ∧ (triThrough G (s(u, v)) : ℝ) ≤ (Fintype.card V : ℝ) := by
  rw [triThrough_edge G huv]
  refine ⟨?_, ?_⟩
  · have hc : (8 : ℝ) * Fintype.card V ≤ 10 * codeg G u v := by
      exact_mod_cast codeg_ge_of_dense G h u v
    linarith
  · have hc : codeg G u v ≤ Fintype.card V := by
      rw [codeg]; exact le_trans (Finset.card_le_univ _) (le_of_eq Finset.card_univ)
    exact_mod_cast hc

/-- **Per-edge `Tₑ` bounds with an arbitrary deficiency `δ`.** `Tₑ ∈ [(1−2δ)n, n]` from
`codeg ≥ 2·minDegree − n ≥ (1−2δ)n`. Used in the ε-reparametrisation (tighter than `0.8n`). -/
public theorem triThrough_bounds_delta (G : SimpleGraph V) [DecidableRel G.Adj] (δ : ℝ)
    (hδ_deg : (Fintype.card V : ℝ) - G.minDegree ≤ δ * Fintype.card V)
    {u v : V} (huv : G.Adj u v) :
    (1 - 2 * δ) * (Fintype.card V : ℝ) ≤ (triThrough G (s(u, v)) : ℝ)
      ∧ (triThrough G (s(u, v)) : ℝ) ≤ (Fintype.card V : ℝ) := by
  rw [triThrough_edge G huv]
  refine ⟨?_, ?_⟩
  · have hie : G.degree u + G.degree v ≤ Fintype.card V + codeg G u v := by
      rw [codeg]
      have hun : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ Fintype.card V :=
        le_trans (Finset.card_le_univ _) (le_of_eq Finset.card_univ)
      have hsum := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
      rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hsum
      omega
    have hdu : G.minDegree ≤ G.degree u := G.minDegree_le_degree u
    have hdv : G.minDegree ≤ G.degree v := G.minDegree_le_degree v
    have hier : (G.degree u : ℝ) + G.degree v ≤ Fintype.card V + codeg G u v := by
      exact_mod_cast hie
    have hdur : (G.minDegree : ℝ) ≤ G.degree u := by exact_mod_cast hdu
    have hdvr : (G.minDegree : ℝ) ≤ G.degree v := by exact_mod_cast hdv
    nlinarith [hier, hdur, hdvr, hδ_deg]
  · have hc : codeg G u v ≤ Fintype.card V := by
      rw [codeg]; exact le_trans (Finset.card_le_univ _) (le_of_eq Finset.card_univ)
    exact_mod_cast hc

end LeanPool.DrossFractionalTriangleDecomposition
