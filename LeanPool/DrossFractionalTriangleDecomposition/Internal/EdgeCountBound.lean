/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.DrossFractionalTriangleDecomposition.Internal.HighDegreeCount
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The exact edge-count bound

Split the degree sum into vertices of degree at least `minDegree + 2` and
the remaining vertices. The sharpened high-degree count supplies the
linear correction in Dross's exact cut inequality.
-/

namespace LeanPool.DrossFractionalTriangleDecomposition

open SimpleGraph Finset

variable {V : Type*} [Fintype V]

public theorem mbound_tight (G : SimpleGraph V) [DecidableRel G.Adj] (δ : ℝ)
    (h : 9 * Fintype.card V ≤ 10 * G.minDegree)
    (hn20 : 20 ≤ Fintype.card V)
    (hδeq : (Fintype.card V : ℝ) - G.minDegree = δ * (Fintype.card V : ℝ))
    (hδn2 : (2 : ℝ) ≤ δ * (Fintype.card V : ℝ))
    (hnb : ((Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v)).card : ℝ)
      ≤ 2 * δ * (Fintype.card V : ℝ) - 4) :
    2 * (G.edgeFinset.card : ℝ)
      ≤ (1 - δ + 2 * δ ^ 2) * (Fintype.card V : ℝ) ^ 2 + 4 + (Fintype.card V : ℝ)
        - 6 * δ * (Fintype.card V : ℝ) := by
  classical
  set Vb := Finset.univ.filter (fun v => G.minDegree + 2 ≤ G.degree v) with hVbdef
  have hdeg_le : ∀ v : V, G.degree v ≤ Fintype.card V - 1 :=
    degree_le_card_sub_one G
  have h2m : 2 * G.edgeFinset.card = ∑ v, G.degree v := by
    rw [← G.sum_degrees_eq_twice_card_edges]
  have hVbbound : ∑ v ∈ Vb, G.degree v ≤ Vb.card * (Fintype.card V - 1) := by
    calc
      ∑ v ∈ Vb, G.degree v ≤ ∑ _v ∈ Vb, (Fintype.card V - 1) :=
        Finset.sum_le_sum (fun v _ => hdeg_le v)
      _ = Vb.card * (Fintype.card V - 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hcompbound : ∑ v ∈ Vbᶜ, G.degree v ≤ Vbᶜ.card * (G.minDegree + 1) := by
    calc
      ∑ v ∈ Vbᶜ, G.degree v ≤ ∑ _v ∈ Vbᶜ, (G.minDegree + 1) := by
        apply Finset.sum_le_sum
        intro v hv
        simp only [hVbdef, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
          true_and, not_le] at hv
        omega
      _ = Vbᶜ.card * (G.minDegree + 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hcompcard : Vbᶜ.card = Fintype.card V - Vb.card := Finset.card_compl Vb
  have hVble : Vb.card ≤ Fintype.card V := Finset.card_le_univ _
  have h2mr : 2 * (G.edgeFinset.card : ℝ)
      ≤ (Vb.card : ℝ) * ((Fintype.card V : ℝ) - 1)
        + ((Fintype.card V : ℝ) - Vb.card) * ((G.minDegree : ℝ) + 1) := by
    have hb1 : (∑ v ∈ Vb, G.degree v : ℝ)
        ≤ (Vb.card : ℝ) * ((Fintype.card V : ℝ) - 1) := by
      have hcast : ((Vb.card * (Fintype.card V - 1) : ℕ) : ℝ)
          = (Vb.card : ℝ) * ((Fintype.card V : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
        push_cast
        ring
      calc
        (∑ v ∈ Vb, G.degree v : ℝ) ≤ ((Vb.card * (Fintype.card V - 1) : ℕ) : ℝ) := by
          exact_mod_cast hVbbound
        _ = _ := hcast
    have hb2 : (∑ v ∈ Vbᶜ, G.degree v : ℝ)
        ≤ ((Fintype.card V : ℝ) - Vb.card) * ((G.minDegree : ℝ) + 1) := by
      have hcast : ((Vbᶜ.card * (G.minDegree + 1) : ℕ) : ℝ)
          = ((Fintype.card V : ℝ) - Vb.card) * ((G.minDegree : ℝ) + 1) := by
        rw [Nat.cast_mul, hcompcard, Nat.cast_sub hVble]
        push_cast
        ring
      calc
        (∑ v ∈ Vbᶜ, G.degree v : ℝ) ≤ ((Vbᶜ.card * (G.minDegree + 1) : ℕ) : ℝ) := by
          exact_mod_cast hcompbound
        _ = _ := hcast
    have h2mR : 2 * (G.edgeFinset.card : ℝ) = ∑ v, (G.degree v : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast h2m
    rw [h2mR, ← Finset.sum_add_sum_compl Vb (fun v => (G.degree v : ℝ))]
    linarith [hb1, hb2]
  have hmd : (G.minDegree : ℝ) = (Fintype.card V : ℝ) - δ * Fintype.card V := by
    linarith [hδeq]
  have hnR : (20 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn20
  have hVbleR : (Vb.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hVble
  have hmle : G.minDegree ≤ Fintype.card V := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
    exact le_trans (G.minDegree_le_degree v) (le_trans (hdeg_le v) (by omega))
  have hδn0 : (0 : ℝ) ≤ δ * (Fintype.card V : ℝ) := by
    rw [← hδeq]
    have hml : (G.minDegree : ℝ) ≤ Fintype.card V := by exact_mod_cast hmle
    linarith
  have hδsmall : δ * (Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ) / 10 := by
    rw [← hδeq]
    have hc : (9 : ℝ) * Fintype.card V ≤ 10 * G.minDegree := by exact_mod_cast h
    linarith
  have hVbmd : (Vb.card : ℝ) * (G.minDegree : ℝ)
      = (Vb.card : ℝ) * (Fintype.card V : ℝ)
        - (Vb.card : ℝ) * (δ * Fintype.card V) := by
    rw [hmd]
    ring
  have hnmd : (Fintype.card V : ℝ) * (G.minDegree : ℝ)
      = (Fintype.card V : ℝ) ^ 2 - δ * (Fintype.card V : ℝ) ^ 2 := by
    rw [hmd]
    ring
  nlinarith [h2mr, hnb, hmd, hnR, hVbleR, hδn0, hVbmd, hnmd, hδn2,
    mul_nonneg
      (show (0 : ℝ) ≤ 2 * δ * (Fintype.card V : ℝ) - 4 - (Vb.card : ℝ) by linarith [hnb])
      (show (0 : ℝ) ≤ δ * (Fintype.card V : ℝ) - 2 by linarith [hδn2]),
    mul_nonneg (show (0 : ℝ) ≤ (Vb.card : ℝ) by positivity) hδn0, hδsmall]

end LeanPool.DrossFractionalTriangleDecomposition
