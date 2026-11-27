/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Sparse supports and total wager

The deterministic averaging estimate in Section 5 of Liu and Meng,
arXiv:2611.31004v1. If each position belongs to few candidate supports,
then the average total wager on a candidate is small. A square-sum bound
controls the total wager on the pool by Cauchy–Schwarz.

This file proves the estimate for an already supplied finite family.
It does not construct the sparse, rank-preserving family of Lemma 4.
-/

@[expose] public section

namespace Klr.Sparse

open scoped BigOperators

variable {α Q : Type*} [Fintype α] [Fintype Q]

/-- How many candidate supports contain a particular position. -/
def incidence [DecidableEq α] (S : Q → Finset α) (a : α) : ℕ :=
  (Finset.univ.filter (fun q => a ∈ S q)).card

/-- Double counting, with an arbitrary real weight on each pool position. -/
theorem sum_support_weights [DecidableEq α] (S : Q → Finset α) (w : α → ℝ) :
    (∑ q, ∑ a ∈ S q, w a) = ∑ a, (incidence S a : ℝ) * w a := by
  classical
  calc
    (∑ q, ∑ a ∈ S q, w a) = ∑ q, ∑ a, if a ∈ S q then w a else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Finset.sum_filter]
      simp
    _ = ∑ a, ∑ q, if a ∈ S q then w a else 0 := Finset.sum_comm
    _ = ∑ a, (incidence S a : ℝ) * w a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_filter]
      simp [incidence]

/-- The incidence bound controls the sum over all candidates. -/
theorem sum_support_weights_le [DecidableEq α] (S : Q → Finset α) (w : α → ℝ) (B : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hS : ∀ a, (incidence S a : ℝ) ≤ B) :
    (∑ q, ∑ a ∈ S q, w a) ≤ B * ∑ a, w a := by
  rw [sum_support_weights, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hS a) (hw a)

/-- Cauchy–Schwarz turns a square-sum budget into an ordinary sum budget. -/
theorem sum_weights_le_sqrt (w : α → ℝ) (C : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hC : ∑ a, (w a) ^ 2 ≤ C) :
    (∑ a, w a) ≤ Real.sqrt ((Fintype.card α : ℝ) * C) := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (s := (Finset.univ : Finset α)) (f := fun _ => (1 : ℝ)) (g := w)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hCS
  have hcard : 0 ≤ (Fintype.card α : ℝ) := Nat.cast_nonneg _
  have hsq : (∑ a, w a) ^ 2 ≤ (Fintype.card α : ℝ) * C :=
    hCS.trans (mul_le_mul_of_nonneg_left hC hcard)
  have hs : 0 ≤ ∑ a, w a := Finset.sum_nonneg fun a _ => hw a
  exact (Real.le_sqrt hs ((sq_nonneg _).trans hsq)).2 hsq

/-- Averaging over a nonempty candidate family. `δ` bounds the fraction of
candidates containing any one position. -/
theorem average_support_weights_le [DecidableEq α] [Nonempty Q]
    (S : Q → Finset α) (w : α → ℝ) (δ C : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hδ : 0 ≤ δ)
    (hS : ∀ a, (incidence S a : ℝ) ≤ δ * Fintype.card Q)
    (hC : ∑ a, (w a) ^ 2 ≤ C) :
    (∑ q, ∑ a ∈ S q, w a) / Fintype.card Q ≤
      δ * Real.sqrt ((Fintype.card α : ℝ) * C) := by
  have hQ : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hQ).2
  calc
    (∑ q, ∑ a ∈ S q, w a) ≤ (δ * Fintype.card Q) * ∑ a, w a :=
      sum_support_weights_le S w _ hw hS
    _ ≤ (δ * Fintype.card Q) * Real.sqrt ((Fintype.card α : ℝ) * C) :=
      mul_le_mul_of_nonneg_left (sum_weights_le_sqrt w C hw hC) (by positivity)
    _ = (δ * Real.sqrt ((Fintype.card α : ℝ) * C)) * Fintype.card Q := by ring

/-- Some candidate does at least as well as the average bound. -/
theorem exists_small_support [DecidableEq α] [Nonempty Q]
    (S : Q → Finset α) (w : α → ℝ) (δ C : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hδ : 0 ≤ δ)
    (hS : ∀ a, (incidence S a : ℝ) ≤ δ * Fintype.card Q)
    (hC : ∑ a, (w a) ^ 2 ≤ C) :
    ∃ q, (∑ a ∈ S q, w a) ≤ δ * Real.sqrt ((Fintype.card α : ℝ) * C) := by
  classical
  have havg := average_support_weights_le S w δ C hw hδ hS hC
  have hQ : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  by_contra hn
  push Not at hn
  have hsum : (Fintype.card Q : ℝ) * (δ * Real.sqrt ((Fintype.card α : ℝ) * C)) <
      ∑ q, ∑ a ∈ S q, w a := by
    simpa using Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun q _ => hn q)
  have := (div_le_iff₀ hQ).mp havg
  nlinarith

end Klr.Sparse
