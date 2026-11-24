/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring

/-!
# Finite products of contractions

The difference between an ordered product of contractions and its linear part
has a quadratic bound. The proof uses the contraction of each factor, without
assuming multiplicativity of the norm or a normalized identity.

## Main definitions

* `FQFP.contractionProduct`: partial products with later factors on the left.

## Main results

* `FQFP.norm_contractionProduct_sub_one_le`: the linear telescoping bound.
* `FQFP.norm_contractionProduct_sub_one_sub_sum_le`: the quadratic remainder bound.
-/

@[expose] public section

open Finset

namespace FQFP

variable {A : Type*}

section Algebra

variable [NonAssocSemiring A]

/-- Ordered partial products, with later increments multiplying on the left. -/
def contractionProduct (D : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => (1 + D n) * contractionProduct D n

@[simp]
lemma contractionProduct_zero (D : ℕ → A) : contractionProduct D 0 = 1 := rfl

@[simp]
lemma contractionProduct_succ (D : ℕ → A) (n : ℕ) :
    contractionProduct D (n + 1) = (1 + D n) * contractionProduct D n := rfl

/-- A recursively specified product agrees with the ordered partial product. -/
lemma eq_contractionProduct_of_recurrence (D P : ℕ → A) (h0 : P 0 = 1)
    (hs : ∀ k, P (k + 1) = (1 + D k) * P k) (n : ℕ) :
    P n = contractionProduct D n := by
  induction n with
  | zero => exact h0
  | succ n ih => rw [hs, ih, contractionProduct_succ]

end Algebra

variable [NormedRing A]

/-- Telescoping bounds the distance of a product of contractions from the identity. -/
theorem norm_contractionProduct_sub_one_le (D : ℕ → A) {δ : ℝ}
    (hf : ∀ k, ‖1 + D k‖ ≤ 1) (hD : ∀ k, ‖D k‖ ≤ δ) (n : ℕ) :
    ‖contractionProduct D n - 1‖ ≤ (n : ℝ) * δ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ‖(1 + D n) * (contractionProduct D n - 1) + D n‖ := by
        congr 1
        rw [contractionProduct_succ]
        noncomm_ring
      _ ≤ ‖(1 + D n) * (contractionProduct D n - 1)‖ + ‖D n‖ := norm_add_le _ _
      _ ≤ 1 * ((n : ℝ) * δ) + δ :=
        add_le_add (norm_mul_le_of_le (hf n) ih) (hD n)
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_one]
        ring

/-- The nonlinear part of a finite contraction product is at most a quadratic binomial bound. -/
theorem norm_contractionProduct_sub_one_sub_sum_le (D : ℕ → A) {δ : ℝ}
    (hf : ∀ k, ‖1 + D k‖ ≤ 1) (hD : ∀ k, ‖D k‖ ≤ δ) (n : ℕ) :
    ‖contractionProduct D n - 1 - ∑ k ∈ range n, D k‖ ≤
      (n : ℝ) * ((n : ℝ) - 1) / 2 * δ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ‖(contractionProduct D n - 1 - ∑ k ∈ range n, D k) +
          D n * (contractionProduct D n - 1)‖ := by
        congr 1
        rw [contractionProduct_succ, sum_range_succ]
        noncomm_ring
      _ ≤ ‖contractionProduct D n - 1 - ∑ k ∈ range n, D k‖ +
          ‖D n * (contractionProduct D n - 1)‖ := norm_add_le _ _
      _ ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 * δ ^ 2 + δ * ((n : ℝ) * δ) :=
        add_le_add ih (norm_mul_le_of_le (hD n)
          (norm_contractionProduct_sub_one_le D hf hD n))
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_one]
        ring

end FQFP
