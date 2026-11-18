/-
Copyright (c) 2026 Marcel Blattner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Blattner
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic.Ring

/-!
# Matching polynomials of weighted paths

`Dv s j` is the matching polynomial of the path with `j` vertices `0, …, j-1` in which the edge
between `i` and `i + 1` carries the weight `s i`:

  Dv s j = ∑ over matchings M of the path, (∏_{e ∈ M} s e) · X ^ |M|.

It is defined by the recurrence obtained from the last vertex (unmatched, or matched to its
left neighbour).
-/

@[expose] public section

open Polynomial Finset

namespace Corless

/-- Matching polynomial of the path with `j` vertices and edge weights `s 0, s 1, …`. -/
noncomputable def Dv (s : ℕ → ℤ) : ℕ → ℤ[X]
  | 0 => 1
  | 1 => 1
  | (j + 2) => Dv s (j + 1) + C (s j) * X * Dv s j

@[simp] lemma Dv_zero (s : ℕ → ℤ) : Dv s 0 = 1 := by rw [Dv]
@[simp] lemma Dv_one (s : ℕ → ℤ) : Dv s 1 = 1 := by rw [Dv]

lemma Dv_succ_succ (s : ℕ → ℤ) (j : ℕ) :
    Dv s (j + 2) = Dv s (j + 1) + C (s j) * X * Dv s j := by
  rw [Dv]

/-- `Dv s j` only depends on the weights of the `j - 1` edges of the path. -/
lemma Dv_congr {s t : ℕ → ℤ} : ∀ {j : ℕ}, (∀ i, i + 1 < j → s i = t i) → Dv s j = Dv t j
  | 0, _ => by simp
  | 1, _ => by simp
  | j + 2, h => by
      rw [Dv_succ_succ, Dv_succ_succ, Dv_congr (j := j + 1) (fun i hi => h i (by omega)),
        Dv_congr (j := j) (fun i hi => h i (by omega)), h j (by omega)]

/-- Splitting the path at the edge `k` (between the vertices `k` and `k + 1`): matchings either
avoid the edge (left part times right part) or use it. -/
lemma Dv_split (s : ℕ → ℤ) (k : ℕ) : ∀ m : ℕ,
    Dv s (k + m + 2) = Dv s (k + 1) * Dv (fun i => s (i + k + 1)) (m + 1)
      + C (s k) * X * Dv s k * Dv (fun i => s (i + k + 2)) m
  | 0 => by simp [Dv_succ_succ]
  | 1 => by
      have e : s (0 + k + 1) = s (k + 1) := by congr 1; omega
      rw [Dv_succ_succ, Dv_succ_succ s k,
        show (1 : ℕ) + 1 = 0 + 2 by rfl, Dv_succ_succ (fun i => s (i + k + 1)) 0, e]
      simp only [Dv_zero, zero_add, Dv_one]
      ring
  | m + 2 => by
      have h1 := Dv_split s k (m + 1)
      have h0 := Dv_split s k m
      have e1 : s (m + 1 + k + 1) = s (k + m + 2) := by congr 1; omega
      have e2 : s (m + k + 2) = s (k + m + 2) := by congr 1; omega
      rw [show k + (m + 2) + 2 = (k + m + 2) + 2 by omega, Dv_succ_succ,
        show (k + m + 2) + 1 = k + (m + 1) + 2 by omega,
        show m + 2 + 1 = (m + 1) + 2 by omega, Dv_succ_succ (fun i => s (i + k + 1)) (m + 1),
        Dv_succ_succ (fun i => s (i + k + 2)) m, e1, e2, h1, h0]
      ring

/-- The recurrence from the first vertex. -/
lemma Dv_succ_succ_left (s : ℕ → ℤ) (m : ℕ) :
    Dv s (m + 2) = Dv (fun i => s (i + 1)) (m + 1) + C (s 0) * X * Dv (fun i => s (i + 2)) m := by
  have h := Dv_split s 0 m
  simp only [zero_add, Dv_one, Dv_zero, one_mul, mul_one, add_zero] at h
  rw [h]

/-- Reversing the path does not change its matching polynomial. -/
lemma Dv_reverse (s : ℕ → ℤ) : ∀ j : ℕ, Dv (fun i => s (j - 2 - i)) j = Dv s j
  | 0 => by simp
  | 1 => by simp
  | j + 2 => by
      rw [Dv_succ_succ, Dv_succ_succ_left s j]
      have h1 : Dv (fun i => s (j + 2 - 2 - i)) (j + 1) = Dv (fun i => s (i + 1)) (j + 1) := by
        rw [← Dv_reverse (fun i => s (i + 1)) (j + 1)]
        apply Dv_congr
        intro i hi
        congr 1
        omega
      have h0 : Dv (fun i => s (j + 2 - 2 - i)) j = Dv (fun i => s (i + 2)) j := by
        rw [← Dv_reverse (fun i => s (i + 2)) j]
        apply Dv_congr
        intro i hi
        congr 1
        omega
      have e : s (j + 2 - 2 - j) = s 0 := by congr 1; omega
      rw [h1, h0, e]

end Corless
