/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import Mathlib.NumberTheory.Chebyshev

/-!
# Analytic estimates for multiplicative block constructions

Elementary logarithm and prime-count bounds used by both lower-bound constructions.
-/

open Finset Real

@[expose] public section

namespace RunsOfMultiples

lemma log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : log x ≤ 2 * √x := by
  have h1 : log √x = log x / 2 := log_sqrt (by linarith)
  have h2 : log √x ≤ √x - 1 := log_le_sub_one_of_pos (sqrt_pos.2 (by linarith))
  linarith

lemma log_sq_le {x : ℝ} (hx : 1 ≤ x) : log x ^ 2 ≤ 16 * √x := by
  have hs : 1 ≤ √x := by rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt hx
  have h1 : log x = 4 * log √(√x) := by
    rw [log_sqrt (sqrt_nonneg _), log_sqrt (by linarith)]; ring
  have h2 : log √(√x) ≤ √(√x) - 1 := log_le_sub_one_of_pos (sqrt_pos.2 (by linarith))
  have h3 : √(√x) ^ 2 = √x := sq_sqrt (sqrt_nonneg _)
  have h4 : 0 ≤ log √(√x) := log_nonneg (by rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt hs)
  have h5 : log √(√x) ^ 2 ≤ √(√x) ^ 2 := pow_le_pow_left₀ h4 (by linarith) 2
  rw [h1]
  nlinarith

lemma sqrt_le_div_log {x : ℝ} (hx : 1 < x) : √x ≤ 2 * (x / log x) := by
  have hl : 0 < log x := log_pos hx
  have h1 := log_le_two_sqrt hx.le
  have h2 : √x * √x = x := mul_self_sqrt (by linarith)
  rw [mul_div_assoc', le_div_iff₀ hl]
  have : 0 ≤ √x := sqrt_nonneg _
  nlinarith

lemma sqrt_mul_log_le {x : ℝ} (hx : 1 < x) : √x * log x ≤ 16 * (x / log x) := by
  have hl : 0 < log x := log_pos hx
  have h1 := log_sq_le hx.le
  have h2 : √x * √x = x := mul_self_sqrt (by linarith)
  rw [mul_div_assoc', le_div_iff₀ hl]
  have : 0 ≤ √x := sqrt_nonneg _
  nlinarith

/-- Chebyshev: `π(y) ≤ (2 log 4 + 2) y / log y`. -/
lemma card_primesBelow_le (y : ℕ) (hy : 2 ≤ y) :
    ((y + 1).primesBelow.card : ℝ) ≤ (2 * log 4 + 2) * (y / log y) := by
  have hy1 : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hly : 0 < log (y : ℝ) := log_pos hy1
  have h1 : (y + 1).primesBelow.card = Nat.primeCounting y := by
    rw [Nat.primesBelow_card_eq_primeCounting']; rfl
  have h2 := Chebyshev.pi_le_log4_mul_div hy1
  rw [Nat.floor_natCast, log_sqrt (by linarith)] at h2
  rw [h1]
  have h3 := sqrt_le_div_log hy1
  have h4 : log 4 * (y : ℝ) / (log y / 2) = 2 * log 4 * (y / log y) := by
    field_simp
  linarith

end RunsOfMultiples
