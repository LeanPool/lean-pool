/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A deterministic bound for normalized wager fractions

This file proves the pathwise quadratic-variation estimate in Lemma 2 of
Liu and Meng, *Separating Kolmogorov–Loveland randomness from Martin-Löf
randomness*, arXiv:2611.31004v1, pp. 4–5.

For wager fractions `f t`, write `Q n = ∑ t < n, (f t)^2` and replace the next
fraction by `f n / (2 * (1 + Q n))`. The sum of the squares of the replacement
fractions is at most `1 / 2`. The proof gives the stronger finite telescoping
bound with remainder `1 / (2 * (1 + Q n))`, and then passes to the infinite sum.

This is an analytic estimate for real sequences. It does not yet assert that the
normalization preserves success or that a strategy computing these fractions is
computable.
-/

@[expose] public section

namespace Klr

open scoped BigOperators

/-- The sum of squared wager fractions strictly before time `n`. -/
def quadraticVariation (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, (f t) ^ 2

/-- The damping of wager fractions used in Lemma 2 of the paper. -/
noncomputable def normalizedWager (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f n / (2 * (1 + quadraticVariation f n))

@[simp]
theorem quadraticVariation_zero (f : ℕ → ℝ) : quadraticVariation f 0 = 0 := by
  simp [quadraticVariation]

@[simp]
theorem quadraticVariation_succ (f : ℕ → ℝ) (n : ℕ) :
    quadraticVariation f (n + 1) = quadraticVariation f n + (f n) ^ 2 := by
  simp [quadraticVariation, Finset.sum_range_succ]

theorem quadraticVariation_nonneg (f : ℕ → ℝ) (n : ℕ) :
    0 ≤ quadraticVariation f n := by
  exact Finset.sum_nonneg fun t _ ↦ sq_nonneg (f t)

/-- The one-step inequality underlying the telescoping estimate. -/
theorem normalized_square_le_telescope (q x : ℝ) (hq : 0 ≤ q) (hx : x ^ 2 ≤ 1) :
    (x / (2 * (1 + q))) ^ 2 ≤
      (1 / 2 : ℝ) * (1 / (1 + q) - 1 / (1 + (q + x ^ 2))) := by
  have ha : 0 < 1 + q := by linarith
  have hb : 0 < 1 + q + x ^ 2 := by positivity
  have hproduct : 0 ≤ 2 * (1 + q) * (x ^ 2 * ((1 + q) - x ^ 2)) := by
    apply mul_nonneg (by positivity)
    exact mul_nonneg (sq_nonneg x) (by linarith)
  have hfrac : x ^ 2 / (4 * (1 + q) ^ 2) ≤
      x ^ 2 / (2 * (1 + q) * (1 + q + x ^ 2)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [hproduct]
  calc
    (x / (2 * (1 + q))) ^ 2 = x ^ 2 / (4 * (1 + q) ^ 2) := by
      field_simp
      ring
    _ ≤ x ^ 2 / (2 * (1 + q) * (1 + q + x ^ 2)) := hfrac
    _ = (1 / 2 : ℝ) * (1 / (1 + q) - 1 / (1 + (q + x ^ 2))) := by
      field_simp
      ring

theorem normalizedWager_sq_le_telescope (f : ℕ → ℝ) (n : ℕ)
    (hf : (f n) ^ 2 ≤ 1) :
    (normalizedWager f n) ^ 2 ≤
      (1 / 2 : ℝ) * (1 / (1 + quadraticVariation f n) -
        1 / (1 + quadraticVariation f (n + 1))) := by
  simpa only [normalizedWager, quadraticVariation_succ] using
    normalized_square_le_telescope (quadraticVariation f n) (f n)
      (quadraticVariation_nonneg f n) hf

/-- A stronger finite estimate, retaining the nonnegative telescoping remainder. -/
theorem sum_normalizedWager_sq_le_telescope (f : ℕ → ℝ)
    (hf : ∀ t, (f t) ^ 2 ≤ 1) (n : ℕ) :
    (∑ t ∈ Finset.range n, (normalizedWager f t) ^ 2) ≤
      (1 / 2 : ℝ) * (1 - 1 / (1 + quadraticVariation f n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hstep := normalizedWager_sq_le_telescope f n (hf n)
      linarith

/-- The pathwise bound in equation (2), for every finite initial segment. -/
theorem sum_normalizedWager_sq_le_half (f : ℕ → ℝ)
    (hf : ∀ t, (f t) ^ 2 ≤ 1) (n : ℕ) :
    (∑ t ∈ Finset.range n, (normalizedWager f t) ^ 2) ≤ (1 / 2 : ℝ) := by
  have htel := sum_normalizedWager_sq_le_telescope f hf n
  have hnonneg : 0 ≤ 1 / (1 + quadraticVariation f n) := by
    have := quadraticVariation_nonneg f n
    positivity
  linarith

/-- The replacement fractions are square-summable on every path. -/
theorem summable_normalizedWager_sq (f : ℕ → ℝ)
    (hf : ∀ t, |f t| ≤ 1) : Summable (fun t ↦ (normalizedWager f t) ^ 2) := by
  apply summable_of_sum_range_le (c := (1 / 2 : ℝ)) (fun t ↦ sq_nonneg _)
  exact sum_normalizedWager_sq_le_half f (fun t ↦ (sq_le_one_iff_abs_le_one _).2 (hf t))

/-- The infinite-series bound in equation (2) of the paper. -/
theorem tsum_normalizedWager_sq_le_half (f : ℕ → ℝ)
    (hf : ∀ t, |f t| ≤ 1) :
    (∑' t, (normalizedWager f t) ^ 2) ≤ (1 / 2 : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun t ↦ sq_nonneg _)
  exact sum_normalizedWager_sq_le_half f (fun t ↦ (sq_le_one_iff_abs_le_one _).2 (hf t))

end Klr
