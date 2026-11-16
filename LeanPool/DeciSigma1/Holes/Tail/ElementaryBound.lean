/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

import Mathlib.Tactic.Positivity.Basic

public import LeanPool.DeciSigma1.Arithmetic.ElementaryBounds
public import LeanPool.DeciSigma1.Holes.Tail.Compression
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Elementary bounds for periodic compression

The split piece cap is affine in the uncovered length. Its slope is constant throughout the
compression passes, and its intercept increases with the number of remaining runs.

## Main declarations

- `compressionSlope`, `compressionIntercept`: the coefficients of the split piece cap.
- `splitPieceLengthBound_eq_affine`: the exact affine formula.
- `compressionLengthBoundIter_le_affine`: an affine bound on all compression passes.
- `compressionLengthBoundIter_le_exp2`: a single exponential coefficient times `E + 1`.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open Arithmetic

/-- The coefficient of the uncovered length in a split piece cap. -/
def compressionSlope (k N D : ℕ) : ℕ :=
  2 ^ (k * (N - 1)) * (Periodic.comparisonGap N D + Periodic.statePeriodModulus N D)

/-- The split piece cap with no uncovered positions and `r` remaining runs. -/
def compressionIntercept (k N D r : ℕ) : ℕ :=
  Periodic.fixedMargin N D + Periodic.statePeriodModulus N D +
    ((2 * r + 1) * 2 ^ (k * (N - 1)) - 1) *
      (Periodic.comparisonGap N D + Periodic.statePeriodModulus N D)

/-- The split piece cap is exactly affine in the uncovered length. -/
theorem splitPieceLengthBound_eq_affine (k N D r E : ℕ) :
    Periodic.pieceLengthBound N D (k * (N - 1)) (2 * r + E) =
      compressionIntercept k N D r + compressionSlope k N D * E := by
  have hQ : 1 ≤ 2 ^ (k * (N - 1)) := Nat.one_le_pow _ _ (by decide)
  have hbase : 1 ≤ (2 * r + 1) * 2 ^ (k * (N - 1)) := by nlinarith
  unfold Periodic.pieceLengthBound compressionIntercept compressionSlope
  rw [show (2 * r + E + 1) * 2 ^ (k * (N - 1)) =
    E * 2 ^ (k * (N - 1)) + (2 * r + 1) * 2 ^ (k * (N - 1)) by ring,
    Nat.add_sub_assoc hbase]
  ring

/-- The intercept increases with the number of remaining runs. -/
theorem compressionIntercept_mono (k N D : ℕ) : Monotone (compressionIntercept k N D) := by
  intro r s h
  unfold compressionIntercept
  gcongr

private theorem compressionSlope_pos (k N : ℕ) {D : ℕ} (hD : 0 < D) :
    0 < compressionSlope k N D := by
  unfold compressionSlope Periodic.comparisonGap Periodic.statePeriodModulus
  have := Nat.factorial_pos N
  positivity

/-- A common affine envelope for the descending compression passes, including zero runs. -/
theorem compressionLengthBoundIter_le_affine (k N D r E : ℕ) :
    compressionLengthBoundIter k N D r E ≤
      (1 + r * compressionSlope k N D) ^ r *
        (E + r * compressionIntercept k N D r) := by
  by_cases hD : D = 0
  · subst D
    have hz (n E : ℕ) : compressionLengthBoundIter k N 0 n E = E := by
      induction n generalizing E with
      | zero => rfl
      | succ n ih =>
        simp [compressionLengthBoundIter, Periodic.pieceLengthBound,
          Periodic.fixedMargin, Periodic.comparisonGap, Periodic.boundaryMargin,
          Periodic.stateTransientLength, Periodic.statePeriodModulus, ih]
    simp [hz, compressionSlope, compressionIntercept, Periodic.fixedMargin,
      Periodic.comparisonGap, Periodic.boundaryMargin, Periodic.stateTransientLength,
      Periodic.statePeriodModulus]
  have hb := compressionSlope_pos k N (Nat.pos_of_ne_zero hD)
  let b := compressionSlope k N D
  let c := compressionIntercept k N D r
  let A := 1 + r * b
  have haux (n : ℕ) : n ≤ r → ∀ E,
      compressionLengthBoundIter k N D n E + r * c ≤ A ^ n * (E + r * c) := by
    induction n with
    | zero => intro _ E; simp [compressionLengthBoundIter]
    | succ n ih =>
      intro hn E
      have hm : compressionIntercept k N D (n + 1) ≤ c :=
        compressionIntercept_mono k N D hn
      have hA : 2 ≤ A := by dsimp [A, b]; nlinarith
      have hcoef := Nat.mul_le_mul_right E (Nat.mul_le_mul_right b hn)
      have hconst := Nat.mul_le_mul hn hm
      have hconst' := Nat.mul_le_mul_right (r * c) hA
      have hstep : E + (n + 1) *
          Periodic.pieceLengthBound N D (k * (N - 1)) (2 * (n + 1) + E) +
          r * c ≤ A * (E + r * c) := by
        rw [splitPieceLengthBound_eq_affine]
        dsimp [A, b] at *
        nlinarith
      rw [compressionLengthBoundIter]
      calc
        _ ≤ A ^ n * (E + (n + 1) *
            Periodic.pieceLengthBound N D (k * (N - 1)) (2 * (n + 1) + E) +
            r * c) := ih (by omega) _
        _ ≤ A ^ n * (A * (E + r * c)) := Nat.mul_le_mul_left _ hstep
        _ = A ^ (n + 1) * (E + r * c) := by rw [pow_succ]; ring
  exact (Nat.le_add_right _ _).trans (haux r le_rfl E)

private def arithmeticBudget (k N D : ℕ) : ℕ := k * N + N * N + N + D + 4

private theorem margins_le_exp2 (N D : ℕ) :
    Periodic.fixedMargin N D + Periodic.statePeriodModulus N D ≤
        exp2 (N * N + N + D + 4) ∧
      Periodic.comparisonGap N D + Periodic.statePeriodModulus N D ≤
        exp2 (N * N + N + D + 3) := by
  have htrans : N * D ≤ exp2 (N * N + N + D) := by
    calc
      _ ≤ exp2 N * exp2 D := Nat.mul_le_mul (le_exp2 N) (le_exp2 D)
      _ = exp2 (N + D) := (exp2_add N D).symm
      _ ≤ _ := exp2_mono (by omega)
  have hmod : D * N.factorial ≤ exp2 (N * N + N + D) := by
    calc
      _ ≤ exp2 D * exp2 (N * N) := Nat.mul_le_mul (le_exp2 D) (factorial_le_exp2_sq N)
      _ = exp2 (D + N * N) := (exp2_add D (N * N)).symm
      _ ≤ _ := exp2_mono (by omega)
  unfold Periodic.fixedMargin Periodic.comparisonGap Periodic.boundaryMargin
    Periodic.stateTransientLength Periodic.statePeriodModulus
  rw [exp2_add (N * N + N + D) 4, exp2_add (N * N + N + D) 3]
  change _ ≤ exp2 (N * N + N + D) * 16 ∧ _ ≤ exp2 (N * N + N + D) * 8
  constructor <;> nlinarith

private theorem compressionSlope_le_exp2 (k N D : ℕ) :
    compressionSlope k N D ≤ exp2 (arithmeticBudget k N D) := by
  have hQ : 2 ^ (k * (N - 1)) ≤ exp2 (k * N) :=
    exp2_mono (Nat.mul_le_mul_left k (Nat.sub_le N 1))
  calc
    _ ≤ exp2 (k * N) * exp2 (N * N + N + D + 3) :=
      Nat.mul_le_mul hQ (margins_le_exp2 N D).2
    _ = exp2 (k * N + (N * N + N + D + 3)) := (exp2_add _ _).symm
    _ ≤ _ := exp2_mono (by unfold arithmeticBudget; omega)

private theorem compressionIntercept_le_exp2 (k N D r : ℕ) :
    compressionIntercept k N D r ≤ exp2 (arithmeticBudget k N D + r + 1) := by
  let q := arithmeticBudget k N D
  have hA : Periodic.fixedMargin N D + Periodic.statePeriodModulus N D ≤ exp2 q :=
    (margins_le_exp2 N D).1.trans (exp2_mono (by dsimp [q, arithmeticBudget]; omega))
  have hb := compressionSlope_le_exp2 k N D
  have hc : compressionIntercept k N D r ≤
      (Periodic.fixedMargin N D + Periodic.statePeriodModulus N D) +
        (2 * r + 1) * compressionSlope k N D := by
    unfold compressionIntercept compressionSlope
    calc
      _ ≤ _ + ((2 * r + 1) * 2 ^ (k * (N - 1))) *
          (Periodic.comparisonGap N D + Periodic.statePeriodModulus N D) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ 1)) _
      _ = _ := by ring
  calc
    _ ≤ exp2 q + (2 * r + 1) * exp2 q :=
      hc.trans (Nat.add_le_add hA (Nat.mul_le_mul_left _ hb))
    _ = 2 * (r + 1) * exp2 q := by ring
    _ ≤ 2 * exp2 r * exp2 q :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (succ_le_exp2 r))
    _ = _ := by
      change exp2 1 * exp2 r * exp2 q = _
      rw [← exp2_add, ← exp2_add]
      congr 1; dsimp [q]; omega

/-- Compression is bounded by a single exponential coefficient times the initial length plus
one, uniformly in all natural-number parameters. -/
theorem compressionLengthBoundIter_le_exp2 (k N D r E : ℕ) :
    compressionLengthBoundIter k N D r E ≤
      exp2 (16 * (k + N + D + r + 2) ^ 4) * (E + 1) := by
  let q := arithmeticBudget k N D
  have hb := compressionSlope_le_exp2 k N D
  have hc := compressionIntercept_le_exp2 k N D r
  have hbase : 1 + r * compressionSlope k N D ≤ exp2 (r + q + 1) := by
    calc
      _ ≤ exp2 0 + exp2 r * exp2 q :=
        Nat.add_le_add (le_refl 1) (Nat.mul_le_mul (le_exp2 r) hb)
      _ = exp2 0 + exp2 (r + q) := by rw [← exp2_add]
      _ ≤ _ := by simpa using exp2_add_le 0 (r + q)
  have hrc : r * compressionIntercept k N D r ≤ exp2 (q + 2 * r + 1) := by
    calc
      _ ≤ exp2 r * exp2 (q + r + 1) := Nat.mul_le_mul (le_exp2 r) hc
      _ = _ := by rw [← exp2_add]; congr 1; omega
  have hE : E + r * compressionIntercept k N D r ≤
      exp2 (q + 2 * r + 1) * (E + 1) := by
    have hpos : 1 ≤ exp2 (q + 2 * r + 1) := Nat.one_le_pow _ _ (by decide)
    nlinarith
  have hpoly : (r + q + 1) * r + (q + 2 * r + 1) ≤
      16 * (k + N + D + r + 2) ^ 4 := by
    dsimp [q, arithmeticBudget]
    ring_nf
    omega
  calc
    _ ≤ (1 + r * compressionSlope k N D) ^ r *
        (E + r * compressionIntercept k N D r) :=
      compressionLengthBoundIter_le_affine k N D r E
    _ ≤ exp2 (r + q + 1) ^ r * (exp2 (q + 2 * r + 1) * (E + 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hbase r) hE
    _ = exp2 ((r + q + 1) * r + (q + 2 * r + 1)) * (E + 1) := by
      rw [← exp2_mul, ← Nat.mul_assoc, ← exp2_add]
    _ ≤ _ := Nat.mul_le_mul_right _ (exp2_mono hpoly)

end DeciSigma1.Holes.Tail
