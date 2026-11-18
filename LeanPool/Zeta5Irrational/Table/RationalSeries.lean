/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.Zeta5Irrational.TableCheck
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith

/-!
# Rational certificates for finite analytic series

The table bounds use only rational inputs. Check their finite sums in `ℚ`, then transport
one inequality to `ℝ`, avoiding a separate normalization proof for every real operation.
Binary range reduction also checks its rational rounding bound before using the shared
lower bound on `Real.log 2`.
-/

public section

open Finset

namespace Zeta5Irrational

/-- A rational upper certificate for the logarithm series and its geometric tail. -/
lemma log_le_of_ge_one_rat {r U : ℚ} (m : ℕ)
    (certificate : 1 ≤ r ∧
      2 * ∑ k ∈ range m, (1 / (2 * (k : ℚ) + 1)) * ((r - 1) / (r + 1)) ^ (2 * k + 1) +
          2 * ((r - 1) / (r + 1)) ^ (2 * m + 1) /
            ((2 * m + 1) * (1 - ((r - 1) / (r + 1)) ^ 2)) ≤ U) :
    Real.log (r : ℝ) ≤ (U : ℝ) := by
  apply log_le_of_ge_one (by exact_mod_cast certificate.1) m
  have h := (Rat.cast_le (K := ℝ)).2 certificate.2
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_neg] using h

/-- A rational lower certificate for the logarithm series. -/
lemma log_ge_of_ge_one_rat {r L : ℚ} (m : ℕ)
    (certificate : 1 ≤ r ∧ L ≤ 2 * ∑ k ∈ range m,
      (1 / (2 * (k : ℚ) + 1)) * ((r - 1) / (r + 1)) ^ (2 * k + 1)) :
    (L : ℝ) ≤ Real.log (r : ℝ) := by
  apply log_ge_of_ge_one (by exact_mod_cast certificate.1) m
  have h := (Rat.cast_le (K := ℝ)).2 certificate.2
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_neg] using h

/-- A rational lower certificate for the alternating arctangent series. -/
lemma arctan_ge_of_series_rat {z L : ℚ} (k : ℕ)
    (certificate : 0 ≤ z ∧ z < 1 ∧ L ≤ ∑ i ∈ range (2 * k),
      (-1 : ℚ) ^ i * (z ^ (2 * i + 1) / (2 * (i : ℚ) + 1))) :
    (L : ℝ) ≤ Real.arctan (z : ℝ) := by
  apply arctan_ge_of_series (by exact_mod_cast certificate.1) (by exact_mod_cast certificate.2.1) k
  have h := (Rat.cast_le (K := ℝ)).2 certificate.2.2
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_neg] using h

/-- A rational upper certificate for the alternating arctangent series. -/
lemma arctan_le_of_series_rat {z U : ℚ} (k : ℕ)
    (certificate : 0 ≤ z ∧ z < 1 ∧ ∑ i ∈ range (2 * k + 1),
      (-1 : ℚ) ^ i * (z ^ (2 * i + 1) / (2 * (i : ℚ) + 1)) ≤ U) :
    Real.arctan (z : ℝ) ≤ (U : ℝ) := by
  apply arctan_le_of_series (by exact_mod_cast certificate.1) (by exact_mod_cast certificate.2.1) k
  have h := (Rat.cast_le (K := ℝ)).2 certificate.2.2
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_neg] using h

/-- Check binary range reduction and its final logarithm bound in the rationals. -/
lemma log_le_of_split_neg_rational {r r' U U' : ℚ} (power m : ℕ)
    (certificate : 1 ≤ r' ∧
      2 * ∑ k ∈ range m, (1 / (2 * (k : ℚ) + 1)) * ((r' - 1) / (r' + 1)) ^ (2 * k + 1) +
          2 * ((r' - 1) / (r' + 1)) ^ (2 * m + 1) /
            ((2 * m + 1) * (1 - ((r' - 1) / (r' + 1)) ^ 2)) ≤ U')
    (reduction : r = r' / 2 ^ power ∧ U' - power * (6931471803 / 10000000000) ≤ U) :
    Real.log (r : ℝ) ≤ (U : ℝ) := by
  have hr : (r : ℝ) = (r' : ℝ) / 2 ^ power := by exact_mod_cast reduction.1
  have hr' : (0 : ℝ) < r' := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℚ) < 1) certificate.1)
  have h := log_le_of_split_neg power hr hr' (log_le_of_ge_one_rat m certificate)
  have hround : (U' : ℝ) - power * (6931471803 / 10000000000) ≤ U := by
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 reduction.2
  have hlog : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by
    linarith only [Real.log_two_gt_d9]
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) power)
  exact h.trans ((sub_le_sub_left hmul _).trans hround)

end Zeta5Irrational
