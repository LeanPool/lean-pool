/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.Zeta5Irrational.TableCheck

/-!
# Rational certificates for finite analytic series

The table bounds use only rational inputs. Check their finite sums in `ℚ`, then transport
one inequality to `ℝ`, avoiding a separate normalization proof for every real operation.
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

end Zeta5Irrational
