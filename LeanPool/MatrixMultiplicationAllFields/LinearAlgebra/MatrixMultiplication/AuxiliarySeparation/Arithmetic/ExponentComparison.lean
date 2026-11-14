/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Comparing power growth

The last scalar step of the auxiliary-separation argument compares a
fourth-power lower bound for the cube of the diagonal profile with its
dimension upper bound.  Powers of two suffice to compare the exponents, so
the argument needs no asymptotic estimates or approximation of constants.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

/-- A uniform bound on all positive natural inputs forces the exponent on
the left to be no larger than the exponent on the right. -/
theorem rpow_exponent_le_of_nat_bound {a b C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ a ≤ C * (n : ℝ) ^ b) :
    a ≤ b := by
  have hC : 0 < C := by
    have h := hbound 1 (by omega)
    norm_num at h
    linarith
  by_contra hab
  have hab' : 0 < a - b := sub_pos.mpr (lt_of_not_ge hab)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hp : 0 < (a - b) * Real.log 2 := mul_pos hab' hlog2
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.log C / ((a - b) * Real.log 2))
  have hk' : Real.log C < (k : ℝ) * ((a - b) * Real.log 2) :=
    (div_lt_iff₀ hp).mp hk
  have hn : (0 : ℝ) < (2 ^ k : ℕ) := by positivity
  have h := Real.log_le_log (Real.rpow_pos_of_pos hn a)
    (hbound (2 ^ k) (Nat.one_le_iff_ne_zero.mpr (by positivity)))
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hn b).ne',
    Real.log_rpow hn a, Real.log_rpow hn b] at h
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  nlinarith

/-- The diagonal lower bound and the dimension upper bound force the scalar
exponent to be at most `3/4`. -/
theorem diagonal_exponent_le_three_quarters {D : ℕ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hnonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ D n)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ 4 ≤ D n ^ 3)
    (hupper : ∀ n : ℕ, 1 ≤ n → D n ≤ (2 * (n : ℝ) - 1) ^ (1 / t)) :
    t ≤ 3 / 4 := by
  have hexp : 0 ≤ 1 / t := le_of_lt (one_div_pos.mpr ht)
  have hpower : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ (4 : ℝ) ≤
        (2 : ℝ) ^ ((1 / t) * 3) * (n : ℝ) ^ ((1 / t) * 3) := by
    intro n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hbase : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
    have hu : D n ≤ (2 * (n : ℝ)) ^ (1 / t) :=
      (hupper n hn).trans (Real.rpow_le_rpow hbase (by linarith) hexp)
    calc
      (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ 4 := by norm_num
      _ ≤ D n ^ 3 := hlower n hn
      _ ≤ ((2 * (n : ℝ)) ^ (1 / t)) ^ 3 :=
        pow_le_pow_left₀ (hnonneg n hn) hu 3
      _ = (2 * (n : ℝ)) ^ ((1 / t) * 3) := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_mul_natCast (show 0 ≤ 2 * (n : ℝ) by positivity) (1 / t) 3).symm
      _ = (2 : ℝ) ^ ((1 / t) * 3) * (n : ℝ) ^ ((1 / t) * 3) :=
        Real.mul_rpow (by norm_num) (by positivity)
  have hcompare : (4 : ℝ) ≤ (1 / t) * 3 :=
    rpow_exponent_le_of_nat_bound hpower
  have hmul := mul_le_mul_of_nonneg_right hcompare (le_of_lt ht)
  have hcancel : ((1 / t) * 3) * t = (3 : ℝ) := by
    field_simp
  rw [hcancel] at hmul
  linarith

/-- The scalar comparison in the normalization used for the matrix
multiplication exponent. -/
theorem three_mul_diagonal_exponent_le_nine_quarters {D : ℕ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hnonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ D n)
    (hlower : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ 4 ≤ D n ^ 3)
    (hupper : ∀ n : ℕ, 1 ≤ n → D n ≤ (2 * (n : ℝ) - 1) ^ (1 / t)) :
    3 * t ≤ 9 / 4 := by
  have h := diagonal_exponent_le_three_quarters ht hnonneg hlower hupper
  linarith

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
