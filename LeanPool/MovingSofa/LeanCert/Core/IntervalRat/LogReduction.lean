/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import LeanPool.MovingSofa.LeanCert.Core.Expr  -- for Real.atanh

/-!
# Verified Argument Reduction for Logarithm

This file provides argument reduction for computing log(q) using the identity:
  log(q) = log(m) + k * log(2)
where m = q * 2^(-k) is in a "good" range [1/2, 2] for Taylor series convergence.

## Main definitions

* `reductionExponent` - Find k such that q * 2^(-k) is in [1/2, 2]
* `reduceMantissa` - The reduced mantissa m = q * 2^(-k)

## Main theorems

* `reconstruction_eq` - Algebraic identity: q = m * 2^k
* `reduced_bounds` - Bounds on m: 1 / 2 ≤ m ≤ 2 for q > 0

## Design notes

This reduction allows us to use the rapidly converging atanh-based series:
  log(m) = 2 * atanh((m-1)/(m+1))
For m ∈ [1/2, 2], we have (m-1)/(m+1) ∈ [-1/3, 1/3], where atanh converges very fast.
-/

/-! ### Argument Reduction -/

@[expose] public section

namespace LeanCert.Core.LogReduction

/-- Find k such that q * 2^(-k) is approximately in [1/2, 2].
    Implementation: k = log2(num) - log2(den) approximately. -/
def reductionExponent (q : ℚ) : ℤ :=
  if q ≤ 0 then 0
  else
    let n_log := q.num.natAbs.log2
    let d_log := q.den.log2
    (n_log : ℤ) - (d_log : ℤ)

/-- The reduced mantissa m = q * 2^(-k). -/
def reduceMantissa (q : ℚ) : ℚ :=
  if q ≤ 0 then 1  -- Default for non-positive inputs
  else
    let k := reductionExponent q
    q * (2 : ℚ) ^ (-k)

/-- The main algebraic theorem: q = m * 2^k for positive q -/
theorem reconstruction_eq {q : ℚ} (hq : 0 < q) :
    let k := reductionExponent q
    let m := reduceMantissa q
    q = m * (2 : ℚ) ^ k := by
  simp only [reductionExponent, reduceMantissa, not_le.mpr hq, ↓reduceIte]
  -- Goal: q = (q * 2^(-k)) * 2^k = q * (2^(-k) * 2^k) = q * 2^0 = q
  rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  simp only [neg_add_cancel, zpow_zero, mul_one]

/-- The reduced mantissa is bounded: 1/4 ≤ m ≤ 4 for q > 0.
    (We use slightly weaker bounds than [1/2, 2] for simpler proofs,
     but the series still converges rapidly.) -/
theorem reduced_bounds_weak {q : ℚ} (hq : 0 < q) :
    let m := reduceMantissa q
    1 / 4 ≤ m ∧ m ≤ 4 := by
  simp only [reduceMantissa, reductionExponent, not_le.mpr hq, ↓reduceIte]
  set n := q.num.natAbs.log2 with hn_def
  set d := q.den.log2 with hd_def
  have hnum_pos : q.num > 0 := Rat.num_pos.mpr hq
  have hnum_ne : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hnum_pos)
  have hden_pos := q.den_pos
  have hden_ne : q.den ≠ 0 := ne_of_gt hden_pos
  have h_num_lo : (2 : ℕ) ^ n ≤ q.num.natAbs := Nat.log2_self_le hnum_ne
  have h_num_hi : q.num.natAbs < 2 ^ (n + 1) := (Nat.log2_lt hnum_ne).mp (Nat.lt_succ_self _)
  have h_den_lo : (2 : ℕ) ^ d ≤ q.den := Nat.log2_self_le hden_ne
  have h_den_hi : q.den < 2 ^ (d + 1) := (Nat.log2_lt hden_ne).mp (Nat.lt_succ_self _)
  have h2_ne : (2 : ℚ) ≠ 0 := by norm_num
  have hden_pos_q : (0 : ℚ) < q.den := by exact_mod_cast hden_pos
  have hnum_pos_q : (0 : ℚ) < q.num.natAbs := by exact_mod_cast Nat.pos_of_ne_zero hnum_ne
  have hq_eq : q = q.num / q.den := (Rat.num_div_den q).symm
  have hnum_eq : (q.num : ℚ) = q.num.natAbs := by simp only [Nat.cast_natAbs, abs_of_pos hnum_pos]
  have hexp : (-(↑n - ↑d) : ℤ) = (d : ℤ) - (n : ℤ) := by ring
  rw [hexp]
  have hpow_diff : (2 : ℚ) ^ ((d : ℤ) - (n : ℤ)) = 2 ^ d / 2 ^ n := by
    rw [zpow_sub₀ h2_ne, zpow_natCast, zpow_natCast]
  rw [hpow_diff, hq_eq, hnum_eq]
  have h_num_lo_q : (2 : ℚ) ^ n ≤ q.num.natAbs := by exact_mod_cast h_num_lo
  have h_num_hi_q : (q.num.natAbs : ℚ) < 2 ^ (n + 1) := by exact_mod_cast h_num_hi
  have h_den_lo_q : (2 : ℚ) ^ d ≤ q.den := by exact_mod_cast h_den_lo
  have h_den_hi_q : (q.den : ℚ) < 2 ^ (d + 1) := by exact_mod_cast h_den_hi
  constructor
  · -- Lower bound: 1/4 ≤ m
    have h_simp : (q.num.natAbs : ℚ) / q.den * (2 ^ d / 2 ^ n) =
                  (q.num.natAbs * 2 ^ d) / (q.den * 2 ^ n) := by field_simp
    rw [h_simp, one_div, le_div_iff₀ (by positivity : (0 : ℚ) < q.den * 2 ^ n)]
    have key : (q.den : ℚ) * 2 ^ n / 4 < q.num.natAbs * 2 ^ d := by
      have h1 : (q.den : ℚ) * 2 ^ n / 4 < 2 ^ (d + 1) * 2 ^ n / 4 := by
        apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℚ) < 4)
        exact mul_lt_mul_of_pos_right h_den_hi_q (by positivity)
      have h2 : (2 : ℚ) ^ (d + 1) * 2 ^ n / 4 = 2 ^ d * 2 ^ n / 2 := by rw [pow_succ]; ring
      have h3 : (2 : ℚ) ^ d * 2 ^ n / 2 ≤ 2 ^ n * 2 ^ d := by
        rw [mul_comm (2 ^ d : ℚ) (2 ^ n)]; apply div_le_self (by positivity) (by norm_num)
      have h4 : (2 : ℚ) ^ n * 2 ^ d ≤ q.num.natAbs * 2 ^ d := by
        apply mul_le_mul_of_nonneg_right h_num_lo_q (by positivity)
      linarith
    linarith
  · -- Upper bound: m ≤ 4
    have h_simp : (q.num.natAbs : ℚ) / q.den * (2 ^ d / 2 ^ n) =
                  (q.num.natAbs * 2 ^ d) / (q.den * 2 ^ n) := by field_simp
    rw [h_simp, div_le_iff₀ (by positivity : (0 : ℚ) < q.den * 2 ^ n)]
    have h1 : (q.num.natAbs : ℚ) * 2 ^ d < 2 ^ (n + 1) * 2 ^ d := by
      apply mul_lt_mul_of_pos_right h_num_hi_q (by positivity)
    have h2 : (2 : ℚ) ^ (n + 1) * 2 ^ d = 2 * (2 ^ n * 2 ^ d) := by rw [pow_succ]; ring
    have h3 : (2 : ℚ) * (2 ^ n * 2 ^ d) ≤ 4 * (2 ^ n * 2 ^ d) := by
      have hp : (0 : ℚ) ≤ 2 ^ n * 2 ^ d := by positivity
      linarith
    have h4 : (4 : ℚ) * (2 ^ n * 2 ^ d) ≤ 4 * (q.den * 2 ^ n) := by
      have : (2 : ℚ) ^ n * 2 ^ d ≤ q.den * 2 ^ n := by
        calc (2 : ℚ) ^ n * 2 ^ d = 2 ^ d * 2 ^ n := by ring
          _ ≤ q.den * 2 ^ n := by apply mul_le_mul_of_nonneg_right h_den_lo_q (by positivity)
      linarith
    calc (q.num.natAbs : ℚ) * 2 ^ d ≤ 2 ^ (n + 1) * 2 ^ d := le_of_lt h1
      _ = 2 * (2 ^ n * 2 ^ d) := h2
      _ ≤ 4 * (2 ^ n * 2 ^ d) := h3
      _ ≤ 4 * (q.den * 2 ^ n) := h4

/-- Tighter bounds: 1 / 2 ≤ m ≤ 2 for most q > 0 -/
theorem reduced_bounds {q : ℚ} (hq : 0 < q) :
    let m := reduceMantissa q
    1 / 2 ≤ m ∧ m ≤ 2 := by
  simp only [reduceMantissa, reductionExponent, not_le.mpr hq, ↓reduceIte]
  set n := q.num.natAbs.log2 with hn_def
  set d := q.den.log2 with hd_def
  have hnum_pos : q.num > 0 := Rat.num_pos.mpr hq
  have hnum_ne : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (ne_of_gt hnum_pos)
  have hden_pos := q.den_pos
  have hden_ne : q.den ≠ 0 := ne_of_gt hden_pos
  have h_num_lo : (2 : ℕ) ^ n ≤ q.num.natAbs := Nat.log2_self_le hnum_ne
  have h_num_hi : q.num.natAbs < 2 ^ (n + 1) := (Nat.log2_lt hnum_ne).mp (Nat.lt_succ_self _)
  have h_den_lo : (2 : ℕ) ^ d ≤ q.den := Nat.log2_self_le hden_ne
  have h_den_hi : q.den < 2 ^ (d + 1) := (Nat.log2_lt hden_ne).mp (Nat.lt_succ_self _)
  have h2_ne : (2 : ℚ) ≠ 0 := by norm_num
  have hden_pos_q : (0 : ℚ) < q.den := by exact_mod_cast hden_pos
  have hnum_pos_q : (0 : ℚ) < q.num.natAbs := by exact_mod_cast Nat.pos_of_ne_zero hnum_ne
  have hq_eq : q = q.num / q.den := (Rat.num_div_den q).symm
  have hnum_eq : (q.num : ℚ) = q.num.natAbs := by simp only [Nat.cast_natAbs, abs_of_pos hnum_pos]
  have hexp : (-(↑n - ↑d) : ℤ) = (d : ℤ) - (n : ℤ) := by ring
  rw [hexp]
  have hpow_diff : (2 : ℚ) ^ ((d : ℤ) - (n : ℤ)) = 2 ^ d / 2 ^ n := by
    rw [zpow_sub₀ h2_ne, zpow_natCast, zpow_natCast]
  rw [hpow_diff, hq_eq, hnum_eq]
  have h_num_lo_q : (2 : ℚ) ^ n ≤ q.num.natAbs := by exact_mod_cast h_num_lo
  have h_num_hi_q : (q.num.natAbs : ℚ) < 2 ^ (n + 1) := by exact_mod_cast h_num_hi
  have h_den_lo_q : (2 : ℚ) ^ d ≤ q.den := by exact_mod_cast h_den_lo
  have h_den_hi_q : (q.den : ℚ) < 2 ^ (d + 1) := by exact_mod_cast h_den_hi
  constructor
  · -- Lower bound: 1 / 2 ≤ m
    have h_simp : (q.num.natAbs : ℚ) / q.den * (2 ^ d / 2 ^ n) =
                  (q.num.natAbs * 2 ^ d) / (q.den * 2 ^ n) := by field_simp
    rw [h_simp, one_div, le_div_iff₀ (by positivity : (0 : ℚ) < q.den * 2 ^ n)]
    -- Goal: (1/2) * (den * 2^n) ≤ natAbs * 2^d, i.e., den * 2^n / 2 ≤ natAbs * 2^d
    have key : (q.den : ℚ) * 2 ^ n / 2 < q.num.natAbs * 2 ^ d := by
      have h1 : (q.den : ℚ) * 2 ^ n / 2 < 2 ^ (d + 1) * 2 ^ n / 2 := by
        apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℚ) < 2)
        exact mul_lt_mul_of_pos_right h_den_hi_q (by positivity)
      have h2 : (2 : ℚ) ^ (d + 1) * 2 ^ n / 2 = 2 ^ d * 2 ^ n := by rw [pow_succ]; ring
      have h3 : (2 : ℚ) ^ d * 2 ^ n = 2 ^ n * 2 ^ d := by ring
      have h4 : (2 : ℚ) ^ n * 2 ^ d ≤ q.num.natAbs * 2 ^ d := by
        apply mul_le_mul_of_nonneg_right h_num_lo_q (by positivity)
      linarith
    linarith
  · -- Upper bound: m ≤ 2
    have h_simp : (q.num.natAbs : ℚ) / q.den * (2 ^ d / 2 ^ n) =
                  (q.num.natAbs * 2 ^ d) / (q.den * 2 ^ n) := by field_simp
    rw [h_simp, div_le_iff₀ (by positivity : (0 : ℚ) < q.den * 2 ^ n)]
    -- Goal: natAbs * 2^d ≤ 2 * (den * 2^n)
    have h1 : (q.num.natAbs : ℚ) * 2 ^ d < 2 ^ (n + 1) * 2 ^ d := by
      apply mul_lt_mul_of_pos_right h_num_hi_q (by positivity)
    have h2 : (2 : ℚ) ^ (n + 1) * 2 ^ d = 2 * (2 ^ n * 2 ^ d) := by rw [pow_succ]; ring
    have h3 : (2 : ℚ) * (2 ^ n * 2 ^ d) ≤ 2 * (q.den * 2 ^ n) := by
      have : (2 : ℚ) ^ n * 2 ^ d ≤ q.den * 2 ^ n := by
        calc (2 : ℚ) ^ n * 2 ^ d = 2 ^ d * 2 ^ n := by ring
          _ ≤ q.den * 2 ^ n := by apply mul_le_mul_of_nonneg_right h_den_lo_q (by positivity)
      linarith
    calc (q.num.natAbs : ℚ) * 2 ^ d ≤ 2 ^ (n + 1) * 2 ^ d := le_of_lt h1
      _ = 2 * (2 ^ n * 2 ^ d) := h2
      _ ≤ 2 * (q.den * 2 ^ n) := h3

/-- The reduced mantissa is positive for positive input -/
theorem reduced_pos {q : ℚ} (hq : 0 < q) : 0 < reduceMantissa q := by
  simp only [reduceMantissa, not_le.mpr hq, ↓reduceIte]
  apply mul_pos hq
  apply zpow_pos
  norm_num

/-! ### Connection to Real.log -/

/-- Key algebraic identity for Real.log: log(q) = log(m) + k * log(2) -/
theorem log_reduction {q : ℚ} (hq : 0 < q) :
    let k := reductionExponent q
    let m := reduceMantissa q
    Real.log q = Real.log m + k * Real.log 2 := by
  intro k m  -- Introduce let-bound variables
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast reduced_pos hq
  have h_recon := reconstruction_eq hq
  have hq_eq : (q : ℝ) = (m : ℝ) * (2 : ℝ) ^ k := by
    conv_lhs => rw [h_recon]
    push_cast
    rfl
  rw [hq_eq]
  have h2_pos : (0 : ℝ) < 2 ^ k := zpow_pos (by norm_num : (0 : ℝ) < 2) k
  rw [Real.log_mul (ne_of_gt hm_pos) (ne_of_gt h2_pos), Real.log_zpow]

/-- The transformation y = (m-1)/(m+1) maps m ∈ [1/2, 2] to y ∈ [-1/3, 1/3] -/
theorem atanh_arg_bounds {m : ℚ} (hlo : 1 / 2 ≤ m) (hhi : m ≤ 2) :
    let y := (m - 1) / (m + 1)
    (-1)/3 ≤ y ∧ y ≤ 1/3 := by
  intro y  -- Introduce let-bound variable
  have hden_pos : 0 < m + 1 := by linarith
  have hden_nonneg : 0 ≤ m + 1 := le_of_lt hden_pos
  constructor
  · -- Lower bound: (m-1)/(m+1) ≥ -1/3 when m ≥ 1/2
    -- Cross multiply: -1/3 ≤ (m-1)/(m+1) ↔ -(m+1) ≤ 3(m-1) ↔ 2 ≤ 4m
    have h : (-1 : ℚ) / 3 * (m + 1) ≤ m - 1 := by linarith
    have key := div_le_div_of_nonneg_right h hden_nonneg
    simp only [mul_div_assoc, div_self (ne_of_gt hden_pos), mul_one] at key
    exact key
  · -- Upper bound: (m-1)/(m+1) ≤ 1/3 when m ≤ 2
    -- Cross multiply: (m-1)/(m+1) ≤ 1/3 ↔ 3(m-1) ≤ m+1 ↔ 2m ≤ 4
    have h : m - 1 ≤ (1 : ℚ) / 3 * (m + 1) := by linarith
    have key := div_le_div_of_nonneg_right h hden_nonneg
    simp only [mul_div_assoc, div_self (ne_of_gt hden_pos), mul_one] at key
    exact key

/-- log(m) = 2 * atanh((m-1)/(m+1)) for m > 0 with m ≠ 1 -/
theorem log_via_atanh {m : ℚ} (hm_pos : 0 < m) :
    Real.log m = 2 * Real.atanh ((m - 1) / (m + 1)) := by
  have hm_pos' : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hsum_pos : (0 : ℝ) < m + 1 := by linarith
  have hdiff_ne : (m : ℝ) + 1 ≠ 0 := ne_of_gt hsum_pos
  -- atanh(y) = (1/2) * log((1+y)/(1-y))
  -- Setting y = (m-1)/(m+1):
  -- 1 + y = 1 + (m-1)/(m+1) = ((m+1) + (m-1))/(m+1) = 2m/(m+1)
  -- 1 - y = 1 - (m-1)/(m+1) = ((m+1) - (m-1))/(m+1) = 2/(m+1)
  -- (1+y)/(1-y) = (2m/(m+1)) / (2/(m+1)) = m
  rw [Real.atanh]
  have h1 : 1 + ((m : ℝ) - 1) / (m + 1) = 2 * m / (m + 1) := by field_simp; ring
  have h2 : 1 - ((m : ℝ) - 1) / (m + 1) = 2 / (m + 1) := by field_simp; ring
  rw [h1, h2]
  have h3 : 2 * (m : ℝ) / (m + 1) / (2 / (m + 1)) = m := by field_simp
  rw [h3]
  ring

end LeanCert.Core.LogReduction
