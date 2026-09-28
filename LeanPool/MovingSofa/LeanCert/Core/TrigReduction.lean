/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import LeanPool.MovingSofa.LeanCert.Core.IntervalRat.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
/-!
# Shared Trigonometric Range Reduction

Common rational `π` bounds and interval-shifting proofs used by IntervalRat and
Taylor-model trigonometric evaluators.
-/

/-! ### Rational approximations of π and 2π -/

@[expose] public section

namespace LeanCert.Core.TrigReduction

open LeanCert.Core

/-- Lower bound for π: 314159265/100000000 < π -/
def piRatLo : ℚ := 314159265/100000000

/-- Upper bound for π: π < 355/113 -/
def piRatHi : ℚ := 355/113

/-- Lower bound for 2π -/
def twoPiRatLo : ℚ := 2 * piRatLo

/-- Upper bound for 2π -/
def twoPiRatHi : ℚ := 2 * piRatHi

/-- `piRatLo < π`, proved from Mathlib's decimal π bounds. -/
theorem piRatLo_lt_pi : (piRatLo : ℝ) < Real.pi := by
  have h₁ : (piRatLo : ℝ) < (3.14159265358979323846 : ℝ) := by
    norm_num [piRatLo]
  exact lt_trans h₁ Real.pi_gt_d20

/-- `π < piRatHi`, proved from Mathlib's decimal π bounds. -/
theorem pi_lt_piRatHi : Real.pi < (piRatHi : ℝ) := by
  have h₁ : (3.14159265358979323847 : ℝ) < (piRatHi : ℝ) := by
    norm_num [piRatHi]
  exact lt_trans Real.pi_lt_d20 h₁

/-- twoPiRatLo < 2π -/
theorem twoPiRatLo_lt_two_pi : (twoPiRatLo : ℝ) < 2 * Real.pi := by
  unfold twoPiRatLo
  simp only [Rat.cast_mul, Rat.cast_ofNat]
  have h := piRatLo_lt_pi
  linarith

/-- 2π < twoPiRatHi -/
theorem two_pi_lt_twoPiRatHi : 2 * Real.pi < (twoPiRatHi : ℝ) := by
  unfold twoPiRatHi
  simp only [Rat.cast_mul, Rat.cast_ofNat]
  have h := pi_lt_piRatHi
  linarith

/-- twoPiRatLo ≤ twoPiRatHi -/
theorem twoPiRatLo_le_twoPiRatHi : twoPiRatLo ≤ twoPiRatHi := by
  unfold twoPiRatLo twoPiRatHi piRatLo piRatHi
  norm_num

/-! ### Range reduction -/

/-- Compute the shift amount k such that I.midpoint - k * 2π is approximately in [-π, π]. -/
def computeShiftK (I : IntervalRat) : ℤ :=
  let mid := I.midpoint
  (mid / twoPiRatHi).floor

/-- Shift an interval by subtracting k * 2π using rational bounds. -/
def shiftInterval (I : IntervalRat) (k : ℤ) : IntervalRat :=
  if hk : k ≥ 0 then
    ⟨I.lo - k * twoPiRatHi, I.hi - k * twoPiRatLo,
      by have h1 := twoPiRatLo_le_twoPiRatHi
         have hk_cast : (0 : ℚ) ≤ k := Int.cast_nonneg hk
         have h2 : (k : ℚ) * twoPiRatLo ≤ k * twoPiRatHi :=
           mul_le_mul_of_nonneg_left h1 hk_cast
         linarith [I.le]⟩
  else
    ⟨I.lo - k * twoPiRatLo, I.hi - k * twoPiRatHi,
      by have h1 := twoPiRatLo_le_twoPiRatHi
         have hkneg : k < 0 := Int.not_le.mp hk
         have hk_cast : (k : ℚ) ≤ 0 := Int.cast_nonpos.mpr (le_of_lt hkneg)
         have h2 : (k : ℚ) * twoPiRatHi ≤ k * twoPiRatLo :=
           mul_le_mul_of_nonpos_left h1 hk_cast
         linarith [I.le]⟩

/-- Reduce interval to be approximately in [-π, π] by subtracting multiples of 2π. -/
def reduceToMainPeriod (I : IntervalRat) : IntervalRat × ℤ :=
  let k := computeShiftK I
  (shiftInterval I k, k)

/-! ### Correctness of range reduction -/

/-- If x ∈ I, then x - 2πk ∈ shiftInterval I k. -/
theorem mem_shiftInterval_of_mem {x : ℝ} {I : IntervalRat} {k : ℤ}
    (hx : x ∈ I) : x - 2 * Real.pi * k ∈ shiftInterval I k := by
  simp only [IntervalRat.mem_def] at hx ⊢
  unfold shiftInterval
  split_ifs with hk
  · constructor
    · have h1 : (I.lo : ℝ) ≤ x := hx.1
      have h2 : 2 * Real.pi ≤ (twoPiRatHi : ℝ) := le_of_lt two_pi_lt_twoPiRatHi
      have hk_cast : (0 : ℝ) ≤ k := Int.cast_nonneg hk
      have h3 : 2 * Real.pi * k ≤ (twoPiRatHi : ℝ) * k :=
        mul_le_mul_of_nonneg_right h2 hk_cast
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast]
      linarith
    · have h1 : x ≤ (I.hi : ℝ) := hx.2
      have h2 : (twoPiRatLo : ℝ) ≤ 2 * Real.pi := le_of_lt twoPiRatLo_lt_two_pi
      have hk_cast : (0 : ℝ) ≤ k := Int.cast_nonneg hk
      have h3 : (twoPiRatLo : ℝ) * k ≤ 2 * Real.pi * k :=
        mul_le_mul_of_nonneg_right h2 hk_cast
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast]
      linarith
  · have hkneg : k < 0 := Int.not_le.mp hk
    have hk_cast : (k : ℝ) ≤ 0 := Int.cast_nonpos.mpr (le_of_lt hkneg)
    constructor
    · have h1 : (I.lo : ℝ) ≤ x := hx.1
      have h2 : (twoPiRatLo : ℝ) ≤ 2 * Real.pi := le_of_lt twoPiRatLo_lt_two_pi
      have h3 : (k : ℝ) * (2 * Real.pi) ≤ k * twoPiRatLo :=
        mul_le_mul_of_nonpos_left h2 hk_cast
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast]
      linarith
    · have h1 : x ≤ (I.hi : ℝ) := hx.2
      have h2 : 2 * Real.pi ≤ (twoPiRatHi : ℝ) := le_of_lt two_pi_lt_twoPiRatHi
      have h3 : (k : ℝ) * twoPiRatHi ≤ k * (2 * Real.pi) :=
        mul_le_mul_of_nonpos_left h2 hk_cast
      simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_intCast]
      linarith

/-- Convenience form: if x ∈ I, then x - 2πk ∈ (reduceToMainPeriod I).1. -/
theorem mem_reduceToMainPeriod_of_mem {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    x - 2 * Real.pi * (reduceToMainPeriod I).2 ∈ (reduceToMainPeriod I).1 := by
  unfold reduceToMainPeriod
  exact mem_shiftInterval_of_mem hx

end LeanCert.Core.TrigReduction
