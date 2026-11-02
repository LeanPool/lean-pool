/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.CongruenceCount
public import LeanPool.NairTenenbaum.Contributions.ShortIntervalCardinality

/-! # Upper congruence counts with the rounding error retained -/

@[expose] public section

namespace NairTenenbaum

open Finset Polynomial

theorem shortInterval_polynomial_congruence_count_le (Q : ℤ[X]) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) {q : ℕ} (hq : 0 < q) :
    (((shortInterval x y).filter (fun n : ℕ => q ∣ (Q.eval (n : ℤ)).natAbs)).card : ℝ) ≤
      (y + 1) * rootCount Q q / q + rootCount Q q := by
  classical
  have Hcard : ((shortInterval x y).filter (fun n : ℕ => q ∣ (Q.eval (n : ℤ)).natAbs)).card ≤
      polynomialCongruenceCount Q q (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) := by
    apply card_le_card_of_injOn (fun n : ℕ => (n : ℤ))
    · intro n hn
      obtain ⟨hn, hdiv⟩ := mem_filter.mp hn
      apply mem_filter.mpr
      refine ⟨mem_Ioc.mpr ?_, Int.natCast_dvd.mpr hdiv⟩
      change (⌊x⌋₊ : ℤ) < (n : ℤ) ∧ (n : ℤ) ≤ (⌊x + y⌋₊ : ℤ)
      exact_mod_cast mem_Ioc.mp hn
    · exact fun _ _ _ _ h => Int.ofNat_inj.mp h
  have hab : (⌊x⌋₊ : ℤ) ≤ (⌊x + y⌋₊ : ℤ) := by
    exact_mod_cast Nat.floor_mono (show x ≤ x + y by linarith)
  have H := (abs_le.mp (polynomialCongruenceCount_error Q hq (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) hab)).2
  have HL : (⌊x + y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) ≤ y + 1 := by
    linarith [Nat.floor_le (add_nonneg hx hy), Nat.lt_floor_add_one x]
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast hq
  have HB := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right HL (Nat.cast_nonneg (rootCount Q q))) hq₀.le
  have HC : (((shortInterval x y).filter (fun n : ℕ => q ∣ (Q.eval (n : ℤ)).natAbs)).card : ℝ) ≤
      (polynomialCongruenceCount Q q (⌊x⌋₊ : ℤ) (⌊x + y⌋₊ : ℤ) : ℝ) := by exact_mod_cast Hcard
  simp only [Int.cast_natCast] at H
  linarith

end NairTenenbaum
