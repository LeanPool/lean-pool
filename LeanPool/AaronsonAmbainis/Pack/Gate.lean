/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.RowDefs

/-!
# The Chebyshev gate parameters

For `N = M ^ 2` (the bound for the number of blocks through a coordinate) and `m = ⌈π M / 2⌉₊`,
this file proves the three numerical facts used in the proof of the packing bound (Lemma 6.5 of
the paper):

* `gate_pos` : `0 < m` (for `M ≥ 1`);
* `gate_cos` : `N (1 - cos (π / m)) ≤ 2` (for `M ≥ 1`);
* `gate_sq`  : `4 m² ≤ (π M + 2)²`.
-/

@[expose] public section

namespace AaronsonAmbainis.Pack

/-- `m = ⌈π M / 2⌉₊` is positive when `M` is. -/
theorem gate_pos (M : ℕ) (hM : 0 < M) : 0 < ⌈Real.pi * (M : ℝ) / 2⌉₊ := by
  have hMr : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  exact Nat.ceil_pos.mpr (div_pos (mul_pos hpi hMr) two_pos)

/-- The hypothesis `N (1 - cos (π / m)) ≤ 2` of the block inequality for `N = M ^ 2` and
`m = ⌈π M / 2⌉₊`. -/
theorem gate_cos (M : ℕ) (hM : 0 < M) :
    ((M ^ 2 : ℕ) : ℝ) * (1 - Real.cos (Real.pi / ((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ))) ≤ 2 := by
  have hMr : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- abbreviate the real number `m`
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hm]
  have hle : Real.pi * (M : ℝ) / 2 ≤ m := by
    rw [hm]; exact Nat.le_ceil _
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (div_pos (mul_pos hpi hMr) two_pos) hle
  -- the cosine bound
  have hcos : 1 - (Real.pi / m) ^ 2 / 2 ≤ Real.cos (Real.pi / m) :=
    Real.one_sub_sq_div_two_le_cos
  have h1 : 1 - Real.cos (Real.pi / m) ≤ (Real.pi / m) ^ 2 / 2 := by linarith
  -- `M π / m ≤ 2`
  have h3 : (M : ℝ) * Real.pi / m ≤ 2 := by
    rw [div_le_iff₀ hmpos]; linarith
  have h4 : 0 ≤ (M : ℝ) * Real.pi / m :=
    div_nonneg (mul_nonneg hMr.le hpi.le) hmpos.le
  have h5 : ((M : ℝ) * Real.pi / m) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ h4 h3 2
  have h6 : (M : ℝ) ^ 2 * ((Real.pi / m) ^ 2 / 2) = ((M : ℝ) * Real.pi / m) ^ 2 / 2 := by
    ring
  have hM2 : (0 : ℝ) ≤ (M : ℝ) ^ 2 := sq_nonneg _
  have hcast : ((M ^ 2 : ℕ) : ℝ) = (M : ℝ) ^ 2 := by push_cast; ring
  rw [hcast]
  calc (M : ℝ) ^ 2 * (1 - Real.cos (Real.pi / m))
      ≤ (M : ℝ) ^ 2 * ((Real.pi / m) ^ 2 / 2) := mul_le_mul_of_nonneg_left h1 hM2
    _ = ((M : ℝ) * Real.pi / m) ^ 2 / 2 := h6
    _ ≤ 2 := by linarith

/-- `4 m² ≤ (π M + 2)²` for `m = ⌈π M / 2⌉₊`. -/
theorem gate_sq (M : ℕ) :
    4 * (((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ)) ^ 2 ≤ (Real.pi * (M : ℝ) + 2) ^ 2 := by
  have hMr : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h0 : (0 : ℝ) ≤ Real.pi * (M : ℝ) / 2 := div_nonneg (mul_nonneg hpi.le hMr) two_pos.le
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((⌈Real.pi * (M : ℝ) / 2⌉₊ : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hm]
  have hlt : m < Real.pi * (M : ℝ) / 2 + 1 := by
    rw [hm]; exact Nat.ceil_lt_add_one h0
  have hm0 : (0 : ℝ) ≤ m := by
    rw [hm]; exact Nat.cast_nonneg _
  have h2 : 2 * m ≤ Real.pi * (M : ℝ) + 2 := by linarith
  have h3 : (2 * m) ^ 2 ≤ (Real.pi * (M : ℝ) + 2) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg two_pos.le hm0) h2 2
  calc 4 * m ^ 2 = (2 * m) ^ 2 := by ring
    _ ≤ (Real.pi * (M : ℝ) + 2) ^ 2 := h3

end AaronsonAmbainis.Pack
