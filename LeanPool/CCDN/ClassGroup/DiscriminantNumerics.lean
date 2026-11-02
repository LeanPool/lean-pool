/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The exact discriminant exponent obtained from a square-root norm-curve
count and the `n−1` dimensional translation-class count. -/

@[expose] public section
namespace CCDN

private lemma classGroup_balanced_radius_power_identity {D : ℝ} (hD : 0 < D)
    {n : ℕ} (hn : 0 < n) :
    (9 * D ^ (1 / (n : ℝ))) ^ (n - 1) *
        Real.sqrt (9 * D ^ (1 / (n : ℝ))) =
      (3 * (9 : ℝ) ^ (n - 1)) *
        D ^ (1 / 2 - 1 / (2 * (n : ℝ))) * Real.sqrt D := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpred : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hsqrt : Real.sqrt (9 * D ^ (1 / (n : ℝ))) =
      3 * D ^ (1 / (2 * (n : ℝ))) := by
    have h9 : Real.sqrt (9 : ℝ) = 3 :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9), h9,
      Real.sqrt_eq_rpow, ← Real.rpow_mul hD.le]
    congr 2
    field_simp
  have hp : (D ^ (1 / (n : ℝ))) ^ (n - 1) =
      D ^ (((n - 1 : ℕ) : ℝ) / n) := by
    rw [← Real.rpow_mul_natCast hD.le]
    congr 1
    ring
  have hexp : ((n - 1 : ℕ) : ℝ) / n + 1 / (2 * (n : ℝ)) =
      (1 / 2 - 1 / (2 * (n : ℝ))) + 1 / 2 := by
    rw [hpred]
    field_simp
    ring
  rw [mul_pow, hp, hsqrt, Real.sqrt_eq_rpow]
  calc
    _ = (3 * (9 : ℝ) ^ (n - 1)) *
        (D ^ (((n - 1 : ℕ) : ℝ) / n) * D ^ (1 / (2 * (n : ℝ)))) := by ring
    _ = (3 * (9 : ℝ) ^ (n - 1)) *
        (D ^ (1 / 2 - 1 / (2 * (n : ℝ))) * D ^ (1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hD, hexp, Real.rpow_add hD]
    _ = _ := by ring

/-- If `N * √D ≤ A * R ^ (n - 1) * √R` for the balanced radius `R = 9 * D ^ (1 / n)`, then
`N ≤ A * 3 * 9 ^ (n - 1) * D ^ (1 / 2 - 1 / (2 * n))`: the discriminant exponent obtained from
a square-root norm-curve count and an `n - 1` dimensional translation-class count. -/
theorem classGroup_discriminant_bound_of_balanced_radius
    {D A N : ℝ} (hD : 0 < D) {n : ℕ} (hn : 0 < n)
    (h : N * Real.sqrt D ≤
      A * ((9 * D ^ (1 / (n : ℝ))) ^ (n - 1) *
        Real.sqrt (9 * D ^ (1 / (n : ℝ))))) :
    N ≤ (A * (3 * (9 : ℝ) ^ (n - 1))) *
      D ^ (1 / 2 - 1 / (2 * (n : ℝ))) := by
  rw [classGroup_balanced_radius_power_identity hD hn] at h
  apply (mul_le_mul_iff_left₀ (Real.sqrt_pos.mpr hD)).mp
  nlinarith only [h]

end CCDN
