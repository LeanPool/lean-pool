/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Constants.Series
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # The actual cubic geometric sum after interpolation -/

@[expose] public section

namespace VacuumBellSeparation.Gaussian
open scoped ENNReal

theorem cubic_geometric_interpolation_term {A B q t θ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hratio : q ^ (1 - θ) * t ^ θ ≤ 1 / 2) (n : ℕ) :
    (A * ((n : ℝ) + 1) ^ 3 * q ^ n) ^ (1 - θ) * (B * t ^ n) ^ θ ≤
      (A ^ (1 - θ) * B ^ θ) * (((n : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ n) := by
  have hn : 1 ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hp : (((n : ℝ) + 1) ^ 3) ^ (1 - θ) ≤ ((n : ℝ) + 1) ^ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn (show 1 - θ ≤ 1 by linarith [hθ.1])
  have hratio₀ : 0 ≤ q ^ (1 - θ) * t ^ θ :=
    mul_nonneg (Real.rpow_nonneg hq _) (Real.rpow_nonneg ht _)
  calc
    _ = (A ^ (1 - θ) * B ^ θ) * (((n : ℝ) + 1) ^ 3) ^ (1 - θ) *
        (q ^ (1 - θ) * t ^ θ) ^ n := by
      rw [Real.mul_rpow (mul_nonneg hA (by positivity)) (pow_nonneg hq _),
        Real.mul_rpow hA (by positivity), Real.mul_rpow hB (pow_nonneg ht _),
        ← Real.rpow_pow_comm hq, ← Real.rpow_pow_comm ht, mul_pow]
      ring
    _ ≤ (A ^ (1 - θ) * B ^ θ) * ((n : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ n := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left hp (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _)))
        (pow_le_pow_left₀ hratio₀ hratio n) (pow_nonneg hratio₀ _)
        (by positivity)
    _ = _ := by ring

theorem tsum_cubic_geometric_interpolation_le {A B q t θ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hratio : q ^ (1 - θ) * t ^ θ ≤ 1 / 2) :
    (∑' n : ℕ,
      ENNReal.ofReal (A * ((n : ℝ) + 1) ^ 3 * q ^ n) ^ (1 - θ) *
        ENNReal.ofReal (B * t ^ n) ^ θ) ≤
      ENNReal.ofReal (52 * A ^ (1 - θ) * B ^ θ) := by
  let C := A ^ (1 - θ) * B ^ θ
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _)
  have hs := VacuumBellSeparation.hasSum_cube_mul_half_pow.mul_left C
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C * (((n : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ n)) := by
      apply tsum_le_tsum
      intro n
      dsimp only
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (sub_nonneg.mpr hθ.2),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ.1,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
      exact ENNReal.ofReal_le_ofReal (cubic_geometric_interpolation_term hA hB hq ht hθ hratio n)
    _ = ENNReal.ofReal (C * 52) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable, hs.tsum_eq]
    _ = _ := by congr 1; dsimp only [C]; ring

end VacuumBellSeparation.Gaussian
