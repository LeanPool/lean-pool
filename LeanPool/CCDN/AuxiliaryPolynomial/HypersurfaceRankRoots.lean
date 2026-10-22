/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile

/-! Exact leading term for the dimension root of the homogeneous Hilbert rank. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Taking the dimension root preserves the factorial leading coefficient. -/
theorem hypersurface_rank_root_bounds {r d M s : ℕ} (hrpos : 0 < r) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    (d : ℝ) ^ (1 / (r : ℝ)) * ((M : ℝ) - d + 1) ≤
        (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) ∧
      (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) ≤
        (d : ℝ) ^ (1 / (r : ℝ)) * ((M : ℝ) + r) := by
  obtain ⟨hl, hu⟩ := hypersurface_rank_power_bounds hdM hr
  have hfac : (0 : ℝ) < r.factorial := by positivity
  have hmd : (0 : ℝ) ≤ (M : ℝ) - d + 1 := by
    have : (d : ℝ) ≤ M := by exact_mod_cast hdM
    linarith
  have hl' := (div_le_iff₀ hfac).mp hl
  have hu' := (le_div_iff₀ hfac).mp hu
  have hlroot := Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg hmd r)) hl'
    (show 0 ≤ 1 / (r : ℝ) by positivity)
  have huroot := Real.rpow_le_rpow
    (mul_nonneg (Nat.cast_nonneg s) hfac.le) hu' (show 0 ≤ 1 / (r : ℝ) by positivity)
  rw [Real.mul_rpow (Nat.cast_nonneg d) (pow_nonneg hmd r),
    Real.mul_rpow (Nat.cast_nonneg s) hfac.le, one_div,
    Real.pow_rpow_inv_natCast hmd hrpos.ne'] at hlroot
  rw [Real.mul_rpow (Nat.cast_nonneg s) hfac.le,
    Real.mul_rpow (Nat.cast_nonneg d) (by positivity), one_div,
    Real.pow_rpow_inv_natCast (by positivity) hrpos.ne'] at huroot
  constructor
  · simpa only [one_div, mul_comm] using hlroot
  · simpa only [one_div, mul_comm] using huroot

end
end CCDN
