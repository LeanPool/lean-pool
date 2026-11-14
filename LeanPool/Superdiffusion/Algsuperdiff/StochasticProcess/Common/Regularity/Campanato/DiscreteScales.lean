/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.TriadicRadii

/-!
# DiscreteScales

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Triadic radii and cube half-sides

## Main results

* `triadicRadius_half_zpow` — the dictionary between the telescope radii based
  at `3 ^ m / 2` and the half-sides `3 ^ (m - k) / 2` of the cubes of the
  underlying scale range.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Campanato

/-! ## Dictionary with cube half-sides -/

/-- The telescope based at the half-side `3 ^ m / 2` of the top cube visits
exactly the half-sides of the cubes of the scale range below it. -/
theorem triadicRadius_half_zpow (m : ℤ) (k : ℕ) :
    triadicRadius ((3 : ℝ) ^ m / 2) k = (3 : ℝ) ^ (m - (k : ℤ)) / 2 := by
  rw [triadicRadius, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  rw [show (1 / 3 : ℝ) ^ k = ((3 : ℝ) ^ (k : ℤ))⁻¹ by
    rw [zpow_natCast, one_div, inv_pow]]
  field_simp

end Algsuperdiff.StochasticProcess.Common.Regularity.Campanato
