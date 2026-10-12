/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.FourierFactor

/-!
# Vacuum density-power integral

The density is zero everywhere in the vacuum.

The vacuum density-power integral vanishes for every positive real exponent.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring

/-- The density is zero everywhere in the vacuum. -/
theorem density_vacuum {q : ℕ} (ψ : State 0 q) (x : Position) : density ψ x = 0 :=
  Finset.sum_empty

/-- The vacuum density-power integral vanishes for every positive real exponent. -/
theorem lintegral_density_rpow_vacuum {q : ℕ} (ψ : State 0 q)
    (p : ℝ) (hp : 0 < p) :
    (∫⁻ x : Position, density ψ x ^ p) = 0 := by
  simp only [density_vacuum, ENNReal.zero_rpow_of_pos hp, lintegral_zero]

end LiebThirring
end
