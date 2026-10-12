/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.State

/-!
# One-particle density

The spatial density obtained by integrating out all other particle coordinates and summing over
particles.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- One-particle density obtained by integrating out the remaining spatial coordinates. -/
@[expose] noncomputable def density {N q : ℕ} (ψ : State N q) (x : Position) : ℝ≥0∞ :=
  ∑ i : Fin N, ∫⁻ y : OtherConfiguration i,
    (‖ψ (insertParticle i x y)‖₊ : ℝ≥0∞) ^ 2

end LiebThirring

end
