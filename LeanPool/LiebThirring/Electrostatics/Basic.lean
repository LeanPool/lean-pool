/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.Coulomb

/-!
# Coulomb potentials and energies of positive measures

The Coulomb potential `Φ_α(x) = ∫ |x - y|⁻¹ dα(y)` of a positive measure, in `ℝ≥0∞`.

The mutual Coulomb energy `I(α, β) = double integral |x - y|⁻¹ dα(x) dβ(y)` of positive measures,
in `ℝ≥0∞`
(no factor `1/2`).
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring

/-- The Coulomb potential `Φ_α(x) = ∫ |x - y|⁻¹ dα(y)` of a positive measure, in `ℝ≥0∞`. -/
noncomputable def coulombPotential (α : Measure Position) (x : Position) : ℝ≥0∞ :=
  ∫⁻ y, coulombKernel x y ∂α

/-- The mutual Coulomb energy `I(α, β) = double integral |x - y|⁻¹ dα(x) dβ(y)` of positive
measures,
in `ℝ≥0∞` (no factor `1/2`). -/
noncomputable def coulombEnergy (α β : Measure Position) : ℝ≥0∞ :=
  ∫⁻ x, coulombPotential β x ∂α

end LiebThirring

end
