/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Rumin’s constant

The explicit three-dimensional coefficient in the kinetic Lieb–Thirring inequality.
-/

public section

open scoped NNReal

namespace LiebThirring

/-- The explicit three-dimensional kinetic coefficient obtained from Rumin’s argument. -/
@[expose] noncomputable def ruminConstant : ℝ≥0 :=
  Real.toNNReal ((9 / 35 : ℝ) * (6 * Real.pi ^ 2) ^ ((2 : ℝ) / 3))

end LiebThirring

end
