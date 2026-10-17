/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Model
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar

/-!
# Scales

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Section 3 scale vocabulary

The two distinguished induction landmarks from ABK26, equations
`e.mstarstar` and `e.mstar`, and the adopted Section 3.2 Option-A loss.
-/

namespace Algsuperdiff.Section3

noncomputable section

/-- The base-case starting scale `m**`, using the source-normalized Frobenius
origin-mass constant `cstarPlus`. -/
def mStarStar {d : ℕ} (model : ABKModel d) : ℤ :=
  ⌊(2 * model.gamma)⁻¹ *
    Real.logb 3
      (model.nu ^ 2 * model.gamma ^ 3 /
        (2 * Real.log 3 * Disorder.cstarPlus model))⌋

/-- The base-plateau scale `m*`, using the source-normalized
Frobenius origin-mass constant `cstarPlus`. -/
def mStar {d : ℕ} (model : ABKModel d) : ℤ :=
  ⌊(2 * model.gamma)⁻¹ *
    Real.logb 3
      (model.nu ^ 2 * model.gamma /
        (2 * Real.log 3 * Disorder.cstarPlus model))⌋

/-- The adopted Option-A all-scale loss in the Section 3.2 base case, on the
literal source range `0 < s < 1`. -/
def baseLoss (d : ℕ) (s : {s : ℝ // s ∈ Set.Ioo 0 1}) : ℝ :=
  1 + 6 * (d : ℝ) * Real.log 3 / (s : ℝ)

end

end Algsuperdiff.Section3
