/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Groups

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `rpow` / geometric-power bridge of the shell groups

Local helper for ABK26, Section 4.1, the right-hand side of
`e.mathcalE.annular.decomp`.  `threeRpow_neg_natMul` rewrites the real power
`3^(-c j)` at a natural index `j` as the `j`-th power of `3^(-c)`, which is the
form the geometric shell sums of the annular decomposition are stated in.
-/

namespace Algsuperdiff.Section4.Provider.Annular

noncomputable section

/-! ## The `rpow` / geometric-power bridge -/

/-- `3 ^ (-(c * j)) = (3 ^ (-c)) ^ j` for a natural `j`. -/
theorem threeRpow_neg_natMul (c : ℝ) (j : ℕ) :
    (3 : ℝ) ^ (-(c * (j : ℝ))) = ((3 : ℝ) ^ (-c)) ^ j := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-c)) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

end

end Algsuperdiff.Section4.Provider.Annular
