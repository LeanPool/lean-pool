/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeCellProbability

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeCellArithmetic

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constants for the one-cell renormalization estimate
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

noncomputable section

variable {d : ℕ}

/-- The dimension, old exponent, and reference cost in the one-cell estimate. -/
@[expose]
def unitRangeCellGain (d : ℕ) (g : ℝ) (E : BlockMat d) : ℝ :=
  32 * (d : ℝ) ^ 2 * kappaRef E * (3 : ℝ) ^ g *
    frThreshold d * (1 + unitRangeRenormShift d)

theorem unitRangeCellGain_pos [NeZero d] {g : ℝ} {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E) :
    0 < unitRangeCellGain d g E := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hk : 0 < kappaRef E :=
    lt_of_lt_of_le zero_lt_one (Initialization.one_le_kappaRef hE hEpd hsharp)
  have hs : 0 ≤ unitRangeRenormShift d := unitRangeRenormShift_nonneg d
  have hshift : 0 < 1 + unitRangeRenormShift d := by linarith only [hs]
  rw [unitRangeCellGain]
  exact mul_pos
    (mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (by norm_num) (sq_pos_of_pos hd)) hk)
          (Real.rpow_pos_of_pos (by norm_num) g))
        (frThreshold_pos d))
      hshift

end

end Quenched
end HighContrast
end HCPolySupport
