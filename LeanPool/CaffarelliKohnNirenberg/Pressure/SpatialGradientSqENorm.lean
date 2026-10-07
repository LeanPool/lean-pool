/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder

/-!
# Spatial Gradient Sq ENorm

Supporting estimates for the Navier–Stokes development.
-/

public section

open CKN.Foundation.Parabolic

namespace CKN

/-- The extended-real form of the inequality `|∇u|² ≤ 9 ‖Du‖²`: for any velocity field `u` and
its spatial gradient `Du`, the `ENNReal`-valued `ofReal` of the squared spatial gradient density
is bounded by `9` times the `ENNReal`-valued norm of `Du` raised to power `(2 : ℝ)`. -/
theorem ofReal_spatialGradientSq_le_nine_mul
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) :
    ENNReal.ofReal (spatialGradientSq u Du z) ≤ 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
  have hreal := pressure_spatialGradientSq_le u Du z
  calc
    ENNReal.ofReal (spatialGradientSq u Du z) ≤
        ENNReal.ofReal (9 * ‖Du z‖ ^ (2 : ℕ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm]
      norm_num [ENNReal.rpow_natCast]

end CKN
