/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure

/-!
# Stability Local Product Integral

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- A local-box scalar integral in CKN coordinates equals its ordinary
product-measure integral. -/
theorem stability_setIntegral_localBox_eq_prod
    {Ω' : Set Vec3} {J : Set ℝ} (F : ParabolicPoint → ℝ) :
    (∫ z in CKN.spaceTimeSet Ω' J, F z ∂volume) =
      ∫ z : Vec3 × ℝ, F (z.1, z.2)
        ∂((volume.restrict Ω').prod (volume.restrict J)) := by
  rw [setIntegral_parabolic_to_product]
  rw [Measure.prod_restrict,
    ← MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  rfl

end CKN
