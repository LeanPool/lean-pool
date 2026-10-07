/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Is Locally Square Integrable Force

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- Square integrability of the force on every finite positive-time slab. -/
@[expose]
def IsLocallySquareIntegrableForce (f : ParabolicPoint → Vec3) : Prop :=
  ∀ T : ℝ, 0 < T →
    MemLp f (2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))

end CKN
