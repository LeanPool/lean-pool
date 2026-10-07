/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.LocalBox
public import LeanPool.CaffarelliKohnNirenberg.Statements.LocalVecLp
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Is Locally QIntegrable Force

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- Local `L^q` integrability of the force on the cylinders in `def:sws`. -/
@[expose]
def IsLocallyQIntegrableForce (q : ℝ) (f : ParabolicPoint → Vec3) : Prop :=
  ∀ Ω' J, localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J →
    localVecLp (spaceTimeSet Ω' J) q f

end CKN
