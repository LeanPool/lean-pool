/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsForcedLerayHopfSolution

/-!
# Is Global Forced Leray Hopf Solution

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- A global forced Leray--Hopf solution on every finite interval. -/
@[expose]
def IsGlobalForcedLerayHopfSolution (a : Vec3 → Vec3)
    (f : ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) : Prop :=
  ∀ T : ℝ, 0 < T → IsForcedLerayHopfSolution T a f u Du

end CKN
