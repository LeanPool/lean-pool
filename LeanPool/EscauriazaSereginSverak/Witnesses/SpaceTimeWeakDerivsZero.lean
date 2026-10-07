/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs

/-!
# The zero field has space-time weak derivatives

The predicate `CKN.HasSpaceTimeWeakDerivs` (manuscript §2, space-time weak
derivatives) is satisfied by the zero field with zero derivative data, on any
spatial set and time set.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


namespace ESS

/-- The zero field and zero derivative data satisfy `HasSpaceTimeWeakDerivs`. -/
theorem hasSpaceTimeWeakDerivs_zero (Ω : Set Vec3) (I : Set ℝ) :
    HasSpaceTimeWeakDerivs Ω I (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
  refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, locallyIntegrableOn_zero,
    locallyIntegrableOn_zero, fun φ _ => ⟨fun i j => ?_, fun i j k => ?_, fun i => ?_⟩⟩ <;>
    simp

end ESS
