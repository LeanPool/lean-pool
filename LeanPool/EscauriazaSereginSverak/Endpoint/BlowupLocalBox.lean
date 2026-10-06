/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSliceRescaleUniform

/-!
# Blowup Local Box

Bounds on local boxes in the endpoint blow-up construction.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set
noncomputable section
namespace ESS

/-- A finite inner past cylinder is a local box of the larger rescaled
suitable-solution domain. -/
theorem blowup_inner_past_localBox
    (R a b : ℝ) (hR : 0 < R) (hab : a < b) (hb : b < 0) :
    localBox (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0)
      (vec3Ball 0 R) (Ioo a b) := by
  have houter : CKN.euclideanBall (0 : Vec3) (R + 1) =
      vec3Ball 0 (R + 1) :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
      (by linarith only [hR])
  refine ⟨isOpen_vec3Ball 0 R, isCompact_closure_vec3Ball hR, ?_,
    ordConnected_Ioo, ?_, ?_⟩
  · rw [closure_vec3Ball hR, houter]
    intro x hx
    change vec3EuclideanNorm (x - 0) ≤ R at hx
    change vec3EuclideanNorm (x - 0) < R + 1
    linarith only [hx]
  · rw [closure_Ioo hab.ne]
    exact isCompact_Icc
  · rw [closure_Ioo hab.ne]
    intro t ht
    exact ⟨by linarith only [ht.1], by linarith only [ht.2, hb]⟩

end ESS
