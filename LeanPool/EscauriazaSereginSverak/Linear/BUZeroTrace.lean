/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineAE

/-!
# Continuity at the next time endpoint

The zero trace used at each step of `lem:bu-iterate` follows from vanishing
on the preceding open time interval and continuity up to the endpoint.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Vanishing on every earlier positive time implies vanishing at a time
strictly inside the half-space cylinder. -/
theorem bu_zero_at_time_of_left
    (w : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hzero : ∀ x : Vec3, 0 < x 2 → ∀ t : ℝ,
      0 < t → t < τ → w (x, t) = 0)
    (x : Vec3) (hx : 0 < x 2) :
    w (x, τ) = 0 := by
  have hmap : Continuous (fun t : ℝ => (show ParabolicPoint from (x, t))) :=
    continuous_prod_to_parabolicPoint.comp
      (continuous_const.prodMk continuous_id)
  have hslice : ContinuousOn (fun t : ℝ => w (x, t)) (Ico 0 1) :=
    hcont.comp hmap.continuousOn (fun t ht => ⟨hx, ht⟩)
  have hwithin : ContinuousWithinAt (fun t : ℝ => w (x, t))
      (Ioo 0 τ) τ := by
    apply (hslice τ ⟨hτ.le, hτ1⟩).mono
    intro t ht
    exact ⟨ht.1.le, ht.2.trans hτ1⟩
  have hclosure : τ ∈ closure (Ioo (0 : ℝ) τ) := by
    rw [closure_Ioo hτ.ne]
    exact ⟨hτ.le, le_rfl⟩
  exact hwithin.eq_const_of_mem_closure hclosure
    (fun t ht => hzero x hx t ht.1 ht.2)

end ESS
