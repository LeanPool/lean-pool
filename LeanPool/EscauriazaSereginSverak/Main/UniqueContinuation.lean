/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCRadiusIteration
public import LeanPool.EscauriazaSereginSverak.Linear.UCOriginTrace
public import LeanPool.EscauriazaSereginSverak.Linear.UCFlatness

/-!
# Unique continuation across a spatial boundary

Infinite-order pointwise vanishing at the origin propagates throughout the
initial spatial ball under the backward parabolic differential inequality.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS.Main

/-- Unique continuation across spatial boundaries (`thm:uc`; ESS Theorem 4.1). -/
theorem uniqueContinuation (R T c₁ : ℝ) (hR : 0 < R) (hT : 0 < T) (hc₁ : 0 < c₁)
    (w : ParabolicPoint → Vec3) (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w (vec3Ball 0 R ×ˢ Ico 0 T))
    (hderiv : CKN.HasSpaceTimeWeakDerivs (vec3Ball 0 R) (Ioo 0 T) w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 R) (Ioo 0 T),
        ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict (spaceTimeSet (vec3Ball 0 R) (Ioo 0 T))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        c₁ * (vec3EuclideanNorm (w z) + Real.sqrt (spatialGradientSq w Dw z)))
    (hvanish : ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ spaceTimeSet (vec3Ball 0 R) (Ioo 0 T),
      vec3EuclideanNorm (w z) ≤ C * (vec3EuclideanNorm z.1 + Real.sqrt z.2) ^ k) :
    ∀ x ∈ vec3Ball 0 R, w (x, 0) = 0 := by
  have hflat := ESS.uc_pointwise_to_integral_flatness R T hT w hvanish
  have hzero := ESS.uc_origin_trace_zero R T hR hT w hcont hvanish
  change ∀ᵐ z ∂(volume.restrict (spaceTimeSet (vec3Ball 0 R) (Ioo 0 T))),
    vec3EuclideanNorm (ESS.ucWeakHeatVector D2w Dtw z) ≤
      c₁ * (vec3EuclideanNorm (w z) + Real.sqrt (spatialGradientSq w Dw z)) at hineq
  exact ESS.uc_radius_iteration R T c₁ hR hT hc₁ w Dw D2w Dtw
    hcont hderiv hL2 hineq hzero hflat

end ESS.Main
