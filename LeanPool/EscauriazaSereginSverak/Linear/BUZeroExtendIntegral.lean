/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUZeroExtendBridge
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure

/-!
# Integrals of fields supported in a smaller cylinder

The product-coordinate integral of a field supported inside a target
cylinder equals its set integral on that cylinder.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- For a scalar integrand supported in a subset of a target cylinder,
the target set integral is the unrestricted product-coordinate integral. -/
theorem bu_target_setIntegral_eq_product_integral
    {Ω : Set Vec3} {I : Set ℝ} {K : Set ParabolicPoint}
    (hKsub : K ⊆ spaceTimeSet Ω I)
    (F : ParabolicPoint → ℝ)
    (hzero : ∀ z ∉ K, F z = 0) :
    (∫ z in spaceTimeSet Ω I, F z ∂(volume : Measure ParabolicPoint)) =
      ∫ q, F (parabolicHomeomorph.symm q)
        ∂(volume : Measure (Vec3 × ℝ)) := by
  rw [setIntegral_parabolic_to_product]
  apply bu_setIntegral_eq_integral_of_zero_off
  intro q hq
  have hz : parabolicHomeomorph.symm q ∉ K := by
    intro hK
    apply hq
    have hU := hKsub hK
    rcases q with ⟨y, s⟩
    exact hU
  exact hzero _ hz

end ESS
