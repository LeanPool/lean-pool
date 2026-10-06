/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszCompactDecay

public section

open MeasureTheory Set Filter CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- The canonical space-time Riesz pressure has its Poisson distribution
identity against every smooth compact test. -/
theorem blowup_rieszPressureSpaceTime_compact_duality
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ z, CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        F hF z * CKN.Leray.rieszPressureJointLaplacian ψ z =
      -∑ i : Fin 3, ∑ j : Fin 3, ∫ z, F i j z *
        CKN.Leray.rieszPressureJointHessian ψ i j z :=
  CKN.Leray.rieszPressureSpaceTime_noncompactPotential_duality
    F hF hψ (blowup_compact_test_rieszPressurePotentialDecay hψ hψc)

/-- The pressure of a tensor supported outside a spatial region has zero
spatial Laplacian there in space-time distributions. -/
theorem blowup_rieszPressureSpaceTime_exterior_distribution_zero
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (U : Set Vec3)
    (hzero : ∀ i j z, z.1 ∈ U → F i j z = 0)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψU : ∀ z ∈ tsupport ψ, z.1 ∈ U) :
    ∫ z, CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        F hF z * CKN.Leray.rieszPressureJointLaplacian ψ z = 0 := by
  have hfirst (j : Fin 3) :
      tsupport (CKN.Leray.rieszPressureJointDirection ψ j) ⊆ tsupport ψ := by
    change tsupport (fun z => (fderiv ℝ ψ z) (CKN.basisVec j, (0 : ℝ))) ⊆
      tsupport ψ
    exact tsupport_fderiv_apply_subset ℝ (CKN.basisVec j, (0 : ℝ))
  have hsecond (i j : Fin 3) :
      tsupport (CKN.Leray.rieszPressureJointHessian ψ i j) ⊆
        tsupport ψ := by
    change tsupport (fun z =>
      (fderiv ℝ (CKN.Leray.rieszPressureJointDirection ψ j) z)
        (CKN.basisVec i, (0 : ℝ))) ⊆ tsupport ψ
    exact (tsupport_fderiv_apply_subset ℝ (CKN.basisVec i, (0 : ℝ))).trans
      (hfirst j)
  have hprod (i j : Fin 3) (z : Vec3 × ℝ) :
      F i j z * CKN.Leray.rieszPressureJointHessian ψ i j z = 0 := by
    by_cases hz : z.1 ∈ U
    · rw [hzero i j z hz, zero_mul]
    · have hnot : z ∉ tsupport
          (CKN.Leray.rieszPressureJointHessian ψ i j) := fun hm =>
        hz (hψU z (hsecond i j hm))
      rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  rw [blowup_rieszPressureSpaceTime_compact_duality F hF hψ hψc]
  simp only [hprod, integral_zero, Finset.sum_const_zero, neg_zero]

end ESS
