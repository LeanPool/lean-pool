/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRieszExteriorDistribution

/-!
# Blowup Riesz Product Test

Pressure reconstruction and convergence bounds for the rescaled sequence.
-/

public section

open MeasureTheory Set CKN.Foundation.Parabolic
noncomputable section
namespace ESS

private theorem spatialLaplacian_mul_const
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (c : ℝ) (x : Vec3) :
    CKN.spatialLaplacian (fun y => ψ y * c) x =
      CKN.spatialLaplacian ψ x * c := by
  simp only [CKN.spatialLaplacian]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hfun : (fun y : Vec3 => (fderiv ℝ (fun w => ψ w * c) y)
      (CKN.basisVec i)) = (fun y => (fderiv ℝ ψ y) (CKN.basisVec i) * c) := by
    funext y
    rw [fderiv_mul_const (hd y) c]
    simp only [smul_apply, smul_eq_mul]
    ring
  change (fderiv ℝ (fun y : Vec3 => (fderiv ℝ (fun w => ψ w * c) y)
    (CKN.basisVec i)) x) (CKN.basisVec i) = _
  rw [hfun]
  have hd2 : Differentiable ℝ (fun y : Vec3 => (fderiv ℝ ψ y) (CKN.basisVec i)) := by
    have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ ψ) :=
      (contDiff_infty_iff_fderiv.mp hψ).2
    exact (hfd.clm_apply (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec3 => CKN.basisVec i))).differentiable (by norm_num)
  change (fderiv ℝ (fun y : Vec3 => (fderiv ℝ ψ y) (CKN.basisVec i) * c)
    x) (CKN.basisVec i) = _
  rw [fderiv_mul_const (hd2 x) c]
  simp only [smul_apply, smul_eq_mul]
  change c * (fderiv ℝ (fun y : Vec3 => (fderiv ℝ ψ y) (CKN.basisVec i))
    x) (CKN.basisVec i) =
    (fderiv ℝ (fun y : Vec3 => (fderiv ℝ ψ y) (CKN.basisVec i))
      x) (CKN.basisVec i) * c
  exact mul_comm _ _

theorem blowup_rieszPressureJointLaplacian_product
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (z : Vec3 × ℝ) :
    CKN.Leray.rieszPressureJointLaplacian
      (fun w : Vec3 × ℝ => ψ w.1 * θ w.2) z =
      θ z.2 * CKN.spatialLaplacian ψ z.1 := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => ψ w.1 * θ w.2) :=
    (hψ.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff).mul
      (hθ.comp (ContinuousLinearMap.snd ℝ Vec3 ℝ).contDiff)
  rw [← CKN.Leray.rieszPressure_sliceLaplacian_eq_joint hφ z]
  change CKN.spatialLaplacian (fun x : Vec3 => ψ x * θ z.2) z.1 = _
  rw [spatialLaplacian_mul_const hψ]
  ring

end ESS
