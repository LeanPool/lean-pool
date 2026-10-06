/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineGeometry

/-!
# High-contrast homogenization: Analytic.AffinePairing

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Pairings under an invertible affine normalization

An invertible matrix transports absolute integrability between a set and its
linear image.  Consequently the determinant Jacobian cancels in the normalized
duality pairing.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Multiplication by an invertible matrix is a measurable embedding. -/
theorem measurableEmbedding_matVecMul {L : Mat d} (hL : IsUnit L.det) :
    MeasurableEmbedding (matVecMul L : Vec d → Vec d) :=
  (continuous_matVecMul L).measurableEmbedding
    (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det L).mpr hL))

/-- Pulling a compactly supported smooth vector test back by an invertible
matrix gives a test on the inverse-image domain. -/
theorem IsLocalVecTest.comp_matVecMul {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} {psi : Vec d → Vec d}
    (hpsi : IsLocalVecTest (matImage L U) psi) :
    IsLocalVecTest U (fun y => psi (matVecMul L y)) := by
  let e : Vec d ≃ₜ Vec d :=
    { toFun := matVecMul L
      invFun := matVecMul L⁻¹
      left_inv := fun x => by
        rw [matVecMul_mul, Matrix.nonsing_inv_mul L hL, matVecMul_one]
      right_inv := fun x => by
        rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
      continuous_toFun := continuous_matVecMul L
      continuous_invFun := continuous_matVecMul L⁻¹ }
  refine ⟨?_, ?_, ?_⟩
  · let T : Vec d →L[ℝ] Vec d :=
      LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
    change ContDiff ℝ (⊤ : ℕ∞) (psi ∘ T)
    exact hpsi.contDiff.comp T.contDiff
  · show HasCompactSupport (psi ∘ e)
    simpa [e, Function.comp_def] using hpsi.hasCompactSupport.comp_homeomorph e
  · intro y hy
    have hy' : matVecMul L y ∈ tsupport psi := by
      rw [show (fun z => psi (matVecMul L z)) = psi ∘ e by rfl,
        tsupport_comp_eq_preimage psi e] at hy
      exact hy
    rcases hpsi.tsupport_subset hy' with ⟨z, hz, hzy⟩
    exact (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det L).mpr hL) hzy).symm ▸ hz

/-- Absolute integrability is equivalent before and after an invertible linear
change of variables. -/
theorem integrableOn_matImage_iff {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (f : Vec d → F) :
    IntegrableOn f (matImage L U) volume ↔
      IntegrableOn (fun y ↦ f (matVecMul L y)) U volume := by
  have hc_pos : 0 < |L.det|⁻¹ := inv_pos.mpr (abs_pos.mpr hL.ne_zero)
  have hc_zero : ENNReal.ofReal (|L.det|⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hc_pos
  have hmap :
      Integrable f
          (Measure.map (matVecMul L) (volume.restrict U)) ↔
        Integrable (fun y ↦ f (matVecMul L y)) (volume.restrict U) :=
    (measurableEmbedding_matVecMul hL).integrable_map_iff
  rw [map_restrict_volume_matVecMul hL hU] at hmap
  exact
    (integrable_smul_measure hc_zero ENNReal.ofReal_ne_top).symm.trans
      hmap

/-- Normalized nonnegative averages are unchanged after affine pullback. -/
theorem eVolumeAverage_matImage {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (f : Vec d → ℝ≥0∞) :
    eVolumeAverage (matImage L U) f =
      eVolumeAverage U (fun y ↦ f (matVecMul L y)) := by
  let T : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
  have hderiv : ∀ x ∈ U,
      HasFDerivWithinAt (matVecMul L) T U x := by
    intro x _hx
    exact (T.hasFDerivAt.congr_of_eventuallyEq (by
      filter_upwards with z
      rfl)).hasFDerivWithinAt
  have hinj : Set.InjOn (matVecMul L) U :=
    (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det L).mpr hL)).injOn
  have hTdet : T.det = L.det := by
    dsimp [T]
    rw [← Matrix.toLin'_apply']
    exact LinearMap.det_toLin' L
  have hchange' :=
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      hU hderiv hinj f
  have ha_zero : ENNReal.ofReal |L.det| ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr hL.ne_zero)
  have hnum :
      (∫⁻ x in matImage L U, f x ∂volume) =
        ENNReal.ofReal |L.det| *
          ∫⁻ y in U, f (matVecMul L y) ∂volume := by
    change (∫⁻ x in matVecMul L '' U, f x ∂volume) = _
    rw [hchange']
    simp_rw [hTdet]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  unfold eVolumeAverage
  rw [hnum, volume_matImage]
  exact ENNReal.mul_div_mul_left _ _ ha_zero ENNReal.ofReal_ne_top

/-- The normalized scalar `L²` norm is invariant under simultaneous affine
transport of the domain and field. -/
theorem normalizedL2Norm_matImage {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (v : Vec d → ℝ) :
    normalizedL2Norm (matImage L U) v =
      normalizedL2Norm U (fun y ↦ v (matVecMul L y)) := by
  unfold normalizedL2Norm
  rw [eVolumeAverage_matImage hL hU]

/-- The symmetric energy density is invariant under the dual affine actions on
gradients and fluxes. -/
theorem affineCoefficient_symmetric_energy {L : Mat d} (hL : IsUnit L.det)
    (a : CoeffField d) (y xi : Vec d) :
    vecDot (matVecMul (matTranspose L) xi)
        (matVecMul (symmPart (affineCoefficient L hL a y))
          (matVecMul (matTranspose L) xi)) =
      vecDot xi
        (matVecMul (symmPart (a (matVecMul L y))) xi) := by
  rw [symmPart_affineCoefficient_apply]
  simpa only [affineCoefficient_apply] using
    affineCoefficient_energy hL (fun x ↦ symmPart (a x)) y xi

/-- The normalized coefficient-weighted gradient norm is invariant under the
divergence-form affine pullback. -/
theorem weightedGradNorm_matImage {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U)
    (a : CoeffField d) (F : Vec d → Vec d) :
    weightedGradNorm a (matImage L U) F =
      weightedGradNorm (affineCoefficient L hL a) U
        (fun y ↦ matVecMul (matTranspose L) (F (matVecMul L y))) := by
  unfold weightedGradNorm
  rw [eVolumeAverage_matImage hL hU]
  congr 2
  funext y
  rw [affineCoefficient_symmetric_energy hL]

/-- The normalized pairing is unchanged when both fields are pulled back by
the same invertible coordinate map. -/
theorem dualPairing_matImage {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U)
    (F psi : Vec d → Vec d) :
    dualPairing (matImage L U) F psi =
      dualPairing U (fun y ↦ F (matVecMul L y))
        (fun y ↦ psi (matVecMul L y)) := by
  classical
  have hint := integrableOn_matImage_iff hL hU
    (fun x ↦ vecDot (F x) (psi x))
  unfold dualPairing
  by_cases h :
      IntegrableOn (fun x ↦ vecDot (F x) (psi x))
        (matImage L U) volume
  · rw [ite_eq_left h, ite_eq_left (hint.mp h)]
    congr 1
    rw [volumeAverage_matImage hL hU]
  · rw [ite_eq_right h, ite_eq_right (mt hint.mpr h)]

end

end HighContrast
end HCPolySupport
