/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitConclusion
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureIntegrability

/-!
# Space-time pressure mass estimates for the fixed split

The uniform spatial pressure estimate also controls the local space-time
mass of the whole-space part.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Integrating the fixed-slice pressure estimate bounds the local space-time
`L^(3/2)` mass of the whole-space pressure by its uniform slice bound. -/
theorem pressureSplitRieszPressure_source_mass_bound
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
      (volume.restrict pressureSplitTime) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict pressureSplitTime), ∀ i : Fin 3,
      HasWeakGradientOn pressureSplitBall (fun x => u (x,t) i)
        (fun x => Du (x,t) i)) :
    ∫⁻ z in pressureSplitProductDomain,
      ENNReal.ofReal |pressureSplitRieszPressure (pressureSplitTensor u)
        (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad)
        (parabolicHomeomorph.symm z)| ^ (3 / 2 : ℝ) ≤
      ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound
        (3 / 2 : ℝ) (by norm_num) *
        (9 * pressureSplitVelocityLpBound u ^ 2)) ^ (3 / 2 : ℝ) := by
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := pressureSplitTensor u
  let hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
  let P : ParabolicPoint → ℝ := pressureSplitRieszPressure F hF
  have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hmeasure : (volume.restrict pressureSplitBall).prod
      (volume.restrict pressureSplitTime) =
        (volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
    simp only [pressureSplitProductDomain]
  have hPslice := pressureSplitRieszPressure_slice_bound hu hDu henergy hL3 hgrad
  have hslice : ∀ᵐ t ∂(volume.restrict pressureSplitTime),
      eLpNorm (fun x : Vec3 => P (x,t)) (3 / 2 : ℝ≥0∞)
        (volume.restrict pressureSplitBall) ≤
          ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound
            (3 / 2 : ℝ) (by norm_num) *
              (9 * pressureSplitVelocityLpBound u ^ 2)) := by
    filter_upwards [hPslice] with t ht
    calc
      _ ≤ eLpNorm (fun x : Vec3 => P (x,t)) (3 / 2 : ℝ≥0∞) volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound
          (3 / 2 : ℝ) (by norm_num) *
            (9 * pressureSplitVelocityLpBound u ^ 2)) := by
        simpa only [P, F, hF, pressureSplitRieszPressure, hcoeff] using ht.2
  have hPglobal : MemLp (fun z : Vec3 × ℝ =>
      P (parabolicHomeomorph.symm z)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    have h := CKN.Leray.rieszPressureSpaceTime_memLp (3 / 2 : ℝ)
      (by norm_num) F hF
    have heq : (fun z : Vec3 × ℝ => P (parabolicHomeomorph.symm z)) =
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF := by
      funext z
      change CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        F hF (parabolicHomeomorph (parabolicHomeomorph.symm z)) = _
      rw [parabolicHomeomorph.apply_symm_apply]
    exact (memLp_congr_ae (Eventually.of_forall fun z => (congrFun heq z).symm)).2 h
  have hPprod : AEStronglyMeasurable (fun z : Vec3 × ℝ =>
      P (parabolicHomeomorph.symm z))
      ((volume.restrict pressureSplitBall).prod
        (volume.restrict pressureSplitTime)) := by
    rw [hmeasure]
    exact (hPglobal.restrict pressureSplitProductDomain).aestronglyMeasurable
  have hTonelli := blowupScalarTimeThreeHalves_eq (Ω := pressureSplitBall)
    (J := pressureSplitTime) (fun z : ParabolicPoint =>
      P (parabolicHomeomorph.symm z)) hPprod
  have htime : (∫⁻ t in pressureSplitTime,
      eLpNorm (fun x : Vec3 => P (x,t)) (3 / 2 : ℝ≥0∞)
        (volume.restrict pressureSplitBall) ^ (3 / 2 : ℝ)) ≤
      (ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound
        (3 / 2 : ℝ) (by norm_num) *
          (9 * pressureSplitVelocityLpBound u ^ 2)) ^ (3 / 2 : ℝ)) := by
    calc
      _ ≤ ∫⁻ _t in pressureSplitTime,
          ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound
            (3 / 2 : ℝ) (by norm_num) *
              (9 * pressureSplitVelocityLpBound u ^ 2)) ^ (3 / 2 : ℝ) := by
        apply lintegral_mono_ae
        filter_upwards [hslice] with t ht
        exact ENNReal.rpow_le_rpow ht (by norm_num)
      _ = _ := by
        rw [setLIntegral_const]
        simp [pressureSplitTime]
  calc
    _ = ∫⁻ z, ENNReal.ofReal |P (parabolicHomeomorph.symm z)| ^
          (3 / 2 : ℝ)
          ∂((volume.restrict pressureSplitBall).prod
          (volume.restrict pressureSplitTime)) := by
      rw [← hmeasure]
    _ = ∫⁻ t in pressureSplitTime,
        eLpNorm (fun x : Vec3 => P (x,t)) (3 / 2 : ℝ≥0∞)
          (volume.restrict pressureSplitBall) ^ (3 / 2 : ℝ) := by
      simpa only [parabolicHomeomorph_symm_apply] using hTonelli.symm
    _ ≤ _ := htime

end ESS

end
