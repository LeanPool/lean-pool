/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupHarmonicTime

/-!
# Vanishing critical energy at a zero limit

Strong local convergence of the velocity and pressure to zero makes the
unit-cylinder critical energy vanish (`prop:blowup-limit`).
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- On the unit past cylinder, the critical energy is the sum of the scalar
`L³` and `L^(3/2)` norm powers. -/
theorem blowupUnitEnergy_eq_eLpNorm_powers
    (v : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hv : AEStronglyMeasurable (fun z => vec3EuclideanNorm (v z))
      (volume.restrict (goodPointPastCylinder 0 0 1)))
    (hp : AEStronglyMeasurable p
      (volume.restrict (goodPointPastCylinder 0 0 1))) :
    goodPointEnergy v p 0 0 1 =
      eLpNorm (fun z => vec3EuclideanNorm (v z))
          (3 : ℝ≥0∞)
          (volume.restrict (goodPointPastCylinder 0 0 1)) ^ (3 : ℝ) +
        eLpNorm p (3 / 2 : ℝ≥0∞)
          (volume.restrict (goodPointPastCylinder 0 0 1)) ^ (3 / 2 : ℝ) := by
  rw [goodPointEnergy_eq_open_top]
  have hvm : AEMeasurable
      (fun z => ENNReal.ofReal (vec3EuclideanNorm (v z)) ^ (3 : ℝ))
      (volume.restrict (goodPointPastCylinder 0 0 1)) := by
    exact (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable hv.aemeasurable))
  rw [lintegral_add_left' hvm]
  have hV :
      eLpNorm (fun z => vec3EuclideanNorm (v z))
          (3 : ℝ≥0∞)
          (volume.restrict (goodPointPastCylinder 0 0 1)) ^ (3 : ℝ) =
        ∫⁻ z in goodPointPastCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (v z)) ^ (3 : ℝ) := by
    have h := eLpNorm_nnreal_pow_eq_lintegral
      (p := (3 : NNReal)) (f := fun z => vec3EuclideanNorm (v z))
      (by norm_num) hv
    norm_num at h ⊢
    simpa [Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using h
  have hP :
      eLpNorm p (3 / 2 : ℝ≥0∞)
          (volume.restrict (goodPointPastCylinder 0 0 1)) ^ (3 / 2 : ℝ) =
        ∫⁻ z in goodPointPastCylinder 0 0 1,
          ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) := by
    have h := eLpNorm_nnreal_pow_eq_lintegral
      (p := (3 / 2 : NNReal)) (f := p) (by norm_num) hp
    norm_num at h ⊢
    simpa [Real.enorm_eq_ofReal_abs] using h
  rw [← hV, ← hP]

/-- Strong `L³` velocity convergence and strong `L^(3/2)` pressure convergence
to zero force the rescaled critical energy to vanish. -/
theorem blowupUnitEnergy_tendsto_zero
    (v : ℕ → ParabolicPoint → Vec3) (p : ℕ → ParabolicPoint → ℝ)
    (hv : ∀ k, AEStronglyMeasurable (fun z => vec3EuclideanNorm (v k z))
      (volume.restrict (goodPointPastCylinder 0 0 1)))
    (hp : ∀ k, AEStronglyMeasurable (p k)
      (volume.restrict (goodPointPastCylinder 0 0 1)))
    (hV : Tendsto (fun k => eLpNorm (fun z => vec3EuclideanNorm (v k z))
      (3 : ℝ≥0∞) (volume.restrict (goodPointPastCylinder 0 0 1)))
      atTop (nhds 0))
    (hP : Tendsto (fun k => eLpNorm (p k) (3 / 2 : ℝ≥0∞)
      (volume.restrict (goodPointPastCylinder 0 0 1)))
      atTop (nhds 0)) :
    Tendsto (fun k => goodPointEnergy (v k) (p k) 0 0 1)
      atTop (nhds 0) := by
  have hVpow : Tendsto (fun k =>
      eLpNorm (fun z => vec3EuclideanNorm (v k z)) (3 : ℝ≥0∞)
        (volume.restrict (goodPointPastCylinder 0 0 1)) ^ (3 : ℝ))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using (ENNReal.continuous_rpow_const (y := (3 : ℝ))).continuousAt.tendsto.comp hV
  have hPpow : Tendsto (fun k =>
      eLpNorm (p k) (3 / 2 : ℝ≥0∞)
        (volume.restrict (goodPointPastCylinder 0 0 1)) ^ (3 / 2 : ℝ))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using (ENNReal.continuous_rpow_const (y := (3 / 2 : ℝ))).continuousAt.tendsto.comp hP
  have hsum := hVpow.add hPpow
  have heq : (fun k => goodPointEnergy (v k) (p k) 0 0 1) =
      (fun k =>
        eLpNorm (fun z => vec3EuclideanNorm (v k z)) (3 : ℝ≥0∞)
            (volume.restrict (goodPointPastCylinder 0 0 1)) ^ (3 : ℝ) +
          eLpNorm (p k) (3 / 2 : ℝ≥0∞)
            (volume.restrict (goodPointPastCylinder 0 0 1)) ^ (3 / 2 : ℝ)) := by
    funext k
    exact blowupUnitEnergy_eq_eLpNorm_powers (v k) (p k) (hv k) (hp k)
  rw [heq]
  simpa only [zero_add] using hsum

end ESS
