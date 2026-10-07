/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureRemainder
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvariance

/-!
# Spatial scaling of the harmonic pressure supremum

Positive spatial dilations preserve essential suprema up to the pressure
amplitude, on any measurable region whose image stays in the interior ball.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The spatial pressure scaling is bounded by the source interior supremum
on every measurable region whose image lies in the three-quarter ball. -/
theorem pressureSplit_scaledSpatial_sup_le
    {Ω : Set Vec3} (hΩ : MeasurableSet Ω)
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r)
    (himage : ∀ x ∈ Ω, CKN.scalingSpace r x₀ x ∈
      CKN.euclideanBall (0 : Vec3) (3 / 4 : ℝ))
    (p : Vec3 → ℝ)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (CKN.euclideanBall (0 : Vec3) 1))) :
    eLpNorm (fun x : Vec3 => r ^ 2 * p (CKN.scalingSpace r x₀ x)) ⊤
      (volume.restrict Ω) ≤
      ENNReal.ofReal (r ^ 2) * eLpNorm p ⊤
        (volume.restrict (CKN.euclideanBall (0 : Vec3) (3 / 4 : ℝ))) := by
  let φ : Vec3 ≃ₜ Vec3 :=
    (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft x₀)
  have hφ : (fun x : Vec3 => φ x) = CKN.scalingSpace r x₀ := by
    funext x
    rfl
  let E : Set Vec3 := CKN.scalingSpace r x₀ '' Ω
  have hEmeas : MeasurableSet E := by
    dsimp [E]
    rw [← hφ]
    exact φ.measurableEmbedding.measurableSet_image.mpr hΩ
  have hpre : CKN.rescaledSpace r x₀ E = Ω := by
    change CKN.scalingSpace r x₀ ⁻¹' (CKN.scalingSpace r x₀ '' Ω) = Ω
    rw [← hφ]
    exact φ.preimage_image Ω
  have hmap : Measure.map φ (volume.restrict Ω) =
      ENNReal.ofReal (r⁻¹ ^ 3) • volume.restrict E := by
    have h := CKN.map_scalingSpace_restrict hr x₀ hEmeas
    rw [hpre] at h
    simpa only [hφ] using h
  have hcoef : ENNReal.ofReal (r⁻¹ ^ 3) ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (by positivity : 0 < r⁻¹ ^ 3)).ne'
  have hEsubset34 : E ⊆ CKN.euclideanBall (0 : Vec3) (3 / 4 : ℝ) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact himage x hx
  have hEsubset : E ⊆ CKN.euclideanBall (0 : Vec3) 1 := by
    intro y hy
    have hy34 : y ∈ CKN.euclideanBall (0 : Vec3) (3 / 4 : ℝ) := hEsubset34 hy
    have hnorm' := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by norm_num : (0 : ℝ) < 3 / 4)).mp hy34
    have hnorm : vec3EuclideanNorm y < 3 / 4 := by
      simpa [CKN.vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot,
        pow_two] using hnorm'
    apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by norm_num : (0 : ℝ) < 1)).mpr
    have hnormEq : CKN.vecEuclideanNorm y = vec3EuclideanNorm y := by
      simp [CKN.vecEuclideanNorm, vec3EuclideanNorm, vecNormSq, vecDot, pow_two]
    change CKN.vecEuclideanNorm (y - 0) < 1
    rw [sub_zero, hnormEq]
    exact lt_trans hnorm (by norm_num)
  have hBall34subset1 : CKN.euclideanBall (0 : Vec3) (3 / 4 : ℝ) ⊆
      CKN.euclideanBall (0 : Vec3) 1 := by
    intro y hy
    have hnorm := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by norm_num : (0 : ℝ) < 3 / 4)).mp hy
    apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by norm_num : (0 : ℝ) < 1)).mpr
    linarith only [hnorm, show (3 / 4 : ℝ) < 1 by norm_num]
  have hp34 : AEStronglyMeasurable p
      (volume.restrict (CKN.euclideanBall (0 : Vec3) (3 / 4 : ℝ))) :=
    hp.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume hBall34subset1)
  have hpE : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict E) :=
    hp.mono_measure (Measure.restrict_mono_set volume hEsubset)
  have hpMap : AEStronglyMeasurable p (Measure.map φ (volume.restrict Ω)) := by
    rw [hmap]
    exact hpE.aestronglyMeasurable.smul_measure _
  have hpcomp : AEStronglyMeasurable (fun x : Vec3 => p (φ x))
      (volume.restrict Ω) :=
    (φ.measurableEmbedding.aestronglyMeasurable_map_iff).1 hpMap
  have hscaled : AEStronglyMeasurable
      (fun x : Vec3 => r ^ 2 * p (CKN.scalingSpace r x₀ x))
      (volume.restrict Ω) := by
    simpa only [hφ] using hpcomp.const_mul (r ^ 2)
  have hsupMap : eLpNormEssSup p (Measure.map φ (volume.restrict Ω)) =
      eLpNormEssSup (fun x : Vec3 => p (φ x)) (volume.restrict Ω) :=
    φ.measurableEmbedding.eLpNormEssSup_map_measure
  have hsupE : eLpNormEssSup p (volume.restrict E) =
      eLpNormEssSup (fun x : Vec3 => p (φ x)) (volume.restrict Ω) := by
    calc
      _ = eLpNormEssSup p
          (ENNReal.ofReal (r⁻¹ ^ 3) • volume.restrict E) := by
            symm
            exact eLpNormEssSup_ennreal_smul_measure hcoef p
      _ = eLpNormEssSup p (Measure.map φ (volume.restrict Ω)) := by rw [hmap]
      _ = _ := hsupMap
  have hsupMono : eLpNormEssSup p (volume.restrict E) ≤
      eLpNormEssSup p (volume.restrict (CKN.euclideanBall (0 : Vec3) (3 / 4 : ℝ))) :=
    eLpNormEssSup_mono_measure p
      (Measure.absolutelyContinuous_of_le
        (Measure.restrict_mono_set volume hEsubset34))
  calc
    eLpNorm (fun x : Vec3 => r ^ 2 * p (CKN.scalingSpace r x₀ x)) ⊤
        (volume.restrict Ω) = eLpNormEssSup
          (fun x : Vec3 => r ^ 2 * p (CKN.scalingSpace r x₀ x))
          (volume.restrict Ω) := eLpNorm_exponent_top hscaled
    _ = ENNReal.ofReal (r ^ 2) *
        eLpNormEssSup (fun x : Vec3 => p (φ x))
          (volume.restrict Ω) := by
            have hfun : (fun x : Vec3 => r ^ 2 * p (CKN.scalingSpace r x₀ x)) =
                (r ^ 2) • (fun x : Vec3 => p (φ x)) := by
              funext x
              change r ^ 2 * p (CKN.scalingSpace r x₀ x) =
                r ^ 2 * p (φ x)
              rw [← congrFun hφ x]
            rw [hfun, eLpNormEssSup_const_smul]
            simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg r)]
    _ ≤ ENNReal.ofReal (r ^ 2) *
        eLpNormEssSup p (volume.restrict (CKN.euclideanBall (0 : Vec3) (3 / 4 : ℝ))) := by
            rw [← hsupE]
            gcongr
    _ = ENNReal.ofReal (r ^ 2) * eLpNorm p ⊤
        (volume.restrict (CKN.euclideanBall (0 : Vec3) (3 / 4 : ℝ))) := by
            rw [eLpNorm_exponent_top hp34]

end ESS

end
