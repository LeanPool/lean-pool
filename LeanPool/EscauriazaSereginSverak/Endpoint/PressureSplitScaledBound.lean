/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitScaleSpatial
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTimeAE

/-!
# Mixed-norm scaling of the harmonic pressure remainder

The interior slice supremum scales with degree two in space, and the time
change of variables leaves the critical factor `R`.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The zero-extended rescaled harmonic remainder has a mixed spatial
`L∞` time `L^(3/2)` bound with the critical linear scale factor. -/
theorem blowupPressureRemainder_mixed_sup_scale_bound
    (p₂ : ParabolicPoint → ℝ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    {Ω : Set Vec3} (hΩ : MeasurableSet Ω)
    (himage : ∀ x ∈ Ω, CKN.scalingSpace r x₀ x ∈
      CKN.euclideanBall 0 (3 / 4 : ℝ)) :
    (∫⁻ t : ℝ,
      eLpNorm (fun x : Vec3 => parabolicRescalePressure x₀ t₀ r
        (goodPointDomain.indicator p₂) (x,t)) ⊤
        (volume.restrict Ω) ^ (3 / 2 : ℝ)) ≤
      ENNReal.ofReal r *
        (∫⁻ s : ℝ, blowupHarmonicSupExtended p₂ s ^ (3 / 2 : ℝ)) := by
  let I : Set ℝ := Ioo (-1 : ℝ) 0
  let J : Set ℝ := CKN.rescaledTime r t₀ I
  have hI : MeasurableSet I := by simpa only [I] using measurableSet_Ioo
  have hJ : MeasurableSet J := by
    dsimp [J, CKN.rescaledTime]
    exact hI.preimage (by
      unfold CKN.scalingTime
      fun_prop)
  have hpSlice : ∀ᵐ s ∂(volume.restrict I),
      MemLp (fun x : Vec3 => p₂ (x,s)) (3 / 2 : ℝ≥0∞)
        (volume.restrict (CKN.euclideanBall 0 1)) :=
    pressureSlice_memLp_ae (J := I) p₂ (by simpa only [I] using hp₂)
  have hpull := blowup_ae_time_pullback r t₀ hr I hI
    (fun s => MemLp (fun x : Vec3 => p₂ (x,s)) (3 / 2 : ℝ≥0∞)
      (volume.restrict (CKN.euclideanBall 0 1))) hpSlice
  have hinside : ∀ᵐ t ∂(volume.restrict J),
      eLpNorm (fun x : Vec3 => parabolicRescalePressure x₀ t₀ r
        (goodPointDomain.indicator p₂) (x,t)) ⊤
          (volume.restrict Ω) ≤
        ENNReal.ofReal (r ^ 2) * blowupHarmonicSupExtended p₂
          (CKN.scalingTime r t₀ t) := by
    filter_upwards [hpull, ae_restrict_mem hJ] with t hslice htJ
    have hs : CKN.scalingTime r t₀ t ∈ I := htJ
    have hfun : (fun x : Vec3 => parabolicRescalePressure x₀ t₀ r
        (goodPointDomain.indicator p₂) (x,t)) =ᵐ[volume.restrict Ω]
          fun x : Vec3 => r ^ 2 * p₂
            (CKN.scalingSpace r x₀ x, CKN.scalingTime r t₀ t) := by
      filter_upwards [ae_restrict_mem hΩ] with x hx
      have hx34 : CKN.scalingSpace r x₀ x ∈
          CKN.euclideanBall 0 (3 / 4 : ℝ) := himage x hx
      have hx1 : CKN.scalingSpace r x₀ x ∈ CKN.euclideanBall 0 1 := by
        have hnorm := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
          (by norm_num : (0 : ℝ) < 3 / 4)).mp hx34
        apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
          (by norm_num : (0 : ℝ) < 1)).mpr
        linarith only [hnorm, show (3 / 4 : ℝ) < 1 by norm_num]
      have hxball : CKN.scalingSpace r x₀ x ∈ vec3Ball 0 1 := by
        rw [← CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
          (by norm_num : (0 : ℝ) < 1)]
        exact hx1
      have hpoint :
          (parabolicTranslate x₀ t₀ (parabolicScale r (x,t)) : ParabolicPoint) ∈
            goodPointDomain := by
        change CKN.scalingSpace r x₀ x ∈ vec3Ball 0 1 ∧
          CKN.scalingTime r t₀ t ∈ Ioo (-1 : ℝ) 0
        simpa only [I] using ⟨hxball, hs⟩
      change r ^ 2 * goodPointDomain.indicator p₂
          (parabolicTranslate x₀ t₀ (parabolicScale r (x,t))) = _
      rw [Set.indicator_of_mem hpoint]
      rfl
    rw [eLpNorm_congr_ae hfun]
    have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have hslice' : MemLp (fun x : Vec3 => p₂ (x, CKN.scalingTime r t₀ t))
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (CKN.euclideanBall 0 1)) := by
      rw [hcoeff]
      exact hslice
    have hspatial := pressureSplit_scaledSpatial_sup_le hΩ hr himage
      (fun x : Vec3 => p₂ (x, CKN.scalingTime r t₀ t)) hslice'
    calc
      _ ≤ ENNReal.ofReal (r ^ 2) * eLpNorm
          (fun x : Vec3 => p₂ (x, CKN.scalingTime r t₀ t)) ⊤
            (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))) := hspatial
      _ = _ := by
        rw [show blowupHarmonicSupExtended p₂ (CKN.scalingTime r t₀ t) =
          eLpNorm (fun x : Vec3 => p₂ (x, CKN.scalingTime r t₀ t)) ⊤
            (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ)) ) by
              dsimp [blowupHarmonicSupExtended]
              exact Set.indicator_of_mem hs _]
  have houtside : ∀ᵐ t ∂(volume.restrict Jᶜ),
      eLpNorm (fun x : Vec3 => parabolicRescalePressure x₀ t₀ r
        (goodPointDomain.indicator p₂) (x,t)) ⊤
          (volume.restrict Ω) ≤
        ENNReal.ofReal (r ^ 2) * blowupHarmonicSupExtended p₂
          (CKN.scalingTime r t₀ t) := by
    filter_upwards [ae_restrict_mem hJ.compl] with t htJ
    have hs : CKN.scalingTime r t₀ t ∉ I := by
      intro hs
      exact htJ (show t ∈ J by
        dsimp [J, CKN.rescaledTime]
        exact hs)
    have hzero (x : Vec3) : parabolicRescalePressure x₀ t₀ r
        (goodPointDomain.indicator p₂) (x,t) = 0 := by
      simp only [parabolicRescalePressure, parabolicTranslate, parabolicScale,
        goodPointDomain]
      apply mul_eq_zero_of_right
      exact Set.indicator_of_notMem (by
        intro hz
        exact hs hz.2) _
    have hnorm : (fun x : Vec3 => parabolicRescalePressure x₀ t₀ r
        (goodPointDomain.indicator p₂) (x,t)) = fun _ => 0 := by
      funext x
      exact hzero x
    rw [hnorm]
    have hnormzero : eLpNorm (fun x : Vec3 => (0 : ℝ)) ⊤
        (volume.restrict Ω) = 0 := eLpNorm_zero
    rw [hnormzero]
    rw [show blowupHarmonicSupExtended p₂ (CKN.scalingTime r t₀ t) = 0 by
      dsimp [blowupHarmonicSupExtended]
      exact Set.indicator_of_notMem hs _]
    simp
  have hAE : ∀ᵐ t ∂(volume : Measure ℝ),
      eLpNorm (fun x : Vec3 => parabolicRescalePressure x₀ t₀ r
        (goodPointDomain.indicator p₂) (x,t)) ⊤
          (volume.restrict Ω) ^ (3 / 2 : ℝ) ≤
        (ENNReal.ofReal (r ^ 2) * blowupHarmonicSupExtended p₂
          (CKN.scalingTime r t₀ t)) ^ (3 / 2 : ℝ) := by
    have h := ae_of_ae_restrict_of_ae_restrict_compl J hinside houtside
    filter_upwards [h] with t ht
    exact ENNReal.rpow_le_rpow ht (by norm_num)
  calc
    _ ≤ ∫⁻ t : ℝ,
        (ENNReal.ofReal (r ^ 2) * blowupHarmonicSupExtended p₂
          (CKN.scalingTime r t₀ t)) ^ (3 / 2 : ℝ) := lintegral_mono_ae hAE
    _ = ENNReal.ofReal r *
        (∫⁻ s : ℝ, blowupHarmonicSupExtended p₂ s ^ (3 / 2 : ℝ)) := by
      let g : ℝ → ℝ≥0∞ := fun s => blowupHarmonicSupExtended p₂ s ^ (3 / 2 : ℝ)
      have hscaleTime : MeasurePreserving (CKN.scalingTime r t₀)
          (volume : Measure ℝ)
          (ENNReal.ofReal ((r ^ 2)⁻¹) • (volume : Measure ℝ)) := by
        refine ⟨?_, CKN.map_scalingTime r hr t₀⟩
        unfold CKN.scalingTime
        fun_prop
      have htime := hscaleTime.lintegral_comp_emb
        ((Homeomorph.smulOfNeZero (r ^ 2) (sq_pos_of_pos hr).ne' |>.trans
          (Homeomorph.addLeft t₀)).measurableEmbedding) g
      rw [lintegral_smul_measure] at htime
      have hpow : (r ^ 2) ^ (3 / 2 : ℝ) = r ^ 3 := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_natCast r 3,
          ← Real.rpow_mul hr.le]
        norm_num
      have hpoint (s : ℝ) :
          (ENNReal.ofReal (r ^ 2) * blowupHarmonicSupExtended p₂ s) ^
              (3 / 2 : ℝ) =
            ENNReal.ofReal (r ^ 3) * g s := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 2)]
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg r)
          (by norm_num : (0 : ℝ) ≤ 3 / 2), hpow]
      simp_rw [hpoint]
      rw [lintegral_const_mul' (ENNReal.ofReal (r ^ 3)) _ ENNReal.ofReal_ne_top,
        htime]
      have hcoeff : ENNReal.ofReal (r ^ 3) * ENNReal.ofReal ((r ^ 2)⁻¹) =
          ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ 3)]
        congr 1
        field_simp
      change ENNReal.ofReal (r ^ 3) *
          (ENNReal.ofReal ((r ^ 2)⁻¹) * (∫⁻ s : ℝ, g s)) =
        ENNReal.ofReal r * (∫⁻ s : ℝ, g s)
      rw [← mul_assoc, hcoeff]

end ESS

end
