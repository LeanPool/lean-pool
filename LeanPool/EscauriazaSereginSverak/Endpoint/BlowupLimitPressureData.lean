/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitConclusion
public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitScaling

/-!
# Pressure-split data for the blow-up limit

The local hypotheses give the measurable whole-space pressure, bounded
source slices, and harmonic remainder used in the rescaled estimates.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

private theorem pressureSplit_source_velocity_slice_bound
    {u : ParabolicPoint → Vec3}
    (hFslice : ∀ᵐ s ∂volume.restrict pressureSplitTime,
      MemLp (fun x : Vec3 => pressureSplitVelocityExtension u (x,s)) 3 volume ∧
      eLpNorm (fun x : Vec3 => pressureSplitVelocityExtension u (x,s))
        3 volume ≤ ENNReal.ofReal (pressureSplitVelocityLpBound u)) :
    ∃ Mᵤ : ℝ≥0∞, Mᵤ < ⊤ ∧
      ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
        AEStronglyMeasurable (fun x : Vec3 => (goodPointDomain.indicator u) (x,s)) volume ∧
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm
          ((goodPointDomain.indicator u) (x,s))) 3 volume ≤ Mᵤ := by
  have hball : CKN.euclideanBall (0 : Vec3) 1 = vec3Ball 0 1 := by
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by norm_num)]
  let Mᵤ : ℝ≥0∞ := ENNReal.ofReal
    (Real.sqrt 3 * pressureSplitVelocityLpBound u)
  have hMᵤ : Mᵤ < ⊤ := ENNReal.ofReal_lt_top
  have hextEq (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0) :
      (fun x : Vec3 => (goodPointDomain.indicator u)
        (parabolicHomeomorph.symm (x,s))) =
        fun x => pressureSplitVelocityExtension u (x,s) := by
    funext x
    by_cases hx : x ∈ vec3Ball (0 : Vec3) 1
    · have hmem : parabolicHomeomorph.symm (x,s) ∈ goodPointDomain := by
        change x ∈ vec3Ball (0 : Vec3) 1 ∧ s ∈ Ioo (-1 : ℝ) 0
        exact ⟨hx, hs⟩
      have hb : x ∈ pressureSplitBall := by
        simpa [pressureSplitBall] using hx
      change goodPointDomain.indicator u
        (parabolicHomeomorph.symm (x,s)) =
          pressureSplitBall.indicator (fun y => u (y,s)) x
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hb]
      simp only [parabolicHomeomorph_symm_apply]
    · have hnot : parabolicHomeomorph.symm (x,s) ∉ goodPointDomain := by
        change ¬ (x ∈ vec3Ball (0 : Vec3) 1 ∧ s ∈ Ioo (-1 : ℝ) 0)
        exact fun h => hx h.1
      have hb : x ∉ pressureSplitBall := by
        simpa [pressureSplitBall] using hx
      change goodPointDomain.indicator u
        (parabolicHomeomorph.symm (x,s)) =
          pressureSplitBall.indicator (fun y => u (y,s)) x
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hb]
  have hextEq' (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0) :
      (fun x : Vec3 => (goodPointDomain.indicator u) (x,s)) =
        fun x => pressureSplitVelocityExtension u (x,s) := by
    simpa only [parabolicHomeomorph_symm_apply] using hextEq s hs
  have hsourceU : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 =>
        (goodPointDomain.indicator u) (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        ((goodPointDomain.indicator u) (x,s))) 3 volume ≤ Mᵤ := by
    filter_upwards [hFslice, self_mem_ae_restrict measurableSet_Ioo]
      with s hs hsI
    have hEuMeas : AEStronglyMeasurable
        (fun x : Vec3 => vec3EuclideanNorm
          (pressureSplitVelocityExtension u (x,s))) volume :=
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        hs.1.aestronglyMeasurable
    have hNormMeas : AEStronglyMeasurable
        (fun x : Vec3 => ‖pressureSplitVelocityExtension u (x,s)‖) volume :=
      continuous_norm.comp_aestronglyMeasurable
        hs.1.aestronglyMeasurable
    have hpoint (x : Vec3) :
        vec3EuclideanNorm (pressureSplitVelocityExtension u (x,s)) ≤
          Real.sqrt 3 * ‖pressureSplitVelocityExtension u (x,s)‖ :=
      CKN.Foundation.Parabolic.vec3EuclideanNorm_le_sqrt_three_mul_norm _
    have hLp : eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        (pressureSplitVelocityExtension u (x,s))) 3 volume ≤
        ENNReal.ofReal (Real.sqrt 3) *
          eLpNorm (fun x : Vec3 =>
            ‖pressureSplitVelocityExtension u (x,s)‖) 3 volume := by
      calc
        _ ≤ eLpNorm (fun x : Vec3 => Real.sqrt 3 *
              ‖pressureSplitVelocityExtension u (x,s)‖) 3 volume := by
          apply eLpNorm_mono_enorm_ae hEuMeas
          filter_upwards [] with x
          rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (vec3EuclideanNorm_nonneg _), abs_of_nonneg
              (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
          exact ENNReal.ofReal_le_ofReal (hpoint x)
        _ = ENNReal.ofReal (Real.sqrt 3) *
              eLpNorm (fun x : Vec3 =>
                ‖pressureSplitVelocityExtension u (x,s)‖) 3 volume := by
          rw [show (fun x : Vec3 => Real.sqrt 3 *
              ‖pressureSplitVelocityExtension u (x,s)‖) =
              Real.sqrt 3 • (fun x : Vec3 =>
                ‖pressureSplitVelocityExtension u (x,s)‖) by
              funext x
              simp only [Pi.smul_apply, smul_eq_mul]]
          rw [eLpNorm_const_smul]
          rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg 3)]
    have hnorm : eLpNorm (fun x : Vec3 =>
        ‖pressureSplitVelocityExtension u (x,s)‖) 3 volume =
          eLpNorm (fun x : Vec3 => pressureSplitVelocityExtension u (x,s))
            3 volume :=
      eLpNorm_norm _ hs.1.aestronglyMeasurable
    have hbound : eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        (pressureSplitVelocityExtension u (x,s))) 3 volume ≤ Mᵤ := by
      calc
        _ ≤ ENNReal.ofReal (Real.sqrt 3) *
            eLpNorm (fun x : Vec3 =>
              ‖pressureSplitVelocityExtension u (x,s)‖) 3 volume := hLp
        _ = ENNReal.ofReal (Real.sqrt 3) *
            eLpNorm (fun x : Vec3 => pressureSplitVelocityExtension u (x,s))
              3 volume := by rw [hnorm]
        _ ≤ ENNReal.ofReal (Real.sqrt 3) *
            ENNReal.ofReal (pressureSplitVelocityLpBound u) := by
              gcongr
              exact hs.2
        _ = Mᵤ := by
              dsimp [Mᵤ]
              rw [ENNReal.ofReal_mul (Real.sqrt_nonneg 3)]
    refine ⟨?_, ?_⟩
    · rw [hextEq' s hsI]
      exact hs.1.aestronglyMeasurable
    · have hnormeq :
          eLpNorm (fun x : Vec3 => vec3EuclideanNorm
            ((goodPointDomain.indicator u) (x,s))) 3 volume =
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
            (pressureSplitVelocityExtension u (x,s))) 3 volume := by
        congr 1
        funext x
        exact congrArg vec3EuclideanNorm (congrFun (hextEq' s hsI) x)
      rw [hnormeq]
      exact hbound
  exact ⟨Mᵤ, hMᵤ, hsourceU⟩

/-- The local source hypotheses determine all pressure and velocity slice
data needed for the blow-up estimates. -/
theorem blowup_limit_pressure_split_data
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hpmeas : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ‖u (x,t)‖ₑ ^ (2 : ℝ)) (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1) (fun x => u (x,t) i)
        (fun x => Du (x,t) i))
    (hS2 : ∀ ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0) :
    let F := pressureSplitTensor u
    let hF := pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
    let p₁ := pressureSplitRieszPressure F hF
    let p₂ := pressureSplitRemainder p p₁
    AEStronglyMeasurable p₁
        (volume.restrict (Set.univ ×ˢ Ioo (-1 : ℝ) 0)) ∧
      (∃ Mᵤ : ℝ≥0∞, Mᵤ < ⊤ ∧
        ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
          AEStronglyMeasurable (fun x : Vec3 =>
            (goodPointDomain.indicator u) (x,s)) volume ∧
          eLpNorm (fun x : Vec3 => vec3EuclideanNorm
            ((goodPointDomain.indicator u) (x,s))) 3 volume ≤ Mᵤ) ∧
      (∃ Mₚ : ℝ≥0∞, Mₚ < ⊤ ∧
        ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
          AEStronglyMeasurable (fun x : Vec3 => p₁ (x,s)) volume ∧
          eLpNorm (fun x : Vec3 => p₁ (x,s)) (3 / 2 : ℝ≥0∞) volume ≤ Mₚ) ∧
      MemLp (fun z : Vec3 × ℝ => p₂ (z.1,z.2)) (3 / 2 : ℝ≥0∞)
        ((volume.restrict (CKN.euclideanBall 0 1)).prod
          (volume.restrict (Ioo (-1 : ℝ) 0))) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 0),
        CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
          (fun x : Vec3 => p₂ (x,t))) := by
  dsimp only
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := pressureSplitTensor u
  let hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
  let p₁ : ParabolicPoint → ℝ := pressureSplitRieszPressure F hF
  let p₂ : ParabolicPoint → ℝ := pressureSplitRemainder p p₁
  let P : Vec3 × ℝ → ℝ :=
    CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF
  have hPmeas : Measurable P :=
    CKN.Leray.rieszPressureSpaceTime_measurable (3 / 2 : ℝ)
      (by norm_num) F hF
  have hp₁meas : Measurable p₁ := by
    change Measurable (fun z : ParabolicPoint => P (parabolicHomeomorph z))
    exact hPmeas.comp parabolicHomeomorph.measurable
  have hball : CKN.euclideanBall (0 : Vec3) 1 = vec3Ball 0 1 := by
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by norm_num)]
  have htime : Ioo (-1 : ℝ) 0 = pressureSplitTime := by
    rfl
  have hFslice := pressureSplitVelocityExtension_slice_memLp_bound hu hL3
  obtain ⟨Mᵤ, hMᵤ, hsourceU⟩ := pressureSplit_source_velocity_slice_bound hFslice
  let A : ℝ := CKN.Leray.rieszPressureOperatorBound
    (3 / 2 : ℝ) (by norm_num)
  let Mₚ : ℝ≥0∞ := ENNReal.ofReal
    (A * (9 * pressureSplitVelocityLpBound u ^ 2))
  have hMₚ : Mₚ < ⊤ := ENNReal.ofReal_lt_top
  have hsourceP : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => p₁ (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => p₁ (x,s)) (3 / 2 : ℝ≥0∞) volume ≤ Mₚ := by
    have hbound := pressureSplitRieszPressure_slice_bound
      hu hDu henergy hL3 hgrad
    filter_upwards [hbound] with s hs
    have hmeas : AEStronglyMeasurable (fun x : Vec3 => p₁ (x,s)) volume :=
      hs.1.aestronglyMeasurable
    have hnorm : eLpNorm (fun x : Vec3 => p₁ (x,s))
        (3 / 2 : ℝ≥0∞) volume ≤ Mₚ := by
      change eLpNorm (fun x : Vec3 =>
        pressureSplitRieszPressure (pressureSplitTensor u)
          (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad) (x,s))
        (3 / 2 : ℝ≥0∞) volume ≤ ENNReal.ofReal
          (A * (9 * pressureSplitVelocityLpBound u ^ 2))
      have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      simpa [A, hcoeff] using hs.2
    exact ⟨hmeas, hnorm⟩
  have hsplit := pressureSplit_remainder_harmonic_interior_bound
    hu hDu hpmeas hL2 henergy hp hL3 hgrad hS2 hS3
  have hp₂ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))) := by
    have hmeasure : (volume.restrict pressureSplitBall).prod
        (volume.restrict pressureSplitTime) =
          (volume : Measure (Vec3 × ℝ)).restrict pressureSplitProductDomain := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
      simp only [pressureSplitProductDomain]
    have hrestrict := hsplit.1.restrict pressureSplitProductDomain
    rw [← hmeasure] at hrestrict
    have heq : (fun z : Vec3 × ℝ =>
        pressureSplitRemainder p p₁ (parabolicHomeomorph.symm z)) =
          fun z => p₂ (z.1,z.2) := by
      funext z
      simp [p₂, p₁]
    have hlocal₀ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
        (ENNReal.ofReal (3 / 2 : ℝ))
        ((volume.restrict pressureSplitBall).prod
          (volume.restrict pressureSplitTime)) := by
      exact (memLp_congr_ae
        (Eventually.of_forall fun z => (congrFun heq z).symm)).2 hrestrict
    have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [← hcoeff]
    simpa only [pressureSplitBall, pressureSplitTime, hball] using hlocal₀
  have hharm : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 0),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p₂ (x,t)) := by
    rw [htime, hball]
    exact hsplit.2.1
  exact ⟨hp₁meas.aestronglyMeasurable.restrict,
    ⟨Mᵤ, hMᵤ, hsourceU⟩, ⟨Mₚ, hMₚ, hsourceP⟩, hp₂, hharm⟩

end ESS
