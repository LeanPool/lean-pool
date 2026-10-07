/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitScaledResult
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSliceScaling

/-!
# Critical scaling in the fixed pressure split

The velocity and whole-space pressure have invariant critical slice masses.
The harmonic remainder has vanishing mixed supremum mass on each bounded
spatial region under rescaling.
-/

public section


open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The fixed whole-space pressure has the claimed essentially uniform
spatial `L^(3/2)` bound on the source time interval. -/
theorem pressureSplitRieszPressure_essSup_slice_bound
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
    let F := pressureSplitTensor u
    let hF := pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
    essSup (fun t : ℝ => eLpNorm (fun x : Vec3 =>
      pressureSplitRieszPressure F hF ((x,t) : ParabolicPoint))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume)
      (volume.restrict pressureSplitTime) ≤
        ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound
          (3 / 2 : ℝ) (by norm_num) *
          (9 * pressureSplitVelocityLpBound u ^ 2)) := by
  dsimp only
  have hslice := pressureSplitRieszPressure_slice_bound hu hDu
    henergy hL3 hgrad
  have hbound : (fun t : ℝ => eLpNorm (fun x : Vec3 =>
      pressureSplitRieszPressure (pressureSplitTensor u)
        (pressureSplitTensor_memLp hu hDu henergy hL3 hgrad)
        ((x,t) : ParabolicPoint)) (ENNReal.ofReal (3 / 2 : ℝ)) volume) ≤ᵐ[
        volume.restrict pressureSplitTime]
      fun _ => ENNReal.ofReal
        (CKN.Leray.rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
          (9 * pressureSplitVelocityLpBound u ^ 2)) := by
    filter_upwards [hslice] with t ht
    exact ht.2
  exact essSup_le_of_ae_le _ hbound (by
    change IsCobounded (· ≤ ·) (Filter.map _ _)
    exact ⟨0, fun _ _ => bot_le⟩)

/-- The critical velocity and whole-space pressure slice masses are invariant
under the parabolic rescaling of the fixed pressure split. -/
theorem pressureSplit_rescaled_critical_slice_masses
    {u : ParabolicPoint → Vec3} {p₁ : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
      (volume.restrict pressureSplitTime) < ⊤)
    (hp₁ : ∀ᵐ s ∂(volume.restrict pressureSplitTime),
      MemLp (fun x : Vec3 => p₁ (x,s))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    ∀ᵐ t ∂volume,
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm
          (parabolicRescaleVelocity x₀ t₀ r
            (goodPointDomain.indicator u) (x,t))) ^ (3 : ℝ)) =
          ∫⁻ y : Vec3, ENNReal.ofReal (vec3EuclideanNorm
            (goodPointDomain.indicator u
              (parabolicHomeomorph.symm (y, CKN.scalingTime r t₀ t)))) ^
            (3 : ℝ) ∧
      (∫⁻ x : Vec3,
        ENNReal.ofReal (abs (parabolicRescalePressure x₀ t₀ r
          (fun z : ParabolicPoint =>
            (Ioo (-1 : ℝ) 0).indicator (fun s => p₁ (z.1,s)) z.2)
          (x,t))) ^ (3 / 2 : ℝ)) =
          ∫⁻ y : Vec3, ENNReal.ofReal (abs
            ((Ioo (-1 : ℝ) 0).indicator (fun s => p₁ (y,s))
              (CKN.scalingTime r t₀ t))) ^ (3 / 2 : ℝ) := by
  let uExt : ParabolicPoint → Vec3 := goodPointDomain.indicator u
  let p1Ext : ParabolicPoint → ℝ := fun z =>
    (Ioo (-1 : ℝ) 0).indicator (fun s => p₁ (z.1,s)) z.2
  have hvelI := pressureSplitVelocityExtension_slice_memLp_bound hu hL3
  have hvelInside : ∀ᵐ s ∂(volume.restrict pressureSplitTime),
    AEStronglyMeasurable (fun y : Vec3 =>
      uExt (parabolicHomeomorph.symm (y,s))) volume := by
    filter_upwards [hvelI, ae_restrict_mem measurableSet_Ioo] with s ⟨hslice, _⟩ hs
    have heq : (fun y : Vec3 => uExt (parabolicHomeomorph.symm (y,s))) =
        fun y => pressureSplitVelocityExtension u (y,s) := by
      funext y
      change goodPointDomain.indicator u
          (parabolicHomeomorph.symm (y,s)) =
        pressureSplitBall.indicator (fun x => u (x,s)) y
      by_cases hy : y ∈ pressureSplitBall
      · have hmem : parabolicHomeomorph.symm (y,s) ∈ goodPointDomain := by
          change y ∈ vec3Ball 0 1 ∧ s ∈ Ioo (-1 : ℝ) 0
          exact ⟨by simpa [pressureSplitBall] using hy,
            by simpa [pressureSplitTime] using hs⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hy]
        simp only [parabolicHomeomorph_symm_apply]
      · have hnot : parabolicHomeomorph.symm (y,s) ∉ goodPointDomain := by
          intro hz
          exact hy (by
            change y ∈ vec3Ball 0 1 ∧ s ∈ Ioo (-1 : ℝ) 0 at hz
            simpa [pressureSplitBall] using hz.1)
        rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hy]
    rw [heq]
    exact hslice.aestronglyMeasurable
  have hvelOutside : ∀ᵐ s ∂(volume.restrict pressureSplitTimeᶜ),
    AEStronglyMeasurable (fun y : Vec3 =>
      uExt (parabolicHomeomorph.symm (y,s))) volume := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with s hs
    have hs' : s ∉ Ioo (-1 : ℝ) 0 := by
      simpa only [Set.mem_compl_iff, pressureSplitTime] using hs
    have heq : (fun y : Vec3 => uExt (parabolicHomeomorph.symm (y,s))) =
        fun _ => (0 : Vec3) := by
      funext y
      change goodPointDomain.indicator u
        (parabolicHomeomorph.symm (y,s)) = 0
      have hnot : parabolicHomeomorph.symm (y,s) ∉ goodPointDomain := by
        intro hz
        exact hs' (by
          change y ∈ vec3Ball 0 1 ∧ s ∈ Ioo (-1 : ℝ) 0 at hz
          exact hz.2)
      apply Set.indicator_of_notMem
      exact hnot
    rw [heq]
    exact aestronglyMeasurable_const
  have hvelSource : ∀ᵐ s ∂volume,
      AEStronglyMeasurable (fun y : Vec3 =>
        uExt (parabolicHomeomorph.symm (y,s))) volume :=
    ae_of_ae_restrict_of_ae_restrict_compl pressureSplitTime
      hvelInside hvelOutside
  have hpInside : ∀ᵐ s ∂(volume.restrict pressureSplitTime),
      AEStronglyMeasurable (fun y : Vec3 =>
        p1Ext (parabolicHomeomorph.symm (y,s))) volume := by
    filter_upwards [hp₁, ae_restrict_mem measurableSet_Ioo] with s hslice hs
    have heq : (fun y : Vec3 => p1Ext (parabolicHomeomorph.symm (y,s))) =
        fun y => p₁ (y,s) := by
      funext y
      have hs' : s ∈ Ioo (-1 : ℝ) 0 := by
        simpa [pressureSplitTime] using hs
      simp only [p1Ext, parabolicHomeomorph_symm_apply,
        Set.indicator_of_mem hs']
    rw [heq]
    exact hslice.aestronglyMeasurable
  have hpOutside : ∀ᵐ s ∂(volume.restrict pressureSplitTimeᶜ),
      AEStronglyMeasurable (fun y : Vec3 =>
        p1Ext (parabolicHomeomorph.symm (y,s))) volume := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with s hs
    have hs' : s ∉ Ioo (-1 : ℝ) 0 := by
      simpa only [Set.mem_compl_iff, pressureSplitTime] using hs
    have heq : (fun y : Vec3 => p1Ext (parabolicHomeomorph.symm (y,s))) =
        fun _ => (0 : ℝ) := by
      funext y
      simp only [p1Ext, parabolicHomeomorph_symm_apply,
        Set.indicator_of_notMem hs']
    rw [heq]
    exact aestronglyMeasurable_const
  have hpSource : ∀ᵐ s ∂volume,
      AEStronglyMeasurable (fun y : Vec3 =>
        p1Ext (parabolicHomeomorph.symm (y,s))) volume :=
    ae_of_ae_restrict_of_ae_restrict_compl pressureSplitTime
      hpInside hpOutside
  have hvelSource' : ∀ᵐ s ∂(volume.restrict Set.univ),
      AEStronglyMeasurable (fun y : Vec3 =>
        uExt (parabolicHomeomorph.symm (y,s))) volume := by
    simpa only [Measure.restrict_univ] using hvelSource
  have hpSource' : ∀ᵐ s ∂(volume.restrict Set.univ),
      AEStronglyMeasurable (fun y : Vec3 =>
        p1Ext (parabolicHomeomorph.symm (y,s))) volume := by
    simpa only [Measure.restrict_univ] using hpSource
  have hJ : CKN.rescaledTime r t₀ Set.univ = Set.univ := by
    ext t
    simp [CKN.rescaledTime]
  have hvelPull := blowup_ae_time_pullback r t₀ hr Set.univ
    MeasurableSet.univ _ hvelSource'
  have hpPull := blowup_ae_time_pullback r t₀ hr Set.univ
    MeasurableSet.univ _ hpSource'
  have hvelPull' : ∀ᵐ t ∂volume,
      AEStronglyMeasurable (fun y : Vec3 => uExt
        (parabolicHomeomorph.symm (y, CKN.scalingTime r t₀ t))) volume := by
    simpa only [hJ, Measure.restrict_univ] using hvelPull
  have hpPull' : ∀ᵐ t ∂volume,
      AEStronglyMeasurable (fun y : Vec3 => p1Ext
        (parabolicHomeomorph.symm (y, CKN.scalingTime r t₀ t))) volume := by
    simpa only [hJ, Measure.restrict_univ] using hpPull
  filter_upwards [hvelPull', hpPull'] with t hvt hpt
  constructor
  · simpa only [uExt, parabolicRescaleVelocity, parabolicTranslate,
      parabolicScale, CKN.scalingTime, parabolicHomeomorph_symm_apply] using
      blowupVelocitySlice_mass_eq
        (fun y : Vec3 => uExt
          (parabolicHomeomorph.symm (y, CKN.scalingTime r t₀ t))) hvt x₀ r hr
  · simpa only [p1Ext, parabolicRescalePressure, parabolicTranslate,
      parabolicScale, CKN.scalingTime, parabolicHomeomorph_symm_apply] using
      blowupPressureSlice_mass_eq
        (fun y : Vec3 => p1Ext
          (parabolicHomeomorph.symm (y, CKN.scalingTime r t₀ t))) hpt x₀ r hr

/-- The mixed `L^(3/2)` supremum norm expression of the rescaled fixed
harmonic remainder tends to zero on every bounded measurable spatial region. -/
theorem pressureSplit_remainder_mixed_sup_norm_tendsto_zero
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict pressureSplitDomain))
    (hDu : AEStronglyMeasurable Du (volume.restrict pressureSplitDomain))
    (hpmeas : AEStronglyMeasurable p (volume.restrict pressureSplitDomain))
    (hL2 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ‖u (x,t)‖ₑ ^ (2 : ℝ)) (volume.restrict pressureSplitTime) < ⊤)
    (henergy : (∫⁻ z in pressureSplitDomain,
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict pressureSplitDomain))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in pressureSplitBall,
      ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
      (volume.restrict pressureSplitTime) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict pressureSplitTime), ∀ i : Fin 3,
      HasWeakGradientOn pressureSplitBall (fun x => u (x,t) i)
        (fun x => Du (x,t) i))
    (hdiv : ∀ χ : Vec3 × ℝ → ℝ,
      χ ∈ spaceTimeTestFunction (V := ℝ) pressureSplitBall pressureSplitTime →
      ∫ z in pressureSplitDomain,
        ∑ i : Fin 3, u z i * spatialPartial χ i z = 0)
    (hMomentum : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) pressureSplitBall pressureSplitTime →
      ∫ z in pressureSplitDomain,
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0)
    (x₀ : Vec3) (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (t₀ : ℝ) {Ω : Set Vec3} (hΩmeas : MeasurableSet Ω)
    (hΩbounded : Bornology.IsBounded Ω)
    (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0)) :
    let F := pressureSplitTensor u
    let hF := pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
    let p₁ := pressureSplitRieszPressure F hF
    let p₂ := pressureSplitRemainder p p₁
    Tendsto (fun k =>
      (∫⁻ t : ℝ,
        eLpNorm (fun x : Vec3 => parabolicRescalePressure x₀ t₀ (r k)
          (goodPointDomain.indicator p₂) (x,t)) ⊤
          (volume.restrict Ω) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ))
      atTop (nhds 0) := by
  dsimp only
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := pressureSplitTensor u
  let hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
  let p₁ : ParabolicPoint → ℝ := pressureSplitRieszPressure F hF
  let p₂ : ParabolicPoint → ℝ := pressureSplitRemainder p p₁
  obtain ⟨C, hC, δ, hδ, hscale⟩ := pressureSplit_remainder_mixed_scale_bound
    hu hDu hpmeas hL2 henergy hp hL3 hgrad hdiv hMomentum x₀ hx₀ t₀
    hΩmeas hΩbounded
  let μ : Measure (Vec3 × ℝ) :=
    (volume.restrict (CKN.euclideanBall 0 1)).prod
      (volume.restrict (Ioo (-1 : ℝ) 0))
  let A : ℝ≥0∞ :=
    eLpNorm (fun z : Vec3 × ℝ => p (z.1,z.2))
      (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ) +
      ENNReal.ofReal (pressureSplitVelocityLpBound u ^ 3)
  have hball : CKN.euclideanBall (0 : Vec3) 1 = pressureSplitBall := by
    rw [pressureSplitBall, CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
      (by norm_num : (0 : ℝ) < 1)]
  have hmeasure : μ = (volume : Measure (Vec3 × ℝ)).restrict
      pressureSplitProductDomain := by
    dsimp [μ]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
    simp only [pressureSplitProductDomain, pressureSplitTime, hball]
  have hpara : MeasurableSet pressureSplitDomain := by
    exact (isOpen_spaceTimeSet pressureSplitBall pressureSplitTime
      (isOpen_vec3Ball (0 : Vec3) 1) isOpen_Ioo).measurableSet
  have hpre : parabolicHomeomorph.symm ⁻¹' pressureSplitDomain =
      pressureSplitProductDomain := by
    ext z
    rfl
  have hmp : MeasurePreserving parabolicHomeomorph.symm μ
      (volume.restrict pressureSplitDomain) := by
    have h := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hpara
    rw [hpre] at h
    rw [hmeasure]
    exact h
  have hpProduct0 := hp.comp_measurePreserving hmp
  have hpeq : (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z)) =ᵐ[μ]
      (fun z => p (z.1,z.2)) := by
    filter_upwards [] with z
    simp only [parabolicHomeomorph_symm_apply]
  have hpProduct : MemLp (fun z : Vec3 × ℝ => p (z.1,z.2))
      (3 / 2 : ℝ≥0∞) μ := by
    have hcoeff : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [← hcoeff]
    exact (memLp_congr_ae hpeq).2 hpProduct0
  have hApow : eLpNorm (fun z : Vec3 × ℝ => p (z.1,z.2))
      (3 / 2 : ℝ≥0∞) μ ^ (3 / 2 : ℝ) < ⊤ := by
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      hpProduct.eLpNorm_lt_top.ne
  have hA : A < ⊤ := by
    dsimp [A]
    exact ENNReal.add_lt_top.mpr ⟨hApow,
      lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top⟩
  have hrOf : Tendsto (fun k => ENNReal.ofReal (r k)) atTop (nhds 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr0
    rw [ENNReal.ofReal_zero] at h
    have hfun : (fun k => ENNReal.ofReal (r k)) = ENNReal.ofReal ∘ r := by
      funext k
      rfl
    rw [hfun]
    exact h
  have hAne : A ≠ ⊤ := ne_of_lt hA
  have hCne : C ≠ ⊤ := ne_of_lt hC
  have hright : Tendsto (fun k => C * (ENNReal.ofReal (r k) * A))
      atTop (nhds 0) := by
    have hmulA : Tendsto (fun k => ENNReal.ofReal (r k) * A)
        atTop (nhds (0 * A)) :=
      ENNReal.Tendsto.mul_const hrOf (Or.inr hAne)
    have hmulC : Tendsto (fun k => C *
        (ENNReal.ofReal (r k) * A)) atTop (nhds (C * (0 * A))) :=
      ENNReal.Tendsto.const_mul hmulA (Or.inr hCne)
    simpa using hmulC
  have hsmall : ∀ᶠ k in atTop, r k < δ :=
    hr0.eventually (Iio_mem_nhds hδ)
  have hbound : ∀ᶠ k in atTop,
      (∫⁻ t : ℝ,
        eLpNorm (fun x : Vec3 => parabolicRescalePressure x₀ t₀ (r k)
          (goodPointDomain.indicator p₂) (x,t)) ⊤
          (volume.restrict Ω) ^ (3 / 2 : ℝ)) ≤
        C * (ENNReal.ofReal (r k) * A) := by
    filter_upwards [hsmall] with k hk
    exact hscale (r k) (hr k) hk
  have hmod : Tendsto (fun k =>
      ∫⁻ t : ℝ,
        eLpNorm (fun x : Vec3 => parabolicRescalePressure x₀ t₀ (r k)
          (goodPointDomain.indicator p₂) (x,t)) ⊤
          (volume.restrict Ω) ^ (3 / 2 : ℝ)) atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hright
      (Eventually.of_forall fun _ => bot_le) hbound
  simpa [Function.comp_def, p₂, p₁, F, hF] using
    (ENNReal.continuous_rpow_const (y := (2 / 3 : ℝ))).continuousAt.tendsto.comp hmod

end ESS

end
