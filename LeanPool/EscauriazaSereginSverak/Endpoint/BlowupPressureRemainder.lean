/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureDecay

/-!
# Blowup Pressure Remainder

Pressure bounds and convergence estimates for the rescaled sequence.
-/

public section

open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- The interior harmonic supremum extended by zero outside the source time
interval. -/
@[expose] def blowupHarmonicSupExtended (p₂ : ParabolicPoint → ℝ) : ℝ → ℝ≥0∞ :=
  (Ioo (-1 : ℝ) 0).indicator
    (fun t => eLpNorm (fun x : Vec3 => p₂ (x,t)) ⊤
      (volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))))

/-- On the inner spatial ball, the zero-extended pressure is almost
everywhere bounded by its harmonic slice supremum. -/
theorem blowupPressureExtension_ae_sup_bound
    (p₂ : ParabolicPoint → ℝ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0)))) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      ∀ᵐ x ∂(volume.restrict (CKN.euclideanBall 0 (3 / 4 : ℝ))),
        ENNReal.ofReal |goodPointDomain.indicator p₂ (x,t)| ≤
          blowupHarmonicSupExtended p₂ t := by
  let J := Ioo (-1 : ℝ) 0
  let B := CKN.euclideanBall (0 : Vec3) (3 / 4 : ℝ)
  have hB : B ⊆ CKN.euclideanBall 0 1 := by
    intro x hx
    have hx' := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by norm_num : (0 : ℝ) < 3/4)).mp hx
    exact (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by norm_num : (0 : ℝ) < 1)).mpr
        (lt_trans hx' (by norm_num))
  have hJ := pressureSlice_memLp_ae (J := J) p₂ hp₂
  have hin : ∀ᵐ t ∂(volume.restrict J),
      ∀ᵐ x ∂(volume.restrict B),
        ENNReal.ofReal |goodPointDomain.indicator p₂ (x,t)| ≤
          blowupHarmonicSupExtended p₂ t := by
    filter_upwards [hJ, ae_restrict_mem measurableSet_Ioo] with t ht htJ
    have hmemB : MemLp (fun x : Vec3 => p₂ (x,t)) (3 / 2 : ℝ≥0∞)
        (volume.restrict B) :=
      ht.mono_measure (Measure.restrict_mono hB (le_refl volume))
    have hsup := ae_le_eLpNormEssSup
      (f := fun x : Vec3 => p₂ (x,t)) (μ := volume.restrict B)
    filter_upwards [hsup, ae_restrict_mem (by
      simpa [B, CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
        (by norm_num : (0 : ℝ) < 3/4)] using
          (vec3Ball_measurable (0 : Vec3) (3/4 : ℝ)))] with x hx hxB
    have hxD : ((x,t) : ParabolicPoint) ∈ goodPointDomain := by
      refine ⟨?_, htJ⟩
      rw [← CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
        (by norm_num : (0 : ℝ) < 1)]
      exact hB hxB
    have hEq : goodPointDomain.indicator p₂ ((x,t) : ParabolicPoint) = p₂ (x,t) :=
      Set.indicator_of_mem hxD _
    simp only [hEq]
    have hSupEq : eLpNorm (fun y : Vec3 => p₂ (y,t)) ⊤
        (volume.restrict B) = eLpNormEssSup (fun y : Vec3 => p₂ (y,t))
          (volume.restrict B) := eLpNorm_exponent_top hmemB.aestronglyMeasurable
    have hBound : ENNReal.ofReal |p₂ (x,t)| ≤ eLpNorm
        (fun y : Vec3 => p₂ (y,t)) ⊤ (volume.restrict B) := by
      rw [hSupEq]
      simpa only [Real.enorm_eq_ofReal_abs] using hx
    change ENNReal.ofReal |p₂ (x,t)| ≤
      (J.indicator (fun s => eLpNorm (fun y : Vec3 => p₂ (y,s)) ⊤
        (volume.restrict B))) t
    rw [Set.indicator_of_mem htJ]
    exact hBound
  have hout : ∀ᵐ t ∂(volume.restrict Jᶜ),
      ∀ᵐ x ∂(volume.restrict B),
        ENNReal.ofReal |goodPointDomain.indicator p₂ (x,t)| ≤
          blowupHarmonicSupExtended p₂ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with t ht
    have htJ : t ∉ J := ht
    filter_upwards [] with x
    have hxD : ((x,t) : ParabolicPoint) ∉ goodPointDomain := by
      intro hz
      exact htJ hz.2
    have hEq : goodPointDomain.indicator p₂ ((x,t) : ParabolicPoint) = 0 :=
      Set.indicator_of_notMem hxD _
    simp only [hEq, abs_zero, ENNReal.ofReal_zero]
    change (0 : ℝ≥0∞) ≤
      (J.indicator (fun s => eLpNorm (fun y : Vec3 => p₂ (y,s)) ⊤
        (volume.restrict B))) t
    rw [Set.indicator_of_notMem htJ]
  exact ae_of_ae_restrict_of_ae_restrict_compl J hin hout

/-- The zero-extended harmonic supremum is time integrable whenever the
pressure remainder has harmonic slices and finite local `L^(3/2)` mass. -/
theorem blowupHarmonicSupExtended_integrable
    (p₂ : ParabolicPoint → ℝ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hharm : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p₂ (x,t))) :
    (∫⁻ t, blowupHarmonicSupExtended p₂ t ^ (3 / 2 : ℝ)) < ⊤ := by
  exact blowupHarmonicPressure_global_sup_integrable p₂ hp₂ hharm

/-- Zero extension of a local `L^(3/2)` pressure is strongly measurable on
all of space-time. -/
theorem blowupPressureExtension_aestronglyMeasurable
    (p₂ : ParabolicPoint → ℝ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0)))) :
    AEStronglyMeasurable (goodPointDomain.indicator p₂)
      (volume : Measure ParabolicPoint) := by
  have hpD : MemLp p₂ (3 / 2 : ℝ≥0∞)
      (volume.restrict goodPointDomain) := by
    rw [goodPointDomain]
    rw [← CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
      (by norm_num : (0 : ℝ) < 1)]
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    change MemLp (fun z : Vec3 × ℝ => p₂ (z.1,z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.prod volume).restrict
        (CKN.euclideanBall 0 1 ×ˢ Ioo (-1 : ℝ) 0))
    rw [← Measure.prod_restrict]
    exact hp₂
  have hDmeas : MeasurableSet goodPointDomain :=
    (vec3Ball_measurable 0 1).prod measurableSet_Ioo
  exact (aestronglyMeasurable_indicator_iff hDmeas).mpr
    hpD.aestronglyMeasurable

/-- The fixed harmonic remainder vanishes under parabolic blow-up on every
fixed past cylinder once its slices are harmonic and locally integrable. -/
theorem blowupHarmonicPressure_extension_mass_tendsto_zero
    (p₂ : ParabolicPoint → ℝ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hharm : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p₂ (x,t)))
    (x₀ : Vec3) (t₀ S : ℝ) (hS : 0 < S) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0)) :
    Tendsto (fun k =>
      ∫⁻ z in parabolicCylinder 0 0 S,
        ENNReal.ofReal |parabolicRescalePressure x₀ t₀ (r k)
          (goodPointDomain.indicator p₂) z| ^ (3 / 2 : ℝ))
      atTop (nhds 0) := by
  have hH := blowupHarmonicSupExtended_integrable p₂ hp₂ hharm
  have hF := blowupPressureExtension_aestronglyMeasurable p₂ hp₂
  have hB := blowupPressureExtension_ae_sup_bound p₂ hp₂
  have hball := blowupSpatialBall_eventually_subset_inner x₀ S r hx₀ hr0
  apply blowupHarmonicRemainder_mass_tendsto_zero
    (goodPointDomain.indicator p₂) (blowupHarmonicSupExtended p₂)
    x₀ t₀ S hS r hr hr0 hH hball
  · exact Eventually.of_forall fun k => hF.restrict
  · exact Eventually.of_forall fun k => ae_restrict_of_ae hB

/-- The fixed harmonic pressure remainder converges strongly to zero in
`L^(3/2)` on each fixed past cylinder. -/
theorem blowupHarmonicPressure_extension_eLpNorm_tendsto_zero
    (p₂ : ParabolicPoint → ℝ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hharm : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p₂ (x,t)))
    (x₀ : Vec3) (t₀ S : ℝ) (hS : 0 < S) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0)) :
    Tendsto (fun k =>
      eLpNorm (parabolicRescalePressure x₀ t₀ (r k)
          (goodPointDomain.indicator p₂))
        (3 / 2 : ℝ≥0∞)
        (volume.restrict (parabolicCylinder 0 0 S)))
      atTop (nhds 0) := by
  let f := goodPointDomain.indicator p₂
  have hfm := blowupPressureExtension_aestronglyMeasurable p₂ hp₂
  have hmass := blowupHarmonicPressure_extension_mass_tendsto_zero
    p₂ hp₂ hharm x₀ t₀ S hS r hx₀ hr hr0
  have heq (k : ℕ) :
      eLpNorm (parabolicRescalePressure x₀ t₀ (r k) f)
        (3 / 2 : ℝ≥0∞)
        (volume.restrict (parabolicCylinder 0 0 S)) =
      (∫⁻ z in parabolicCylinder 0 0 S,
        ENNReal.ofReal |parabolicRescalePressure x₀ t₀ (r k) f z| ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
    have hsm : AEStronglyMeasurable
        (parabolicRescalePressure x₀ t₀ (r k) f)
        (volume.restrict (parabolicCylinder 0 0 S)) :=
      (blowupRescaledPressure_aestronglyMeasurable f hfm
        x₀ t₀ (r k) (hr k)).restrict
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
      (by finiteness : (3 / 2 : ℝ≥0∞) ≠ ⊤) hsm]
    norm_num
    simp only [Real.enorm_eq_ofReal_abs]
  have hpow : Tendsto (fun k =>
      (∫⁻ z in parabolicCylinder 0 0 S,
        ENNReal.ofReal |parabolicRescalePressure x₀ t₀ (r k) f z| ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) atTop (nhds 0) := by
    simpa [f, Function.comp_def] using
      (ENNReal.continuous_rpow_const (y := (2 / 3 : ℝ))).continuousAt.tendsto.comp hmass
  have hfun : (fun k =>
      eLpNorm (parabolicRescalePressure x₀ t₀ (r k) f)
        (3 / 2 : ℝ≥0∞)
        (volume.restrict (parabolicCylinder 0 0 S))) =
      (fun k => (∫⁻ z in parabolicCylinder 0 0 S,
        ENNReal.ofReal |parabolicRescalePressure x₀ t₀ (r k) f z| ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) := by
    funext k
    exact heq k
  change Tendsto (fun k =>
      eLpNorm (parabolicRescalePressure x₀ t₀ (r k) f)
        (3 / 2 : ℝ≥0∞)
        (volume.restrict (parabolicCylinder 0 0 S))) atTop (nhds 0)
  rw [hfun]
  exact hpow

/-- Harmonic pressure remainder convergence holds on any measurable region
contained in a fixed past cylinder. -/
theorem blowupHarmonicPressure_extension_eLpNorm_tendsto_zero_on
    (p₂ : ParabolicPoint → ℝ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hharm : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p₂ (x,t)))
    (x₀ : Vec3) (t₀ S : ℝ) (hS : 0 < S) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (C : Set ParabolicPoint)
    (hC : C ⊆ parabolicCylinder 0 0 S) :
    Tendsto (fun k =>
      eLpNorm (parabolicRescalePressure x₀ t₀ (r k)
          (goodPointDomain.indicator p₂))
        (3 / 2 : ℝ≥0∞) (volume.restrict C)) atTop (nhds 0) := by
  have hlarge := blowupHarmonicPressure_extension_eLpNorm_tendsto_zero
    p₂ hp₂ hharm x₀ t₀ S hS r hx₀ hr hr0
  have hle : ∀ k,
      eLpNorm (parabolicRescalePressure x₀ t₀ (r k)
          (goodPointDomain.indicator p₂))
        (3 / 2 : ℝ≥0∞) (volume.restrict C) ≤
      eLpNorm (parabolicRescalePressure x₀ t₀ (r k)
          (goodPointDomain.indicator p₂))
        (3 / 2 : ℝ≥0∞)
        (volume.restrict (parabolicCylinder 0 0 S)) := by
    intro k
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hC (le_refl volume))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hlarge
    (Eventually.of_forall fun k => bot_le)
    (Eventually.of_forall hle)

/-- The harmonic pressure remainder converges strongly on every bounded
open past cylinder. -/
theorem blowupHarmonicPressure_eLpNorm_tendsto_zero_pastBox
    (p₂ : ParabolicPoint → ℝ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p₂ (z.1, z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hharm : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p₂ (x,t)))
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0) :
    Tendsto (fun k =>
      eLpNorm (parabolicRescalePressure x₀ t₀ (r k)
          (goodPointDomain.indicator p₂))
        (3 / 2 : ℝ≥0∞)
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)))
      atTop (nhds 0) := by
  obtain ⟨S, hS, hC⟩ := blowupPastBox_subset_pastCylinder R a hR ha
  exact blowupHarmonicPressure_extension_eLpNorm_tendsto_zero_on
    p₂ hp₂ hharm x₀ t₀ S hS r hx₀ hr hr0
    (vec3Ball 0 R ×ˢ Ioo a 0) hC

/-- The remainder of the fixed pressure split vanishes strongly on bounded
past cylinders after rescaling. -/
theorem blowupPressureRemainder_eLpNorm_tendsto_zero_pastBox
    (p p₁ : ParabolicPoint → ℝ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p (z.1, z.2) - p₁ (z.1, z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hharm : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p (x,t) - p₁ (x,t)))
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0) :
    Tendsto (fun k =>
      eLpNorm (blowupPressureRemainder x₀ t₀ (r k) p p₁)
        (3 / 2 : ℝ≥0∞)
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)))
      atTop (nhds 0) := by
  simpa only [blowupPressureRemainder] using
    blowupHarmonicPressure_eLpNorm_tendsto_zero_pastBox
      (fun z : ParabolicPoint => p z - p₁ z) hp₂ hharm
      x₀ t₀ r hx₀ hr hr0 R a hR ha

end ESS
