/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffs
public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineWeak

/-!
# Affine coordinates on an arbitrary time interval

The shifted time interval in `lem:bu-small-time` is transported to the
initial interval by a positive parabolic dilation with a time translation.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The affine preimage of a half-space time slab has the expected
endpoints. -/
theorem buAffinePoint_preimage_interval
    (τ scale a b : ℝ) (hscale : 0 < scale) :
    buAffinePoint τ scale ⁻¹'
        spaceTimeSet {x : Vec3 | 0 < x 2}
          (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) =
      spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b) := by
  ext z
  have hs2 : 0 < scale ^ 2 := sq_pos_of_pos hscale
  constructor
  · rintro ⟨hx, ht⟩
    change 0 < scale * z.1 2 at hx
    change τ + scale ^ 2 * z.2 ∈
      Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b) at ht
    refine ⟨(mul_pos_iff_of_pos_left hscale).mp hx, ?_, ?_⟩
    · apply (mul_lt_mul_iff_of_pos_left hs2).mp
      linarith only [ht.1]
    · apply (mul_lt_mul_iff_of_pos_left hs2).mp
      linarith only [ht.2]
  · rintro ⟨hx, ht⟩
    change 0 < scale * z.1 2 ∧
      τ + scale ^ 2 * z.2 ∈
        Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)
    refine ⟨mul_pos hscale hx, ?_⟩
    exact ⟨by linarith only [mul_lt_mul_of_pos_left ht.1 hs2],
      by linarith only [mul_lt_mul_of_pos_left ht.2 hs2]⟩

/-- The affine image of a half-space time interval is its translated,
parabolically dilated interval. -/
theorem buAffineHomeomorph_image_interval
    (τ scale a b : ℝ) (hscale : 0 < scale) :
    buAffineHomeomorph τ scale hscale ''
        spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b) =
      spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) := by
  have hpre : (buAffineHomeomorph τ scale hscale) ⁻¹'
      spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) =
      spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b) := by
    rw [buAffineHomeomorph_eq]
    exact buAffinePoint_preimage_interval τ scale a b hscale
  rw [← hpre]
  exact (buAffineHomeomorph τ scale hscale).image_preimage _

/-- Smooth compactly supported tests pull back from the normalized
half-space interval to the source time slab. -/
theorem bu_affine_pullback_test_interval
    (τ scale a b : ℝ) (hscale : 0 < scale)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      {x : Vec3 | 0 < x 2} (Ioo a b)) :
    (ψ ∘ (buAffineHomeomorph τ scale hscale).symm) ∈
      spaceTimeTestFunction (V := ℝ)
        {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) := by
  rcases hψ with ⟨hψdiff, hψcompact, hψsupport⟩
  refine ⟨hψdiff.comp
      (buAffineHomeomorph_symm_contDiff τ scale hscale),
    hψcompact.comp_homeomorph (buAffineHomeomorph τ scale hscale).symm, ?_⟩
  rw [tsupport_comp_eq_preimage ψ (buAffineHomeomorph τ scale hscale).symm]
  rw [← (buAffineHomeomorph τ scale hscale).image_eq_preimage_symm]
  exact (image_mono hψsupport).trans_eq
    (buAffineHomeomorph_image_interval τ scale a b hscale)

/-- Integration over any normalized half-space interval transforms by the
parabolic Jacobian of the affine map. -/
theorem bu_affine_integral_comp_interval
    (τ scale a b : ℝ) (hscale : 0 < scale)
    (F : ParabolicPoint → ℝ)
    (hFm : AEStronglyMeasurable F
      (volume.restrict
        (spaceTimeSet {x : Vec3 | 0 < x 2}
          (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))))) :
    (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b),
      F (buAffinePoint τ scale z)) =
      scale⁻¹ ^ 5 *
        ∫ z in spaceTimeSet {x : Vec3 | 0 < x 2}
          (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)),
          F z := by
  have hΩ : MeasurableSet {x : Vec3 | 0 < x 2} :=
    (isOpen_lt continuous_const (continuous_apply 2)).measurableSet
  have h := CKN.integral_comp_scaling_test scale hscale
    ((0 : Vec3), τ) (Ω := {x : Vec3 | 0 < x 2})
    (I := Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))
    hΩ measurableSet_Ioo hFm
  rw [rescaledSpaceTimeSet_eq_preimage scale
      (show ParabolicPoint from ((0 : Vec3), τ))
      {x : Vec3 | 0 < x 2}
      (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)),
    ← buAffinePoint_eq_scalingParabolic,
    buAffinePoint_preimage_interval τ scale a b hscale] at h
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  simpa only [smul_eq_mul] using h

/-- Local integrability transfers through affine coordinates between any
two corresponding positive half-space time intervals. -/
theorem bu_affine_locallyIntegrableOn_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ scale a b : ℝ) (hscale : 0 < scale)
    (f : ParabolicPoint → E)
    (hf : LocallyIntegrableOn f
      (spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))) volume) :
    LocallyIntegrableOn (f ∘ buAffinePoint τ scale)
      (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b)) volume := by
  let e := buAffineParabolicHomeomorph τ scale hscale
  let Q := spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b)
  let S := spaceTimeSet {x : Vec3 | 0 < x 2}
    (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))
  have hQopen : IsOpen Q :=
    CKN.Foundation.Parabolic.isOpen_spaceTimeSet _ _
      (isOpen_lt continuous_const (continuous_apply 2)) isOpen_Ioo
  have : LocallyCompactSpace ParabolicPoint :=
    parabolicHomeomorph.isOpenEmbedding.locallyCompactSpace
  apply (locallyIntegrableOn_iff hQopen.isLocallyClosed).2
  intro K hKsub hKcompact
  have himage : e '' K ⊆ S := by
    rintro z ⟨q, hq, rfl⟩
    rw [buAffineParabolicHomeomorph_eq]
    have hq' : q ∈ buAffinePoint τ scale ⁻¹' S := by
      rw [buAffinePoint_preimage_interval τ scale a b hscale]
      exact hKsub hq
    exact hq'
  have hsource : IntegrableOn f (e '' K) volume :=
    hf.integrableOn_compact_subset himage (hKcompact.image e.continuous)
  have hcoef : ENNReal.ofReal (scale⁻¹ ^ 5) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsmul : IntegrableOn f (e '' K)
      (ENNReal.ofReal (scale⁻¹ ^ 5) • volume) := by
    rw [IntegrableOn, Measure.restrict_smul]
    exact hsource.smul_measure hcoef
  have hmap : Measure.map e volume =
      ENNReal.ofReal (scale⁻¹ ^ 5) • (volume : Measure ParabolicPoint) := by
    rw [buAffineParabolicHomeomorph_eq, buAffinePoint_eq_scalingParabolic]
    exact CKN.map_scalingParabolic scale hscale ((0 : Vec3), τ)
  have htrans : IntegrableOn f (e '' K) (Measure.map e volume) := by
    rw [hmap]
    exact hsmul
  have hcomp := (integrableOn_map_equiv e.toMeasurableEquiv).1 htrans
  have hpre : e ⁻¹' (e '' K) = K := e.preimage_image K
  rw [Homeomorph.toMeasurableEquiv_coe, hpre] at hcomp
  simpa only [e, Homeomorph.toMeasurableEquiv_coe,
    buAffineParabolicHomeomorph_eq] using hcomp

end ESS
