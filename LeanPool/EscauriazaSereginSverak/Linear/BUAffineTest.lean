/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUAffine
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Smooth tests in affine parabolic coordinates

The pullback of a compactly supported smooth test remains an admissible test
on the image time slab in `lem:bu-iterate`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

/-- The affine coordinate map as a homeomorphism of the ordinary product
space. -/
@[expose] def buAffineHomeomorph (τ scale : ℝ) (hscale : 0 < scale) :
    (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) :=
  Homeomorph.prodCongr
    (Homeomorph.smulOfNeZero scale hscale.ne')
    ((Homeomorph.smulOfNeZero (scale ^ 2)
      (sq_pos_of_pos hscale).ne').trans (Homeomorph.addLeft τ))

/-- The affine homeomorphism evaluates to the parabolic coordinate map. -/
theorem buAffineHomeomorph_eq (τ scale : ℝ) (hscale : 0 < scale) :
    ⇑(buAffineHomeomorph τ scale hscale) = buAffinePoint τ scale := by
  funext z
  change (scale • z.1, τ + scale ^ 2 * z.2) =
    (scale • z.1, τ + scale ^ 2 * z.2)
  rfl

/-- The inverse affine map has the expected coordinate formula. -/
theorem buAffineHomeomorph_symm_eq (τ scale : ℝ) (hscale : 0 < scale) :
    ⇑(buAffineHomeomorph τ scale hscale).symm =
      (fun z : Vec3 × ℝ =>
        (scale⁻¹ • z.1, (scale ^ 2)⁻¹ * (z.2 - τ))) := by
  ext z
  all_goals simp [buAffineHomeomorph, Homeomorph.trans, Homeomorph.prodCongr,
    Homeomorph.smulOfNeZero, Homeomorph.addLeft,
    Equiv.addLeft, Units.smul_def]
  all_goals ring

/-- The inverse affine map is smooth on the ordinary product space. -/
theorem buAffineHomeomorph_symm_contDiff
    (τ scale : ℝ) (hscale : 0 < scale) :
    ContDiff ℝ (⊤ : ℕ∞) (buAffineHomeomorph τ scale hscale).symm := by
  rw [buAffineHomeomorph_symm_eq τ scale hscale]
  fun_prop

/-- The affine image of the unit half-space cylinder is the corresponding
time slab. -/
theorem buAffineHomeomorph_image_halfCylinder
    (τ scale : ℝ) (hscale : 0 < scale) :
    buAffineHomeomorph τ scale hscale ''
        spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) =
      spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)) := by
  have hpre : (buAffineHomeomorph τ scale hscale) ⁻¹'
        spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)) =
      spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) := by
    rw [buAffineHomeomorph_eq]
    exact buAffinePoint_preimage_halfSlab τ scale hscale
  rw [← hpre]
  exact (buAffineHomeomorph τ scale hscale).image_preimage _

/-- Pulling back a smooth compactly supported test by the inverse affine map
gives an admissible test on the image slab. -/
theorem bu_affine_pullback_test
    (τ scale : ℝ) (hscale : 0 < scale)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      {x : Vec3 | 0 < x 2} (Ioo 0 1)) :
    (ψ ∘ (buAffineHomeomorph τ scale hscale).symm) ∈
      spaceTimeTestFunction (V := ℝ)
        {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)) := by
  rcases hψ with ⟨hψdiff, hψcompact, hψsupport⟩
  refine ⟨hψdiff.comp
      (buAffineHomeomorph_symm_contDiff τ scale hscale),
    hψcompact.comp_homeomorph (buAffineHomeomorph τ scale hscale).symm, ?_⟩
  rw [tsupport_comp_eq_preimage ψ (buAffineHomeomorph τ scale hscale).symm]
  rw [← (buAffineHomeomorph τ scale hscale).image_eq_preimage_symm]
  exact (image_mono hψsupport).trans_eq
    (buAffineHomeomorph_image_halfCylinder τ scale hscale)

/-- Integration on the normalized half-space cylinder transforms by the
parabolic Jacobian of the affine map. -/
theorem bu_affine_integral_comp
    (τ scale : ℝ) (hscale : 0 < scale)
    (F : ParabolicPoint → ℝ)
    (hFm : AEStronglyMeasurable F
      (volume.restrict
        (spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2))))) :
    (∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      F (buAffinePoint τ scale z)) =
      scale⁻¹ ^ 5 *
        ∫ z in spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)),
          F z := by
  have hΩ : MeasurableSet {x : Vec3 | 0 < x 2} :=
    (isOpen_lt continuous_const (continuous_apply 2)).measurableSet
  have h := CKN.integral_comp_scaling_test scale hscale
    ((0 : Vec3), τ) (Ω := {x : Vec3 | 0 < x 2})
    (I := Ioo τ (τ + scale ^ 2)) hΩ measurableSet_Ioo hFm
  rw [rescaledSpaceTimeSet_eq_preimage scale
      (show ParabolicPoint from ((0 : Vec3), τ))
      {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)),
    ← buAffinePoint_eq_scalingParabolic,
    buAffinePoint_preimage_halfSlab τ scale hscale] at h
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  simpa only [smul_eq_mul] using h

end ESS
