/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingQuantities

/-!
# Changes of variables under parabolic scaling

The parabolic scaling z ↦ (x₀ + R x, t₀ + R² t) is a measurable equivalence
of space-time whose push-forward of Lebesgue measure is R⁻⁵ times Lebesgue
measure. This file records the resulting change-of-variables identities for
lower integrals, almost-everywhere statements, measurability and Lᵖ
membership, with no measurability hypothesis on lower integrands. They are the
bookkeeping behind the rescaling step of `lem:pv-positive-bound`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The parabolic scaling map as a measurable equivalence. -/
@[expose] def pvScalingEquiv (R : ℝ) (hR : 0 < R) (z₀ : ParabolicPoint) :
    ParabolicPoint ≃ᵐ ParabolicPoint where
  toFun := CKN.scalingParabolic R z₀
  invFun := fun z => ((R⁻¹ • (z.1 - z₀.1), (R ^ 2)⁻¹ * (z.2 - z₀.2)) : Vec3 × ℝ)
  left_inv := by
    intro z
    have hR0 : R ≠ 0 := hR.ne'
    have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR0
    change ((R⁻¹ • (z₀.1 + R • z.1 - z₀.1), (R ^ 2)⁻¹ * (z₀.2 + R ^ 2 * z.2 - z₀.2))
      : Vec3 × ℝ) = z
    refine Prod.ext ?_ ?_
    · change R⁻¹ • (z₀.1 + R • z.1 - z₀.1) = z.1
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hR0, one_smul]
    · change (R ^ 2)⁻¹ * (z₀.2 + R ^ 2 * z.2 - z₀.2) = z.2
      rw [add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ hR2, one_mul]
  right_inv := by
    intro z
    have hR0 : R ≠ 0 := hR.ne'
    have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR0
    change ((z₀.1 + R • (R⁻¹ • (z.1 - z₀.1)), z₀.2 + R ^ 2 * ((R ^ 2)⁻¹ * (z.2 - z₀.2)))
      : Vec3 × ℝ) = z
    refine Prod.ext ?_ ?_
    · change z₀.1 + R • (R⁻¹ • (z.1 - z₀.1)) = z.1
      rw [smul_smul, mul_inv_cancel₀ hR0, one_smul, add_sub_cancel]
    · change z₀.2 + R ^ 2 * ((R ^ 2)⁻¹ * (z.2 - z₀.2)) = z.2
      rw [← mul_assoc, mul_inv_cancel₀ hR2, one_mul, add_sub_cancel]
  measurable_toFun := by
    change Measurable (fun z : Vec3 × ℝ => ((z₀.1 + R • z.1, z₀.2 + R ^ 2 * z.2) : Vec3 × ℝ))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : Vec3 × ℝ =>
      ((R⁻¹ • (z.1 - z₀.1), (R ^ 2)⁻¹ * (z.2 - z₀.2)) : Vec3 × ℝ))
    fun_prop

private theorem pvScalingEquiv_coe (R : ℝ) (hR : 0 < R) (z₀ : ParabolicPoint) :
    ⇑(pvScalingEquiv R hR z₀) = CKN.scalingParabolic R z₀ := rfl

/-- The spatial scaling map as a measurable equivalence. -/
@[expose] def pvSpaceScalingEquiv (R : ℝ) (hR : 0 < R) (x₀ : Vec3) : Vec3 ≃ᵐ Vec3 where
  toFun := CKN.scalingSpace R x₀
  invFun := fun y => R⁻¹ • (y - x₀)
  left_inv := by
    intro x
    change R⁻¹ • (x₀ + R • x - x₀) = x
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  right_inv := by
    intro y
    change x₀ + R • (R⁻¹ • (y - x₀)) = y
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
  measurable_toFun := by
    change Measurable (fun x : Vec3 => x₀ + R • x)
    fun_prop
  measurable_invFun := by
    change Measurable (fun y : Vec3 => R⁻¹ • (y - x₀))
    fun_prop

private theorem pvSpaceScalingEquiv_coe (R : ℝ) (hR : 0 < R) (x₀ : Vec3) :
    ⇑(pvSpaceScalingEquiv R hR x₀) = CKN.scalingSpace R x₀ := rfl

private theorem pvScaling_map_restrict (R : ℝ) (hR : 0 < R) (z₀ : ParabolicPoint)
    (S : Set ParabolicPoint) :
    Measure.map (CKN.scalingParabolic R z₀)
        (volume.restrict (CKN.scalingParabolic R z₀ ⁻¹' S)) =
      ENNReal.ofReal (R⁻¹ ^ 5) • volume.restrict S := by
  rw [← pvScalingEquiv_coe R hR z₀, ← MeasurableEquiv.restrict_map,
    pvScalingEquiv_coe R hR z₀, CKN.map_scalingParabolic R hR z₀,
    Measure.restrict_smul]

/-- Change of variables for lower integrals under parabolic scaling, for an
arbitrary integrand and an arbitrary target set. -/
theorem pv_lintegral_scalingParabolic (R : ℝ) (hR : 0 < R) (z₀ : ParabolicPoint)
    (S : Set ParabolicPoint) (F : ParabolicPoint → ℝ≥0∞) :
    ∫⁻ z in CKN.scalingParabolic R z₀ ⁻¹' S, F (CKN.scalingParabolic R z₀ z) =
      ENNReal.ofReal (R⁻¹ ^ 5) * ∫⁻ z in S, F z := by
  have h := lintegral_map_equiv F (pvScalingEquiv R hR z₀)
    (μ := volume.restrict (CKN.scalingParabolic R z₀ ⁻¹' S))
  rw [pvScalingEquiv_coe R hR z₀, pvScaling_map_restrict R hR z₀ S,
    lintegral_smul_measure] at h
  rw [← h]
  rfl

/-- Change of variables for lower integrals under spatial scaling. -/
theorem pv_lintegral_scalingSpace (R : ℝ) (hR : 0 < R) (x₀ : Vec3)
    (A : Set Vec3) (F : Vec3 → ℝ≥0∞) :
    ∫⁻ x in CKN.scalingSpace R x₀ ⁻¹' A, F (CKN.scalingSpace R x₀ x) =
      ENNReal.ofReal (R⁻¹ ^ 3) * ∫⁻ x in A, F x := by
  have hmap : Measure.map (CKN.scalingSpace R x₀)
      (volume.restrict (CKN.scalingSpace R x₀ ⁻¹' A)) =
      ENNReal.ofReal (R⁻¹ ^ 3) • volume.restrict A := by
    rw [← pvSpaceScalingEquiv_coe R hR x₀, ← MeasurableEquiv.restrict_map,
      pvSpaceScalingEquiv_coe R hR x₀, CKN.map_scalingSpace R hR x₀,
      Measure.restrict_smul]
  have h := lintegral_map_equiv F (pvSpaceScalingEquiv R hR x₀)
    (μ := volume.restrict (CKN.scalingSpace R x₀ ⁻¹' A))
  rw [pvSpaceScalingEquiv_coe R hR x₀, hmap, lintegral_smul_measure] at h
  rw [← h]
  rfl

/-- Almost-everywhere statements transfer through parabolic scaling. -/
theorem pv_ae_scalingParabolic_iff (R : ℝ) (hR : 0 < R) (z₀ : ParabolicPoint)
    (S : Set ParabolicPoint) (P : ParabolicPoint → Prop) :
    (∀ᵐ z ∂volume.restrict (CKN.scalingParabolic R z₀ ⁻¹' S),
        P (CKN.scalingParabolic R z₀ z)) ↔
      ∀ᵐ z ∂volume.restrict S, P z := by
  have hc : ENNReal.ofReal (R⁻¹ ^ 5) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have h := (pvScalingEquiv R hR z₀).measurableEmbedding.ae_map_iff
    (μ := volume.restrict (CKN.scalingParabolic R z₀ ⁻¹' S)) (p := P)
  rw [pvScalingEquiv_coe R hR z₀, pvScaling_map_restrict R hR z₀ S,
    Measure.ae_ennreal_smul_measure_eq hc] at h
  exact h.symm

/-- Almost-everywhere strong measurability transfers through parabolic
scaling. -/
theorem pv_aestronglyMeasurable_comp_scalingParabolic {E : Type} [TopologicalSpace E]
    (R : ℝ) (hR : 0 < R) (z₀ : ParabolicPoint) {S : Set ParabolicPoint}
    {f : ParabolicPoint → E} (hf : AEStronglyMeasurable f (volume.restrict S)) :
    AEStronglyMeasurable (f ∘ CKN.scalingParabolic R z₀)
      (volume.restrict (CKN.scalingParabolic R z₀ ⁻¹' S)) := by
  have hs := hf.smul_measure (ENNReal.ofReal (R⁻¹ ^ 5))
  rw [← pvScaling_map_restrict R hR z₀ S] at hs
  exact hs.comp_measurable (pvScalingEquiv R hR z₀).measurable

/-- Lᵖ membership transfers through parabolic scaling. -/
theorem pv_memLp_comp_scalingParabolic {E : Type} [NormedAddCommGroup E]
    (R : ℝ) (hR : 0 < R) (z₀ : ParabolicPoint) {S : Set ParabolicPoint}
    {f : ParabolicPoint → E} {q : ℝ≥0∞} (hf : MemLp f q (volume.restrict S)) :
    MemLp (f ∘ CKN.scalingParabolic R z₀) q
      (volume.restrict (CKN.scalingParabolic R z₀ ⁻¹' S)) := by
  have hs := hf.smul_measure (c := ENNReal.ofReal (R⁻¹ ^ 5)) ENNReal.ofReal_ne_top
  rw [← pvScaling_map_restrict R hR z₀ S] at hs
  exact hs.comp_of_map (pvScalingEquiv R hR z₀).measurable.aemeasurable

end ESS
