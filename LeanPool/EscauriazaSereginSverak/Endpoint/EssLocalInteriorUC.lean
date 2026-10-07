/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalProofVorticity
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalFlatness
public import LeanPool.EscauriazaSereginSverak.Main.UniqueContinuation

/-!
# Unique continuation at a translated top time

The unique continuation theorem `thm:uc` is stated at the spatial origin and
initial time zero of a forward cylinder.  Reversing time about a top time
`t₀` and translating the spatial center to `x₀` transports it to past
cylinders `B_R(x₀) × (t₀ - T, t₀]`.  Vanishing on a small past cylinder at the
top point gives the infinite-order hypothesis by `lem:flat-from-vanishing`.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Unique continuation for the backward heat inequality on a past cylinder:
a bounded continuous field of class `W^{2,1}_2` satisfying
`|∂ₜω - Δω| ≤ C (|ω| + |∇ω|)` which vanishes on a small past cylinder at the top
point `(x₀, t₀)` vanishes on the whole top ball (`thm:uc`,
`lem:flat-from-vanishing`). -/
theorem essLocal_uniqueContinuation_past
    (R T C M r₀ : ℝ) (hR : 0 < R) (hT : 0 < T) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hr₀ : 0 < r₀) (hr₀R : r₀ ≤ R) (hr₀T : r₀ ^ 2 ≤ T)
    (x₀ : Vec3) (t₀ : ℝ)
    (ω : ParabolicPoint → Vec3) (Dω : ParabolicPoint → Fin 3 → Vec3)
    (D2ω : ParabolicPoint → Fin 3 → Fin 3 → Vec3) (Dtω : ParabolicPoint → Vec3)
    (hcont : ContinuousOn ω (spaceTimeSet (vec3Ball x₀ R) (Ioc (t₀ - T) t₀)))
    (hderiv : HasSpaceTimeWeakDerivs (vec3Ball x₀ R) (Ioo (t₀ - T) t₀)
      ω Dω D2ω Dtω)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball x₀ R) (Ioo (t₀ - T) t₀),
      ‖ω z‖ₑ ^ (2 : ℝ) + ‖Dω z‖ₑ ^ (2 : ℝ) +
        ‖D2ω z‖ₑ ^ (2 : ℝ) + ‖Dtω z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
        (spaceTimeSet (vec3Ball x₀ R) (Ioo (t₀ - T) t₀))),
      vec3EuclideanNorm (fun i => Dtω z i - ∑ j, D2ω z i j j) ≤
        C * (vec3EuclideanNorm (ω z) + Real.sqrt (spatialGradientSq ω Dω z)))
    (hbound : ∀ z ∈ spaceTimeSet (vec3Ball x₀ R) (Ioc (t₀ - T) t₀),
      vec3EuclideanNorm (ω z) ≤ M)
    (hzero : ∀ x s, x ∈ vec3Ball x₀ r₀ → s ∈ Ioo (t₀ - r₀ ^ 2) t₀ →
      ω (x, s) = 0) :
    ∀ x ∈ vec3Ball x₀ R, ω (x, t₀) = 0 := by
  let e : ParabolicPoint → ParabolicPoint := fun z =>
    essLocalSpatialTranslate x₀ (essLocalTimeTranslate t₀ (essLocalTimeReflection z))
  have hEcoord (z : ParabolicPoint) : e z = (x₀ + z.1, t₀ + -z.2) := by
    change essLocalSpatialTranslate x₀ (essLocalTimeTranslate t₀ (essLocalTimeReflection z)) = _
    rw [essLocalSpatialTranslate_apply, essLocalTimeTranslate_apply,
      essLocalTimeReflection_apply]
  let w : ParabolicPoint → Vec3 := fun z => ω (e z)
  let Dw : ParabolicPoint → Fin 3 → Vec3 := fun z i j => Dω (e z) i j
  let D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k => D2ω (e z) i j k
  let Dtw : ParabolicPoint → Vec3 := fun z i => -Dtω (e z) i
  have hBallOpen : IsOpen (vec3Ball x₀ R) := isOpen_vec3Ball x₀ R
  -- weak derivatives
  have h1 := essLocal_timeTranslate_weakDerivs t₀ hBallOpen isOpen_Ioo hderiv
  have hset1 : {s : ℝ | s + t₀ ∈ Ioo (t₀ - T) t₀} = Ioo (-T) 0 := by
    ext s
    simp only [mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨by linarith only [h₁], by linarith only [h₂]⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨by linarith only [h₁], by linarith only [h₂]⟩
  rw [hset1] at h1
  have h2 := essLocal_spatialTranslate_weakDerivs x₀ hBallOpen isOpen_Ioo h1
  have hset2 : {y : Vec3 | x₀ + y ∈ vec3Ball x₀ R} = vec3Ball 0 R := by
    ext y
    simp only [mem_ofPred_eq, mem_vec3Ball, sub_zero, add_sub_cancel_left]
  rw [hset2] at h2
  have hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 R) (Ioo (0 : ℝ) T) w Dw D2w Dtw :=
    essLocal_timeReflection_weakDerivs (isOpen_vec3Ball 0 R) h2
  -- measure preservation
  have hmp : MeasurePreserving e (volume : Measure ParabolicPoint)
      (volume : Measure ParabolicPoint) :=
    (essLocalSpatialTranslate_measurePreserving x₀).comp
      ((essLocalTimeTranslate_measurePreserving t₀).comp
        essLocalTimeReflection_measurePreserving)
  let eH : ParabolicPoint ≃ₜ ParabolicPoint :=
    (essLocalTimeReflection.trans (essLocalTimeTranslate t₀)).trans
      (essLocalSpatialTranslate x₀)
  have heH : (eH : ParabolicPoint → ParabolicPoint) = e := rfl
  have hemb : MeasurableEmbedding e := by
    rw [← heH]
    exact eH.measurableEmbedding
  have hmapsOpen : ∀ z ∈ spaceTimeSet (vec3Ball 0 R) (Ioo (0 : ℝ) T),
      e z ∈ spaceTimeSet (vec3Ball x₀ R) (Ioo (t₀ - T) t₀) := by
    intro z hz
    rw [hEcoord]
    refine ⟨?_, ?_, ?_⟩
    · change vec3EuclideanNorm (x₀ + z.1 - x₀) < R
      have hz1 : vec3EuclideanNorm (z.1 - 0) < R := hz.1
      simpa only [add_sub_cancel_left, sub_zero] using hz1
    · linarith only [hz.2.2]
    · linarith only [hz.2.1]
  have hmapsIco : ∀ z : ParabolicPoint, z ∈ vec3Ball (0 : Vec3) R ×ˢ Ico (0 : ℝ) T →
      e z ∈ spaceTimeSet (vec3Ball x₀ R) (Ioc (t₀ - T) t₀) := by
    intro z hz
    rw [hEcoord z]
    refine ⟨?_, ?_, ?_⟩
    · change vec3EuclideanNorm (x₀ + z.1 - x₀) < R
      have hz1 : vec3EuclideanNorm (z.1 - 0) < R := hz.1
      simpa only [add_sub_cancel_left, sub_zero] using hz1
    · linarith only [hz.2.2]
    · linarith only [hz.2.1]
  -- continuity
  have heCont : Continuous e :=
    (essLocalSpatialTranslate x₀).continuous.comp
      ((essLocalTimeTranslate t₀).continuous.comp essLocalTimeReflection.continuous)
  have hcontW : ContinuousOn w (vec3Ball (0 : Vec3) R ×ˢ Ico (0 : ℝ) T) :=
    hcont.comp heCont.continuousOn hmapsIco
  -- square integrability
  have hL2W : (∫⁻ z in spaceTimeSet (vec3Ball 0 R) (Ioo (0 : ℝ) T),
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    let F : ParabolicPoint → ℝ≥0∞ := fun z =>
      ‖ω z‖ₑ ^ (2 : ℝ) + ‖Dω z‖ₑ ^ (2 : ℝ) +
        ‖D2ω z‖ₑ ^ (2 : ℝ) + ‖Dtω z‖ₑ ^ (2 : ℝ)
    have hEq : (fun z => ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) = fun z => F (e z) := by
      funext z
      change ‖ω (e z)‖ₑ ^ (2 : ℝ) + ‖Dω (e z)‖ₑ ^ (2 : ℝ) +
          ‖D2ω (e z)‖ₑ ^ (2 : ℝ) + ‖-Dtω (e z)‖ₑ ^ (2 : ℝ) = F (e z)
      rw [enorm_neg]
    rw [hEq, hmp.setLIntegral_comp_emb hemb F]
    refine lt_of_le_of_lt (lintegral_mono_set ?_) hL2
    rintro y ⟨z, hz, rfl⟩
    exact hmapsOpen z hz
  -- the differential inequality
  have hineqW : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 R) (Ioo (0 : ℝ) T))),
      vec3EuclideanNorm (fun i => Dtw z i + ∑ j, D2w z i j j) ≤
        (C + 1) * (vec3EuclideanNorm (w z) +
          Real.sqrt (spatialGradientSq w Dw z)) := by
    have hSrc : MeasurableSet (spaceTimeSet (vec3Ball x₀ R) (Ioo (t₀ - T) t₀)) :=
      (isOpen_spaceTimeSet _ _ hBallOpen isOpen_Ioo).measurableSet
    have hTgt : MeasurableSet (spaceTimeSet (vec3Ball 0 R) (Ioo (0 : ℝ) T)) :=
      (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball 0 R) isOpen_Ioo).measurableSet
    have hglobal := hmp.quasiMeasurePreserving.ae ((ae_restrict_iff' hSrc).1 hineq)
    refine (ae_restrict_iff' hTgt).2 ?_
    filter_upwards [hglobal] with z hz hzin
    have hz' := hz (hmapsOpen z hzin)
    have hheat : (fun i => Dtw z i + ∑ j, D2w z i j j) =
        -(fun i => Dtω (e z) i - ∑ j, D2ω (e z) i j j) := by
      funext i
      simp only [Dtw, D2w, Pi.neg_apply]
      ring
    rw [hheat, vec3EuclideanNorm_neg]
    have hsumNonneg : 0 ≤ vec3EuclideanNorm (w z) +
        Real.sqrt (spatialGradientSq w Dw z) :=
      add_nonneg (vec3EuclideanNorm_nonneg _) (Real.sqrt_nonneg _)
    refine le_trans hz' ?_
    exact mul_le_mul_of_nonneg_right (by linarith only [hC]) hsumNonneg
  -- infinite-order vanishing at the top point
  have hvanish : ∀ k : ℕ, ∃ C' : ℝ, ∀ z ∈ spaceTimeSet (vec3Ball 0 R) (Ioo (0 : ℝ) T),
      vec3EuclideanNorm (w z) ≤ C' * (vec3EuclideanNorm z.1 + Real.sqrt z.2) ^ k := by
    have hflat := flat_from_vanishing R T r₀ M 0 w hr₀ hM hr₀R hr₀T
      (fun z hz => hbound (e z) (hmapsIco z hz))
      (by
        intro x s hx hs0 hs _
        change ω (x₀ + x, t₀ + -s) = 0
        apply hzero
        · change vec3EuclideanNorm (x₀ + x - x₀) < r₀
          have hx1 : vec3EuclideanNorm (x - 0) < r₀ := hx
          simpa only [add_sub_cancel_left, sub_zero] using hx1
        · constructor
          · change t₀ - r₀ ^ 2 < t₀ + -s
            linarith only [hs]
          · change t₀ + -s < t₀
            linarith only [hs0])
    intro k
    refine ⟨M * r₀⁻¹ ^ k, ?_⟩
    rintro ⟨x, s⟩ hz
    have h := hflat k x s hz
    simpa only [sub_zero] using h
  have hUC := ESS.Main.uniqueContinuation R T (C + 1) hR hT (by linarith only [hC])
    w Dw D2w Dtw hcontW hweak hL2W hineqW hvanish
  intro x hx
  have hx0 : x - x₀ ∈ vec3Ball (0 : Vec3) R := by
    change vec3EuclideanNorm (x - x₀ - 0) < R
    rw [sub_zero]
    exact hx
  have h := hUC (x - x₀) hx0
  change ω (x₀ + (x - x₀), t₀ + -0) = 0 at h
  simpa only [add_sub_cancel, neg_zero, add_zero] using h

end ESS
