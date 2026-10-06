/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupGradientSource

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace ESS

/-- The fixed pressure split makes the zero extension of the source pressure
measurable on the whole spacetime domain. -/
theorem blowupPressureExtension_aestronglyMeasurable_of_split
    (p p₁ : ParabolicPoint → ℝ)
    (hp₁ : AEStronglyMeasurable p₁
      (volume.restrict (Set.univ ×ˢ Ioo (-1 : ℝ) 0)))
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p (z.1,z.2) - p₁ (z.1,z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0)))) :
    AEStronglyMeasurable (goodPointDomain.indicator p)
      (volume : Measure ParabolicPoint) := by
  have hball : CKN.euclideanBall (0 : Vec3) 1 = vec3Ball 0 1 :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by norm_num)
  have hdiff : AEStronglyMeasurable (fun z : ParabolicPoint => p z - p₁ z)
      (volume.restrict goodPointDomain) := by
    have h := hp₂.aestronglyMeasurable
    rw [Measure.prod_restrict,
      ← CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod] at h
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    change AEStronglyMeasurable
      (fun z : Vec3 × ℝ => p (z.1,z.2) - p₁ (z.1,z.2))
      ((volume.prod volume).restrict goodPointDomain)
    simpa only [goodPointDomain, hball,
      CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod] using h
  have hsub : goodPointDomain ⊆ (Set.univ : Set Vec3) ×ˢ Ioo (-1 : ℝ) 0 := by
    intro z hz
    exact ⟨Set.mem_univ _, hz.2⟩
  have hp₁loc : AEStronglyMeasurable p₁
      (volume.restrict goodPointDomain) :=
    hp₁.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hp : AEStronglyMeasurable p (volume.restrict goodPointDomain) := by
    convert hdiff.add hp₁loc using 1
    funext z
    dsimp
    ring
  exact (aestronglyMeasurable_indicator_iff
    ((isOpen_vec3Ball 0 1).measurableSet.prod measurableSet_Ioo)).2 hp

/-- The rescaled zero-extended pressure is measurable at every positive
scale. -/
theorem blowupPressure_aestronglyMeasurable_of_split
    (p p₁ : ParabolicPoint → ℝ)
    (hp₁ : AEStronglyMeasurable p₁
      (volume.restrict (Set.univ ×ˢ Ioo (-1 : ℝ) 0)))
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p (z.1,z.2) - p₁ (z.1,z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    AEStronglyMeasurable (blowupPressure x₀ t₀ r p)
      (volume : Measure ParabolicPoint) := by
  exact blowupRescaledPressure_aestronglyMeasurable
    (goodPointDomain.indicator p)
    (blowupPressureExtension_aestronglyMeasurable_of_split p p₁ hp₁ hp₂)
    x₀ t₀ r hr

end ESS
