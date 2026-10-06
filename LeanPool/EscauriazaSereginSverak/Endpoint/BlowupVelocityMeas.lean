/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupVelocityTime

public section

open MeasureTheory CKN CKN.Foundation.Parabolic Set
open scoped ENNReal
noncomputable section
namespace ESS

/-- Positive parabolic rescaling preserves almost everywhere strong
measurability of a velocity field. -/
theorem blowupRescaledVelocity_aestronglyMeasurable
    (u : ParabolicPoint → Vec3)
    (hu : AEStronglyMeasurable u (volume : Measure ParabolicPoint))
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) :
    AEStronglyMeasurable (parabolicRescaleVelocity x₀ t₀ r u)
      (volume : Measure ParabolicPoint) := by
  let φ : ParabolicPoint → ParabolicPoint := CKN.scalingParabolic r (x₀,t₀)
  let a : ℝ≥0∞ := ENNReal.ofReal (r⁻¹ ^ 5)
  have hmap : Measure.map φ (volume : Measure ParabolicPoint) =
      a • (volume : Measure ParabolicPoint) :=
    CKN.map_scalingParabolic r hr (x₀,t₀)
  have huMap : AEStronglyMeasurable u
      (Measure.map φ (volume : Measure ParabolicPoint)) := by
    rw [hmap]
    exact hu.mono_ac Measure.smul_absolutelyContinuous
  have hφmeas : Measurable φ := by
    apply Continuous.measurable
    change Continuous (CKN.scalingParabolic r ((x₀,t₀) : ParabolicPoint))
    rw [CKN.scalingParabolic_eq r ((x₀,t₀) : ParabolicPoint)]
    have hs : Continuous (CKN.scalingSpace r x₀) := by
      change Continuous (fun x : Vec3 => x₀ + r • x)
      fun_prop
    have ht : Continuous (CKN.scalingTime r t₀) := by
      change Continuous (fun t : ℝ => t₀ + r ^ 2 * t)
      fun_prop
    exact continuous_prod_to_parabolicPoint.comp
      (((hs.comp continuous_fst).prodMk (ht.comp continuous_snd)).comp
        continuous_parabolicPoint_to_prod)
  have hcomp : AEStronglyMeasurable (u ∘ φ)
      (volume : Measure ParabolicPoint) :=
    huMap.comp_aemeasurable hφmeas.aemeasurable
  have hscale : Continuous (fun v : Vec3 => r • v) := by fun_prop
  have hscaled := hscale.comp_aestronglyMeasurable hcomp
  change AEStronglyMeasurable
    (fun z => r • u (parabolicTranslate x₀ t₀ (parabolicScale r z))) volume
  exact hscaled

/-- The scalar velocity norm of a rescaling is jointly measurable on every
product past-time region. -/
theorem blowupRescaledVelocity_norm_aestronglyMeasurable_prod
    (u : ParabolicPoint → Vec3)
    (hu : AEStronglyMeasurable u (volume : Measure ParabolicPoint))
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r) (J : Set ℝ) :
    AEStronglyMeasurable
      (fun z : Vec3 × ℝ =>
        vec3EuclideanNorm (parabolicRescaleVelocity x₀ t₀ r u (z.1,z.2)))
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict J)) := by
  have h := CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
    (blowupRescaledVelocity_aestronglyMeasurable u hu x₀ t₀ r hr)
  have h' := h.restrict (s := ((Set.univ : Set Vec3) ×ˢ J : Set ParabolicPoint))
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod] at h'
  change AEStronglyMeasurable
    (fun z : Vec3 × ℝ =>
      vec3EuclideanNorm (parabolicRescaleVelocity x₀ t₀ r u (z.1,z.2)))
    ((volume.prod volume).restrict ((Set.univ : Set Vec3) ×ˢ J)) at h'
  simpa only [Measure.prod_restrict] using h'

end ESS
