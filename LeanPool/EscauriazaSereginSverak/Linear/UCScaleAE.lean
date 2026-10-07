/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCScaleWeak

/-!
# Differential inequality under parabolic scaling

The almost-everywhere heat inequality in `lem:uc-gaussian` transfers through
the normalized parabolic coordinates.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The differential inequality is preserved almost everywhere under the
subunit parabolic dilation. -/
theorem uc_scaled_weak_heat_ae_bound
    (x₀ : Vec3) (scale ρ c₁ : ℝ) (hscale : 0 < scale)
    (hscale1 : scale ≤ 1) (hc₁ : 0 ≤ c₁)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hsource : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball x₀ (scale * ρ))
        (Ioo 0 (scale ^ 2 * 2)))),
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
        c₁ * (vec3EuclideanNorm (w z) +
          Real.sqrt (spatialGradientSq w Dw z))) :
    ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      vec3EuclideanNorm
        (ucWeakHeatVector (ucScaledD2w x₀ scale D2w)
          (ucScaledDtw x₀ scale Dtw) z) ≤
        c₁ * scale *
          (vec3EuclideanNorm ((ucScaledField x₀ scale w) z) +
            Real.sqrt (spatialGradientSq (ucScaledField x₀ scale w)
              (ucScaledDw x₀ scale Dw) z)) := by
  have hΩ : MeasurableSet (vec3Ball x₀ (scale * ρ)) :=
    vec3Ball_measurable _ _
  have hI : MeasurableSet (Ioo 0 (scale ^ 2 * 2)) := measurableSet_Ioo
  have hmap := CKN.map_scalingParabolic_restrict hscale
    ((x₀, 0) : ParabolicPoint) hΩ hI
  have hpoint : scalingParabolic scale ((x₀, 0) : ParabolicPoint) =
      ucScaledPoint x₀ scale := by
    funext z
    simp only [scalingParabolic, parabolicTranslate, parabolicScale,
      ucScaledPoint, zero_add]
    rfl
  rw [uc_scaled_cylinder_preimage x₀ scale ρ hscale, hpoint] at hmap
  have hpointMeas : Measurable (ucScaledPoint x₀ scale) := by
    change Measurable (fun z : ParabolicPoint =>
      (x₀ + scale • z.1, scale ^ 2 * z.2))
    have hs : Measurable (fun y : Vec3 => x₀ + scale • y) :=
      (measurable_const_add x₀).comp (measurable_const_smul scale)
    have ht : Measurable (fun s : ℝ => scale ^ 2 * s) :=
      measurable_const_mul (scale ^ 2)
    exact (hs.comp measurable_fst).prodMk (ht.comp measurable_snd)
  have hsourceMap : ∀ᵐ z ∂(Measure.map (ucScaledPoint x₀ scale)
      (volume.restrict (ucCylinder ρ))),
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
        c₁ * (vec3EuclideanNorm (w z) +
          Real.sqrt (spatialGradientSq w Dw z)) := by
    rw [hmap]
    exact Measure.ae_smul_measure hsource (ENNReal.ofReal (scale⁻¹ ^ 5))
  have hscaled := ae_of_ae_map hpointMeas.aemeasurable hsourceMap
  filter_upwards [hscaled] with z hz
  exact uc_scaled_weak_heat_bound x₀ scale c₁ hscale hscale1 hc₁
    w Dw D2w Dtw z hz

end ESS
