/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupGradientComponent

/-!
# Blowup Slice Rescale Uniform

Spatial slice bounds and rescaling identities in the endpoint compactness argument.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- The source `L³` slice bound controls the local `L²` essential
supremum of each rescaled velocity component on any past interval. -/
theorem blowupRescaledVelocity_component_slice_two_essSup_le
    (u : ParabolicPoint → Vec3)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (J : Set ℝ) (hJ : J ⊆ CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0))
    (M : ℝ≥0∞)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => u (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,s))) 3 volume ≤ M)
    (c : Vec3) (R : ℝ) (i : Fin 3) :
    essSup (fun t => eLpNorm (fun x : Vec3 =>
      parabolicRescaleVelocity x₀ t₀ r u (x,t) i) 2
      (volume.restrict (vec3Ball c R))) (volume.restrict J) ≤
      M * (volume (vec3Ball c R)) ^ (1 / 6 : ℝ) := by
  have hpull := blowup_ae_time_pullback_on r t₀ hr
    (Ioo (-1 : ℝ) 0) J measurableSet_Ioo hJ
    (fun s => AEStronglyMeasurable (fun x : Vec3 => u (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x,s))) 3 volume ≤ M)
    hsource
  have hbound := blowupRescaledVelocity_slice_bound_ae
    u x₀ t₀ r hr J hJ M hsource
  have hslice : ∀ᵐ t ∂volume.restrict J,
      AEStronglyMeasurable
        (fun x : Vec3 => parabolicRescaleVelocity x₀ t₀ r u (x,t)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        (parabolicRescaleVelocity x₀ t₀ r u (x,t))) 3 volume ≤ M := by
    filter_upwards [hpull, hbound] with t ht hb
    have heq (x : Vec3) :
        parabolicRescaleVelocity x₀ t₀ r u (x,t) =
          r • u (x₀ + r • x, CKN.scalingTime r t₀ t) := by
      simp [parabolicRescaleVelocity, CKN.scalingTime,
        parabolicTranslate, parabolicScale]
    refine ⟨?_, hb⟩
    simp_rw [heq]
    exact blowup_rescaled_velocitySlice_aestronglyMeasurable
      (fun x => u (x, CKN.scalingTime r t₀ t))
      ht.1 x₀ r hr
  exact blowup_component_slice_two_essSup_le_of_three
    (parabolicRescaleVelocity x₀ t₀ r u) J c R i M hslice

end ESS
