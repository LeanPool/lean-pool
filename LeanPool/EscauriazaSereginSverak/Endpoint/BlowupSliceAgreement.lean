/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLocalBox

/-!
# Blowup Slice Agreement

Spatial slice bounds and rescaling identities in the endpoint compactness argument.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- On an interior rescaled cylinder, the ordinary velocity has the same
uniform local `L²` slice bound as the zero-extended velocity. -/
theorem blowupRescaledVelocity_component_slice_two_essSup_le_of_domain
    (u : ParabolicPoint → Vec3)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (J : Set ℝ) (hJm : MeasurableSet J)
    (hJ : J ⊆ CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0))
    (M : ℝ≥0∞)
    (hsource : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable
        (fun x : Vec3 => (goodPointDomain.indicator u) (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        ((goodPointDomain.indicator u) (x,s))) 3 volume ≤ M)
    (c : Vec3) (R : ℝ) (i : Fin 3)
    (hdomain : vec3Ball c R ×ˢ J ⊆ blowupDomain x₀ t₀ r) :
    essSup (fun t => eLpNorm (fun x : Vec3 =>
      parabolicRescaleVelocity x₀ t₀ r u (x,t) i) 2
      (volume.restrict (vec3Ball c R))) (volume.restrict J) ≤
      M * (volume (vec3Ball c R)) ^ (1 / 6 : ℝ) := by
  have hres := blowupRescaledVelocity_component_slice_two_essSup_le
    (goodPointDomain.indicator u) x₀ t₀ r hr J hJ M hsource c R i
  have hslice : ∀ᵐ t ∂volume.restrict J,
      eLpNorm (fun x : Vec3 =>
        parabolicRescaleVelocity x₀ t₀ r u (x,t) i) 2
        (volume.restrict (vec3Ball c R)) =
      eLpNorm (fun x : Vec3 =>
        blowupVelocity x₀ t₀ r u (x,t) i) 2
        (volume.restrict (vec3Ball c R)) := by
    filter_upwards [ae_restrict_mem hJm] with t ht
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_vec3Ball c R).measurableSet] with x hx
    have hz : (x,t) ∈ blowupDomain x₀ t₀ r := hdomain ⟨hx, ht⟩
    rw [blowupVelocity_eq_of_mem x₀ t₀ r u (x,t) hz]
    rfl
  have heq := essSup_congr_ae hslice
  rw [heq]
  simpa only [blowupVelocity] using hres

end ESS
