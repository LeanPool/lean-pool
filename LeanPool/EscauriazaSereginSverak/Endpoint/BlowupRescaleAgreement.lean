/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupGradientLocal

public section

open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- On each fixed past cylinder, zero extension agrees eventually with the
ordinary rescalings used in the suitable-solution statement. -/
theorem blowupFields_eventually_eq_rescale_on_pastBox
    (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) :
    ∀ᶠ k in atTop, ∀ z ∈ vec3Ball 0 R ×ˢ Ioo a 0,
      blowupVelocity x₀ t₀ (r k) u z =
        parabolicRescaleVelocity x₀ t₀ (r k) u z ∧
      blowupPressure x₀ t₀ (r k) p z =
        parabolicRescalePressure x₀ t₀ (r k) p z := by
  have hsubset := blowupCylinder_eventually_subset_domain
    x₀ t₀ R a r hx₀ ht₀ hr hr0
  filter_upwards [hsubset] with k hk z hz
  exact ⟨blowupVelocity_eq_of_mem x₀ t₀ (r k) u z (hk hz),
    blowupPressure_eq_of_mem x₀ t₀ (r k) p z (hk hz)⟩

/-- The eventual pointwise agreement transfers local velocity and pressure
seminorms between zero extension and ordinary rescaling. -/
theorem blowupFields_eventually_eLpNorm_eq_rescale
    (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) :
    ∀ᶠ k in atTop,
      eLpNorm (fun z => vec3EuclideanNorm
        (blowupVelocity x₀ t₀ (r k) u z)) 3
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) =
        eLpNorm (fun z => vec3EuclideanNorm
          (parabolicRescaleVelocity x₀ t₀ (r k) u z)) 3
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
      eLpNorm (blowupPressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞)
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) =
        eLpNorm (parabolicRescalePressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞)
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) := by
  let C := vec3Ball 0 R ×ˢ Ioo a 0
  have hC : MeasurableSet C :=
    (isOpen_vec3Ball 0 R).measurableSet.prod measurableSet_Ioo
  have heq := blowupFields_eventually_eq_rescale_on_pastBox
    u p x₀ t₀ r hx₀ ht₀ hr hr0 R a
  filter_upwards [heq] with k hk
  have hvel : (fun z => vec3EuclideanNorm (blowupVelocity x₀ t₀ (r k) u z))
      =ᵐ[volume.restrict C]
      (fun z => vec3EuclideanNorm (parabolicRescaleVelocity x₀ t₀ (r k) u z)) := by
    filter_upwards [ae_restrict_mem hC] with z hz
    rw [(hk z hz).1]
  have hpress : blowupPressure x₀ t₀ (r k) p =ᵐ[volume.restrict C]
      parabolicRescalePressure x₀ t₀ (r k) p := by
    filter_upwards [ae_restrict_mem hC] with z hz
    exact (hk z hz).2
  exact ⟨eLpNorm_congr_ae hvel, eLpNorm_congr_ae hpress⟩

end ESS
