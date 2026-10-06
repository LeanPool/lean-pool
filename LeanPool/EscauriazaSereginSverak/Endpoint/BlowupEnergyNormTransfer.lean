/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupRescaleAgreement

public section

open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section
namespace ESS

/-- Local bounds for the zero-extended fields transfer to the ordinary
rescaled fields entering the suitable local energy inequality. -/
theorem blowupFields_eventually_energy_norms
    (u : ParabolicPoint → Vec3)
    (p : ParabolicPoint → ℝ)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ)
    (hvel : ∃ Bᵤ : ℝ≥0∞, Bᵤ < ⊤ ∧
      ∀ᶠ k in atTop,
        eLpNorm (fun z => vec3EuclideanNorm
          (blowupVelocity x₀ t₀ (r k) u z)) 3
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ Bᵤ)
    (hpress : ∃ Bₚ : ℝ≥0∞, Bₚ < ⊤ ∧
      ∀ᶠ k in atTop,
        eLpNorm (blowupPressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞)
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ Bₚ) :
    ∃ Bᵤ Bₚ : ℝ≥0∞, Bᵤ < ⊤ ∧ Bₚ < ⊤ ∧
      ∀ᶠ k in atTop,
        (MemLp (fun z => vec3EuclideanNorm
          (parabolicRescaleVelocity x₀ t₀ (r k) u z)) 3
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
        eLpNorm (fun z => vec3EuclideanNorm
          (parabolicRescaleVelocity x₀ t₀ (r k) u z)) 3
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ Bᵤ) ∧
        (MemLp (parabolicRescalePressure x₀ t₀ (r k) p)
          (3 / 2 : ℝ≥0∞)
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
        eLpNorm (parabolicRescalePressure x₀ t₀ (r k) p)
          (3 / 2 : ℝ≥0∞)
          (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ Bₚ) := by
  obtain ⟨Bᵤ, hBᵤ, hev⟩ := hvel
  obtain ⟨Bₚ, hBₚ, hep⟩ := hpress
  refine ⟨Bᵤ, Bₚ, hBᵤ, hBₚ, ?_⟩
  have heq := blowupFields_eventually_eLpNorm_eq_rescale
    u p x₀ t₀ r hx₀ ht₀ hr hr0 R a
  filter_upwards [heq, hev, hep] with k hk hkv hkp
  have hv : eLpNorm (fun z => vec3EuclideanNorm
      (parabolicRescaleVelocity x₀ t₀ (r k) u z)) 3
      (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ Bᵤ := by
    rw [← hk.1]
    exact hkv
  have hp : eLpNorm (parabolicRescalePressure x₀ t₀ (r k) p)
      (3 / 2 : ℝ≥0∞)
      (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ Bₚ := by
    rw [← hk.2]
    exact hkp
  constructor
  · exact ⟨(memLp_iff).2 (hv.trans_lt hBᵤ), hv⟩
  · exact ⟨(memLp_iff).2 (hp.trans_lt hBₚ), hp⟩

end ESS
