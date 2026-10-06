/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupEnergyPressureIntegral

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- The source velocity bound and fixed pressure split control pressure mass
and Dirichlet energy on a rescaled open past cylinder, including its top. -/
theorem blowupRescale_eventually_energy_pressure_bound_of_source_slices
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (p p₁ : ParabolicPoint → ℝ)
    (hSuitable : IsSuitableWeakSolution (vec3Ball 0 (3 / 4 : ℝ))
      (Ioo (-1) 0) 3 u Du p (0 : ParabolicPoint → Vec3))
    (hu : AEStronglyMeasurable (goodPointDomain.indicator u)
      (volume : Measure ParabolicPoint))
    (Mᵤ : ℝ≥0∞) (hMᵤ : Mᵤ < ⊤)
    (hsourceU : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable
        (fun x : Vec3 => (goodPointDomain.indicator u) (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        ((goodPointDomain.indicator u) (x,s))) 3 volume ≤ Mᵤ)
    (hp₁ : AEStronglyMeasurable p₁
      (volume.restrict (Set.univ ×ˢ Ioo (-1 : ℝ) 0)))
    (Mₚ : ℝ≥0∞) (hMₚ : Mₚ < ⊤)
    (hsourceP : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 => p₁ (x,s)) volume ∧
      eLpNorm (fun x : Vec3 => p₁ (x,s)) (3 / 2 : ℝ≥0∞) volume ≤ Mₚ)
    (hp₂ : MemLp (fun z : Vec3 × ℝ => p (z.1,z.2) - p₁ (z.1,z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hharm : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p (x,t) - p₁ (x,t)))
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      IntegrableOn (fun z =>
        |blowupPressure x₀ t₀ (r k) p z| ^ (3 / 2 : ℝ) +
        spatialGradientSq
          (parabolicRescaleVelocity x₀ t₀ (r k) u)
          (parabolicRescaleGradient x₀ t₀ (r k) Du) z)
        (vec3Ball 0 R ×ˢ Ioo a 0) volume ∧
      (∫ (z : ParabolicPoint) in vec3Ball 0 R ×ˢ Ioo a 0,
        |blowupPressure x₀ t₀ (r k) p z| ^ (3 / 2 : ℝ) +
        spatialGradientSq
          (parabolicRescaleVelocity x₀ t₀ (r k) u)
          (parabolicRescaleGradient x₀ t₀ (r k) Du) z
        ∂(volume : Measure ParabolicPoint)) ≤ C := by
  obtain ⟨Cg, hCg, hgrad⟩ :=
    blowupRescale_eventually_gradient_bound_to_time_zero_of_source_slices
      u Du p p₁ hSuitable hu Mᵤ hMᵤ hsourceU
      hp₁ Mₚ hMₚ hsourceP hp₂ hharm
      x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha
  obtain ⟨Cp, hCp, hpress⟩ :=
    blowupPressure_eventually_mass_bound_pastBox
      p p₁ hp₁ Mₚ hMₚ hsourceP hp₂ hharm
      x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha
  refine ⟨Cp + Cg, add_nonneg hCp hCg, ?_⟩
  filter_upwards [hgrad, hpress] with k hkg hkp
  have hball : CKN.euclideanBall (0 : Vec3) R = vec3Ball 0 R :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hR
  rw [hball] at hkg
  exact blowup_energyPressure_integral_bound R a
    (parabolicRescaleVelocity x₀ t₀ (r k) u)
    (parabolicRescaleGradient x₀ t₀ (r k) Du)
    (blowupPressure x₀ t₀ (r k) p)
    Cg Cp hkg.1 hkg.2 hkp.1 hkp.2

end ESS
