/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupGradientTop
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureUniform

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- Source slice bounds for the zero-extended velocity and the fixed pressure
split give a uniform rescaled gradient bound up to the open terminal time. -/
theorem blowupRescale_eventually_gradient_bound_to_time_zero_of_source_slices
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
      IntegrableOn (fun z => spatialGradientSq
        (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (parabolicRescaleGradient x₀ t₀ (r k) Du) z)
        (spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a 0)) volume ∧
      2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a 0),
        spatialGradientSq
          (parabolicRescaleVelocity x₀ t₀ (r k) u)
          (parabolicRescaleGradient x₀ t₀ (r k) Du) z) ≤ C := by
  have hvel : ∃ Bᵤ : ℝ≥0∞, Bᵤ < ⊤ ∧
      ∀ᶠ k in atTop,
        eLpNorm (fun z => vec3EuclideanNorm
          (blowupVelocity x₀ t₀ (r k) u z)) 3
          (volume.restrict (vec3Ball 0 (R + 1) ×ˢ Ioo (a - 2) 0)) ≤ Bᵤ := by
    simpa only [blowupVelocity] using
      blowupRescaledVelocity_eventually_bounded_pastBox
        (goodPointDomain.indicator u) hu Mᵤ hMᵤ hsourceU
        x₀ t₀ r ht₀ hr hr0 (R + 1) (a - 2)
  have hpress : ∃ Bₚ : ℝ≥0∞, Bₚ < ⊤ ∧
      ∀ᶠ k in atTop,
        eLpNorm (blowupPressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞)
          (volume.restrict (vec3Ball 0 (R + 1) ×ˢ Ioo (a - 2) 0)) ≤ Bₚ :=
    blowupPressure_eventually_bounded_pastBox
      p p₁ hp₁ Mₚ hMₚ hsourceP hp₂ hharm
      x₀ t₀ r hx₀ ht₀ hr hr0
      (R + 1) (a - 2) (by linarith only [hR]) (by linarith only [ha])
  exact blowupRescale_eventually_gradient_bound_to_time_zero_of_local_norms
    u Du p hSuitable x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha hvel hpress

end ESS
