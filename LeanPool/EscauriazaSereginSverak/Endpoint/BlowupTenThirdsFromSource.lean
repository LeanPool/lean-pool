/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTenThirdsEventually

/-!
# Blowup Ten Thirds From Source

Space-time integrability of the rescaled velocity at exponent 10/3.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- The source slice estimate and fixed pressure split give the local
space-time `L^(10/3)` bound for the rescaled velocity. -/
theorem blowupRescale_eventually_tenThirds_of_source_slices
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
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ᶠ k in atTop,
      MemLp (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ∧
      eLpNorm (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (ENNReal.ofReal (10 / 3 : ℝ))
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)) ≤ B := by
  obtain ⟨C, _, hgrad⟩ :=
    blowupRescale_eventually_gradient_bound_to_time_zero_of_source_slices
      u Du p p₁ hSuitable hu Mᵤ hMᵤ hsourceU
      hp₁ Mₚ hMₚ hsourceP hp₂ hharm
      x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha
  exact blowupRescale_eventually_tenThirds_of_gradient_bound
    u Du p hSuitable hu Mᵤ hMᵤ hsourceU
    x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha C hgrad

end ESS
