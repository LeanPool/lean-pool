/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupCompactnessTop
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTenThirdsFromSource

/-!
# Blowup Compactness Source

Compactness of the rescaled fields in the endpoint regularity argument.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- The source slice and pressure bounds upgrade local strong `L²`
convergence of rescaled velocities to strong `L³` convergence on every
bounded cylinder ending at time zero. -/
theorem blowupRescale_strong_Lthree_to_time_zero_of_local_Ltwo
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
    (R a : ℝ) (hR : 0 < R) (ha : a < 0)
    (v : ParabolicPoint → Vec3)
    (hlocal : ∀ b : ℝ, b < 0 →
      Tendsto (fun k => eLpNorm
        (fun z => parabolicRescaleVelocity x₀ t₀ (r k) u z - v z) 2
        (volume.restrict (vec3Ball 0 R ×ˢ Ioo a b)))
        atTop (nhds 0)) :
    Tendsto (fun k => eLpNorm
      (fun z => parabolicRescaleVelocity x₀ t₀ (r k) u z - v z) 3
      (volume.restrict (vec3Ball 0 R ×ˢ Ioo a 0)))
      atTop (nhds 0) := by
  have hhigh := blowupRescale_eventually_tenThirds_of_source_slices
    u Du p p₁ hSuitable hu Mᵤ hMᵤ hsourceU
    hp₁ Mₚ hMₚ hsourceP hp₂ hharm
    x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha
  have hvolume : volume (vec3Ball (0 : Vec3) R) < ⊤ :=
    CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top
  have hExp : ENNReal.ofReal (10 / 3 : ℝ) = (10 / 3 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
    norm_num
  rw [hExp] at hhigh
  exact blowup_strong_Lthree_to_time_zero_parabolic
    (vec3Ball 0 R) (vec3Ball_measurable 0 R) hvolume a
    (fun k => parabolicRescaleVelocity x₀ t₀ (r k) u) v
    hhigh hlocal

end ESS
