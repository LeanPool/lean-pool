/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupEnergyNormTransfer

/-!
# Blowup Gradient Rescale

Gradient estimates for the rescaled sequence used in endpoint compactness.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- Fixed local velocity and pressure norms give a scale-uniform gradient
bound on each compactly contained past cylinder of the rescaled solution. -/
theorem blowupRescale_eventually_gradient_bound_of_local_norms
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ)
    (hSuitable : IsSuitableWeakSolution (vec3Ball 0 (3 / 4 : ℝ))
      (Ioo (-1) 0) 3 u Du p (0 : ParabolicPoint → Vec3))
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0))
    (R a : ℝ) (hR : 0 < R) (ha : a < 0)
    (hvel : ∃ Bᵤ : ℝ≥0∞, Bᵤ < ⊤ ∧
      ∀ᶠ k in atTop,
        eLpNorm (fun z => vec3EuclideanNorm
          (blowupVelocity x₀ t₀ (r k) u z)) 3
          (volume.restrict (vec3Ball 0 (R + 1) ×ˢ Ioo (a - 2) 0)) ≤ Bᵤ)
    (hpress : ∃ Bₚ : ℝ≥0∞, Bₚ < ⊤ ∧
      ∀ᶠ k in atTop,
        eLpNorm (blowupPressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞)
          (volume.restrict (vec3Ball 0 (R + 1) ×ˢ Ioo (a - 2) 0)) ≤ Bₚ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, ∀ b : ℝ, b < 0 →
        2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a b),
          spatialGradientSq
            (parabolicRescaleVelocity x₀ t₀ (r k) u)
            (parabolicRescaleGradient x₀ t₀ (r k) Du) z) ≤ C := by
  have hsuit := blowupRescale_eventually_suitableIntegrable_outer
    u Du p hSuitable x₀ t₀ r hx₀ ht₀ hr hr0 R a hR ha
  obtain ⟨Bᵤ, Bₚ, hBᵤ, hBₚ, hnorm⟩ :=
    blowupFields_eventually_energy_norms u p x₀ t₀ r hx₀ ht₀ hr hr0
      (R + 1) (a - 2) hvel hpress
  have hball : CKN.euclideanBall (0 : Vec3) (R + 1) =
      vec3Ball 0 (R + 1) :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by linarith only [hR])
  have hnorm' : ∀ᶠ k in atTop,
      (MemLp (fun z => vec3EuclideanNorm
        (parabolicRescaleVelocity x₀ t₀ (r k) u z)) 3
        (volume.restrict (spaceTimeSet (CKN.euclideanBall 0 (R + 1))
          (Ioo (a - 2) 0))) ∧
       eLpNorm (fun z => vec3EuclideanNorm
        (parabolicRescaleVelocity x₀ t₀ (r k) u z)) 3
        (volume.restrict (spaceTimeSet (CKN.euclideanBall 0 (R + 1))
          (Ioo (a - 2) 0))) ≤ Bᵤ) ∧
      (MemLp (parabolicRescalePressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞)
        (volume.restrict (spaceTimeSet (CKN.euclideanBall 0 (R + 1))
          (Ioo (a - 2) 0))) ∧
       eLpNorm (parabolicRescalePressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞)
        (volume.restrict (spaceTimeSet (CKN.euclideanBall 0 (R + 1))
          (Ioo (a - 2) 0))) ≤ Bₚ) := by
    simpa only [spaceTimeSet, hball] using hnorm
  let V : ℕ → ParabolicPoint → Vec3 := fun k =>
    parabolicRescaleVelocity x₀ t₀ (r k) u
  let D : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun k =>
    parabolicRescaleGradient x₀ t₀ (r k) Du
  let P : ℕ → ParabolicPoint → ℝ := fun k =>
    parabolicRescalePressure x₀ t₀ (r k) p
  have hv : ∀ᶠ k in atTop, MemLp (fun z => vec3EuclideanNorm (V k z)) 3
      (volume.restrict (spaceTimeSet (CKN.euclideanBall 0 (R + 1))
        (Ioo (a - 2) 0))) ∧
      eLpNorm (fun z => vec3EuclideanNorm (V k z)) 3
      (volume.restrict (spaceTimeSet (CKN.euclideanBall 0 (R + 1))
        (Ioo (a - 2) 0))) ≤ Bᵤ := by
    filter_upwards [hnorm'] with k hk
    exact hk.1
  have hp : ∀ᶠ k in atTop, MemLp (P k) (3 / 2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet (CKN.euclideanBall 0 (R + 1))
        (Ioo (a - 2) 0))) ∧
      eLpNorm (P k) (3 / 2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet (CKN.euclideanBall 0 (R + 1))
        (Ioo (a - 2) 0))) ≤ Bₚ := by
    filter_upwards [hnorm'] with k hk
    exact hk.2
  obtain ⟨C₀, hC₀, hgrad⟩ := blowupGradient_eventually_bounded_all_upper_times
    R a hR V D P Bᵤ Bₚ hBᵤ hBₚ hsuit hv hp
  refine ⟨C₀, hC₀, ?_⟩
  simpa only [V, D, P] using hgrad

end ESS
