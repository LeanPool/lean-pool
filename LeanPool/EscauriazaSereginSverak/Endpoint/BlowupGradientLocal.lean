/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSuitableIntegrable
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupMassLp

/-!
# Blowup Gradient Local

Gradient estimates for the rescaled sequence used in endpoint compactness.
-/

public section

open CKN CKN.Foundation.Parabolic MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace ESS

/-- The same tail and numerical bound work for every upper endpoint below
time zero. -/
theorem blowupGradient_eventually_bounded_all_upper_times
    (R a : ℝ) (hR : 0 < R)
    (u : ℕ → ParabolicPoint → Vec3)
    (Du : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (p : ℕ → ParabolicPoint → ℝ)
    (Bᵤ Bₚ : ℝ≥0∞) (hBᵤ : Bᵤ < ⊤) (hBₚ : Bₚ < ⊤)
    (hsuitable : ∀ᶠ k in atTop,
      IsSuitableWeakSolutionIntegrable
        (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0) 3
        (u k) (Du k) (p k) 0)
    (hu : ∀ᶠ k in atTop,
      MemLp (fun z : ParabolicPoint => vec3EuclideanNorm (u k z)) 3
        (volume.restrict
          (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0))) ∧
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (u k z)) 3
        (volume.restrict
          (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0))) ≤ Bᵤ)
    (hp : ∀ᶠ k in atTop,
      MemLp (p k) (3 / 2 : ℝ≥0∞)
        (volume.restrict
          (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0))) ∧
      eLpNorm (p k) (3 / 2 : ℝ≥0∞)
        (volume.restrict
          (spaceTimeSet (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0))) ≤ Bₚ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, ∀ b : ℝ, b < 0 →
        2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R) (Ioo a b),
          spatialGradientSq (u k) (Du k) z) ≤ C := by
  obtain ⟨C₀, hC₀, hbound⟩ := blowupEnergyCutoff_gradient_bound_of_norms R hR
  let C : ℝ := (8 + 3 * C₀) *
      (volume.restrict (spaceTimeSet (CKN.euclideanBall 0 (R + 1))
        (Ioo (a - 2) 0))).real Set.univ +
      (8 + 8 * C₀) * Bᵤ.toReal ^ 3 +
      4 * C₀ * Bₚ.toReal ^ (3 / 2 : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsuitable, hu, hp] with k hs hkᵤ hkₚ
  intro b hb
  exact hbound a b hb Bᵤ Bₚ hBᵤ hBₚ hs hkᵤ.1 hkₚ.1 hkᵤ.2 hkₚ.2

end ESS
