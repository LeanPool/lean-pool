/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSuitable
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupVelocityUniform
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MainTheorems

/-!
# Blowup Suitable Integrable

Integrability conditions needed for suitability of the rescaled fields.
-/

public section

open CKN CKN.Foundation.Parabolic Set Filter
noncomputable section
namespace ESS

/-- The rescaled solutions satisfy the integrable suitable class on each
fixed larger past cylinder once the scale is small. -/
theorem blowupRescale_eventually_suitableIntegrable_outer
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
    (R a : ℝ) (hR : 0 < R) (ha : a < 0) :
    ∀ᶠ k in atTop,
      IsSuitableWeakSolutionIntegrable
        (CKN.euclideanBall 0 (R + 1)) (Ioo (a - 2) 0) 3
        (parabolicRescaleVelocity x₀ t₀ (r k) u)
        (parabolicRescaleGradient x₀ t₀ (r k) Du)
        (parabolicRescalePressure x₀ t₀ (r k) p)
        (0 : ParabolicPoint → Vec3) := by
  have houter := blowupRescale_eventually_suitable_on_cylinder
    u Du p hSuitable x₀ t₀ (R + 1) (a - 2) r
    hx₀ ht₀ hr hr0 (by linarith only [hR]) (by linarith only [ha])
  filter_upwards [houter] with k hk
  have hball : CKN.euclideanBall (0 : Vec3) (R + 1) =
      vec3Ball 0 (R + 1) :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by linarith only [hR])
  rw [hball]
  exact isSuitableWeakSolution_iff_integrable.mp hk

end ESS
