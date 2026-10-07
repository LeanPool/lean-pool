/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsDefinition
public import LeanPool.EscauriazaSereginSverak.Endpoint.RescalingSuitable

/-!
# Fields on rescaled past cylinders

The original velocity, weak gradient, and pressure are extended by zero from
the source cylinder before parabolic rescaling, as in `prop:blowup-limit`.
-/

public section


open Set CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The rescaled preimage of the original open cylinder (`prop:blowup-limit`). -/
@[expose] def blowupDomain (x₀ : Vec3) (t₀ r : ℝ) : Set ParabolicPoint :=
  (fun z => parabolicTranslate x₀ t₀ (parabolicScale r z)) ⁻¹' goodPointDomain

/-- The velocity after zero extension from the source cylinder and scaling. -/
@[expose] def blowupVelocity (x₀ : Vec3) (t₀ r : ℝ)
    (u : ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  parabolicRescaleVelocity x₀ t₀ r (goodPointDomain.indicator u)

/-- The weak spatial gradient after zero extension and scaling. -/
@[expose] def blowupGradient (x₀ : Vec3) (t₀ r : ℝ)
    (Du : ParabolicPoint → Fin 3 → Vec3) :
    ParabolicPoint → Fin 3 → Vec3 :=
  parabolicRescaleGradient x₀ t₀ r (goodPointDomain.indicator Du)

/-- The pressure after zero extension from the source cylinder and scaling. -/
@[expose] def blowupPressure (x₀ : Vec3) (t₀ r : ℝ)
    (p : ParabolicPoint → ℝ) : ParabolicPoint → ℝ :=
  parabolicRescalePressure x₀ t₀ r (goodPointDomain.indicator p)

/-- On the rescaled source domain, the velocity agrees with ordinary
Navier--Stokes scaling. -/
theorem blowupVelocity_eq_of_mem (x₀ : Vec3) (t₀ r : ℝ)
    (u : ParabolicPoint → Vec3) (z : ParabolicPoint)
    (hz : z ∈ blowupDomain x₀ t₀ r) :
    blowupVelocity x₀ t₀ r u z =
      r • u (parabolicTranslate x₀ t₀ (parabolicScale r z)) := by
  change parabolicTranslate x₀ t₀ (parabolicScale r z) ∈ goodPointDomain at hz
  simp only [blowupVelocity, parabolicRescaleVelocity]
  rw [Set.indicator_of_mem hz]

/-- On the rescaled source domain, the weak gradient agrees with ordinary
Navier--Stokes scaling. -/
theorem blowupGradient_eq_of_mem (x₀ : Vec3) (t₀ r : ℝ)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint)
    (hz : z ∈ blowupDomain x₀ t₀ r) :
    blowupGradient x₀ t₀ r Du z =
      fun i => r ^ 2 • Du (parabolicTranslate x₀ t₀ (parabolicScale r z)) i := by
  change parabolicTranslate x₀ t₀ (parabolicScale r z) ∈ goodPointDomain at hz
  funext i
  simp only [blowupGradient, parabolicRescaleGradient]
  rw [Set.indicator_of_mem hz]

/-- On the rescaled source domain, the pressure agrees with ordinary
Navier--Stokes scaling. -/
theorem blowupPressure_eq_of_mem (x₀ : Vec3) (t₀ r : ℝ)
    (p : ParabolicPoint → ℝ) (z : ParabolicPoint)
    (hz : z ∈ blowupDomain x₀ t₀ r) :
    blowupPressure x₀ t₀ r p z =
      r ^ 2 * p (parabolicTranslate x₀ t₀ (parabolicScale r z)) := by
  change parabolicTranslate x₀ t₀ (parabolicScale r z) ∈ goodPointDomain at hz
  simp only [blowupPressure, parabolicRescalePressure]
  rw [Set.indicator_of_mem hz]

end ESS
