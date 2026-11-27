/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit e2161e0936f181d4a5a9d49963a666f7cea42502.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V32TransportObservables
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumVerletDispersion
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumVerletStability

/-! # V3.2 Stage 15: exact centered-step spectrum -/

@[expose] public section



namespace LeanDirac.V2

noncomputable section
open Filter Topology

/-- The bundled V3.2 C en te re dS te pT ra ns po rt Ce rt if ic at e. -/
structure V32CenteredStepTransportCertificate : Prop where
  exactDispersion : ∀ r dt momentum,
    uniformVerletStable r dt momentum →
      Real.cos (dt * uniformVerletAngularFrequency r dt momentum) =
        1 - uniformVerletStabilityParameter r dt momentum / 2
  rootHasUnitNorm : ∀ r dt momentum,
    ‖uniformVerletCharacteristicRoot r dt momentum‖ = 1
  rootSolvesRecurrence : ∀ r dt momentum,
    uniformVerletStable r dt momentum →
      uniformVerletCharacteristicRoot r dt momentum ^ 2 -
        ((2 - uniformVerletStabilityParameter r dt momentum : ℝ) : ℂ) *
          uniformVerletCharacteristicRoot r dt momentum + 1 = 0
  modifiedEnergyInvariant : ∀ r dt momentum phase,
    uniformVerletModifiedEnergy r dt momentum
        (uniformVerletPhaseStep r dt momentum phase) =
      uniformVerletModifiedEnergy r dt momentum phase
  numericalFrequencyConverges : ∀ r momentum,
    Tendsto (fun dt : ℝ => uniformVerletAngularFrequency r dt momentum)
      (nhds 0) (nhds (uniformVacuumModalFrequency r momentum))
  exactStepAngle : ∀ r dt momentum,
    dt * uniformVerletAngularFrequency r dt momentum =
      2 * Real.arcsin
        (dt * uniformVacuumModalFrequency r momentum / 2)

theorem v32_centered_step_transport : V32CenteredStepTransportCertificate where
  exactDispersion := uniform_verlet_exact_dispersion
  rootHasUnitNorm := uniform_verlet_characteristic_root_norm
  rootSolvesRecurrence := uniform_verlet_characteristic_root_equation
  modifiedEnergyInvariant := uniform_verlet_modified_energy_invariant
  numericalFrequencyConverges :=
    uniform_verlet_angular_frequency_tends_to_native
  exactStepAngle := uniform_verlet_step_angle


end
end LeanDirac.V2
