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

public import LeanPool.LatticeDiracDerivation.V32NonrelativisticLimit
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumCurrentBridge

/-! # V3.2 Stage 12: native rest mass and physical-scale identifiability -/

@[expose] public section



namespace LeanDirac.V2

noncomputable section

/-- The V3.2 P hy si ca lR es tE ne rg y definition used by this stage. -/
def v32PhysicalRestEnergy (nativeEnergyUnit : ℝ) : ℝ :=
  chi0 * nativeEnergyUnit

/-- The V3.2 R es tS pi nU p definition used by this stage. -/
def v32RestSpinUp : CubicalCell4
  | 0 => 1
  | _ => 0

/-- The V3.2 R es tS pi nD ow n definition used by this stage. -/
def v32RestSpinDown : CubicalCell4
  | 1 => 1
  | _ => 0

/-- The V3.2 N at iv eC om pt on Le ng th definition used by this stage. -/
def v32NativeComptonLength : ℝ := c19ContinuumSpeed / chi0

theorem v32_native_rest_mass_is_nineteen : chi0 = 19 := by
  norm_num [chi0]

theorem v32_rest_gap_is_thirty_eight : 2 * chi0 = 38 := by
  norm_num [chi0]

theorem v32_rest_hamiltonian_exact (z : CubicalCell4) :
    v32ContinuumHamiltonian chi0 0 0 0 z =
      fun component => (chi0 : ℂ) * cubicalStandardBeta z component := by
  funext component
  fin_cases component <;>
    simp [v32ContinuumHamiltonian, cubicalStandardHamiltonian,
      cubicalStandardSpatial, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ]

theorem v32_physical_conversion_law (nativeEnergyUnit : ℝ) :
    v32PhysicalRestEnergy nativeEnergyUnit = 19 * nativeEnergyUnit := by
  simp [v32PhysicalRestEnergy, chi0]

theorem v32_absolute_energy_scale_not_selected :
    ∃ unitA unitB : ℝ,
      unitA ≠ unitB ∧
      v32PhysicalRestEnergy unitA ≠ v32PhysicalRestEnergy unitB := by
  refine ⟨1, 2, by norm_num, ?_⟩
  norm_num [v32PhysicalRestEnergy, chi0]

theorem v32_rest_spinors_are_positive_energy :
    (v32ContinuumHamiltonian chi0 0 0 0 v32RestSpinUp =
        fun component => (chi0 : ℂ) * v32RestSpinUp component) ∧
      (v32ContinuumHamiltonian chi0 0 0 0 v32RestSpinDown =
        fun component => (chi0 : ℂ) * v32RestSpinDown component) := by
  constructor <;> funext component <;> fin_cases component <;>
    simp [v32ContinuumHamiltonian, cubicalStandardHamiltonian,
      cubicalStandardSpatial, cubicalStandardBeta,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ, v32RestSpinUp, v32RestSpinDown]

theorem v32_rest_spinor_densities_are_one :
    cubicalCell4Density v32RestSpinUp = 1 ∧
      cubicalCell4Density v32RestSpinDown = 1 := by
  constructor <;>
    norm_num [cubicalCell4Density, v32RestSpinUp, v32RestSpinDown,
      Complex.normSq, Fin.sum_univ_four]

theorem v32_native_inertial_coefficient :
    (1 : ℝ) / (2 * chi0) = 1 / 38 := by
  norm_num [chi0]

theorem v32_native_compton_clock_ratio :
    chi0 * v32NativeComptonLength = c19ContinuumSpeed := by
  norm_num [v32NativeComptonLength, chi0]
  ring

/-- The bundled V3.2 N at iv eR es tM as sC er ti fi ca te. -/
structure NativeRestMassCertificate : Prop where
  canonicalMass :
    (0 : ℝ) ≤ chi0 ∧ chi0 ^ 2 = chi0 ^ 2 ∧
      ∀ mass : ℝ, 0 ≤ mass → mass ^ 2 = chi0 ^ 2 → mass = chi0
  nativeValue : chi0 = 19
  restHamiltonian : ∀ z,
    v32ContinuumHamiltonian chi0 0 0 0 z =
      fun component => (chi0 : ℂ) * cubicalStandardBeta z component
  positiveRestCurrentZero : ∀ axis r, r ≠ 0 → ∀ position,
    uniformPhaseSpaceCurrent axis r (fun _ => 0)
      (uniformRestPositivePhase r position) = 0
  restGap : 2 * chi0 = 38
  physicalConversion : ∀ nativeEnergyUnit,
    v32PhysicalRestEnergy nativeEnergyUnit = 19 * nativeEnergyUnit
  absoluteScaleNeedsAnchor : ∃ unitA unitB : ℝ,
    unitA ≠ unitB ∧
      v32PhysicalRestEnergy unitA ≠ v32PhysicalRestEnergy unitB
  explicitPositiveRestSpinors :
    (v32ContinuumHamiltonian chi0 0 0 0 v32RestSpinUp =
        fun component => (chi0 : ℂ) * v32RestSpinUp component) ∧
      (v32ContinuumHamiltonian chi0 0 0 0 v32RestSpinDown =
        fun component => (chi0 : ℂ) * v32RestSpinDown component)
  unitRestDensities :
    cubicalCell4Density v32RestSpinUp = 1 ∧
      cubicalCell4Density v32RestSpinDown = 1
  inertialCoefficient : (1 : ℝ) / (2 * chi0) = 1 / 38
  comptonClockRatio : chi0 * v32NativeComptonLength = c19ContinuumSpeed

theorem v32_native_rest_mass : NativeRestMassCertificate where
  canonicalMass := canonical_native_mass_is_chi0
  nativeValue := v32_native_rest_mass_is_nineteen
  restHamiltonian := v32_rest_hamiltonian_exact
  positiveRestCurrentZero := uniform_positive_rest_dirac_current_zero
  restGap := v32_rest_gap_is_thirty_eight
  physicalConversion := v32_physical_conversion_law
  absoluteScaleNeedsAnchor := v32_absolute_energy_scale_not_selected
  explicitPositiveRestSpinors := v32_rest_spinors_are_positive_energy
  unitRestDensities := v32_rest_spinor_densities_are_one
  inertialCoefficient := v32_native_inertial_coefficient
  comptonClockRatio := v32_native_compton_clock_ratio


end
end LeanDirac.V2
