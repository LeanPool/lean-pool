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

public import LeanPool.LatticeDiracDerivation.V32ScaleIdentifiability
public import LeanPool.LatticeDiracDerivation.V32LatticeArtifacts
public import LeanPool.LatticeDiracDerivation.V32CopyClassification
public import LeanPool.LatticeDiracDerivation.V2.ReadoutCharacterization

/-! # V3.2 Stage 13: declared robustness and uniqueness scope -/

@[expose] public section



namespace LeanDirac.V2

noncomputable section
open Filter Topology

/-- The finite-periodic transverse tangent theorem is valid for an arbitrary
substrate kinetic normalization `B`.  The conclusion contains no selected
numerical value of `B`. -/
theorem v32_free_transverse_tangent_uniform_in_B
    {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r B : ℝ) (hr : r ≠ 0)
    (mode : PeriodicC19FourierMode L momentum)
    (position velocity : UniformCell2) :
    Tendsto
      (fun eps : ℝ =>
        periodicC19LagrangianTangentQuotient
          r B eps mode position velocity)
      (nhds 0)
      (nhds (2 * periodicSiteCount L *
        uniformVacuumModalLagrangian r momentum position velocity)) :=
  periodic_c19_lagrangian_tangent_tends_to_modal
    r B hr mode position velocity

/-- The bundled V3.2 T wo Co py Re st Se ct or Ce rt if ic at e. -/
structure V32TwoCopyRestSectorCertificate : Prop where
  spinUpPairMass :
    v32CopyPairHamiltonian (chi0 : ℂ) 0 0 0
        (v32RestSpinUp, v32RestSpinUp) =
      (fun component => (chi0 : ℂ) * v32RestSpinUp component,
        fun component => (chi0 : ℂ) * v32RestSpinUp component)
  spinDownPairMass :
    v32CopyPairHamiltonian (chi0 : ℂ) 0 0 0
        (v32RestSpinDown, v32RestSpinDown) =
      (fun component => (chi0 : ℂ) * v32RestSpinDown component,
        fun component => (chi0 : ℂ) * v32RestSpinDown component)
  unitDensity :
    cubicalCell4Density v32RestSpinUp = 1 ∧
      cubicalCell4Density v32RestSpinDown = 1
  zeroRestCurrent : ∀ axis,
    cubicalDiracCurrent axis v32RestSpinUp = 0 ∧
      cubicalDiracCurrent axis v32RestSpinDown = 0
  nativeMass : chi0 = 19
  branchGap : 2 * chi0 = 38

theorem v32_two_copy_rest_sector : V32TwoCopyRestSectorCertificate where
  spinUpPairMass := by
    apply Prod.ext <;> funext component
    · exact congrFun v32_rest_spinors_are_positive_energy.1 component
    · exact congrFun v32_rest_spinors_are_positive_energy.1 component
  spinDownPairMass := by
    apply Prod.ext <;> funext component
    · exact congrFun v32_rest_spinors_are_positive_energy.2 component
    · exact congrFun v32_rest_spinors_are_positive_energy.2 component
  unitDensity := v32_rest_spinor_densities_are_one
  zeroRestCurrent := by
    intro axis
    fin_cases axis <;>
      constructor <;>
      norm_num [cubicalDiracCurrent, cubicalVelocityOperator,
        cubicalCell4RealPair, cubicalAlpha, cubicalStandardAlphaX,
        cubicalStandardAlphaY, cubicalStandardAlphaZ,
        v32RestSpinUp, v32RestSpinDown, Fin.sum_univ_four,
        Complex.normSq, Complex.mul_re, Complex.mul_im]
  nativeMass := v32_native_rest_mass_is_nineteen
  branchGap := v32_rest_gap_is_thirty_eight

/-- The bundled V3.2 R ob us tn es sC er ti fi ca te. -/
structure V32RobustnessCertificate : Prop where
  fullFreeChain : CompleteFreeDiracCertificate
  readoutScope : CubicalReadoutCharacterizationCertificate
  flavorScope : CubicalFlavorClassificationCertificate
  nativeMass : NativeRestMassCertificate
  artifacts : V32LatticeArtifactCertificate
  twoCopyRestSector : V32TwoCopyRestSectorCertificate
  arbitraryB : ∀ {L : ℕ} [NeZero L] {momentum : LatticeMomentum}
    (r B : ℝ), r ≠ 0 →
    ∀ (mode : PeriodicC19FourierMode L momentum)
      (position velocity : UniformCell2),
      Tendsto
        (fun eps : ℝ =>
          periodicC19LagrangianTangentQuotient
            r B eps mode position velocity)
        (nhds 0)
        (nhds (2 * periodicSiteCount L *
          uniformVacuumModalLagrangian r momentum position velocity))

theorem v32_robustness : V32RobustnessCertificate where
  fullFreeChain := complete_first_principles_free_dirac
  readoutScope := cubical_readout_characterization
  flavorScope := cubical_flavor_classification
  nativeMass := v32_native_rest_mass
  artifacts := v32_lattice_artifacts
  twoCopyRestSector := v32_two_copy_rest_sector
  arbitraryB := fun r B hr mode position velocity =>
    v32_free_transverse_tangent_uniform_in_B
      r B hr mode position velocity


end
end LeanDirac.V2
