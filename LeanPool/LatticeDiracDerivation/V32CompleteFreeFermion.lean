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

public import LeanPool.LatticeDiracDerivation.V32DiscreteSymmetries
public import LeanPool.LatticeDiracDerivation.V32PacketBenchmarks

/-!
# V3.2 Stage 17: cumulative machine-checked certificate

This certificate assembles the V3.2 modules.  Release status is controlled by
the separate hostile claim audit; compilation alone does not widen any claim.
-/

@[expose] public section



namespace LeanDirac.V2

noncomputable section

/-- The bundled V3.2 C om pl et eF re eF er mi on Ce rt if ic at e. -/
structure V32CompleteFreeFermionCertificate : Prop where
  framework : V32FrameworkLockCertificate
  spectrum : V32GlobalSpectrumCertificate
  projectors : V32SpectralProjectorCertificate
  brillouin : V32BrillouinZoneCertificate
  copies : V32CopyClassificationCertificate
  particleSector : V32IrreducibleParticleCertificate
  finiteLorentz : V32FiniteLorentzCertificate
  discreteSymmetries : V32DiscreteSymmetryCertificate
  nonrelativistic : V32NonrelativisticLimitCertificate
  continuum : V32ContinuumOperatorConvergenceCertificate
  artifacts : V32LatticeArtifactCertificate
  restMass : NativeRestMassCertificate
  robustness : V32RobustnessCertificate
  transport : V32TransportObservableCertificate
  centeredStep : V32CenteredStepTransportCertificate
  packets : V32PacketBenchmarkCertificate

theorem v32_complete_free_fermion : V32CompleteFreeFermionCertificate where
  framework := v32_framework_lock
  spectrum := v32_global_spectrum
  projectors := v32_spectral_projectors
  brillouin := v32_brillouin_zone_audit
  copies := v32_copy_classification
  particleSector := v32_irreducible_particle_sector
  finiteLorentz := v32_finite_lorentz
  discreteSymmetries := v32_discrete_symmetries
  nonrelativistic := v32_nonrelativistic_limit
  continuum := v32_continuum_operator_convergence
  artifacts := v32_lattice_artifacts
  restMass := v32_native_rest_mass
  robustness := v32_robustness
  transport := v32_transport_observables
  centeredStep := v32_centered_step_transport
  packets := v32_packet_benchmarks


end
end LeanDirac.V2
