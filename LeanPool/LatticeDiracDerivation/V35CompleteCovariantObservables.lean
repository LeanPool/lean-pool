/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit 43859849eb6ed37e16c802fbae3fd50dd731665c.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V35FrameworkAndGapLock
public import LeanPool.LatticeDiracDerivation.V35AntiparticleResidueClosure
public import LeanPool.LatticeDiracDerivation.V35GeneratedLorentzTransformations
public import LeanPool.LatticeDiracDerivation.V35CovariantSolutionTransport
public import LeanPool.LatticeDiracDerivation.V35CompleteBilinears
public import LeanPool.LatticeDiracDerivation.V35BilinearCliffordClosure
public import LeanPool.LatticeDiracDerivation.V35MovingSpinInvariant

/-!
# V3.5 Stage 8: complete covariant-observable closure

The certificate packages the theorem-only V3.5 extension.  The transport
field is algebraic covariance of free solutions under the derived finite
boost; it is not a claim about finite packets or nonlinear evolution.
-/

@[expose] public section

namespace LeanDirac.V2

/-- Cumulative V3.5 certificate assembling the unchanged V3.4 result and all
new covariant-observable closure stages. -/
structure V35CompleteCovariantObservableCertificate : Prop where
  framework : V35FrameworkAndGapLockCertificate
  prior : V34CompleteCovariantFreeSpinorCertificate
  antiparticleResidue : V35AntiparticleResidueClosureCertificate
  generatedTransformations : V35GeneratedLorentzTransformationCertificate
  covariantSolutions : V35CovariantSolutionTransportCertificate
  completeBilinears : V35CompleteBilinearCertificate
  bilinearClosure : V35BilinearCliffordClosureCertificate
  movingSpin : V35MovingSpinInvariantCertificate

theorem v35_complete_covariant_observables :
    V35CompleteCovariantObservableCertificate where
  framework := v35_framework_and_gap_lock
  prior := v34_complete_covariant_free_spinor
  antiparticleResidue := v35_antiparticle_residue_closure
  generatedTransformations := v35_generated_lorentz_transformations
  covariantSolutions := v35_covariant_solution_transport
  completeBilinears := v35_complete_bilinears
  bilinearClosure := v35_bilinear_clifford_closure
  movingSpin := v35_moving_spin_invariant

end LeanDirac.V2
