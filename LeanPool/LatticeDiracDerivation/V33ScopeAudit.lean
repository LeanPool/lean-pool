/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit 7b2a51cf933798eeb931731609fda0ffa81123fe.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V33FreePropagator

/-!
# V3.3 Stage 9: scope and provenance audit

This certificate keeps the new observable package tied to the unchanged V3.2
chain.  The exclusions documented in the release plan are claim restrictions,
not propositions manufactured inside Lean.
-/

@[expose] public section

namespace LeanDirac.V2

/-- Certificate recording the proved free-linearized scope and its explicit exclusions. -/
structure V33ScopeAuditCertificate : Prop where
  unchangedFramework : V33FrameworkLockCertificate
  inheritedFreeTheory : V32CompleteFreeFermionCertificate
  basis : V33SpinorBasisCertificate
  branches : V33ProjectedSpinorCertificate
  nativeMassOnly : chi0 = 19

theorem v33_scope_audit : V33ScopeAuditCertificate where
  unchangedFramework := v33_framework_lock
  inheritedFreeTheory := v32_complete_free_fermion
  basis := v33_spinor_basis
  branches := v33_projected_spinors
  nativeMassOnly := v32_native_rest_mass_is_nineteen

end LeanDirac.V2
