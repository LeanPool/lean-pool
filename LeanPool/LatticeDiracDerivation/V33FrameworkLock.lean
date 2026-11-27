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

public import LeanPool.LatticeDiracDerivation.V32CompleteFreeFermion

/-!
# V3.3 Stage 1: cumulative framework lock

V3.3 is a theorem-only continuation of V3.2.  No native dynamics are changed.
-/

@[expose] public section

namespace LeanDirac.V2

/-- Certificate that V3.3 retains the accepted action and framework constants. -/
structure V33FrameworkLockCertificate : Prop where
  prior : V32CompleteFreeFermionCertificate
  framework : V32FrameworkLockCertificate
  nativeMass : chi0 = 19

theorem v33_framework_lock : V33FrameworkLockCertificate where
  prior := v32_complete_free_fermion
  framework := v32_framework_lock
  nativeMass := v32_native_rest_mass_is_nineteen

end LeanDirac.V2
