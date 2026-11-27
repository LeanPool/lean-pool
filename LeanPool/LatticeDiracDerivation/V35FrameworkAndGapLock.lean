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

public import LeanPool.LatticeDiracDerivation.V34CompleteCovariantFreeSpinor

/-!
# V3.5 Stage 1: framework and gap lock

V3.5 is a theorem-only extension of V3.4.  This certificate deliberately
records the inherited free-sector result before any new notation is added.
-/

@[expose] public section

namespace LeanDirac.V2

/-- Certificate that V3.5 inherits V3.4 and retains the native mass and C19
speed-square values. -/
structure V35FrameworkAndGapLockCertificate : Prop where
  prior : V34CompleteCovariantFreeSpinorCertificate
  nativeMass : chi0 = 19
  nativeSpeedSquare : c19ContinuumSpeed ^ 2 = 12

theorem v35_framework_and_gap_lock : V35FrameworkAndGapLockCertificate where
  prior := v34_complete_covariant_free_spinor
  nativeMass := v32_native_rest_mass_is_nineteen
  nativeSpeedSquare := c19_continuum_speed_square

end LeanDirac.V2
