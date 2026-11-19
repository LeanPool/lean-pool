/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac009Closed.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac009Geometry

/-!
# DIRAC-009: descaffolded continuum Clifford gate

The native law remains the positive two-field C19 action admitted in
DIRAC-002 and evolved through DIRAC-008. The cubical Clifford operators are
introduced only as a square-root readout of its isotropic low-momentum symbol.
The exact finite-lattice mismatch is retained with an explicit fourth-order
bound. No signed-incidence, shape-holding, or Dirac transport energy is added
to the action.
-/

@[expose] public section

namespace LeanDirac

/-- The DIRAC-009 statement bundle: the DIRAC-002 certificate, the DIRAC-008 certificate for
every nonzero timestep `dt`, and `Dirac009NecessaryGeometry`. -/
structure Dirac009ClosedCertificate : Prop where
  candidateAction : Dirac002Certificate
  throughFirstOrderMap : ∀ (dt : ℝ) (hdt : dt ≠ 0),
    Dirac008Certificate dt hdt
  geometry : Dirac009NecessaryGeometry

theorem dirac009_closed_native_clifford :
    Dirac009ClosedCertificate where
  candidateAction := dirac002_candidate_action_and_geometry
  throughFirstOrderMap := dirac008_complete_native_first_order_map
  geometry := dirac009_necessary_cube_geometry

end LeanDirac
