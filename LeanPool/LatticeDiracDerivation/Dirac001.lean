/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac001.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.C19Geometry

/-!
DIRAC-001: explicit native-framework boundary.

This gate fixes the two native complex-C3 field families, the declared
constants, and the positive C19 neighborhood weights.  It makes no action,
prepared-background, spinor, electron, or Dirac claim.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

theorem dirac001_native_framework (state : State Site) :
    chi0 = 19 ∧
    kappa = 1 / 63 ∧
    chiKineticNormalization = 1197 ∧
    state = ⟨state.psi, state.chi⟩ ∧
    ∀ neighbor : C19Neighbor, 0 < c19Weight neighbor := by
  exact ⟨rfl, rfl, chi_kinetic_normalization_eq_1197,
    state_has_exactly_two_field_families state, c19_weight_positive⟩

end LeanDirac
