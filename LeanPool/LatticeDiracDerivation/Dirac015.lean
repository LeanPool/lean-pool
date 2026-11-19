/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac015.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac013

/-!
# DIRAC-015: final free-Dirac continuum theorem

This file packages the already-proved chain into one explicit theorem.  Its
central statement is the action-to-Klein--Gordon-to-Dirac relationship:

1. the native two-field action supplies the quadratic massive C19 wave
   symbol on the declared prepared background;
2. that exact symbol splits into a continuum Klein--Gordon symbol and the
   retained finite-lattice remainder;
3. the cubical four-component Hamiltonian squares to that same continuum
   Klein--Gordon symbol;
4. the centered recurrence itself supplies a first-order branch whose exact
   native defect is the retained spatial remainder and whose generator tends
   to the same Dirac Hamiltonian; and
5. the same action and embedding supply the admitted density/current limit.

This theorem is conditional on the declared prepared background and the
low-momentum, small-timestep hypotheses written in its residual field.  It
does not assert a localized electron, electromagnetic coupling, nonlinear
live-chi closure, uniqueness of the square root, or canonical LFM status.
-/

@[expose] public section

namespace LeanDirac

noncomputable section

structure LFMFreeDiracContinuumCertificate : Prop where
  completePriorChain : Dirac013Certificate
  actionRestrictionAndVariation : Dirac006ActionRestrictionCertificate
  kleinGordonTangentFromAction : ∀ eps amplitude momentum site,
    nativePreparedModalPotential eps amplitude momentum site =
      eps ^ 2 * Complex.normSq amplitude / 2 *
          nativePsiTangentSymbol momentum +
        eps ^ 4 * Complex.normSq amplitude ^ 2 / 4
  exactNativeSymbolSplits : ∀ momentum,
    nativePsiTangentSymbol momentum =
      chi0 ^ 2 + c19QuadraticSymbol momentum +
        c19SpatialRemainder momentum
  diracSquareIsContinuumKleinGordon : ∀ momentum z,
    standardC19Hamiltonian (chi0 : ℂ) momentum
        (standardC19Hamiltonian (chi0 : ℂ) momentum z) =
      fun component =>
        ((chi0 ^ 2 + c19QuadraticSymbol momentum : ℝ) : ℂ) * z component
  recurrenceDerivedFirstOrderBranch : Dirac012RecurrenceBranchCertificate
  nativeContinuityAndDiracCurrent : Dirac013Certificate

theorem lfm_free_dirac_continuum_limit :
    LFMFreeDiracContinuumCertificate where
  completePriorChain := dirac013_native_density_current_continuity
  actionRestrictionAndVariation := dirac006_action_restriction_bridge
  kleinGordonTangentFromAction := native_prepared_modal_potential_expansion
  exactNativeSymbolSplits := native_psi_tangent_symbol_is_exact_scalar_coefficient
  diracSquareIsContinuumKleinGordon :=
    standard_c19_hamiltonian_square_is_continuum_dispersion
  recurrenceDerivedFirstOrderBranch := dirac012_native_recurrence_branch
  nativeContinuityAndDiracCurrent :=
    dirac013_native_density_current_continuity

end
end LeanDirac
