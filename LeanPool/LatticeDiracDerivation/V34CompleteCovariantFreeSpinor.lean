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

public import LeanPool.LatticeDiracDerivation.V34SpinorSectorBasis
public import LeanPool.LatticeDiracDerivation.V34CovariantSpinSums
public import LeanPool.LatticeDiracDerivation.V34MomentumHelicity
public import LeanPool.LatticeDiracDerivation.V34NonforwardGordon
public import LeanPool.LatticeDiracDerivation.V34PropagatorResidues

/-!
# V3.4 Stage 7: complete covariant free-spinor closure

This certificate packages the cumulative V3.4 handoffs.  It extends, rather
than replaces, the V3.2 free-fermion and V3.3 free-spinor certificates.  The
scope remains the free linearized sector of the declared LFM action.
-/

@[expose] public section

namespace LeanDirac.V2

/-- Cumulative certificate for the V3.4 covariant free-spinor sector. -/
structure V34CompleteCovariantFreeSpinorCertificate : Prop where
  priorFreeSpinor : V33CompleteFreeSpinorCertificate
  covariantSpinors : V34CovariantSpinorCertificate
  sectorBasis : V34SpinorSectorBasisCertificate
  covariantSpinSums : V34CovariantSpinSumCertificate
  momentumHelicity : V34MomentumHelicityCertificate
  nonforwardGordon : V34NonforwardGordonCertificate
  propagatorResidues : V34PropagatorResidueCertificate

theorem v34_complete_covariant_free_spinor :
    V34CompleteCovariantFreeSpinorCertificate where
  priorFreeSpinor := v33_complete_free_spinor
  covariantSpinors := v34_covariant_spinors
  sectorBasis := v34_spinor_sector_basis
  covariantSpinSums := v34_covariant_spin_sums
  momentumHelicity := v34_momentum_helicity
  nonforwardGordon := v34_nonforward_gordon
  propagatorResidues := v34_propagator_residues

end LeanDirac.V2
