/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.C19Fourier
public import LeanPool.LatticeDiracDerivation.V2.CanonicalSpectralReadout

/-! # Canonical spinor readout at a C19 lattice momentum -/

@[expose] public section

namespace LeanDirac.V2

noncomputable section

/-- Spectral spinor coordinates with the momentum scaled by the C19 continuum speed. -/
def canonicalSpectralMomentumReadout
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (phase : UniformTwoChannelPhase) : CubicalCell4 :=
  canonicalSpectralReadout mass energy
    (c19ScaledMomentum momentum 0)
    (c19ScaledMomentum momentum 1)
    (c19ScaledMomentum momentum 2) phase

theorem canonical_spectral_momentum_readout_additive
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (first second : UniformTwoChannelPhase) :
    canonicalSpectralMomentumReadout mass energy momentum
        (fun component => first.1 component + second.1 component,
         fun component => first.2 component + second.2 component) =
      fun component =>
        canonicalSpectralMomentumReadout mass energy momentum first component +
          canonicalSpectralMomentumReadout mass energy momentum second component := by
  unfold canonicalSpectralMomentumReadout
  exact canonical_spectral_readout_additive _ _ _ _ _ first second

theorem canonical_spectral_momentum_readout_positive_phase
    (mass energy : ℝ) (momentum : LatticeMomentum) (henergy : energy ≠ 0) (q : UniformCell2) :
    canonicalSpectralMomentumReadout mass energy momentum
        (nativePhaseOfFrequencyAmplitudes energy q (fun _ => 0)) =
      normalizedPositiveFrequencyEmbedding mass energy
        (c19ScaledMomentum momentum 0) (c19ScaledMomentum momentum 1)
        (c19ScaledMomentum momentum 2) q :=
  canonical_spectral_readout_positive_phase _ _ _ _ _ henergy q

end
end LeanDirac.V2
