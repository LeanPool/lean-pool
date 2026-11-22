/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.CanonicalSpectralReadout

/-!
# Scope of the positive-frequency packet current bridge

The mode theorem identifies the normalized Dirac density with the native
positive-frequency U(1) density for one momentum mode.  This file records an
explicit two-mode counterexample to the corresponding *pointwise* statement
for arbitrary positive-energy packets.  The obstruction is an interference
cross term, not a negative-frequency contribution.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex BigOperators
noncomputable section

/-- A fixed two-component polarization used in the pointwise charge counterexample. -/
def packetScopeAmplitude : UniformCell2
  | 0 => 1
  | _ => 0

/-- The interfering Dirac modes evaluated at the origin of the counterexample. -/
def packetScopeDiracAtOrigin : CubicalCell4 :=
  fun component =>
    normalizedPositiveFrequencyEmbedding 3 5 0 0 4
        packetScopeAmplitude component +
      normalizedPositiveFrequencyEmbedding 3 5 0 0 (-4)
        packetScopeAmplitude component

/-- The positive-frequency native phase used in the two-mode counterexample. -/
def packetScopePositivePhase : UniformTwoChannelPhase :=
  nativePhaseOfFrequencyAmplitudes 5 packetScopeAmplitude (fun _ => 0)

/-- The sum of the native mode phases at the origin of the counterexample. -/
def packetScopeNativeAtOrigin : UniformTwoChannelPhase :=
  nativePhaseOfFrequencyAmplitudes 5
    (fun component => 2 * packetScopeAmplitude component)
    (fun _ => 0)

/-- Two positive-energy modes with mass `3`, energy `5`, and opposite
momenta `±4` are each on shell. -/
theorem packet_scope_modes_are_positive_on_shell :
    (0 : ℝ) < 5 + 3 ∧
      (5 : ℝ) ^ 2 = 3 ^ 2 + 4 ^ 2 + 0 ^ 2 + 0 ^ 2 ∧
      (5 : ℝ) ^ 2 = 3 ^ 2 + (-4) ^ 2 + 0 ^ 2 + 0 ^ 2 := by
  norm_num

/-- Both summands are obtained from the same native positive-frequency phase
by the canonical spectral readout; no spinor datum is inserted independently. -/
theorem packet_scope_dirac_field_uses_canonical_native_modes :
    packetScopeDiracAtOrigin = fun component =>
      canonicalSpectralReadout 3 5 0 0 4 packetScopePositivePhase component +
        canonicalSpectralReadout 3 5 0 0 (-4)
          packetScopePositivePhase component := by
  rw [show canonicalSpectralReadout 3 5 0 0 4 packetScopePositivePhase =
      normalizedPositiveFrequencyEmbedding 3 5 0 0 4
        packetScopeAmplitude by
    exact canonical_spectral_readout_positive_phase
      3 5 0 0 4 (by norm_num) packetScopeAmplitude]
  rw [show canonicalSpectralReadout 3 5 0 0 (-4) packetScopePositivePhase =
      normalizedPositiveFrequencyEmbedding 3 5 0 0 (-4)
        packetScopeAmplitude by
    exact canonical_spectral_readout_positive_phase
      3 5 0 0 (-4) (by norm_num) packetScopeAmplitude]
  rfl

/-- At the origin the two positive-energy modes have native U(1) density
`20`, while the density of the sum of their canonically normalized Dirac
images is `16`.  Hence the single-mode same-state theorem cannot be promoted
to a pointwise arbitrary-packet identity without adding the missing bilinear
interference kernel. -/
theorem positive_packet_pointwise_native_density_is_not_dirac_density :
    cubicalCell4Density packetScopeDiracAtOrigin = 16 ∧
      -uniformNativePhaseDensity packetScopeNativeAtOrigin.1
          packetScopeNativeAtOrigin.2 = 20 := by
  constructor
  · norm_num [packetScopeDiracAtOrigin, packetScopeAmplitude,
      normalizedPositiveFrequencyEmbedding, positiveFrequencyScale,
      positiveFrequencyRatio, positivePauliSpatial,
      cubicalCell4Density, Complex.normSq, Fin.sum_univ_four]
  · norm_num [packetScopeNativeAtOrigin, packetScopeAmplitude,
      nativePhaseOfFrequencyAmplitudes, uniformNativePhaseDensity,
      uniformScalarPhasePair, uniformCell2Density,
      Complex.mul_im, Fin.sum_univ_succ]

theorem positive_packet_pointwise_bridge_is_false :
    cubicalCell4Density packetScopeDiracAtOrigin ≠
      -uniformNativePhaseDensity packetScopeNativeAtOrigin.1
        packetScopeNativeAtOrigin.2 := by
  intro heq
  have h := positive_packet_pointwise_native_density_is_not_dirac_density
  rw [h.1, h.2] at heq
  norm_num at heq

end
end LeanDirac.V2
