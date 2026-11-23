/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.CanonicalSpectralReadout
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumCurrentBridge

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

/-- The common mass of the two counterexample modes. -/
def packetScopeMass : ℝ := 3

/-- The common energy of the two counterexample modes. -/
def packetScopeEnergy : ℝ := 5

/-- The counterexample modes have opposite momenta along the third coordinate. -/
def packetScopeMomentum (mode : Fin 2) : LatticeMomentum := fun axis =>
  if axis = 2 then if mode = 0 then 4 else -4 else 0

/-- Positivity and the mass-shell condition for a mode used by the counterexample. -/
def packetScopeModePositiveOnShell (mode : Fin 2) : Prop :=
  0 < packetScopeEnergy ∧ 0 < packetScopeEnergy + packetScopeMass ∧
    packetScopeEnergy ^ 2 = packetScopeMass ^ 2 + (packetScopeMomentum mode 0) ^ 2 +
      (packetScopeMomentum mode 1) ^ 2 + (packetScopeMomentum mode 2) ^ 2

/-- Each mode in the pointwise counterexample is on the positive mass shell. -/
theorem packet_scope_modes_are_positive_on_shell (mode : Fin 2) :
    packetScopeModePositiveOnShell mode := by
  fin_cases mode <;> norm_num [packetScopeModePositiveOnShell, packetScopeMass,
    packetScopeEnergy, packetScopeMomentum]

/-- The positive-frequency native phase used in the two-mode counterexample. -/
def packetScopePositivePhase : UniformTwoChannelPhase :=
  uniformPositiveFrequencyPhase packetScopeEnergy packetScopeAmplitude

/-- The Dirac modes obtained by reading out the common native input. -/
def packetScopeDiracAtOrigin : CubicalCell4 :=
  ∑ mode : Fin 2, canonicalSpectralReadout packetScopeMass packetScopeEnergy
    (packetScopeMomentum mode 0) (packetScopeMomentum mode 1) (packetScopeMomentum mode 2)
    packetScopePositivePhase

/-- The sum of the native phases over the same modes at the origin. -/
def packetScopeNativeAtOrigin : UniformTwoChannelPhase :=
  ∑ _mode : Fin 2, packetScopePositivePhase

/-- Each summand reads out the native phase at its own momentum. -/
theorem packet_scope_dirac_field_uses_canonical_native_modes :
    packetScopeDiracAtOrigin = fun component =>
      ∑ mode : Fin 2, canonicalSpectralReadout packetScopeMass packetScopeEnergy
        (packetScopeMomentum mode 0) (packetScopeMomentum mode 1) (packetScopeMomentum mode 2)
        packetScopePositivePhase component := by
  funext component
  simp only [packetScopeDiracAtOrigin, Finset.sum_apply]

private theorem packet_scope_dirac_field_is_normalized_sum :
    packetScopeDiracAtOrigin =
      ∑ mode : Fin 2, normalizedPositiveFrequencyEmbedding packetScopeMass packetScopeEnergy
        (packetScopeMomentum mode 0) (packetScopeMomentum mode 1) (packetScopeMomentum mode 2)
        packetScopeAmplitude := by
  unfold packetScopeDiracAtOrigin
  apply Finset.sum_congr rfl
  intro mode _
  exact canonical_spectral_readout_uniform_positive packetScopeMass packetScopeEnergy
    (packetScopeMomentum mode 0) (packetScopeMomentum mode 1) (packetScopeMomentum mode 2)
    (ne_of_gt (packet_scope_modes_are_positive_on_shell mode).1) packetScopeAmplitude

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
  · norm_num [packet_scope_dirac_field_is_normalized_sum, packetScopeMass, packetScopeEnergy,
      packetScopeMomentum, Finset.sum_apply, Fin.sum_univ_two, packetScopeAmplitude,
      normalized_positive_frequency_embedding_apply, positiveFrequencyScale,
      positiveFrequencyRatio, positive_pauli_spatial_apply_zero, positive_pauli_spatial_apply_one,
      cubicalCell4Density, Complex.normSq, Fin.sum_univ_four]
  · norm_num [packetScopeNativeAtOrigin, packetScopePositivePhase, packetScopeEnergy,
      Fin.sum_univ_two, packetScopeAmplitude,
      uniformPositiveFrequencyPhase, uniformNativePhaseDensity,
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
