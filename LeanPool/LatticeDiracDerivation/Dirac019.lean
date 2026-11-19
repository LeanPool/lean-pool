/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac019.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac018

/-!
# DIRAC-019: finite positive-frequency packet transport

The preceding chain derives the first-order branch and its current one
momentum at a time.  This stage lifts those identities to an arbitrary finite
family of positive-frequency modes.  It is deliberately a momentum-space
transport theorem for the recurrence-derived continuum branch: it proves
norm-preserving branch evolution, the exact
density-weighted group-current law, a strict massive speed bound, and
convergence of the complete finite-packet infinitesimal generator.

It does not claim a spatially localized nonlinear electron, a finite-time
uniform PDE error estimate, or unrestricted live-chi evolution.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex Filter Topology

def continuumTransportVelocity
    (momentum : LatticeMomentum) (axis : Fin 3) : ℝ :=
  c19ContinuumSpeed ^ 2 * momentum axis / continuumModeFrequency momentum

def continuumTransportSpeedSq (momentum : LatticeMomentum) : ℝ :=
  ∑ axis, continuumTransportVelocity momentum axis ^ 2

theorem continuum_transport_speed_strictly_subluminal
    (momentum : LatticeMomentum) :
    continuumTransportSpeedSq momentum < c19ContinuumSpeed ^ 2 := by
  have hfrequency : 0 < continuumModeFrequency momentum :=
    continuum_mode_frequency_positive momentum
  have hfrequency_ne : continuumModeFrequency momentum ≠ 0 := ne_of_gt hfrequency
  have hfrequency_sq := continuum_mode_frequency_square momentum
  rw [c19_continuum_speed_square]
  unfold continuumTransportSpeedSq continuumTransportVelocity
  rw [c19_continuum_speed_square]
  simp [Fin.sum_univ_succ]
  unfold continuumModeSquare c19QuadraticSymbol chi0 at hfrequency_sq
  field_simp [hfrequency_ne]
  nlinarith [sq_nonneg (momentum 0), sq_nonneg (momentum 1),
    sq_nonneg (momentum 2)]

def recurrencePositivePhase (dt : ℝ) (momentum : LatticeMomentum) : ℂ :=
  (recurrenceBranchCos dt (continuumModeFrequency momentum) : ℂ) -
    Complex.I *
      (recurrenceBranchSin dt (continuumModeFrequency momentum) : ℂ)

theorem recurrence_positive_phase_normSq
    (dt : ℝ) (momentum : LatticeMomentum)
    (hstable : (dt * continuumModeFrequency momentum) ^ 2 ≤ 4) :
    Complex.normSq (recurrencePositivePhase dt momentum) = 1 := by
  rw [show Complex.normSq (recurrencePositivePhase dt momentum) =
      recurrenceBranchCos dt (continuumModeFrequency momentum) ^ 2 +
        recurrenceBranchSin dt (continuumModeFrequency momentum) ^ 2 by
    simp [recurrencePositivePhase, Complex.normSq, Complex.mul_re,
      Complex.mul_im]
    ring]
  exact recurrence_branch_circle dt (continuumModeFrequency momentum) hstable

structure PositiveFrequencyMode where
  momentum : LatticeMomentum
  amplitude : Cell4
  eigen : standardC19Hamiltonian (chi0 : ℂ) momentum amplitude =
    fun component => (continuumModeFrequency momentum : ℂ) *
      amplitude component

def cell4Basis0 : Cell4
  | 0 => 1
  | _ => 0

def canonicalPositiveAmplitude (momentum : LatticeMomentum) : Cell4 :=
  cell4LinearCombination 1 (continuumModeFrequency momentum : ℂ)
    (standardC19Hamiltonian (chi0 : ℂ) momentum cell4Basis0)
    cell4Basis0

theorem canonical_positive_amplitude_is_eigen
    (momentum : LatticeMomentum) :
    standardC19Hamiltonian (chi0 : ℂ) momentum
        (canonicalPositiveAmplitude momentum) =
      fun component => (continuumModeFrequency momentum : ℂ) *
        canonicalPositiveAmplitude momentum component := by
  unfold canonicalPositiveAmplitude
  rw [standard_c19_hamiltonian_linear_combination]
  rw [standard_c19_hamiltonian_square_is_frequency_square]
  funext component
  unfold cell4LinearCombination
  push_cast
  ring

def canonicalPositiveFrequencyMode
    (momentum : LatticeMomentum) : PositiveFrequencyMode where
  momentum := momentum
  amplitude := canonicalPositiveAmplitude momentum
  eigen := canonical_positive_amplitude_is_eigen momentum

theorem canonical_positive_amplitude_component_zero
    (momentum : LatticeMomentum) :
    canonicalPositiveAmplitude momentum 0 =
      (chi0 + continuumModeFrequency momentum : ℝ) := by
  simp [canonicalPositiveAmplitude, cell4LinearCombination, cell4Basis0,
    standardC19Hamiltonian, standardDiracHamiltonian, standardDiracSpatial,
    standardDiracBeta, standardDiracAlphaX, standardDiracAlphaY,
    standardDiracAlphaZ]

theorem canonical_positive_frequency_mode_nonzero
    (momentum : LatticeMomentum) :
    (canonicalPositiveFrequencyMode momentum).amplitude ≠ 0 := by
  intro hzero
  have hcomponent := congrFun hzero (0 : Fin 4)
  rw [show (canonicalPositiveFrequencyMode momentum).amplitude =
      canonicalPositiveAmplitude momentum by rfl,
    canonical_positive_amplitude_component_zero momentum] at hcomponent
  have hpositive : 0 < chi0 + continuumModeFrequency momentum := by
    have := continuum_mode_frequency_positive momentum
    norm_num [chi0]
    positivity
  have hne : ((chi0 + continuumModeFrequency momentum : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hpositive)
  exact hne hcomponent

theorem recurrence_step_on_positive_mode
    (dt : ℝ) (mode : PositiveFrequencyMode) :
    recurrenceDiracBranchStep dt mode.momentum mode.amplitude =
      fun component => recurrencePositivePhase dt mode.momentum *
        mode.amplitude component := by
  funext component
  have heigen := congrFun mode.eigen component
  have hfrequency : continuumModeFrequency mode.momentum ≠ 0 :=
    ne_of_gt (continuum_mode_frequency_positive mode.momentum)
  unfold recurrenceDiracBranchStep recurrencePositivePhase
    cell4LinearCombination
  rw [heigen]
  push_cast
  field_simp [hfrequency]
  ring

theorem standard_c19_hamiltonian_complex_scale
    (mass : ℂ) (momentum : LatticeMomentum) (scale : ℂ) (z : Cell4) :
    standardC19Hamiltonian mass momentum
        (fun component => scale * z component) =
      fun component => scale *
        standardC19Hamiltonian mass momentum z component := by
  calc
    standardC19Hamiltonian mass momentum
        (fun component => scale * z component) =
        standardC19Hamiltonian mass momentum
          (cell4LinearCombination scale 0 z (0 : Cell4)) := by
            congr 1
            funext component
            simp [cell4LinearCombination]
    _ = cell4LinearCombination scale 0
          (standardC19Hamiltonian mass momentum z)
          (standardC19Hamiltonian mass momentum (0 : Cell4)) :=
      standard_c19_hamiltonian_linear_combination mass momentum
        scale 0 z (0 : Cell4)
    _ = fun component => scale *
          standardC19Hamiltonian mass momentum z component := by
            funext component
            simp [cell4LinearCombination]

def positiveModeEvolution
    (dt : ℝ) (mode : PositiveFrequencyMode) (step : ℕ) : Cell4 :=
  fun component =>
    recurrencePositivePhase dt mode.momentum ^ step * mode.amplitude component

theorem positive_mode_evolution_is_eigen
    (dt : ℝ) (mode : PositiveFrequencyMode) (step : ℕ) :
    standardC19Hamiltonian (chi0 : ℂ) mode.momentum
        (positiveModeEvolution dt mode step) =
      fun component => (continuumModeFrequency mode.momentum : ℂ) *
        positiveModeEvolution dt mode step component := by
  rw [show positiveModeEvolution dt mode step =
      fun component => recurrencePositivePhase dt mode.momentum ^ step *
        mode.amplitude component by rfl]
  rw [standard_c19_hamiltonian_complex_scale, mode.eigen]
  funext component
  ring

theorem recurrence_step_advances_positive_mode_evolution
    (dt : ℝ) (mode : PositiveFrequencyMode) (step : ℕ) :
    recurrenceDiracBranchStep dt mode.momentum
        (positiveModeEvolution dt mode step) =
      positiveModeEvolution dt mode (step + 1) := by
  let evolvedMode : PositiveFrequencyMode :=
    { momentum := mode.momentum
      amplitude := positiveModeEvolution dt mode step
      eigen := positive_mode_evolution_is_eigen dt mode step }
  have hstep := recurrence_step_on_positive_mode dt evolvedMode
  rw [show evolvedMode.momentum = mode.momentum by rfl,
    show evolvedMode.amplitude = positiveModeEvolution dt mode step by rfl]
    at hstep
  rw [hstep]
  funext component
  unfold positiveModeEvolution
  rw [pow_succ]
  ring

theorem cell4_density_complex_scale
    (scale : ℂ) (z : Cell4) :
    cell4Density (fun component => scale * z component) =
      Complex.normSq scale * cell4Density z := by
  unfold cell4Density
  simp_rw [Complex.normSq_mul]
  rw [← Finset.mul_sum]

theorem positive_mode_step_preserves_density
    (dt : ℝ) (mode : PositiveFrequencyMode)
    (hstable : (dt * continuumModeFrequency mode.momentum) ^ 2 ≤ 4) :
    cell4Density
        (recurrenceDiracBranchStep dt mode.momentum mode.amplitude) =
      cell4Density mode.amplitude := by
  rw [recurrence_step_on_positive_mode]
  rw [cell4_density_complex_scale,
    recurrence_positive_phase_normSq dt mode.momentum hstable]
  simp

theorem recurrence_positive_phase_pow_normSq
    (dt : ℝ) (momentum : LatticeMomentum) (step : ℕ)
    (hstable : (dt * continuumModeFrequency momentum) ^ 2 ≤ 4) :
    Complex.normSq (recurrencePositivePhase dt momentum ^ step) = 1 := by
  induction step with
  | zero => simp
  | succ step ih =>
      rw [pow_succ, Complex.normSq_mul,
        recurrence_positive_phase_normSq dt momentum hstable, ih]
      norm_num

theorem positive_mode_evolution_preserves_density
    (dt : ℝ) (mode : PositiveFrequencyMode) (step : ℕ)
    (hstable : (dt * continuumModeFrequency mode.momentum) ^ 2 ≤ 4) :
    cell4Density (positiveModeEvolution dt mode step) =
      cell4Density mode.amplitude := by
  unfold positiveModeEvolution
  rw [cell4_density_complex_scale,
    recurrence_positive_phase_pow_normSq dt mode.momentum step hstable]
  simp

theorem positive_mode_evolution_current_is_initial_velocity_moment
    (dt : ℝ) (mode : PositiveFrequencyMode) (step : ℕ) (axis : Fin 3)
    (hstable : (dt * continuumModeFrequency mode.momentum) ^ 2 ≤ 4) :
    standardC19DiracCurrent axis (positiveModeEvolution dt mode step) =
      continuumTransportVelocity mode.momentum axis *
        cell4Density mode.amplitude := by
  rw [positive_frequency_dirac_current_is_group_velocity
    chi0 (continuumModeFrequency mode.momentum) mode.momentum axis
    (positiveModeEvolution dt mode step)
    (ne_of_gt (continuum_mode_frequency_positive mode.momentum))
    (positive_mode_evolution_is_eigen dt mode step)]
  rw [positive_mode_evolution_preserves_density dt mode step hstable]
  rfl

structure FinitePositivePacket (Mode : Type) [Fintype Mode] where
  mode : Mode → PositiveFrequencyMode

def finitePacketDensity {Mode : Type} [Fintype Mode]
    (packet : FinitePositivePacket Mode) : ℝ :=
  ∑ index, cell4Density (packet.mode index).amplitude

def finitePacketAdvancedDensity {Mode : Type} [Fintype Mode]
    (dt : ℝ) (packet : FinitePositivePacket Mode) : ℝ :=
  ∑ index, cell4Density
    (recurrenceDiracBranchStep dt (packet.mode index).momentum
      (packet.mode index).amplitude)

def finitePacketEvolvedDensity {Mode : Type} [Fintype Mode]
    (dt : ℝ) (packet : FinitePositivePacket Mode) (step : ℕ) : ℝ :=
  ∑ index, cell4Density (positiveModeEvolution dt (packet.mode index) step)

theorem finite_packet_step_preserves_density
    {Mode : Type} [Fintype Mode]
    (dt : ℝ) (packet : FinitePositivePacket Mode)
    (hstable : ∀ index,
      (dt * continuumModeFrequency (packet.mode index).momentum) ^ 2 ≤ 4) :
    finitePacketAdvancedDensity dt packet = finitePacketDensity packet := by
  unfold finitePacketAdvancedDensity finitePacketDensity
  apply Finset.sum_congr rfl
  intro index _
  exact positive_mode_step_preserves_density dt (packet.mode index)
    (hstable index)

theorem finite_packet_evolution_preserves_density
    {Mode : Type} [Fintype Mode]
    (dt : ℝ) (packet : FinitePositivePacket Mode) (step : ℕ)
    (hstable : ∀ index,
      (dt * continuumModeFrequency (packet.mode index).momentum) ^ 2 ≤ 4) :
    finitePacketEvolvedDensity dt packet step = finitePacketDensity packet := by
  unfold finitePacketEvolvedDensity finitePacketDensity
  apply Finset.sum_congr rfl
  intro index _
  exact positive_mode_evolution_preserves_density dt (packet.mode index) step
    (hstable index)

def finitePacketDiracCurrent {Mode : Type} [Fintype Mode]
    (axis : Fin 3) (packet : FinitePositivePacket Mode) : ℝ :=
  ∑ index, standardC19DiracCurrent axis (packet.mode index).amplitude

def finitePacketEvolvedDiracCurrent {Mode : Type} [Fintype Mode]
    (dt : ℝ) (axis : Fin 3) (packet : FinitePositivePacket Mode)
    (step : ℕ) : ℝ :=
  ∑ index, standardC19DiracCurrent axis
    (positiveModeEvolution dt (packet.mode index) step)

def finitePacketVelocityMoment {Mode : Type} [Fintype Mode]
    (axis : Fin 3) (packet : FinitePositivePacket Mode) : ℝ :=
  ∑ index,
    continuumTransportVelocity (packet.mode index).momentum axis *
      cell4Density (packet.mode index).amplitude

theorem finite_packet_current_is_density_weighted_velocity
    {Mode : Type} [Fintype Mode]
    (axis : Fin 3) (packet : FinitePositivePacket Mode) :
    finitePacketDiracCurrent axis packet =
      finitePacketVelocityMoment axis packet := by
  unfold finitePacketDiracCurrent finitePacketVelocityMoment
    continuumTransportVelocity
  apply Finset.sum_congr rfl
  intro index _
  exact positive_frequency_dirac_current_is_group_velocity
    chi0 (continuumModeFrequency (packet.mode index).momentum)
    (packet.mode index).momentum axis (packet.mode index).amplitude
    (ne_of_gt (continuum_mode_frequency_positive
      (packet.mode index).momentum)) (packet.mode index).eigen

theorem finite_packet_evolved_current_is_density_weighted_velocity
    {Mode : Type} [Fintype Mode]
    (dt : ℝ) (axis : Fin 3) (packet : FinitePositivePacket Mode)
    (step : ℕ)
    (hstable : ∀ index,
      (dt * continuumModeFrequency (packet.mode index).momentum) ^ 2 ≤ 4) :
    finitePacketEvolvedDiracCurrent dt axis packet step =
      finitePacketVelocityMoment axis packet := by
  unfold finitePacketEvolvedDiracCurrent finitePacketVelocityMoment
  apply Finset.sum_congr rfl
  intro index _
  exact positive_mode_evolution_current_is_initial_velocity_moment
    dt (packet.mode index) step axis (hstable index)

def finitePacketGeneratorDefect {Mode : Type} [Fintype Mode]
    (dt : ℝ) (packet : FinitePositivePacket Mode)
    (component : Fin 4) : ℂ :=
  ∑ index, recurrenceBranchGeneratorDefect dt
    (packet.mode index).momentum (packet.mode index).amplitude component

theorem finite_packet_generator_defect_tends_to_zero
    {Mode : Type} [Fintype Mode]
    (packet : FinitePositivePacket Mode) (component : Fin 4) :
    Tendsto
      (fun dt : ℝ => finitePacketGeneratorDefect dt packet component)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  unfold finitePacketGeneratorDefect
  have hterm : ∀ index ∈ (Finset.univ : Finset Mode),
      Tendsto
        (fun dt : ℝ => recurrenceBranchGeneratorDefect dt
          (packet.mode index).momentum (packet.mode index).amplitude component)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (0 : ℂ)) := by
    intro index _
    exact recurrence_branch_generator_defect_tends_to_zero
      (packet.mode index).momentum (packet.mode index).amplitude component
  simpa using
    (tendsto_finsetSum (Finset.univ : Finset Mode) hterm)

structure Dirac019FinitePacketTransportCertificate : Prop where
  priorChain : Dirac018NativeFactorizationClassificationCertificate
  nonzeroPositiveModeExistsAtEveryMomentum : ∀ momentum,
    (canonicalPositiveFrequencyMode momentum).amplitude ≠ 0
  massiveModesAreStrictlySubluminal : ∀ momentum,
    continuumTransportSpeedSq momentum < c19ContinuumSpeed ^ 2
  stableBranchStepPreservesEveryModeDensity : ∀ dt (mode : PositiveFrequencyMode),
    (dt * continuumModeFrequency mode.momentum) ^ 2 ≤ 4 →
      cell4Density
          (recurrenceDiracBranchStep dt mode.momentum mode.amplitude) =
        cell4Density mode.amplitude
  stableBranchStepPreservesPacketDensity :
    ∀ {Mode : Type} [Fintype Mode] dt
      (packet : FinitePositivePacket Mode),
      (∀ index,
        (dt * continuumModeFrequency (packet.mode index).momentum) ^ 2 ≤ 4) →
      finitePacketAdvancedDensity dt packet = finitePacketDensity packet
  stableBranchEvolutionPreservesPacketDensity :
    ∀ {Mode : Type} [Fintype Mode] dt
      (packet : FinitePositivePacket Mode) step,
      (∀ index,
        (dt * continuumModeFrequency (packet.mode index).momentum) ^ 2 ≤ 4) →
      finitePacketEvolvedDensity dt packet step = finitePacketDensity packet
  packetCurrentIsDensityWeightedGroupVelocity :
    ∀ {Mode : Type} [Fintype Mode] axis
      (packet : FinitePositivePacket Mode),
      finitePacketDiracCurrent axis packet =
        finitePacketVelocityMoment axis packet
  packetCurrentPersistsForEveryStableUpdate :
    ∀ {Mode : Type} [Fintype Mode] dt axis
      (packet : FinitePositivePacket Mode) step,
      (∀ index,
        (dt * continuumModeFrequency (packet.mode index).momentum) ^ 2 ≤ 4) →
      finitePacketEvolvedDiracCurrent dt axis packet step =
        finitePacketVelocityMoment axis packet
  finitePacketGeneratorConverges :
    ∀ {Mode : Type} [Fintype Mode]
      (packet : FinitePositivePacket Mode) component,
      Tendsto
        (fun dt : ℝ => finitePacketGeneratorDefect dt packet component)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0)

theorem dirac019_finite_packet_transport :
    Dirac019FinitePacketTransportCertificate where
  priorChain := dirac018_native_factorization_classification
  nonzeroPositiveModeExistsAtEveryMomentum :=
    canonical_positive_frequency_mode_nonzero
  massiveModesAreStrictlySubluminal :=
    continuum_transport_speed_strictly_subluminal
  stableBranchStepPreservesEveryModeDensity :=
    positive_mode_step_preserves_density
  stableBranchStepPreservesPacketDensity :=
    finite_packet_step_preserves_density
  stableBranchEvolutionPreservesPacketDensity :=
    finite_packet_evolution_preserves_density
  packetCurrentIsDensityWeightedGroupVelocity :=
    finite_packet_current_is_density_weighted_velocity
  packetCurrentPersistsForEveryStableUpdate :=
    finite_packet_evolved_current_is_density_weighted_velocity
  finitePacketGeneratorConverges :=
    finite_packet_generator_defect_tends_to_zero

end
end LeanDirac
