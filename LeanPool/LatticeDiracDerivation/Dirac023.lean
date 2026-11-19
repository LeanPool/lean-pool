/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac023.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac022

/-!
# DIRAC-023: phase harmony and transport-clock dilation

The preceding chain independently supplies three ingredients: the continuum
mode frequency from the native C19 quadratic symbol, the current velocity
from the Hamiltonian momentum response, and the action-selected rest clock.
This stage combines them without changing the action or introducing a new
speed, mass, clock, or phase rule.

For a plane-wave phase `p.x - E t`, following the packet at the already-proved
transport velocity changes the phase at rate `E - p.v`.  Lean proves that
this rate is `chi0 ^ 2 / E`.  Relative to the rest rate `chi0`, its square is
exactly `1 - |v| ^ 2 / c_eff ^ 2`; equivalently, the energy ratio and clock-rate
ratio are reciprocal.  For every nonzero momentum component, the corresponding
group and phase velocities multiply to `c_eff ^ 2`.

These are continuum-sector consequences of the existing C19 dispersion and
current theorems.  They do not assert an exact finite-spacing identity, an SI
calibration, a localized nonlinear electron, or unrestricted live-chi motion.
-/

@[expose] public section

namespace LeanDirac

noncomputable section

/-! The phase velocity seen along one coordinate direction.  This is defined
only as an algebraic value here; the reciprocity theorem below requires the
selected momentum component to be nonzero. -/
/-- The phase velocity along `axis`, the quotient of `continuumModeFrequency momentum` by the
momentum component `momentum axis`. -/
def continuumDirectionalPhaseVelocity
    (momentum : LatticeMomentum) (axis : Fin 3) : ℝ :=
  continuumModeFrequency momentum / momentum axis

/-! A one-direction slice of the continuum plane-wave phase `p*x - E*t`.
This gives the phase-velocity definition an operational test: moving at that
speed must keep the phase fixed. -/
/-- The plane-wave phase `p * x - E * t` restricted to one coordinate direction, with
`p = momentum axis`, `x = position`, `t = time` and `E = continuumModeFrequency momentum`. -/
def continuumDirectionalPlanePhase
    (momentum : LatticeMomentum) (axis : Fin 3)
    (position time : ℝ) : ℝ :=
  momentum axis * position - continuumModeFrequency momentum * time

theorem directional_phase_velocity_keeps_plane_phase_fixed
    (momentum : LatticeMomentum) (axis : Fin 3)
    (time : ℝ) (hmomentum : momentum axis ≠ 0) :
    continuumDirectionalPlanePhase momentum axis
        (continuumDirectionalPhaseVelocity momentum axis * time) time = 0 := by
  unfold continuumDirectionalPlanePhase continuumDirectionalPhaseVelocity
  field_simp [hmomentum]
  ring

/-! Rate of the plane-wave phase along the packet center `x(t) = v t`, where
`v` is the current-derived transport velocity from DIRAC-013/019. -/
/-- The rate `E - p · v` of the plane-wave phase along the moving center, where
`E = continuumModeFrequency momentum` and `v = continuumTransportVelocity momentum`. -/
def continuumTransportPhaseRate (momentum : LatticeMomentum) : ℝ :=
  continuumModeFrequency momentum -
    ∑ axis, momentum axis * continuumTransportVelocity momentum axis

/-! The complete three-direction plane-wave phase evaluated on the packet
center moving with the independently derived transport velocity. -/
/-- The three-dimensional plane-wave phase `p · x - E * t` evaluated at `x = v * time`, where
`v = continuumTransportVelocity momentum` and `E = continuumModeFrequency momentum`. -/
def continuumPlanePhaseAlongTransport
    (momentum : LatticeMomentum) (time : ℝ) : ℝ :=
  (∑ axis,
      momentum axis * (continuumTransportVelocity momentum axis * time)) -
    continuumModeFrequency momentum * time

theorem plane_phase_along_transport_is_accumulated_clock
    (momentum : LatticeMomentum) (time : ℝ) :
    continuumPlanePhaseAlongTransport momentum time =
      -continuumTransportPhaseRate momentum * time := by
  unfold continuumPlanePhaseAlongTransport continuumTransportPhaseRate
  simp [Fin.sum_univ_succ]
  ring

/-! Dimensionless clock-rate ratio, derived from the phase accumulated along
the packet center and normalized only by the action-selected rest clock. -/
/-- The ratio of `continuumTransportPhaseRate momentum` to `nativeRestAngularFrequency`. -/
def continuumTransportClockRatio (momentum : LatticeMomentum) : ℝ :=
  continuumTransportPhaseRate momentum / nativeRestAngularFrequency

/-! Dimensionless energy ratio relative to the same action-selected rest
frequency.  The theorem below proves that it is reciprocal to the clock ratio;
that reciprocity is not assumed in either definition. -/
/-- The ratio of `continuumModeFrequency momentum` to `nativeRestAngularFrequency`. -/
def continuumEnergyRatio (momentum : LatticeMomentum) : ℝ :=
  continuumModeFrequency momentum / nativeRestAngularFrequency

theorem directional_group_phase_velocity_reciprocity
    (momentum : LatticeMomentum) (axis : Fin 3)
    (hmomentum : momentum axis ≠ 0) :
    continuumTransportVelocity momentum axis *
        continuumDirectionalPhaseVelocity momentum axis =
      c19ContinuumSpeed ^ 2 := by
  have hfrequency : continuumModeFrequency momentum ≠ 0 :=
    ne_of_gt (continuum_mode_frequency_positive momentum)
  unfold continuumTransportVelocity continuumDirectionalPhaseVelocity
  field_simp [hmomentum, hfrequency]

theorem continuum_transport_phase_rate_is_mass_square_over_energy
    (momentum : LatticeMomentum) :
    continuumTransportPhaseRate momentum =
      chi0 ^ 2 / continuumModeFrequency momentum := by
  have hfrequency : continuumModeFrequency momentum ≠ 0 :=
    ne_of_gt (continuum_mode_frequency_positive momentum)
  have hfrequency_sq := continuum_mode_frequency_square momentum
  unfold continuumTransportPhaseRate continuumTransportVelocity
  rw [c19_continuum_speed_square]
  simp [Fin.sum_univ_succ]
  unfold continuumModeSquare c19QuadraticSymbol at hfrequency_sq
  field_simp [hfrequency]
  nlinarith

theorem continuum_transport_clock_ratio_is_mass_over_energy
    (momentum : LatticeMomentum) :
    continuumTransportClockRatio momentum =
      chi0 / continuumModeFrequency momentum := by
  rw [continuumTransportClockRatio,
    continuum_transport_phase_rate_is_mass_square_over_energy]
  rw [nativeRestAngularFrequency, continuum_rest_frequency_is_chi0]
  have hchi : chi0 ≠ 0 := by norm_num [chi0]
  field_simp [hchi]

theorem continuum_energy_clock_reciprocity
    (momentum : LatticeMomentum) :
    continuumEnergyRatio momentum *
        continuumTransportClockRatio momentum = 1 := by
  rw [continuumEnergyRatio,
    continuum_transport_clock_ratio_is_mass_over_energy]
  rw [nativeRestAngularFrequency, continuum_rest_frequency_is_chi0]
  have hchi : chi0 ≠ 0 := by norm_num [chi0]
  have hfrequency : continuumModeFrequency momentum ≠ 0 :=
    ne_of_gt (continuum_mode_frequency_positive momentum)
  field_simp [hchi, hfrequency]

theorem continuum_clock_ratio_square_is_speed_factor
    (momentum : LatticeMomentum) :
    continuumTransportClockRatio momentum ^ 2 =
      1 - continuumTransportSpeedSq momentum / c19ContinuumSpeed ^ 2 := by
  have hfrequency : continuumModeFrequency momentum ≠ 0 :=
    ne_of_gt (continuum_mode_frequency_positive momentum)
  have hspeed : c19ContinuumSpeed ^ 2 ≠ 0 := by
    rw [c19_continuum_speed_square]
    norm_num
  have hfrequency_sq := continuum_mode_frequency_square momentum
  rw [continuum_transport_clock_ratio_is_mass_over_energy]
  unfold continuumTransportSpeedSq continuumTransportVelocity
  rw [c19_continuum_speed_square]
  simp [Fin.sum_univ_succ]
  unfold continuumModeSquare c19QuadraticSymbol at hfrequency_sq
  field_simp [hfrequency, hspeed]
  nlinarith

theorem continuum_transport_clock_ratio_positive
    (momentum : LatticeMomentum) :
    0 < continuumTransportClockRatio momentum := by
  rw [continuum_transport_clock_ratio_is_mass_over_energy]
  have hchi : 0 < chi0 := by norm_num [chi0]
  exact div_pos hchi (continuum_mode_frequency_positive momentum)

theorem continuum_clock_ratio_is_sqrt_speed_factor
    (momentum : LatticeMomentum) :
    continuumTransportClockRatio momentum =
      Real.sqrt
        (1 - continuumTransportSpeedSq momentum / c19ContinuumSpeed ^ 2) := by
  rw [← continuum_clock_ratio_square_is_speed_factor]
  symm
  exact Real.sqrt_sq (le_of_lt
    (continuum_transport_clock_ratio_positive momentum))

theorem continuum_transport_phase_rate_is_rest_clock_times_speed_factor
    (momentum : LatticeMomentum) :
    (continuumTransportPhaseRate momentum /
        nativeRestAngularFrequency) ^ 2 =
      1 - continuumTransportSpeedSq momentum / c19ContinuumSpeed ^ 2 := by
  exact continuum_clock_ratio_square_is_speed_factor momentum

theorem continuum_transport_phase_rate_at_rest :
    continuumTransportPhaseRate zeroLatticeMomentum =
      nativeRestAngularFrequency := by
  rw [continuum_transport_phase_rate_is_mass_square_over_energy,
    continuum_rest_frequency_is_chi0, nativeRestAngularFrequency,
    continuum_rest_frequency_is_chi0]
  norm_num [chi0]

theorem continuum_transport_clock_ratio_at_rest :
    continuumTransportClockRatio zeroLatticeMomentum = 1 := by
  rw [continuum_transport_clock_ratio_is_mass_over_energy,
    continuum_rest_frequency_is_chi0]
  norm_num [chi0]

/-! DIRAC-022 already contained this exact identity; carrying it in the
certificate makes the previously buried scale lock explicit next to the new
phase-harmony result. -/
theorem zitter_scale_lock_is_emergent_speed :
    nativeZitterAmplitude * nativeZitterAngularFrequency =
      c19ContinuumSpeed :=
  native_zitter_amplitude_times_frequency

/-- The collected phase identities: group and phase velocities multiply to
`c19ContinuumSpeed ^ 2`, the phase rate along the moving center is `chi0 ^ 2 / E`, the energy and
clock ratios are reciprocal, and the clock ratio is `√(1 - |v| ^ 2 / c19ContinuumSpeed ^ 2)`. -/
structure Dirac023PhaseHarmonyCertificate : Prop where
  previousGate : Dirac022ZitterbewegungCertificate
  phaseVelocityHasOperationalMeaning :
    ∀ momentum axis time, momentum axis ≠ 0 →
      continuumDirectionalPlanePhase momentum axis
          (continuumDirectionalPhaseVelocity momentum axis * time) time = 0
  directionalGroupPhaseReciprocity :
    ∀ momentum axis, momentum axis ≠ 0 →
      continuumTransportVelocity momentum axis *
          continuumDirectionalPhaseVelocity momentum axis =
        c19ContinuumSpeed ^ 2
  packetCenterPhaseRate : ∀ momentum,
    continuumTransportPhaseRate momentum =
      chi0 ^ 2 / continuumModeFrequency momentum
  packetCenterPhaseAccumulation : ∀ momentum time,
    continuumPlanePhaseAlongTransport momentum time =
      -continuumTransportPhaseRate momentum * time
  energyClockReciprocity : ∀ momentum,
    continuumEnergyRatio momentum *
        continuumTransportClockRatio momentum = 1
  relativisticClockFactor : ∀ momentum,
    continuumTransportClockRatio momentum =
      Real.sqrt
        (1 - continuumTransportSpeedSq momentum / c19ContinuumSpeed ^ 2)
  restControl :
    continuumTransportPhaseRate zeroLatticeMomentum =
        nativeRestAngularFrequency ∧
      continuumTransportClockRatio zeroLatticeMomentum = 1
  inheritedZitterScaleLock :
    nativeZitterAmplitude * nativeZitterAngularFrequency =
      c19ContinuumSpeed

theorem dirac023_phase_harmony_and_time_dilation :
    Dirac023PhaseHarmonyCertificate where
  previousGate := dirac022_action_derived_zitterbewegung
  phaseVelocityHasOperationalMeaning :=
    directional_phase_velocity_keeps_plane_phase_fixed
  directionalGroupPhaseReciprocity :=
    directional_group_phase_velocity_reciprocity
  packetCenterPhaseRate :=
    continuum_transport_phase_rate_is_mass_square_over_energy
  packetCenterPhaseAccumulation :=
    plane_phase_along_transport_is_accumulated_clock
  energyClockReciprocity := continuum_energy_clock_reciprocity
  relativisticClockFactor := continuum_clock_ratio_is_sqrt_speed_factor
  restControl :=
    ⟨continuum_transport_phase_rate_at_rest,
      continuum_transport_clock_ratio_at_rest⟩
  inheritedZitterScaleLock := zitter_scale_lock_is_emergent_speed

end
end LeanDirac
