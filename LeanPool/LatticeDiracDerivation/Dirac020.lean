/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac020.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac019
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

/-!
# DIRAC-020: coherent finite real-space Fourier transport

DIRAC-019 proved sustained transport for finite positive-frequency spectral
families.  This gate constructs a single coherent spatial field from those
modes.  The spatial frame is not assumed informally: an explicit normalized
finite Fourier frame is constructed from characters of every finite abelian
periodic lattice, and its orthonormality is proved from character
orthogonality.

The resulting four-component field obeys exact Parseval density preservation,
its integrated action-derived current is the density-weighted transport
velocity already proved in DIRAC-019, and a nonzero velocity moment therefore
gives nonzero spatial current at every stable update.  A separate theorem
bounds the finite-update recurrence error against exact continuum phase
evolution by the accumulated one-step phase mismatch.

This remains a linear continuum-branch result.  It does not claim exact native
finite-spacing factorization, a localized nonlinear electron, unrestricted
live-chi transport, or a uniform fixed-physical-time convergence rate.
-/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section
open Complex

structure FiniteSpatialFrame (Mode Site : Type) [Fintype Mode] [Fintype Site]
    [DecidableEq Mode] where
  basis : Mode → Site → ℂ
  orthonormal : ∀ first second,
    (∑ site, starRingEnd ℂ (basis first site) * basis second site) =
      if first = second then 1 else 0

def scalarSpatialSynthesis
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site) (amplitude : Mode → ℂ)
    (site : Site) : ℂ :=
  ∑ mode, frame.basis mode site * amplitude mode

theorem star_scalar_spatial_synthesis
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site) (amplitude : Mode → ℂ)
    (site : Site) :
    starRingEnd ℂ (scalarSpatialSynthesis frame amplitude site) =
      ∑ mode, starRingEnd ℂ (amplitude mode) *
        starRingEnd ℂ (frame.basis mode site) := by
  unfold scalarSpatialSynthesis
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro mode _
  rw [map_mul]
  ring

theorem scalar_spatial_synthesis_inner
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site) (a b : Mode → ℂ) :
    (∑ site, starRingEnd ℂ (scalarSpatialSynthesis frame a site) *
      scalarSpatialSynthesis frame b site) =
    ∑ mode, starRingEnd ℂ (a mode) * b mode := by
  simp_rw [star_scalar_spatial_synthesis]
  unfold scalarSpatialSynthesis
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.sum_comm]
  calc
    (∑ second, ∑ site,
      (starRingEnd ℂ (a first) * starRingEnd ℂ (frame.basis first site)) *
        (frame.basis second site * b second)) =
        ∑ second, (starRingEnd ℂ (a first) * b second) *
          ∑ site, starRingEnd ℂ (frame.basis first site) *
            frame.basis second site := by
      apply Finset.sum_congr rfl
      intro second _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro site _
      ring
    _ = starRingEnd ℂ (a first) * b first := by
      simp [frame.orthonormal]

theorem scalar_spatial_synthesis_parseval
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site) (a : Mode → ℂ) :
    (∑ site, Complex.normSq (scalarSpatialSynthesis frame a site)) =
      ∑ mode, Complex.normSq (a mode) := by
  have h := scalar_spatial_synthesis_inner frame a a
  have hre := congrArg Complex.re h
  simpa [Complex.mul_conj, mul_comm] using hre

theorem scalar_spatial_synthesis_real_pair
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site) (a b : Mode → ℂ) :
    (∑ site, scalarRealPair (scalarSpatialSynthesis frame a site)
      (scalarSpatialSynthesis frame b site)) =
      ∑ mode, scalarRealPair (a mode) (b mode) := by
  have h := scalar_spatial_synthesis_inner frame a b
  have hre := congrArg Complex.re h
  simpa [scalarRealPair] using hre

def cell4SpatialSynthesis
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site) (amplitude : Mode → Cell4)
    (site : Site) : Cell4 :=
  fun component => scalarSpatialSynthesis frame
    (fun mode => amplitude mode component) site

theorem cell4_spatial_synthesis_real_pair
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site) (a b : Mode → Cell4) :
    (∑ site, cell4RealPair (cell4SpatialSynthesis frame a site)
      (cell4SpatialSynthesis frame b site)) =
      ∑ mode, cell4RealPair (a mode) (b mode) := by
  unfold cell4RealPair cell4SpatialSynthesis
  calc
    (∑ site, ∑ component,
      scalarRealPair
        (scalarSpatialSynthesis frame (fun mode => a mode component) site)
        (scalarSpatialSynthesis frame (fun mode => b mode component) site)) =
        ∑ component, ∑ site,
          scalarRealPair
            (scalarSpatialSynthesis frame (fun mode => a mode component) site)
            (scalarSpatialSynthesis frame (fun mode => b mode component) site) :=
      Finset.sum_comm
    _ = ∑ component, ∑ mode,
        scalarRealPair (a mode component) (b mode component) := by
      apply Finset.sum_congr rfl
      intro component _
      exact scalar_spatial_synthesis_real_pair frame
        (fun mode => a mode component) (fun mode => b mode component)
    _ = ∑ mode, ∑ component,
        scalarRealPair (a mode component) (b mode component) :=
      Finset.sum_comm

theorem cell4_spatial_synthesis_parseval
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site) (amplitude : Mode → Cell4) :
    (∑ site, cell4Density (cell4SpatialSynthesis frame amplitude site)) =
      ∑ mode, cell4Density (amplitude mode) := by
  simp_rw [← cell4_density_is_real_pair_self]
  exact cell4_spatial_synthesis_real_pair frame amplitude amplitude

theorem standard_c19_velocity_spatial_synthesis
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site) (amplitude : Mode → Cell4)
    (site : Site) (axis : Fin 3) :
    standardC19VelocityOperator axis
        (cell4SpatialSynthesis frame amplitude site) =
      cell4SpatialSynthesis frame
        (fun mode => standardC19VelocityOperator axis (amplitude mode)) site := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [cell4SpatialSynthesis, scalarSpatialSynthesis,
      standardC19VelocityOperator, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]

theorem cell4_spatial_synthesis_current_parseval
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site) (amplitude : Mode → Cell4)
    (axis : Fin 3) :
    (∑ site, standardC19DiracCurrent axis
      (cell4SpatialSynthesis frame amplitude site)) =
      ∑ mode, standardC19DiracCurrent axis (amplitude mode) := by
  unfold standardC19DiracCurrent
  simp_rw [standard_c19_velocity_spatial_synthesis]
  exact cell4_spatial_synthesis_real_pair frame amplitude
    (fun mode => standardC19VelocityOperator axis (amplitude mode))

def coherentSpatialPacket
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site)
    (packet : FinitePositivePacket Mode) (dt : ℝ) (step : ℕ)
    (site : Site) : Cell4 :=
  cell4SpatialSynthesis frame
    (fun mode => positiveModeEvolution dt (packet.mode mode) step) site

def coherentSpatialPacketDensity
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site)
    (packet : FinitePositivePacket Mode) (dt : ℝ) (step : ℕ) : ℝ :=
  ∑ site, cell4Density (coherentSpatialPacket frame packet dt step site)

def coherentSpatialPacketCurrent
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site)
    (packet : FinitePositivePacket Mode) (dt : ℝ) (step : ℕ)
    (axis : Fin 3) : ℝ :=
  ∑ site, standardC19DiracCurrent axis
    (coherentSpatialPacket frame packet dt step site)

theorem coherent_spatial_packet_density_is_spectral_density
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site)
    (packet : FinitePositivePacket Mode) (dt : ℝ) (step : ℕ) :
    coherentSpatialPacketDensity frame packet dt step =
      finitePacketEvolvedDensity dt packet step := by
  unfold coherentSpatialPacketDensity coherentSpatialPacket
    finitePacketEvolvedDensity
  exact cell4_spatial_synthesis_parseval frame
    (fun mode => positiveModeEvolution dt (packet.mode mode) step)

theorem coherent_spatial_packet_density_is_preserved
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site)
    (packet : FinitePositivePacket Mode) (dt : ℝ) (step : ℕ)
    (hstable : ∀ index,
      (dt * continuumModeFrequency (packet.mode index).momentum) ^ 2 ≤ 4) :
    coherentSpatialPacketDensity frame packet dt step =
      finitePacketDensity packet := by
  rw [coherent_spatial_packet_density_is_spectral_density]
  exact finite_packet_evolution_preserves_density dt packet step hstable

theorem coherent_spatial_packet_current_is_velocity_moment
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site)
    (packet : FinitePositivePacket Mode) (dt : ℝ) (step : ℕ)
    (axis : Fin 3)
    (hstable : ∀ index,
      (dt * continuumModeFrequency (packet.mode index).momentum) ^ 2 ≤ 4) :
    coherentSpatialPacketCurrent frame packet dt step axis =
      finitePacketVelocityMoment axis packet := by
  unfold coherentSpatialPacketCurrent coherentSpatialPacket
  rw [cell4_spatial_synthesis_current_parseval]
  exact finite_packet_evolved_current_is_density_weighted_velocity
    dt axis packet step hstable

theorem coherent_spatial_packet_has_nonzero_transport
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site)
    (packet : FinitePositivePacket Mode) (dt : ℝ) (step : ℕ)
    (axis : Fin 3)
    (hstable : ∀ index,
      (dt * continuumModeFrequency (packet.mode index).momentum) ^ 2 ≤ 4)
    (hmoving : finitePacketVelocityMoment axis packet ≠ 0) :
    coherentSpatialPacketCurrent frame packet dt step axis ≠ 0 := by
  rw [coherent_spatial_packet_current_is_velocity_moment
    frame packet dt step axis hstable]
  exact hmoving

def exactContinuumPositivePhase (dt : ℝ) (momentum : LatticeMomentum) : ℂ :=
  Complex.exp (-Complex.I *
    ((dt * continuumModeFrequency momentum : ℝ) : ℂ))

theorem exact_continuum_positive_phase_norm
    (dt : ℝ) (momentum : LatticeMomentum) :
    ‖exactContinuumPositivePhase dt momentum‖ = 1 := by
  unfold exactContinuumPositivePhase
  rw [Complex.norm_exp]
  simp

theorem recurrence_positive_phase_norm
    (dt : ℝ) (momentum : LatticeMomentum)
    (hstable : (dt * continuumModeFrequency momentum) ^ 2 ≤ 4) :
    ‖recurrencePositivePhase dt momentum‖ = 1 := by
  have hs := recurrence_positive_phase_normSq dt momentum hstable
  rw [← Complex.sq_norm] at hs
  nlinarith [norm_nonneg (recurrencePositivePhase dt momentum)]

theorem complex_unit_phase_power_error
    (first second : ℂ) (step : ℕ)
    (hfirst : ‖first‖ = 1) (hsecond : ‖second‖ = 1) :
    ‖first ^ step - second ^ step‖ ≤
      (step : ℝ) * ‖first - second‖ := by
  induction step with
  | zero => simp
  | succ step ih =>
      rw [pow_succ, pow_succ]
      rw [show first ^ step * first - second ^ step * second =
          first ^ step * (first - second) +
            (first ^ step - second ^ step) * second by ring]
      calc
        ‖first ^ step * (first - second) +
            (first ^ step - second ^ step) * second‖ ≤
            ‖first ^ step * (first - second)‖ +
              ‖(first ^ step - second ^ step) * second‖ := norm_add_le _ _
        _ = ‖first - second‖ + ‖first ^ step - second ^ step‖ := by
          simp [norm_pow, hfirst, hsecond]
        _ ≤ ‖first - second‖ +
            (step : ℝ) * ‖first - second‖ := by gcongr
        _ = (Nat.succ step : ℝ) * ‖first - second‖ := by
          push_cast
          ring

theorem recurrence_phase_finite_step_error
    (dt : ℝ) (momentum : LatticeMomentum) (step : ℕ)
    (hstable : (dt * continuumModeFrequency momentum) ^ 2 ≤ 4) :
    ‖recurrencePositivePhase dt momentum ^ step -
        exactContinuumPositivePhase dt momentum ^ step‖ ≤
      (step : ℝ) *
        ‖recurrencePositivePhase dt momentum -
          exactContinuumPositivePhase dt momentum‖ := by
  exact complex_unit_phase_power_error _ _ step
    (recurrence_positive_phase_norm dt momentum hstable)
    (exact_continuum_positive_phase_norm dt momentum)

def exactPositiveModeEvolution
    (dt : ℝ) (mode : PositiveFrequencyMode) (step : ℕ) : Cell4 :=
  fun component =>
    exactContinuumPositivePhase dt mode.momentum ^ step *
      mode.amplitude component

theorem positive_mode_finite_step_component_error
    (dt : ℝ) (mode : PositiveFrequencyMode) (step : ℕ)
    (component : Fin 4)
    (hstable : (dt * continuumModeFrequency mode.momentum) ^ 2 ≤ 4) :
    ‖positiveModeEvolution dt mode step component -
        exactPositiveModeEvolution dt mode step component‖ ≤
      (step : ℝ) *
        ‖recurrencePositivePhase dt mode.momentum -
          exactContinuumPositivePhase dt mode.momentum‖ *
        ‖mode.amplitude component‖ := by
  unfold positiveModeEvolution exactPositiveModeEvolution
  rw [show recurrencePositivePhase dt mode.momentum ^ step *
        mode.amplitude component -
      exactContinuumPositivePhase dt mode.momentum ^ step *
        mode.amplitude component =
      (recurrencePositivePhase dt mode.momentum ^ step -
        exactContinuumPositivePhase dt mode.momentum ^ step) *
          mode.amplitude component by ring]
  rw [norm_mul]
  gcongr
  exact recurrence_phase_finite_step_error dt mode.momentum step hstable

def exactCoherentSpatialPacket
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site)
    (packet : FinitePositivePacket Mode) (dt : ℝ) (step : ℕ)
    (site : Site) : Cell4 :=
  cell4SpatialSynthesis frame
    (fun mode => exactPositiveModeEvolution dt (packet.mode mode) step) site

def coherentSpatialPointErrorBound
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site)
    (packet : FinitePositivePacket Mode) (dt : ℝ) (step : ℕ)
    (site : Site) (component : Fin 4) : ℝ :=
  ∑ mode,
    ‖frame.basis mode site‖ *
      ((step : ℝ) *
        ‖recurrencePositivePhase dt (packet.mode mode).momentum -
          exactContinuumPositivePhase dt (packet.mode mode).momentum‖ *
        ‖(packet.mode mode).amplitude component‖)

theorem coherent_spatial_packet_finite_step_error
    {Mode Site : Type} [Fintype Mode] [Fintype Site]
    [DecidableEq Mode]
    (frame : FiniteSpatialFrame Mode Site)
    (packet : FinitePositivePacket Mode) (dt : ℝ) (step : ℕ)
    (site : Site) (component : Fin 4)
    (hstable : ∀ index,
      (dt * continuumModeFrequency (packet.mode index).momentum) ^ 2 ≤ 4) :
    ‖coherentSpatialPacket frame packet dt step site component -
        exactCoherentSpatialPacket frame packet dt step site component‖ ≤
      coherentSpatialPointErrorBound frame packet dt step site component := by
  unfold coherentSpatialPacket exactCoherentSpatialPacket
    cell4SpatialSynthesis scalarSpatialSynthesis
    coherentSpatialPointErrorBound
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ mode, (
      frame.basis mode site *
          positiveModeEvolution dt (packet.mode mode) step component -
        frame.basis mode site *
          exactPositiveModeEvolution dt (packet.mode mode) step component)‖ ≤
        ∑ mode, ‖(
          frame.basis mode site *
          positiveModeEvolution dt (packet.mode mode) step component -
        frame.basis mode site *
          exactPositiveModeEvolution dt (packet.mode mode) step component)‖ := by
      simpa using norm_sum_le (Finset.univ : Finset Mode)
        (fun mode =>
          frame.basis mode site *
              positiveModeEvolution dt (packet.mode mode) step component -
            frame.basis mode site *
              exactPositiveModeEvolution dt (packet.mode mode) step component)
    _ ≤ ∑ mode,
        ‖frame.basis mode site‖ *
          ((step : ℝ) *
            ‖recurrencePositivePhase dt (packet.mode mode).momentum -
              exactContinuumPositivePhase dt
                (packet.mode mode).momentum‖ *
            ‖(packet.mode mode).amplitude component‖) := by
      apply Finset.sum_le_sum
      intro mode _
      rw [show frame.basis mode site *
              positiveModeEvolution dt (packet.mode mode) step component -
            frame.basis mode site *
              exactPositiveModeEvolution dt (packet.mode mode) step component =
          frame.basis mode site *
            (positiveModeEvolution dt (packet.mode mode) step component -
              exactPositiveModeEvolution dt (packet.mode mode) step component) by
        ring]
      rw [norm_mul]
      gcongr
      exact positive_mode_finite_step_component_error dt
        (packet.mode mode) step component (hstable mode)

theorem finite_addchar_sum_orthogonality
    {G : Type} [AddCommGroup G] [Fintype G]
    (first second : AddChar G ℂ) :
    (∑ site, starRingEnd ℂ (first site) * second site) =
      (Fintype.card G : ℂ) * if first = second then 1 else 0 := by
  have h := AddChar.wInner_cWeight_eq_boole first second
  simp [RCLike.wInner_cWeight_eq_expect,
    Fintype.expect_eq_sum_div_card, RCLike.inner_apply] at h
  have hcardNat : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast hcardNat
  field_simp [hcard] at h
  simpa [mul_comm] using h

def normalizedFiniteFourierBasis
    {G : Type} [AddCommGroup G] [Fintype G]
    (mode : AddChar G ℂ) (site : G) : ℂ :=
  mode site / (Real.sqrt (Fintype.card G) : ℂ)

theorem normalized_finite_fourier_basis_orthonormal
    {G : Type} [AddCommGroup G] [Fintype G]
    (first second : AddChar G ℂ) :
    (∑ site, starRingEnd ℂ (normalizedFiniteFourierBasis first site) *
      normalizedFiniteFourierBasis second site) =
      if first = second then 1 else 0 := by
  rw [show (∑ site,
      starRingEnd ℂ (normalizedFiniteFourierBasis first site) *
        normalizedFiniteFourierBasis second site) =
      (∑ site, starRingEnd ℂ (first site) * second site) /
        ((Real.sqrt (Fintype.card G) : ℂ) ^ 2) by
    unfold normalizedFiniteFourierBasis
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro site _
    simp [pow_two]
    ring]
  rw [finite_addchar_sum_orthogonality]
  rw [show (Real.sqrt (Fintype.card G) : ℂ) ^ 2 =
      (Fintype.card G : ℂ) by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ (Fintype.card G : ℝ) by
      positivity)]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  field_simp [hcard]

noncomputable def finiteFourierSpatialFrame
    (G : Type) [AddCommGroup G] [Fintype G] :
    FiniteSpatialFrame (AddChar G ℂ) G := by
  classical
  exact
    { basis := normalizedFiniteFourierBasis
      orthonormal := normalized_finite_fourier_basis_orthonormal }

/-! The spatial character and the momentum carried by a positive-frequency
mode must be the same label.  The following construction closes that bridge
rather than silently pairing an arbitrary orthonormal basis vector with an
unrelated momentum. -/

def characterMomentum
    {G : Type} [AddCommGroup G] [Fintype G]
    (axisStep : Fin 3 → G) (mode : AddChar G ℂ) : LatticeMomentum :=
  fun axis => Complex.arg (mode (axisStep axis))

theorem character_value_is_momentum_phase
    {G : Type} [AddCommGroup G] [Fintype G]
    (axisStep : Fin 3 → G) (mode : AddChar G ℂ) (axis : Fin 3) :
    mode (axisStep axis) =
      Complex.exp (Complex.I *
        ((characterMomentum axisStep mode axis : ℝ) : ℂ)) := by
  rw [show Complex.I *
      ((characterMomentum axisStep mode axis : ℝ) : ℂ) =
      (Complex.arg (mode (axisStep axis)) : ℂ) * Complex.I by
    simp [characterMomentum]
    ring]
  calc
    mode (axisStep axis) =
        (‖mode (axisStep axis)‖ : ℂ) *
          Complex.exp
            ((Complex.arg (mode (axisStep axis)) : ℂ) * Complex.I) := by
      exact (Complex.norm_mul_exp_arg_mul_I (mode (axisStep axis))).symm
    _ = Complex.exp
          ((Complex.arg (mode (axisStep axis)) : ℂ) * Complex.I) := by
      rw [AddChar.norm_apply]
      simp

theorem normalized_finite_fourier_basis_translation_phase
    {G : Type} [AddCommGroup G] [Fintype G]
    (axisStep : Fin 3 → G) (mode : AddChar G ℂ)
    (site : G) (axis : Fin 3) :
    normalizedFiniteFourierBasis mode (site + axisStep axis) =
      Complex.exp (Complex.I *
          ((characterMomentum axisStep mode axis : ℝ) : ℂ)) *
        normalizedFiniteFourierBasis mode site := by
  unfold normalizedFiniteFourierBasis
  rw [AddChar.map_add_eq_mul]
  rw [character_value_is_momentum_phase axisStep mode axis]
  ring

def canonicalCharacterPacket
    {G : Type} [AddCommGroup G] [Fintype G]
    (axisStep : Fin 3 → G) : FinitePositivePacket (AddChar G ℂ) where
  mode character :=
    canonicalPositiveFrequencyMode (characterMomentum axisStep character)

structure MomentumCompatibleCharacterPacket
    (G : Type) [AddCommGroup G] [Fintype G]
    (axisStep : Fin 3 → G) where
  packet : FinitePositivePacket (AddChar G ℂ)
  momentumMatchesCharacter : ∀ mode,
    (packet.mode mode).momentum = characterMomentum axisStep mode

def canonicalMomentumCompatibleCharacterPacket
    {G : Type} [AddCommGroup G] [Fintype G]
    (axisStep : Fin 3 → G) :
    MomentumCompatibleCharacterPacket G axisStep where
  packet := canonicalCharacterPacket axisStep
  momentumMatchesCharacter := fun _ => rfl

theorem canonical_character_packet_momentum_is_spatial_momentum
    {G : Type} [AddCommGroup G] [Fintype G]
    (axisStep : Fin 3 → G) (mode : AddChar G ℂ) :
    ((canonicalCharacterPacket axisStep).mode mode).momentum =
      characterMomentum axisStep mode := rfl

theorem canonical_character_packet_basis_translation
    {G : Type} [AddCommGroup G] [Fintype G]
    (axisStep : Fin 3 → G) (mode : AddChar G ℂ)
    (site : G) (axis : Fin 3) :
    (finiteFourierSpatialFrame G).basis mode (site + axisStep axis) =
      Complex.exp (Complex.I *
        ((((canonicalCharacterPacket axisStep).mode mode).momentum axis : ℝ) : ℂ)) *
      (finiteFourierSpatialFrame G).basis mode site := by
  exact normalized_finite_fourier_basis_translation_phase
    axisStep mode site axis

theorem momentum_compatible_packet_basis_translation
    {G : Type} [AddCommGroup G] [Fintype G]
    {axisStep : Fin 3 → G}
    (spatialPacket : MomentumCompatibleCharacterPacket G axisStep)
    (mode : AddChar G ℂ) (site : G) (axis : Fin 3) :
    (finiteFourierSpatialFrame G).basis mode (site + axisStep axis) =
      Complex.exp (Complex.I *
        (((spatialPacket.packet.mode mode).momentum axis : ℝ) : ℂ)) *
      (finiteFourierSpatialFrame G).basis mode site := by
  rw [spatialPacket.momentumMatchesCharacter mode]
  exact normalized_finite_fourier_basis_translation_phase
    axisStep mode site axis

abbrev PeriodicCubicSites (N : ℕ) := Fin 3 → ZMod N

def periodicCubicAxisStep (N : ℕ) (axis : Fin 3) : PeriodicCubicSites N :=
  fun component => if component = axis then 1 else 0

theorem periodic_cubic_character_packet_is_momentum_compatible
    (N : ℕ) [NeZero N]
    (mode : AddChar (PeriodicCubicSites N) ℂ)
    (site : PeriodicCubicSites N) (axis : Fin 3) :
    (finiteFourierSpatialFrame (PeriodicCubicSites N)).basis mode
        (site + periodicCubicAxisStep N axis) =
      Complex.exp (Complex.I *
        ((((canonicalCharacterPacket (periodicCubicAxisStep N)).mode mode).momentum
          axis : ℝ) : ℂ)) *
      (finiteFourierSpatialFrame (PeriodicCubicSites N)).basis mode site := by
  exact canonical_character_packet_basis_translation
    (periodicCubicAxisStep N) mode site axis

theorem momentum_compatible_coherent_density_is_preserved
    {G : Type} [AddCommGroup G] [Fintype G]
    {axisStep : Fin 3 → G}
    (spatialPacket : MomentumCompatibleCharacterPacket G axisStep)
    (dt : ℝ) (step : ℕ)
    (hstable : ∀ mode,
      (dt * continuumModeFrequency
        (spatialPacket.packet.mode mode).momentum) ^ 2 ≤ 4) :
    coherentSpatialPacketDensity (finiteFourierSpatialFrame G)
        spatialPacket.packet dt step =
      finitePacketDensity spatialPacket.packet := by
  exact coherent_spatial_packet_density_is_preserved
    (finiteFourierSpatialFrame G) spatialPacket.packet dt step hstable

theorem momentum_compatible_coherent_current_is_velocity_moment
    {G : Type} [AddCommGroup G] [Fintype G]
    {axisStep : Fin 3 → G}
    (spatialPacket : MomentumCompatibleCharacterPacket G axisStep)
    (dt : ℝ) (step : ℕ) (axis : Fin 3)
    (hstable : ∀ mode,
      (dt * continuumModeFrequency
        (spatialPacket.packet.mode mode).momentum) ^ 2 ≤ 4) :
    coherentSpatialPacketCurrent (finiteFourierSpatialFrame G)
        spatialPacket.packet dt step axis =
      finitePacketVelocityMoment axis spatialPacket.packet := by
  exact coherent_spatial_packet_current_is_velocity_moment
    (finiteFourierSpatialFrame G) spatialPacket.packet dt step axis hstable

theorem momentum_compatible_nonzero_velocity_gives_spatial_transport
    {G : Type} [AddCommGroup G] [Fintype G]
    {axisStep : Fin 3 → G}
    (spatialPacket : MomentumCompatibleCharacterPacket G axisStep)
    (dt : ℝ) (step : ℕ) (axis : Fin 3)
    (hstable : ∀ mode,
      (dt * continuumModeFrequency
        (spatialPacket.packet.mode mode).momentum) ^ 2 ≤ 4)
    (hmoving : finitePacketVelocityMoment axis spatialPacket.packet ≠ 0) :
    coherentSpatialPacketCurrent (finiteFourierSpatialFrame G)
        spatialPacket.packet dt step axis ≠ 0 := by
  exact coherent_spatial_packet_has_nonzero_transport
    (finiteFourierSpatialFrame G) spatialPacket.packet dt step axis
      hstable hmoving

theorem momentum_compatible_coherent_finite_step_error
    {G : Type} [AddCommGroup G] [Fintype G]
    {axisStep : Fin 3 → G}
    (spatialPacket : MomentumCompatibleCharacterPacket G axisStep)
    (dt : ℝ) (step : ℕ) (site : G) (component : Fin 4)
    (hstable : ∀ mode,
      (dt * continuumModeFrequency
        (spatialPacket.packet.mode mode).momentum) ^ 2 ≤ 4) :
    ‖coherentSpatialPacket (finiteFourierSpatialFrame G)
          spatialPacket.packet dt step site component -
        exactCoherentSpatialPacket (finiteFourierSpatialFrame G)
          spatialPacket.packet dt step site component‖ ≤
      coherentSpatialPointErrorBound (finiteFourierSpatialFrame G)
        spatialPacket.packet dt step site component := by
  exact coherent_spatial_packet_finite_step_error
    (finiteFourierSpatialFrame G) spatialPacket.packet dt step site component
      hstable

structure Dirac020CoherentSpatialTransportCertificate : Prop where
  priorChain : Dirac019FinitePacketTransportCertificate
  explicitFiniteFourierFrameIsOrthonormal :
    ∀ {G : Type} [AddCommGroup G] [Fintype G]
      (first second : AddChar G ℂ),
      (∑ site,
        starRingEnd ℂ (normalizedFiniteFourierBasis first site) *
          normalizedFiniteFourierBasis second site) =
        if first = second then 1 else 0
  periodicCubicCharacterMomentumMatchesSpatialPhase :
    ∀ (N : ℕ) [NeZero N]
      (mode : AddChar (PeriodicCubicSites N) ℂ)
      (site : PeriodicCubicSites N) (axis : Fin 3),
      (finiteFourierSpatialFrame (PeriodicCubicSites N)).basis mode
          (site + periodicCubicAxisStep N axis) =
        Complex.exp (Complex.I *
          ((((canonicalCharacterPacket (periodicCubicAxisStep N)).mode mode).momentum
            axis : ℝ) : ℂ)) *
        (finiteFourierSpatialFrame (PeriodicCubicSites N)).basis mode site
  compatiblePacketMomentumMatchesSpatialPhase :
    ∀ {G : Type} [AddCommGroup G] [Fintype G]
      {axisStep : Fin 3 → G}
      (spatialPacket : MomentumCompatibleCharacterPacket G axisStep)
      (mode : AddChar G ℂ) (site : G) (axis : Fin 3),
      (finiteFourierSpatialFrame G).basis mode (site + axisStep axis) =
        Complex.exp (Complex.I *
          (((spatialPacket.packet.mode mode).momentum axis : ℝ) : ℂ)) *
        (finiteFourierSpatialFrame G).basis mode site
  coherentDensityIsParsevalDensity :
    ∀ {Mode Site : Type} [Fintype Mode] [Fintype Site]
      [DecidableEq Mode] (frame : FiniteSpatialFrame Mode Site)
      (packet : FinitePositivePacket Mode) dt step,
      coherentSpatialPacketDensity frame packet dt step =
        finitePacketEvolvedDensity dt packet step
  coherentDensityPersistsForEveryStableUpdate :
    ∀ {G : Type} [AddCommGroup G] [Fintype G]
      {axisStep : Fin 3 → G}
      (spatialPacket : MomentumCompatibleCharacterPacket G axisStep) dt step,
      (∀ mode,
        (dt * continuumModeFrequency
          (spatialPacket.packet.mode mode).momentum) ^ 2 ≤ 4) →
      coherentSpatialPacketDensity (finiteFourierSpatialFrame G)
          spatialPacket.packet dt step =
        finitePacketDensity spatialPacket.packet
  coherentCurrentIsDensityWeightedVelocity :
    ∀ {G : Type} [AddCommGroup G] [Fintype G]
      {axisStep : Fin 3 → G}
      (spatialPacket : MomentumCompatibleCharacterPacket G axisStep)
      dt step axis,
      (∀ mode,
        (dt * continuumModeFrequency
          (spatialPacket.packet.mode mode).momentum) ^ 2 ≤ 4) →
      coherentSpatialPacketCurrent (finiteFourierSpatialFrame G)
          spatialPacket.packet dt step axis =
        finitePacketVelocityMoment axis spatialPacket.packet
  nonzeroVelocityMomentGivesSpatialTransport :
    ∀ {G : Type} [AddCommGroup G] [Fintype G]
      {axisStep : Fin 3 → G}
      (spatialPacket : MomentumCompatibleCharacterPacket G axisStep)
      dt step axis,
      (∀ mode,
        (dt * continuumModeFrequency
          (spatialPacket.packet.mode mode).momentum) ^ 2 ≤ 4) →
      finitePacketVelocityMoment axis spatialPacket.packet ≠ 0 →
      coherentSpatialPacketCurrent (finiteFourierSpatialFrame G)
          spatialPacket.packet dt step axis ≠ 0
  finiteUpdatePointwiseErrorIsControlled :
    ∀ {G : Type} [AddCommGroup G] [Fintype G]
      {axisStep : Fin 3 → G}
      (spatialPacket : MomentumCompatibleCharacterPacket G axisStep)
      dt step site component,
      (∀ mode,
        (dt * continuumModeFrequency
          (spatialPacket.packet.mode mode).momentum) ^ 2 ≤ 4) →
      ‖coherentSpatialPacket (finiteFourierSpatialFrame G)
            spatialPacket.packet dt step site component -
          exactCoherentSpatialPacket (finiteFourierSpatialFrame G)
            spatialPacket.packet dt step site component‖ ≤
        coherentSpatialPointErrorBound (finiteFourierSpatialFrame G)
          spatialPacket.packet dt step site component

theorem dirac020_coherent_spatial_transport :
    Dirac020CoherentSpatialTransportCertificate where
  priorChain := dirac019_finite_packet_transport
  explicitFiniteFourierFrameIsOrthonormal :=
    normalized_finite_fourier_basis_orthonormal
  periodicCubicCharacterMomentumMatchesSpatialPhase :=
    periodic_cubic_character_packet_is_momentum_compatible
  compatiblePacketMomentumMatchesSpatialPhase :=
    momentum_compatible_packet_basis_translation
  coherentDensityIsParsevalDensity :=
    coherent_spatial_packet_density_is_spectral_density
  coherentDensityPersistsForEveryStableUpdate :=
    momentum_compatible_coherent_density_is_preserved
  coherentCurrentIsDensityWeightedVelocity :=
    momentum_compatible_coherent_current_is_velocity_moment
  nonzeroVelocityMomentGivesSpatialTransport :=
    momentum_compatible_nonzero_velocity_gives_spatial_transport
  finiteUpdatePointwiseErrorIsControlled :=
    momentum_compatible_coherent_finite_step_error

end
end LeanDirac
