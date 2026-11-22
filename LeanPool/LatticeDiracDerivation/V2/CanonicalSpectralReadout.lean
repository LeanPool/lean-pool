/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.PositiveFrequencyCurrentBridge

/-!
# Canonical spectral readout of the native Klein--Gordon phase space

At fixed positive mass-shell energy, every native two-layer phase splits
uniquely into positive- and negative-frequency amplitudes.  This file maps
those amplitudes to the corresponding energy eigenspaces of the cube-derived
Hamiltonian, and constructs the inverse map explicitly.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex BigOperators
noncomputable section

/-- Extract the positive-frequency amplitude from native position and velocity. -/
def nativePositiveAmplitude
    (energy : ℝ) (phase : UniformTwoChannelPhase) : UniformCell2 :=
  fun component =>
    (phase.1 component + I * phase.2 component / (energy : ℂ)) / 2

/-- Extract the negative-frequency amplitude from native position and velocity. -/
def nativeNegativeAmplitude
    (energy : ℝ) (phase : UniformTwoChannelPhase) : UniformCell2 :=
  fun component =>
    (phase.1 component - I * phase.2 component / (energy : ℂ)) / 2

/-- Reassemble native position and velocity from both frequency branches. -/
def nativePhaseOfFrequencyAmplitudes
    (energy : ℝ) (positive negative : UniformCell2) :
    UniformTwoChannelPhase :=
  (fun component => positive component + negative component,
    fun component =>
      -I * (energy : ℂ) * positive component +
        I * (energy : ℂ) * negative component)

theorem native_frequency_amplitudes_reconstruct
    (energy : ℝ) (henergy : energy ≠ 0)
    (phase : UniformTwoChannelPhase) :
    nativePhaseOfFrequencyAmplitudes energy
        (nativePositiveAmplitude energy phase)
        (nativeNegativeAmplitude energy phase) = phase := by
  apply Prod.ext <;> funext component
  · simp [nativePhaseOfFrequencyAmplitudes, nativePositiveAmplitude,
      nativeNegativeAmplitude]
    field_simp [show (energy : ℂ) ≠ 0 by exact_mod_cast henergy]
    ring
  · simp [nativePhaseOfFrequencyAmplitudes, nativePositiveAmplitude,
      nativeNegativeAmplitude]
    field_simp [show (energy : ℂ) ≠ 0 by exact_mod_cast henergy]
    ring_nf
    rw [Complex.I_sq]
    ring

theorem native_frequency_amplitudes_extract
    (energy : ℝ) (henergy : energy ≠ 0)
    (positive negative : UniformCell2) :
    nativePositiveAmplitude energy
        (nativePhaseOfFrequencyAmplitudes energy positive negative) = positive ∧
      nativeNegativeAmplitude energy
        (nativePhaseOfFrequencyAmplitudes energy positive negative) = negative := by
  constructor <;> funext component <;>
    simp [nativePositiveAmplitude, nativeNegativeAmplitude,
      nativePhaseOfFrequencyAmplitudes] <;>
    field_simp [show (energy : ℂ) ≠ 0 by exact_mod_cast henergy] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

/-- Canonically normalized negative-energy embedding. -/
def normalizedNegativeFrequencyEmbedding
    (mass energy px py pz : ℝ) (q : UniformCell2) : CubicalCell4
  | 0 => -(positiveFrequencyRatio mass energy : ℂ) *
      positivePauliSpatial px py pz q 0
  | 1 => -(positiveFrequencyRatio mass energy : ℂ) *
      positivePauliSpatial px py pz q 1
  | 2 => (positiveFrequencyScale mass energy : ℂ) * q 0
  | _ => (positiveFrequencyScale mass energy : ℂ) * q 1

theorem normalized_negative_frequency_is_energy_eigenstate
    (mass energy px py pz : ℝ)
    (hdenom : energy + mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (q : UniformCell2) :
    cubicalStandardHamiltonian (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
        (normalizedNegativeFrequencyEmbedding mass energy px py pz q) =
      fun component =>
        -(energy : ℂ) *
          normalizedNegativeFrequencyEmbedding mass energy px py pz q component := by
  have hratio : positiveFrequencyRatio mass energy * (energy + mass) =
      positiveFrequencyScale mass energy := by
    simp [positiveFrequencyRatio, hdenom]
  have hmassShell : mass * (energy + mass) +
        (px ^ 2 + py ^ 2 + pz ^ 2) = energy * (energy + mass) := by
    nlinarith
  have htop : mass * positiveFrequencyRatio mass energy -
        positiveFrequencyScale mass energy =
      -energy * positiveFrequencyRatio mass energy := by
    nlinarith [hratio]
  have hbottom :
      -(px ^ 2 + py ^ 2 + pz ^ 2) * positiveFrequencyRatio mass energy -
        mass * positiveFrequencyScale mass energy =
      -energy * positiveFrequencyScale mass energy := by
    calc
      -(px ^ 2 + py ^ 2 + pz ^ 2) * positiveFrequencyRatio mass energy -
          mass * positiveFrequencyScale mass energy =
        -positiveFrequencyRatio mass energy *
          ((px ^ 2 + py ^ 2 + pz ^ 2) + mass * (energy + mass)) := by
            rw [← hratio]
            ring
      _ = -positiveFrequencyRatio mass energy *
          (energy * (energy + mass)) := by
        rw [show (px ^ 2 + py ^ 2 + pz ^ 2) + mass * (energy + mass) =
          energy * (energy + mass) by nlinarith [hmassShell]]
      _ = -energy * positiveFrequencyScale mass energy := by
        rw [← hratio]
        ring
  have htopC : (mass : ℂ) * (positiveFrequencyRatio mass energy : ℂ) -
        (positiveFrequencyScale mass energy : ℂ) =
      -(energy : ℂ) * (positiveFrequencyRatio mass energy : ℂ) := by
    exact_mod_cast htop
  have hbottomC :
      -((px : ℂ) ^ 2 + (py : ℂ) ^ 2 + (pz : ℂ) ^ 2) *
          (positiveFrequencyRatio mass energy : ℂ) -
        (mass : ℂ) * (positiveFrequencyScale mass energy : ℂ) =
      -(energy : ℂ) * (positiveFrequencyScale mass energy : ℂ) := by
    exact_mod_cast hbottom
  funext component
  fin_cases component
  · simp [cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      normalizedNegativeFrequencyEmbedding, positivePauliSpatial]
    ring_nf
    linear_combination
      -((pz : ℂ) * q 0 + ((px : ℂ) - I * (py : ℂ)) * q 1) * htopC
  · simp [cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      normalizedNegativeFrequencyEmbedding, positivePauliSpatial]
    ring_nf
    linear_combination
      -(((px : ℂ) + I * (py : ℂ)) * q 0 - (pz : ℂ) * q 1) * htopC
  · simp [cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      normalizedNegativeFrequencyEmbedding, positivePauliSpatial]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
    linear_combination (q 0) * hbottomC
  · simp [cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      normalizedNegativeFrequencyEmbedding, positivePauliSpatial]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
    linear_combination (q 1) * hbottomC

/-- Combine the positive and negative branch embeddings in one spinor. -/
def canonicalSpectralReadout
    (mass energy px py pz : ℝ)
    (phase : UniformTwoChannelPhase) : CubicalCell4 :=
  fun component =>
    normalizedPositiveFrequencyEmbedding mass energy px py pz
        (nativePositiveAmplitude energy phase) component +
      normalizedNegativeFrequencyEmbedding mass energy px py pz
        (nativeNegativeAmplitude energy phase) component

theorem canonical_spectral_readout_positive_phase
    (mass energy px py pz : ℝ) (henergy : energy ≠ 0)
    (q : UniformCell2) :
    canonicalSpectralReadout mass energy px py pz
        (nativePhaseOfFrequencyAmplitudes energy q (fun _ => 0)) =
      normalizedPositiveFrequencyEmbedding mass energy px py pz q := by
  have h := native_frequency_amplitudes_extract energy henergy q (fun _ => 0)
  funext component
  simp only [canonicalSpectralReadout]
  rw [show nativePositiveAmplitude energy
      (nativePhaseOfFrequencyAmplitudes energy q (fun _ => 0)) = q from h.1,
    show nativeNegativeAmplitude energy
      (nativePhaseOfFrequencyAmplitudes energy q (fun _ => 0)) =
        (fun _ => 0) from h.2]
  fin_cases component <;>
    simp [normalizedNegativeFrequencyEmbedding,
      positivePauliSpatial]

theorem canonical_spectral_readout_negative_phase
    (mass energy px py pz : ℝ) (henergy : energy ≠ 0)
    (q : UniformCell2) :
    canonicalSpectralReadout mass energy px py pz
        (nativePhaseOfFrequencyAmplitudes energy (fun _ => 0) q) =
      normalizedNegativeFrequencyEmbedding mass energy px py pz q := by
  have h := native_frequency_amplitudes_extract energy henergy (fun _ => 0) q
  funext component
  simp only [canonicalSpectralReadout]
  rw [show nativePositiveAmplitude energy
      (nativePhaseOfFrequencyAmplitudes energy (fun _ => 0) q) =
        (fun _ => 0) from h.1,
    show nativeNegativeAmplitude energy
      (nativePhaseOfFrequencyAmplitudes energy (fun _ => 0) q) = q from h.2]
  fin_cases component <;>
    simp [normalizedPositiveFrequencyEmbedding,
      positivePauliSpatial]

theorem native_amplitudes_of_kg_generator
    (mass energy px py pz : ℝ) (henergy : energy ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (phase : UniformTwoChannelPhase) :
    nativePositiveAmplitude energy
        (uniformTwoChannelKleinGordonVector (mass : ℂ)
          (px : ℂ) (py : ℂ) (pz : ℂ) phase) =
        (fun component =>
          -I * (energy : ℂ) *
            nativePositiveAmplitude energy phase component) ∧
      nativeNegativeAmplitude energy
        (uniformTwoChannelKleinGordonVector (mass : ℂ)
          (px : ℂ) (py : ℂ) (pz : ℂ) phase) =
        fun component =>
          I * (energy : ℂ) *
            nativeNegativeAmplitude energy phase component := by
  have hshellC : ((mass : ℂ) ^ 2 + (px : ℂ) ^ 2 +
      (py : ℂ) ^ 2 + (pz : ℂ) ^ 2) = (energy : ℂ) ^ 2 := by
    exact_mod_cast hshell.symm
  constructor <;> funext component <;>
    simp [nativePositiveAmplitude, nativeNegativeAmplitude,
      uniformTwoChannelKleinGordonVector] <;>
    field_simp [show (energy : ℂ) ≠ 0 by exact_mod_cast henergy] <;>
    ring_nf <;>
    rw [← hshellC] <;>
    rw [Complex.I_sq] <;>
    ring

theorem normalized_positive_frequency_embedding_scale
    (mass energy px py pz : ℝ) (scalar : ℂ) (q : UniformCell2) :
    normalizedPositiveFrequencyEmbedding mass energy px py pz
        (fun component => scalar * q component) =
      fun component => scalar *
        normalizedPositiveFrequencyEmbedding mass energy px py pz q component := by
  funext component
  fin_cases component <;>
    simp [normalizedPositiveFrequencyEmbedding, positivePauliSpatial] <;>
    ring

theorem normalized_negative_frequency_embedding_scale
    (mass energy px py pz : ℝ) (scalar : ℂ) (q : UniformCell2) :
    normalizedNegativeFrequencyEmbedding mass energy px py pz
        (fun component => scalar * q component) =
      fun component => scalar *
        normalizedNegativeFrequencyEmbedding mass energy px py pz q component := by
  funext component
  fin_cases component <;>
    simp [normalizedNegativeFrequencyEmbedding, positivePauliSpatial] <;>
    ring

theorem cubical_standard_hamiltonian_add
    (mass px py pz : ℂ) (first second : CubicalCell4) :
    cubicalStandardHamiltonian mass px py pz
        (fun component => first component + second component) =
      fun component =>
        cubicalStandardHamiltonian mass px py pz first component +
          cubicalStandardHamiltonian mass px py pz second component := by
  funext component
  fin_cases component <;>
    simp [cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    ring

/-- The one spectral map intertwines the complete positive+negative native
phase space with the same cubical Hamiltonian. -/
theorem canonical_spectral_readout_intertwines
    (mass energy px py pz : ℝ)
    (henergy : energy ≠ 0) (hdenom : energy + mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (phase : UniformTwoChannelPhase) :
    canonicalSpectralReadout mass energy px py pz
        (uniformTwoChannelKleinGordonVector (mass : ℂ)
          (px : ℂ) (py : ℂ) (pz : ℂ) phase) =
      fun component =>
        -I * cubicalStandardHamiltonian (mass : ℂ)
          (px : ℂ) (py : ℂ) (pz : ℂ)
          (canonicalSpectralReadout mass energy px py pz phase) component := by
  have hamp := native_amplitudes_of_kg_generator
    mass energy px py pz henergy hshell phase
  have hpos := normalized_positive_frequency_is_energy_eigenstate
    mass energy px py pz hdenom hshell
      (nativePositiveAmplitude energy phase)
  have hneg := normalized_negative_frequency_is_energy_eigenstate
    mass energy px py pz hdenom hshell
      (nativeNegativeAmplitude energy phase)
  have hposScale := normalized_positive_frequency_embedding_scale
    mass energy px py pz (-I * (energy : ℂ))
      (nativePositiveAmplitude energy phase)
  have hnegScale := normalized_negative_frequency_embedding_scale
    mass energy px py pz (I * (energy : ℂ))
      (nativeNegativeAmplitude energy phase)
  have hadd := cubical_standard_hamiltonian_add
    (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
    (normalizedPositiveFrequencyEmbedding mass energy px py pz
      (nativePositiveAmplitude energy phase))
    (normalizedNegativeFrequencyEmbedding mass energy px py pz
      (nativeNegativeAmplitude energy phase))
  unfold canonicalSpectralReadout
  rw [show nativePositiveAmplitude energy
      (uniformTwoChannelKleinGordonVector (mass : ℂ)
        (px : ℂ) (py : ℂ) (pz : ℂ) phase) =
      (fun c => -I * (energy : ℂ) *
        nativePositiveAmplitude energy phase c) from hamp.1,
    show nativeNegativeAmplitude energy
      (uniformTwoChannelKleinGordonVector (mass : ℂ)
        (px : ℂ) (py : ℂ) (pz : ℂ) phase) =
      (fun c => I * (energy : ℂ) *
        nativeNegativeAmplitude energy phase c) from hamp.2]
  rw [hposScale, hnegScale, hadd, hpos, hneg]
  funext component
  ring

/-- Restrict a four-component spinor to its upper two components. -/
def cubicalCell4Upper (z : CubicalCell4) : UniformCell2
  | 0 => z 0
  | _ => z 1

/-- Restrict a four-component spinor to its lower two components. -/
def cubicalCell4LowerHalf (z : CubicalCell4) : UniformCell2
  | 0 => z 2
  | _ => z 3

/-- Recover the positive-frequency coefficient from the spinor spectral coordinates. -/
def spectralPositiveCoordinate
    (mass energy px py pz : ℝ) (z : CubicalCell4) : UniformCell2 :=
  fun component =>
    ((positiveFrequencyScale mass energy : ℂ) * cubicalCell4Upper z component +
      (positiveFrequencyRatio mass energy : ℂ) *
        positivePauliSpatial px py pz (cubicalCell4LowerHalf z) component) /
      (energy : ℂ)

/-- Recover the negative-frequency coefficient from the spinor spectral coordinates. -/
def spectralNegativeCoordinate
    (mass energy px py pz : ℝ) (z : CubicalCell4) : UniformCell2 :=
  fun component =>
    (-(positiveFrequencyRatio mass energy : ℂ) *
        positivePauliSpatial px py pz (cubicalCell4Upper z) component +
      (positiveFrequencyScale mass energy : ℂ) *
        cubicalCell4LowerHalf z component) /
      (energy : ℂ)

/-- Recover native phase coordinates by extracting and reassembling both branches. -/
def canonicalSpectralReadoutInverse
    (mass energy px py pz : ℝ) (z : CubicalCell4) :
    UniformTwoChannelPhase :=
  nativePhaseOfFrequencyAmplitudes energy
    (spectralPositiveCoordinate mass energy px py pz z)
    (spectralNegativeCoordinate mass energy px py pz z)

theorem spectral_normalization_coefficient
    (mass energy px py pz : ℝ)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) :
    positiveFrequencyScale mass energy ^ 2 +
        positiveFrequencyRatio mass energy ^ 2 *
          (px ^ 2 + py ^ 2 + pz ^ 2) = energy := by
  have hdenom : energy + mass ≠ 0 := ne_of_gt hpositive
  have hscale := positive_frequency_scale_square mass energy (le_of_lt hpositive)
  rw [positiveFrequencyRatio]
  field_simp [hdenom]
  rw [hscale]
  nlinarith

theorem spectral_coordinates_extract_embeddings
    (mass energy px py pz : ℝ)
    (henergy : energy ≠ 0) (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (positive negative : UniformCell2) :
    let z : CubicalCell4 := fun component =>
      normalizedPositiveFrequencyEmbedding mass energy px py pz positive component +
        normalizedNegativeFrequencyEmbedding mass energy px py pz negative component
    spectralPositiveCoordinate mass energy px py pz z = positive ∧
      spectralNegativeCoordinate mass energy px py pz z = negative := by
  dsimp only
  have hcoeff := spectral_normalization_coefficient
    mass energy px py pz hpositive hshell
  have hcoeffC :
      (positiveFrequencyScale mass energy : ℂ) ^ 2 +
          (positiveFrequencyRatio mass energy : ℂ) ^ 2 *
            ((px : ℂ) ^ 2 + (py : ℂ) ^ 2 + (pz : ℂ) ^ 2) =
        (energy : ℂ) := by
    exact_mod_cast hcoeff
  constructor <;> funext component <;> fin_cases component <;>
    simp [spectralPositiveCoordinate, spectralNegativeCoordinate,
      cubicalCell4Upper, cubicalCell4LowerHalf,
      normalizedPositiveFrequencyEmbedding,
      normalizedNegativeFrequencyEmbedding, positivePauliSpatial] <;>
    field_simp [show (energy : ℂ) ≠ 0 by exact_mod_cast henergy] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring_nf <;>
    first
    | linear_combination positive 0 * hcoeffC
    | linear_combination positive 1 * hcoeffC
    | linear_combination negative 0 * hcoeffC
    | linear_combination negative 1 * hcoeffC

theorem canonical_spectral_readout_left_inverse
    (mass energy px py pz : ℝ)
    (henergy : energy ≠ 0) (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (phase : UniformTwoChannelPhase) :
    canonicalSpectralReadoutInverse mass energy px py pz
        (canonicalSpectralReadout mass energy px py pz phase) = phase := by
  have hcoords := spectral_coordinates_extract_embeddings
    mass energy px py pz henergy hpositive hshell
      (nativePositiveAmplitude energy phase)
      (nativeNegativeAmplitude energy phase)
  unfold canonicalSpectralReadoutInverse canonicalSpectralReadout
  rw [hcoords.1, hcoords.2]
  exact native_frequency_amplitudes_reconstruct energy henergy phase

theorem canonical_spectral_readout_injective
    (mass energy px py pz : ℝ)
    (henergy : energy ≠ 0) (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) :
    Function.Injective (canonicalSpectralReadout mass energy px py pz) := by
  intro first second heq
  have := congrArg
    (canonicalSpectralReadoutInverse mass energy px py pz) heq
  simpa [canonical_spectral_readout_left_inverse mass energy px py pz
    henergy hpositive hshell] using this

theorem spectral_embeddings_reconstruct_cell
    (mass energy px py pz : ℝ)
    (henergy : energy ≠ 0) (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (z : CubicalCell4) :
    (fun component =>
      normalizedPositiveFrequencyEmbedding mass energy px py pz
          (spectralPositiveCoordinate mass energy px py pz z) component +
        normalizedNegativeFrequencyEmbedding mass energy px py pz
          (spectralNegativeCoordinate mass energy px py pz z) component) = z := by
  have hcoeff := spectral_normalization_coefficient
    mass energy px py pz hpositive hshell
  have hcoeffC :
      (positiveFrequencyScale mass energy : ℂ) ^ 2 +
          (positiveFrequencyRatio mass energy : ℂ) ^ 2 *
            ((px : ℂ) ^ 2 + (py : ℂ) ^ 2 + (pz : ℂ) ^ 2) =
        (energy : ℂ) := by
    exact_mod_cast hcoeff
  funext component
  fin_cases component <;>
    simp [spectralPositiveCoordinate, spectralNegativeCoordinate,
      cubicalCell4Upper, cubicalCell4LowerHalf,
      normalizedPositiveFrequencyEmbedding,
      normalizedNegativeFrequencyEmbedding, positivePauliSpatial] <;>
    field_simp [show (energy : ℂ) ≠ 0 by exact_mod_cast henergy] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring_nf <;>
    first
    | linear_combination z 0 * hcoeffC
    | linear_combination z 1 * hcoeffC
    | linear_combination z 2 * hcoeffC
    | linear_combination z 3 * hcoeffC

theorem canonical_spectral_readout_right_inverse
    (mass energy px py pz : ℝ)
    (henergy : energy ≠ 0) (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (z : CubicalCell4) :
    canonicalSpectralReadout mass energy px py pz
        (canonicalSpectralReadoutInverse mass energy px py pz z) = z := by
  have hamp := native_frequency_amplitudes_extract energy henergy
    (spectralPositiveCoordinate mass energy px py pz z)
    (spectralNegativeCoordinate mass energy px py pz z)
  unfold canonicalSpectralReadoutInverse canonicalSpectralReadout
  rw [hamp.1, hamp.2]
  exact spectral_embeddings_reconstruct_cell
    mass energy px py pz henergy hpositive hshell z

theorem canonical_spectral_readout_bijective
    (mass energy px py pz : ℝ)
    (henergy : energy ≠ 0) (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) :
    Function.Bijective (canonicalSpectralReadout mass energy px py pz) := by
  constructor
  · exact canonical_spectral_readout_injective
      mass energy px py pz henergy hpositive hshell
  · intro z
    exact ⟨canonicalSpectralReadoutInverse mass energy px py pz z,
      canonical_spectral_readout_right_inverse
        mass energy px py pz henergy hpositive hshell z⟩

/-- Same-state positive-frequency density/current bridge.  The native phase,
the canonical spectral spinor, the U(1) density, and the directed C19 bond
flux all use the same native amplitude `q`.  The only current mismatch is the
explicit finite-spacing sine remainder. -/
theorem canonical_spectral_positive_phase_has_native_density_current
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (henergy : energy ≠ 0) (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 +
      (c19ContinuumSpeed * momentum 0) ^ 2 +
      (c19ContinuumSpeed * momentum 1) ^ 2 +
      (c19ContinuumSpeed * momentum 2) ^ 2)
    (axis : Fin 3) (q : UniformCell2) :
    cubicalCell4Density
        (canonicalSpectralReadout mass energy
          (c19ContinuumSpeed * momentum 0)
          (c19ContinuumSpeed * momentum 1)
          (c19ContinuumSpeed * momentum 2)
          (nativePhaseOfFrequencyAmplitudes energy q (fun _ => 0))) =
      -uniformNativePhaseDensity
        (nativePhaseOfFrequencyAmplitudes energy q (fun _ => 0)).1
        (nativePhaseOfFrequencyAmplitudes energy q (fun _ => 0)).2 ∧
    uniformNativePositiveAxisFlux momentum axis q =
      cubicalDiracCurrent axis
        (canonicalSpectralReadout mass energy
          (c19ContinuumSpeed * momentum 0)
          (c19ContinuumSpeed * momentum 1)
          (c19ContinuumSpeed * momentum 2)
          (nativePhaseOfFrequencyAmplitudes energy q (fun _ => 0))) +
        finiteC19CurrentRemainder momentum axis q := by
  have hread := canonical_spectral_readout_positive_phase mass energy
    (c19ContinuumSpeed * momentum 0)
    (c19ContinuumSpeed * momentum 1)
    (c19ContinuumSpeed * momentum 2) henergy q
  constructor
  · rw [hread]
    simpa [nativePhaseOfFrequencyAmplitudes] using
      normalized_density_is_positive_native_u1 mass energy
        (c19ContinuumSpeed * momentum 0)
        (c19ContinuumSpeed * momentum 1)
        (c19ContinuumSpeed * momentum 2) hpositive hshell q
  · rw [hread]
    exact native_plane_wave_flux_is_dirac_current_plus_remainder
      mass energy momentum hpositive hshell axis q

end
end LeanDirac.V2
