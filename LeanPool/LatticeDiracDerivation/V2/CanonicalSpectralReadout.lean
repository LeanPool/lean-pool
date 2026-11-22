/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.PositiveFrequencyEmbedding

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
  let lower := cubicalSpinorOfBlocks 0 q
  have hr := positive_frequency_ratio_mul_denominator mass energy hdenom
  have hshift : normalizedNegativeFrequencyEmbedding mass energy px py pz q =
      fun component => -(positiveFrequencyRatio mass energy : ℂ) *
        (cubicalStandardHamiltonian mass px py pz lower component -
          (energy : ℂ) * lower component) := by
    dsimp only [lower]
    rw [cubical_standard_hamiltonian_blocks, positive_pauli_spatial_zero]
    funext component
    fin_cases component <;>
      simp [cubicalSpinorOfBlocks, normalizedNegativeFrequencyEmbedding, ← hr] <;> ring
  simp only [sub_eq_add_neg, neg_mul] at hshift
  rw [hshift]
  have hshellC : (mass : ℂ) ^ 2 + (px : ℂ) ^ 2 + (py : ℂ) ^ 2 + (pz : ℂ) ^ 2 =
      (energy : ℂ) ^ 2 := by exact_mod_cast hshell.symm
  have hsquare : (mass : ℂ) ^ 2 + (px : ℂ) ^ 2 + (py : ℂ) ^ 2 + (pz : ℂ) ^ 2 =
      (-(energy : ℂ)) ^ 2 := by simpa only [neg_sq] using hshellC
  simpa only [neg_mul] using cubical_standard_hamiltonian_shift mass px py pz
    (-(energy : ℂ)) (-(positiveFrequencyRatio mass energy : ℂ)) hsquare lower

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
      positive_pauli_spatial_apply_zero, positive_pauli_spatial_apply_one]

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
      positive_pauli_spatial_apply_zero, positive_pauli_spatial_apply_one]

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

theorem normalized_negative_frequency_embedding_scale
    (mass energy px py pz : ℝ) (scalar : ℂ) (q : UniformCell2) :
    normalizedNegativeFrequencyEmbedding mass energy px py pz
        (fun component => scalar * q component) =
      fun component => scalar *
        normalizedNegativeFrequencyEmbedding mass energy px py pz q component := by
  funext component
  fin_cases component <;>
    simp [normalizedNegativeFrequencyEmbedding, positive_pauli_spatial_apply_zero,
      positive_pauli_spatial_apply_one] <;>
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

private def pauliSpatialLinear (px py pz : ℝ) : UniformCell2 →ₗ[ℂ] UniformCell2 :=
  cubicalSpatialLowerLinear (px : ℂ) (py : ℂ) (pz : ℂ)

private theorem pauli_spatial_linear_apply (px py pz : ℝ) (position : UniformCell2) :
    pauliSpatialLinear px py pz position = positivePauliSpatial px py pz position :=
  (positive_pauli_spatial_is_cubical_lower px py pz position).symm

private def spectralBlock (spatial : UniformCell2 →ₗ[ℂ] UniformCell2)
    (diagonal offDiagonal : ℂ) (first second : UniformCell2) : UniformCell2 :=
  diagonal • first + offDiagonal • spatial second

private theorem spectralBlock_smul (spatial : UniformCell2 →ₗ[ℂ] UniformCell2)
    (a b c : ℂ) (u v : UniformCell2) :
    spectralBlock spatial a b (c • u) (c • v) = c • spectralBlock spatial a b u v := by
  simp only [spectralBlock, map_smul, smul_add, smul_comm a c, smul_comm b c]

private theorem spectralBlock_comp (px py pz : ℝ) (a b coefficient : ℂ)
    (hcoeff : a ^ 2 + b ^ 2 * ((px ^ 2 + py ^ 2 + pz ^ 2 : ℝ) : ℂ) = coefficient)
    (u v : UniformCell2) :
    let spatial := pauliSpatialLinear px py pz
    spectralBlock spatial a (-b) (spectralBlock spatial a b u v)
        (spectralBlock spatial a (-b) v u) = coefficient • u := by
  dsimp only
  have hSquare : pauliSpatialLinear px py pz (pauliSpatialLinear px py pz u) =
      ((px ^ 2 + py ^ 2 + pz ^ 2 : ℝ) : ℂ) • u :=
    positive_pauli_spatial_square px py pz u
  simp only [spectralBlock, map_add, map_smul, hSquare]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  linear_combination u i * hcoeff

private theorem spectralEmbedding_halves (mass energy px py pz : ℝ)
    (positive negative : UniformCell2) :
    let a : ℂ := positiveFrequencyScale mass energy
    let b : ℂ := positiveFrequencyRatio mass energy
    let spatial := pauliSpatialLinear px py pz
    let z : CubicalCell4 := fun component ↦
      normalizedPositiveFrequencyEmbedding mass energy px py pz positive component +
        normalizedNegativeFrequencyEmbedding mass energy px py pz negative component
    cubicalCell4Upper z = spectralBlock spatial a (-b) positive negative ∧
      cubicalCell4LowerHalf z = spectralBlock spatial a b negative positive := by
  constructor <;> funext component <;> fin_cases component <;>
    simp [cubicalCell4Upper, cubicalCell4LowerHalf, normalizedPositiveFrequencyEmbedding,
      normalizedNegativeFrequencyEmbedding, spectralBlock, pauli_spatial_linear_apply, add_comm]

private theorem spectralCoordinates_blocks (mass energy px py pz : ℝ) (z : CubicalCell4) :
    let a : ℂ := positiveFrequencyScale mass energy
    let b : ℂ := positiveFrequencyRatio mass energy
    let spatial := pauliSpatialLinear px py pz
    spectralPositiveCoordinate mass energy px py pz z =
      (energy : ℂ)⁻¹ • spectralBlock spatial a b (cubicalCell4Upper z) (cubicalCell4LowerHalf z) ∧
    spectralNegativeCoordinate mass energy px py pz z =
      (energy : ℂ)⁻¹ •
        spectralBlock spatial a (-b) (cubicalCell4LowerHalf z) (cubicalCell4Upper z) := by
  constructor <;> funext component <;>
    simp [spectralPositiveCoordinate, spectralNegativeCoordinate, spectralBlock,
      pauli_spatial_linear_apply, div_eq_mul_inv, mul_comm, add_comm]

private theorem spectralNormalization_complex (mass energy px py pz : ℝ)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) :
    (positiveFrequencyScale mass energy : ℂ) ^ 2 +
        (positiveFrequencyRatio mass energy : ℂ) ^ 2 *
          ((px ^ 2 + py ^ 2 + pz ^ 2 : ℝ) : ℂ) = (energy : ℂ) := by
  exact_mod_cast spectral_normalization_coefficient mass energy px py pz hpositive hshell

private theorem spectral_cancel_energy (energy : ℝ) (henergy : energy ≠ 0) (u : UniformCell2) :
    (energy : ℂ)⁻¹ • ((energy : ℂ) • u) = u := by
  have he : (energy : ℂ) ≠ 0 := by exact_mod_cast henergy
  rw [smul_smul, inv_mul_cancel₀ he, one_smul]

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
  let a : ℂ := positiveFrequencyScale mass energy
  let b : ℂ := positiveFrequencyRatio mass energy
  have hcoeff := spectralNormalization_complex mass energy px py pz hpositive hshell
  have hpos := spectralBlock_comp px py pz a (-b) energy (by simpa only [neg_sq] using hcoeff)
    positive negative
  have hneg := spectralBlock_comp px py pz a b energy hcoeff negative positive
  have hhalves := spectralEmbedding_halves mass energy px py pz positive negative
  let z : CubicalCell4 := fun component ↦
    normalizedPositiveFrequencyEmbedding mass energy px py pz positive component +
      normalizedNegativeFrequencyEmbedding mass energy px py pz negative component
  change spectralPositiveCoordinate mass energy px py pz z = positive ∧
    spectralNegativeCoordinate mass energy px py pz z = negative
  have hcoords := spectralCoordinates_blocks mass energy px py pz z
  constructor
  · rw [hcoords.1, hhalves.1, hhalves.2]
    simp only [a, b, neg_neg] at hpos
    rw [hpos, spectral_cancel_energy energy henergy]
  · rw [hcoords.2, hhalves.1, hhalves.2, hneg, spectral_cancel_energy energy henergy]

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
  let result : CubicalCell4 := fun component ↦
    normalizedPositiveFrequencyEmbedding mass energy px py pz
        (spectralPositiveCoordinate mass energy px py pz z) component +
      normalizedNegativeFrequencyEmbedding mass energy px py pz
        (spectralNegativeCoordinate mass energy px py pz z) component
  change result = z
  let a : ℂ := positiveFrequencyScale mass energy
  let b : ℂ := positiveFrequencyRatio mass energy
  have hcoeff := spectralNormalization_complex mass energy px py pz hpositive hshell
  have hpos := spectralBlock_comp px py pz a b energy hcoeff
    (cubicalCell4Upper z) (cubicalCell4LowerHalf z)
  have hneg := spectralBlock_comp px py pz a (-b) energy (by simpa only [neg_sq] using hcoeff)
    (cubicalCell4LowerHalf z) (cubicalCell4Upper z)
  simp only [a, b, neg_neg] at hneg
  have hhalves := spectralEmbedding_halves mass energy px py pz
    (spectralPositiveCoordinate mass energy px py pz z)
    (spectralNegativeCoordinate mass energy px py pz z)
  have hcoords := spectralCoordinates_blocks mass energy px py pz z
  have hupper : cubicalCell4Upper result = cubicalCell4Upper z := by
    rw [show cubicalCell4Upper result = _ from hhalves.1, hcoords.1, hcoords.2, spectralBlock_smul,
      hpos, spectral_cancel_energy energy henergy]
  have hlower : cubicalCell4LowerHalf result = cubicalCell4LowerHalf z := by
    rw [show cubicalCell4LowerHalf result = _ from hhalves.2, hcoords.1, hcoords.2,
      spectralBlock_smul, hneg, spectral_cancel_energy energy henergy]
  funext component
  fin_cases component
  · exact congrFun hupper 0
  · exact congrFun hupper 1
  · exact congrFun hlower 0
  · exact congrFun hlower 1

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


end
end LeanDirac.V2
