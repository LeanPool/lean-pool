/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.NativePhaseReadout

/-! # The normalized positive-frequency embedding

The two-component Pauli response gives a normalized embedding into the four-component
energy eigenspace. The action-derived phase readout gives its native preimage.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex
noncomputable section

/-- The two-coordinate spatial Pauli response obtained from the lower half of
the same standard cubical spatial operator. -/
def positivePauliSpatial (px py pz : ℝ)
    (q : UniformCell2) : UniformCell2
  | 0 => (pz : ℂ) * q 0 + ((px : ℂ) - I * (py : ℂ)) * q 1
  | _ => ((px : ℂ) + I * (py : ℂ)) * q 0 - (pz : ℂ) * q 1

theorem positive_pauli_spatial_is_cubical_lower
    (px py pz : ℝ) (q : UniformCell2) :
    positivePauliSpatial px py pz q =
      cubicalSpatialLower (px : ℂ) (py : ℂ) (pz : ℂ) q := by
  funext component
  fin_cases component <;>
    simp [positivePauliSpatial, cubicalSpatialLower,
      oriented_cubical_spatial_coordinates_eq_standard,
      cubicalUpperEmbedding, cubicalStandardSpatial,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ] <;>
    ring

theorem positive_pauli_spatial_square
    (px py pz : ℝ) (q : UniformCell2) :
    positivePauliSpatial px py pz
        (positivePauliSpatial px py pz q) =
      fun component =>
        ((px ^ 2 + py ^ 2 + pz ^ 2 : ℝ) : ℂ) * q component := by
  funext component
  fin_cases component <;>
    simp [positivePauliSpatial] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

/-- Positive real square-root normalization inherited from the native
mass-shell energy. -/
def positiveFrequencyScale (mass energy : ℝ) : ℝ :=
  Real.sqrt ((energy + mass) / 2)

theorem positive_frequency_scale_square
    (mass energy : ℝ) (h : 0 ≤ energy + mass) :
    positiveFrequencyScale mass energy ^ 2 = (energy + mass) / 2 := by
  exact Real.sq_sqrt (div_nonneg h (by norm_num))

/-- The coefficient of the momentum-dependent block in the positive-frequency embedding. -/
def positiveFrequencyRatio (mass energy : ℝ) : ℝ :=
  positiveFrequencyScale mass energy / (energy + mass)

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

/-- Canonical positive-frequency embedding of a two-channel amplitude.  Its
scale is fixed by simultaneous energy-eigenstate and U(1)-normalization
conditions below.  The explicit relation to the non-isometric full
phase-space readout is proved separately rather than assumed here. -/
def normalizedPositiveFrequencyEmbedding
    (mass energy px py pz : ℝ) (q : UniformCell2) : CubicalCell4
  | 0 => (positiveFrequencyScale mass energy : ℂ) * q 0
  | 1 => (positiveFrequencyScale mass energy : ℂ) * q 1
  | 2 => (positiveFrequencyRatio mass energy : ℂ) *
      positivePauliSpatial px py pz q 0
  | _ => (positiveFrequencyRatio mass energy : ℂ) *
      positivePauliSpatial px py pz q 1

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

theorem positive_frequency_ratio_mul_denominator (mass energy : ℝ)
    (hdenom : energy + mass ≠ 0) :
    (positiveFrequencyRatio mass energy : ℂ) * ((energy : ℂ) + (mass : ℂ)) =
      (positiveFrequencyScale mass energy : ℂ) := by
  exact_mod_cast (show positiveFrequencyRatio mass energy * (energy + mass) =
    positiveFrequencyScale mass energy from div_mul_cancel₀ _ hdenom)

theorem normalized_positive_frequency_is_energy_eigenstate
    (mass energy px py pz : ℝ)
    (hdenom : energy + mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (q : UniformCell2) :
    cubicalStandardHamiltonian (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
        (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
      fun component =>
        (energy : ℂ) *
          normalizedPositiveFrequencyEmbedding mass energy px py pz q component := by
  have hr := positive_frequency_ratio_mul_denominator mass energy hdenom
  have hshift : normalizedPositiveFrequencyEmbedding mass energy px py pz q =
      fun component => (positiveFrequencyRatio mass energy : ℂ) *
        (cubicalStandardHamiltonian mass px py pz (cubicalUpperEmbedding q) component +
          (energy : ℂ) * cubicalUpperEmbedding q component) := by
    funext component
    fin_cases component <;>
      simp [normalizedPositiveFrequencyEmbedding, cubicalUpperEmbedding, cubicalStandardHamiltonian,
        cubicalStandardSpatial, cubicalStandardBeta, cubicalStandardAlphaX, cubicalStandardAlphaY,
        cubicalStandardAlphaZ, positivePauliSpatial, ← hr] <;> ring_nf <;> simp
  rw [hshift]
  apply cubical_standard_hamiltonian_shift
  exact_mod_cast hshell.symm

/-- Restricted native-flow intertwiner.  The source amplitude is the position
of the positive-frequency native phase `(q,-iE q)`; applying one infinitesimal
native time step and then reading it out agrees with the cubical Dirac time
derivative. -/
theorem normalized_positive_frequency_intertwines_native_phase
    (mass energy px py pz : ℝ)
    (hdenom : energy + mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (q : UniformCell2) :
    normalizedPositiveFrequencyEmbedding mass energy px py pz
        (fun component => -I * (energy : ℂ) * q component) =
      fun component =>
        -I * cubicalStandardHamiltonian (mass : ℂ)
          (px : ℂ) (py : ℂ) (pz : ℂ)
          (normalizedPositiveFrequencyEmbedding
            mass energy px py pz q) component := by
  rw [normalized_positive_frequency_is_energy_eigenstate
    mass energy px py pz hdenom hshell q]
  simpa only [mul_assoc] using
    normalized_positive_frequency_embedding_scale mass energy px py pz (-I * (energy : ℂ)) q

/-- The concrete native phase whose full lossless action readout is the
normalized positive-frequency spinor.  This makes the change of native
amplitude explicit instead of identifying the spinor parameter with the raw
native position. -/
def normalizedEmbeddingNativePhase
    (mass energy px py pz : ℝ) (q : UniformCell2) :
    UniformTwoChannelPhase :=
  cubicalPhaseReadoutInverse (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
    (normalizedPositiveFrequencyEmbedding mass energy px py pz q)

theorem normalized_embedding_is_full_action_readout
    (mass energy px py pz : ℝ) (hmass : mass ≠ 0)
    (q : UniformCell2) :
    cubicalPhaseReadout (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
        (normalizedEmbeddingNativePhase mass energy px py pz q) =
      normalizedPositiveFrequencyEmbedding mass energy px py pz q := by
  exact cubical_phase_readout_right_inverse
    (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
    (by exact_mod_cast hmass) _

/-- The inverse-readout phase is not arbitrary: on the mass shell it is an
actual positive-frequency phase of the native Klein--Gordon generator. -/
theorem normalized_embedding_native_phase_is_positive_frequency
    (mass energy px py pz : ℝ)
    (hmass : mass ≠ 0)
    (hdenom : energy + mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (q : UniformCell2) :
    uniformTwoChannelKleinGordonVector
        (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
        (normalizedEmbeddingNativePhase mass energy px py pz q) =
      uniformTwoChannelScale (-I * (energy : ℂ))
        (normalizedEmbeddingNativePhase mass energy px py pz q) := by
  let phase := normalizedEmbeddingNativePhase mass energy px py pz q
  have hmassC : (mass : ℂ) ≠ 0 := by exact_mod_cast hmass
  have hread : cubicalPhaseReadout (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
      phase = normalizedPositiveFrequencyEmbedding mass energy px py pz q := by
    exact normalized_embedding_is_full_action_readout
      mass energy px py pz hmass q
  apply (cubical_phase_readout_injective
    (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ) hmassC)
  calc
    cubicalPhaseReadout (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
        (uniformTwoChannelKleinGordonVector
          (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ) phase) =
      fun component => -I * cubicalStandardHamiltonian
        (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
        (cubicalPhaseReadout (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
          phase) component :=
        cubical_phase_readout_intertwines
          (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ) hmassC phase
    _ = fun component => (-I * (energy : ℂ)) *
        normalizedPositiveFrequencyEmbedding mass energy px py pz q component := by
      rw [hread, normalized_positive_frequency_is_energy_eigenstate
        mass energy px py pz hdenom hshell q]
      funext component
      ring
    _ = cubicalPhaseReadout (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ)
        (uniformTwoChannelScale (-I * (energy : ℂ)) phase) := by
      rw [cubical_phase_readout_scale, hread]

/-- The normalized positive-frequency image is therefore not an auxiliary
spinor sector: every such vector has a concrete positive-frequency preimage
under the full action-derived phase-space readout. -/
theorem normalized_embedding_has_action_positive_preimage
    (mass energy px py pz : ℝ)
    (hmass : mass ≠ 0) (hdenom : energy + mass ≠ 0)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (q : UniformCell2) :
    ∃ phase : UniformTwoChannelPhase,
      cubicalPhaseReadout (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ) phase =
          normalizedPositiveFrequencyEmbedding mass energy px py pz q ∧
        uniformTwoChannelKleinGordonVector
            (mass : ℂ) (px : ℂ) (py : ℂ) (pz : ℂ) phase =
          uniformTwoChannelScale (-I * (energy : ℂ)) phase := by
  refine ⟨normalizedEmbeddingNativePhase mass energy px py pz q, ?_, ?_⟩
  · exact normalized_embedding_is_full_action_readout
      mass energy px py pz hmass q
  · exact normalized_embedding_native_phase_is_positive_frequency
      mass energy px py pz hmass hdenom hshell q

end
end LeanDirac.V2
