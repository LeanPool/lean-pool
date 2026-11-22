/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumCurrentBridge
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Positive-frequency density and current normalization

The lossless full phase-space readout is an operator equivalence, but it is not
an isometry of the native positive-frequency U(1) form at nonzero momentum.
This module therefore derives an isometric readout on the positive-frequency
native subspace itself and relates it explicitly back to the full readout.
It changes neither the action nor the full phase-space readout.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex BigOperators Filter Topology
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

theorem positive_pauli_spatial_density
    (px py pz : ℝ) (q : UniformCell2) :
    uniformCell2Density (positivePauliSpatial px py pz q) =
      (px ^ 2 + py ^ 2 + pz ^ 2) * uniformCell2Density q := by
  simp [uniformCell2Density, positivePauliSpatial,
    Complex.normSq, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ]
  ring

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

theorem normalized_positive_frequency_density_formula
    (mass energy px py pz : ℝ) (q : UniformCell2) :
    cubicalCell4Density
        (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
      positiveFrequencyScale mass energy ^ 2 * uniformCell2Density q +
        positiveFrequencyRatio mass energy ^ 2 *
          uniformCell2Density (positivePauliSpatial px py pz q) := by
  simp [cubicalCell4Density, normalizedPositiveFrequencyEmbedding,
    uniformCell2Density, Complex.normSq, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ]
  ring

theorem normalized_positive_frequency_current_formula
    (mass energy px py pz : ℝ) (q : UniformCell2) (axis : Fin 3) :
    cubicalDiracCurrent axis
        (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
      2 * c19ContinuumSpeed *
        positiveFrequencyScale mass energy * positiveFrequencyRatio mass energy *
        (fun axis : Fin 3 => if axis = 0 then px else if axis = 1 then py else pz) axis *
        uniformCell2Density q := by
  fin_cases axis <;>
    simp [cubicalDiracCurrent, cubicalVelocityOperator,
      cubicalCell4RealPair, normalizedPositiveFrequencyEmbedding,
      cubicalStandardAlphaX, cubicalStandardAlphaY, cubicalStandardAlphaZ,
      positivePauliSpatial, uniformCell2Density, Fin.sum_univ_succ,
      Complex.normSq, Complex.mul_re, Complex.mul_im] <;>
    ring

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
  have hratio : positiveFrequencyRatio mass energy * (energy + mass) =
      positiveFrequencyScale mass energy := by
    simp [positiveFrequencyRatio, hdenom]
  have hmassShell : mass * (energy + mass) +
        (px ^ 2 + py ^ 2 + pz ^ 2) = energy * (energy + mass) := by
    nlinarith
  have htop : mass * positiveFrequencyScale mass energy +
        (px ^ 2 + py ^ 2 + pz ^ 2) * positiveFrequencyRatio mass energy =
      energy * positiveFrequencyScale mass energy := by
    calc
      mass * positiveFrequencyScale mass energy +
          (px ^ 2 + py ^ 2 + pz ^ 2) * positiveFrequencyRatio mass energy =
        positiveFrequencyRatio mass energy *
          (mass * (energy + mass) + (px ^ 2 + py ^ 2 + pz ^ 2)) := by
            rw [← hratio]
            ring
      _ = positiveFrequencyRatio mass energy *
          (energy * (energy + mass)) := by rw [hmassShell]
      _ = energy * positiveFrequencyScale mass energy := by
        calc
          positiveFrequencyRatio mass energy * (energy * (energy + mass)) =
              energy * (positiveFrequencyRatio mass energy *
                (energy + mass)) := by ring
          _ = energy * positiveFrequencyScale mass energy := by rw [hratio]
  have hbottom : positiveFrequencyScale mass energy -
        mass * positiveFrequencyRatio mass energy =
      energy * positiveFrequencyRatio mass energy := by
    nlinarith [hratio]
  have htopC : (mass : ℂ) * (positiveFrequencyScale mass energy : ℂ) +
        ((px : ℂ) ^ 2 + (py : ℂ) ^ 2 + (pz : ℂ) ^ 2) *
          (positiveFrequencyRatio mass energy : ℂ) =
      (energy : ℂ) * (positiveFrequencyScale mass energy : ℂ) := by
    exact_mod_cast htop
  have hbottomC : (positiveFrequencyScale mass energy : ℂ) -
        (mass : ℂ) * (positiveFrequencyRatio mass energy : ℂ) =
      (energy : ℂ) * (positiveFrequencyRatio mass energy : ℂ) := by
    exact_mod_cast hbottom
  funext component
  fin_cases component
  · simp [cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      normalizedPositiveFrequencyEmbedding, positivePauliSpatial]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
    linear_combination (q 0) * htopC
  · simp [cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      normalizedPositiveFrequencyEmbedding, positivePauliSpatial]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
    linear_combination (q 1) * htopC
  · simp [cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      normalizedPositiveFrequencyEmbedding, positivePauliSpatial]
    ring_nf
    linear_combination
      ((pz : ℂ) * q 0 + ((px : ℂ) - I * (py : ℂ)) * q 1) * hbottomC
  · simp [cubicalStandardHamiltonian, cubicalStandardSpatial,
      cubicalStandardBeta, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ,
      normalizedPositiveFrequencyEmbedding, positivePauliSpatial]
    ring_nf
    linear_combination
      (((px : ℂ) + I * (py : ℂ)) * q 0 - (pz : ℂ) * q 1) * hbottomC

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
  funext component
  fin_cases component <;>
    simp [normalizedPositiveFrequencyEmbedding,
      positivePauliSpatial] <;>
    ring

/-- Scalar multiplication on the native two-layer phase space. -/
def uniformTwoChannelScale
    (scalar : ℂ) (phase : UniformTwoChannelPhase) :
    UniformTwoChannelPhase :=
  (fun component => scalar * phase.1 component,
    fun component => scalar * phase.2 component)

theorem cubical_phase_readout_scale
    (mass px py pz scalar : ℂ) (phase : UniformTwoChannelPhase) :
    cubicalPhaseReadout mass px py pz
        (uniformTwoChannelScale scalar phase) =
      fun component =>
        scalar * cubicalPhaseReadout mass px py pz phase component := by
  funext component
  fin_cases component <;>
    simp [uniformTwoChannelScale, cubicalPhaseReadout,
      cubicalPhaseLower, cubicalSpatialLower,
      oriented_cubical_spatial_coordinates_eq_standard,
      cubicalUpperEmbedding, cubicalStandardSpatial,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ] <;>
    ring

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

theorem normalized_positive_frequency_density
    (mass energy px py pz : ℝ)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (q : UniformCell2) :
    cubicalCell4Density
        (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
      energy * uniformCell2Density q := by
  have hdenom : energy + mass ≠ 0 := ne_of_gt hpositive
  have hscale := positive_frequency_scale_square mass energy (le_of_lt hpositive)
  have hcoefficient : positiveFrequencyScale mass energy ^ 2 +
        positiveFrequencyRatio mass energy ^ 2 *
          (px ^ 2 + py ^ 2 + pz ^ 2) = energy := by
    rw [positiveFrequencyRatio]
    field_simp [hdenom]
    rw [hscale]
    nlinarith
  rw [normalized_positive_frequency_density_formula]
  rw [positive_pauli_spatial_density]
  calc
    positiveFrequencyScale mass energy ^ 2 * uniformCell2Density q +
        positiveFrequencyRatio mass energy ^ 2 *
          ((px ^ 2 + py ^ 2 + pz ^ 2) * uniformCell2Density q) =
      (positiveFrequencyScale mass energy ^ 2 +
        positiveFrequencyRatio mass energy ^ 2 *
          (px ^ 2 + py ^ 2 + pz ^ 2)) * uniformCell2Density q := by ring
    _ = energy * uniformCell2Density q := by rw [hcoefficient]

/-- The normalized density is exactly the negative of the native U(1) phase
charge on positive-frequency data. -/
theorem normalized_density_is_positive_native_u1
    (mass energy px py pz : ℝ)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (q : UniformCell2) :
    cubicalCell4Density
        (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
      -uniformNativePhaseDensity q
        (fun component => -I * (energy : ℂ) * q component) := by
  rw [normalized_positive_frequency_density mass energy px py pz
    hpositive hshell]
  have hphase := uniform_native_u1_positive_frequency energy q
  change energy * uniformCell2Density q =
    -uniformNativePhaseDensity
      (uniformPositiveFrequencyPhase energy q).1
      (uniformPositiveFrequencyPhase energy q).2
  rw [hphase]
  ring

theorem normalized_positive_frequency_current
    (mass energy px py pz : ℝ)
    (hpositive : 0 < energy + mass)
    (_hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (q : UniformCell2) (axis : Fin 3) :
    cubicalDiracCurrent axis
        (normalizedPositiveFrequencyEmbedding mass energy px py pz q) =
      c19ContinuumSpeed *
        (fun axis : Fin 3 => if axis = 0 then px else if axis = 1 then py else pz) axis *
        uniformCell2Density q := by
  have hdenom : energy + mass ≠ 0 := ne_of_gt hpositive
  have hscale := positive_frequency_scale_square mass energy (le_of_lt hpositive)
  rw [normalized_positive_frequency_current_formula]
  rw [positiveFrequencyRatio]
  have hfactor : 2 * positiveFrequencyScale mass energy *
      (positiveFrequencyScale mass energy / (energy + mass)) = 1 := by
    field_simp [hdenom]
    nlinarith
  rw [show 2 * c19ContinuumSpeed * positiveFrequencyScale mass energy *
      (positiveFrequencyScale mass energy / (energy + mass)) =
      c19ContinuumSpeed by
    calc
      2 * c19ContinuumSpeed * positiveFrequencyScale mass energy *
          (positiveFrequencyScale mass energy / (energy + mass)) =
        c19ContinuumSpeed *
          (2 * positiveFrequencyScale mass energy *
            (positiveFrequencyScale mass energy / (energy + mass))) := by ring
      _ = c19ContinuumSpeed := by rw [hfactor]; ring]

/-! ## Exact finite-C19 native flux and its continuum remainder -/

/-- The value of the same two native transverse amplitudes at the endpoint
of a directed C19 bond in a plane wave.  This is a state construction, not a
new current definition. -/
def uniformCell2PlaneWaveNeighbor
    (momentum : LatticeMomentum) (direction : C19Neighbor)
    (q : UniformCell2) : UniformCell2 :=
  fun component => c19Character momentum direction * q component

/-- The scalar directed-bond current evaluated on an actual C19 plane wave. -/
theorem uniform_native_plane_wave_bond_current
    (weight : ℝ) (amplitude : ℂ) (momentum : LatticeMomentum)
    (direction : C19Neighbor) :
    uniformNativeOutwardBondCurrent weight amplitude
        (c19Character momentum direction * amplitude) =
      -2 * weight * Complex.normSq amplitude *
        Real.sin (c19PhaseAngle momentum direction) := by
  unfold uniformNativeOutwardBondCurrent uniformScalarPhasePair c19Character
  rw [show Complex.I * (c19PhaseAngle momentum direction : ℂ) =
      (c19PhaseAngle momentum direction : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I]
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im,
    Complex.sin_ofReal_re]
  ring

/-- Summing the literal native bond current over the two retained transverse
channels produces the density factor used by the four-component readout. -/
theorem uniform_cell2_plane_wave_bond_current
    (weight : ℝ) (momentum : LatticeMomentum)
    (direction : C19Neighbor) (q : UniformCell2) :
    (∑ component : Fin 2,
      uniformNativeOutwardBondCurrent weight (q component)
        (uniformCell2PlaneWaveNeighbor momentum direction q component)) =
      -2 * weight * Real.sin (c19PhaseAngle momentum direction) *
        uniformCell2Density q := by
  simp_rw [uniformCell2PlaneWaveNeighbor,
    uniform_native_plane_wave_bond_current]
  simp [uniformCell2Density, Fin.sum_univ_succ]
  ring

/-- The oriented positive-frequency flux obtained directly from the native
bond current.  The factor `-1/2` simultaneously removes the directed-bond
double count and uses the positive-charge convention `-rho_N`. -/
def uniformNativePositiveAxisFlux
    (momentum : LatticeMomentum) (axis : Fin 3)
    (q : UniformCell2) : ℝ :=
  -1 / 2 * ∑ direction : C19Neighbor,
    (c19Coord axis direction : ℝ) *
      (∑ component : Fin 2,
        uniformNativeOutwardBondCurrent (c19Weight direction) (q component)
          (uniformCell2PlaneWaveNeighbor momentum direction q component))

/-- Positive-frequency axis flux obtained from the directed native C19 bond
current.  The factor `-1/2` removes directed-bond double counting and flips
the sign together with the positive density `-rho_N`. -/
def finiteC19PositiveAxisFlux
    (momentum : LatticeMomentum) (axis : Fin 3)
    (q : UniformCell2) : ℝ :=
  (∑ direction : C19Neighbor,
      c19Weight direction * (c19Coord axis direction : ℝ) *
        Real.sin (c19PhaseAngle momentum direction)) *
    uniformCell2Density q

/-- The finite-C19 flux is not an independently postulated sine expression:
it is exactly the oriented sum of the action-derived native bond currents on
the same plane-wave state. -/
theorem uniform_native_positive_axis_flux_eq_finite_c19
    (momentum : LatticeMomentum) (axis : Fin 3)
    (q : UniformCell2) :
    uniformNativePositiveAxisFlux momentum axis q =
      finiteC19PositiveAxisFlux momentum axis q := by
  unfold uniformNativePositiveAxisFlux finiteC19PositiveAxisFlux
  simp_rw [uniform_cell2_plane_wave_bond_current]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro direction _
  ring

/-- The exact sine-minus-phase defect in the finite C19 current along one axis. -/
def finiteC19CurrentRemainder
    (momentum : LatticeMomentum) (axis : Fin 3)
    (q : UniformCell2) : ℝ :=
  (∑ direction : C19Neighbor,
      c19Weight direction * (c19Coord axis direction : ℝ) *
        (Real.sin (c19PhaseAngle momentum direction) -
          c19PhaseAngle momentum direction)) *
    uniformCell2Density q

/-- The absolute C19 weight carried by bonds crossing any one coordinate
axis is exactly twelve.  This is a property of the native six face and
twelve edge bonds, not an estimated continuum coefficient. -/
theorem c19_axis_absolute_weight_sum (axis : Fin 3) :
    ∑ direction : C19Neighbor,
      c19Weight direction * |(c19Coord axis direction : ℝ)| = 12 := by
  have count : ∀ a : Fin 3, (∑ d : C19Neighbor,
      (if d.val < 6 then 2 else 1) * (c19Coord a d).natAbs) = (12 : ℕ) := by
    -- The count consists of three finite sums over the eighteen stencil offsets.
    decide
  have castCount := congrArg (fun n : ℕ ↦ (n : ℝ)) (count axis)
  push_cast at castCount
  have absCast (n : ℤ) : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  simpa only [c19Weight, absCast] using castCount

/-- The sine error on every C19 bond is cubic in the momentum radius. -/
theorem c19_sine_phase_error_bound
    (momentum : LatticeMomentum) (radius : ℝ) (hradius : 0 ≤ radius)
    (hmomentum : ∀ axis, |momentum axis| ≤ radius)
    (direction : C19Neighbor) :
    |Real.sin (c19PhaseAngle momentum direction) -
        c19PhaseAngle momentum direction| ≤
      (4 / 3 : ℝ) * radius ^ 3 := by
  have hphase := c19_phase_angle_abs_le_two_mul
    momentum radius hradius hmomentum direction
  have hcube : |c19PhaseAngle momentum direction|^3 ≤
      (2 * radius) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hphase 3
  calc
    |Real.sin (c19PhaseAngle momentum direction) -
        c19PhaseAngle momentum direction| =
        |c19PhaseAngle momentum direction -
          Real.sin (c19PhaseAngle momentum direction)| := by
            rw [abs_sub_comm]
    _ ≤ |c19PhaseAngle momentum direction|^3 / 6 :=
      Real.abs_sub_sin_le _
    _ ≤ (2 * radius) ^ 3 / 6 := by nlinarith
    _ = (4 / 3 : ℝ) * radius ^ 3 := by ring

/-- Explicit finite-spacing bound for the action-derived C19 current.  The
constant sixteen comes from the exact axis weight twelve and the global
sine remainder bound on face/edge phases. -/
theorem finite_c19_current_remainder_bound
    (momentum : LatticeMomentum) (axis : Fin 3) (q : UniformCell2)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hmomentum : ∀ coordinate, |momentum coordinate| ≤ radius) :
    |finiteC19CurrentRemainder momentum axis q| ≤
      16 * radius ^ 3 * uniformCell2Density q := by
  have hdensity : 0 ≤ uniformCell2Density q := by
    exact Finset.sum_nonneg (fun component _ => Complex.normSq_nonneg _)
  unfold finiteC19CurrentRemainder
  rw [abs_mul, abs_of_nonneg hdensity]
  calc
    |∑ direction : C19Neighbor,
        c19Weight direction * (c19Coord axis direction : ℝ) *
          (Real.sin (c19PhaseAngle momentum direction) -
            c19PhaseAngle momentum direction)| * uniformCell2Density q ≤
      (∑ direction : C19Neighbor,
        |c19Weight direction * (c19Coord axis direction : ℝ) *
          (Real.sin (c19PhaseAngle momentum direction) -
            c19PhaseAngle momentum direction)|) *
          uniformCell2Density q := by
        exact mul_le_mul_of_nonneg_right
          (Finset.abs_sum_le_sum_abs _ _) hdensity
    _ ≤ (∑ direction : C19Neighbor,
        c19Weight direction * |(c19Coord axis direction : ℝ)| *
          ((4 / 3 : ℝ) * radius ^ 3)) * uniformCell2Density q := by
      apply mul_le_mul_of_nonneg_right _ hdensity
      apply Finset.sum_le_sum
      intro direction _
      rw [abs_mul, abs_mul,
        abs_of_pos (c19_weight_positive direction)]
      exact mul_le_mul_of_nonneg_left
        (c19_sine_phase_error_bound
          momentum radius hradius hmomentum direction)
        (mul_nonneg (le_of_lt (c19_weight_positive direction))
          (abs_nonneg _))
    _ = 16 * radius ^ 3 * uniformCell2Density q := by
      rw [← Finset.sum_mul, c19_axis_absolute_weight_sum]
      ring

/-- Along every fixed momentum ray, the explicit C19 current remainder
vanishes at low momentum. -/
theorem finite_c19_current_remainder_tends_to_zero
    (momentum : LatticeMomentum) (axis : Fin 3) (q : UniformCell2) :
    Tendsto
      (fun scale : ℝ =>
        finiteC19CurrentRemainder
          (fun coordinate => scale * momentum coordinate) axis q)
      (nhds 0) (nhds 0) := by
  have hcontinuous : Continuous (fun scale : ℝ =>
      finiteC19CurrentRemainder
        (fun coordinate => scale * momentum coordinate) axis q) := by
    unfold finiteC19CurrentRemainder c19PhaseAngle
    fun_prop
  have htend : Tendsto
      (fun scale : ℝ =>
        finiteC19CurrentRemainder
          (fun coordinate => scale * momentum coordinate) axis q)
      (nhds 0)
      (nhds (finiteC19CurrentRemainder
        (fun coordinate => (0 : ℝ) * momentum coordinate) axis q)) :=
    hcontinuous.continuousAt
  simpa [finiteC19CurrentRemainder, c19PhaseAngle] using htend

theorem c19_linear_axis_moment
    (momentum : LatticeMomentum) (axis : Fin 3) :
    ∑ direction : C19Neighbor,
        c19Weight direction * (c19Coord axis direction : ℝ) *
          c19PhaseAngle momentum direction =
      12 * momentum axis := by
  have hmoment (first second : Fin 3) :
      (∑ direction : C19Neighbor,
        c19Weight direction * (c19Coord first direction : ℝ) *
          (c19Coord second direction : ℝ)) =
        (c19SecondMoment first second : ℝ) := by
    simp_rw [c19_weight_is_integer_weight]
    exact_mod_cast rfl
  unfold c19PhaseAngle
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ x : Fin 3, ∑ direction : C19Neighbor,
      c19Weight direction * (c19Coord axis direction : ℝ) *
        (momentum x * (c19Coord x direction : ℝ))) =
        ∑ x : Fin 3, momentum x *
          (∑ direction : C19Neighbor,
            c19Weight direction * (c19Coord axis direction : ℝ) *
              (c19Coord x direction : ℝ)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro direction _
      ring
    _ = ∑ x : Fin 3, momentum x * c19SecondMoment axis x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hmoment]
    _ = 12 * momentum axis := by
      simp [c19_second_moment_isotropic]
      ring

theorem finite_c19_flux_is_continuum_plus_remainder
    (momentum : LatticeMomentum) (axis : Fin 3)
    (q : UniformCell2) :
    finiteC19PositiveAxisFlux momentum axis q =
      12 * momentum axis * uniformCell2Density q +
        finiteC19CurrentRemainder momentum axis q := by
  unfold finiteC19PositiveAxisFlux finiteC19CurrentRemainder
  rw [show (∑ direction : C19Neighbor,
      c19Weight direction * (c19Coord axis direction : ℝ) *
        Real.sin (c19PhaseAngle momentum direction)) =
      (∑ direction : C19Neighbor,
        c19Weight direction * (c19Coord axis direction : ℝ) *
          c19PhaseAngle momentum direction) +
      (∑ direction : C19Neighbor,
        c19Weight direction * (c19Coord axis direction : ℝ) *
          (Real.sin (c19PhaseAngle momentum direction) -
            c19PhaseAngle momentum direction)) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro direction _
      ring]
  rw [c19_linear_axis_moment]
  ring

/-- Literal same-state bridge: after the C19 momentum is converted to the
Hamiltonian momentum `p = c_eff k`, the action-derived native bond flux is
the positive-energy Dirac current plus the explicit finite-spacing sine
remainder.  No current formula is supplied independently on either side. -/
theorem native_plane_wave_flux_is_dirac_current_plus_remainder
    (mass energy : ℝ) (momentum : LatticeMomentum)
    (hpositive : 0 < energy + mass)
    (hshell : energy ^ 2 = mass ^ 2 +
      (c19ContinuumSpeed * momentum 0) ^ 2 +
      (c19ContinuumSpeed * momentum 1) ^ 2 +
      (c19ContinuumSpeed * momentum 2) ^ 2)
    (axis : Fin 3) (q : UniformCell2) :
    uniformNativePositiveAxisFlux momentum axis q =
      cubicalDiracCurrent axis
        (normalizedPositiveFrequencyEmbedding mass energy
          (c19ContinuumSpeed * momentum 0)
          (c19ContinuumSpeed * momentum 1)
          (c19ContinuumSpeed * momentum 2) q) +
        finiteC19CurrentRemainder momentum axis q := by
  rw [uniform_native_positive_axis_flux_eq_finite_c19,
    finite_c19_flux_is_continuum_plus_remainder,
    normalized_positive_frequency_current mass energy
      (c19ContinuumSpeed * momentum 0)
      (c19ContinuumSpeed * momentum 1)
      (c19ContinuumSpeed * momentum 2) hpositive hshell q axis]
  have hspeed := c19_continuum_speed_square
  have hspeedMul : c19ContinuumSpeed * c19ContinuumSpeed = 12 := by
    simpa [pow_two] using hspeed
  fin_cases axis <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, one_ne_zero,
      Fin.reduceEq, ↓reduceIte, add_left_inj, mul_eq_mul_right_iff] <;>
    rw [← hspeedMul] <;> ring_nf <;> simp

end
end LeanDirac.V2
