/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac011.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac010

/-!
# DIRAC-011: common frequency branches and native rest-mass selection

This gate adds no native field or action term. It uses the same cubical
embedding admitted by DIRAC-010. The two signs below are the two invariant
frequency graphs of the same second-order C19 symbol. Their exact
finite-lattice failure to be invariant is precisely the spatial remainder
already bounded in DIRAC-009.

The mass result is a uniqueness theorem. On the declared running family, the
native action selects the nonnegative rest frequency `chi0`. Any nonnegative
Dirac mass coefficient whose squared rest spectrum matches that native
frequency must therefore equal `chi0`; it is not supplied independently.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex

/-- The negative-frequency embedding of a cube amplitude into canonical states: the position is
`amplitude` and the velocity is `I` times `c19ContinuumDiracSymbol` applied to `amplitude`. -/
def c19NegativeFrequencyEmbedding
    (mass : ℂ) (momentum : LatticeMomentum)
    (amplitude : Cell8) : CubeCanonicalState where
  position := amplitude
  velocity := fun corner =>
    Complex.I * c19ContinuumDiracSymbol mass momentum amplitude corner

theorem c19_negative_embedding_position_intertwines_exactly
    (mass : ℂ) (momentum : LatticeMomentum) (amplitude : Cell8) :
    (c19ExactCanonicalVector mass momentum
      (c19NegativeFrequencyEmbedding mass momentum amplitude)).position =
    (c19NegativeFrequencyEmbedding mass momentum
      (fun corner => Complex.I *
        c19ContinuumDiracSymbol mass momentum amplitude corner)).position := by
  rfl

theorem c19_negative_embedding_velocity_residual_is_spatial_remainder
    (mass : ℂ) (momentum : LatticeMomentum) (amplitude : Cell8) :
    (c19ExactCanonicalVector mass momentum
        (c19NegativeFrequencyEmbedding mass momentum amplitude)).velocity =
      fun corner =>
        (c19NegativeFrequencyEmbedding mass momentum
          (fun site => Complex.I *
            c19ContinuumDiracSymbol mass momentum amplitude site)).velocity corner -
        (c19SpatialRemainder momentum : ℂ) * amplitude corner := by
  funext corner
  simp only [c19ExactCanonicalVector, c19NegativeFrequencyEmbedding]
  rw [c19_exact_scalar_symbol_splits]
  simp only [c19ContinuumDiracSymbol]
  rw [cube_dirac_symbol_scale, cube_dirac_symbol_square]
  rw [cube_scalar_scaled_is_c19_continuum_symbol]
  change
    -(c19ContinuumScalarSymbol mass momentum amplitude corner +
        (c19SpatialRemainder momentum : ℂ) * amplitude corner) =
      Complex.I *
          (Complex.I *
            c19ContinuumScalarSymbol mass momentum amplitude corner) -
        (c19SpatialRemainder momentum : ℂ) * amplitude corner
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The standard Dirac Hamiltonian on four-component vectors with momentum components
`(-c p₂, -c p₁, c p₀)`, where `c = c19ContinuumSpeed = √12` and `p = momentum`. -/
def standardC19Hamiltonian
    (mass : ℂ) (momentum : LatticeMomentum) (z : Cell4) : Cell4 :=
  standardDiracHamiltonian mass
    (-((c19ContinuumSpeed * momentum 2 : ℝ) : ℂ))
    (-((c19ContinuumSpeed * momentum 1 : ℝ) : ℂ))
    (((c19ContinuumSpeed * momentum 0 : ℝ) : ℂ)) z

/-- The zero lattice momentum. -/
def zeroLatticeMomentum : LatticeMomentum := fun _ => 0

theorem c19_continuum_symbol_eq_interpreted
    (mass : ℂ) (momentum : LatticeMomentum) (amplitude : Cell8) :
    c19ContinuumDiracSymbol mass momentum amplitude =
      interpretedCubeDiracHamiltonian mass
        (-((c19ContinuumSpeed * momentum 2 : ℝ) : ℂ))
        (-((c19ContinuumSpeed * momentum 1 : ℝ) : ℂ))
        (((c19ContinuumSpeed * momentum 0 : ℝ) : ℂ)) amplitude := by
  funext corner
  simp [c19ContinuumDiracSymbol, cubeDiracSymbol,
    interpretedCubeDiracHamiltonian, nativeCubeDiracSpatial,
    cubeIncidenceLinear]

theorem c19_continuum_intertwines_standard_minus
    (mass : ℂ) (momentum : LatticeMomentum) (z : Cell4) :
    c19ContinuumDiracSymbol mass momentum (cubeDiracEmbedMinus z) =
      cubeDiracEmbedMinus (standardC19Hamiltonian mass momentum z) := by
  rw [c19_continuum_symbol_eq_interpreted]
  exact interpreted_hamiltonian_intertwines_minus mass
      (-((c19ContinuumSpeed * momentum 2 : ℝ) : ℂ))
      (-((c19ContinuumSpeed * momentum 1 : ℝ) : ℂ))
      (((c19ContinuumSpeed * momentum 0 : ℝ) : ℂ)) z

theorem c19_continuum_intertwines_standard_plus
    (mass : ℂ) (momentum : LatticeMomentum) (z : Cell4) :
    c19ContinuumDiracSymbol mass momentum (cubeDiracEmbedPlus z) =
      cubeDiracEmbedPlus (standardC19Hamiltonian mass momentum z) := by
  rw [c19_continuum_symbol_eq_interpreted]
  exact interpreted_hamiltonian_intertwines_plus mass
      (-((c19ContinuumSpeed * momentum 2 : ℝ) : ℂ))
      (-((c19ContinuumSpeed * momentum 1 : ℝ) : ℂ))
      (((c19ContinuumSpeed * momentum 0 : ℝ) : ℂ)) z

theorem cube_dirac_embed_minus_scale (scalar : ℂ) (z : Cell4) :
    (fun corner => scalar * cubeDiracEmbedMinus z corner) =
      cubeDiracEmbedMinus (fun component => scalar * z component) := by
  funext corner
  fin_cases corner <;>
    simp [cubeDiracEmbedMinus, cubeEmbedMinus, standardToMinusCubeSpinor] <;>
    ring

theorem cube_dirac_embed_plus_scale (scalar : ℂ) (z : Cell4) :
    (fun corner => scalar * cubeDiracEmbedPlus z corner) =
      cubeDiracEmbedPlus (fun component => scalar * z component) := by
  funext corner
  fin_cases corner <;>
    simp [cubeDiracEmbedPlus, cubeEmbedPlus, standardToPlusCubeSpinor] <;>
    ring

theorem positive_frequency_uses_same_minus_embedding
    (mass : ℂ) (momentum : LatticeMomentum) (z : Cell4) :
    (c19PositiveFrequencyEmbedding mass momentum
      (cubeDiracEmbedMinus z)).velocity =
      cubeDiracEmbedMinus
        (fun component =>
          -Complex.I * standardC19Hamiltonian mass momentum z component) := by
  simp only [c19PositiveFrequencyEmbedding]
  rw [c19_continuum_intertwines_standard_minus]
  exact cube_dirac_embed_minus_scale (-Complex.I)
    (standardC19Hamiltonian mass momentum z)

theorem negative_frequency_uses_same_minus_embedding
    (mass : ℂ) (momentum : LatticeMomentum) (z : Cell4) :
    (c19NegativeFrequencyEmbedding mass momentum
      (cubeDiracEmbedMinus z)).velocity =
      cubeDiracEmbedMinus
        (fun component =>
          Complex.I * standardC19Hamiltonian mass momentum z component) := by
  simp only [c19NegativeFrequencyEmbedding]
  rw [c19_continuum_intertwines_standard_minus]
  exact cube_dirac_embed_minus_scale Complex.I
    (standardC19Hamiltonian mass momentum z)

theorem positive_frequency_uses_same_plus_embedding
    (mass : ℂ) (momentum : LatticeMomentum) (z : Cell4) :
    (c19PositiveFrequencyEmbedding mass momentum
      (cubeDiracEmbedPlus z)).velocity =
      cubeDiracEmbedPlus
        (fun component =>
          -Complex.I * standardC19Hamiltonian mass momentum z component) := by
  simp only [c19PositiveFrequencyEmbedding]
  rw [c19_continuum_intertwines_standard_plus]
  exact cube_dirac_embed_plus_scale (-Complex.I)
    (standardC19Hamiltonian mass momentum z)

theorem negative_frequency_uses_same_plus_embedding
    (mass : ℂ) (momentum : LatticeMomentum) (z : Cell4) :
    (c19NegativeFrequencyEmbedding mass momentum
      (cubeDiracEmbedPlus z)).velocity =
      cubeDiracEmbedPlus
        (fun component =>
          Complex.I * standardC19Hamiltonian mass momentum z component) := by
  simp only [c19NegativeFrequencyEmbedding]
  rw [c19_continuum_intertwines_standard_plus]
  exact cube_dirac_embed_plus_scale Complex.I
    (standardC19Hamiltonian mass momentum z)

theorem matching_nonnegative_rest_mass_is_chi0
    (A R omega mass : ℝ) (hA : A ≠ 0)
    (hdensity : A ^ 2 + R ^ 2 = chi0 ^ 2)
    (hpsi : omega ^ 2 * A = (R ^ 2 + A ^ 2) * A)
    (homega : 0 ≤ omega) (hmass : 0 ≤ mass)
    (hmatch : mass ^ 2 = omega ^ 2) :
    mass = chi0 := by
  have homega_eq : omega = chi0 :=
    prepared_running_rest_frequency_is_chi0 A R omega hA hdensity hpsi homega
  rw [homega_eq] at hmatch
  exact (sq_eq_sq₀ hmass (by norm_num [chi0])).mp hmatch

theorem standard_c19_rest_square_matches_native_frequency
    (A R omega : ℝ) (hA : A ≠ 0)
    (hdensity : A ^ 2 + R ^ 2 = chi0 ^ 2)
    (hpsi : omega ^ 2 * A = (R ^ 2 + A ^ 2) * A)
    (homega : 0 ≤ omega) (z : Cell4) :
    standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum
        (standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum z) =
      fun component => ((omega ^ 2 : ℝ) : ℂ) * z component := by
  have homega_eq : omega = chi0 :=
    prepared_running_rest_frequency_is_chi0 A R omega hA hdensity hpsi homega
  rw [homega_eq]
  simpa [standardC19Hamiltonian, zeroLatticeMomentum] using
    standard_dirac_hamiltonian_square (chi0 : ℂ) 0 0 0 z

/-- The collected results on the negative-frequency embedding and its spatial remainder, the
intertwining of `c19ContinuumDiracSymbol` with `standardC19Hamiltonian` under both cube
embeddings, and the uniqueness of the nonnegative rest mass `chi0`. -/
structure Dirac011Certificate : Prop where
  previousGate : Dirac010Certificate
  negativePositionBranch : ∀ mass momentum amplitude,
    (c19ExactCanonicalVector mass momentum
      (c19NegativeFrequencyEmbedding mass momentum amplitude)).position =
    (c19NegativeFrequencyEmbedding mass momentum
      (fun corner => Complex.I *
        c19ContinuumDiracSymbol mass momentum amplitude corner)).position
  negativeVelocityRemainder : ∀ mass momentum amplitude,
    (c19ExactCanonicalVector mass momentum
        (c19NegativeFrequencyEmbedding mass momentum amplitude)).velocity =
      fun corner =>
        (c19NegativeFrequencyEmbedding mass momentum
          (fun site => Complex.I *
            c19ContinuumDiracSymbol mass momentum amplitude site)).velocity corner -
        (c19SpatialRemainder momentum : ℂ) * amplitude corner
  standardContinuumCopies :
    (∀ mass momentum z,
      c19ContinuumDiracSymbol mass momentum (cubeDiracEmbedMinus z) =
        cubeDiracEmbedMinus (standardC19Hamiltonian mass momentum z)) ∧
    (∀ mass momentum z,
      c19ContinuumDiracSymbol mass momentum (cubeDiracEmbedPlus z) =
        cubeDiracEmbedPlus (standardC19Hamiltonian mass momentum z))
  commonFrequencyEmbedding :
    (∀ mass momentum z,
      (c19PositiveFrequencyEmbedding mass momentum
        (cubeDiracEmbedMinus z)).velocity =
        cubeDiracEmbedMinus
          (fun component => -Complex.I *
            standardC19Hamiltonian mass momentum z component)) ∧
    (∀ mass momentum z,
      (c19NegativeFrequencyEmbedding mass momentum
        (cubeDiracEmbedMinus z)).velocity =
        cubeDiracEmbedMinus
          (fun component => Complex.I *
            standardC19Hamiltonian mass momentum z component)) ∧
    (∀ mass momentum z,
      (c19PositiveFrequencyEmbedding mass momentum
        (cubeDiracEmbedPlus z)).velocity =
        cubeDiracEmbedPlus
          (fun component => -Complex.I *
            standardC19Hamiltonian mass momentum z component)) ∧
    (∀ mass momentum z,
      (c19NegativeFrequencyEmbedding mass momentum
        (cubeDiracEmbedPlus z)).velocity =
        cubeDiracEmbedPlus
          (fun component => Complex.I *
            standardC19Hamiltonian mass momentum z component))
  uniqueRestMass : ∀ A R omega mass, A ≠ 0 →
    A ^ 2 + R ^ 2 = chi0 ^ 2 →
    omega ^ 2 * A = (R ^ 2 + A ^ 2) * A →
    0 ≤ omega → 0 ≤ mass → mass ^ 2 = omega ^ 2 → mass = chi0
  restSquareMatchesNative : ∀ A R omega, A ≠ 0 →
    A ^ 2 + R ^ 2 = chi0 ^ 2 →
    omega ^ 2 * A = (R ^ 2 + A ^ 2) * A →
    0 ≤ omega → ∀ z,
      standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum
          (standardC19Hamiltonian (chi0 : ℂ) zeroLatticeMomentum z) =
        fun component => ((omega ^ 2 : ℝ) : ℂ) * z component

theorem dirac011_common_frequency_and_mass : Dirac011Certificate where
  previousGate := dirac010_native_operator_equals_standard_dirac
  negativePositionBranch := c19_negative_embedding_position_intertwines_exactly
  negativeVelocityRemainder :=
    c19_negative_embedding_velocity_residual_is_spatial_remainder
  standardContinuumCopies :=
    ⟨c19_continuum_intertwines_standard_minus,
      c19_continuum_intertwines_standard_plus⟩
  commonFrequencyEmbedding :=
    ⟨positive_frequency_uses_same_minus_embedding,
      negative_frequency_uses_same_minus_embedding,
      positive_frequency_uses_same_plus_embedding,
      negative_frequency_uses_same_plus_embedding⟩
  uniqueRestMass := matching_nonnegative_rest_mass_is_chi0
  restSquareMatchesNative := standard_c19_rest_square_matches_native_frequency

end
end LeanDirac
