/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac010.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac009Closed

/-!
# DIRAC-010: downstream standard-Dirac identification

DIRAC-009 derives three equal-square, mutually anticommuting cubical
directions as the continuum square root of the ordinary C19 action symbol,
with the exact lattice remainder kept explicit. This file performs the
downstream change of basis needed to compare that derived algebra with the
usual four-component Dirac representation.

The standard operators below are explicit definitions, not assumptions used
upstream.  Both native flavor sectors are retained.  They use different
four-coordinate basis maps but the same signed permutation of spatial axes.
No mass value is supplied here: `mass` is an arbitrary coefficient multiplying
the native cube-parity grading.  Establishing that the native dynamics selects
a physical mass coefficient remains downstream work.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex

/-! ## The conventional Dirac representation, introduced only downstream -/

/-- The matrix `β = diag(1, 1, -1, -1)` of the standard Dirac representation, acting on
four-component vectors. -/
def standardDiracBeta (z : Cell4) : Cell4
  | 0 => z 0
  | 1 => z 1
  | 2 => -z 2
  | _ => -z 3

/-- The matrix `α_x` of the standard Dirac representation, which reverses the components:
`(z₀, z₁, z₂, z₃) ↦ (z₃, z₂, z₁, z₀)`. -/
def standardDiracAlphaX (z : Cell4) : Cell4
  | 0 => z 3
  | 1 => z 2
  | 2 => z 1
  | _ => z 0

/-- The matrix `α_y` of the standard Dirac representation:
`(z₀, z₁, z₂, z₃) ↦ (-i z₃, i z₂, -i z₁, i z₀)`. -/
def standardDiracAlphaY (z : Cell4) : Cell4
  | 0 => -I * z 3
  | 1 => I * z 2
  | 2 => -I * z 1
  | _ => I * z 0

/-- The matrix `α_z` of the standard Dirac representation:
`(z₀, z₁, z₂, z₃) ↦ (z₂, -z₃, z₀, -z₁)`. -/
def standardDiracAlphaZ (z : Cell4) : Cell4
  | 0 => z 2
  | 1 => -z 3
  | 2 => z 0
  | _ => -z 1

/-- The operator `px α_x + py α_y + pz α_z` built from `standardDiracAlphaX`,
`standardDiracAlphaY` and `standardDiracAlphaZ`. -/
def standardDiracSpatial
    (px py pz : ℂ) (z : Cell4) : Cell4 :=
  fun component =>
    px * standardDiracAlphaX z component +
      py * standardDiracAlphaY z component +
      pz * standardDiracAlphaZ z component

/-- The standard Dirac Hamiltonian `mass β + px α_x + py α_y + pz α_z` acting on four-component
vectors. -/
def standardDiracHamiltonian
    (mass px py pz : ℂ) (z : Cell4) : Cell4 :=
  fun component =>
    mass * standardDiracBeta z component +
      standardDiracSpatial px py pz z component

theorem standard_dirac_beta_square (z : Cell4) :
    standardDiracBeta (standardDiracBeta z) = z := by
  funext component
  fin_cases component <;> simp [standardDiracBeta]

theorem standard_dirac_alpha_x_square (z : Cell4) :
    standardDiracAlphaX (standardDiracAlphaX z) = z := by
  funext component
  fin_cases component <;> simp [standardDiracAlphaX]

theorem standard_dirac_alpha_y_square (z : Cell4) :
    standardDiracAlphaY (standardDiracAlphaY z) = z := by
  funext component
  fin_cases component <;>
    simp [standardDiracAlphaY] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;>
    ring

theorem standard_dirac_alpha_z_square (z : Cell4) :
    standardDiracAlphaZ (standardDiracAlphaZ z) = z := by
  funext component
  fin_cases component <;> simp [standardDiracAlphaZ]

theorem standard_dirac_alpha_xy_anticommute (z : Cell4) :
    standardDiracAlphaX (standardDiracAlphaY z) =
      fun component =>
        -standardDiracAlphaY (standardDiracAlphaX z) component := by
  funext component
  fin_cases component <;>
    simp [standardDiracAlphaX, standardDiracAlphaY]

theorem standard_dirac_alpha_xz_anticommute (z : Cell4) :
    standardDiracAlphaX (standardDiracAlphaZ z) =
      fun component =>
        -standardDiracAlphaZ (standardDiracAlphaX z) component := by
  funext component
  fin_cases component <;>
    simp [standardDiracAlphaX, standardDiracAlphaZ]

theorem standard_dirac_alpha_yz_anticommute (z : Cell4) :
    standardDiracAlphaY (standardDiracAlphaZ z) =
      fun component =>
        -standardDiracAlphaZ (standardDiracAlphaY z) component := by
  funext component
  fin_cases component <;>
    simp [standardDiracAlphaY, standardDiracAlphaZ]

theorem standard_dirac_beta_anticommutes_x (z : Cell4) :
    standardDiracBeta (standardDiracAlphaX z) =
      fun component =>
        -standardDiracAlphaX (standardDiracBeta z) component := by
  funext component
  fin_cases component <;>
    simp [standardDiracBeta, standardDiracAlphaX]

theorem standard_dirac_beta_anticommutes_y (z : Cell4) :
    standardDiracBeta (standardDiracAlphaY z) =
      fun component =>
        -standardDiracAlphaY (standardDiracBeta z) component := by
  funext component
  fin_cases component <;>
    simp [standardDiracBeta, standardDiracAlphaY]

theorem standard_dirac_beta_anticommutes_z (z : Cell4) :
    standardDiracBeta (standardDiracAlphaZ z) =
      fun component =>
        -standardDiracAlphaZ (standardDiracBeta z) component := by
  funext component
  fin_cases component <;>
    simp [standardDiracBeta, standardDiracAlphaZ]

theorem standard_dirac_hamiltonian_square
    (mass px py pz : ℂ) (z : Cell4) :
    standardDiracHamiltonian mass px py pz
        (standardDiracHamiltonian mass px py pz z) =
      fun component =>
        (mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) * z component := by
  funext component
  fin_cases component <;>
    simp [standardDiracHamiltonian, standardDiracSpatial,
      standardDiracBeta, standardDiracAlphaX, standardDiracAlphaY,
      standardDiracAlphaZ] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;>
    ring

/-! ## Basis maps derived for the two retained native flavor sectors -/

/-- The signed permutation `(z₀, z₁, z₂, z₃) ↦ (z₀, -z₃, z₂, z₁)`, changing standard Dirac
coordinates to the coordinates fed to `cubeEmbedMinus`. -/
def standardToMinusCubeSpinor (z : Cell4) : Cell4
  | 0 => z 0
  | 1 => -z 3
  | 2 => z 2
  | _ => z 1

/-- The signed permutation `(z₀, z₁, z₂, z₃) ↦ (-z₁, z₂, z₃, z₀)`, changing standard Dirac
coordinates to the coordinates fed to `cubeEmbedPlus`. -/
def standardToPlusCubeSpinor (z : Cell4) : Cell4
  | 0 => -z 1
  | 1 => z 2
  | 2 => z 3
  | _ => z 0

/-- The signed permutation `(z₀, z₁, z₂, z₃) ↦ (z₀, z₃, z₂, -z₁)`, the inverse of
`standardToMinusCubeSpinor`. -/
def minusCubeSpinorToStandard (z : Cell4) : Cell4
  | 0 => z 0
  | 1 => z 3
  | 2 => z 2
  | _ => -z 1

/-- The signed permutation `(z₀, z₁, z₂, z₃) ↦ (z₃, -z₀, z₁, z₂)`, the inverse of
`standardToPlusCubeSpinor`. -/
def plusCubeSpinorToStandard (z : Cell4) : Cell4
  | 0 => z 3
  | 1 => -z 0
  | 2 => z 1
  | _ => z 2

theorem minus_cube_basis_left_inverse (z : Cell4) :
    minusCubeSpinorToStandard (standardToMinusCubeSpinor z) = z := by
  funext component
  fin_cases component <;>
    simp [minusCubeSpinorToStandard, standardToMinusCubeSpinor]

theorem minus_cube_basis_right_inverse (z : Cell4) :
    standardToMinusCubeSpinor (minusCubeSpinorToStandard z) = z := by
  funext component
  fin_cases component <;>
    simp [minusCubeSpinorToStandard, standardToMinusCubeSpinor]

theorem plus_cube_basis_left_inverse (z : Cell4) :
    plusCubeSpinorToStandard (standardToPlusCubeSpinor z) = z := by
  funext component
  fin_cases component <;>
    simp [plusCubeSpinorToStandard, standardToPlusCubeSpinor]

theorem plus_cube_basis_right_inverse (z : Cell4) :
    standardToPlusCubeSpinor (plusCubeSpinorToStandard z) = z := by
  funext component
  fin_cases component <;>
    simp [plusCubeSpinorToStandard, standardToPlusCubeSpinor]

/-- The embedding of standard four-component vectors into eight-corner amplitudes, given by
`cubeEmbedMinus` composed with `standardToMinusCubeSpinor`. -/
def cubeDiracEmbedMinus (z : Cell4) : Cell8 :=
  cubeEmbedMinus (standardToMinusCubeSpinor z)

/-- The embedding of standard four-component vectors into eight-corner amplitudes, given by
`cubeEmbedPlus` composed with `standardToPlusCubeSpinor`. -/
def cubeDiracEmbedPlus (z : Cell4) : Cell8 :=
  cubeEmbedPlus (standardToPlusCubeSpinor z)

theorem cube_dirac_embed_minus_injective :
    Function.Injective cubeDiracEmbedMinus := by
  intro first second h
  have hcube : standardToMinusCubeSpinor first =
      standardToMinusCubeSpinor second :=
    cube_embed_minus_injective h
  have hstandard := congrArg minusCubeSpinorToStandard hcube
  simpa only [minus_cube_basis_left_inverse] using hstandard

theorem cube_dirac_embed_plus_injective :
    Function.Injective cubeDiracEmbedPlus := by
  intro first second h
  have hcube : standardToPlusCubeSpinor first =
      standardToPlusCubeSpinor second :=
    cube_embed_plus_injective h
  have hstandard := congrArg plusCubeSpinorToStandard hcube
  simpa only [plus_cube_basis_left_inverse] using hstandard

theorem cube_dirac_embed_minus_has_negative_flavor (z : Cell4) :
    cubeFlavor (cubeDiracEmbedMinus z) =
      fun corner => -cubeDiracEmbedMinus z corner := by
  exact cube_embed_minus_has_negative_flavor
    (standardToMinusCubeSpinor z)

theorem cube_dirac_embed_plus_has_positive_flavor (z : Cell4) :
    cubeFlavor (cubeDiracEmbedPlus z) = cubeDiracEmbedPlus z := by
  exact cube_embed_plus_has_positive_flavor
    (standardToPlusCubeSpinor z)

/-! ## Exact intertwining with the conventional alpha/beta operators -/

theorem cube_beta_intertwines_minus (z : Cell4) :
    cubeParityBeta (cubeDiracEmbedMinus z) =
      cubeDiracEmbedMinus (standardDiracBeta z) := by
  funext corner
  fin_cases corner <;>
    simp [cubeParityBeta, cubeDiracEmbedMinus, cubeEmbedMinus,
      standardToMinusCubeSpinor, standardDiracBeta,
      cellBit0, cellBit1, cellBit2]

theorem cube_beta_intertwines_plus (z : Cell4) :
    cubeParityBeta (cubeDiracEmbedPlus z) =
      cubeDiracEmbedPlus (standardDiracBeta z) := by
  funext corner
  fin_cases corner <;>
    simp [cubeParityBeta, cubeDiracEmbedPlus, cubeEmbedPlus,
      standardToPlusCubeSpinor, standardDiracBeta,
      cellBit0, cellBit1, cellBit2]

theorem cube_gamma0_intertwines_minus (z : Cell4) :
    cubeIncidenceGamma 0 (cubeDiracEmbedMinus z) =
      cubeDiracEmbedMinus (standardDiracAlphaZ z) := by
  funext corner
  fin_cases corner <;>
    simp [cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cubeDiracEmbedMinus, cubeEmbedMinus, standardToMinusCubeSpinor,
      standardDiracAlphaZ, cellFlip0]

theorem cube_gamma0_intertwines_plus (z : Cell4) :
    cubeIncidenceGamma 0 (cubeDiracEmbedPlus z) =
      cubeDiracEmbedPlus (standardDiracAlphaZ z) := by
  funext corner
  fin_cases corner <;>
    simp [cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cubeDiracEmbedPlus, cubeEmbedPlus, standardToPlusCubeSpinor,
      standardDiracAlphaZ, cellFlip0]

theorem cube_gamma1_intertwines_minus (z : Cell4) :
    cubeIncidenceGamma 1 (cubeDiracEmbedMinus z) =
      fun corner =>
        -cubeDiracEmbedMinus (standardDiracAlphaY z) corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cubeDiracEmbedMinus, cubeEmbedMinus, standardToMinusCubeSpinor,
      standardDiracAlphaY, cellFlip1, cellBit0] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;>
    ring

theorem cube_gamma1_intertwines_plus (z : Cell4) :
    cubeIncidenceGamma 1 (cubeDiracEmbedPlus z) =
      fun corner =>
        -cubeDiracEmbedPlus (standardDiracAlphaY z) corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cubeDiracEmbedPlus, cubeEmbedPlus, standardToPlusCubeSpinor,
      standardDiracAlphaY, cellFlip1, cellBit0] <;>
    ring_nf <;>
    rw [Complex.I_sq] <;>
    ring

theorem cube_gamma2_intertwines_minus (z : Cell4) :
    cubeIncidenceGamma 2 (cubeDiracEmbedMinus z) =
      fun corner =>
        -cubeDiracEmbedMinus (standardDiracAlphaX z) corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cubeDiracEmbedMinus, cubeEmbedMinus, standardToMinusCubeSpinor,
      standardDiracAlphaX, cellFlip2, cellBit0, cellBit1]

theorem cube_gamma2_intertwines_plus (z : Cell4) :
    cubeIncidenceGamma 2 (cubeDiracEmbedPlus z) =
      fun corner =>
        -cubeDiracEmbedPlus (standardDiracAlphaX z) corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cubeDiracEmbedPlus, cubeEmbedPlus, standardToPlusCubeSpinor,
      standardDiracAlphaX, cellFlip2, cellBit0, cellBit1]

/-- The operator `pz Γ₀ - py Γ₁ - px Γ₂` on eight-corner amplitudes, where `Γₐ` is
`cubeIncidenceGamma a`; that is, `cubeIncidenceLinear pz (-py) (-px)`. -/
def nativeCubeDiracSpatial
    (px py pz : ℂ) (amplitude : Cell8) : Cell8 :=
  cubeIncidenceLinear pz (-py) (-px) amplitude

/-!
This is a continuum interpretation operator, not a new native evolution law.
Its spatial part is the DIRAC-009 square-root readout of the base C19 action.
The `mass` coefficient is deliberately arbitrary because DIRAC-010 identifies
the cube-parity grading with standard beta but does not claim that the action
has selected a physical mass.
-/
/-- The operator `mass * cubeParityBeta + nativeCubeDiracSpatial px py pz` on eight-corner
amplitudes, with an arbitrary complex coefficient `mass`. -/
def interpretedCubeDiracHamiltonian
    (mass px py pz : ℂ) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    mass * cubeParityBeta amplitude corner +
      nativeCubeDiracSpatial px py pz amplitude corner

theorem native_spatial_intertwines_minus
    (px py pz : ℂ) (z : Cell4) :
    nativeCubeDiracSpatial px py pz (cubeDiracEmbedMinus z) =
      cubeDiracEmbedMinus (standardDiracSpatial px py pz z) := by
  unfold nativeCubeDiracSpatial cubeIncidenceLinear
  funext corner
  rw [congrFun (cube_gamma0_intertwines_minus z) corner,
    congrFun (cube_gamma1_intertwines_minus z) corner,
    congrFun (cube_gamma2_intertwines_minus z) corner]
  fin_cases corner <;>
    simp [cubeDiracEmbedMinus,
      cubeEmbedMinus, standardToMinusCubeSpinor, standardDiracSpatial,
      standardDiracAlphaX, standardDiracAlphaY, standardDiracAlphaZ] <;>
    ring

theorem native_spatial_intertwines_plus
    (px py pz : ℂ) (z : Cell4) :
    nativeCubeDiracSpatial px py pz (cubeDiracEmbedPlus z) =
      cubeDiracEmbedPlus (standardDiracSpatial px py pz z) := by
  unfold nativeCubeDiracSpatial cubeIncidenceLinear
  funext corner
  rw [congrFun (cube_gamma0_intertwines_plus z) corner,
    congrFun (cube_gamma1_intertwines_plus z) corner,
    congrFun (cube_gamma2_intertwines_plus z) corner]
  fin_cases corner <;>
    simp [cubeDiracEmbedPlus,
      cubeEmbedPlus, standardToPlusCubeSpinor, standardDiracSpatial,
      standardDiracAlphaX, standardDiracAlphaY, standardDiracAlphaZ] <;>
    ring

theorem interpreted_hamiltonian_intertwines_minus
    (mass px py pz : ℂ) (z : Cell4) :
    interpretedCubeDiracHamiltonian mass px py pz (cubeDiracEmbedMinus z) =
      cubeDiracEmbedMinus
        (standardDiracHamiltonian mass px py pz z) := by
  funext corner
  rw [show
      interpretedCubeDiracHamiltonian mass px py pz
          (cubeDiracEmbedMinus z) corner =
        mass * cubeParityBeta (cubeDiracEmbedMinus z) corner +
          nativeCubeDiracSpatial px py pz
            (cubeDiracEmbedMinus z) corner by rfl]
  rw [congrFun (cube_beta_intertwines_minus z) corner,
    congrFun (native_spatial_intertwines_minus px py pz z) corner]
  fin_cases corner <;>
    simp [cubeDiracEmbedMinus, cubeEmbedMinus,
      standardToMinusCubeSpinor, standardDiracHamiltonian,
      standardDiracBeta, standardDiracSpatial,
      standardDiracAlphaX, standardDiracAlphaY, standardDiracAlphaZ] <;>
    ring

theorem interpreted_hamiltonian_intertwines_plus
    (mass px py pz : ℂ) (z : Cell4) :
    interpretedCubeDiracHamiltonian mass px py pz (cubeDiracEmbedPlus z) =
      cubeDiracEmbedPlus
        (standardDiracHamiltonian mass px py pz z) := by
  funext corner
  rw [show
      interpretedCubeDiracHamiltonian mass px py pz
          (cubeDiracEmbedPlus z) corner =
        mass * cubeParityBeta (cubeDiracEmbedPlus z) corner +
          nativeCubeDiracSpatial px py pz
            (cubeDiracEmbedPlus z) corner by rfl]
  rw [congrFun (cube_beta_intertwines_plus z) corner,
    congrFun (native_spatial_intertwines_plus px py pz z) corner]
  fin_cases corner <;>
    simp [cubeDiracEmbedPlus, cubeEmbedPlus,
      standardToPlusCubeSpinor, standardDiracHamiltonian,
      standardDiracBeta, standardDiracSpatial,
      standardDiracAlphaX, standardDiracAlphaY, standardDiracAlphaZ] <;>
    ring

/-- The bundle of results of this file: the `Dirac009ClosedCertificate`, the Clifford relations of
the standard Dirac matrices and of `cubeParityBeta`, injectivity of the two embeddings, and their
intertwining of the cube operators with `standardDiracBeta` and `standardDiracHamiltonian`. -/
structure Dirac010Certificate : Prop where
  previousGate : Dirac009ClosedCertificate
  standardBetaSquare : ∀ z,
    standardDiracBeta (standardDiracBeta z) = z
  standardAlphaSquares :
    (∀ z, standardDiracAlphaX (standardDiracAlphaX z) = z) ∧
      (∀ z, standardDiracAlphaY (standardDiracAlphaY z) = z) ∧
      (∀ z, standardDiracAlphaZ (standardDiracAlphaZ z) = z)
  standardAlphaAnticommutation :
    (∀ z, standardDiracAlphaX (standardDiracAlphaY z) =
      fun component =>
        -standardDiracAlphaY (standardDiracAlphaX z) component) ∧
    (∀ z, standardDiracAlphaX (standardDiracAlphaZ z) =
      fun component =>
        -standardDiracAlphaZ (standardDiracAlphaX z) component) ∧
    (∀ z, standardDiracAlphaY (standardDiracAlphaZ z) =
      fun component =>
        -standardDiracAlphaZ (standardDiracAlphaY z) component)
  standardBetaAnticommutation :
    (∀ z, standardDiracBeta (standardDiracAlphaX z) =
      fun component =>
        -standardDiracAlphaX (standardDiracBeta z) component) ∧
    (∀ z, standardDiracBeta (standardDiracAlphaY z) =
      fun component =>
        -standardDiracAlphaY (standardDiracBeta z) component) ∧
    (∀ z, standardDiracBeta (standardDiracAlphaZ z) =
      fun component =>
        -standardDiracAlphaZ (standardDiracBeta z) component)
  standardHamiltonianSquare : ∀ mass px py pz z,
    standardDiracHamiltonian mass px py pz
        (standardDiracHamiltonian mass px py pz z) =
      fun component =>
        (mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) * z component
  nativeGradingSquare : ∀ amplitude,
    cubeParityBeta (cubeParityBeta amplitude) = amplitude
  nativeGradingAnticommutation : ∀ axis amplitude,
    cubeParityBeta (cubeIncidenceGamma axis amplitude) =
      fun corner =>
        -cubeIncidenceGamma axis (cubeParityBeta amplitude) corner
  nativeFlavorPreservesGrading : ∀ amplitude,
    cubeFlavor (cubeParityBeta amplitude) =
      cubeParityBeta (cubeFlavor amplitude)
  retainedCopies :
    Function.Injective cubeDiracEmbedMinus ∧
      Function.Injective cubeDiracEmbedPlus
  gradingIntertwines :
    (∀ z, cubeParityBeta (cubeDiracEmbedMinus z) =
      cubeDiracEmbedMinus (standardDiracBeta z)) ∧
    (∀ z, cubeParityBeta (cubeDiracEmbedPlus z) =
      cubeDiracEmbedPlus (standardDiracBeta z))
  interpretedHamiltonianIntertwines :
    (∀ mass px py pz z,
      interpretedCubeDiracHamiltonian mass px py pz
          (cubeDiracEmbedMinus z) =
        cubeDiracEmbedMinus
          (standardDiracHamiltonian mass px py pz z)) ∧
    (∀ mass px py pz z,
      interpretedCubeDiracHamiltonian mass px py pz
          (cubeDiracEmbedPlus z) =
        cubeDiracEmbedPlus
          (standardDiracHamiltonian mass px py pz z))

theorem dirac010_native_operator_equals_standard_dirac :
    Dirac010Certificate where
  previousGate := dirac009_closed_native_clifford
  standardBetaSquare := standard_dirac_beta_square
  standardAlphaSquares :=
    ⟨standard_dirac_alpha_x_square,
      standard_dirac_alpha_y_square,
      standard_dirac_alpha_z_square⟩
  standardAlphaAnticommutation :=
    ⟨standard_dirac_alpha_xy_anticommute,
      standard_dirac_alpha_xz_anticommute,
      standard_dirac_alpha_yz_anticommute⟩
  standardBetaAnticommutation :=
    ⟨standard_dirac_beta_anticommutes_x,
      standard_dirac_beta_anticommutes_y,
      standard_dirac_beta_anticommutes_z⟩
  standardHamiltonianSquare := standard_dirac_hamiltonian_square
  nativeGradingSquare := cube_parity_beta_square
  nativeGradingAnticommutation := cube_parity_beta_anticommutes
  nativeFlavorPreservesGrading := cube_flavor_commutes_beta
  retainedCopies :=
    ⟨cube_dirac_embed_minus_injective, cube_dirac_embed_plus_injective⟩
  gradingIntertwines :=
    ⟨cube_beta_intertwines_minus, cube_beta_intertwines_plus⟩
  interpretedHamiltonianIntertwines :=
    ⟨interpreted_hamiltonian_intertwines_minus,
      interpreted_hamiltonian_intertwines_plus⟩

end
end LeanDirac
