/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Cubical Clifford algebra without a prepared field background

This module constructs the three spatial Clifford generators and the parity
grading from the oriented incidence geometry of one abstract cube.  It does
not import the native-field action, the prepared tetrahedral rays, or any
previous Dirac stage.  Conventional four-component matrices occur only
downstream, as coordinates on the two rank-four flavor sectors of the
eight-corner incidence representation.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section
open Complex

/-- The eight corners, ordered so that the three coordinate bits index the cube. -/
abbrev CubicalCorner := Fin 8

/-- A complex amplitude on each corner of the cube. -/
abbrev CubicalCell8 := CubicalCorner → ℂ

/-- The four complex coordinates of a standard free Dirac spinor. -/
abbrev CubicalCell4 := Fin 4 → ℂ

/-! ## Oriented cube incidence -/

/-- Flip the first cube coordinate, across the faces normal to axis zero. -/
def cubicalFlip0 : CubicalCorner → CubicalCorner
  | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 7
  | 4 => 0 | 5 => 1 | 6 => 2 | _ => 3

/-- Flip the second cube coordinate, across the faces normal to axis one. -/
def cubicalFlip1 : CubicalCorner → CubicalCorner
  | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1
  | 4 => 6 | 5 => 7 | 6 => 4 | _ => 5

/-- Flip the third cube coordinate, across the faces normal to axis two. -/
def cubicalFlip2 : CubicalCorner → CubicalCorner
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2
  | 4 => 5 | 5 => 4 | 6 => 7 | _ => 6

/-- The first cube coordinate in the corner ordering. -/
def cubicalBit0 : CubicalCorner → Nat
  | 0 | 1 | 2 | 3 => 0
  | _ => 1

/-- The second cube coordinate in the corner ordering. -/
def cubicalBit1 : CubicalCorner → Nat
  | 0 | 1 | 4 | 5 => 0
  | _ => 1

/-- The third cube coordinate in the corner ordering. -/
def cubicalBit2 : CubicalCorner → Nat
  | 0 | 2 | 4 | 6 => 0
  | _ => 1

/-- Flip the coordinate specified by an axis of the cube. -/
def cubicalFlip (axis : Fin 3) : CubicalCorner → CubicalCorner :=
  match axis with
  | 0 => cubicalFlip0
  | 1 => cubicalFlip1
  | _ => cubicalFlip2

/-- Integer Koszul incidence sign from the lower-index bits. -/
def cubicalIncidenceSignInteger (axis : Fin 3) (corner : CubicalCorner) : ℤ :=
  match axis with
  | 0 => 1
  | 1 => if cubicalBit0 corner = 0 then 1 else -1
  | _ => if (cubicalBit0 corner + cubicalBit1 corner) % 2 = 0 then 1 else -1

/-- The Koszul incidence sign acting on complex amplitudes. -/
def cubicalIncidenceSign (axis : Fin 3) (corner : CubicalCorner) : ℂ :=
  (cubicalIncidenceSignInteger axis corner : ℂ)

/-- The signed coordinate flip representing one oriented incidence generator. -/
def cubicalGamma (axis : Fin 3) (amplitude : CubicalCell8) : CubicalCell8 :=
  fun corner => cubicalIncidenceSign axis corner *
    amplitude (cubicalFlip axis corner)

/-- The cube parity grading, acting by the parity of the sum of the coordinate bits. -/
def cubicalBeta (amplitude : CubicalCell8) : CubicalCell8 := fun corner =>
  if (cubicalBit0 corner + cubicalBit1 corner + cubicalBit2 corner) % 2 = 0 then
    amplitude corner
  else
    -amplitude corner

theorem cubical_gamma_square (axis : Fin 3) (amplitude : CubicalCell8) :
    cubicalGamma axis (cubicalGamma axis amplitude) = amplitude := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalGamma, cubicalIncidenceSign, cubicalIncidenceSignInteger, cubicalFlip,
      cubicalFlip0, cubicalFlip1, cubicalFlip2, cubicalBit0, cubicalBit1]

private theorem cubical_flips_commute :
    ∀ (axis other : Fin 3) (corner : CubicalCorner),
      cubicalFlip other (cubicalFlip axis corner) =
        cubicalFlip axis (cubicalFlip other corner) := by
  decide

private theorem cubical_crossing_sign_anticommutes :
    ∀ (axis other : Fin 3), axis ≠ other → ∀ corner,
      cubicalIncidenceSignInteger axis corner *
        cubicalIncidenceSignInteger other (cubicalFlip axis corner) =
      -(cubicalIncidenceSignInteger other corner *
        cubicalIncidenceSignInteger axis (cubicalFlip other corner)) := by
  decide

theorem cubical_gamma_anticommute
    (axis other : Fin 3) (haxis : axis ≠ other) (amplitude : CubicalCell8) :
    cubicalGamma axis (cubicalGamma other amplitude) =
      fun corner => -cubicalGamma other (cubicalGamma axis amplitude) corner := by
  funext corner
  have signs := congrArg (fun sign : ℤ => (sign : ℂ))
    (cubical_crossing_sign_anticommutes axis other haxis corner)
  simp only [Int.cast_mul, Int.cast_neg] at signs
  change cubicalIncidenceSign axis corner * cubicalIncidenceSign other (cubicalFlip axis corner) =
    -(cubicalIncidenceSign other corner * cubicalIncidenceSign axis (cubicalFlip other corner))
    at signs
  simp only [cubicalGamma, ← mul_assoc, cubical_flips_commute axis other corner, signs, neg_mul]

theorem cubical_beta_square (amplitude : CubicalCell8) :
    cubicalBeta (cubicalBeta amplitude) = amplitude := by
  funext corner
  fin_cases corner <;>
    simp [cubicalBeta, cubicalBit0, cubicalBit1, cubicalBit2]

theorem cubical_beta_anticommutes
    (axis : Fin 3) (amplitude : CubicalCell8) :
    cubicalBeta (cubicalGamma axis amplitude) =
      fun corner => -cubicalGamma axis (cubicalBeta amplitude) corner := by
  fin_cases axis
  all_goals
    funext corner
    fin_cases corner <;>
      simp [cubicalBeta, cubicalGamma, cubicalIncidenceSign,
      cubicalIncidenceSignInteger, cubicalFlip,
        cubicalFlip0, cubicalFlip1, cubicalFlip2,
        cubicalBit0, cubicalBit1, cubicalBit2]

/-- A linear combination of the three oriented incidence generators. -/
def cubicalIncidenceLinear
    (k0 k1 k2 : ℂ) (amplitude : CubicalCell8) : CubicalCell8 := fun corner =>
  k0 * cubicalGamma 0 amplitude corner +
    k1 * cubicalGamma 1 amplitude corner +
    k2 * cubicalGamma 2 amplitude corner

theorem cubical_incidence_linear_square
    (k0 k1 k2 : ℂ) (amplitude : CubicalCell8) :
    cubicalIncidenceLinear k0 k1 k2
        (cubicalIncidenceLinear k0 k1 k2 amplitude) =
      fun corner => (k0 ^ 2 + k1 ^ 2 + k2 ^ 2) * amplitude corner := by
  have hlinear (axis : Fin 3) :
      cubicalGamma axis (cubicalIncidenceLinear k0 k1 k2 amplitude) =
        fun corner => k0 * cubicalGamma axis (cubicalGamma 0 amplitude) corner +
          k1 * cubicalGamma axis (cubicalGamma 1 amplitude) corner +
          k2 * cubicalGamma axis (cubicalGamma 2 amplitude) corner := by
    funext corner
    simp only [cubicalIncidenceLinear, cubicalGamma]
    ring
  funext corner
  change k0 * cubicalGamma 0 (cubicalIncidenceLinear k0 k1 k2 amplitude) corner +
    k1 * cubicalGamma 1 (cubicalIncidenceLinear k0 k1 k2 amplitude) corner +
    k2 * cubicalGamma 2 (cubicalIncidenceLinear k0 k1 k2 amplitude) corner = _
  simp only [hlinear, cubical_gamma_square,
    cubical_gamma_anticommute 0 1 (by decide) amplitude,
    cubical_gamma_anticommute 0 2 (by decide) amplitude,
    cubical_gamma_anticommute 1 2 (by decide) amplitude]
  ring

/-! ## The two geometry-derived rank-four flavor sectors -/

/-- The orientation sign in the composition of the two flips defining the flavor operator. -/
def cubicalFlavorSign (corner : CubicalCorner) : ℝ :=
  if cubicalBit2 corner % 2 = 0 then 1 else -1

/-- The involution whose eigenspaces give the two four-component sectors. -/
def cubicalFlavor (amplitude : CubicalCell8) : CubicalCell8 := fun corner =>
  I * (cubicalFlavorSign corner : ℂ) *
    amplitude (cubicalFlip1 (cubicalFlip2 corner))

theorem cubical_flavor_involution (amplitude : CubicalCell8) :
    cubicalFlavor (cubicalFlavor amplitude) = amplitude := by
  funext corner
  fin_cases corner <;>
    simp [cubicalFlavor, cubicalFlavorSign, cubicalFlip1, cubicalFlip2,
      cubicalBit2] <;> ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cubical_flavor_commutes_gamma
    (axis : Fin 3) (amplitude : CubicalCell8) :
    cubicalFlavor (cubicalGamma axis amplitude) =
      cubicalGamma axis (cubicalFlavor amplitude) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalFlavor, cubicalFlavorSign, cubicalGamma,
      cubicalIncidenceSign, cubicalIncidenceSignInteger, cubicalFlip, cubicalFlip0, cubicalFlip1,
      cubicalFlip2, cubicalBit0, cubicalBit1, cubicalBit2]

theorem cubical_flavor_commutes_beta (amplitude : CubicalCell8) :
    cubicalFlavor (cubicalBeta amplitude) =
      cubicalBeta (cubicalFlavor amplitude) := by
  funext corner
  fin_cases corner <;>
    simp [cubicalFlavor, cubicalFlavorSign, cubicalBeta,
      cubicalFlip1, cubicalFlip2, cubicalBit0, cubicalBit1, cubicalBit2]

/-- Extend four coordinates to an amplitude in the negative flavor eigenspace. -/
def cubicalEmbedMinus (z : CubicalCell4) : CubicalCell8
  | 0 => z 0 | 1 => z 1 | 2 => -I * z 1 | 3 => I * z 0
  | 4 => z 2 | 5 => z 3 | 6 => -I * z 3 | _ => I * z 2

/-- Extend four coordinates to an amplitude in the positive flavor eigenspace. -/
def cubicalEmbedPlus (z : CubicalCell4) : CubicalCell8
  | 0 => z 0 | 1 => z 1 | 2 => I * z 1 | 3 => -I * z 0
  | 4 => z 2 | 5 => z 3 | 6 => I * z 3 | _ => -I * z 2

theorem cubical_embed_minus_injective : Function.Injective cubicalEmbedMinus := by
  intro first second h
  funext component
  fin_cases component
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 4
  · exact congrFun h 5

theorem cubical_embed_plus_injective : Function.Injective cubicalEmbedPlus := by
  intro first second h
  funext component
  fin_cases component
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 4
  · exact congrFun h 5

theorem cubical_embed_minus_has_negative_flavor (z : CubicalCell4) :
    cubicalFlavor (cubicalEmbedMinus z) =
      fun corner => -cubicalEmbedMinus z corner := by
  funext corner
  fin_cases corner <;>
    simp [cubicalFlavor, cubicalFlavorSign, cubicalEmbedMinus,
      cubicalFlip1, cubicalFlip2, cubicalBit2] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cubical_embed_plus_has_positive_flavor (z : CubicalCell4) :
    cubicalFlavor (cubicalEmbedPlus z) = cubicalEmbedPlus z := by
  funext corner
  fin_cases corner <;>
    simp [cubicalFlavor, cubicalFlavorSign, cubicalEmbedPlus,
      cubicalFlip1, cubicalFlip2, cubicalBit2] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

/-! ## Downstream standard four-component coordinates -/

/-- The mass matrix in standard four-component coordinates. -/
def cubicalStandardBeta (z : CubicalCell4) : CubicalCell4
  | 0 => z 0 | 1 => z 1 | 2 => -z 2 | _ => -z 3

/-- The transport matrix for the first physical momentum component. -/
def cubicalStandardAlphaX (z : CubicalCell4) : CubicalCell4
  | 0 => z 3 | 1 => z 2 | 2 => z 1 | _ => z 0

/-- The transport matrix for the second physical momentum component. -/
def cubicalStandardAlphaY (z : CubicalCell4) : CubicalCell4
  | 0 => -I * z 3 | 1 => I * z 2 | 2 => -I * z 1 | _ => I * z 0

/-- The transport matrix for the third physical momentum component. -/
def cubicalStandardAlphaZ (z : CubicalCell4) : CubicalCell4
  | 0 => z 2 | 1 => -z 3 | 2 => z 0 | _ => -z 1

/-- Coordinate form of the incidence-derived spatial alpha operator. -/
def cubicalAlpha (axis : Fin 3) (z : CubicalCell4) : CubicalCell4 :=
  match axis with
  | 0 => cubicalStandardAlphaX z
  | 1 => cubicalStandardAlphaY z
  | _ => cubicalStandardAlphaZ z

/-- The momentum-weighted spatial Dirac matrix in standard coordinates. -/
def cubicalStandardSpatial
    (px py pz : ℂ) (z : CubicalCell4) : CubicalCell4 := fun component =>
  px * cubicalStandardAlphaX z component +
    py * cubicalStandardAlphaY z component +
    pz * cubicalStandardAlphaZ z component

/-- The free Dirac Hamiltonian with mass and all three momentum components. -/
def cubicalStandardHamiltonian
    (mass px py pz : ℂ) (z : CubicalCell4) : CubicalCell4 := fun component =>
  mass * cubicalStandardBeta z component +
    cubicalStandardSpatial px py pz z component

/-- Change from standard coordinates to the four independent negative-sector coordinates. -/
def standardToCubicalMinus (z : CubicalCell4) : CubicalCell4
  | 0 => z 0 | 1 => -z 3 | 2 => z 2 | _ => z 1

/-- Change from standard coordinates to the four independent positive-sector coordinates. -/
def standardToCubicalPlus (z : CubicalCell4) : CubicalCell4
  | 0 => -z 1 | 1 => z 2 | 2 => z 3 | _ => z 0

/-- Embed a standard spinor in the negative flavor sector of the cube. -/
def cubicalDiracEmbedMinus (z : CubicalCell4) : CubicalCell8 :=
  cubicalEmbedMinus (standardToCubicalMinus z)

/-- Embed a standard spinor in the positive flavor sector of the cube. -/
def cubicalDiracEmbedPlus (z : CubicalCell4) : CubicalCell8 :=
  cubicalEmbedPlus (standardToCubicalPlus z)

/-- Four standard coordinates recovered from a negative-flavor amplitude. -/
def cubicalNegativeFlavorRead (amplitude : CubicalCell8) : CubicalCell4
  | 0 => amplitude 0
  | 1 => amplitude 5
  | 2 => amplitude 4
  | _ => -amplitude 1

theorem cubical_dirac_embed_minus_injective :
    Function.Injective cubicalDiracEmbedMinus := by
  intro first second h
  have hcube := cubical_embed_minus_injective h
  funext component
  fin_cases component
  · exact congrFun hcube 0
  · exact congrFun hcube 3
  · exact congrFun hcube 2
  · have := congrFun hcube 1
    simpa [standardToCubicalMinus] using congrArg Neg.neg this

theorem cubical_dirac_embed_plus_injective :
    Function.Injective cubicalDiracEmbedPlus := by
  intro first second h
  have hcube := cubical_embed_plus_injective h
  funext component
  fin_cases component
  · exact congrFun hcube 3
  · have := congrFun hcube 0
    simpa [standardToCubicalPlus] using congrArg Neg.neg this
  · exact congrFun hcube 1
  · exact congrFun hcube 2

/-- The native spatial generator, with the physical momentum sign and axis convention. -/
def cubicalNativeSpatial
    (px py pz : ℂ) (amplitude : CubicalCell8) : CubicalCell8 :=
  cubicalIncidenceLinear pz (-py) (-px) amplitude

/-- The massive native cube Hamiltonian before restriction to a flavor sector. -/
def cubicalNativeHamiltonian
    (mass px py pz : ℂ) (amplitude : CubicalCell8) : CubicalCell8 :=
  fun corner => mass * cubicalBeta amplitude corner +
    cubicalNativeSpatial px py pz amplitude corner

theorem cubical_beta_intertwines_minus (z : CubicalCell4) :
    cubicalBeta (cubicalDiracEmbedMinus z) =
      cubicalDiracEmbedMinus (cubicalStandardBeta z) := by
  funext corner
  fin_cases corner <;>
    simp [cubicalBeta, cubicalDiracEmbedMinus, cubicalEmbedMinus,
      standardToCubicalMinus, cubicalStandardBeta,
      cubicalBit0, cubicalBit1, cubicalBit2]

theorem cubical_beta_intertwines_plus (z : CubicalCell4) :
    cubicalBeta (cubicalDiracEmbedPlus z) =
      cubicalDiracEmbedPlus (cubicalStandardBeta z) := by
  funext corner
  fin_cases corner <;>
    simp [cubicalBeta, cubicalDiracEmbedPlus, cubicalEmbedPlus,
      standardToCubicalPlus, cubicalStandardBeta,
      cubicalBit0, cubicalBit1, cubicalBit2]

/-- The standard four-component matrix of an oriented cube axis. -/
def cubicalStandardAxis : Fin 3 → CubicalCell4 → CubicalCell4
  | 0 => cubicalStandardAlphaZ
  | 1 => fun z => -cubicalStandardAlphaY z
  | _ => fun z => -cubicalStandardAlphaX z

/-- Embed standard spinors into the negative flavor sector as a complex linear map. -/
def cubicalDiracLinearEmbedMinus : CubicalCell4 →ₗ[ℂ] CubicalCell8 where
  toFun := cubicalDiracEmbedMinus
  map_add' first second := by
    funext corner
    fin_cases corner <;>
      simp [cubicalDiracEmbedMinus, cubicalEmbedMinus, standardToCubicalMinus, mul_add] <;> ring
  map_smul' scalar amplitude := by
    funext corner
    fin_cases corner <;>
      simp [cubicalDiracEmbedMinus, cubicalEmbedMinus, standardToCubicalMinus] <;> ring

theorem cubical_gamma_intertwines_minus (axis : Fin 3) (z : CubicalCell4) :
    cubicalGamma axis (cubicalDiracEmbedMinus z) =
      cubicalDiracEmbedMinus (cubicalStandardAxis axis z) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalGamma, cubicalIncidenceSign,
      cubicalIncidenceSignInteger, cubicalFlip, cubicalFlip0,
      cubicalFlip1, cubicalFlip2, cubicalDiracEmbedMinus, cubicalEmbedMinus,
      standardToCubicalMinus, cubicalStandardAxis, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ, cubicalBit0, cubicalBit1] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

/-- Embed standard spinors into the positive flavor sector as a complex linear map. -/
def cubicalDiracLinearEmbedPlus : CubicalCell4 →ₗ[ℂ] CubicalCell8 where
  toFun := cubicalDiracEmbedPlus
  map_add' first second := by
    funext corner
    fin_cases corner <;>
      simp [cubicalDiracEmbedPlus, cubicalEmbedPlus, standardToCubicalPlus, mul_add] <;> ring
  map_smul' scalar amplitude := by
    funext corner
    fin_cases corner <;>
      simp [cubicalDiracEmbedPlus, cubicalEmbedPlus, standardToCubicalPlus] <;> ring

theorem cubical_gamma_intertwines_plus (axis : Fin 3) (z : CubicalCell4) :
    cubicalGamma axis (cubicalDiracEmbedPlus z) =
      cubicalDiracEmbedPlus (cubicalStandardAxis axis z) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubicalGamma, cubicalIncidenceSign,
      cubicalIncidenceSignInteger, cubicalFlip, cubicalFlip0,
      cubicalFlip1, cubicalFlip2, cubicalDiracEmbedPlus, cubicalEmbedPlus,
      standardToCubicalPlus, cubicalStandardAxis, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ, cubicalBit0, cubicalBit1] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

private theorem cubical_standard_spatial_eq_axis_sum
    (px py pz : ℂ) (z : CubicalCell4) :
    cubicalStandardSpatial px py pz z =
      pz • cubicalStandardAxis 0 z + (-py) • cubicalStandardAxis 1 z +
        (-px) • cubicalStandardAxis 2 z := by
  funext component
  simp [cubicalStandardSpatial, cubicalStandardAxis]
  ring

theorem cubical_native_spatial_intertwines_minus
    (px py pz : ℂ) (z : CubicalCell4) :
    cubicalNativeSpatial px py pz (cubicalDiracEmbedMinus z) =
      cubicalDiracEmbedMinus (cubicalStandardSpatial px py pz z) := by
  change _ = cubicalDiracLinearEmbedMinus (cubicalStandardSpatial px py pz z)
  rw [cubical_standard_spatial_eq_axis_sum,
    map_add, map_add, map_smul, map_smul, map_smul]
  change _ =
    pz • cubicalDiracEmbedMinus (cubicalStandardAxis 0 z) +
      (-py) • cubicalDiracEmbedMinus (cubicalStandardAxis 1 z) +
      (-px) • cubicalDiracEmbedMinus (cubicalStandardAxis 2 z)
  rw [← cubical_gamma_intertwines_minus, ← cubical_gamma_intertwines_minus,
    ← cubical_gamma_intertwines_minus]
  rfl

theorem cubical_native_spatial_intertwines_plus
    (px py pz : ℂ) (z : CubicalCell4) :
    cubicalNativeSpatial px py pz (cubicalDiracEmbedPlus z) =
      cubicalDiracEmbedPlus (cubicalStandardSpatial px py pz z) := by
  change _ = cubicalDiracLinearEmbedPlus (cubicalStandardSpatial px py pz z)
  rw [cubical_standard_spatial_eq_axis_sum,
    map_add, map_add, map_smul, map_smul, map_smul]
  change _ =
    pz • cubicalDiracEmbedPlus (cubicalStandardAxis 0 z) +
      (-py) • cubicalDiracEmbedPlus (cubicalStandardAxis 1 z) +
      (-px) • cubicalDiracEmbedPlus (cubicalStandardAxis 2 z)
  rw [← cubical_gamma_intertwines_plus, ← cubical_gamma_intertwines_plus,
    ← cubical_gamma_intertwines_plus]
  rfl

theorem cubical_hamiltonian_intertwines_minus
    (mass px py pz : ℂ) (z : CubicalCell4) :
    cubicalNativeHamiltonian mass px py pz (cubicalDiracEmbedMinus z) =
      cubicalDiracEmbedMinus
        (cubicalStandardHamiltonian mass px py pz z) := by
  change mass • cubicalBeta (cubicalDiracEmbedMinus z) +
      cubicalNativeSpatial px py pz (cubicalDiracEmbedMinus z) =
    cubicalDiracLinearEmbedMinus (mass • cubicalStandardBeta z + cubicalStandardSpatial px py pz z)
  rw [map_add, map_smul, cubical_beta_intertwines_minus,
    cubical_native_spatial_intertwines_minus]
  rfl

theorem cubical_hamiltonian_intertwines_plus
    (mass px py pz : ℂ) (z : CubicalCell4) :
    cubicalNativeHamiltonian mass px py pz (cubicalDiracEmbedPlus z) =
      cubicalDiracEmbedPlus
        (cubicalStandardHamiltonian mass px py pz z) := by
  change mass • cubicalBeta (cubicalDiracEmbedPlus z) +
      cubicalNativeSpatial px py pz (cubicalDiracEmbedPlus z) =
    cubicalDiracLinearEmbedPlus (mass • cubicalStandardBeta z + cubicalStandardSpatial px py pz z)
  rw [map_add, map_smul, cubical_beta_intertwines_plus,
    cubical_native_spatial_intertwines_plus]
  rfl

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

theorem cubical_standard_hamiltonian_scale
    (mass px py pz scalar : ℂ) (z : CubicalCell4) :
    cubicalStandardHamiltonian mass px py pz (fun component => scalar * z component) =
      fun component => scalar * cubicalStandardHamiltonian mass px py pz z component := by
  funext component
  fin_cases component <;>
    simp [cubicalStandardHamiltonian, cubicalStandardSpatial, cubicalStandardBeta,
      cubicalStandardAlphaX, cubicalStandardAlphaY, cubicalStandardAlphaZ] <;> ring

private theorem cubical_beta_at_corner (amplitude : CubicalCell8) (corner : CubicalCorner) :
    cubicalBeta amplitude corner =
      (if (cubicalBit0 corner + cubicalBit1 corner + cubicalBit2 corner) % 2 = 0 then 1 else -1) *
        amplitude corner := by
  unfold cubicalBeta
  split <;> simp only [one_mul, neg_mul]

/-- The native square follows from the Clifford and parity relations on the cube. -/
theorem cubical_native_hamiltonian_square (mass px py pz : ℂ) (amplitude : CubicalCell8) :
    cubicalNativeHamiltonian mass px py pz
        (cubicalNativeHamiltonian mass px py pz amplitude) =
      (mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) • amplitude := by
  funext corner
  let spatial := cubicalNativeSpatial px py pz
  let parity : ℂ := if (cubicalBit0 corner + cubicalBit1 corner + cubicalBit2 corner) % 2 = 0
    then 1 else -1
  have hBeta (field : CubicalCell8) : cubicalBeta field corner = parity * field corner :=
    cubical_beta_at_corner field corner
  have hAxis (axis : Fin 3) : parity * cubicalGamma axis amplitude corner =
      -cubicalGamma axis (cubicalBeta amplitude) corner :=
    (hBeta _).symm.trans (congrFun (cubical_beta_anticommutes axis amplitude) corner)
  have hAnti : parity * spatial amplitude corner = -spatial (cubicalBeta amplitude) corner := by
    simp only [spatial, cubicalNativeSpatial, cubicalIncidenceLinear]
    linear_combination pz * hAxis 0 - py * hAxis 1 - px * hAxis 2
  have hSpatialAdd : spatial (fun j => mass * cubicalBeta amplitude j + spatial amplitude j)
        corner = mass * spatial (cubicalBeta amplitude) corner +
          spatial (spatial amplitude) corner := by
    simp only [spatial, cubicalNativeSpatial, cubicalIncidenceLinear, cubicalGamma]
    ring
  have hSpatialSquare : spatial (spatial amplitude) corner =
      (px ^ 2 + py ^ 2 + pz ^ 2) * amplitude corner := by
    simpa only [spatial, cubicalNativeSpatial, neg_sq, add_assoc, add_left_comm, add_comm] using
      congrFun (cubical_incidence_linear_square pz (-py) (-px) amplitude) corner
  have hBetaSquare : parity * cubicalBeta amplitude corner = amplitude corner :=
    (hBeta _).symm.trans (congrFun (cubical_beta_square amplitude) corner)
  change mass * cubicalBeta
      (fun j => mass * cubicalBeta amplitude j + spatial amplitude j) corner +
    spatial (fun j => mass * cubicalBeta amplitude j + spatial amplitude j) corner = _
  rw [hBeta, hSpatialAdd, hSpatialSquare]
  change _ = (mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) * amplitude corner
  linear_combination mass ^ 2 * hBetaSquare + mass * hAnti

theorem cubical_standard_hamiltonian_square
    (mass px py pz : ℂ) (z : CubicalCell4) :
    cubicalStandardHamiltonian mass px py pz
        (cubicalStandardHamiltonian mass px py pz z) =
      fun component => (mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2) * z component := by
  let coefficient := mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2
  apply cubical_dirac_embed_minus_injective
  rw [← cubical_hamiltonian_intertwines_minus, ← cubical_hamiltonian_intertwines_minus,
    cubical_native_hamiltonian_square]
  change coefficient • cubicalDiracLinearEmbedMinus z =
    cubicalDiracLinearEmbedMinus (coefficient • z)
  rw [map_smul]

/-- The Hamiltonian shifted by an energy maps into its corresponding eigenspace on shell. -/
theorem cubical_standard_hamiltonian_shift
    (mass px py pz energy scalar : ℂ)
    (hshell : mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 = energy ^ 2) (z : CubicalCell4) :
    let shift : CubicalCell4 := fun component =>
      scalar * (cubicalStandardHamiltonian mass px py pz z component + energy * z component)
    cubicalStandardHamiltonian mass px py pz shift =
      fun component => energy * shift component := by
  dsimp only
  rw [cubical_standard_hamiltonian_scale, cubical_standard_hamiltonian_add,
    cubical_standard_hamiltonian_scale, cubical_standard_hamiltonian_square, hshell]
  funext component
  ring

/-- The shared readout for the negative flavor sector. -/
abbrev negativeFlavorCoordinateRead := cubicalNegativeFlavorRead

theorem negative_flavor_coordinate_read_embed (z : CubicalCell4) :
    negativeFlavorCoordinateRead (cubicalDiracEmbedMinus z) = z := by
  funext component
  fin_cases component <;>
    simp [negativeFlavorCoordinateRead, cubicalNegativeFlavorRead, cubicalDiracEmbedMinus,
      cubicalEmbedMinus, standardToCubicalMinus]

/-- The four-coordinate spatial operator is obtained by applying the
eight-corner incidence root and then reading one derived flavor fiber.  No
four-by-four matrix occurs in this definition. -/
def orientedCubicalSpatialCoordinates
    (px py pz : ℂ) (z : CubicalCell4) : CubicalCell4 :=
  negativeFlavorCoordinateRead
    (cubicalNativeSpatial px py pz (cubicalDiracEmbedMinus z))

/-- In the conventional coordinate chart, the incidence-derived operator has
the familiar standard spatial entries. -/
@[simp] theorem oriented_cubical_spatial_coordinates_eq_standard
    (px py pz : ℂ) (z : CubicalCell4) :
    orientedCubicalSpatialCoordinates px py pz z =
      cubicalStandardSpatial px py pz z := by
  unfold orientedCubicalSpatialCoordinates
  rw [cubical_native_spatial_intertwines_minus]
  exact negative_flavor_coordinate_read_embed _

end
end LeanDirac.V2
