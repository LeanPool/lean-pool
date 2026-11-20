/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac017Closed.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac017

/-!
# DIRAC-017 closure: standard-spin and Hamiltonian covariance

This module closes the representation-level gaps found by the focused
DIRAC-017 red team.  It adds no native field, action term, update rule, or
runtime projection.  The remaining localized-carrier experiment is excluded
from this algebraic gate explicitly rather than being mislabeled as proved.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex

/-! ## The same generators in the conventional Dirac basis -/

/-- The standard-basis counterpart of `cubeIncidenceGamma axis`: `α_z`, `-α_y` or `-α_x` for
`axis = 0, 1, 2`. -/
def standardCubeGamma (axis : Fin 3) (z : Cell4) : Cell4 :=
  match axis with
  | 0 => standardDiracAlphaZ z
  | 1 => fun component => -standardDiracAlphaY z component
  | _ => fun component => -standardDiracAlphaX z component

/-- The product `Gⱼ Gₖ` of `standardCubeGamma` operators for the cyclic pair `(j, k)` following
`axis`: `G₁ G₂`, `G₂ G₀` or `G₀ G₁` for `axis = 0, 1, 2`. -/
def standardCubePlaneBivector (axis : Fin 3) (z : Cell4) : Cell4 :=
  match axis with
  | 0 => standardCubeGamma 1 (standardCubeGamma 2 z)
  | 1 => standardCubeGamma 2 (standardCubeGamma 0 z)
  | _ => standardCubeGamma 0 (standardCubeGamma 1 z)

/-- The operator `(1 / 2) * (-i) * standardCubePlaneBivector axis` on four-component vectors. -/
def standardCubeSpin (axis : Fin 3) (z : Cell4) : Cell4 :=
  fun component =>
    (1 / 2 : ℂ) * (-I * standardCubePlaneBivector axis z component)

theorem cube_spin_intertwines_minus (axis : Fin 3) (z : Cell4) :
    cubeSpin axis (cubeDiracEmbedMinus z) =
      cubeDiracEmbedMinus (standardCubeSpin axis z) := by
  rw [show cubeSpin = cubeScaledSpin nativeSpinScale from rfl]
  rw [native_spin_scale_eq_half]
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeScaledSpin, cubeSigma, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cubeDiracEmbedMinus, cubeEmbedMinus, standardToMinusCubeSpinor,
      standardCubeSpin, standardCubePlaneBivector, standardCubeGamma,
      standardDiracAlphaX, standardDiracAlphaY, standardDiracAlphaZ,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1] <;>
    ring_nf <;> simp <;> ring

theorem cube_spin_intertwines_plus (axis : Fin 3) (z : Cell4) :
    cubeSpin axis (cubeDiracEmbedPlus z) =
      cubeDiracEmbedPlus (standardCubeSpin axis z) := by
  rw [show cubeSpin = cubeScaledSpin nativeSpinScale from rfl]
  rw [native_spin_scale_eq_half]
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeScaledSpin, cubeSigma, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cubeDiracEmbedPlus, cubeEmbedPlus, standardToPlusCubeSpinor,
      standardCubeSpin, standardCubePlaneBivector, standardCubeGamma,
      standardDiracAlphaX, standardDiracAlphaY, standardDiracAlphaZ,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1] <;>
    ring_nf <;> simp <;> ring

theorem standard_cube_spin0_component_formula (z : Cell4) :
    standardCubeSpin 0 z = fun component =>
      if component = 0 ∨ component = 2 then
        (-1 / 2 : ℂ) * z component
      else
        (1 / 2 : ℂ) * z component := by
  funext component
  fin_cases component <;>
    simp [standardCubeSpin, standardCubePlaneBivector,
      standardCubeGamma, standardDiracAlphaX, standardDiracAlphaY] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

/-! ## Mass grading and the complete interpreted Hamiltonian rotate together -/

theorem cube_beta_commutes_spin (axis : Fin 3) (amplitude : Cell8) :
    cubeParityBeta (cubeSpin axis amplitude) =
      cubeSpin axis (cubeParityBeta amplitude) := by
  rw [show cubeSpin = cubeScaledSpin nativeSpinScale from rfl]
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeScaledSpin, cubeSigma, cubePlaneBivector,
      cubeParityBeta, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2,
      cellBit0, cellBit1, cellBit2]

theorem cube_beta_commutes_quarter_turn
    (axis : Fin 3) (amplitude : Cell8) :
    cubeParityBeta (cubeQuarterTurn axis amplitude) =
      cubeQuarterTurn axis (cubeParityBeta amplitude) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeParityBeta,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1, cellBit2] <;>
    ring

/-- The first component of `(px, py, pz)` after the signed permutation attached to a quarter-turn
about `axis`: `py`, `pz` or `px` for `axis = 0, 1, 2`. -/
def cubeRotatedPx (axis : Fin 3) (px py pz : ℂ) : ℂ :=
  match axis with
  | 0 => py
  | 1 => pz
  | _ => px

/-- The second component of `(px, py, pz)` after the signed permutation attached to a quarter-turn
about `axis`: `-px`, `py` or `-pz` for `axis = 0, 1, 2`. -/
def cubeRotatedPy (axis : Fin 3) (px py pz : ℂ) : ℂ :=
  match axis with
  | 0 => -px
  | 1 => py
  | _ => -pz

/-- The third component of `(px, py, pz)` after the signed permutation attached to a quarter-turn
about `axis`: `pz`, `-px` or `py` for `axis = 0, 1, 2`. -/
def cubeRotatedPz (axis : Fin 3) (px py pz : ℂ) : ℂ :=
  match axis with
  | 0 => pz
  | 1 => -px
  | _ => py

theorem cube_quarter_turn_hamiltonian_covariance
    (axis : Fin 3) (mass px py pz : ℂ) (amplitude : Cell8) :
    cubeQuarterTurn axis
        (interpretedCubeDiracHamiltonian mass px py pz amplitude) =
      interpretedCubeDiracHamiltonian mass
        (cubeRotatedPx axis px py pz)
        (cubeRotatedPy axis px py pz)
        (cubeRotatedPz axis px py pz)
        (cubeQuarterTurn axis amplitude) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeQuarterTurn, interpretedCubeDiracHamiltonian,
      nativeCubeDiracSpatial, cubeIncidenceLinear, cubePlaneBivector,
      cubeParityBeta, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cubeRotatedPx, cubeRotatedPy, cubeRotatedPz,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1, cellBit2] <;>
    ring

/-!
The quarter-turn theorem above is the discrete cubical case.  The same
incidence rotor also covaries the complete interpreted Hamiltonian for every
real angle; the physical momentum rotates through the full angle while the
spinor rotor uses the derived half-angle.
-/

/-- The first component of `(px, py, pz)` after rotation by `θ = angle` in the `(px, py)`,
`(px, pz)` or `(py, pz)` plane for `axis = 0, 1, 2`: `cos θ px + sin θ py`, `cos θ px + sin θ pz`
or `px`. -/
def cubeContinuousRotatedPx
    (angle : ℝ) (axis : Fin 3) (px py pz : ℂ) : ℂ :=
  match axis with
  | 0 => Real.cos angle * px + Real.sin angle * py
  | 1 => Real.cos angle * px + Real.sin angle * pz
  | _ => px

/-- The second component of `(px, py, pz)` after rotation by `θ = angle` in the `(px, py)`,
`(px, pz)` or `(py, pz)` plane for `axis = 0, 1, 2`: `-sin θ px + cos θ py`, `py`
or `cos θ py - sin θ pz`. -/
def cubeContinuousRotatedPy
    (angle : ℝ) (axis : Fin 3) (px py pz : ℂ) : ℂ :=
  match axis with
  | 0 => -Real.sin angle * px + Real.cos angle * py
  | 1 => py
  | _ => Real.cos angle * py - Real.sin angle * pz

/-- The third component of `(px, py, pz)` after rotation by `θ = angle` in the `(px, py)`,
`(px, pz)` or `(py, pz)` plane for `axis = 0, 1, 2`: `pz`, `-sin θ px + cos θ pz`
or `sin θ py + cos θ pz`. -/
def cubeContinuousRotatedPz
    (angle : ℝ) (axis : Fin 3) (px py pz : ℂ) : ℂ :=
  match axis with
  | 0 => pz
  | 1 => -Real.sin angle * px + Real.cos angle * pz
  | _ => Real.sin angle * py + Real.cos angle * pz

/-- The operator `(1 - 2 i S) / √2` on four-component vectors, where `S = standardCubeSpin axis`;
the standard-basis counterpart of `cubeQuarterTurn axis`. -/
def standardCubeQuarterTurn (axis : Fin 3) (z : Cell4) : Cell4 :=
  fun component => (((1 / Real.sqrt 2 : ℝ) : ℂ) *
    (z component - 2 * I * standardCubeSpin axis z component))

theorem cube_quarter_turn_intertwines_minus (axis : Fin 3) (z : Cell4) :
    cubeQuarterTurn axis (cubeDiracEmbedMinus z) =
      cubeDiracEmbedMinus (standardCubeQuarterTurn axis z) := by
  rw [cube_quarter_turn_is_spin_rotor]
  funext corner
  rw [congrFun (cube_spin_intertwines_minus axis z) corner]
  fin_cases axis <;> fin_cases corner <;>
    simp [standardCubeQuarterTurn, cubeDiracEmbedMinus, cubeEmbedMinus,
      standardToMinusCubeSpinor, standardCubeSpin,
      standardCubePlaneBivector, standardCubeGamma,
      standardDiracAlphaX, standardDiracAlphaY, standardDiracAlphaZ] <;>
    ring

theorem cube_quarter_turn_intertwines_plus (axis : Fin 3) (z : Cell4) :
    cubeQuarterTurn axis (cubeDiracEmbedPlus z) =
      cubeDiracEmbedPlus (standardCubeQuarterTurn axis z) := by
  rw [cube_quarter_turn_is_spin_rotor]
  funext corner
  rw [congrFun (cube_spin_intertwines_plus axis z) corner]
  fin_cases axis <;> fin_cases corner <;>
    simp [standardCubeQuarterTurn, cubeDiracEmbedPlus, cubeEmbedPlus,
      standardToPlusCubeSpinor, standardCubeSpin,
      standardCubePlaneBivector, standardCubeGamma,
      standardDiracAlphaX, standardDiracAlphaY, standardDiracAlphaZ] <;>
    ring

/-! ## Positive native inner product and exact unitarity -/

theorem cell8_inner_self_eq_density (amplitude : Cell8) :
    cell8Inner amplitude amplitude = (cell8Density amplitude : ℂ) := by
  apply Complex.ext
  · simp [cell8Inner, cell8Density, Complex.normSq,
      Complex.mul_re, Fin.sum_univ_succ]
  · simp [cell8Inner, cell8Density, Complex.normSq,
      Complex.mul_im, Fin.sum_univ_succ]
    ring

theorem cell8_density_nonnegative (amplitude : Cell8) :
    0 ≤ cell8Density amplitude := by
  exact Fintype.sum_nonneg fun corner =>
    Complex.normSq_nonneg (amplitude corner)

theorem cell8_density_eq_zero_iff (amplitude : Cell8) :
    cell8Density amplitude = 0 ↔ amplitude = 0 := by
  constructor
  · intro hzero
    have hall : (fun corner => Complex.normSq (amplitude corner)) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg
        (fun corner => Complex.normSq_nonneg (amplitude corner))).mp hzero
    funext corner
    exact Complex.normSq_eq_zero.mp (congrFun hall corner)
  · intro hzero
    subst amplitude
    simp [cell8Density]

theorem cell8_inner_positive_definite (amplitude : Cell8) :
    cell8Inner amplitude amplitude = 0 ↔ amplitude = 0 := by
  rw [cell8_inner_self_eq_density]
  norm_cast
  exact cell8_density_eq_zero_iff amplitude

theorem cube_quarter_turn_preserves_inner
    (axis : Fin 3) (first second : Cell8) :
    cell8Inner (cubeQuarterTurn axis first)
        (cubeQuarterTurn axis second) =
      cell8Inner first second := by
  fin_cases axis <;>
    apply Complex.ext <;>
    simp [cell8Inner, cubeQuarterTurn, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1,
      Complex.mul_re, Complex.mul_im, Fin.sum_univ_succ] <;>
    field_simp [sqrt_two_ne_zero] <;>
    ring_nf <;>
    rw [sqrt_two_sq] <;>
    ring

/-! ## The two-plus/two-minus component spectrum is explicit -/

/-- The standard basis vector of `Cell4` with a `1` in position `basisComponent` and `0`
elsewhere. -/
def standardCell4Basis (basisComponent : Fin 4) : Cell4 :=
  fun component => if component = basisComponent then 1 else 0

theorem standard_cube_spin0_basis_spectrum :
    (standardCubeSpin 0 (standardCell4Basis 0) =
        fun component => (-1 / 2 : ℂ) * standardCell4Basis 0 component) ∧
    (standardCubeSpin 0 (standardCell4Basis 1) =
        fun component => (1 / 2 : ℂ) * standardCell4Basis 1 component) ∧
    (standardCubeSpin 0 (standardCell4Basis 2) =
        fun component => (-1 / 2 : ℂ) * standardCell4Basis 2 component) ∧
    (standardCubeSpin 0 (standardCell4Basis 3) =
        fun component => (1 / 2 : ℂ) * standardCell4Basis 3 component) := by
  constructor
  · funext component
    fin_cases component <;>
      simp [standardCubeSpin, standardCubePlaneBivector,
        standardCubeGamma, standardDiracAlphaX, standardDiracAlphaY,
        standardCell4Basis]
    ring_nf
  constructor
  · funext component
    fin_cases component <;>
      simp [standardCubeSpin, standardCubePlaneBivector,
        standardCubeGamma, standardDiracAlphaX, standardDiracAlphaY,
        standardCell4Basis]
  constructor
  · funext component
    fin_cases component <;>
      simp [standardCubeSpin, standardCubePlaneBivector,
        standardCubeGamma, standardDiracAlphaX, standardDiracAlphaY,
        standardCell4Basis]
    ring_nf
  · funext component
    fin_cases component <;>
      simp [standardCubeSpin, standardCubePlaneBivector,
        standardCubeGamma, standardDiracAlphaX, standardDiracAlphaY,
        standardCell4Basis]

/-! ## Continuous native rotations -/

/-- The operator `cos (s θ) - sin (s θ) B` on eight-corner amplitudes, where `θ = angle`,
`s = nativeSpinScale` (which equals `1 / 2`) and `B = cubePlaneBivector axis`. -/
def cubeContinuousTurn
    (angle : ℝ) (axis : Fin 3) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    ((Real.cos (nativeSpinScale * angle) : ℝ) : ℂ) * amplitude corner -
      ((Real.sin (nativeSpinScale * angle) : ℝ) : ℂ) *
        cubePlaneBivector axis amplitude corner

theorem cube_continuous_turn_hamiltonian_covariance
    (angle : ℝ) (axis : Fin 3) (mass px py pz : ℂ)
    (amplitude : Cell8) :
    cubeContinuousTurn angle axis
        (interpretedCubeDiracHamiltonian mass px py pz amplitude) =
      interpretedCubeDiracHamiltonian mass
        (cubeContinuousRotatedPx angle axis px py pz)
        (cubeContinuousRotatedPy angle axis px py pz)
        (cubeContinuousRotatedPz angle axis px py pz)
        (cubeContinuousTurn angle axis amplitude) := by
  have hcos : Real.cos angle =
      Real.cos (angle / 2) ^ 2 - Real.sin (angle / 2) ^ 2 := by
    calc
      Real.cos angle = Real.cos (2 * (angle / 2)) := by
        congr 1
        ring
      _ = 2 * Real.cos (angle / 2) ^ 2 - 1 := by
        rw [Real.cos_two_mul]
      _ = Real.cos (angle / 2) ^ 2 - Real.sin (angle / 2) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq (angle / 2)]
  have hsin : Real.sin angle =
      2 * Real.sin (angle / 2) * Real.cos (angle / 2) := by
    calc
      Real.sin angle = Real.sin (2 * (angle / 2)) := by
        congr 1
        ring
      _ = 2 * Real.sin (angle / 2) * Real.cos (angle / 2) := by
        rw [Real.sin_two_mul]
  have htrig :
      Complex.cos ((angle : ℂ) * (1 / 2)) ^ 2 +
        Complex.sin ((angle : ℂ) * (1 / 2)) ^ 2 = 1 := by
    exact Complex.cos_sq_add_sin_sq ((angle : ℂ) * (1 / 2))
  have hsinSq :
      Complex.sin ((angle : ℂ) * (1 / 2)) ^ 2 =
        1 - Complex.cos ((angle : ℂ) * (1 / 2)) ^ 2 := by
    linear_combination htrig
  have hsinCube :
      Complex.sin ((angle : ℂ) * (1 / 2)) ^ 3 =
        (1 - Complex.cos ((angle : ℂ) * (1 / 2)) ^ 2) *
          Complex.sin ((angle : ℂ) * (1 / 2)) := by
    calc
      Complex.sin ((angle : ℂ) * (1 / 2)) ^ 3 =
          Complex.sin ((angle : ℂ) * (1 / 2)) ^ 2 *
            Complex.sin ((angle : ℂ) * (1 / 2)) := by ring
      _ = (1 - Complex.cos ((angle : ℂ) * (1 / 2)) ^ 2) *
            Complex.sin ((angle : ℂ) * (1 / 2)) := by rw [hsinSq]
  have hcosSq :
      Complex.cos ((angle : ℂ) * (1 / 2)) ^ 2 =
        1 - Complex.sin ((angle : ℂ) * (1 / 2)) ^ 2 := by
    linear_combination htrig
  have hcosCube :
      Complex.cos ((angle : ℂ) * (1 / 2)) ^ 3 =
        (1 - Complex.sin ((angle : ℂ) * (1 / 2)) ^ 2) *
          Complex.cos ((angle : ℂ) * (1 / 2)) := by
    calc
      Complex.cos ((angle : ℂ) * (1 / 2)) ^ 3 =
          Complex.cos ((angle : ℂ) * (1 / 2)) ^ 2 *
            Complex.cos ((angle : ℂ) * (1 / 2)) := by ring
      _ = (1 - Complex.sin ((angle : ℂ) * (1 / 2)) ^ 2) *
            Complex.cos ((angle : ℂ) * (1 / 2)) := by rw [hcosSq]
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeContinuousTurn, interpretedCubeDiracHamiltonian,
      nativeCubeDiracSpatial, cubeIncidenceLinear, cubePlaneBivector,
      cubeParityBeta, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cubeContinuousRotatedPx,
      cubeContinuousRotatedPy, cubeContinuousRotatedPz,
      native_spin_scale_eq_half, hcos, hsin,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1, cellBit2] <;>
    ring_nf <;>
    simp only [hsinCube, hcosCube] <;>
    ring

theorem cube_continuous_turn_add
    (firstAngle secondAngle : ℝ) (axis : Fin 3) (amplitude : Cell8) :
    cubeContinuousTurn firstAngle axis
        (cubeContinuousTurn secondAngle axis amplitude) =
      cubeContinuousTurn (firstAngle + secondAngle) axis amplitude := by
  have hscaled : nativeSpinScale * (firstAngle + secondAngle) =
      nativeSpinScale * firstAngle + nativeSpinScale * secondAngle := by ring
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeContinuousTurn, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1,
      hscaled, Real.cos_add, Real.sin_add] <;>
    ring

theorem cube_continuous_turn_zero
    (axis : Fin 3) (amplitude : Cell8) :
    cubeContinuousTurn 0 axis amplitude = amplitude := by
  funext corner
  simp [cubeContinuousTurn, native_spin_scale_eq_half]

theorem cube_continuous_turn_two_pi
    (axis : Fin 3) (amplitude : Cell8) :
    cubeContinuousTurn (2 * Real.pi) axis amplitude =
      fun corner => -amplitude corner := by
  funext corner
  simp [cubeContinuousTurn, native_spin_scale_eq_half]

theorem cube_continuous_turn_four_pi
    (axis : Fin 3) (amplitude : Cell8) :
    cubeContinuousTurn (4 * Real.pi) axis amplitude = amplitude := by
  have hangle : (1 / 2 : ℝ) * (4 * Real.pi) = 2 * Real.pi := by ring
  funext corner
  simp only [cubeContinuousTurn]
  rw [native_spin_scale_eq_half, hangle]
  simp

theorem sqrt_two_div_two_eq_inv_sqrt_two :
    Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
  field_simp [sqrt_two_ne_zero]
  nlinarith [sqrt_two_sq]

theorem cube_continuous_turn_pi_div_two
    (axis : Fin 3) (amplitude : Cell8) :
    cubeContinuousTurn (Real.pi / 2) axis amplitude =
      cubeQuarterTurn axis amplitude := by
  have hangle : (1 / 2 : ℝ) * (Real.pi / 2) = Real.pi / 4 := by ring
  funext corner
  simp only [cubeContinuousTurn, cubeQuarterTurn,
    native_spin_scale_eq_half, hangle,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  rw [sqrt_two_div_two_eq_inv_sqrt_two]
  push_cast
  ring

theorem cube_real_plane_rotation_inner_scaling
    (identityCoeff planeCoeff : ℝ)
    (axis : Fin 3) (first second : Cell8) :
    cell8Inner
        (fun corner =>
          (identityCoeff : ℂ) * first corner -
            (planeCoeff : ℂ) * cubePlaneBivector axis first corner)
        (fun corner =>
          (identityCoeff : ℂ) * second corner -
            (planeCoeff : ℂ) * cubePlaneBivector axis second corner) =
      ((identityCoeff ^ 2 + planeCoeff ^ 2 : ℝ) : ℂ) *
        cell8Inner first second := by
  fin_cases axis <;>
    apply Complex.ext <;>
    simp [cell8Inner, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1, Complex.mul_re, Complex.mul_im,
      Fin.sum_univ_succ, -Complex.ofReal_pow] <;>
    ring

theorem cube_real_plane_rotation_preserves_inner
    (identityCoeff planeCoeff : ℝ)
    (hnorm : identityCoeff ^ 2 + planeCoeff ^ 2 = 1)
    (axis : Fin 3) (first second : Cell8) :
    cell8Inner
        (fun corner =>
          (identityCoeff : ℂ) * first corner -
            (planeCoeff : ℂ) * cubePlaneBivector axis first corner)
        (fun corner =>
          (identityCoeff : ℂ) * second corner -
            (planeCoeff : ℂ) * cubePlaneBivector axis second corner) =
      cell8Inner first second := by
  rw [cube_real_plane_rotation_inner_scaling]
  rw [hnorm]
  simp

theorem cube_continuous_turn_preserves_inner
    (angle : ℝ) (axis : Fin 3) (first second : Cell8) :
    cell8Inner (cubeContinuousTurn angle axis first)
        (cubeContinuousTurn angle axis second) =
      cell8Inner first second := by
  change cell8Inner
      (fun corner =>
        (Real.cos (nativeSpinScale * angle) : ℂ) * first corner -
          (Real.sin (nativeSpinScale * angle) : ℂ) *
            cubePlaneBivector axis first corner)
      (fun corner =>
        (Real.cos (nativeSpinScale * angle) : ℂ) * second corner -
          (Real.sin (nativeSpinScale * angle) : ℂ) *
            cubePlaneBivector axis second corner) =
    cell8Inner first second
  apply cube_real_plane_rotation_preserves_inner
  nlinarith [Real.sin_sq_add_cos_sq (nativeSpinScale * angle)]

theorem cube_continuous_turn_preserves_density
    (angle : ℝ) (axis : Fin 3) (amplitude : Cell8) :
    cell8Density (cubeContinuousTurn angle axis amplitude) =
      cell8Density amplitude := by
  have hinner := cube_continuous_turn_preserves_inner
    angle axis amplitude amplitude
  rw [cell8_inner_self_eq_density,
    cell8_inner_self_eq_density] at hinner
  exact_mod_cast hinner

/-! ## The quarter-turn is characterized, not merely selected -/

/-- The operator `identityCoeff + planeCoeff * B` on eight-corner amplitudes, where
`B = cubePlaneBivector axis`. -/
def cubePlaneRotor
    (identityCoeff planeCoeff : ℝ)
    (axis : Fin 3) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    (identityCoeff : ℂ) * amplitude corner +
      (planeCoeff : ℂ) * cubePlaneBivector axis amplitude corner

/-- The condition `R Γ₁ = Γ₂ R` on every amplitude, where `R = cubePlaneRotor identityCoeff
planeCoeff 0` and `Γₐ = cubeIncidenceGamma a`. -/
def cubeAxis0QuarterTurnCovariance
    (identityCoeff planeCoeff : ℝ) : Prop :=
  ∀ amplitude : Cell8,
    cubePlaneRotor identityCoeff planeCoeff 0
        (cubeIncidenceGamma 1 amplitude) =
      cubeIncidenceGamma 2
        (cubePlaneRotor identityCoeff planeCoeff 0 amplitude)

theorem cube_axis0_quarter_turn_covariance_defect
    (identityCoeff planeCoeff : ℝ) (amplitude : Cell8) :
    (fun corner =>
      cubePlaneRotor identityCoeff planeCoeff 0
          (cubeIncidenceGamma 1 amplitude) corner -
        cubeIncidenceGamma 2
          (cubePlaneRotor identityCoeff planeCoeff 0 amplitude) corner) =
      fun corner =>
        ((identityCoeff + planeCoeff : ℝ) : ℂ) *
          (cubeIncidenceGamma 1 amplitude corner -
            cubeIncidenceGamma 2 amplitude corner) := by
  funext corner
  fin_cases corner <;>
    simp [cubePlaneRotor, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip1,
      cellFlip2, cellBit0, cellBit1] <;>
    ring

theorem cube_axis0_quarter_turn_covariance_iff
    (identityCoeff planeCoeff : ℝ) :
    cubeAxis0QuarterTurnCovariance identityCoeff planeCoeff ↔
      planeCoeff = -identityCoeff := by
  constructor
  · intro hcovariance
    have hzero :
        (fun corner =>
          cubePlaneRotor identityCoeff planeCoeff 0
              (cubeIncidenceGamma 1 uniformCubeAmplitude) corner -
            cubeIncidenceGamma 2
              (cubePlaneRotor identityCoeff planeCoeff 0
                uniformCubeAmplitude) corner) = 0 := by
      funext corner
      rw [hcovariance uniformCubeAmplitude]
      simp
    rw [cube_axis0_quarter_turn_covariance_defect] at hzero
    have hcomponent :
        ((identityCoeff + planeCoeff : ℝ) : ℂ) *
          (cubeIncidenceGamma 1 uniformCubeAmplitude 2 -
            cubeIncidenceGamma 2 uniformCubeAmplitude 2) = 0 :=
      congrFun hzero 2
    have hfactor : cubeIncidenceGamma 1 uniformCubeAmplitude 2 -
        cubeIncidenceGamma 2 uniformCubeAmplitude 2 ≠ 0 := by
      norm_num [uniformCubeAmplitude, cubeIncidenceGamma,
        cubeIncidenceSign, cubeIncidenceFlip, cellFlip1, cellFlip2,
        cellBit0, cellBit1]
    have hsum : ((identityCoeff + planeCoeff : ℝ) : ℂ) = 0 :=
      (mul_eq_zero.mp hcomponent).resolve_right hfactor
    have hreal : identityCoeff + planeCoeff = 0 := by
      exact_mod_cast hsum
    linarith
  · intro hcoefficient amplitude
    subst planeCoeff
    funext corner
    fin_cases corner <;>
      simp [cubePlaneRotor, cubePlaneBivector, cubeIncidenceGamma,
        cubeIncidenceSign, cubeIncidenceFlip,
        cellFlip1, cellFlip2, cellBit0, cellBit1] <;>
      ring

/-- The coefficient pair is admissible when `identityCoeff` is positive, the rotor
`cubePlaneRotor identityCoeff planeCoeff 0` satisfies `cubeAxis0QuarterTurnCovariance`, and it
preserves `cell8Density`. -/
def admissibleCubeQuarterTurnCoefficients
    (identityCoeff planeCoeff : ℝ) : Prop :=
  0 < identityCoeff ∧
  cubeAxis0QuarterTurnCovariance identityCoeff planeCoeff ∧
  ∀ amplitude : Cell8,
    cell8Density (cubePlaneRotor identityCoeff planeCoeff 0 amplitude) =
      cell8Density amplitude

/-- The standard basis vector of `Cell8` with a `1` at corner `basisCorner` and `0` elsewhere. -/
def cell8CornerBasis (basisCorner : Fin 8) : Cell8 :=
  fun corner => if corner = basisCorner then 1 else 0

theorem cell8_corner_basis_density (basisCorner : Fin 8) :
    cell8Density (cell8CornerBasis basisCorner) = 1 := by
  fin_cases basisCorner <;>
    norm_num [cell8Density, cell8CornerBasis, Complex.normSq,
      Fin.sum_univ_succ]

theorem cube_plane_rotor_density_scaling
    (identityCoeff planeCoeff : ℝ)
    (axis : Fin 3) (amplitude : Cell8) :
    cell8Density (cubePlaneRotor identityCoeff planeCoeff axis amplitude) =
      (identityCoeff ^ 2 + planeCoeff ^ 2) * cell8Density amplitude := by
  fin_cases axis <;>
    simp [cell8Density, cubePlaneRotor, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1,
      Complex.normSq, Complex.mul_re, Complex.mul_im,
      Fin.sum_univ_succ] <;>
    ring

theorem canonical_quarter_turn_coefficients_admissible :
    admissibleCubeQuarterTurnCoefficients
      (1 / Real.sqrt 2) (-1 / Real.sqrt 2) := by
  refine ⟨by positivity, ?_, ?_⟩
  · rw [cube_axis0_quarter_turn_covariance_iff]
    ring
  · intro amplitude
    rw [cube_plane_rotor_density_scaling]
    have hcoefficient :
        (1 / Real.sqrt 2) ^ 2 + (-1 / Real.sqrt 2) ^ 2 = 1 := by
      field_simp [sqrt_two_ne_zero]
      nlinarith [sqrt_two_sq]
    rw [hcoefficient, one_mul]

theorem admissible_quarter_turn_coefficients_unique
    (identityCoeff planeCoeff : ℝ)
    (hadmissible :
      admissibleCubeQuarterTurnCoefficients identityCoeff planeCoeff) :
    identityCoeff = 1 / Real.sqrt 2 ∧
      planeCoeff = -1 / Real.sqrt 2 := by
  rcases hadmissible with ⟨hpositive, hcovariance, hdensity⟩
  have hplane : planeCoeff = -identityCoeff :=
    (cube_axis0_quarter_turn_covariance_iff
      identityCoeff planeCoeff).mp hcovariance
  have hscale := cube_plane_rotor_density_scaling
    identityCoeff planeCoeff 0 (cell8CornerBasis 0)
  rw [hdensity, cell8_corner_basis_density, mul_one] at hscale
  rw [hplane] at hscale
  have hsqrtPositive : 0 < Real.sqrt 2 := by positivity
  have hidentity : identityCoeff = 1 / Real.sqrt 2 := by
    field_simp [sqrt_two_ne_zero]
    nlinarith [sqrt_two_sq, hscale]
  exact ⟨hidentity, by rw [hplane, hidentity]; ring⟩

theorem exists_unique_admissible_cube_quarter_turn_coefficients :
    ∃! coefficients : ℝ × ℝ,
      admissibleCubeQuarterTurnCoefficients
        coefficients.1 coefficients.2 := by
  refine ⟨(1 / Real.sqrt 2, -1 / Real.sqrt 2),
    canonical_quarter_turn_coefficients_admissible, ?_⟩
  intro coefficients hadmissible
  rcases admissible_quarter_turn_coefficients_unique
    coefficients.1 coefficients.2 hadmissible with ⟨hfirst, hsecond⟩
  exact Prod.ext hfirst hsecond

/-! ## Continuous rotations in the conventional four-component basis -/

/-- The operator `cos (s θ) - 2 i sin (s θ) S` on four-component vectors, where `θ = angle`,
`s = nativeSpinScale` and `S = standardCubeSpin axis`. -/
def standardCubeContinuousTurn
    (angle : ℝ) (axis : Fin 3) (z : Cell4) : Cell4 :=
  fun component =>
    (Real.cos (nativeSpinScale * angle) : ℂ) * z component -
      2 * I * (Real.sin (nativeSpinScale * angle) : ℂ) *
        standardCubeSpin axis z component

theorem cube_continuous_turn_is_spin_rotor
    (angle : ℝ) (axis : Fin 3) (amplitude : Cell8) :
    cubeContinuousTurn angle axis amplitude =
      fun corner =>
        (Real.cos (nativeSpinScale * angle) : ℂ) * amplitude corner -
          2 * I * (Real.sin (nativeSpinScale * angle) : ℂ) *
            cubeSpin axis amplitude corner := by
  rw [show cubeSpin = cubeScaledSpin nativeSpinScale from rfl]
  unfold cubeContinuousTurn
  simp_rw [native_spin_scale_eq_half]
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeScaledSpin, cubeSigma,
      cubePlaneBivector, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2,
      cellBit0, cellBit1] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cube_continuous_turn_intertwines_minus
    (angle : ℝ) (axis : Fin 3) (z : Cell4) :
    cubeContinuousTurn angle axis (cubeDiracEmbedMinus z) =
      cubeDiracEmbedMinus (standardCubeContinuousTurn angle axis z) := by
  rw [cube_continuous_turn_is_spin_rotor]
  funext corner
  rw [congrFun (cube_spin_intertwines_minus axis z) corner]
  fin_cases corner <;>
    simp [standardCubeContinuousTurn, cubeDiracEmbedMinus,
      cubeEmbedMinus, standardToMinusCubeSpinor] <;>
    ring

theorem cube_continuous_turn_intertwines_plus
    (angle : ℝ) (axis : Fin 3) (z : Cell4) :
    cubeContinuousTurn angle axis (cubeDiracEmbedPlus z) =
      cubeDiracEmbedPlus (standardCubeContinuousTurn angle axis z) := by
  rw [cube_continuous_turn_is_spin_rotor]
  funext corner
  rw [congrFun (cube_spin_intertwines_plus axis z) corner]
  fin_cases corner <;>
    simp [standardCubeContinuousTurn, cubeDiracEmbedPlus,
      cubeEmbedPlus, standardToPlusCubeSpinor] <;>
    ring

/-! ## Strengthened representation certificate -/

/-- The bundle of results of this file: intertwining of `cubeSpin`, `cubeQuarterTurn` and
`cubeContinuousTurn` with their standard-basis counterparts, covariance of
`interpretedCubeDiracHamiltonian`, unitarity, the `2π` sign and `4π` return of
`cubeContinuousTurn`, and uniqueness of the quarter-turn coefficients. -/
structure Dirac017ClosedSpinHalfRepresentationCertificate : Prop where
  priorRepresentation : Dirac017NativeSpinHalfCertificate
  standardSpinIntertwining :
    (∀ axis z,
      cubeSpin axis (cubeDiracEmbedMinus z) =
        cubeDiracEmbedMinus (standardCubeSpin axis z)) ∧
    (∀ axis z,
      cubeSpin axis (cubeDiracEmbedPlus z) =
        cubeDiracEmbedPlus (standardCubeSpin axis z))
  explicitTwoPlusTwoMinusSpectrum :
    (standardCubeSpin 0 (standardCell4Basis 0) =
        fun component => (-1 / 2 : ℂ) * standardCell4Basis 0 component) ∧
    (standardCubeSpin 0 (standardCell4Basis 1) =
        fun component => (1 / 2 : ℂ) * standardCell4Basis 1 component) ∧
    (standardCubeSpin 0 (standardCell4Basis 2) =
        fun component => (-1 / 2 : ℂ) * standardCell4Basis 2 component) ∧
    (standardCubeSpin 0 (standardCell4Basis 3) =
        fun component => (1 / 2 : ℂ) * standardCell4Basis 3 component)
  massGradingCommutesWithSpin : ∀ axis amplitude,
    cubeParityBeta (cubeSpin axis amplitude) =
      cubeSpin axis (cubeParityBeta amplitude)
  quarterTurnHamiltonianCovariance : ∀ axis mass px py pz amplitude,
    cubeQuarterTurn axis
        (interpretedCubeDiracHamiltonian mass px py pz amplitude) =
      interpretedCubeDiracHamiltonian mass
        (cubeRotatedPx axis px py pz)
        (cubeRotatedPy axis px py pz)
        (cubeRotatedPz axis px py pz)
        (cubeQuarterTurn axis amplitude)
  continuousHamiltonianCovariance : ∀ angle axis mass px py pz amplitude,
    cubeContinuousTurn angle axis
        (interpretedCubeDiracHamiltonian mass px py pz amplitude) =
      interpretedCubeDiracHamiltonian mass
        (cubeContinuousRotatedPx angle axis px py pz)
        (cubeContinuousRotatedPy angle axis px py pz)
        (cubeContinuousRotatedPz angle axis px py pz)
        (cubeContinuousTurn angle axis amplitude)
  nativeInnerSelfIsDensity : ∀ amplitude,
    cell8Inner amplitude amplitude = (cell8Density amplitude : ℂ)
  nativeDensityIsNonnegative : ∀ amplitude,
    0 ≤ cell8Density amplitude
  positiveDefiniteNativeInnerProduct : ∀ amplitude,
    cell8Inner amplitude amplitude = 0 ↔ amplitude = 0
  quarterTurnIsUnitary : ∀ axis first second,
    cell8Inner (cubeQuarterTurn axis first)
        (cubeQuarterTurn axis second) = cell8Inner first second
  quarterTurnCoefficientsAreCharacterized :
    ∃! coefficients : ℝ × ℝ,
      admissibleCubeQuarterTurnCoefficients
        coefficients.1 coefficients.2
  continuousRotationComposition : ∀ firstAngle secondAngle axis amplitude,
    cubeContinuousTurn firstAngle axis
        (cubeContinuousTurn secondAngle axis amplitude) =
      cubeContinuousTurn (firstAngle + secondAngle) axis amplitude
  continuousRotationsAreUnitary : ∀ angle axis first second,
    cell8Inner (cubeContinuousTurn angle axis first)
        (cubeContinuousTurn angle axis second) = cell8Inner first second
  continuousTwoPiSign : ∀ axis amplitude,
    cubeContinuousTurn (2 * Real.pi) axis amplitude =
      fun corner => -amplitude corner
  continuousFourPiReturn : ∀ axis amplitude,
    cubeContinuousTurn (4 * Real.pi) axis amplitude = amplitude
  continuousStandardIntertwining :
    (∀ angle axis z,
      cubeContinuousTurn angle axis (cubeDiracEmbedMinus z) =
        cubeDiracEmbedMinus (standardCubeContinuousTurn angle axis z)) ∧
    (∀ angle axis z,
      cubeContinuousTurn angle axis (cubeDiracEmbedPlus z) =
        cubeDiracEmbedPlus (standardCubeContinuousTurn angle axis z))

theorem dirac017_closed_spin_half_representation :
    Dirac017ClosedSpinHalfRepresentationCertificate where
  priorRepresentation := dirac017_native_spin_half
  standardSpinIntertwining :=
    ⟨cube_spin_intertwines_minus, cube_spin_intertwines_plus⟩
  explicitTwoPlusTwoMinusSpectrum := standard_cube_spin0_basis_spectrum
  massGradingCommutesWithSpin := cube_beta_commutes_spin
  quarterTurnHamiltonianCovariance := cube_quarter_turn_hamiltonian_covariance
  continuousHamiltonianCovariance :=
    cube_continuous_turn_hamiltonian_covariance
  nativeInnerSelfIsDensity := cell8_inner_self_eq_density
  nativeDensityIsNonnegative := cell8_density_nonnegative
  positiveDefiniteNativeInnerProduct := cell8_inner_positive_definite
  quarterTurnIsUnitary := cube_quarter_turn_preserves_inner
  quarterTurnCoefficientsAreCharacterized :=
    exists_unique_admissible_cube_quarter_turn_coefficients
  continuousRotationComposition := cube_continuous_turn_add
  continuousRotationsAreUnitary := cube_continuous_turn_preserves_inner
  continuousTwoPiSign := cube_continuous_turn_two_pi
  continuousFourPiReturn := cube_continuous_turn_four_pi
  continuousStandardIntertwining :=
    ⟨cube_continuous_turn_intertwines_minus,
      cube_continuous_turn_intertwines_plus⟩

end
end LeanDirac
