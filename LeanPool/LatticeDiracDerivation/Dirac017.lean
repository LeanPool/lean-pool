/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac017.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac016

/-!
# DIRAC-017: spin one-half derived from native cube rotations

The three signed cube-incidence operators were derived before the standard
Dirac basis was introduced.  This module uses only those native operators to
construct the three oriented cube-plane bivectors.  Their algebra fixes the
normalization of a nonzero rotation generator uniquely: imposing the ordinary
three-axis rotation commutator forces the scale to be `1/2`.

The corresponding geometric quarter-turn is built from the same incidence
operators.  Four quarter-turns act as `-1`, while eight return the native
amplitude.  Thus the `2*pi` sign reversal and `4*pi` return are theorems of the
eight-corner algebra; they are not inserted through an angle-halving rule.

This remains a representation theorem for the already-derived continuum
sector.  It does not establish a localized electron, an electromagnetic
magnetic moment, or a value of `g`.

## Literature lineage

The geometric strategy is informed by the Dirac--Kahler and staggered-fermion
construction surveyed in F. L. Teixeira, *Differential Forms in Lattice Field
Theories: An Overview* (2013), Appendix A, DOI 10.1155/2013/487270.  That
review credits the foundational hypercubic treatments of P. Becher and
H. Joos (1982), DOI 10.1007/BF01614426, and J. M. Rabin (1982), DOI
10.1016/0550-3213(82)90434-5.  This development does not claim the idea of
representing lattice fermions by cell-based Clifford data as original.  Its
specific contribution here is the machine-checked specialization to the
already-derived eight-corner incidence operators, including the unique
nonzero normalization, self-adjointness, Casimir, rotor action, copy
preservation, and explicit claim boundary.
-/

@[expose] public section


namespace LeanDirac

noncomputable section

open Complex

/-! ## Native oriented cube planes -/

def cubePlaneBivector (axis : Fin 3) (amplitude : Cell8) : Cell8 :=
  match axis with
  | 0 => cubeIncidenceGamma 1 (cubeIncidenceGamma 2 amplitude)
  | 1 => cubeIncidenceGamma 2 (cubeIncidenceGamma 0 amplitude)
  | _ => cubeIncidenceGamma 0 (cubeIncidenceGamma 1 amplitude)

def cubeSigma (axis : Fin 3) (amplitude : Cell8) : Cell8 :=
  fun corner => -I * cubePlaneBivector axis amplitude corner

theorem cube_plane_bivector_square
    (axis : Fin 3) (amplitude : Cell8) :
    cubePlaneBivector axis (cubePlaneBivector axis amplitude) =
      fun corner => -amplitude corner := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubePlaneBivector, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2,
      cellBit0, cellBit1]

theorem cube_sigma_square (axis : Fin 3) (amplitude : Cell8) :
    cubeSigma axis (cubeSigma axis amplitude) = amplitude := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeSigma, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cube_sigma_01_product (amplitude : Cell8) :
    cubeSigma 0 (cubeSigma 1 amplitude) =
      fun corner => I * cubeSigma 2 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeSigma, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1]

theorem cube_sigma_10_product (amplitude : Cell8) :
    cubeSigma 1 (cubeSigma 0 amplitude) =
      fun corner => -I * cubeSigma 2 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeSigma, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1]

theorem cube_sigma_12_product (amplitude : Cell8) :
    cubeSigma 1 (cubeSigma 2 amplitude) =
      fun corner => I * cubeSigma 0 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeSigma, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1]

theorem cube_sigma_21_product (amplitude : Cell8) :
    cubeSigma 2 (cubeSigma 1 amplitude) =
      fun corner => -I * cubeSigma 0 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeSigma, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1]

theorem cube_sigma_20_product (amplitude : Cell8) :
    cubeSigma 2 (cubeSigma 0 amplitude) =
      fun corner => I * cubeSigma 1 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeSigma, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1]

theorem cube_sigma_02_product (amplitude : Cell8) :
    cubeSigma 0 (cubeSigma 2 amplitude) =
      fun corner => -I * cubeSigma 1 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeSigma, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1]

/-! ## The rotation algebra selects the nonzero scale -/

def cubeScaledSpin (scale : ℝ) (axis : Fin 3) (amplitude : Cell8) : Cell8 :=
  fun corner => (scale : ℂ) * cubeSigma axis amplitude corner

theorem cube_scaled_spin_commutator_01
    (scale : ℝ) (amplitude : Cell8) :
    (fun corner =>
      cubeScaledSpin scale 0 (cubeScaledSpin scale 1 amplitude) corner -
        cubeScaledSpin scale 1 (cubeScaledSpin scale 0 amplitude) corner) =
      fun corner =>
        ((2 * scale ^ 2 : ℝ) : ℂ) * I * cubeSigma 2 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeScaledSpin, cubeSigma, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1] <;>
    ring

theorem cube_scaled_spin_commutator_12
    (scale : ℝ) (amplitude : Cell8) :
    (fun corner =>
      cubeScaledSpin scale 1 (cubeScaledSpin scale 2 amplitude) corner -
        cubeScaledSpin scale 2 (cubeScaledSpin scale 1 amplitude) corner) =
      fun corner =>
        ((2 * scale ^ 2 : ℝ) : ℂ) * I * cubeSigma 0 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeScaledSpin, cubeSigma, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1] <;>
    ring

theorem cube_scaled_spin_commutator_20
    (scale : ℝ) (amplitude : Cell8) :
    (fun corner =>
      cubeScaledSpin scale 2 (cubeScaledSpin scale 0 amplitude) corner -
        cubeScaledSpin scale 0 (cubeScaledSpin scale 2 amplitude) corner) =
      fun corner =>
        ((2 * scale ^ 2 : ℝ) : ℂ) * I * cubeSigma 1 amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeScaledSpin, cubeSigma, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1] <;>
    ring

def cubeSpinClosureAtScale (scale : ℝ) : Prop :=
  ∀ amplitude : Cell8,
    (fun corner =>
      cubeScaledSpin scale 0 (cubeScaledSpin scale 1 amplitude) corner -
        cubeScaledSpin scale 1 (cubeScaledSpin scale 0 amplitude) corner) =
      fun corner => I * cubeScaledSpin scale 2 amplitude corner

def uniformCubeAmplitude : Cell8 := fun _ => 1

theorem cube_spin_closure_iff_scale_equation (scale : ℝ) :
    cubeSpinClosureAtScale scale ↔ 2 * scale ^ 2 = scale := by
  constructor
  · intro hclosure
    have hcomponent := congrFun (hclosure uniformCubeAmplitude) 0
    simp [uniformCubeAmplitude, cubeScaledSpin, cubeSigma,
      cubePlaneBivector, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2,
      cellBit0, cellBit1] at hcomponent
    apply_fun Complex.re at hcomponent
    norm_num at hcomponent
    nlinarith [hcomponent]
  · intro hscale amplitude
    rw [cube_scaled_spin_commutator_01]
    funext corner
    rw [hscale]
    simp [cubeScaledSpin]
    ring

def admissibleSpinScale (scale : ℝ) : Prop :=
  scale ≠ 0 ∧ cubeSpinClosureAtScale scale

theorem admissible_spin_scale_half : admissibleSpinScale (1 / 2) := by
  constructor
  · norm_num
  · rw [cube_spin_closure_iff_scale_equation]
    norm_num

theorem admissible_spin_scale_unique
    (scale : ℝ) (hscale : admissibleSpinScale scale) :
    scale = 1 / 2 := by
  rcases hscale with ⟨hne, hclosure⟩
  rw [cube_spin_closure_iff_scale_equation] at hclosure
  have hfactor : scale * (2 * scale - 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hzero | hhalf
  · exact (hne hzero).elim
  · nlinarith

theorem exists_unique_admissible_spin_scale :
    ∃! scale : ℝ, admissibleSpinScale scale := by
  refine ⟨1 / 2, admissible_spin_scale_half, ?_⟩
  intro scale hscale
  exact admissible_spin_scale_unique scale hscale

noncomputable def nativeSpinScale : ℝ :=
  Classical.choose exists_unique_admissible_spin_scale

theorem native_spin_scale_admissible :
    admissibleSpinScale nativeSpinScale :=
  (Classical.choose_spec exists_unique_admissible_spin_scale).1

theorem native_spin_scale_eq_half : nativeSpinScale = 1 / 2 :=
  admissible_spin_scale_unique nativeSpinScale native_spin_scale_admissible

def cubeSpin (axis : Fin 3) (amplitude : Cell8) : Cell8 :=
  cubeScaledSpin nativeSpinScale axis amplitude

theorem cube_spin_commutator_01 (amplitude : Cell8) :
    (fun corner =>
      cubeSpin 0 (cubeSpin 1 amplitude) corner -
        cubeSpin 1 (cubeSpin 0 amplitude) corner) =
      fun corner => I * cubeSpin 2 amplitude corner := by
  rw [show cubeSpin = cubeScaledSpin nativeSpinScale from rfl]
  rw [cube_scaled_spin_commutator_01]
  funext corner
  rw [native_spin_scale_eq_half]
  simp [cubeScaledSpin]
  ring

theorem cube_spin_commutator_12 (amplitude : Cell8) :
    (fun corner =>
      cubeSpin 1 (cubeSpin 2 amplitude) corner -
        cubeSpin 2 (cubeSpin 1 amplitude) corner) =
      fun corner => I * cubeSpin 0 amplitude corner := by
  rw [show cubeSpin = cubeScaledSpin nativeSpinScale from rfl]
  rw [cube_scaled_spin_commutator_12]
  funext corner
  rw [native_spin_scale_eq_half]
  simp [cubeScaledSpin]
  ring

theorem cube_spin_commutator_20 (amplitude : Cell8) :
    (fun corner =>
      cubeSpin 2 (cubeSpin 0 amplitude) corner -
        cubeSpin 0 (cubeSpin 2 amplitude) corner) =
      fun corner => I * cubeSpin 1 amplitude corner := by
  rw [show cubeSpin = cubeScaledSpin nativeSpinScale from rfl]
  rw [cube_scaled_spin_commutator_20]
  funext corner
  rw [native_spin_scale_eq_half]
  simp [cubeScaledSpin]
  ring

theorem cube_spin_component_square (axis : Fin 3) (amplitude : Cell8) :
    cubeSpin axis (cubeSpin axis amplitude) =
      fun corner => (1 / 4 : ℂ) * amplitude corner := by
  rw [show cubeSpin = cubeScaledSpin nativeSpinScale from rfl]
  rw [native_spin_scale_eq_half]
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeScaledSpin, cubeSigma, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cube_spin_casimir (amplitude : Cell8) :
    (fun corner =>
      cubeSpin 0 (cubeSpin 0 amplitude) corner +
      cubeSpin 1 (cubeSpin 1 amplitude) corner +
      cubeSpin 2 (cubeSpin 2 amplitude) corner) =
      fun corner => (3 / 4 : ℂ) * amplitude corner := by
  funext corner
  have h0 := congrFun (cube_spin_component_square 0 amplitude) corner
  have h1 := congrFun (cube_spin_component_square 1 amplitude) corner
  have h2 := congrFun (cube_spin_component_square 2 amplitude) corner
  rw [h0, h1, h2]
  ring

def cell8Inner (first second : Cell8) : ℂ :=
  ∑ corner, star (first corner) * second corner

theorem cube_sigma_self_adjoint
    (axis : Fin 3) (first second : Cell8) :
    cell8Inner first (cubeSigma axis second) =
      cell8Inner (cubeSigma axis first) second := by
  fin_cases axis <;>
    apply Complex.ext <;>
    simp [cell8Inner, cubeSigma, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem cube_spin_self_adjoint
    (axis : Fin 3) (first second : Cell8) :
    cell8Inner first (cubeSpin axis second) =
      cell8Inner (cubeSpin axis first) second := by
  rw [show cubeSpin = cubeScaledSpin nativeSpinScale from rfl]
  rw [native_spin_scale_eq_half]
  fin_cases axis <;>
    apply Complex.ext <;>
    simp [cell8Inner, cubeScaledSpin, cubeSigma, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1,
      Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im] <;>
    ring

/-! ## A quarter-turn built from the native incidence algebra -/

theorem sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by positivity

def cubeQuarterTurn (axis : Fin 3) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    (((1 / Real.sqrt 2 : ℝ) : ℂ) *
      (amplitude corner - cubePlaneBivector axis amplitude corner))

def cubeQuarterTurnInverse (axis : Fin 3) (amplitude : Cell8) : Cell8 :=
  fun corner =>
    (((1 / Real.sqrt 2 : ℝ) : ℂ) *
      (amplitude corner + cubePlaneBivector axis amplitude corner))

theorem cube_quarter_turn_inverse
    (axis : Fin 3) (amplitude : Cell8) :
    cubeQuarterTurnInverse axis (cubeQuarterTurn axis amplitude) =
      amplitude := by
  have hsqrtTwoComplex : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by
    exact_mod_cast sqrt_two_sq
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeQuarterTurnInverse, cubeQuarterTurn,
      cubePlaneBivector, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2,
      cellBit0, cellBit1] <;>
    field_simp [sqrt_two_ne_zero] <;>
    ring_nf <;> rw [hsqrtTwoComplex]

theorem cube_quarter_turn_four (axis : Fin 3) (amplitude : Cell8) :
    cubeQuarterTurn axis
      (cubeQuarterTurn axis
        (cubeQuarterTurn axis (cubeQuarterTurn axis amplitude))) =
      fun corner => -amplitude corner := by
  have hsqrtTwoComplexPowFour : (((Real.sqrt 2 : ℝ) : ℂ) ^ 4) = 4 := by
    exact_mod_cast sqrt_two_pow_four
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1] <;>
    field_simp [sqrt_two_ne_zero] <;>
    ring_nf <;> rw [hsqrtTwoComplexPowFour]

theorem cube_quarter_turn_eight (axis : Fin 3) (amplitude : Cell8) :
    cubeQuarterTurn axis
      (cubeQuarterTurn axis
        (cubeQuarterTurn axis
          (cubeQuarterTurn axis
            (cubeQuarterTurn axis
              (cubeQuarterTurn axis
                (cubeQuarterTurn axis (cubeQuarterTurn axis amplitude))))))) =
      amplitude := by
  rw [cube_quarter_turn_four]
  funext corner
  rw [congrFun (cube_quarter_turn_four axis amplitude) corner]
  simp

theorem cube_quarter_turn_axis0_rotates_gamma1 (amplitude : Cell8) :
    cubeQuarterTurn 0 (cubeIncidenceGamma 1 amplitude) =
      cubeIncidenceGamma 2 (cubeQuarterTurn 0 amplitude) := by
  funext corner
  fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip1,
      cellFlip2, cellBit0, cellBit1] <;> ring

theorem cube_quarter_turn_axis0_rotates_gamma2 (amplitude : Cell8) :
    cubeQuarterTurn 0 (cubeIncidenceGamma 2 amplitude) =
      fun corner => -cubeIncidenceGamma 1 (cubeQuarterTurn 0 amplitude) corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip1,
      cellFlip2, cellBit0, cellBit1] <;> ring

theorem cube_quarter_turn_axis0_fixes_gamma0 (amplitude : Cell8) :
    cubeQuarterTurn 0 (cubeIncidenceGamma 0 amplitude) =
      cubeIncidenceGamma 0 (cubeQuarterTurn 0 amplitude) := by
  funext corner
  fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1]

theorem cube_quarter_turn_axis1_rotates_gamma2 (amplitude : Cell8) :
    cubeQuarterTurn 1 (cubeIncidenceGamma 2 amplitude) =
      cubeIncidenceGamma 0 (cubeQuarterTurn 1 amplitude) := by
  funext corner
  fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0,
      cellFlip2, cellBit0, cellBit1] <;> ring

theorem cube_quarter_turn_axis1_rotates_gamma0 (amplitude : Cell8) :
    cubeQuarterTurn 1 (cubeIncidenceGamma 0 amplitude) =
      fun corner => -cubeIncidenceGamma 2 (cubeQuarterTurn 1 amplitude) corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0,
      cellFlip2, cellBit0, cellBit1] <;> ring

theorem cube_quarter_turn_axis1_fixes_gamma1 (amplitude : Cell8) :
    cubeQuarterTurn 1 (cubeIncidenceGamma 1 amplitude) =
      cubeIncidenceGamma 1 (cubeQuarterTurn 1 amplitude) := by
  funext corner
  fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1] <;> ring

theorem cube_quarter_turn_axis2_rotates_gamma0 (amplitude : Cell8) :
    cubeQuarterTurn 2 (cubeIncidenceGamma 0 amplitude) =
      cubeIncidenceGamma 1 (cubeQuarterTurn 2 amplitude) := by
  funext corner
  fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellBit0] <;> ring

theorem cube_quarter_turn_axis2_rotates_gamma1 (amplitude : Cell8) :
    cubeQuarterTurn 2 (cubeIncidenceGamma 1 amplitude) =
      fun corner => -cubeIncidenceGamma 0 (cubeQuarterTurn 2 amplitude) corner := by
  funext corner
  fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellBit0] <;> ring

theorem cube_quarter_turn_axis2_fixes_gamma2 (amplitude : Cell8) :
    cubeQuarterTurn 2 (cubeIncidenceGamma 2 amplitude) =
      cubeIncidenceGamma 2 (cubeQuarterTurn 2 amplitude) := by
  funext corner
  fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1] <;> ring

theorem cube_quarter_turn_is_spin_rotor
    (axis : Fin 3) (amplitude : Cell8) :
    cubeQuarterTurn axis amplitude =
      fun corner => (((1 / Real.sqrt 2 : ℝ) : ℂ) *
        (amplitude corner - 2 * I * cubeSpin axis amplitude corner)) := by
  rw [show cubeSpin = cubeScaledSpin nativeSpinScale from rfl]
  rw [native_spin_scale_eq_half]
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeQuarterTurn, cubeScaledSpin, cubeSigma,
      cubePlaneBivector, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2,
      cellBit0, cellBit1] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem cube_quarter_turn_preserves_density
    (axis : Fin 3) (amplitude : Cell8) :
    cell8Density (cubeQuarterTurn axis amplitude) =
      cell8Density amplitude := by
  fin_cases axis <;>
    simp [cell8Density, cubeQuarterTurn, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1,
      Complex.normSq, Complex.mul_re, Complex.mul_im,
      Fin.sum_univ_succ] <;>
    field_simp [sqrt_two_ne_zero] <;>
    ring_nf <;>
    nlinarith [sqrt_two_sq]

/-! ## Both native copies carry the same spin algebra -/

theorem cube_flavor_commutes_spin
    (axis : Fin 3) (amplitude : Cell8) :
    cubeFlavor (cubeSpin axis amplitude) =
      cubeSpin axis (cubeFlavor amplitude) := by
  rw [show cubeSpin = cubeScaledSpin nativeSpinScale from rfl]
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeScaledSpin, cubeSigma, cubePlaneBivector,
      cubeFlavor, cubeFlavorSign, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1, cellBit2] <;>
    ring

theorem cube_flavor_commutes_quarter_turn
    (axis : Fin 3) (amplitude : Cell8) :
    cubeFlavor (cubeQuarterTurn axis amplitude) =
      cubeQuarterTurn axis (cubeFlavor amplitude) := by
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeFlavor,
      cubeFlavorSign, cubeIncidenceGamma, cubeIncidenceSign,
      cubeIncidenceFlip, cellFlip0, cellFlip1, cellFlip2,
      cellBit0, cellBit1, cellBit2] <;>
    ring

theorem cube_quarter_turn_preserves_minus_copy
    (axis : Fin 3) (z : Cell4) :
    cubeFlavor (cubeQuarterTurn axis (cubeDiracEmbedMinus z)) =
      fun corner =>
        -cubeQuarterTurn axis (cubeDiracEmbedMinus z) corner := by
  rw [cube_flavor_commutes_quarter_turn,
    cube_dirac_embed_minus_has_negative_flavor]
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeQuarterTurn, cubePlaneBivector, cubeIncidenceGamma,
      cubeIncidenceSign, cubeIncidenceFlip, cellFlip0, cellFlip1,
      cellFlip2, cellBit0, cellBit1] <;> ring

theorem cube_quarter_turn_preserves_plus_copy
    (axis : Fin 3) (z : Cell4) :
    cubeFlavor (cubeQuarterTurn axis (cubeDiracEmbedPlus z)) =
      cubeQuarterTurn axis (cubeDiracEmbedPlus z) := by
  rw [cube_flavor_commutes_quarter_turn,
    cube_dirac_embed_plus_has_positive_flavor]

theorem cube_spin_preserves_minus_copy (axis : Fin 3) (z : Cell4) :
    cubeFlavor (cubeSpin axis (cubeDiracEmbedMinus z)) =
      fun corner => -cubeSpin axis (cubeDiracEmbedMinus z) corner := by
  rw [cube_flavor_commutes_spin, cube_dirac_embed_minus_has_negative_flavor]
  funext corner
  fin_cases axis <;> fin_cases corner <;>
    simp [cubeSpin, cubeScaledSpin, cubeSigma, cubePlaneBivector,
      cubeIncidenceGamma, cubeIncidenceSign, cubeIncidenceFlip,
      cellFlip0, cellFlip1, cellFlip2, cellBit0, cellBit1]

theorem cube_spin_preserves_plus_copy (axis : Fin 3) (z : Cell4) :
    cubeFlavor (cubeSpin axis (cubeDiracEmbedPlus z)) =
      cubeSpin axis (cubeDiracEmbedPlus z) := by
  rw [cube_flavor_commutes_spin, cube_dirac_embed_plus_has_positive_flavor]

structure Dirac017NativeSpinHalfCertificate : Prop where
  priorDerivation : Dirac016CopyTranslationCertificate
  nativePlaneSquare : ∀ axis amplitude,
    cubePlaneBivector axis (cubePlaneBivector axis amplitude) =
      fun corner => -amplitude corner
  unscaledSpinSquare : ∀ axis amplitude,
    cubeSigma axis (cubeSigma axis amplitude) = amplitude
  closureCriterionIsNativeCommutator : ∀ scale : ℝ,
    cubeSpinClosureAtScale scale ↔ 2 * scale ^ 2 = scale
  scaleIsDerivedAndUnique :
    ∃! scale : ℝ, admissibleSpinScale scale
  selectedScaleIsHalf : nativeSpinScale = 1 / 2
  spinCommutator01 : ∀ amplitude,
    (fun corner =>
      cubeSpin 0 (cubeSpin 1 amplitude) corner -
        cubeSpin 1 (cubeSpin 0 amplitude) corner) =
      fun corner => I * cubeSpin 2 amplitude corner
  spinCommutator12 : ∀ amplitude,
    (fun corner =>
      cubeSpin 1 (cubeSpin 2 amplitude) corner -
        cubeSpin 2 (cubeSpin 1 amplitude) corner) =
      fun corner => I * cubeSpin 0 amplitude corner
  spinCommutator20 : ∀ amplitude,
    (fun corner =>
      cubeSpin 2 (cubeSpin 0 amplitude) corner -
        cubeSpin 0 (cubeSpin 2 amplitude) corner) =
      fun corner => I * cubeSpin 1 amplitude corner
  componentSquare : ∀ axis amplitude,
    cubeSpin axis (cubeSpin axis amplitude) =
      fun corner => (1 / 4 : ℂ) * amplitude corner
  spinCasimir : ∀ amplitude,
    (fun corner =>
      cubeSpin 0 (cubeSpin 0 amplitude) corner +
      cubeSpin 1 (cubeSpin 1 amplitude) corner +
      cubeSpin 2 (cubeSpin 2 amplitude) corner) =
      fun corner => (3 / 4 : ℂ) * amplitude corner
  spinGeneratorsAreSelfAdjoint : ∀ axis first second,
    cell8Inner first (cubeSpin axis second) =
      cell8Inner (cubeSpin axis first) second
  quarterTurnRotatesCubeAxes : ∀ amplitude,
    cubeQuarterTurn 0 (cubeIncidenceGamma 1 amplitude) =
      cubeIncidenceGamma 2 (cubeQuarterTurn 0 amplitude)
  quarterTurnRotatesAllThreePlanes :
    (∀ amplitude,
      cubeQuarterTurn 1 (cubeIncidenceGamma 2 amplitude) =
        cubeIncidenceGamma 0 (cubeQuarterTurn 1 amplitude)) ∧
    (∀ amplitude,
      cubeQuarterTurn 2 (cubeIncidenceGamma 0 amplitude) =
        cubeIncidenceGamma 1 (cubeQuarterTurn 2 amplitude))
  quarterTurnFixesOwnAxis :
    (∀ amplitude,
      cubeQuarterTurn 0 (cubeIncidenceGamma 0 amplitude) =
        cubeIncidenceGamma 0 (cubeQuarterTurn 0 amplitude)) ∧
    (∀ amplitude,
      cubeQuarterTurn 1 (cubeIncidenceGamma 1 amplitude) =
        cubeIncidenceGamma 1 (cubeQuarterTurn 1 amplitude)) ∧
    (∀ amplitude,
      cubeQuarterTurn 2 (cubeIncidenceGamma 2 amplitude) =
        cubeIncidenceGamma 2 (cubeQuarterTurn 2 amplitude))
  twoPiSign : ∀ axis amplitude,
    cubeQuarterTurn axis
      (cubeQuarterTurn axis
        (cubeQuarterTurn axis (cubeQuarterTurn axis amplitude))) =
      fun corner => -amplitude corner
  fourPiReturn : ∀ axis amplitude,
    cubeQuarterTurn axis
      (cubeQuarterTurn axis
        (cubeQuarterTurn axis
          (cubeQuarterTurn axis
            (cubeQuarterTurn axis
              (cubeQuarterTurn axis
                (cubeQuarterTurn axis (cubeQuarterTurn axis amplitude))))))) =
      amplitude
  quarterTurnPreservesDensity : ∀ axis amplitude,
    cell8Density (cubeQuarterTurn axis amplitude) = cell8Density amplitude
  copiesRemainIndependent :
    (∀ axis z, cubeFlavor (cubeSpin axis (cubeDiracEmbedMinus z)) =
      fun corner => -cubeSpin axis (cubeDiracEmbedMinus z) corner) ∧
    (∀ axis z, cubeFlavor (cubeSpin axis (cubeDiracEmbedPlus z)) =
      cubeSpin axis (cubeDiracEmbedPlus z))
  quarterTurnPreservesCopies :
    (∀ axis z,
      cubeFlavor (cubeQuarterTurn axis (cubeDiracEmbedMinus z)) =
        fun corner =>
          -cubeQuarterTurn axis (cubeDiracEmbedMinus z) corner) ∧
    (∀ axis z,
      cubeFlavor (cubeQuarterTurn axis (cubeDiracEmbedPlus z)) =
        cubeQuarterTurn axis (cubeDiracEmbedPlus z))

theorem dirac017_native_spin_half : Dirac017NativeSpinHalfCertificate where
  priorDerivation := dirac016_exact_copy_translation_structure
  nativePlaneSquare := cube_plane_bivector_square
  unscaledSpinSquare := cube_sigma_square
  closureCriterionIsNativeCommutator := cube_spin_closure_iff_scale_equation
  scaleIsDerivedAndUnique := exists_unique_admissible_spin_scale
  selectedScaleIsHalf := native_spin_scale_eq_half
  spinCommutator01 := cube_spin_commutator_01
  spinCommutator12 := cube_spin_commutator_12
  spinCommutator20 := cube_spin_commutator_20
  componentSquare := cube_spin_component_square
  spinCasimir := cube_spin_casimir
  spinGeneratorsAreSelfAdjoint := cube_spin_self_adjoint
  quarterTurnRotatesCubeAxes := cube_quarter_turn_axis0_rotates_gamma1
  quarterTurnRotatesAllThreePlanes :=
    ⟨cube_quarter_turn_axis1_rotates_gamma2,
      cube_quarter_turn_axis2_rotates_gamma0⟩
  quarterTurnFixesOwnAxis :=
    ⟨cube_quarter_turn_axis0_fixes_gamma0,
      cube_quarter_turn_axis1_fixes_gamma1,
      cube_quarter_turn_axis2_fixes_gamma2⟩
  twoPiSign := cube_quarter_turn_four
  fourPiReturn := cube_quarter_turn_eight
  quarterTurnPreservesDensity := cube_quarter_turn_preserves_density
  copiesRemainIndependent :=
    ⟨cube_spin_preserves_minus_copy, cube_spin_preserves_plus_copy⟩
  quarterTurnPreservesCopies :=
    ⟨cube_quarter_turn_preserves_minus_copy,
      cube_quarter_turn_preserves_plus_copy⟩

end
end LeanDirac
