/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumEulerLagrange
public import LeanPool.LatticeDiracDerivation.V2.CubicalClifford
import Mathlib.Tactic.Abel

/-!
# The oriented-cube square root of the native C19 continuum Hessian

The action first supplies a scalar continuum Hessian.  The only geometric
input added here is an orientation and ordering of the three cube axes.  That
ordered cube has a canonical signed incidence action: crossing axis `a`
acquires the Koszul sign determined by the lower ordered bits.  This is the
`cubicalGamma` operator already constructed without a spinor or matrix.

This file fixes the scale of that first-order incidence operator from the C19
second moment and proves that its massive square is exactly the continuum
Hessian extracted from the native action.  Four-by-four alpha and beta
matrices occur only at the end, as coordinates on the two derived flavor
fibers.

The theorem is a root characterization, not a claim that the eight fiber
coordinates are eight physical lattice sites.  A global change of cube
orientation and the two commuting flavor sectors remain genuine coordinate
freedoms.
-/

@[expose] public section

namespace LeanDirac.V2

open Complex
noncomputable section

/-! ## Characterization by oriented incidence -/

/-- Crossing a lower ordered axis changes the orientation sign; crossing
the selected or a higher axis preserves it. -/
def koszulFlipFactor (axis other : Fin 3) : ℂ :=
  if other.val < axis.val then -1 else 1

/-- Recursive orientation law for the sign attached to one cubical axis.
It starts at the all-zero corner and propagates across the cube; the closed
lower-bit formula is not part of this specification. -/
structure RecursiveKoszulSignLaw
    (axis : Fin 3) (sign : CubicalCorner → ℂ) : Prop where
  normalized : sign 0 = 1
  flipLaw : ∀ other corner,
    sign (cubicalFlip other corner) =
      koszulFlipFactor axis other * sign corner

theorem cubical_incidence_sign_obeys_recursive_koszul
    (axis : Fin 3) :
    RecursiveKoszulSignLaw axis (cubicalIncidenceSign axis) := by
  have normalized : ∀ axis : Fin 3, cubicalIncidenceSignInteger axis 0 = 1 := by decide
  have flip : ∀ (axis other : Fin 3) (corner : CubicalCorner),
      cubicalIncidenceSignInteger axis (cubicalFlip other corner) =
        (if other.val < axis.val then (-1 : ℤ) else 1) *
          cubicalIncidenceSignInteger axis corner := by decide
  constructor
  · simp only [cubicalIncidenceSign, normalized, Int.cast_one]
  · intro other corner
    simp only [cubicalIncidenceSign, flip, Int.cast_mul, koszulFlipFactor]
    split <;> simp only [Int.cast_neg, Int.cast_one]

/-- Two sign functions satisfying the same recursive oriented-cube law are
equal.  This graph argument does not inspect either sign's closed formula. -/
theorem recursive_koszul_sign_ext
    (axis : Fin 3) (first second : CubicalCorner → ℂ)
    (hfirst : RecursiveKoszulSignLaw axis first)
    (hsecond : RecursiveKoszulSignLaw axis second) :
    first = second := by
  have h0 : first 0 = second 0 := by
    rw [hfirst.normalized, hsecond.normalized]
  have h1 : first 1 = second 1 := by
    change first (cubicalFlip (2 : Fin 3) 0) =
      second (cubicalFlip (2 : Fin 3) 0)
    rw [hfirst.flipLaw, hsecond.flipLaw, h0]
  have h2 : first 2 = second 2 := by
    change first (cubicalFlip (1 : Fin 3) 0) =
      second (cubicalFlip (1 : Fin 3) 0)
    rw [hfirst.flipLaw, hsecond.flipLaw, h0]
  have h3 : first 3 = second 3 := by
    change first (cubicalFlip (2 : Fin 3) 2) =
      second (cubicalFlip (2 : Fin 3) 2)
    rw [hfirst.flipLaw, hsecond.flipLaw, h2]
  have h4 : first 4 = second 4 := by
    change first (cubicalFlip (0 : Fin 3) 0) =
      second (cubicalFlip (0 : Fin 3) 0)
    rw [hfirst.flipLaw, hsecond.flipLaw, h0]
  have h5 : first 5 = second 5 := by
    change first (cubicalFlip (2 : Fin 3) 4) =
      second (cubicalFlip (2 : Fin 3) 4)
    rw [hfirst.flipLaw, hsecond.flipLaw, h4]
  have h6 : first 6 = second 6 := by
    change first (cubicalFlip (1 : Fin 3) 4) =
      second (cubicalFlip (1 : Fin 3) 4)
    rw [hfirst.flipLaw, hsecond.flipLaw, h4]
  have h7 : first 7 = second 7 := by
    change first (cubicalFlip (2 : Fin 3) 6) =
      second (cubicalFlip (2 : Fin 3) 6)
    rw [hfirst.flipLaw, hsecond.flipLaw, h6]
  funext corner
  fin_cases corner
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

/-- The recursive oriented-cube laws uniquely determine the closed Koszul
sign formula.  The theorem is relative to the chosen axis order and global
orientation, not a selection of those conventions by the scalar action. -/
theorem recursive_koszul_sign_unique
    (axis : Fin 3) (sign : CubicalCorner → ℂ)
    (hsign : RecursiveKoszulSignLaw axis sign) :
    sign = cubicalIncidenceSign axis :=
  recursive_koszul_sign_ext axis sign (cubicalIncidenceSign axis)
    hsign (cubical_incidence_sign_obeys_recursive_koszul axis)

/-- A linear operator is the oriented incidence crossing for `axis` when it
flips precisely that cube bit and carries the Koszul sign fixed by the ordered
cube orientation.  This specification contains no Dirac matrix. -/
def IsOrientedCubicalIncidence
    (axis : Fin 3) (operator : CubicalCell8 → CubicalCell8) : Prop :=
  ∀ amplitude corner,
    operator amplitude corner =
      cubicalIncidenceSign axis corner *
        amplitude (cubicalFlip axis corner)

theorem cubical_gamma_is_oriented_incidence (axis : Fin 3) :
    IsOrientedCubicalIncidence axis (cubicalGamma axis) := by
  intro amplitude corner
  rfl

/-- Once the cube orientation and its axis order are fixed, the signed
incidence crossing is unique.  This is deliberately not a claim that the
native action selects a preferred global orientation. -/
theorem oriented_cubical_incidence_unique
    (axis : Fin 3) (operator : CubicalCell8 → CubicalCell8)
    (hoperator : IsOrientedCubicalIncidence axis operator) :
    operator = cubicalGamma axis := by
  funext amplitude corner
  exact hoperator amplitude corner

/-- Degree parity is the canonical grading of the cubical exterior fiber. -/
def cubicalDegreeParitySign (corner : CubicalCorner) : ℂ :=
  if (cubicalBit0 corner + cubicalBit1 corner +
      cubicalBit2 corner) % 2 = 0 then 1 else -1

/-- A grading of cube corners compatible with the oriented degree changes. -/
def IsCubicalDegreeGrading
    (operator : CubicalCell8 → CubicalCell8) : Prop :=
  ∀ amplitude corner,
    operator amplitude corner =
      cubicalDegreeParitySign corner * amplitude corner

theorem cubical_beta_is_degree_grading :
    IsCubicalDegreeGrading cubicalBeta := by
  intro amplitude corner
  fin_cases corner <;>
    simp [cubicalBeta, cubicalDegreeParitySign,
      cubicalBit0, cubicalBit1, cubicalBit2]

/-- The mass grading is unique once the cubical degree parity is fixed; no
matrix-valued mass rule is supplied independently. -/
theorem cubical_degree_grading_unique
    (operator : CubicalCell8 → CubicalCell8)
    (hoperator : IsCubicalDegreeGrading operator) :
    operator = cubicalBeta := by
  funext amplitude corner
  rw [hoperator amplitude corner]
  exact (cubical_beta_is_degree_grading amplitude corner).symm

/-! ## The incidence law is the cubical cell differential

The eight labels are the eight oriented cells of the exterior algebra of
the three coordinate directions: a bit records whether that direction is
present in the cell label.  The following creation and contraction maps are
therefore the ordinary cubical coboundary and its reverse incidence map.
Their sum recovers `cubicalGamma`; the Clifford signs are consequently cell
orientation signs, rather than separately supplied matrices.
-/

/-- Membership of one coordinate direction in a cubical cell label. -/
def cubicalAxisBit (axis : Fin 3) (corner : CubicalCorner) : Nat :=
  match axis with
  | 0 => cubicalBit0 corner
  | 1 => cubicalBit1 corner
  | _ => cubicalBit2 corner

/-- The signed crossing in one axis restricted by the bit of the target cell. -/
def cubicalSelectedIncidence (degree : Fin 2) (axis : Fin 3)
    (amplitude : CubicalCell8) : CubicalCell8 := fun corner =>
  if cubicalAxisBit axis corner = degree.val then cubicalGamma axis amplitude corner else 0

/-- The oriented coboundary on one axis adds the axis to the cell label. -/
def cubicalCoboundaryAxis (axis : Fin 3) (amplitude : CubicalCell8) : CubicalCell8 :=
  cubicalSelectedIncidence 1 axis amplitude

/-- Reverse cubical incidence contracts one axis. -/
def cubicalBoundaryAxis (axis : Fin 3) (amplitude : CubicalCell8) : CubicalCell8 :=
  cubicalSelectedIncidence 0 axis amplitude

/-- Sum the incidence maps that raise the cubical degree. -/
def cubicalExteriorDerivative (amplitude : CubicalCell8) : CubicalCell8 :=
  fun corner => ∑ axis : Fin 3, cubicalCoboundaryAxis axis amplitude corner

/-- Sum the incidence maps that lower the cubical degree. -/
def cubicalExteriorCoderivative (amplitude : CubicalCell8) : CubicalCell8 :=
  fun corner => ∑ axis : Fin 3, cubicalBoundaryAxis axis amplitude corner

/-- The Kähler--Dirac incidence operator of the oriented three-cube. -/
def cubicalKahlerDirac (amplitude : CubicalCell8) : CubicalCell8 :=
  fun corner => cubicalExteriorDerivative amplitude corner +
    cubicalExteriorCoderivative amplitude corner

/-- Directionally weighted cell-incidence operator.  The three coefficients
will later be fixed by the C19 second moment. -/
def cubicalWeightedCellIncidence
    (k0 k1 k2 : ℂ) (amplitude : CubicalCell8) : CubicalCell8 :=
  fun corner =>
    k0 * (cubicalCoboundaryAxis 0 amplitude corner +
      cubicalBoundaryAxis 0 amplitude corner) +
    k1 * (cubicalCoboundaryAxis 1 amplitude corner +
      cubicalBoundaryAxis 1 amplitude corner) +
    k2 * (cubicalCoboundaryAxis 2 amplitude corner +
      cubicalBoundaryAxis 2 amplitude corner)

/-- On each axis, coboundary plus reverse incidence is the previously used
signed bit crossing. -/
theorem cubical_boundary_coboundary_axis_eq_gamma
    (axis : Fin 3) (amplitude : CubicalCell8) :
    (fun corner =>
      cubicalCoboundaryAxis axis amplitude corner +
        cubicalBoundaryAxis axis amplitude corner) =
      cubicalGamma axis amplitude := by
  funext corner
  have bit_range (axis : Fin 3) (corner : CubicalCorner) :
      cubicalAxisBit axis corner = 0 ∨ cubicalAxisBit axis corner = 1 := by
    decide +revert
  rcases bit_range axis corner with zero_bit | one_bit
  · simp [cubicalCoboundaryAxis, cubicalBoundaryAxis, cubicalSelectedIncidence, zero_bit]
  · simp [cubicalCoboundaryAxis, cubicalBoundaryAxis, cubicalSelectedIncidence, one_bit]

private theorem cubical_selected_incidence_square_zero (degree : Fin 2) (amplitude : CubicalCell8) :
    let operator (field : CubicalCell8) : CubicalCell8 := fun corner =>
      ∑ axis : Fin 3, cubicalSelectedIncidence degree axis field corner
    operator (operator amplitude) = fun _ => 0 := by
  dsimp only
  funext corner
  have flip_own (axis : Fin 3) (corner : CubicalCorner) (degree : Fin 2) :
      ¬(cubicalAxisBit axis corner = degree.val ∧
        cubicalAxisBit axis (cubicalFlip axis corner) = degree.val) := by
    decide +revert
  have flip_other (axis other : Fin 3) (distinct : axis ≠ other) (corner : CubicalCorner) :
      cubicalAxisBit other (cubicalFlip axis corner) = cubicalAxisBit other corner := by
    decide +revert
  have distribute (axis : Fin 3) :
      cubicalSelectedIncidence degree axis
          (fun c => ∑ other : Fin 3, cubicalSelectedIncidence degree other amplitude c) corner =
        ∑ other : Fin 3,
          cubicalSelectedIncidence degree axis (cubicalSelectedIncidence degree other amplitude)
            corner := by
    by_cases selected : cubicalAxisBit axis corner = degree.val
    · simp only [cubicalSelectedIncidence, selected, ite_true, cubicalGamma, Finset.mul_sum]
    · simp only [cubicalSelectedIncidence, selected, ite_false, Finset.sum_const_zero]
  have composition (axis other : Fin 3) :
      cubicalSelectedIncidence degree axis
          (cubicalSelectedIncidence degree other amplitude) corner =
        if cubicalAxisBit axis corner = degree.val ∧
            cubicalAxisBit other (cubicalFlip axis corner) = degree.val
        then cubicalGamma axis (cubicalGamma other amplitude) corner else 0 := by
    by_cases axis_selected : cubicalAxisBit axis corner = degree.val <;>
      by_cases other_selected : cubicalAxisBit other (cubicalFlip axis corner) = degree.val <;>
      simp only [cubicalSelectedIncidence, cubicalGamma, axis_selected, other_selected, ite_true,
        ite_false, true_and, false_and, and_false, mul_zero]
  have diagonal (axis : Fin 3) :
      cubicalSelectedIncidence degree axis (cubicalSelectedIncidence degree axis amplitude) corner =
        0 := by
    rw [composition, ite_eq_right (flip_own axis corner degree)]
  have anticommutation (axis other : Fin 3) (distinct : axis ≠ other) :
      cubicalSelectedIncidence degree axis
          (cubicalSelectedIncidence degree other amplitude) corner =
        -cubicalSelectedIncidence degree other (cubicalSelectedIncidence degree axis amplitude)
          corner := by
    rw [composition, composition, flip_other axis other distinct,
      flip_other other axis distinct.symm]
    by_cases axis_selected : cubicalAxisBit axis corner = degree.val <;>
      by_cases other_selected : cubicalAxisBit other corner = degree.val <;>
      simp only [axis_selected, other_selected, true_and, false_and, and_false, ite_true,
        ite_false, neg_zero]
    exact congrFun (cubical_gamma_anticommute axis other distinct amplitude) corner
  simp_rw [distribute]
  simp only [Fin.sum_univ_three, diagonal]
  rw [anticommutation 0 1 (by decide), anticommutation 0 2 (by decide),
    anticommutation 1 2 (by decide)]
  abel

/-- The cubical coboundary is a differential because oriented two-step faces cancel. -/
theorem cubical_exterior_derivative_square_zero (amplitude : CubicalCell8) :
    cubicalExteriorDerivative (cubicalExteriorDerivative amplitude) =
      fun _ => 0 :=
  cubical_selected_incidence_square_zero 1 amplitude

/-- The reverse incidence map is nilpotent by the same face cancellation. -/
theorem cubical_exterior_coderivative_square_zero (amplitude : CubicalCell8) :
    cubicalExteriorCoderivative (cubicalExteriorCoderivative amplitude) =
      fun _ => 0 :=
  cubical_selected_incidence_square_zero 0 amplitude

/-- Summing the three oriented axis-incidence crossings is precisely the
Kähler--Dirac operator `d + d†` of the cube. -/
theorem cubical_kahler_dirac_eq_incidence_linear
    (amplitude : CubicalCell8) :
    cubicalKahlerDirac amplitude =
      cubicalIncidenceLinear 1 1 1 amplitude := by
  funext corner
  unfold cubicalKahlerDirac cubicalExteriorDerivative cubicalExteriorCoderivative
    cubicalIncidenceLinear
  rw [← Finset.sum_add_distrib]
  simp only [Fin.sum_univ_three, one_mul]
  rw [congrFun (cubical_boundary_coboundary_axis_eq_gamma 0 amplitude) corner,
    congrFun (cubical_boundary_coboundary_axis_eq_gamma 1 amplitude) corner,
    congrFun (cubical_boundary_coboundary_axis_eq_gamma 2 amplitude) corner]

/-- Every weighted first-order root used below is therefore a weighted
oriented-cell incidence operator, not an independently introduced matrix. -/
theorem cubical_weighted_cell_incidence_eq_incidence_linear
    (k0 k1 k2 : ℂ) (amplitude : CubicalCell8) :
    cubicalWeightedCellIncidence k0 k1 k2 amplitude =
      cubicalIncidenceLinear k0 k1 k2 amplitude := by
  funext corner
  unfold cubicalWeightedCellIncidence cubicalIncidenceLinear
  rw [show cubicalCoboundaryAxis 0 amplitude corner +
        cubicalBoundaryAxis 0 amplitude corner =
      cubicalGamma 0 amplitude corner by
        exact congrFun
          (cubical_boundary_coboundary_axis_eq_gamma 0 amplitude) corner,
    show cubicalCoboundaryAxis 1 amplitude corner +
        cubicalBoundaryAxis 1 amplitude corner =
      cubicalGamma 1 amplitude corner by
        exact congrFun
          (cubical_boundary_coboundary_axis_eq_gamma 1 amplitude) corner,
    show cubicalCoboundaryAxis 2 amplitude corner +
        cubicalBoundaryAxis 2 amplitude corner =
      cubicalGamma 2 amplitude corner by
        exact congrFun
          (cubical_boundary_coboundary_axis_eq_gamma 2 amplitude) corner]

/-- The square of the unit cubical Kähler--Dirac operator is the scalar
three-dimensional cell Laplacian. -/
theorem cubical_kahler_dirac_square (amplitude : CubicalCell8) :
    cubicalKahlerDirac (cubicalKahlerDirac amplitude) =
      fun corner => 3 * amplitude corner := by
  rw [cubical_kahler_dirac_eq_incidence_linear,
    cubical_kahler_dirac_eq_incidence_linear,
    cubical_incidence_linear_square]
  funext corner
  norm_num

/-- The mass grading is the parity of the native cubical cell degree. -/
theorem cubical_beta_is_exterior_degree_parity (amplitude : CubicalCell8) :
    cubicalBeta amplitude = fun corner =>
      (if (cubicalAxisBit 0 corner + cubicalAxisBit 1 corner +
          cubicalAxisBit 2 corner) % 2 = 0 then 1 else -1) *
        amplitude corner := by
  funext corner
  fin_cases corner <;>
    simp [cubicalBeta, cubicalAxisBit, cubicalBit0, cubicalBit1,
      cubicalBit2]

/-! ## C19 fixes the scale -/

/-- The positive scale of a first-order cubic incidence root is uniquely
fixed by the diagonal C19 second moment. -/
theorem c19_incidence_scale_unique
    (scale : ℝ) (hscale : 0 ≤ scale)
    (hmoment : scale ^ 2 = c19SecondMoment 0 0) :
    scale = c19ContinuumSpeed := by
  have hm : c19SecondMoment 0 0 = 12 := by
    simpa using c19_second_moment_isotropic (0 : Fin 3) (0 : Fin 3)
  have hsquare : scale ^ 2 = 12 := by simpa [hm] using hmoment
  have hc : c19ContinuumSpeed ^ 2 = 12 := c19_continuum_speed_square
  exact (sq_eq_sq₀ hscale (by simp [c19ContinuumSpeed])).mp
    (hsquare.trans hc.symm)

/-- The first-order spatial root obtained from the oriented cube and the C19
second moment.  The signed axis permutation is an orientation convention; it
does not change the square. -/
def nativeC19Px (momentum : LatticeMomentum) : ℂ :=
  (c19ScaledMomentum momentum 0 : ℝ)

/-- The second continuum momentum component in the oriented C19 root. -/
def nativeC19Py (momentum : LatticeMomentum) : ℂ :=
  (c19ScaledMomentum momentum 1 : ℝ)

/-- The third continuum momentum component in the oriented C19 root. -/
def nativeC19Pz (momentum : LatticeMomentum) : ℂ :=
  (c19ScaledMomentum momentum 2 : ℝ)

/-- The momentum-weighted root of the quadratic C19 symbol built from oriented crossings. -/
def nativeC19OrientedSpatialRoot
    (momentum : LatticeMomentum) (amplitude : CubicalCell8) : CubicalCell8 :=
  cubicalNativeSpatial
    (nativeC19Px momentum)
    (nativeC19Py momentum)
    (nativeC19Pz momentum) amplitude

theorem native_c19_oriented_spatial_root_square
    (momentum : LatticeMomentum) (amplitude : CubicalCell8) :
    nativeC19OrientedSpatialRoot momentum
        (nativeC19OrientedSpatialRoot momentum amplitude) =
      fun corner =>
        (c19QuadraticSymbol momentum : ℂ) * amplitude corner := by
  have hcoefficient :
      (nativeC19Pz momentum) ^ 2 + (-nativeC19Py momentum) ^ 2 +
          (-nativeC19Px momentum) ^ 2 =
        (c19QuadraticSymbol momentum : ℂ) := by
    simp only [nativeC19Px, nativeC19Py, nativeC19Pz, even_two, Even.neg_pow,
      c19_quadratic_symbol_eq_scaled_momentum, Complex.ofReal_add, Complex.ofReal_pow]
    ring
  unfold nativeC19OrientedSpatialRoot cubicalNativeSpatial
  rw [cubical_incidence_linear_square]
  funext corner
  rw [hcoefficient]

/-! ## The massive root and the native action Hessian -/

/-- Add the native vacuum curvature through cube parity.  Both terms are
defined on the eight-dimensional oriented incidence fiber. -/
def nativeC19OrientedMassiveRoot
    (r : ℝ) (momentum : LatticeMomentum)
    (amplitude : CubicalCell8) : CubicalCell8 :=
  cubicalNativeHamiltonian (r : ℂ) (nativeC19Px momentum) (nativeC19Py momentum)
    (nativeC19Pz momentum) amplitude

theorem native_c19_oriented_massive_root_square
    (r : ℝ) (momentum : LatticeMomentum) (amplitude : CubicalCell8) :
    nativeC19OrientedMassiveRoot r momentum
        (nativeC19OrientedMassiveRoot r momentum amplitude) =
      fun corner =>
        ((r ^ 2 + c19QuadraticSymbol momentum : ℝ) : ℂ) *
          amplitude corner := by
  simp only [nativeC19OrientedMassiveRoot, cubical_native_hamiltonian_square, nativeC19Px,
    nativeC19Py, nativeC19Pz, c19_quadratic_symbol_eq_scaled_momentum, Complex.ofReal_add,
    Complex.ofReal_pow, add_assoc]
  rfl

/-- The scalar multiplying the square of the oriented incidence root is the
same scalar obtained by the action-derived continuum acceleration. -/
theorem native_c19_root_matches_action_continuum_hessian
    (r : ℝ) (momentum : LatticeMomentum)
    (position : UniformCell2) (component : Fin 2) :
    uniformVacuumContinuumAcceleration r momentum position component =
      -((r ^ 2 + c19QuadraticSymbol momentum : ℝ) : ℂ) *
        position component := by
  rfl

/-- Relative to the exact finite-C19 action Hessian, the oriented local root
misses exactly the already-proved fourth-order spatial remainder. -/
theorem native_c19_root_square_is_exact_hessian_minus_remainder
    (r : ℝ) (momentum : LatticeMomentum) (amplitude : CubicalCell8) :
    nativeC19OrientedMassiveRoot r momentum
        (nativeC19OrientedMassiveRoot r momentum amplitude) =
      fun corner =>
        ((uniformVacuumModalSquare r momentum -
            c19SpatialRemainder momentum : ℝ) : ℂ) *
          amplitude corner := by
  have hcoefficient :
      r ^ 2 + c19QuadraticSymbol momentum =
        uniformVacuumModalSquare r momentum -
          c19SpatialRemainder momentum := by
    unfold uniformVacuumModalSquare
    rw [c19_symbol_exact_quadratic_plus_remainder]
    ring
  rw [native_c19_oriented_massive_root_square]
  funext corner
  rw [hcoefficient]

/-! ## Four-component coordinates are downstream -/

/-- The negative flavor fiber is merely a coordinate chart on the derived
eight-corner root. -/
theorem native_c19_root_intertwines_negative_flavor
    (r : ℝ) (momentum : LatticeMomentum) (z : CubicalCell4) :
    nativeC19OrientedMassiveRoot r momentum
        (cubicalDiracEmbedMinus z) =
      cubicalDiracEmbedMinus
        (cubicalStandardHamiltonian (r : ℂ)
          (nativeC19Px momentum)
          (nativeC19Py momentum)
          (nativeC19Pz momentum) z) := by
  exact cubical_hamiltonian_intertwines_minus _ _ _ _ _

/-- The commuting positive flavor fiber supplies the second coordinate chart
of the same geometry-derived root. -/
theorem native_c19_root_intertwines_positive_flavor
    (r : ℝ) (momentum : LatticeMomentum) (z : CubicalCell4) :
    nativeC19OrientedMassiveRoot r momentum
        (cubicalDiracEmbedPlus z) =
      cubicalDiracEmbedPlus
        (cubicalStandardHamiltonian (r : ℂ)
          (nativeC19Px momentum)
          (nativeC19Py momentum)
          (nativeC19Pz momentum) z) := by
  exact cubical_hamiltonian_intertwines_plus _ _ _ _ _

/-- Compact proof boundary for the non-matrix construction. -/
structure NativeC19CliffordRootCertificate : Prop where
  cellIncidenceDecomposition : ∀ axis amplitude,
    (fun corner =>
      cubicalCoboundaryAxis axis amplitude corner +
        cubicalBoundaryAxis axis amplitude corner) =
      cubicalGamma axis amplitude
  exteriorDifferentialNilpotent : ∀ amplitude,
    cubicalExteriorDerivative (cubicalExteriorDerivative amplitude) =
      fun _ => 0
  exteriorCoderivativeNilpotent : ∀ amplitude,
    cubicalExteriorCoderivative (cubicalExteriorCoderivative amplitude) =
      fun _ => 0
  kahlerDiracFromCellIncidence : ∀ amplitude,
    cubicalKahlerDirac amplitude =
      cubicalIncidenceLinear 1 1 1 amplitude
  weightedRootFromCellIncidence : ∀ k0 k1 k2 amplitude,
    cubicalWeightedCellIncidence k0 k1 k2 amplitude =
      cubicalIncidenceLinear k0 k1 k2 amplitude
  kahlerDiracSquare : ∀ amplitude,
    cubicalKahlerDirac (cubicalKahlerDirac amplitude) =
      fun corner => 3 * amplitude corner
  parityFromCellDegree : ∀ amplitude,
    cubicalBeta amplitude = fun corner =>
      (if (cubicalAxisBit 0 corner + cubicalAxisBit 1 corner +
          cubicalAxisBit 2 corner) % 2 = 0 then 1 else -1) *
        amplitude corner
  recursiveSigns : ∀ axis,
    RecursiveKoszulSignLaw axis (cubicalIncidenceSign axis)
  recursiveSignsUnique : ∀ axis sign,
    RecursiveKoszulSignLaw axis sign →
      sign = cubicalIncidenceSign axis
  incidenceCharacterized : ∀ axis,
    IsOrientedCubicalIncidence axis (cubicalGamma axis)
  incidenceUnique : ∀ axis operator,
    IsOrientedCubicalIncidence axis operator → operator = cubicalGamma axis
  gradingCharacterized : IsCubicalDegreeGrading cubicalBeta
  gradingUnique : ∀ operator,
    IsCubicalDegreeGrading operator → operator = cubicalBeta
  scaleFromC19 : ∀ scale,
    0 ≤ scale → scale ^ 2 = (c19SecondMoment 0 0 : ℝ) →
      scale = c19ContinuumSpeed
  spatialSquare : ∀ momentum amplitude,
    nativeC19OrientedSpatialRoot momentum
        (nativeC19OrientedSpatialRoot momentum amplitude) =
      fun corner =>
        (c19QuadraticSymbol momentum : ℂ) * amplitude corner
  massiveSquare : ∀ r momentum amplitude,
    nativeC19OrientedMassiveRoot r momentum
        (nativeC19OrientedMassiveRoot r momentum amplitude) =
      fun corner =>
        ((r ^ 2 + c19QuadraticSymbol momentum : ℝ) : ℂ) *
          amplitude corner
  exactC19Remainder : ∀ r momentum amplitude,
    nativeC19OrientedMassiveRoot r momentum
        (nativeC19OrientedMassiveRoot r momentum amplitude) =
      fun corner =>
        ((uniformVacuumModalSquare r momentum -
            c19SpatialRemainder momentum : ℝ) : ℂ) * amplitude corner

theorem native_c19_clifford_root : NativeC19CliffordRootCertificate where
  cellIncidenceDecomposition := cubical_boundary_coboundary_axis_eq_gamma
  exteriorDifferentialNilpotent := cubical_exterior_derivative_square_zero
  exteriorCoderivativeNilpotent :=
    cubical_exterior_coderivative_square_zero
  kahlerDiracFromCellIncidence := cubical_kahler_dirac_eq_incidence_linear
  weightedRootFromCellIncidence :=
    cubical_weighted_cell_incidence_eq_incidence_linear
  kahlerDiracSquare := cubical_kahler_dirac_square
  parityFromCellDegree := cubical_beta_is_exterior_degree_parity
  recursiveSigns := cubical_incidence_sign_obeys_recursive_koszul
  recursiveSignsUnique := recursive_koszul_sign_unique
  incidenceCharacterized := cubical_gamma_is_oriented_incidence
  incidenceUnique := oriented_cubical_incidence_unique
  gradingCharacterized := cubical_beta_is_degree_grading
  gradingUnique := cubical_degree_grading_unique
  scaleFromC19 := c19_incidence_scale_unique
  spatialSquare := native_c19_oriented_spatial_root_square
  massiveSquare := native_c19_oriented_massive_root_square
  exactC19Remainder :=
    native_c19_root_square_is_exact_hessian_minus_remainder

end
end LeanDirac.V2
