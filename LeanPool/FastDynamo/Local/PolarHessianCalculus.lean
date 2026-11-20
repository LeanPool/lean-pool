/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.PonomarenkoCartesianExteriorDerivative

/-!
# Elementary polar Hessian calculus on the punctured plane

This file isolates the two geometric second-derivative estimates needed for the exterior
`H2` argument.  All derivatives are taken along the physical Cartesian coordinate lines.
Thus the statements avoid an abstract choice of Hessian while still identifying exactly the
ordered Cartesian partials used elsewhere in the project.

For `r(y) = ‖y‖` and `q(y) = (y₁ + i y₂) / ‖y‖`, the coordinate Hessians are

`r_jk = delta_jk / r - y_j y_k / r^3`

and

`q_jk = -e_j y_k / r^3 - e_k y_j / r^3 - z delta_jk / r^3
          + 3 z y_j y_k / r^5`,

where `z = y₁ + i y₂` and `e_0 = 1`, `e_1 = i`.  The resulting coarse bounds are
`|r_jk| <= 2/r` and `|q_jk| <= 6/r^2`.  A final generic lemma packages the Hessian of a
one-dimensional radial profile and its corresponding pointwise estimate.
-/

@[expose] public section

noncomputable section

namespace FastDynamo
namespace PolarHessianCalculus

open Complex Filter
open scoped RealInnerProductSpace
open CartesianRadialRegularity
open ComplexRadius
open PonomarenkoCartesianExteriorDerivative

/-! ## Coordinate lines and elementary coefficients -/

/-- The continuous linear parametrization of a physical coordinate direction. -/
def coordinateLineCLM (k : Fin 2) : ℝ →L[ℝ] WholePlane :=
  ContinuousLinearMap.toSpanSingleton ℝ (wholePlaneBasis k)

/-- The physical line through `y` in coordinate direction `k`. -/
def coordinateLine (y : WholePlane) (k : Fin 2) (t : ℝ) : WholePlane :=
  coordinateLineCLM k t + y

/-- The coordinate-direction parametrization sends the scalar `t` to `t` times the `k`-th
standard basis vector of the plane. -/
@[simp] theorem coordinateLineCLM_apply (k : Fin 2) (t : ℝ) :
    coordinateLineCLM k t = t • wholePlaneBasis k := by
  simp [coordinateLineCLM]

/-- The two-dimensional Kronecker delta, regarded as a real scalar. -/
def coordinateDelta (j k : Fin 2) : ℝ :=
  if j = k then 1 else 0

/-- The complex coordinate derivative: `e_0 = 1` and `e_1 = i`. -/
def complexCoordinateBasis (j : Fin 2) : ℂ :=
  if j = 0 then 1 else I

/-- The coordinate line through `y` passes through `y` at parameter `0`. -/
@[simp] theorem coordinateLine_zero (y : WholePlane) (k : Fin 2) :
    coordinateLine y k 0 = y := by
  simp [coordinateLine]

/-- The coordinate line `t ↦ t eₖ + y` has constant derivative `eₖ`, so differentiating along it
computes the `k`-th Cartesian partial derivative. -/
theorem coordinateLine_hasDerivAt (y : WholePlane) (k : Fin 2) (t : ℝ) :
    HasDerivAt (coordinateLine y k) (wholePlaneBasis k) t := by
  have h := (coordinateLineCLM k).hasDerivAt (x := t)
  have h' := h.add_const y
  convert! h' using 1
  simp [coordinateLineCLM_apply]

/-- The complex coordinate derivatives `e₀ = 1` and `e₁ = i` are unimodular. -/
@[simp] theorem norm_complexCoordinateBasis (j : Fin 2) :
    ‖complexCoordinateBasis j‖ = 1 := by
  by_cases hj : j = 0 <;> simp [complexCoordinateBasis, hj]

/-- The `j`-th Cartesian component along the `k`-th coordinate line has derivative the Kronecker
delta `δⱼₖ` at the base point. -/
theorem coordinateLine_apply_hasDerivAt
    (y : WholePlane) (j k : Fin 2) :
    HasDerivAt (fun t : ℝ ↦ coordinateLine y k t j)
      (coordinateDelta j k) 0 := by
  have h := ((hasDerivAt_id (x := (0 : ℝ))).mul_const
    (wholePlaneBasis k j)).add_const (y j)
  convert! h using 1
  simp [coordinateDelta, wholePlaneBasis]

/-- Complex-valued form of `coordinateLine_apply_hasDerivAt`: the derivative is the Kronecker
delta viewed in `ℂ`. -/
theorem complex_coordinateLine_apply_hasDerivAt
    (y : WholePlane) (j k : Fin 2) :
    HasDerivAt (fun t : ℝ ↦ (coordinateLine y k t j : ℂ))
      (coordinateDelta j k : ℂ) 0 := by
  have h := (coordinateLine_apply_hasDerivAt y j k).smul_const (1 : ℂ)
  convert! h using 1 <;> simp [Complex.real_smul]

/-- Differentiating the complex coordinate `z = y₀ + i y₁` along the `k`-th coordinate line gives
`e_k`, i.e. `1` for `k = 0` and `i` for `k = 1`. -/
theorem complexCoordinate_coordinateLine_hasDerivAt
    (y : WholePlane) (k : Fin 2) :
    HasDerivAt (fun t : ℝ ↦ complexCoordinate (coordinateLine y k t))
      (complexCoordinateBasis k) 0 := by
  have h0 := complex_coordinateLine_apply_hasDerivAt y (0 : Fin 2) k
  have h1 := complex_coordinateLine_apply_hasDerivAt y (1 : Fin 2) k
  have h := h0.add (h1.const_mul I)
  convert! h using 1
  fin_cases k <;> simp [coordinateDelta, complexCoordinateBasis]

/-! ## The radius Hessian -/

/-- The ordered Cartesian second partial of the Euclidean radius. -/
def radiusSecondPartial (y : WholePlane) (j k : Fin 2) : ℝ :=
  coordinateDelta j k / ‖y‖ - y j * y k / ‖y‖ ^ 3

/-- The first radius derivative along a physical coordinate line. -/
theorem radius_coordinateLine_hasDerivAt
    {y : WholePlane} (hy : y ≠ 0) (k : Fin 2) :
    HasDerivAt (fun t : ℝ ↦ ‖coordinateLine y k t‖)
      (radiusDerivative y (wholePlaneBasis k)) 0 := by
  have h := (radius_hasFDerivAt hy).comp_hasDerivAt_of_eq
    0 (coordinateLine_hasDerivAt y k 0) (coordinateLine_zero y k).symm
  convert! h using 1

/-- Differentiating the `j`-th radius partial along the `k`-th coordinate line gives the
explicit radius Hessian entry. -/
theorem radiusPartial_coordinateLine_hasDerivAt
    {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2) :
    HasDerivAt
      (fun t : ℝ ↦ radiusDerivative (coordinateLine y k t) (wholePlaneBasis j))
      (radiusSecondPartial y j k) 0 := by
  have hcoord := coordinateLine_apply_hasDerivAt y j k
  have hr := radius_coordinateLine_hasDerivAt hy k
  have hquot := hcoord.div hr (by simpa using norm_ne_zero_iff.mpr hy)
  simp only [coordinateLine_zero] at hquot
  have hderiv :
      (coordinateDelta j k * ‖y‖ -
          y j * radiusDerivative y (wholePlaneBasis k)) / ‖y‖ ^ 2 =
        radiusSecondPartial y j k := by
    rw [radiusDerivative_apply, inner_wholePlaneBasis]
    unfold radiusSecondPartial
    field_simp [norm_ne_zero_iff.mpr hy]
  convert! hquot.congr_deriv hderiv using 1
  funext t
  simp [radiusDerivative_apply, inner_wholePlaneBasis]

/-- A coordinate component is bounded by the Euclidean norm. -/
theorem norm_coordinate_apply_le (y : WholePlane) (j : Fin 2) :
    ‖y j‖ ≤ ‖y‖ :=
  PiLp.norm_apply_le y j

/-- Every first coordinate derivative of the radius has norm at most one. -/
theorem norm_radiusDerivative_basis_le_one
    {y : WholePlane} (hy : y ≠ 0) (j : Fin 2) :
    ‖radiusDerivative y (wholePlaneBasis j)‖ ≤ 1 := by
  rw [radiusDerivative_apply, inner_wholePlaneBasis, Real.norm_eq_abs,
    abs_div, abs_of_nonneg (norm_nonneg y)]
  exact (div_le_one (norm_pos_iff.mpr hy)).mpr
    (by simpa [Real.norm_eq_abs] using norm_coordinate_apply_le y j)

/-- The radius Hessian has the coarse coordinate bound `2/r`. -/
theorem norm_radiusSecondPartial_le
    {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2) :
    ‖radiusSecondPartial y j k‖ ≤ 2 / ‖y‖ := by
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hj : ‖y j‖ ≤ ‖y‖ := norm_coordinate_apply_le y j
  have hk : ‖y k‖ ≤ ‖y‖ := norm_coordinate_apply_le y k
  have hdelta : ‖coordinateDelta j k‖ ≤ 1 := by
    by_cases h : j = k <;> simp [coordinateDelta, h]
  have hfirst : ‖coordinateDelta j k / ‖y‖‖ ≤ 1 / ‖y‖ := by
    rw [norm_div, norm_norm]
    exact div_le_div_of_nonneg_right hdelta (le_of_lt hr)
  have hsecond : ‖y j * y k / ‖y‖ ^ 3‖ ≤ 1 / ‖y‖ := by
    rw [norm_div, norm_mul, norm_pow, norm_norm]
    calc
      ‖y j‖ * ‖y k‖ / ‖y‖ ^ 3 ≤ ‖y‖ * ‖y‖ / ‖y‖ ^ 3 := by
        gcongr
      _ = 1 / ‖y‖ := by field_simp [ne_of_gt hr]
  unfold radiusSecondPartial
  calc
    ‖coordinateDelta j k / ‖y‖ - y j * y k / ‖y‖ ^ 3‖ ≤
        ‖coordinateDelta j k / ‖y‖‖ + ‖y j * y k / ‖y‖ ^ 3‖ :=
      norm_sub_le _ _
    _ ≤ 1 / ‖y‖ + 1 / ‖y‖ := add_le_add hfirst hsecond
    _ = 2 / ‖y‖ := by ring

/-! ## The circular phase Hessian -/

/-- The explicit ordered Cartesian second partial of the circular phase. -/
def exteriorPhaseSecondPartial (y : WholePlane) (j k : Fin 2) : ℂ :=
  -(complexCoordinateBasis j * (y k : ℂ) / complexRadius y ^ 3) -
    complexCoordinateBasis k * (y j : ℂ) / complexRadius y ^ 3 -
    complexCoordinate y * (coordinateDelta j k : ℂ) / complexRadius y ^ 3 +
    3 * complexCoordinate y * (y j : ℂ) * (y k : ℂ) / complexRadius y ^ 5

/-- The complex radius along a coordinate line has derivative `y_k/r`. -/
theorem complexRadius_coordinateLine_hasDerivAt
    {y : WholePlane} (hy : y ≠ 0) (k : Fin 2) :
    HasDerivAt (fun t : ℝ ↦ complexRadius (coordinateLine y k t))
      (((y k / ‖y‖ : ℝ) : ℂ)) 0 := by
  have h := (radius_coordinateLine_hasDerivAt hy k).smul_const (1 : ℂ)
  convert! h using 1 <;>
    simp [complexRadius, Complex.real_smul, radiusDerivative_apply,
      inner_wholePlaneBasis]

/-- The first circular-phase derivative along a physical coordinate line. -/
theorem exteriorPhase_coordinateLine_hasDerivAt
    {y : WholePlane} (hy : y ≠ 0) (k : Fin 2) :
    HasDerivAt (fun t : ℝ ↦ exteriorPhase (coordinateLine y k t))
      (exteriorPhaseDerivative y (wholePlaneBasis k)) 0 := by
  have hz := complexCoordinate_coordinateLine_hasDerivAt y k
  have hr := complexRadius_coordinateLine_hasDerivAt hy k
  have hr0 : complexRadius (coordinateLine y k 0) ≠ 0 := by
    rw [coordinateLine_zero, complexRadius]
    exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  have h := hz.div hr hr0
  have hr0y : complexRadius y ≠ 0 := by
    rw [complexRadius]
    exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  have hvalue :
      (complexCoordinateBasis k * complexRadius y -
          complexCoordinate y * (((y k / ‖y‖ : ℝ) : ℂ))) /
            complexRadius y ^ 2 =
        exteriorPhaseDerivative y (wholePlaneBasis k) := by
    rw [exteriorPhaseDerivative_basis]
    unfold complexCoordinateBasis complexRadius
    rw [Complex.ofReal_div]
    field_simp [ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)]
  simp only [coordinateLine_zero] at h
  convert! h.congr_deriv hvalue using 1

/-- Differentiating the `j`-th circular-phase partial along coordinate `k` gives the explicit
phase Hessian entry. -/
theorem exteriorPhasePartial_coordinateLine_hasDerivAt
    {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2) :
    HasDerivAt
      (fun t : ℝ ↦
        exteriorPhaseDerivative (coordinateLine y k t) (wholePlaneBasis j))
      (exteriorPhaseSecondPartial y j k) 0 := by
  have hr := complexRadius_coordinateLine_hasDerivAt hy k
  have hr0 : complexRadius y ≠ 0 :=
    ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  have hz := complexCoordinate_coordinateLine_hasDerivAt y k
  have hj := complex_coordinateLine_apply_hasDerivAt y j k
  have hfirst :=
    (hasDerivAt_const (x := (0 : ℝ)) (complexCoordinateBasis j)).div hr
      (by simpa using hr0)
  have hnum := hz.mul hj
  have hsecond := hnum.div (hr.pow 3) (by simpa using pow_ne_zero 3 hr0)
  have h := hfirst.sub hsecond
  have hfun :
      (fun t : ℝ ↦
          exteriorPhaseDerivative (coordinateLine y k t) (wholePlaneBasis j)) =
        (fun t : ℝ ↦
          complexCoordinateBasis j / complexRadius (coordinateLine y k t) -
            (complexCoordinate (coordinateLine y k t) *
              (coordinateLine y k t j : ℂ)) /
                complexRadius (coordinateLine y k t) ^ 3) := by
    funext t
    rw [exteriorPhaseDerivative_basis]
    simp only [complexCoordinateBasis]
    ring
  rw [hfun]
  apply h.congr_deriv
  unfold exteriorPhaseSecondPartial
  simp only [coordinateLine_zero, Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat,
    pow_succ, pow_zero]
  rw [Complex.ofReal_div]
  unfold complexRadius
  field_simp [hr0]
  ring

/-- A real coordinate, coerced to `ℂ`, is bounded by the physical radius. -/
theorem norm_complex_coordinate_apply_le (y : WholePlane) (j : Fin 2) :
    ‖(y j : ℂ)‖ ≤ ‖y‖ := by
  simpa [Complex.norm_real, Real.norm_eq_abs] using norm_coordinate_apply_le y j

/-- The circular phase Hessian has the coarse coordinate bound `6/r^2`. -/
theorem norm_exteriorPhaseSecondPartial_le
    {y : WholePlane} (hy : y ≠ 0) (j k : Fin 2) :
    ‖exteriorPhaseSecondPartial y j k‖ ≤ 6 / ‖y‖ ^ 2 := by
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hj : ‖(y j : ℂ)‖ ≤ ‖y‖ := norm_complex_coordinate_apply_le y j
  have hk : ‖(y k : ℂ)‖ ≤ ‖y‖ := norm_complex_coordinate_apply_le y k
  have hz : ‖complexCoordinate y‖ = ‖y‖ := norm_complexCoordinate y
  have hdelta : ‖(coordinateDelta j k : ℂ)‖ ≤ 1 := by
    by_cases h : j = k <;> simp [coordinateDelta, h]
  have hpow (n : ℕ) : ‖complexRadius y ^ n‖ = ‖y‖ ^ n := by
    rw [norm_pow, norm_complexRadius]
  have h1 :
      ‖complexCoordinateBasis j * (y k : ℂ) / complexRadius y ^ 3‖ ≤
        1 / ‖y‖ ^ 2 := by
    rw [norm_div, norm_mul, norm_complexCoordinateBasis, one_mul, hpow]
    calc
      ‖(y k : ℂ)‖ / ‖y‖ ^ 3 ≤ ‖y‖ / ‖y‖ ^ 3 := by gcongr
      _ = 1 / ‖y‖ ^ 2 := by field_simp [ne_of_gt hr]
  have h2 :
      ‖complexCoordinateBasis k * (y j : ℂ) / complexRadius y ^ 3‖ ≤
        1 / ‖y‖ ^ 2 := by
    rw [norm_div, norm_mul, norm_complexCoordinateBasis, one_mul, hpow]
    calc
      ‖(y j : ℂ)‖ / ‖y‖ ^ 3 ≤ ‖y‖ / ‖y‖ ^ 3 := by gcongr
      _ = 1 / ‖y‖ ^ 2 := by field_simp [ne_of_gt hr]
  have h3 :
      ‖complexCoordinate y * (coordinateDelta j k : ℂ) /
          complexRadius y ^ 3‖ ≤ 1 / ‖y‖ ^ 2 := by
    rw [norm_div, norm_mul, hz, hpow]
    calc
      ‖y‖ * ‖(coordinateDelta j k : ℂ)‖ / ‖y‖ ^ 3 ≤
          ‖y‖ * 1 / ‖y‖ ^ 3 := by gcongr
      _ = 1 / ‖y‖ ^ 2 := by field_simp [ne_of_gt hr]
  have h4 :
      ‖3 * complexCoordinate y * (y j : ℂ) * (y k : ℂ) /
          complexRadius y ^ 5‖ ≤ 3 / ‖y‖ ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, hz, hpow]
    calc
      ‖(3 : ℂ)‖ * ‖y‖ * ‖(y j : ℂ)‖ * ‖(y k : ℂ)‖ / ‖y‖ ^ 5 ≤
          ‖(3 : ℂ)‖ * ‖y‖ * ‖y‖ * ‖y‖ / ‖y‖ ^ 5 := by gcongr
      _ = 3 / ‖y‖ ^ 2 := by
        rw [show ‖(3 : ℂ)‖ = 3 by norm_num]
        field_simp [ne_of_gt hr]
  unfold exteriorPhaseSecondPartial
  calc
    ‖-(complexCoordinateBasis j * (y k : ℂ) / complexRadius y ^ 3) -
        complexCoordinateBasis k * (y j : ℂ) / complexRadius y ^ 3 -
        complexCoordinate y * (coordinateDelta j k : ℂ) / complexRadius y ^ 3 +
        3 * complexCoordinate y * (y j : ℂ) * (y k : ℂ) /
          complexRadius y ^ 5‖ ≤
        ‖complexCoordinateBasis j * (y k : ℂ) / complexRadius y ^ 3‖ +
          ‖complexCoordinateBasis k * (y j : ℂ) / complexRadius y ^ 3‖ +
          ‖complexCoordinate y * (coordinateDelta j k : ℂ) /
            complexRadius y ^ 3‖ +
          ‖3 * complexCoordinate y * (y j : ℂ) * (y k : ℂ) /
            complexRadius y ^ 5‖ := by
      calc
        _ ≤ ‖-(complexCoordinateBasis j * (y k : ℂ) / complexRadius y ^ 3) -
              complexCoordinateBasis k * (y j : ℂ) / complexRadius y ^ 3 -
              complexCoordinate y * (coordinateDelta j k : ℂ) /
                complexRadius y ^ 3‖ +
              ‖3 * complexCoordinate y * (y j : ℂ) * (y k : ℂ) /
                complexRadius y ^ 5‖ := norm_add_le _ _
        _ ≤ (‖complexCoordinateBasis j * (y k : ℂ) / complexRadius y ^ 3‖ +
              ‖complexCoordinateBasis k * (y j : ℂ) / complexRadius y ^ 3‖ +
              ‖complexCoordinate y * (coordinateDelta j k : ℂ) /
                complexRadius y ^ 3‖) +
              ‖3 * complexCoordinate y * (y j : ℂ) * (y k : ℂ) /
                complexRadius y ^ 5‖ := by
          gcongr
          calc
            _ ≤ ‖-(complexCoordinateBasis j * (y k : ℂ) /
                    complexRadius y ^ 3) -
                    complexCoordinateBasis k * (y j : ℂ) /
                      complexRadius y ^ 3‖ +
                  ‖complexCoordinate y * (coordinateDelta j k : ℂ) /
                    complexRadius y ^ 3‖ := norm_sub_le _ _
            _ ≤ (‖complexCoordinateBasis j * (y k : ℂ) /
                    complexRadius y ^ 3‖ +
                  ‖complexCoordinateBasis k * (y j : ℂ) /
                    complexRadius y ^ 3‖) +
                  ‖complexCoordinate y * (coordinateDelta j k : ℂ) /
                    complexRadius y ^ 3‖ := by
              gcongr
              simpa only [norm_neg] using
                norm_sub_le
                  (-(complexCoordinateBasis j * (y k : ℂ) /
                    complexRadius y ^ 3))
                  (complexCoordinateBasis k * (y j : ℂ) /
                    complexRadius y ^ 3)
        _ = _ := by ring
    _ ≤ 1 / ‖y‖ ^ 2 + 1 / ‖y‖ ^ 2 + 1 / ‖y‖ ^ 2 + 3 / ‖y‖ ^ 2 := by
      gcongr
    _ = 6 / ‖y‖ ^ 2 := by ring

/-! ## Trace and orthogonality identities -/

/-- The squared coordinate norm in the two physical directions. -/
theorem coordinate_sq_sum_eq_norm_sq (y : WholePlane) :
    y (0 : Fin 2) ^ 2 + y (1 : Fin 2) ^ 2 = ‖y‖ ^ 2 := by
  simpa [squaredRadius] using (squaredRadius_eq_coordinate_squares y).symm

/-- The Euclidean radius has Laplacian `1/r` on the punctured plane. -/
theorem radiusSecondPartial_trace
    {y : WholePlane} (hy : y ≠ 0) :
    radiusSecondPartial y (0 : Fin 2) 0 +
        radiusSecondPartial y (1 : Fin 2) 1 = 1 / ‖y‖ := by
  have hr0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hsq := coordinate_sq_sum_eq_norm_sq y
  unfold radiusSecondPartial coordinateDelta
  simp only [ite_true]
  field_simp [hr0]
  nlinarith

/-- The squared (complex-bilinear) length of the radius gradient is one. -/
theorem radiusDerivative_sq_sum_eq_one
    {y : WholePlane} (hy : y ≠ 0) :
    radiusDerivative y (wholePlaneBasis (0 : Fin 2)) ^ 2 +
        radiusDerivative y (wholePlaneBasis (1 : Fin 2)) ^ 2 = 1 := by
  have hr0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hsq := coordinate_sq_sum_eq_norm_sq y
  simp only [radiusDerivative_apply, inner_wholePlaneBasis]
  field_simp [hr0]
  nlinarith

/-- The radius and circular-phase gradients are orthogonal in the complex-bilinear Cartesian
contraction. -/
theorem radiusDerivative_mul_phaseDerivative_sum_eq_zero
    {y : WholePlane} (hy : y ≠ 0) :
    (radiusDerivative y (wholePlaneBasis (0 : Fin 2)) : ℂ) *
          exteriorPhaseDerivative y (wholePlaneBasis (0 : Fin 2)) +
        (radiusDerivative y (wholePlaneBasis (1 : Fin 2)) : ℂ) *
          exteriorPhaseDerivative y (wholePlaneBasis (1 : Fin 2)) = 0 := by
  have hr0 : complexRadius y ≠ 0 := by
    rw [complexRadius]
    exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  have hsqR := coordinate_sq_sum_eq_norm_sq y
  have hsqC :
      (y (0 : Fin 2) : ℂ) ^ 2 + (y (1 : Fin 2) : ℂ) ^ 2 =
        ((‖y‖ : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast hsqR
  rw [radiusDerivative_apply, radiusDerivative_apply,
    inner_wholePlaneBasis, inner_wholePlaneBasis,
    exteriorPhaseDerivative_basis, exteriorPhaseDerivative_basis]
  simp only [ite_eq_left, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]
  rw [Complex.ofReal_div, Complex.ofReal_div]
  unfold complexCoordinate complexRadius at hr0 ⊢
  field_simp [hr0]
  linear_combination
    -((y (0 : Fin 2) : ℂ) + I * (y (1 : Fin 2) : ℂ)) * hsqC

/-- The complex-bilinear square of the circular-phase gradient is `-q^2/r^2`. -/
theorem phaseDerivative_sq_sum_eq
    {y : WholePlane} (hy : y ≠ 0) :
    exteriorPhaseDerivative y (wholePlaneBasis (0 : Fin 2)) ^ 2 +
        exteriorPhaseDerivative y (wholePlaneBasis (1 : Fin 2)) ^ 2 =
      -(exteriorPhase y ^ 2) / (complexRadius y ^ 2) := by
  have hr0 : complexRadius y ≠ 0 := by
    rw [complexRadius]
    exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  have hsqR := coordinate_sq_sum_eq_norm_sq y
  have hsqC :
      (y (0 : Fin 2) : ℂ) ^ 2 + (y (1 : Fin 2) : ℂ) ^ 2 =
        ((‖y‖ : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast hsqR
  rw [exteriorPhaseDerivative_basis, exteriorPhaseDerivative_basis]
  simp only [ite_eq_left, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]
  unfold complexRadius at hr0
  unfold exteriorPhase complexCoordinate complexRadius
  field_simp [hr0]
  linear_combination
    (((y (0 : Fin 2) : ℂ) + I * (y (1 : Fin 2) : ℂ)) ^ 2) * hsqC +
      (((‖y‖ : ℝ) : ℂ) ^ 4) * Complex.I_sq

/-- The circular phase is an angular frequency-one harmonic: `Delta q = -q/r^2`. -/
theorem exteriorPhaseSecondPartial_trace
    {y : WholePlane} (hy : y ≠ 0) :
    exteriorPhaseSecondPartial y (0 : Fin 2) 0 +
        exteriorPhaseSecondPartial y (1 : Fin 2) 1 =
      -exteriorPhase y / (complexRadius y ^ 2) := by
  have hr0 : complexRadius y ≠ 0 := by
    rw [complexRadius]
    exact ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  have hsqR := coordinate_sq_sum_eq_norm_sq y
  have hsqC :
      (y (0 : Fin 2) : ℂ) ^ 2 + (y (1 : Fin 2) : ℂ) ^ 2 =
        ((‖y‖ : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast hsqR
  unfold exteriorPhaseSecondPartial exteriorPhase complexCoordinateBasis coordinateDelta
  simp only [ite_eq_left, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]
  unfold complexCoordinate complexRadius at hr0 ⊢
  field_simp [hr0]
  norm_num
  linear_combination
    (3 * ((y (0 : Fin 2) : ℂ) + I * (y (1 : Fin 2) : ℂ))) * hsqC

/-! ## Generic radial compositions -/

/-- The ordered second partial value of a radial profile with prescribed first and second
radial derivatives. -/
def radialCompositionSecondPartialValue
    (b' b'' : ℂ) (y : WholePlane) (j k : Fin 2) : ℂ :=
  (radiusDerivative y (wholePlaneBasis j) *
      radiusDerivative y (wholePlaneBasis k)) • b'' +
    radiusSecondPartial y j k • b'

/-- Taking the two-dimensional trace recovers the classical radial Laplacian
`b''(r) + b'(r)/r`. -/
theorem radialCompositionSecondPartialValue_trace
    {y : WholePlane} (hy : y ≠ 0) (b' b'' : ℂ) :
    radialCompositionSecondPartialValue b' b'' y (0 : Fin 2) 0 +
        radialCompositionSecondPartialValue b' b'' y (1 : Fin 2) 1 =
      b'' + (1 / ‖y‖) • b' := by
  calc
    _ = (radiusDerivative y (wholePlaneBasis (0 : Fin 2)) ^ 2 +
            radiusDerivative y (wholePlaneBasis (1 : Fin 2)) ^ 2) • b'' +
          (radiusSecondPartial y (0 : Fin 2) 0 +
            radiusSecondPartial y (1 : Fin 2) 1) • b' := by
      simp only [radialCompositionSecondPartialValue, pow_two]
      module
    _ = b'' + (1 / ‖y‖) • b' := by
      rw [radiusDerivative_sq_sum_eq_one hy, radiusSecondPartial_trace hy]
      simp

/-! ## Circular radial product traces -/

/-- The algebraic second partial of the square of the circular phase. -/
def exteriorPhaseSquareSecondPartial (y : WholePlane) (j k : Fin 2) : ℂ :=
  2 * exteriorPhaseDerivative y (wholePlaneBasis j) *
      exteriorPhaseDerivative y (wholePlaneBasis k) +
    2 * exteriorPhase y * exteriorPhaseSecondPartial y j k

/-- The angular frequency-two phase has Laplacian `-4 q^2/r^2`. -/
theorem exteriorPhaseSquareSecondPartial_trace
    {y : WholePlane} (hy : y ≠ 0) :
    exteriorPhaseSquareSecondPartial y (0 : Fin 2) 0 +
        exteriorPhaseSquareSecondPartial y (1 : Fin 2) 1 =
      -(4 * exteriorPhase y ^ 2) / complexRadius y ^ 2 := by
  calc
    _ = 2 * (exteriorPhaseDerivative y (wholePlaneBasis (0 : Fin 2)) ^ 2 +
            exteriorPhaseDerivative y (wholePlaneBasis (1 : Fin 2)) ^ 2) +
          2 * exteriorPhase y *
            (exteriorPhaseSecondPartial y (0 : Fin 2) 0 +
              exteriorPhaseSecondPartial y (1 : Fin 2) 1) := by
      unfold exteriorPhaseSquareSecondPartial
      ring
    _ = -(4 * exteriorPhase y ^ 2) / complexRadius y ^ 2 := by
      rw [phaseDerivative_sq_sum_eq hy, exteriorPhaseSecondPartial_trace hy]
      ring

/-- The algebraic second partial of `q^2 * b(r)` from the polar product rule. -/
def phaseSquareRadialProductSecondPartialValue
    (b b' b'' : ℂ) (y : WholePlane) (j k : Fin 2) : ℂ :=
  exteriorPhaseSquareSecondPartial y j k * b +
    (2 * exteriorPhase y *
        exteriorPhaseDerivative y (wholePlaneBasis j)) *
      ((radiusDerivative y (wholePlaneBasis k) : ℂ) * b') +
    (2 * exteriorPhase y *
        exteriorPhaseDerivative y (wholePlaneBasis k)) *
      ((radiusDerivative y (wholePlaneBasis j) : ℂ) * b') +
    exteriorPhase y ^ 2 * radialCompositionSecondPartialValue b' b'' y j k

/-- The polar Laplacian identity for an angular frequency-two radial product. -/
theorem phaseSquareRadialProductSecondPartialValue_trace
    {y : WholePlane} (hy : y ≠ 0) (b b' b'' : ℂ) :
    phaseSquareRadialProductSecondPartialValue b b' b'' y (0 : Fin 2) 0 +
        phaseSquareRadialProductSecondPartialValue b b' b'' y (1 : Fin 2) 1 =
      exteriorPhase y ^ 2 * (b'' + (1 / ‖y‖) • b') -
        (4 * exteriorPhase y ^ 2 / complexRadius y ^ 2) * b := by
  calc
    _ = (exteriorPhaseSquareSecondPartial y (0 : Fin 2) 0 +
            exteriorPhaseSquareSecondPartial y (1 : Fin 2) 1) * b +
          4 * exteriorPhase y *
            ((radiusDerivative y (wholePlaneBasis (0 : Fin 2)) : ℂ) *
                exteriorPhaseDerivative y (wholePlaneBasis (0 : Fin 2)) +
              (radiusDerivative y (wholePlaneBasis (1 : Fin 2)) : ℂ) *
                exteriorPhaseDerivative y (wholePlaneBasis (1 : Fin 2))) * b' +
          exteriorPhase y ^ 2 *
            (radialCompositionSecondPartialValue b' b'' y (0 : Fin 2) 0 +
              radialCompositionSecondPartialValue b' b'' y (1 : Fin 2) 1) := by
      unfold phaseSquareRadialProductSecondPartialValue
      ring
    _ = exteriorPhase y ^ 2 * (b'' + (1 / ‖y‖) • b') -
          (4 * exteriorPhase y ^ 2 / complexRadius y ^ 2) * b := by
      rw [exteriorPhaseSquareSecondPartial_trace hy,
        radiusDerivative_mul_phaseDerivative_sum_eq_zero hy,
        radialCompositionSecondPartialValue_trace hy]
      ring

/-- Restricting a radial profile to a coordinate line gives the expected first Cartesian
partial. -/
theorem radialComposition_coordinateLine_hasDerivAt
    {b : ℝ → ℂ} {b' : ℂ} {y : WholePlane} (hy : y ≠ 0)
    (hb : HasDerivAt b b' ‖y‖) (k : Fin 2) :
    HasDerivAt (fun t : ℝ ↦ b ‖coordinateLine y k t‖)
      (radiusDerivative y (wholePlaneBasis k) • b') 0 := by
  have h := hb.scomp_of_eq 0 (radius_coordinateLine_hasDerivAt hy k) (by simp)
  convert! h using 1

/-- Differentiating the `j`-th radial-composition partial along coordinate `k` gives the
standard Hessian formula `r_j r_k b'' + r_jk b'`. -/
theorem radialCompositionPartial_coordinateLine_hasDerivAt
    {b : ℝ → ℂ} {b'' : ℂ} {y : WholePlane} (hy : y ≠ 0)
    (hb'' : HasDerivAt (deriv b) b'' ‖y‖) (j k : Fin 2) :
    HasDerivAt
      (fun t : ℝ ↦
        radiusDerivative (coordinateLine y k t) (wholePlaneBasis j) •
          deriv b ‖coordinateLine y k t‖)
      (radialCompositionSecondPartialValue (deriv b ‖y‖) b'' y j k) 0 := by
  have hrj := radiusPartial_coordinateLine_hasDerivAt hy j k
  have hbline := hb''.scomp_of_eq 0 (radius_coordinateLine_hasDerivAt hy k) (by simp)
  have h := hrj.smul hbline
  convert! h using 1
  simp [Function.comp_apply, coordinateLine_zero, radialCompositionSecondPartialValue]
  ring

/-- The Hessian entry of a radial composition is bounded by
`|b''| + (2/r)|b'|`. -/
theorem norm_radialCompositionSecondPartialValue_le
    {y : WholePlane} (hy : y ≠ 0) (b' b'' : ℂ) (j k : Fin 2) :
    ‖radialCompositionSecondPartialValue b' b'' y j k‖ ≤
      ‖b''‖ + (2 / ‖y‖) * ‖b'‖ := by
  have hj := norm_radiusDerivative_basis_le_one hy j
  have hk := norm_radiusDerivative_basis_le_one hy k
  have hsecond := norm_radiusSecondPartial_le hy j k
  unfold radialCompositionSecondPartialValue
  calc
    ‖(radiusDerivative y (wholePlaneBasis j) *
          radiusDerivative y (wholePlaneBasis k)) • b'' +
        radiusSecondPartial y j k • b'‖ ≤
        ‖(radiusDerivative y (wholePlaneBasis j) *
          radiusDerivative y (wholePlaneBasis k)) • b''‖ +
          ‖radiusSecondPartial y j k • b'‖ := norm_add_le _ _
    _ = ‖radiusDerivative y (wholePlaneBasis j)‖ *
          ‖radiusDerivative y (wholePlaneBasis k)‖ * ‖b''‖ +
        ‖radiusSecondPartial y j k‖ * ‖b'‖ := by
      simp
    _ ≤ 1 * 1 * ‖b''‖ + (2 / ‖y‖) * ‖b'‖ := by gcongr
    _ = ‖b''‖ + (2 / ‖y‖) * ‖b'‖ := by ring

end PolarHessianCalculus
end FastDynamo
