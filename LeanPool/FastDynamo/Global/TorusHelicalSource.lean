/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusCellPlacement
public import LeanPool.FastDynamo.Local.ParameterizedHelicalProfile

/-!
# Euclidean helical sources for the placed torus cells

This file constructs the actual translated and rescaled whole-plane helical
velocity used in one Euclidean placement chart.  All statements here are
source-side statements on `ℝ × ℝ`: support, reality, classical first
derivatives, transverse divergence, and the paper's value/gradient
scaling.  Descending this source through the quotient chart and identifying
its classical derivatives with torus weak derivatives is done in
`Global/TorusChartWeakTransfer.lean` and `Global/TorusChartFourierWeakTransfer.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Metric Set
open scoped LineDeriv SchwartzMap RealInnerProductSpace

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}

/-- The canonical real-linear identification of pair coordinates with the
two-dimensional whole plane. -/
def pairToWholePlane : (ℝ × ℝ) →L[ℝ] WholePlane :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin 2 ↦
      ![ContinuousLinearMap.fst ℝ ℝ ℝ,
        ContinuousLinearMap.snd ℝ ℝ ℝ] j)

/-- The zeroth whole-plane coordinate of `pairToWholePlane x` is the first component of the
pair. -/
@[simp] theorem pairToWholePlane_apply_zero (x : ℝ × ℝ) :
    pairToWholePlane x (0 : Fin 2) = x.1 :=
  rfl

/-- The first whole-plane coordinate of `pairToWholePlane x` is the second component of the
pair. -/
@[simp] theorem pairToWholePlane_apply_one (x : ℝ × ℝ) :
    pairToWholePlane x (1 : Fin 2) = x.2 :=
  rfl

/-- The pair-coordinate vector corresponding to a whole-plane basis vector. -/
def pairBasis (j : Fin 2) : ℝ × ℝ :=
  ![(1, 0), (0, 1)] j

/-- The identification carries the pair basis to the whole-plane basis:
`pairToWholePlane (pairBasis j) = wholePlaneBasis j`. -/
@[simp] theorem pairToWholePlane_pairBasis (j : Fin 2) :
    pairToWholePlane (pairBasis j) = wholePlaneBasis j := by
  fin_cases j <;> ext i <;> fin_cases i <;>
    simp [pairBasis, wholePlaneBasis]

/-- Whole-plane coordinates centered at cell `n` and dilated by `ell n`. -/
def helicalCellCoordinate
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (n : ℕ) : (ℝ × ℝ) → WholePlane :=
  (P.scaleFamily.ell n)⁻¹ • fun x ↦
    pairToWholePlane x - pairToWholePlane (P.scaleFamily.cellCenter n)

/-- The paper's Euclidean local source
`ell_n v((x - p_n) / ell_n)` in the `n`th placed cell. -/
def parameterizedHelicalCellSource
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) : (ℝ × ℝ) → C3 :=
  P.scaleFamily.ell n •
    (⇑(parameterizedSmoothedVelocity h angularSpeed axialSpeed) ∘
      helicalCellCoordinate h P n)

/-- The actual coordinate first derivative of the rescaled source.  The
amplitude factor `ell_n` cancels the inverse scale from the argument. -/
def parameterizedHelicalCellSourceDeriv
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (j : Fin 2)
    (x : ℝ × ℝ) : C3 :=
  (∂_{wholePlaneBasis j}
    (parameterizedSmoothedVelocity h angularSpeed axialSpeed))
      (helicalCellCoordinate h P n x)

/-! ## Geometry and support -/

/-- The Euclidean norm of the canonical whole-plane image dominates the
product (sup) metric used for the placement chart. -/
theorem dist_le_norm_pairToWholePlane_sub (x y : ℝ × ℝ) :
    dist x y ≤ ‖pairToWholePlane x - pairToWholePlane y‖ := by
  rw [Prod.dist_eq]
  apply max_le
  · simpa [Real.dist_eq] using
      (PiLp.norm_apply_le (pairToWholePlane x - pairToWholePlane y)
        (0 : Fin 2))
  · simpa [Real.dist_eq] using
      (PiLp.norm_apply_le (pairToWholePlane x - pairToWholePlane y)
        (1 : Fin 2))

/-- Outside the local core disc of cell `n` the rescaled coordinate `(x - p_n)/ell_n` has norm at
least the profile's support radius `1 + h`; this is the geometric step behind the support
statement for the placed helical cell. -/
theorem supportRadius_le_norm_helicalCellCoordinate_of_not_mem
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (n : ℕ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n) :
    1 + (h : ℝ) ≤ ‖helicalCellCoordinate h P n x‖ := by
  have hell : 0 < P.scaleFamily.ell n := P.scaleFamily.ell_pos n
  have hout : (1 + (h : ℝ)) * P.scaleFamily.ell n ≤
      dist x (P.scaleFamily.cellCenter n) := by
    simpa [ScaleFamily.localCoreDisk] using hx
  have hnorm : (1 + (h : ℝ)) * P.scaleFamily.ell n ≤
      ‖pairToWholePlane x -
        pairToWholePlane (P.scaleFamily.cellCenter n)‖ :=
    hout.trans (dist_le_norm_pairToWholePlane_sub _ _)
  simp only [helicalCellCoordinate, Pi.smul_apply]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hell)]
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hell).2 hnorm

/-- The rescaled local source is supported in the local core disc selected
by the placement certificate. -/
theorem parameterizedHelicalCellSource_eq_zero_of_not_mem_localCoreDisk
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n) :
    parameterizedHelicalCellSource h P angularSpeed axialSpeed n x = 0 := by
  simp only [parameterizedHelicalCellSource, Pi.smul_apply,
    Function.comp_apply]
  rw [
    parameterizedSmoothedVelocity_eq_zero_of_radius_le_norm h angularSpeed
      axialSpeed
      (supportRadius_le_norm_helicalCellCoordinate_of_not_mem h P n hx),
    smul_zero]

/-! ## Pointwise reality and transverse divergence -/

/-- The smoothed helical profile is pointwise real: every component of its value has vanishing
imaginary part, since the radial profile is real. -/
theorem parameterizedSmoothedVelocity_pointwiseReal
    (h : PonomarenkoSmoothingWidth) (angularSpeed axialSpeed : ℝ)
    (y : WholePlane) (i : Fin 3) :
    (parameterizedSmoothedVelocity h angularSpeed axialSpeed y i).im = 0 := by
  change (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
    angularSpeed axialSpeed y i).im = 0
  fin_cases i
  · change (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
      angularSpeed axialSpeed y 0).im = 0
    rw [squaredRadiusHelicalVelocity_apply_zero]
    simp [Complex.mul_im, parameterizedRadialProfile_value_real h y]
  · change (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
      angularSpeed axialSpeed y 1).im = 0
    rw [squaredRadiusHelicalVelocity_apply_one]
    simp [Complex.mul_im, parameterizedRadialProfile_value_real h y]
  · change (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
      angularSpeed axialSpeed y 2).im = 0
    rw [squaredRadiusHelicalVelocity_apply_two]
    simp [Complex.mul_im, parameterizedRadialProfile_value_real h y]

/-- Every directional derivative of the smoothed helical profile is pointwise real, since both the
radial profile and its slope are real. -/
theorem parameterizedSmoothedVelocity_lineDeriv_pointwiseReal
    (h : PonomarenkoSmoothingWidth) (angularSpeed axialSpeed : ℝ)
    (j : Fin 2) (y : WholePlane) (i : Fin 3) :
    ((∂_{wholePlaneBasis j}
      (parameterizedSmoothedVelocity h angularSpeed axialSpeed)) y i).im = 0 := by
  change ((∂_{wholePlaneBasis j}
    (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
      angularSpeed axialSpeed)) y i).im = 0
  fin_cases i
  · change ((∂_{wholePlaneBasis j}
      (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
        angularSpeed axialSpeed)) y 0).im = 0
    rw [lineDeriv_squaredRadiusHelicalVelocity_apply_zero]
    simp [Complex.mul_im, parameterizedRadialProfile_value_real h y,
      parameterizedRadialProfile_slope_real h y]
  · change ((∂_{wholePlaneBasis j}
      (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
        angularSpeed axialSpeed)) y 1).im = 0
    rw [lineDeriv_squaredRadiusHelicalVelocity_apply_one]
    simp [Complex.mul_im, parameterizedRadialProfile_value_real h y,
      parameterizedRadialProfile_slope_real h y]
  · change ((∂_{wholePlaneBasis j}
      (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
        angularSpeed axialSpeed)) y 2).im = 0
    rw [lineDeriv_squaredRadiusHelicalVelocity_apply_two]
    simp [Complex.mul_im, parameterizedRadialProfile_slope_real h y]

/-- The rescaled cell source is real in every component, pointwise. -/
theorem parameterizedHelicalCellSource_pointwiseReal
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (x : ℝ × ℝ) (i : Fin 3) :
    (parameterizedHelicalCellSource h P angularSpeed axialSpeed n x i).im = 0 := by
  simp [parameterizedHelicalCellSource,
    parameterizedSmoothedVelocity_pointwiseReal]

/-- The coordinate derivatives are real in every component, pointwise. -/
theorem parameterizedHelicalCellSourceDeriv_pointwiseReal
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (j : Fin 2)
    (x : ℝ × ℝ) (i : Fin 3) :
    (parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j x i).im = 0 := by
  exact parameterizedSmoothedVelocity_lineDeriv_pointwiseReal
    h angularSpeed axialSpeed j (helicalCellCoordinate h P n x) i

/-- The two transverse coordinate derivatives have exactly zero divergence
before any quotient-chart transfer. -/
theorem parameterizedHelicalCellSourceDeriv_transverseDivergence
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (x : ℝ × ℝ) :
    parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n 0 x 0 +
      parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n 1 x 1 = 0 := by
  exact squaredRadiusHelicalVelocity_transverseDivergence
    (parameterizedRadialProfile h) angularSpeed axialSpeed
      (helicalCellCoordinate h P n x)

/-- The first derivatives have the same local-core support as the source;
this uses the compact support of both the radial value and its slope. -/
theorem parameterizedHelicalCellSourceDeriv_eq_zero_of_not_mem_localCoreDisk
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (j : Fin 2) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n) :
    parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j x = 0 := by
  let y := helicalCellCoordinate h P n x
  have hy : 1 + (h : ℝ) ≤ ‖y‖ :=
    supportRadius_le_norm_helicalCellCoordinate_of_not_mem h P n hx
  apply PiLp.ext
  intro i
  change ((∂_{wholePlaneBasis j}
    (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
      angularSpeed axialSpeed)) y i) = 0
  fin_cases i
  · change ((∂_{wholePlaneBasis j}
      (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
        angularSpeed axialSpeed)) y 0) = 0
    rw [lineDeriv_squaredRadiusHelicalVelocity_apply_zero]
    simp [parameterizedRadialProfile_value_zero h hy,
      parameterizedRadialProfile_slope_zero h hy]
  · change ((∂_{wholePlaneBasis j}
      (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
        angularSpeed axialSpeed)) y 1) = 0
    rw [lineDeriv_squaredRadiusHelicalVelocity_apply_one]
    simp [parameterizedRadialProfile_value_zero h hy,
      parameterizedRadialProfile_slope_zero h hy]
  · change ((∂_{wholePlaneBasis j}
      (squaredRadiusHelicalVelocity (parameterizedRadialProfile h)
        angularSpeed axialSpeed)) y 2) = 0
    rw [lineDeriv_squaredRadiusHelicalVelocity_apply_two]
    simp [parameterizedRadialProfile_slope_zero h hy]

/-! ## Classical differentiation in the Euclidean chart -/

/-- The derivative of the affine cell-coordinate map. -/
def helicalCellCoordinateFDeriv {h : ℝ}
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (n : ℕ) : (ℝ × ℝ) →L[ℝ] WholePlane :=
  (P.scaleFamily.ell n)⁻¹ • pairToWholePlane

/-- The affine cell coordinate `x ↦ (x - p_n)/ell_n` is differentiable with the constant Fréchet
derivative `ell_n⁻¹ • pairToWholePlane`. -/
theorem helicalCellCoordinate_hasFDerivAt
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (n : ℕ) (x : ℝ × ℝ) :
    HasFDerivAt (helicalCellCoordinate h P n)
      (helicalCellCoordinateFDeriv P n) x := by
  simpa [helicalCellCoordinate, helicalCellCoordinateFDeriv,
    Pi.smul_apply] using
    ((pairToWholePlane.hasFDerivAt.sub_const
      (pairToWholePlane (P.scaleFamily.cellCenter n))).const_smul
        (P.scaleFamily.ell n)⁻¹)

/-- The full classical Fréchet derivative of the rescaled source in pair
coordinates. -/
def parameterizedHelicalCellSourceFDeriv
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (x : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] C3 :=
  P.scaleFamily.ell n •
    ((fderiv ℝ (parameterizedSmoothedVelocity h angularSpeed axialSpeed)
      (helicalCellCoordinate h P n x)).comp
        (helicalCellCoordinateFDeriv P n))

/-- The rescaled cell source `ell_n v((x - p_n)/ell_n)` is Fréchet differentiable, with derivative
the chain-rule composition `ell_n • (Dv ∘ (ell_n⁻¹ • pairToWholePlane))`
(`eq:local-copy`). -/
theorem parameterizedHelicalCellSource_hasFDerivAt
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (x : ℝ × ℝ) :
    HasFDerivAt (parameterizedHelicalCellSource h P angularSpeed axialSpeed n)
      (parameterizedHelicalCellSourceFDeriv h P angularSpeed axialSpeed n x) x := by
  have hcomp :=
    (parameterizedSmoothedVelocity h angularSpeed axialSpeed).hasFDerivAt
      (helicalCellCoordinate h P n x) |>.comp x
        (helicalCellCoordinate_hasFDerivAt h P n x)
  simpa [parameterizedHelicalCellSource,
    parameterizedHelicalCellSourceFDeriv, Pi.smul_apply,
    Function.comp_apply] using
      hcomp.const_smul (P.scaleFamily.ell n)

/-- The formula named `parameterizedHelicalCellSourceDeriv` is the
coordinate derivative of the rescaled source. -/
theorem parameterizedHelicalCellSourceFDeriv_apply_pairBasis
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (x : ℝ × ℝ) (j : Fin 2) :
    parameterizedHelicalCellSourceFDeriv h P angularSpeed axialSpeed n x
        (pairBasis j) =
      parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j x := by
  have hell : P.scaleFamily.ell n ≠ 0 := (P.scaleFamily.ell_pos n).ne'
  simp [parameterizedHelicalCellSourceFDeriv,
    helicalCellCoordinateFDeriv, pairToWholePlane_pairBasis,
    parameterizedHelicalCellSourceDeriv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, hell]

/-! ## Uniform source-side scale estimates -/

/-- A concrete global value bound for the unscaled Schwartz profile. -/
def parameterizedHelicalValueBound
    (h : PonomarenkoSmoothingWidth) (angularSpeed axialSpeed : ℝ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0
    (parameterizedSmoothedVelocity h angularSpeed axialSpeed)

/-- A concrete uniform bound for both coordinate derivatives of the
unscaled profile.  A sum is used so no comparison of the two seminorms is
needed. -/
def parameterizedHelicalFirstDerivativeBound
    (h : PonomarenkoSmoothingWidth) (angularSpeed axialSpeed : ℝ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0
      (∂_{wholePlaneBasis (0 : Fin 2)}
        (parameterizedSmoothedVelocity h angularSpeed axialSpeed)) +
    SchwartzMap.seminorm ℝ 0 0
      (∂_{wholePlaneBasis (1 : Fin 2)}
        (parameterizedSmoothedVelocity h angularSpeed axialSpeed))

/-- The profile value bound, being a Schwartz seminorm, is nonnegative. -/
theorem parameterizedHelicalValueBound_nonneg
    (h : PonomarenkoSmoothingWidth) (angularSpeed axialSpeed : ℝ) :
    0 ≤ parameterizedHelicalValueBound h angularSpeed axialSpeed :=
  apply_nonneg _ _

/-- The profile first-derivative bound, a sum of two Schwartz seminorms, is nonnegative. -/
theorem parameterizedHelicalFirstDerivativeBound_nonneg
    (h : PonomarenkoSmoothingWidth) (angularSpeed axialSpeed : ℝ) :
    0 ≤ parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed := by
  unfold parameterizedHelicalFirstDerivativeBound
  positivity

/-- The local source has the exact amplitude scaling `ell_n`. -/
theorem norm_parameterizedHelicalCellSource_eq
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (x : ℝ × ℝ) :
    ‖parameterizedHelicalCellSource h P angularSpeed axialSpeed n x‖ =
      P.scaleFamily.ell n *
        ‖parameterizedSmoothedVelocity h angularSpeed axialSpeed
          (helicalCellCoordinate h P n x)‖ := by
  simp [parameterizedHelicalCellSource, Pi.smul_apply,
    Function.comp_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (P.scaleFamily.ell_pos n)]

/-- The paper's value estimate: the source is `O(ell_n)` with a
constant depending only on the fixed profile parameters. -/
theorem norm_parameterizedHelicalCellSource_le
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (x : ℝ × ℝ) :
    ‖parameterizedHelicalCellSource h P angularSpeed axialSpeed n x‖ ≤
      parameterizedHelicalValueBound h angularSpeed axialSpeed *
        P.scaleFamily.ell n := by
  rw [norm_parameterizedHelicalCellSource_eq]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right
    (SchwartzMap.norm_le_seminorm ℝ
      (parameterizedSmoothedVelocity h angularSpeed axialSpeed)
      (helicalCellCoordinate h P n x))
    (P.scaleFamily.ell_pos n).le

/-- Each first coordinate derivative is bounded independently of `ell_n`,
expressing the exact cancellation between amplitude and spatial dilation. -/
theorem norm_parameterizedHelicalCellSourceDeriv_le
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (j : Fin 2) (x : ℝ × ℝ) :
    ‖parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j x‖ ≤
      parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed := by
  calc
    ‖parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j x‖ ≤
        SchwartzMap.seminorm ℝ 0 0
          (∂_{wholePlaneBasis j}
            (parameterizedSmoothedVelocity h angularSpeed axialSpeed)) :=
      SchwartzMap.norm_le_seminorm ℝ
        (∂_{wholePlaneBasis j}
          (parameterizedSmoothedVelocity h angularSpeed axialSpeed))
        (helicalCellCoordinate h P n x)
    _ ≤ parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed := by
      fin_cases j
      · change SchwartzMap.seminorm ℝ 0 0
            (∂_{wholePlaneBasis (0 : Fin 2)}
              (parameterizedSmoothedVelocity h angularSpeed axialSpeed)) ≤ _
        exact le_add_of_nonneg_right (apply_nonneg _ _)
      · change SchwartzMap.seminorm ℝ 0 0
            (∂_{wholePlaneBasis (1 : Fin 2)}
              (parameterizedSmoothedVelocity h angularSpeed axialSpeed)) ≤ _
        exact le_add_of_nonneg_left (apply_nonneg _ _)

/-! ## Support as set inclusions -/

/-- The rescaled cell source is supported in the cell's local core disc of radius
`(1 + h) ell_n`. -/
theorem support_parameterizedHelicalCellSource_subset_localCoreDisk
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) :
    Function.support
        (parameterizedHelicalCellSource h P angularSpeed axialSpeed n) ⊆
      P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n := by
  intro x hx
  by_contra hcore
  exact hx
    (parameterizedHelicalCellSource_eq_zero_of_not_mem_localCoreDisk
      h P angularSpeed axialSpeed n hcore)

/-- Each displayed derivative of the rescaled cell source is supported in the cell's local core
disc. -/
theorem support_parameterizedHelicalCellSourceDeriv_subset_localCoreDisk
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) (j : Fin 2) :
    Function.support
        (parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j) ⊆
      P.scaleFamily.localCoreDisk (1 + (h : ℝ)) n := by
  intro x hx
  by_contra hcore
  exact hx
    (parameterizedHelicalCellSourceDeriv_eq_zero_of_not_mem_localCoreDisk
      h P angularSpeed axialSpeed n j hcore)

/-! ## A Euclidean source certificate -/

/-- Source-side data sufficient for the quotient-chart transfer of
`Global/TorusChartWeakTransfer.lean`.  Every function here is defined on the Euclidean chart
and no torus weak-derivative statement is included. -/
structure EuclideanCellSourceCertificate
    {supportRadius : ℝ}
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) where
  /-- The Euclidean chart source. -/
  source : ℝ × ℝ → C3
  /-- Its two coordinate first derivatives. -/
  firstDerivative : Fin 2 → ℝ × ℝ → C3
  /-- Its full real Fréchet derivative. -/
  sourceFDeriv : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] C3)
  /-- The source is supported in the placed local core. -/
  source_support :
    Function.support source ⊆ P.scaleFamily.localCoreDisk supportRadius n
  /-- Both coordinate derivatives are supported in the same local core. -/
  firstDerivative_support : ∀ j,
    Function.support (firstDerivative j) ⊆
      P.scaleFamily.localCoreDisk supportRadius n
  /-- Every source component is pointwise real. -/
  source_pointwiseReal : ∀ x i, (source x i).im = 0
  /-- Every first-derivative component is pointwise real. -/
  firstDerivative_pointwiseReal : ∀ j x i,
    (firstDerivative j x i).im = 0
  /-- The displayed Fréchet derivative is a classical derivative. -/
  source_hasFDerivAt : ∀ x, HasFDerivAt source (sourceFDeriv x) x
  /-- Applying the full derivative to a pair basis vector recovers the
  corresponding coordinate derivative. -/
  sourceFDeriv_apply_pairBasis : ∀ x j,
    sourceFDeriv x (pairBasis j) = firstDerivative j x
  /-- Pointwise transverse divergence cancellation in Euclidean coordinates. -/
  transverseDivergence : ∀ x,
    firstDerivative 0 x 0 + firstDerivative 1 x 1 = 0
  /-- The uniform constant for values. -/
  valueBound : ℝ
  /-- The uniform constant for first derivatives. -/
  firstDerivativeBound : ℝ
  /-- The value bound is nonnegative. -/
  valueBound_nonneg : 0 ≤ valueBound
  /-- The derivative bound is nonnegative. -/
  firstDerivativeBound_nonneg : 0 ≤ firstDerivativeBound
  /-- The value amplitude has the cell scale `ell_n`. -/
  norm_source_le : ∀ x,
    ‖source x‖ ≤ valueBound * P.scaleFamily.ell n
  /-- First derivatives are uniformly bounded independently of `ell_n`. -/
  norm_firstDerivative_le : ∀ j x,
    ‖firstDerivative j x‖ ≤ firstDerivativeBound

/-- The parameterized smoothed helical profile supplies the complete
Euclidean source certificate for every placed cell. -/
def parameterizedHelicalCellSourceCertificate
    (h : PonomarenkoSmoothingWidth)
    (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
    (angularSpeed axialSpeed : ℝ) (n : ℕ) :
    EuclideanCellSourceCertificate P n where
  source := parameterizedHelicalCellSource h P angularSpeed axialSpeed n
  firstDerivative := fun j ↦
    parameterizedHelicalCellSourceDeriv h P angularSpeed axialSpeed n j
  sourceFDeriv :=
    parameterizedHelicalCellSourceFDeriv h P angularSpeed axialSpeed n
  source_support :=
    support_parameterizedHelicalCellSource_subset_localCoreDisk
      h P angularSpeed axialSpeed n
  firstDerivative_support := fun j ↦
    support_parameterizedHelicalCellSourceDeriv_subset_localCoreDisk
      h P angularSpeed axialSpeed n j
  source_pointwiseReal := fun x i ↦
    parameterizedHelicalCellSource_pointwiseReal
      h P angularSpeed axialSpeed n x i
  firstDerivative_pointwiseReal := fun j x i ↦
    parameterizedHelicalCellSourceDeriv_pointwiseReal
      h P angularSpeed axialSpeed n j x i
  source_hasFDerivAt := fun x ↦
    parameterizedHelicalCellSource_hasFDerivAt
      h P angularSpeed axialSpeed n x
  sourceFDeriv_apply_pairBasis := fun x j ↦
    parameterizedHelicalCellSourceFDeriv_apply_pairBasis
      h P angularSpeed axialSpeed n x j
  transverseDivergence := fun x ↦
    parameterizedHelicalCellSourceDeriv_transverseDivergence
      h P angularSpeed axialSpeed n x
  valueBound := parameterizedHelicalValueBound h angularSpeed axialSpeed
  firstDerivativeBound :=
    parameterizedHelicalFirstDerivativeBound h angularSpeed axialSpeed
  valueBound_nonneg :=
    parameterizedHelicalValueBound_nonneg h angularSpeed axialSpeed
  firstDerivativeBound_nonneg :=
    parameterizedHelicalFirstDerivativeBound_nonneg h angularSpeed axialSpeed
  norm_source_le := fun x ↦
    norm_parameterizedHelicalCellSource_le
      h P angularSpeed axialSpeed n x
  norm_firstDerivative_le := fun j x ↦
    norm_parameterizedHelicalCellSourceDeriv_le
      h P angularSpeed axialSpeed n j x

/-- The Euclidean norm of the canonical image of a pair difference is at
most twice its product-metric distance.  The factor two is intentionally
coarse; the placement margin is a factor ten. -/
theorem norm_pairToWholePlane_sub_le_two_mul_dist
    (x y : ℝ × ℝ) :
    ‖pairToWholePlane x - pairToWholePlane y‖ ≤ 2 * dist x y := by
  have hdecomp :
      pairToWholePlane x - pairToWholePlane y =
        (x.1 - y.1) • wholePlaneBasis 0 +
          (x.2 - y.2) • wholePlaneBasis 1 := by
    ext i
    fin_cases i <;> simp [wholePlaneBasis]
  rw [hdecomp]
  calc
    ‖(x.1 - y.1) • wholePlaneBasis 0 +
        (x.2 - y.2) • wholePlaneBasis 1‖ ≤
        ‖(x.1 - y.1) • wholePlaneBasis 0‖ +
          ‖(x.2 - y.2) • wholePlaneBasis 1‖ := norm_add_le _ _
    _ = |x.1 - y.1| + |x.2 - y.2| := by
      rw [norm_smul, norm_smul]
      simp [wholePlaneBasis, PiLp.norm_single, Real.norm_eq_abs]
    _ ≤ dist x y + dist x y := by
      apply add_le_add
      · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        exact le_max_left _ _
      · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        exact le_max_right _ _
    _ = 2 * dist x y := by ring

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
