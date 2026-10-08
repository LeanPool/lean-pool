/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffinePairing
public import LeanPool.HighContrastHomogenization.Analytic.TestNorms
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# High-contrast homogenization: Analytic.AffineFractionalKernel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Kernel distortion under an invertible linear change of variables

The Gagliardo double integral of `e.physical.fractional.norm` measures
the increment of a field against the Euclidean distance between its two
arguments.  An invertible linear map distorts that distance by a factor lying
between the extreme singular values of the map, and rescales the outer
normalized average and the inner integral by the determinant.

This module records the ingredients the fractional comparison needs: the
unnormalized Lebesgue integral over a linear image, the two singular-value
bounds written through the `ℓ²` operator norm, and the pointwise comparison of
the Gagliardo kernels before and after the change of variables.

The singular-value datum is carried abstractly, as a constant `N` satisfying
`|w| ≤ N |L w|` for every `w`; the operator norm of `L⁻¹` is always such a
constant, and a sharper one may be substituted wherever it is known.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Unnormalized integrals over a linear image -/

/-- The Lebesgue integral of a nonnegative function over an invertible linear
image carries the determinant Jacobian. -/
theorem setLIntegral_matImage {L : Mat d} (hL : IsUnit L.det) {U : Set (Vec d)}
    (hU : MeasurableSet U) (f : Vec d → ℝ≥0∞) :
    (∫⁻ x in matImage L U, f x ∂volume) =
      ENNReal.ofReal |L.det| * ∫⁻ y in U, f (matVecMul L y) ∂volume := by
  let T : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
  have hderiv : ∀ x ∈ U, HasFDerivWithinAt (matVecMul L) T U x := by
    intro x _hx
    exact (T.hasFDerivAt.congr_of_eventuallyEq (by
      filter_upwards with z
      rfl)).hasFDerivWithinAt
  have hinj : Set.InjOn (matVecMul L) U :=
    (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det L).mpr hL)).injOn
  have hTdet : T.det = L.det := by
    dsimp [T]
    rw [← Matrix.toLin'_apply']
    exact LinearMap.det_toLin' L
  have hchange :=
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU hderiv hinj f
  change (∫⁻ x in matVecMul L '' U, f x ∂volume) = _
  rw [hchange]
  simp_rw [hTdet]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ## Singular-value bounds through the `ℓ²` operator norm -/

/-- The Euclidean length of a vector, squared, is the ambient squared length of
its `ℓ²` avatar. -/
private theorem norm_toLp_sq (y : Vec d) :
    ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))‖ ^ 2 = vecNormSq y := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vecNormSq, vecDot, Real.norm_eq_abs, sq_abs]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The `ℓ²` operator norm controls the squared length of a matrix-vector
product. -/
theorem vecNormSq_matVecMul_le (M : Mat d) (x : Vec d) :
    vecNormSq (matVecMul M x) ≤ ‖M‖ ^ 2 * vecNormSq x := by
  have hT : Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M (WithLp.toLp 2 x)
      = WithLp.toLp 2 (matVecMul M x) := rfl
  have hle : ‖(WithLp.toLp 2 (matVecMul M x) : EuclideanSpace ℝ (Fin d))‖ ≤
      ‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
    rw [← hT]
    exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M).le_opNorm _
  have hsq : ‖(WithLp.toLp 2 (matVecMul M x) : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤
      (‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖(WithLp.toLp 2 (matVecMul M x) : EuclideanSpace ℝ (Fin d))‖ :=
      norm_nonneg _
    calc ‖(WithLp.toLp 2 (matVecMul M x) : EuclideanSpace ℝ (Fin d))‖ ^ 2
        = ‖(WithLp.toLp 2 (matVecMul M x) : EuclideanSpace ℝ (Fin d))‖ *
            ‖(WithLp.toLp 2 (matVecMul M x) : EuclideanSpace ℝ (Fin d))‖ := sq _
      _ ≤ (‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖) *
            (‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖) :=
          mul_self_le_mul_self h0 hle
      _ = (‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖) ^ 2 := (sq _).symm
  rwa [norm_toLp_sq, mul_pow, norm_toLp_sq] at hsq

/-- **The largest singular value bound.**  The Euclidean length of `M x` is at
most the `ℓ²` operator norm of `M` times the Euclidean length of `x`. -/
theorem sqrt_vecNormSq_matVecMul_le (M : Mat d) (x : Vec d) :
    Real.sqrt (vecNormSq (matVecMul M x)) ≤ ‖M‖ * Real.sqrt (vecNormSq x) := by
  have h : Real.sqrt (vecNormSq (matVecMul M x)) ≤
      Real.sqrt (‖M‖ ^ 2 * vecNormSq x) :=
    Real.sqrt_le_sqrt (vecNormSq_matVecMul_le M x)
  rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg M)] at h

/-- **The smallest singular value bound.**  For an invertible `L` the Euclidean
length of `x` is at most the `ℓ²` operator norm of `L⁻¹` times the Euclidean
length of `L x`. -/
theorem sqrt_vecNormSq_le_norm_inv_mul {L : Mat d} (hL : IsUnit L.det) (x : Vec d) :
    Real.sqrt (vecNormSq x) ≤ ‖L⁻¹‖ * Real.sqrt (vecNormSq (matVecMul L x)) := by
  have h := sqrt_vecNormSq_matVecMul_le L⁻¹ (matVecMul L x)
  rwa [matVecMul_mul, Matrix.nonsing_inv_mul L hL, matVecMul_one] at h

/-! ## Elementary matrix-vector identities -/

/-- A matrix acts linearly on differences. -/
theorem matVecMul_sub_vec (M : Mat d) (x y : Vec d) :
    matVecMul M x - matVecMul M y = matVecMul M (x - y) := by
  funext i
  simp only [Pi.sub_apply, matVecMul, mul_sub, Finset.sum_sub_distrib]

/-- A matrix sends the origin to the origin. -/
theorem matVecMul_zero_vec (M : Mat d) : matVecMul M (0 : Vec d) = 0 := by
  funext i
  simp [matVecMul]

/-- A linear map cannot separate a point from itself: a vanishing Euclidean
length is preserved. -/
theorem sqrt_vecNormSq_matVecMul_eq_zero {M : Mat d} {w : Vec d}
    (h : Real.sqrt (vecNormSq w) = 0) :
    Real.sqrt (vecNormSq (matVecMul M w)) = 0 := by
  have h1 : vecNormSq w ≤ 0 := Real.sqrt_eq_zero'.mp h
  have hw : w = 0 := vecNormSq_eq_zero_iff.mp (le_antisymm h1 (vecNormSq_nonneg w))
  rw [hw, matVecMul_zero_vec, vecNormSq_eq_zero_iff.mpr rfl, Real.sqrt_zero]

/-! ## The pointwise kernel comparison -/

/-- The abstract-real form of the kernel comparison: if `A ≤ N * B` and `A`
vanishes only together with `B`, then a nonnegative numerator over `B ^ p` is at
most `N ^ p` times the same numerator over `A ^ p`. -/
private theorem div_rpow_le_mul_div_rpow {A B N p a : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 ≤ N) (hp : 0 ≤ p) (ha : 0 ≤ a)
    (hAB : A ≤ N * B) (hzero : A = 0 → B = 0) :
    a / B ^ p ≤ N ^ p * (a / A ^ p) := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hB0 : B = 0 := hzero hA0.symm
    rcases eq_or_lt_of_le hp with hp0 | hppos
    · have h1 : A ^ p = 1 := by rw [← hp0, Real.rpow_zero]
      have h2 : B ^ p = 1 := by rw [← hp0, Real.rpow_zero]
      have h3 : N ^ p = 1 := by rw [← hp0, Real.rpow_zero]
      refine le_of_eq ?_
      calc a / B ^ p = a := by rw [h2, div_one]
        _ = N ^ p * (a / A ^ p) := by rw [h1, h3, div_one, one_mul]
    · have h0 : (0 : ℝ) ^ p = 0 := Real.zero_rpow (ne_of_gt hppos)
      calc a / B ^ p = 0 := by rw [hB0, h0, div_zero]
        _ ≤ N ^ p * (a / A ^ p) :=
            le_of_eq (by rw [← hA0, h0, div_zero, mul_zero])
  · have hNB : 0 < N * B := lt_of_lt_of_le hApos hAB
    have hBpos : 0 < B := by
      rcases eq_or_lt_of_le hB with hB0 | hBpos
      · exact absurd hNB (by rw [← hB0, mul_zero]; exact lt_irrefl 0)
      · exact hBpos
    have hNpos : 0 < N := by
      rcases eq_or_lt_of_le hN with hN0 | hNpos
      · exact absurd hNB (by rw [← hN0, zero_mul]; exact lt_irrefl 0)
      · exact hNpos
    have hkey : A ^ p ≤ N ^ p * B ^ p := by
      rw [← Real.mul_rpow hN hB]
      exact Real.rpow_le_rpow hA hAB hp
    have hAp : 0 < A ^ p := Real.rpow_pos_of_pos hApos p
    have hBp : 0 < B ^ p := Real.rpow_pos_of_pos hBpos p
    have hNp : 0 < N ^ p := Real.rpow_pos_of_pos hNpos p
    set α : ℝ := A ^ p
    set β : ℝ := N ^ p
    set γ : ℝ := B ^ p
    clear_value α β γ
    have hquot : α / β ≤ γ := (div_le_iff₀ hNp).mpr (by rw [mul_comm]; exact hkey)
    have hstep : a / γ ≤ a / (α / β) :=
      div_le_div_of_nonneg_left ha (div_pos hAp hNp) hquot
    have hval : a / (α / β) = β * (a / α) := by
      field_simp
    rwa [hval] at hstep

/-- **The Gagliardo kernel comparison.**  With `|w| ≤ N |L w|` the kernel written
in the image variables is at most `N ^ p` times the kernel written in the source
variables, for every nonnegative numerator. -/
theorem gagliardo_kernel_matVecMul_le {L : Mat d} {N p : ℝ} (hN : 0 ≤ N)
    (hp : 0 ≤ p)
    (hker : ∀ w : Vec d,
      Real.sqrt (vecNormSq w) ≤ N * Real.sqrt (vecNormSq (matVecMul L w)))
    {a : ℝ} (ha : 0 ≤ a) (w : Vec d) :
    a / Real.sqrt (vecNormSq (matVecMul L w)) ^ p ≤
      N ^ p * (a / Real.sqrt (vecNormSq w) ^ p) :=
  div_rpow_le_mul_div_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hN hp ha
    (hker w) (fun h => sqrt_vecNormSq_matVecMul_eq_zero h)

end

end HighContrast
end HCPolySupport
