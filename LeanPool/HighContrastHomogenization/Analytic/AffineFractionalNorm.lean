/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineFractionalKernel

/-!
# High-contrast homogenization: Analytic.AffineFractionalNorm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The normalized fractional norm under an invertible affine normalization

The fractional carriers of `e.physical.fractional.norm` are compared
across the change of variables `x = L y` for an invertible matrix `L`.  Two
mechanisms are separated:

* the **domain** transport, which sends the domain `V` to its linear image and
  the field to its pullback.  The volume-normalized `L²` term acquires exactly
  the determinant power `|det L| ^ (-2s/d)`, while the Gagliardo term acquires
  the determinant factor of the inner integral together with the distortion of
  the kernel, controlled by the extreme singular values of `L`;
* the **pointwise** action, which multiplies the values of the field by a fixed
  matrix.  This costs the squared `ℓ²` operator norm of that matrix and leaves
  the domain untouched.

Both comparisons are two-sided: the reverse inequality of the domain transport
is the forward inequality for `L⁻¹`, and its constant is written explicitly
through `|det L|⁻¹` and the operator norm of `L`.  Every constant depends only
on the dimension, on the fractional parameter, and on the transporting matrix.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Monotonicity of the normalized average -/

/-- The normalized nonnegative average is monotone. -/
theorem eVolumeAverage_mono (V : Set (Vec d)) {f g : Vec d → ℝ≥0∞}
    (h : ∀ x, f x ≤ g x) : eVolumeAverage V f ≤ eVolumeAverage V g :=
  ENNReal.div_le_div_right (lintegral_mono h) _

/-- A pointwise bound by a finite constant multiple passes to the normalized
average. -/
theorem eVolumeAverage_le_const_mul (V : Set (Vec d)) {a : ℝ≥0∞} (ha : a ≠ ⊤)
    {f g : Vec d → ℝ≥0∞} (h : ∀ x, f x ≤ a * g x) :
    eVolumeAverage V f ≤ a * eVolumeAverage V g :=
  le_trans (eVolumeAverage_mono V h) (le_of_eq (eVolumeAverage_const_mul V a ha g))

/-- Division by a nonnegative denominator is monotone in the numerator. -/
private theorem div_le_div_of_le_of_nonneg {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) :
    a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hab (inv_nonneg.mpr hc)

/-! ## Linear images of the whole space -/

/-- An invertible linear image of a measurable set is measurable. -/
theorem measurableSet_matImage {L : Mat d} (hL : IsUnit L.det) {U : Set (Vec d)}
    (hU : MeasurableSet U) : MeasurableSet (matImage L U) := by
  rw [matImage_eq_preimage hL]
  exact hU.preimage (continuous_matVecMul L⁻¹).measurable

/-- An invertible linear image of a set of positive volume has positive
volume. -/
theorem volume_matImage_ne_zero {L : Mat d} (hL : IsUnit L.det) {U : Set (Vec d)}
    (hU0 : volume U ≠ 0) : volume (matImage L U) ≠ 0 := by
  rw [volume_matImage]
  exact mul_ne_zero
    (ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr hL.ne_zero)) hU0

/-! ## The Gagliardo term under a pointwise bound on increments -/

/-- A pointwise comparison of increments passes to the Gagliardo double
integral. -/
theorem fracSeminormSq_mono_of_le (V : Set (Vec d)) (s : ℝ) {c : ℝ} (hc : 0 ≤ c)
    {F G : Vec d → Vec d}
    (h : ∀ x y : Vec d, vecNormSq (F x - F y) ≤ c * vecNormSq (G x - G y)) :
    fracSeminormSq V s F ≤ ENNReal.ofReal c * fracSeminormSq V s G := by
  simp only [fracSeminormSq]
  refine eVolumeAverage_le_const_mul V ENNReal.ofReal_ne_top fun x => ?_
  refine le_trans (lintegral_mono fun y => ?_)
    (le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top))
  rw [← ENNReal.ofReal_mul hc]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← mul_div_assoc]
  exact div_le_div_of_le_of_nonneg (h x y)
    (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

/-! ## The domain transport -/

/-- **The Gagliardo term under an invertible change of variables.**  The
determinant of the inner integral and the kernel distortion `N ^ (d + 2s)` are
the only losses, where `N` is any constant with `|w| ≤ N |L w|`. -/
theorem fracSeminormSq_matImage_le {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) {s N : ℝ}
    (hs : 0 ≤ (d : ℝ) + 2 * s) (hN : 0 ≤ N)
    (hker : ∀ w : Vec d,
      Real.sqrt (vecNormSq w) ≤ N * Real.sqrt (vecNormSq (matVecMul L w)))
    (F : Vec d → Vec d) :
    fracSeminormSq (matImage L U) s F ≤
      ENNReal.ofReal (|L.det| * N ^ ((d : ℝ) + 2 * s)) *
        fracSeminormSq U s (fun y => F (matVecMul L y)) := by
  simp only [fracSeminormSq]
  rw [eVolumeAverage_matImage hL hU, ENNReal.ofReal_mul (abs_nonneg L.det)]
  refine eVolumeAverage_le_const_mul U
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) fun u => ?_
  rw [setLIntegral_matImage hL hU, mul_assoc]
  refine mul_le_mul_right ?_ _
  refine le_trans (lintegral_mono fun v => ?_)
    (le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top))
  rw [matVecMul_sub_vec, ← ENNReal.ofReal_mul (Real.rpow_nonneg hN _)]
  exact ENNReal.ofReal_le_ofReal
    (gagliardo_kernel_matVecMul_le hN hs hker (vecNormSq_nonneg _) (u - v))

/-- The normalized `L²` term of the fractional norm square rescales by a pure
determinant power under an invertible change of variables. -/
theorem l2Term_matImage {L : Mat d} (hL : IsUnit L.det) {U : Set (Vec d)}
    (hU : MeasurableSet U) (hU0 : volume U ≠ 0) (s : ℝ) (F : Vec d → Vec d) :
    volume (matImage L U) ^ (-(2 * s) / (d : ℝ)) *
        eVolumeAverage (matImage L U)
          (fun x => ENNReal.ofReal (vecNormSq (F x))) =
      ENNReal.ofReal (|L.det| ^ (-(2 * s) / (d : ℝ))) *
        (volume U ^ (-(2 * s) / (d : ℝ)) *
          eVolumeAverage U
            (fun y => ENNReal.ofReal (vecNormSq (F (matVecMul L y))))) := by
  have hdetpos : 0 < |L.det| := abs_pos.mpr hL.ne_zero
  have hdet0 : ENNReal.ofReal |L.det| ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hdetpos
  rw [volume_matImage, ENNReal.mul_rpow_of_ne_zero hdet0 hU0,
    ENNReal.ofReal_rpow_of_pos hdetpos, eVolumeAverage_matImage hL hU, mul_assoc]

/-- The affine distortion factor of the normalized `H^s` norm square: the larger
of the determinant power seen by the `L²` term and the determinant-times-kernel
factor seen by the Gagliardo term. -/
@[expose]
def hsAffineFactor (L : Mat d) (s N : ℝ) : ℝ :=
  max (|L.det| ^ (-(2 * s) / (d : ℝ))) (|L.det| * N ^ ((d : ℝ) + 2 * s))

/-- The affine distortion factor is positive for an invertible matrix. -/
theorem hsAffineFactor_pos {L : Mat d} (hL : IsUnit L.det) (s N : ℝ) :
    0 < hsAffineFactor L s N :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (abs_pos.mpr hL.ne_zero) _)
    (le_max_left _ _)

/-- **The normalized `H^s` norm square under an invertible change of
variables.**  The constant is the affine distortion factor built from the
determinant of `L` and from any constant `N` with `|w| ≤ N |L w|`. -/
theorem hsNormSq_matImage_le {L : Mat d} (hL : IsUnit L.det) {U : Set (Vec d)}
    (hU : MeasurableSet U) (hU0 : volume U ≠ 0) {s N : ℝ}
    (hs : 0 ≤ (d : ℝ) + 2 * s) (hN : 0 ≤ N)
    (hker : ∀ w : Vec d,
      Real.sqrt (vecNormSq w) ≤ N * Real.sqrt (vecNormSq (matVecMul L w)))
    (F : Vec d → Vec d) :
    hsNormSq (matImage L U) s F ≤
      ENNReal.ofReal (hsAffineFactor L s N) *
        hsNormSq U s (fun y => F (matVecMul L y)) := by
  simp only [hsNormSq, hsAffineFactor]
  rw [mul_add]
  refine add_le_add ?_ ?_
  · rw [l2Term_matImage hL hU hU0]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  · exact le_trans (fracSeminormSq_matImage_le hL hU hs hN hker F)
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _)

/-- **The reverse comparison.**  The pullback of a field to the source domain is
controlled by the field on the image, with the distortion factor of the inverse
map. -/
theorem hsNormSq_comp_matVecMul_le {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hU0 : volume U ≠ 0) {s N : ℝ}
    (hs : 0 ≤ (d : ℝ) + 2 * s) (hN : 0 ≤ N)
    (hker : ∀ w : Vec d,
      Real.sqrt (vecNormSq w) ≤ N * Real.sqrt (vecNormSq (matVecMul L⁻¹ w)))
    (F : Vec d → Vec d) :
    hsNormSq U s (fun y => F (matVecMul L y)) ≤
      ENNReal.ofReal (hsAffineFactor L⁻¹ s N) * hsNormSq (matImage L U) s F := by
  have hLinv : IsUnit (L⁻¹).det := Matrix.isUnit_nonsing_inv_det L hL
  have h : hsNormSq (matImage L⁻¹ (matImage L U)) s
        (fun y => F (matVecMul L y)) ≤
      ENNReal.ofReal (hsAffineFactor L⁻¹ s N) *
        hsNormSq (matImage L U) s
          (fun y => F (matVecMul L (matVecMul L⁻¹ y))) :=
    hsNormSq_matImage_le hLinv (measurableSet_matImage hL hU)
      (volume_matImage_ne_zero hL hU0) hs hN hker (fun y => F (matVecMul L y))
  have hcomp : (fun y : Vec d => F (matVecMul L (matVecMul L⁻¹ y))) = F := by
    funext y
    rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
  rwa [matImage_inv_matImage hL, hcomp] at h

/-! ## The operator-norm instantiations -/

/-- The change-of-variables comparison with the explicit constant built from the
determinant of `L` and the `ℓ²` operator norm of `L⁻¹`. -/
theorem hsNormSq_matImage_le_opNorm {L : Mat d} (hL : IsUnit L.det)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hU0 : volume U ≠ 0) {s : ℝ}
    (hs : 0 ≤ (d : ℝ) + 2 * s) (F : Vec d → Vec d) :
    hsNormSq (matImage L U) s F ≤
      ENNReal.ofReal (hsAffineFactor L s ‖L⁻¹‖) *
        hsNormSq U s (fun y => F (matVecMul L y)) :=
  hsNormSq_matImage_le hL hU hU0 hs (norm_nonneg _)
    (sqrt_vecNormSq_le_norm_inv_mul hL) F

/-! ## The pointwise matrix action on field values -/

/-- Multiplying the values of a field by a fixed matrix costs the squared `ℓ²`
operator norm of that matrix in the Gagliardo term. -/
theorem fracSeminormSq_matVecMul_le (M : Mat d) (V : Set (Vec d)) (s : ℝ)
    (F : Vec d → Vec d) :
    fracSeminormSq V s (fun x => matVecMul M (F x)) ≤
      ENNReal.ofReal (‖M‖ ^ 2) * fracSeminormSq V s F := by
  refine fracSeminormSq_mono_of_le V s (sq_nonneg _) fun x y => ?_
  rw [matVecMul_sub_vec]
  exact vecNormSq_matVecMul_le M (F x - F y)

/-- **The pointwise matrix action on the normalized `H^s` norm square.**  The
domain is untouched; the cost is the squared `ℓ²` operator norm. -/
theorem hsNormSq_matVecMul_le (M : Mat d) (V : Set (Vec d)) (s : ℝ)
    (F : Vec d → Vec d) :
    hsNormSq V s (fun x => matVecMul M (F x)) ≤
      ENNReal.ofReal (‖M‖ ^ 2) * hsNormSq V s F := by
  have hL2 : eVolumeAverage V
        (fun x => ENNReal.ofReal (vecNormSq (matVecMul M (F x)))) ≤
      ENNReal.ofReal (‖M‖ ^ 2) *
        eVolumeAverage V (fun x => ENNReal.ofReal (vecNormSq (F x))) := by
    refine eVolumeAverage_le_const_mul V ENNReal.ofReal_ne_top fun x => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (vecNormSq_matVecMul_le M (F x))
  simp only [hsNormSq]
  rw [mul_add]
  refine add_le_add ?_ (fracSeminormSq_matVecMul_le M V s F)
  rw [← mul_left_comm]
  exact mul_le_mul_right hL2 _

end

end HighContrast
end HCPolySupport
