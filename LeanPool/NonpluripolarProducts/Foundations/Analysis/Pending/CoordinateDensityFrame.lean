/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.StandardKahlerTopPower

/-!
# Real-frame block coefficients of a `(1,1)` two-form

The Pfaffian expression for a top exterior power is evaluated on the
interleaved real frame `e₀, Ie₀, …, eₙ₋₁, Ieₙ₋₁`.  This file isolates the
general block identity that converts a real `(1,1)` form on that frame into
the two complex-coordinate coefficient arrays

`B(j,k) = A(eⱼ,eₖ)` and `C(j,k) = A(eⱼ,Ieₖ)`.

It is the uniform algebraic input for a future shuffle-to-determinant proof:
every real-frame Pfaffian summand can be rewritten solely in terms of `B` and
`C`, before the remaining finite permutation combinatorics is addressed.
-/

@[expose] public section

noncomputable section

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

/-- The mixed coefficient `A(e_j, i e_k)` of a real `(1,1)`-form is symmetric. -/
theorem coordinateFrame_mixed_coefficient_symm {n : ℕ}
    (A : CoordinateRealTwoForm n) (hA : IsOneOne A) (j k : Fin n) :
    A ![coordinateVector k, Complex.I • coordinateVector j] =
      A ![coordinateVector j, Complex.I • coordinateVector k] := by
  rw [twoForm_swap A (Complex.I • coordinateVector j)
      (coordinateVector k),
    twoForm_I_smul_left_of_isOneOne hA]
  ring

/-- The complex coefficient matrix extracted from a real `(1,1)` form is
Hermitian.  Thus its determinant is real, as required for comparison with a
real exterior-power density. -/
theorem normalizedHermitianMatrix_isHermitian {n : ℕ}
    (A : CoordinateRealTwoForm n) (hA : IsOneOne A) :
    (normalizedHermitianMatrix A).IsHermitian := by
  ext j k
  change star (normalizedHermitianMatrix A k j) = normalizedHermitianMatrix A j k
  rw [normalizedHermitianMatrix, normalizedHermitianMatrix,
    coordinateFrame_mixed_coefficient_symm A hA,
    twoForm_swap A (coordinateVector j) (coordinateVector k)]
  rw [Complex.star_def]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]

/-- The determinant of the normalized Hermitian coefficient matrix has zero
imaginary part.  This removes the final complex-to-real ambiguity from the
determinant side of the future Pfaffian comparison. -/
theorem normalizedHermitianMatrix_det_im_eq_zero {n : ℕ}
    (A : CoordinateRealTwoForm n) (hA : IsOneOne A) :
    (normalizedHermitianMatrix A).det.im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  change star ((normalizedHermitianMatrix A).det) = (normalizedHermitianMatrix A).det
  rw [← Matrix.det_conjTranspose,
    (normalizedHermitianMatrix_isHermitian A hA).eq]

/-- The real-frame block coefficient identity of a real `(1,1)` two-form.
The four cases are the entries of the real block
`[[B(j,k), C(j,k)], [-C(j,k), B(j,k)]]`. -/
theorem coordinateTwoForm_apply_realFrame_block {n : ℕ}
    (A : CoordinateRealTwoForm n) (hA : IsOneOne A)
    (j k : Fin n) (b c : Fin 2) :
    A ![coordinateRealFrame (finProdFinEquiv (j, b)),
        coordinateRealFrame (finProdFinEquiv (k, c))] =
      if b = 0 then
        if c = 0 then A ![coordinateVector j, coordinateVector k]
        else A ![coordinateVector j, Complex.I • coordinateVector k]
      else if c = 0 then -A ![coordinateVector j, Complex.I • coordinateVector k]
      else A ![coordinateVector j, coordinateVector k] := by
  rw [coordinateRealFrame_finProdFinEquiv, coordinateRealFrame_finProdFinEquiv]
  fin_cases b <;> fin_cases c
  · simp
  · simp
  · simp only [Fin.isValue]
    exact twoForm_I_smul_left_of_isOneOne hA _ _
  · simp only [Fin.isValue]
    exact hA _ _

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
