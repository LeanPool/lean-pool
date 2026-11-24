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

/-- Antisymmetry of a real two-form in its two slots. -/
theorem coordinateFrame_twoForm_swap {n : ℕ} (A : CoordinateRealTwoForm n)
    (u v : ComplexModel n) :
    A ![v, u] = -A ![u, v] := by
  simpa using A.map_swap ![u, v] (i := 0) (j := 1) (by decide)

/-- A real two-form is `ℝ`-homogeneous in its first slot. -/
theorem coordinateFrame_twoForm_smul_left {n : ℕ} (A : CoordinateRealTwoForm n)
    (r : ℝ) (u v : ComplexModel n) :
    A ![r • u, v] = r * A ![u, v] :=
  A.toMultilinearMap.cons_smul ![v] r u

/-- A real two-form is additive in its first slot. -/
theorem coordinateFrame_twoForm_add_left {n : ℕ} (A : CoordinateRealTwoForm n)
    (u u' v : ComplexModel n) :
    A ![u + u', v] = A ![u, v] + A ![u', v] :=
  A.toMultilinearMap.cons_add ![v] u u'

/-- A real two-form is additive in its second slot. -/
theorem coordinateFrame_twoForm_add_right {n : ℕ} (A : CoordinateRealTwoForm n)
    (u v v' : ComplexModel n) :
    A ![u, v + v'] = A ![u, v] + A ![u, v'] := by
  rw [coordinateFrame_twoForm_swap A (v + v') u, coordinateFrame_twoForm_add_left,
    coordinateFrame_twoForm_swap A u v, coordinateFrame_twoForm_swap A u v']
  ring

/-- A real two-form is `ℝ`-homogeneous in its second slot. -/
theorem coordinateFrame_twoForm_smul_right {n : ℕ} (A : CoordinateRealTwoForm n)
    (r : ℝ) (u v : ComplexModel n) :
    A ![u, r • v] = r * A ![u, v] := by
  rw [coordinateFrame_twoForm_swap A (r • v) u,
    coordinateFrame_twoForm_smul_left, coordinateFrame_twoForm_swap A u v]
  ring

/-- A real two-form negates when its second slot is negated. -/
theorem coordinateFrame_twoForm_neg_right {n : ℕ} (A : CoordinateRealTwoForm n)
    (u v : ComplexModel n) :
    A ![u, -v] = -A ![u, v] := by
  simpa using coordinateFrame_twoForm_smul_right A (-1) u v

/-- A real `(1,1)`-form moves multiplication by `i` between its slots with a sign. -/
theorem coordinateFrame_twoForm_I_smul_left_of_isOneOne {n : ℕ}
    {A : CoordinateRealTwoForm n} (hA : IsOneOne A) (u v : ComplexModel n) :
    A ![Complex.I • u, v] = -A ![u, Complex.I • v] := by
  rw [← hA u (Complex.I • v), smul_smul, Complex.I_mul_I, neg_one_smul,
    coordinateFrame_twoForm_neg_right]
  ring

/-- The mixed coefficient `A(e_j, i e_k)` of a real `(1,1)`-form is symmetric. -/
theorem coordinateFrame_mixed_coefficient_symm {n : ℕ}
    (A : CoordinateRealTwoForm n) (hA : IsOneOne A) (j k : Fin n) :
    A ![coordinateVector k, Complex.I • coordinateVector j] =
      A ![coordinateVector j, Complex.I • coordinateVector k] := by
  rw [coordinateFrame_twoForm_swap A (Complex.I • coordinateVector j)
      (coordinateVector k),
    coordinateFrame_twoForm_I_smul_left_of_isOneOne hA]
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
    coordinateFrame_twoForm_swap A (coordinateVector j) (coordinateVector k)]
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
    exact coordinateFrame_twoForm_I_smul_left_of_isOneOne hA _ _
  · simp only [Fin.isValue]
    exact hA _ _

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
