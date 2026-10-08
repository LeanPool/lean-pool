/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.RelativeSize

/-!
# High-contrast homogenization: Geometry.DetOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Determinants and the Loewner order

The canonical block geometry takes determinants across Loewner inequalities
twice.  In the determinant bound for the canonical metric the balance chain
`M(E) ≤ E ≤ 𝔡(E)^{1/2} M(E)` is read through the determinant, and in
`e.global.selection.metric.loss` the product of the generalized eigenvalues of
a pair is the quotient `det(E)/det(F)` of the two determinants.  Both steps rest
on the two facts collected here:

* the determinant is monotone for the Loewner order on positive definite data,
  and a matrix above the identity has determinant at least one;
* a matrix above the identity has spectral norm at most its determinant.

The last one is the scalar form of the reference text's sentence "every
eigenvalue of `F^{-1/2}EF^{-1/2}` is at least one and their product is
`det(E)/det(F)`, so each eigenvalue is at most `det(E)/det(F)`": on positive
data `‖·‖` is the largest eigenvalue, and the remaining eigenvalues contribute a
factor at least one to the product.

All three statements are read off the eigenvalues of a symmetric matrix, so the
file opens with the two facts about them that are used.  An eigenvalue is the
quadratic form evaluated at the corresponding unit eigenvector, which turns a
Loewner hypothesis into a bound on every eigenvalue; conversely a matrix all of
whose eigenvalues are at most `t` is bounded by `t I`, which is the spectral
theorem read as a congruence of the diagonalization.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Eigenvalues of a symmetric matrix -/

/-- The determinant of a real symmetric matrix is the product of its
eigenvalues. -/
private theorem det_eq_prod_eigenvalues_real {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A.det = ∏ i, hA.eigenvalues i := by
  simpa using hA.det_eq_prod_eigenvalues

/-- The eigenvectors of a symmetric matrix are unit vectors for the dot
product. -/
theorem dotProduct_eigenvectorBasis_self {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    star (⇑(hA.eigenvectorBasis i) : n → ℝ) ⬝ᵥ (⇑(hA.eigenvectorBasis i) : n → ℝ) = 1 := by
  have hnorm := hA.eigenvectorBasis.orthonormal.1 i
  have hinner : (inner ℝ (hA.eigenvectorBasis i) (hA.eigenvectorBasis i) : ℝ)
      = ‖hA.eigenvectorBasis i‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [hnorm, EuclideanSpace.inner_eq_star_dotProduct] at hinner
  simpa [dotProduct_comm] using hinner

/-- **A Loewner bound below is a bound on every eigenvalue.**  Evaluating the
quadratic form of `A - I` at the `i`-th unit eigenvector gives
`eigenvalues A i - 1 ≥ 0`. -/
theorem one_le_eigenvalues_of_one_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (h : 1 ≤ A) (i : n) : 1 ≤ hA.eigenvalues i := by
  have hPS : ((A : Matrix n n ℝ) - 1).PosSemidef := Matrix.le_iff.mp h
  have hq := hPS.dotProduct_mulVec_nonneg (⇑(hA.eigenvectorBasis i) : n → ℝ)
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    dotProduct_eigenvectorBasis_self hA i] at hq
  have hval : hA.eigenvalues i
      = star (⇑(hA.eigenvectorBasis i) : n → ℝ) ⬝ᵥ (A *ᵥ ⇑(hA.eigenvectorBasis i)) := by
    simpa using hA.eigenvalues_eq i
  rw [hval]
  linarith only [hq]

/-- **A bound on every eigenvalue is a Loewner bound above.**  This is the
spectral theorem: the diagonalization is a congruence, and the diagonal matrix
`t I - diag(eigenvalues)` has nonnegative entries. -/
theorem le_smul_one_of_eigenvalues_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {t : ℝ}
    (h : ∀ i, hA.eigenvalues i ≤ t) : A ≤ t • (1 : Matrix n n ℝ) := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℝ) *
      (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspec : A = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal hA.eigenvalues * (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  have hsplit : Matrix.diagonal (fun i => t - hA.eigenvalues i)
      = t • (1 : Matrix n n ℝ) - Matrix.diagonal hA.eigenvalues := by
    ext j k
    by_cases hjk : j = k <;> simp [Matrix.diagonal, hjk]
  have hkey : (hA.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => t - hA.eigenvalues i) *
      (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ = t • (1 : Matrix n n ℝ) - A := by
    rw [hsplit, Matrix.mul_sub, Matrix.sub_mul, ← hspec]
    congr 1
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
  have hdiag : (Matrix.diagonal (fun i => t - hA.eigenvalues i)).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => sub_nonneg.mpr (h i)
  have hconj := hdiag.conjTranspose_mul_mul_same ((hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ)
  rw [Matrix.conjTranspose_conjTranspose, hkey] at hconj
  exact Matrix.le_iff.mpr hconj

/-! ## Determinant monotonicity -/

/-- **A matrix above the identity has determinant at least one.** -/
theorem one_le_det_of_one_le {A : Matrix n n ℝ} (hA : A.PosDef) (h : 1 ≤ A) : 1 ≤ A.det := by
  rw [det_eq_prod_eigenvalues_real hA.isHermitian]
  have hbound := Finset.prod_le_prod₀ (s := (Finset.univ : Finset n)) (f := fun _ => (1 : ℝ))
    (g := hA.isHermitian.eigenvalues) (fun _ _ => zero_le_one)
    (fun i _ => one_le_eigenvalues_of_one_le hA.isHermitian h i)
  simpa using hbound

/-- **A matrix above the identity has spectral norm at most its determinant.**
This is the scalar form of the eigenvalue argument of
`e.global.selection.metric.loss`: the largest eigenvalue is at most the
product of all of them, because the others are at least one. -/
theorem norm_le_det_of_one_le {A : Matrix n n ℝ} (hA : A.PosDef) (h : 1 ≤ A) : ‖A‖ ≤ A.det := by
  have hdet : (1 : ℝ) ≤ A.det := one_le_det_of_one_le hA h
  refine norm_le_of_le_smul_one hA.posSemidef (le_trans zero_le_one hdet) ?_
  refine le_smul_one_of_eigenvalues_le hA.isHermitian fun i => ?_
  rw [det_eq_prod_eigenvalues_real hA.isHermitian,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, hA.isHermitian.eigenvalues j := by
    have hbound := Finset.prod_le_prod₀ (s := Finset.univ.erase i) (f := fun _ => (1 : ℝ))
      (g := hA.isHermitian.eigenvalues) (fun _ _ => zero_le_one)
      (fun j _ => one_le_eigenvalues_of_one_le hA.isHermitian h j)
    simpa using hbound
  have hi : (1 : ℝ) ≤ hA.isHermitian.eigenvalues i :=
    one_le_eigenvalues_of_one_le hA.isHermitian h i
  nlinarith only [hrest, hi]

/-- The square of the determinant of the inverse square root. -/
private theorem det_matSqrt_inv_sq {A : Matrix n n ℝ} (hA : A.PosDef) :
    (matSqrt A⁻¹).det * (matSqrt A⁻¹).det = (A.det)⁻¹ := by
  rw [← Matrix.det_mul, (matSqrt_spec hA.inv.posSemidef).2, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv']

/-- **The determinant of a normalization.**  Conjugating by `A^{-1/2}` divides
the determinant by `det A`; this is the reference text's "their product is
`det(E)/det(F)`". -/
theorem det_conj_matSqrt_inv {A B : Matrix n n ℝ} (hA : A.PosDef) :
    (matSqrt A⁻¹ * B * matSqrt A⁻¹).det = B.det / A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, div_eq_inv_mul, ← det_matSqrt_inv_sq hA]
  ring

/-- **The determinant is monotone for the Loewner order.**  Conjugating
`A ≤ B` by `A^{-1/2}` gives `I ≤ A^{-1/2} B A^{-1/2}`, whose determinant is
`det(B)/det(A)`. -/
theorem det_le_det_of_le {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) (h : A ≤ B) :
    A.det ≤ B.det := by
  have hAdet : 0 < A.det := hA.det_pos
  have hnorm : (1 : Matrix n n ℝ) ≤ matSqrt A⁻¹ * B * matSqrt A⁻¹ := by
    have hcong := conj_le_conj' (conjTranspose_matSqrt_inv hA) h
    rwa [matSqrt_inv_conj hA] at hcong
  have hone := one_le_det_of_one_le (posDef_normalize hB hA) hnorm
  rw [det_conj_matSqrt_inv hA] at hone
  have hmul := mul_le_mul_of_nonneg_left hone hAdet.le
  rw [mul_one] at hmul
  have hrw : A.det * (B.det / A.det) = B.det := by field_simp
  rwa [hrw] at hmul

/-- **The determinant quotient bounds the relative size.**  This is the opening
sentence of the proof of `e.global.selection.metric.loss`: if `F ≤ E` then
every generalized eigenvalue of `E` relative to `F` is at least one, so the
largest of them — the relative size — is at most their product `det(E)/det(F)`.
No eigenvalue is named: the largest one is `‖F^{-1/2} E F^{-1/2}‖` and the
product is its determinant. -/
theorem relSize_le_det_div {E F : Matrix n n ℝ} (hE : E.PosDef) (hF : F.PosDef) (h : F ≤ E) :
    relSize E F ≤ E.det / F.det := by
  have hnorm : (1 : Matrix n n ℝ) ≤ matSqrt F⁻¹ * E * matSqrt F⁻¹ := by
    have hcong := conj_le_conj' (conjTranspose_matSqrt_inv hF) h
    rwa [matSqrt_inv_conj hF] at hcong
  have hbound := norm_le_det_of_one_le (posDef_normalize hE hF) hnorm
  rwa [det_conj_matSqrt_inv hF, ← relSize_def] at hbound

end

end HighContrast
end HCPolySupport
