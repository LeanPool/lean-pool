/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioOrder
public import LeanPool.HighContrastHomogenization.Geometry.SchurData
public import LeanPool.HighContrastHomogenization.Geometry.SizeAlignment

/-!
# High-contrast homogenization: Provider.SourceControl.SchurHelpers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schur-form helpers for the reference intermediate

The endpoint `κ_𝐄 ≤ 6 Π` of the factor-six reference-block comparison and the
intermediate `κ_𝐄 ≤ 1 + 6(Θ - 1)` of
`HCPoly.Provider.SourceControl.ReferenceIntermediate` use the same
Schur-form transport lemmas.  They live here so both comparison modules can
reuse one public implementation.

Two of them are new: `dotProduct_mulVec_smul_self` and
`dotProduct_mulVec_smul_add_smul`, the expansions of a quadratic form on a
scalar multiple and on a two-term combination.  They replace the endpoint's
Young inequality at weight five, which the intermediate cannot use.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Initialization

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Transport between the two Loewner encodings -/

/-- **The quadratic form of a congruence.** -/
theorem quad_conj {n : Type*} [Fintype n]
    (C M : Matrix n n ℝ) (v : n → ℝ) :
    v ⬝ᵥ (Cᴴ * M * C) *ᵥ v = (C *ᵥ v) ⬝ᵥ M *ᵥ (C *ᵥ v) := by
  rw [conjTranspose_eq_transpose', Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- A doubled vector is the elimination of its two halves. -/
theorem elim_comp (v : FullBlockVec d) :
    Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
  funext α
  cases α <;> rfl

/-- **The matrix order from the pointwise comparison of quadratic forms.** -/
theorem le_of_dotProduct_mulVec_le {n : Type*} [Fintype n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ v : n → ℝ, v ⬝ᵥ A *ᵥ v ≤ v ⬝ᵥ B *ᵥ v) : A ≤ B := by
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA)
    fun v => ?_)
  rw [Matrix.sub_mulVec, dotProduct_sub]
  simp only [star_trivial]
  linarith only [h v]

/-- **The pointwise comparison of quadratic forms from the matrix order.** -/
theorem dotProduct_mulVec_le_of_le {n : Type*} [Fintype n]
    {A B : Matrix n n ℝ} (h : A ≤ B) (x : n → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ B *ᵥ x := by
  have hPS : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hx := hPS.dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, dotProduct_sub] at hx
  simp only [star_trivial] at hx
  linarith only [hx]

/-- The `MatLoewnerLE` encoding from the matrix order. -/
theorem matLoewnerLE_of_le {A B : Mat d} (h : A ≤ B) : MatLoewnerLE A B := by
  intro x
  have hx := dotProduct_mulVec_le_of_le h x
  have hA : vecDot x (matVecMul A x) = x ⬝ᵥ A *ᵥ x := rfl
  have hB : vecDot x (matVecMul B x) = x ⬝ᵥ B *ᵥ x := rfl
  rw [hA, hB]
  linarith only [hx]

/-- The matrix order from the `MatLoewnerLE` encoding. -/
theorem le_of_matLoewnerLE {A B : Mat d} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : MatLoewnerLE A B) : A ≤ B := by
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA)
    fun x => ?_)
  have hx := h x
  have hA' : vecDot x (matVecMul A x) = x ⬝ᵥ A *ᵥ x := rfl
  have hB' : vecDot x (matVecMul B x) = x ⬝ᵥ B *ᵥ x := rfl
  rw [hA', hB'] at hx
  rw [Matrix.sub_mulVec, dotProduct_sub]
  simp only [star_trivial]
  linarith only [hx]

/-! ## Two matrix inequalities -/

/-- **The parallelogram bound.**  A sum is squared by a positive semidefinite
congruence at the cost of a factor two on each summand. -/
theorem conj_add_le {X : Mat d} (hX : X.PosSemidef) (a b : Mat d) :
    (a + b)ᴴ * X * (a + b) ≤ (aᴴ * X * a + aᴴ * X * a) + (bᴴ * X * b + bᴴ * X * b) := by
  refine Matrix.le_iff.mpr ?_
  have hdiff : (aᴴ * X * a + aᴴ * X * a) + (bᴴ * X * b + bᴴ * X * b) -
      (a + b)ᴴ * X * (a + b) = (a - b)ᴴ * X * (a - b) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub]
    noncomm_ring
  rw [hdiff]
  exact hX.conjTranspose_mul_mul_same _

/-- **Transposition preserves a normalized quadratic bound.**  If `mᵗ X m ≤ c X⁻¹`
then `m X mᵗ ≤ c X⁻¹`; the two sides are the squared operator norms of
`X^{1/2} m X^{1/2}` and its transpose. -/
theorem conj_transpose_le_of_conj_le {X : Mat d} (hX : X.PosDef) {m : Mat d}
    {c : ℝ} (hc : 0 ≤ c) (h : mᴴ * X * m ≤ c • X⁻¹) : m * X * mᴴ ≤ c • X⁻¹ := by
  set R : Mat d := matSqrt X with hRdef
  have hRpsd : R.PosSemidef := (matSqrt_spec hX.posSemidef).1
  have hRR : R * R = X := (matSqrt_spec hX.posSemidef).2
  have hRsymm : Rᴴ = R := hRpsd.isHermitian
  have hRunit : IsUnit R := isUnit_matSqrt hX
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det _).mp hRunit
  have hRXR : R * X⁻¹ * R = 1 := by
    rw [← hRR, Matrix.mul_inv_rev]
    calc R * (R⁻¹ * R⁻¹) * R = (R * R⁻¹) * (R⁻¹ * R) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by
          rw [Matrix.mul_nonsing_inv R hRdet, Matrix.nonsing_inv_mul R hRdet, one_mul]
  set N : Mat d := R * m * R with hNdef
  have hNH : Nᴴ = R * mᴴ * R := by
    rw [hNdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hRsymm,
      Matrix.mul_assoc]
  have hNN : Nᴴ * N = R * (mᴴ * X * m) * R := by
    rw [hNH, hNdef, ← hRR]
    noncomm_ring
  have hstep : Nᴴ * N ≤ c • (1 : Mat d) := by
    have hconj := conj_le_conj' hRsymm h
    rw [Matrix.mul_smul, Matrix.smul_mul, hRXR] at hconj
    rwa [hNN]
  have hnorm : ‖N‖ * ‖N‖ ≤ c := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self]
    exact norm_le_of_le_smul_one (Matrix.posSemidef_conjTranspose_mul_self N) hc hstep
  have hnorm' : ‖N * Nᴴ‖ ≤ c := by
    have hrw : N * Nᴴ = (Nᴴ)ᴴ * Nᴴ := by rw [Matrix.conjTranspose_conjTranspose]
    rw [hrw, Matrix.l2_opNorm_conjTranspose_mul_self, Matrix.l2_opNorm_conjTranspose]
    exact hnorm
  have hNNH : N * Nᴴ = R * (m * X * mᴴ) * R := by
    rw [hNH, hNdef, ← hRR]
    noncomm_ring
  have hfinal : R * (m * X * mᴴ) * R ≤ R * (c • X⁻¹) * R := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hRXR, ← hNNH]
    exact le_smul_one_of_norm_le
      (by rw [hNNH, ← hNNH]; exact Matrix.posSemidef_self_mul_conjTranspose N) hnorm'
  exact (conj_le_conj_iff (C := R) hRunit).mp (by rwa [hRsymm])

/-! ## Expansions of a quadratic form -/

/-- A scalar multiple passes the quadratic form as its square. -/
theorem dotProduct_mulVec_smul_self (X : Mat d) (a : ℝ) (u : Vec d) :
    (a • u) ⬝ᵥ X *ᵥ (a • u) = a ^ 2 * (u ⬝ᵥ X *ᵥ u) := by
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- **The bilinear expansion.**  A symmetric matrix squares a two-term
combination into the three scalar products. -/
theorem dotProduct_mulVec_smul_add_smul {X : Mat d} (hX : Xᵀ = X) (a b : ℝ)
    (u v : Vec d) :
    (a • u + b • v) ⬝ᵥ X *ᵥ (a • u + b • v) =
      a ^ 2 * (u ⬝ᵥ X *ᵥ u) + 2 * (a * b) * (u ⬝ᵥ X *ᵥ v) + b ^ 2 * (v ⬝ᵥ X *ᵥ v) := by
  have hcross : v ⬝ᵥ X *ᵥ u = u ⬝ᵥ X *ᵥ v := by
    rw [dotProduct_mulVec_symm hX v u, dotProduct_comm]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, hcross]
  ring

end

end Initialization
end HighContrast
end HCPolySupport
