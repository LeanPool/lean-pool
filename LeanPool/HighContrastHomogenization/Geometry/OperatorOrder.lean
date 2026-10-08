/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# High-contrast homogenization: Geometry.OperatorOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Loewner order, the spectral norm, and the square root

The canonical block geometry built on the matrix geometric mean is read entirely
through the Loewner order on real symmetric matrices, written `≤` here, and the
spectral norm `|·|`, written `‖·‖`.  This file collects the interface between the
two:

* congruence `A ≤ B → Cᵀ A C ≤ Cᵀ B C`, and its converse for invertible `C`;
* the scalar comparison `‖A‖ ≤ t ↔ A ≤ t • I` on positive semidefinite data,
  which is the statement that `‖A‖` is the largest eigenvalue;
* order reversal under inversion;
* operator monotonicity of the square root.

Only the last one is not immediate.  The reference text proves it from the
integral representation of the square root; the proof given here is the
equivalent norm argument: writing `S`, `T` for the roots of `A ≤ B` and
`W := T^{-1/2} S T^{-1/2}`, the powers `W^m` factor through `S T^{-1}`, whose
norm the hypothesis bounds by one, so `‖W‖^m` stays bounded and `‖W‖ ≤ 1`.

The scalar sizes of the reference text are spectral norms of positive
semidefinite matrices throughout this development.  The setup layer's
`specBound` is the same number (`specBound_eq_norm`); `‖·‖` is used here because
the geometry is built on index types other than `Fin d`.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Real transposes -/

omit [Fintype n] [DecidableEq n] in
/-- Over the reals the conjugate transpose is the transpose. -/
theorem conjTranspose_eq_transpose' (A : Matrix n n ℝ) : Aᴴ = Aᵀ :=
  Matrix.conjTranspose_eq_transpose_of_trivial A

omit [Fintype n] [DecidableEq n] in
/-- A symmetric real matrix is Hermitian. -/
theorem isHermitian_of_isSymm {A : Matrix n n ℝ} (h : A.IsSymm) : A.IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_eq_transpose']
  exact h

omit [Fintype n] [DecidableEq n] in
/-- A Hermitian real matrix is symmetric. -/
theorem isSymm_of_isHermitian {A : Matrix n n ℝ} (h : A.IsHermitian) : A.IsSymm := by
  rw [Matrix.IsSymm, ← conjTranspose_eq_transpose']
  exact h

/-! ## Congruence -/

omit [DecidableEq n] in
/-- **Congruence is monotone.**  Conjugating both sides of a Loewner inequality
by the same matrix preserves it. -/
theorem conj_le_conj {A B : Matrix n n ℝ} (C : Matrix n n ℝ) (h : A ≤ B) :
    Cᴴ * A * C ≤ Cᴴ * B * C := by
  have hPS : (B - A).PosSemidef := Matrix.le_iff.mp h
  have hconj := hPS.conjTranspose_mul_mul_same C
  rw [Matrix.le_iff]
  have hrw : Cᴴ * B * C - Cᴴ * A * C = Cᴴ * (B - A) * C := by noncomm_ring
  rw [hrw]
  exact hconj

/-- **Congruence by an invertible matrix reflects the order.** -/
theorem conj_le_conj_iff {A B C : Matrix n n ℝ} (hC : IsUnit C) :
    Cᴴ * A * C ≤ Cᴴ * B * C ↔ A ≤ B := by
  constructor
  · intro h
    have hPS : (Cᴴ * (B - A) * C).PosSemidef := by
      have := Matrix.le_iff.mp h
      have hrw : Cᴴ * B * C - Cᴴ * A * C = Cᴴ * (B - A) * C := by noncomm_ring
      rwa [hrw] at this
    exact Matrix.le_iff.mpr
      ((Matrix.IsUnit.posSemidef_star_left_conjugate_iff hC).mp hPS)
  · exact conj_le_conj C

omit [DecidableEq n] in
/-- Congruence by a symmetric matrix, in the form the block geometry uses. -/
theorem conj_le_conj' {A B C : Matrix n n ℝ} (hC : Cᴴ = C) (h : A ≤ B) :
    C * A * C ≤ C * B * C := by
  have := conj_le_conj C h
  rwa [hC] at this

/-! ## The scalar comparison -/

omit [DecidableEq n] in
private theorem inner_toLp (x y : n → ℝ) :
    inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ n) (WithLp.toLp 2 y) = x ⬝ᵥ y := by
  simp [PiLp.inner_apply, dotProduct, RCLike.inner_apply, mul_comm]

omit [DecidableEq n] in
private theorem norm_toLp_sq (x : n → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ ^ 2 = x ⬝ᵥ x := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp]

private theorem toEuclideanCLM_apply' (A : Matrix n n ℝ) (x : n → ℝ) :
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A (WithLp.toLp 2 x)
      = WithLp.toLp 2 (A *ᵥ x) := rfl

omit [DecidableEq n] in
/-- A symmetric matrix moves across the Euclidean pairing. -/
theorem dotProduct_mulVec_symm {A : Matrix n n ℝ} (hA : Aᵀ = A) (x y : n → ℝ) :
    x ⬝ᵥ A *ᵥ y = (A *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]

private theorem le_of_sq_le_sq' {u v : ℝ} (hv : 0 ≤ v) (h : u ^ 2 ≤ v ^ 2) : u ≤ v := by
  have hsq := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg hv] at hsq
  exact le_trans (le_abs_self u) hsq

/-- The quadratic form is controlled by the spectral norm, for every matrix. -/
theorem dotProduct_mulVec_le_norm_mul (A : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ ‖A‖ * (x ⬝ᵥ x) := by
  have hcs : x ⬝ᵥ A *ᵥ x ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ *
        ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ n)‖ := by
    rw [← inner_toLp x (A *ᵥ x)]
    exact real_inner_le_norm _ _
  have hop : ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ n)‖ ≤
      ‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ := by
    rw [← toEuclideanCLM_apply' A x, Matrix.cstar_norm_def]
    exact (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A).le_opNorm _
  have hx : (0 : ℝ) ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ := norm_nonneg _
  calc x ⬝ᵥ A *ᵥ x
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ *
          ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ n)‖ := hcs
    _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ *
          (‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖) :=
        mul_le_mul_of_nonneg_left hop hx
    _ = ‖A‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ ^ 2 := by ring
    _ = ‖A‖ * (x ⬝ᵥ x) := by rw [norm_toLp_sq]

/-- A matrix bounded by `t • I` in the Loewner order has spectral norm at most
`t`, on positive semidefinite data. -/
theorem norm_le_of_le_smul_one {A : Matrix n n ℝ} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 ≤ t) (h : A ≤ t • (1 : Matrix n n ℝ)) : ‖A‖ ≤ t := by
  have hq : ∀ x : n → ℝ, x ⬝ᵥ A *ᵥ x ≤ t * (x ⬝ᵥ x) := by
    intro x
    have hPS := Matrix.posSemidef_iff_dotProduct_mulVec.mp (Matrix.le_iff.mp h)
    have hx := hPS.2 x
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul] at hx
    simp only [star_trivial, smul_eq_mul] at hx
    linarith only [hx]
  -- `A * A ≤ t • A`, because `t • A - A * A = √A (t • I - A) √A`.
  have hsq : ∀ x : n → ℝ, x ⬝ᵥ (A * A) *ᵥ x ≤ t * (x ⬝ᵥ A *ᵥ x) := by
    intro x
    obtain ⟨hBpsd, hBB⟩ := matSqrt_spec hA
    set B : Matrix n n ℝ := matSqrt A with hBdef
    have hBsymm : Bᵀ = B := by
      rw [← conjTranspose_eq_transpose']; exact hBpsd.isHermitian
    have h1 : (B *ᵥ x) ⬝ᵥ A *ᵥ (B *ᵥ x) ≤ t * ((B *ᵥ x) ⬝ᵥ (B *ᵥ x)) := hq (B *ᵥ x)
    have hLHS : (B *ᵥ x) ⬝ᵥ A *ᵥ (B *ᵥ x) = x ⬝ᵥ (A * A) *ᵥ x := by
      have hBAB : B * A * B = A * A := by rw [← hBB]; noncomm_ring
      rw [← dotProduct_mulVec_symm hBsymm x (A *ᵥ (B *ᵥ x)), Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, hBAB]
    have hRHS : (B *ᵥ x) ⬝ᵥ (B *ᵥ x) = x ⬝ᵥ A *ᵥ x := by
      rw [← dotProduct_mulVec_symm hBsymm x (B *ᵥ x), Matrix.mulVec_mulVec, hBB]
    rw [hLHS, hRHS] at h1
    exact h1
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ ht fun y => ?_
  obtain ⟨x, rfl⟩ : ∃ x : n → ℝ, y = WithLp.toLp 2 x := ⟨WithLp.ofLp y, rfl⟩
  rw [toEuclideanCLM_apply']
  refine le_of_sq_le_sq' (mul_nonneg ht (norm_nonneg _)) ?_
  rw [norm_toLp_sq, mul_pow, norm_toLp_sq]
  have hAsymm : Aᵀ = A := by
    rw [← conjTranspose_eq_transpose']; exact hA.isHermitian
  have hexp : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A * A) *ᵥ x := by
    rw [← dotProduct_mulVec_symm hAsymm x (A *ᵥ x), Matrix.mulVec_mulVec]
  have h2 := hsq x
  have h3 := hq x
  have h4 : t * (x ⬝ᵥ A *ᵥ x) ≤ t * (t * (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left h3 ht
  rw [hexp]
  calc x ⬝ᵥ (A * A) *ᵥ x ≤ t * (x ⬝ᵥ A *ᵥ x) := h2
    _ ≤ t * (t * (x ⬝ᵥ x)) := h4
    _ = t ^ 2 * (x ⬝ᵥ x) := by ring

/-- A matrix of spectral norm at most `t` is bounded by `t • I` in the Loewner
order, on positive semidefinite data. -/
theorem le_smul_one_of_norm_le {A : Matrix n n ℝ} (hA : A.PosSemidef) {t : ℝ}
    (h : ‖A‖ ≤ t) : A ≤ t • (1 : Matrix n n ℝ) := by
  have hherm : (t • (1 : Matrix n n ℝ) - A).IsHermitian := by
    refine Matrix.IsHermitian.sub ?_ hA.isHermitian
    simp [Matrix.IsHermitian]
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_)
  have hbound := dotProduct_mulVec_le_norm_mul A x
  have hxx : (0 : ℝ) ≤ x ⬝ᵥ x := by
    rw [← norm_toLp_sq]; positivity
  have hstep : ‖A‖ * (x ⬝ᵥ x) ≤ t * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_right h hxx
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul]
  simp only [star_trivial, smul_eq_mul]
  linarith only [hbound, hstep]

/-- **The spectral norm is the least scalar Loewner bound.**  On positive
semidefinite data `‖A‖` is the reference text's `|A|`. -/
theorem norm_le_iff_le_smul_one {A : Matrix n n ℝ} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 ≤ t) : ‖A‖ ≤ t ↔ A ≤ t • (1 : Matrix n n ℝ) :=
  ⟨fun h => le_smul_one_of_norm_le hA h, fun h => norm_le_of_le_smul_one hA ht h⟩

/-- A positive semidefinite matrix is bounded by its own spectral norm. -/
theorem le_norm_smul_one {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A ≤ ‖A‖ • (1 : Matrix n n ℝ) :=
  le_smul_one_of_norm_le hA le_rfl

/-- The spectral norm is monotone for the Loewner order on positive semidefinite
data. -/
theorem norm_le_norm_of_le {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (h : A ≤ B) : ‖A‖ ≤ ‖B‖ :=
  norm_le_of_le_smul_one hA (norm_nonneg B) (h.trans (le_norm_smul_one hB))

omit [Fintype n] [DecidableEq n] in
/-- A matrix dominating a positive definite matrix is positive definite. -/
theorem posDef_of_posDef_le [Finite n] {A B : Matrix n n ℝ} (hA : A.PosDef) (hAB : A ≤ B) :
    B.PosDef := by
  classical
  let : Fintype n := Fintype.ofFinite n
  have hPS : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · have hsum : B = A + (B - A) := by abel
    rw [hsum]
    exact hA.isHermitian.add hPS.isHermitian
  · intro x hx
    have h1 : 0 < star x ⬝ᵥ A *ᵥ x := hA.dotProduct_mulVec_pos hx
    have h2 : 0 ≤ star x ⬝ᵥ (B - A) *ᵥ x := hPS.dotProduct_mulVec_nonneg x
    rw [Matrix.sub_mulVec, dotProduct_sub] at h2
    linarith only [h1, h2]

/-! ## The square root as a unit -/

/-- `matSqrt` agrees with the C⋆ functional-calculus square root on positive
semidefinite data, so the two APIs may be mixed freely. -/
theorem matSqrt_eq_cfcSqrt {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    matSqrt A = CFC.sqrt A :=
  matSqrt_eq hA (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))
    (CFC.sqrt_mul_sqrt_self A (ha := hA.nonneg))

/-- The determinant of a positive definite matrix is a unit. -/
theorem isUnit_det_of_posDef {A : Matrix n n ℝ} (hA : A.PosDef) : IsUnit A.det :=
  (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit

/-- A positive semidefinite unit is positive definite. -/
theorem posDef_of_posSemidef_of_isUnit {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (hu : IsUnit A) : A.PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp ⟨hA.nonneg, hu⟩

/-- The square root of a positive definite matrix is a unit. -/
theorem isUnit_matSqrt {A : Matrix n n ℝ} (hA : A.PosDef) : IsUnit (matSqrt A) := by
  rw [matSqrt_eq_cfcSqrt hA.posSemidef]
  exact (CFC.isUnit_sqrt_iff A (ha := hA.posSemidef.nonneg)).mpr hA.isUnit

/-- The square root of a positive definite matrix is positive definite. -/
theorem posDef_matSqrt {A : Matrix n n ℝ} (hA : A.PosDef) : (matSqrt A).PosDef :=
  posDef_of_posSemidef_of_isUnit (matSqrt_spec hA.posSemidef).1 (isUnit_matSqrt hA)

/-- The square root of the inverse is the inverse of the square root. -/
theorem matSqrt_inv {A : Matrix n n ℝ} (hA : A.PosDef) :
    matSqrt A⁻¹ = (matSqrt A)⁻¹ := by
  rw [matSqrt_eq_cfcSqrt hA.inv.posSemidef, matSqrt_eq_cfcSqrt hA.posSemidef,
    hA.posSemidef.inv_sqrt]

/-- The inverse square root of a positive definite matrix is symmetric. -/
theorem transpose_matSqrt_inv {A : Matrix n n ℝ} (hA : A.PosDef) :
    (matSqrt A⁻¹)ᵀ = matSqrt A⁻¹ := by
  rw [← conjTranspose_eq_transpose']
  exact (matSqrt_spec hA.inv.posSemidef).1.isHermitian

/-- **The inverse square root normalizes.**  Conjugating a positive definite
matrix by its own inverse square root gives the identity; this is the
substitution the reference text writes as `A^{-1/2} A A^{-1/2} = I`. -/
theorem matSqrt_inv_conj {A : Matrix n n ℝ} (hA : A.PosDef) :
    matSqrt A⁻¹ * A * matSqrt A⁻¹ = 1 := by
  have hS := (matSqrt_spec hA.posSemidef).2
  have hu : IsUnit (matSqrt A).det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hA)
  rw [matSqrt_inv hA]
  calc (matSqrt A)⁻¹ * A * (matSqrt A)⁻¹
      = (matSqrt A)⁻¹ * (matSqrt A * matSqrt A) * (matSqrt A)⁻¹ := by rw [hS]
    _ = ((matSqrt A)⁻¹ * matSqrt A) * (matSqrt A * (matSqrt A)⁻¹) := by noncomm_ring
    _ = 1 := by
        rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/-! ## Order reversal under inversion -/

/-- `I ≤ Z⁻¹` whenever `Z` is positive definite and `Z ≤ I`. -/
private theorem one_le_inv_of_le_one {Z : Matrix n n ℝ} (hZ : Z.PosDef)
    (h : Z ≤ 1) : 1 ≤ Z⁻¹ := by
  have hRsymm : (matSqrt Z⁻¹)ᴴ = matSqrt Z⁻¹ := (matSqrt_spec hZ.inv.posSemidef).1.isHermitian
  have hcong := conj_le_conj' hRsymm h
  rw [matSqrt_inv_conj hZ, Matrix.mul_one, (matSqrt_spec hZ.inv.posSemidef).2] at hcong
  exact hcong

/-- **Inversion reverses the Loewner order.** -/
theorem inv_le_inv_of_le {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (h : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  have hdetA : IsUnit A.det := isUnit_det_of_posDef hA
  have hdetB : IsUnit B.det := isUnit_det_of_posDef hB
  set R : Matrix n n ℝ := matSqrt B⁻¹ with hRdef
  have hRsymm : Rᴴ = R := (matSqrt_spec hB.inv.posSemidef).1.isHermitian
  have hRR : R * R = B⁻¹ := (matSqrt_spec hB.inv.posSemidef).2
  have hRu : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hB.inv)
  have hRBR : R * B * R = 1 := matSqrt_inv_conj hB
  have hZ : (R * A * R).PosDef := by
    have hcm := hA.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit (isUnit_matSqrt hB.inv))
    rwa [hRsymm] at hcm
  have hle1 : R * A * R ≤ 1 := by
    have hc := conj_le_conj' hRsymm h
    rwa [hRBR] at hc
  have hinv : 1 ≤ (R * A * R)⁻¹ := one_le_inv_of_le_one hZ hle1
  have hform : (R * A * R)⁻¹ = R⁻¹ * A⁻¹ * R⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    noncomm_ring
  have hRinvsymm : (R⁻¹)ᴴ = R⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hRsymm]
  have hRinv2 : R⁻¹ * R⁻¹ = B := by
    rw [← Matrix.mul_inv_rev, hRR, Matrix.nonsing_inv_nonsing_inv _ hdetB]
  have hcong := conj_le_conj' hRinvsymm hinv
  rw [hform] at hcong
  have hleft : R⁻¹ * (R⁻¹ * A⁻¹ * R⁻¹) * R⁻¹ = B * A⁻¹ * B := by
    calc R⁻¹ * (R⁻¹ * A⁻¹ * R⁻¹) * R⁻¹
        = (R⁻¹ * R⁻¹) * A⁻¹ * (R⁻¹ * R⁻¹) := by noncomm_ring
      _ = B * A⁻¹ * B := by rw [hRinv2]
  have hright : R⁻¹ * 1 * R⁻¹ = B := by rw [Matrix.mul_one, hRinv2]
  rw [hleft, hright] at hcong
  have hBinvsymm : (B⁻¹)ᴴ = B⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hB.isHermitian]
  have hfinal := conj_le_conj' hBinvsymm hcong
  have e1 : B⁻¹ * B * B⁻¹ = B⁻¹ := by
    rw [Matrix.nonsing_inv_mul _ hdetB, Matrix.one_mul]
  have e2 : B⁻¹ * (B * A⁻¹ * B) * B⁻¹ = A⁻¹ := by
    calc B⁻¹ * (B * A⁻¹ * B) * B⁻¹
        = (B⁻¹ * B) * A⁻¹ * (B * B⁻¹) := by noncomm_ring
      _ = A⁻¹ := by
          rw [Matrix.nonsing_inv_mul _ hdetB, Matrix.mul_nonsing_inv _ hdetB,
            Matrix.one_mul, Matrix.mul_one]
  rwa [e1, e2] at hfinal

end

end HighContrast
end HCPolySupport
