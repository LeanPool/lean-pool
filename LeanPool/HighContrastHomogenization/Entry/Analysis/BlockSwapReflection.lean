/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Contrast
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact
public import LeanPool.HighContrastHomogenization.Setup.Attainment
public import LeanPool.HighContrastHomogenization.Setup.BlockAlgebra
public import LeanPool.HighContrastHomogenization.Setup.SpectralBound
public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormFoundations
public import LeanPool.HighContrastHomogenization.Entry.Multiscale.DriftAdvance

/-!
# High-contrast homogenization: Entry.Analysis.BlockSwapReflection

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The block swap, the skew shear and the Schur factorization

The deterministic block algebra the reference-block comparison of
`HCPoly/Entry/Analysis/ReferenceComparison.lean` runs on; the source argument is Lemma
`l.bfE.bounds` of the companion paper HC, near `e.reference.aspect.ratio`.

* The swap involution `blockSwap d` is symmetric and squares to the identity on the full `2d`
  carrier, and conjugation by it is the block reflection.  Conjugating the inverse of a
  positive definite block therefore leaves it positive definite, sends the lower-right corner
  to `(schurSigma E)⁻¹`, and inverts the determinant.
* The skew shear `blockG h` is invertible with inverse `blockG (-h)`; congruence by it carries
  a symmetric block with positive definite quadratic form to the skew-corrected form in the
  upper-left corner, preserves positive definiteness, and commutes with the swap conjugation
  of the inverse up to the shear of the negated skew part.
* The Schur factorization of a symmetric positive definite block along `schurSkew E`, with the
  positive definiteness of `schurSigma E`.

Two order dictionaries are proved with them: `toFullBlockMat A ≤ toFullBlockMat B` is
`BlockMatLoewnerLE A B` on Hermitian carriers, and `A ≤ B` is `MatLoewnerLE A B` on Hermitian
matrices.  No probability law, quantitative ellipticity constant or annealed premise enters.
-/

open HCPolySupport.HighContrast (IsSkewMat aspectRatio bigLambdaRef blockContrast
  blockContrast_le blockScale blockVecDot_inr exists_isSkewMat_bigLambdaRef_eq
  exists_isSkewMat_blockContrast_eq isUnit_det_lowerRight lambdaRef matLoewnerLE_smul_iff_conj
  matLoewnerLE_specBound_smul_one matSqrt matSqrt_lowerRight_spec posDef_lowerRight refContrast
  schurSigma schurSigmaStar schurSkew skewCorrectedForm specBound)
namespace HCPolySupport.HighContrast.Analysis

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section
variable {d : ℕ}

/-- A real scalar multiple of a Hermitian matrix is Hermitian. -/
theorem isHermitian_smul {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ}
    (hM : M.IsHermitian) (c : ℝ) : (c • M).IsHermitian := by
  change (c • M)ᴴ = c • M
  rw [Matrix.conjTranspose_smul, star_trivial, hM.eq]

private theorem full_eq (E : BlockMat d) :
    toFullBlockMat E = Matrix.fromBlocks E.upperLeft E.upperRight E.lowerLeft E.lowerRight := by
  ext (i | i) (j | j) <;> rfl

/-- A symmetric block whose block quadratic form is positive definite is positive definite on the
full `2d` carrier. -/
theorem posDef_toFullBlockMat_of_blockPosDef {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) : (toFullBlockMat E).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ((toFullBlockMat_isHermitian_iff E).2 hs) ?_
  intro x hx
  have hn : ofFullBlockVec x ≠ 0 := by
    intro h
    apply hx
    have hz := congrArg toFullBlockVec h
    rw [toFullBlockVec_ofFullBlockVec] at hz
    funext i
    have hi := congrFun hz i
    cases i <;> simpa [toFullBlockVec] using hi
  simpa only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
    toFullBlockVec_ofFullBlockVec, star_trivial] using hp (ofFullBlockVec x) hn

/-- On Hermitian full carriers the matrix order is the block Loewner order. -/
theorem toFullBlockMat_le_iff {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian) :
    toFullBlockMat A ≤ toFullBlockMat B ↔ BlockMatLoewnerLE A B := by
  constructor
  · intro h X
    have hn := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg (toFullBlockVec X)
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hn
    have heA := dotProduct_toFullBlockVec X (blockMatVecMul A X)
    have heB := dotProduct_toFullBlockVec X (blockMatVecMul B X)
    rw [toFullBlockVec_blockMatVecMul] at heA heB
    rw [heA, heB] at hn
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp hn) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · intro h
    apply Matrix.le_iff.mpr
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
    intro x
    have hx := h (ofFullBlockVec x)
    simp only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockVec_ofFullBlockVec] at hx
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    linarith only [hx]

/-- Inversion is antitone on positive definite matrices. -/
theorem inv_le_inv_of_posDef_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) (hle : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  have hD : (A⁻¹ - B⁻¹).IsHermitian := hA.inv.isHermitian.sub hB.inv.isHermitian
  have h₁ := hA.posSemidef.conjTranspose_mul_mul_same (A⁻¹ - B⁻¹)
  have h₂ := (Matrix.le_iff.mp hle).conjTranspose_mul_mul_same B⁻¹
  rw [hD.eq] at h₁
  rw [hB.inv.isHermitian.eq] at h₂
  apply Matrix.le_iff.mpr
  (convert h₁.add h₂ using 1; try rfl)
  have hAiA := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hAAi := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hBiB := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit)
  simp only [mul_sub, sub_mul, hAiA, hBiB, one_mul]
  rw [mul_assoc B⁻¹ A A⁻¹, hAAi, mul_one]
  abel

/-- The reflection block is symmetric. -/
theorem isSymmetricBlockMat_blockSwap (d : ℕ) : IsSymmetricBlockMat (blockSwap d) := by
  intro a b
  cases a <;> cases b <;>
    simp [blockSwap, Book.Ch02.blockR, blockMatEntry, Matrix.one_apply, eq_comm]

private theorem swap_full (d : ℕ) :
    toFullBlockMat (blockSwap d) = Matrix.fromBlocks (0 : Mat d) 1 1 0 := by
  rw [full_eq]
  rfl

/-- The reflection block is an involution. -/
theorem toFullBlockMat_blockSwap_mul_self (d : ℕ) :
    toFullBlockMat (blockSwap d) * toFullBlockMat (blockSwap d) = 1 := by
  rw [swap_full, Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, one_mul, zero_add, add_zero, Matrix.fromBlocks_one]

/-- Literal reflection products agree with the CG block reflection. -/
theorem swapConj_eq_blockReflect (F : BlockMat d) :
    ofFullBlockMat (toFullBlockMat (blockSwap d) * toFullBlockMat F *
      toFullBlockMat (blockSwap d)) = blockReflect F := by
  rw [swap_full, full_eq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
  rfl

/-- The inverse instance of the reflection identity. -/
theorem swapConj_inv_eq_blockReflect (F : BlockMat d) :
    ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ *
      toFullBlockMat (blockSwap d)) = blockReflect (ofFullBlockMat (toFullBlockMat F)⁻¹) := by
  simpa only [toFullBlockMat_ofFullBlockMat] using
    swapConj_eq_blockReflect (ofFullBlockMat (toFullBlockMat F)⁻¹)

/-- Conjugation by the swap exchanges the two diagonal corners of a `fromBlocks` matrix and the
two off-diagonal corners. -/
theorem blockSwap_conj_fromBlocks (A B C D : Mat d) :
    toFullBlockMat (blockSwap d) * Matrix.fromBlocks A B C D *
      toFullBlockMat (blockSwap d) = Matrix.fromBlocks D C B A := by
  have h := congrArg toFullBlockMat
    (swapConj_eq_blockReflect (ofFullBlockMat (Matrix.fromBlocks A B C D)))
  calc
    _ = toFullBlockMat (blockReflect (ofFullBlockMat (Matrix.fromBlocks A B C D))) := by
      simpa only [toFullBlockMat_ofFullBlockMat] using h
    _ = _ := by ext (i | i) (j | j) <;> rfl

/-- The swap involution is Hermitian on the full `2d` carrier. -/
theorem isHermitian_toFullBlockMat_blockSwap (d : ℕ) : (toFullBlockMat (blockSwap d)).IsHermitian :=
  (toFullBlockMat_isHermitian_iff _).2 (isSymmetricBlockMat_blockSwap d)

/-- The adjoint reference block is positive definite in the full matrix carrier. -/
theorem swapConj_posDef {F : BlockMat d} (hp : (toFullBlockMat F).PosDef) :
    (toFullBlockMat (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d)))).PosDef := by
  rw [toFullBlockMat_ofFullBlockMat]
  have hu : IsUnit (toFullBlockMat (blockSwap d)) :=
    (Matrix.isUnit_iff_isUnit_det _).2
      (Matrix.isUnit_det_of_right_inverse (toFullBlockMat_blockSwap_mul_self d))
  simpa only [(isHermitian_toFullBlockMat_blockSwap d).eq] using
    (Matrix.posDef_inv_iff.2 hp).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hu)

private theorem shear_full (h : Mat d) :
    toFullBlockMat (Book.Ch02.blockG h) = Matrix.fromBlocks (1 : Mat d) 0 h 1 := by
  rw [full_eq]
  rfl

private theorem shear_mul_neg (h : Mat d) :
    toFullBlockMat (Book.Ch02.blockG h) * toFullBlockMat (Book.Ch02.blockG (-h)) = 1 := by
  rw [shear_full, shear_full, Matrix.fromBlocks_multiply]
  simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add,
    add_neg_cancel, Matrix.fromBlocks_one]

/-- The skew shear is invertible on the full `2d` carrier. -/
theorem isUnit_toFullBlockMat_blockG (h : Mat d) : IsUnit (toFullBlockMat (Book.Ch02.blockG h)) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (shear_mul_neg h))

private theorem shear_inv (h : Mat d) :
    (toFullBlockMat (Book.Ch02.blockG h))⁻¹ = toFullBlockMat (Book.Ch02.blockG (-h)) :=
  Matrix.inv_eq_right_inv (shear_mul_neg h)

/-- The skew shear commutes with the swap conjugation of the inverse, up to the shear of the
negated skew part. -/
theorem blockG_conj_swapConj_eq (E : BlockMat d) (h : Mat d) (hh : IsSkewMat h) :
    (toFullBlockMat (Book.Ch02.blockG h))ᴴ *
      (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d)) *
      toFullBlockMat (Book.Ch02.blockG h) =
    toFullBlockMat (blockSwap d) *
      ((toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat E *
        toFullBlockMat (Book.Ch02.blockG h))⁻¹ * toFullBlockMat (blockSwap d) := by
  have hleft : (toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat (blockSwap d) =
      toFullBlockMat (blockSwap d) * (toFullBlockMat (Book.Ch02.blockG h))⁻¹ := by
    rw [shear_inv]
    rw [shear_full, shear_full, swap_full, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    have hh' : hᴴ = -h := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using! hh
    simp only [hh', Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add]
  have hright := congrArg Matrix.conjTranspose hleft
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (isHermitian_toFullBlockMat_blockSwap d).eq, Matrix.conjTranspose_nonsing_inv] at hright
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc
    _ = ((toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat (blockSwap d)) *
        (toFullBlockMat E)⁻¹ * (toFullBlockMat (blockSwap d) *
          toFullBlockMat (Book.Ch02.blockG h)) := by simp only [mul_assoc]
    _ = _ := by rw [hleft, hright]; simp only [mul_assoc]

private theorem schur_cancel {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) :
    E.lowerRight * schurSkew E = -E.lowerLeft ∧
      (schurSkew E)ᴴ * E.lowerRight = -E.upperRight := by
  have hD : E.lowerRightᴴ = E.lowerRight := (posDef_lowerRight hs hp).isHermitian.eq
  have hC : E.lowerLeftᴴ = E.upperRight := by
    ext i j
    exact hs (Sum.inr j) (Sum.inl i)
  have hk : E.lowerRight * schurSkew E = -E.lowerLeft := by
    rw [schurSkew, mul_neg, ← mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_det_lowerRight hp), one_mul]
  have hk' : (schurSkew E)ᴴ * E.lowerRight = -E.upperRight := by
    have hkt := congrArg Matrix.conjTranspose hk
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, hD, hC] using hkt
  exact ⟨hk, hk'⟩

private theorem skewCorrectedForm_eq {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) :
    skewCorrectedForm E h = E.upperLeft + E.upperRight * h +
      hᴴ * E.lowerLeft + hᴴ * E.lowerRight * h := by
  obtain ⟨hk, hk'⟩ := schur_cancel hs hp
  change E.upperLeft - (schurSkew E)ᵀ * E.lowerRight * schurSkew E +
    (schurSkew E - h)ᵀ * E.lowerRight * (schurSkew E - h) = _
  simp only [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.conjTranspose_sub,
    mul_sub, sub_mul]
  rw [hk', mul_assoc hᴴ E.lowerRight, hk]
  simp only [neg_mul, mul_neg]
  abel

/-- Congruence by the skew shear `blockG h` puts the skew-corrected form in the upper-left corner.
-/
theorem blockG_conj_eq_fromBlocks {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) :
    (toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat E *
      toFullBlockMat (Book.Ch02.blockG h) =
    Matrix.fromBlocks (skewCorrectedForm E h) (E.upperRight + hᴴ * E.lowerRight)
      (E.lowerLeft + E.lowerRight * h) E.lowerRight := by
  rw [shear_full, full_eq, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, skewCorrectedForm_eq hs hp]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_mul]
  congr 1
  abel

/-- Congruence by the skew shear preserves positive definiteness. -/
theorem posDef_blockG_conj {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) :
    ((toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat E *
      toFullBlockMat (Book.Ch02.blockG h)).PosDef :=
  (posDef_toFullBlockMat_of_blockPosDef hs hp).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit (isUnit_toFullBlockMat_blockG h))

/-- On Hermitian matrices the matrix order is the Loewner order read on quadratic forms. -/
theorem matrix_le_iff_matLoewnerLE {A B : Mat d} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ≤ B ↔ MatLoewnerLE A B := by
  constructor
  · intro h x
    have ht := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at ht
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp ht) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · intro h
    refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_)
    intro x
    have hx := h x
    change 1 / 2 * (x ⬝ᵥ A.mulVec x) ≤ 1 / 2 * (x ⬝ᵥ B.mulVec x) at hx
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    linarith only [hx]

private theorem upper_pos {A B C D : Mat d} (hp : (Matrix.fromBlocks A B C D).PosDef) :
    A.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hp.isHermitian.submatrix Sum.inl) ?_
  intro x hx
  have hx' : Sum.elim x (0 : Vec d) ≠ 0 := by
    intro he
    exact hx (congrArg (fun f => f ∘ Sum.inl) he)
  have h := hp.dotProduct_mulVec_pos hx'
  simpa only [star_trivial, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, Matrix.mulVec_zero, add_zero, sumElim_dotProduct_sumElim,
    zero_dotProduct] using h

/-- The skew-corrected form of a symmetric positive definite block is positive definite. -/
theorem posDef_skewCorrectedForm {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) : (skewCorrectedForm E h).PosDef := by
  have he := posDef_blockG_conj hs hp h
  rw [blockG_conj_eq_fromBlocks hs hp] at he
  exact upper_pos he

private theorem schur_factorization {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) :
    toFullBlockMat E = (toFullBlockMat (Book.Ch02.blockG (-schurSkew E)))ᴴ *
      Matrix.fromBlocks (schurSigma E) 0 0 E.lowerRight *
        toFullBlockMat (Book.Ch02.blockG (-schurSkew E)) := by
  obtain ⟨hk, hk'⟩ := schur_cancel hs hp
  rw [full_eq, shear_full, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_neg, one_mul, mul_one, zero_mul, mul_zero,
    add_zero, zero_add, neg_mul, mul_neg, neg_neg, hk, hk']
  congr 1
  change E.upperLeft = E.upperLeft - (schurSkew E)ᵀ * E.lowerRight * schurSkew E +
    -(E.upperRight * schurSkew E)
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial, hk']
  simp only [neg_mul]
  abel

/-- The Schur complement `schurSigma E` of a symmetric positive definite block is positive
definite. -/
theorem posDef_schurSigma {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) : (schurSigma E).PosDef := by
  simpa only [skewCorrectedForm, sub_self, matTranspose, Matrix.transpose_zero, zero_mul, add_zero]
    using posDef_skewCorrectedForm hs hp (schurSkew E)

private theorem diagonal_inv {A D : Mat d} (hA : A.PosDef) (hD : D.PosDef) :
    (Matrix.fromBlocks A 0 0 D)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 D⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, add_zero, zero_add,
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit),
    Matrix.mul_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det _).mp hD.isUnit),
    Matrix.fromBlocks_one]

/-- The lower-right block of the swap-conjugated inverse is the inverse Schur complement
`(schurSigma E)⁻¹`.  This is the Schur factorization read off the reflected inverse. -/
theorem swapConj_lowerRight {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) :
    (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
      toFullBlockMat (blockSwap d))).lowerRight = (schurSigma E)⁻¹ := by
  rw [swapConj_inv_eq_blockReflect, blockReflect_lowerRight]
  rw [schur_factorization hs hp, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    ← Matrix.conjTranspose_nonsing_inv, shear_inv, neg_neg,
    diagonal_inv (posDef_schurSigma hs hp) (posDef_lowerRight hs hp)]
  rw [shear_full, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, one_mul, mul_one,
    zero_mul, mul_zero, add_zero, zero_add]
  rfl

/-- Reflection preserves the inverse determinant; no normalized determinant convention is used. -/
theorem det_swapConj (E : BlockMat d) :
    (toFullBlockMat (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d)))).det = (toFullBlockMat E).det⁻¹ := by
  have hR := congrArg Matrix.det (toFullBlockMat_blockSwap_mul_self d)
  rw [Matrix.det_mul, Matrix.det_one] at hR
  simp only [toFullBlockMat_ofFullBlockMat, Matrix.det_mul, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv]
  calc
    _ = ((toFullBlockMat (blockSwap d)).det * (toFullBlockMat (blockSwap d)).det) *
      (toFullBlockMat E).det⁻¹ := by ring
    _ = _ := by rw [hR, one_mul]
end
end HCPolySupport.HighContrast.Analysis
