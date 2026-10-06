/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.FiniteRun

/-!
# High-contrast homogenization: Entry.Multiscale.Global.DeterminantBounds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Determinant bounds for the adapted mean

The determinant bounds of the entry generation, serving `p.global.selection`: the reference
comparison `𝐄 ≤ 6Π · 𝐑𝐄⁻¹𝐑`, the resulting upper bound `blockLogDet 𝐀 ≤ d log (24Π)` under
the initialization sandwich `𝐀 ≤ 2𝐄`, and the symmetry and positivity of the adapted mean.
-/

open HCPolySupport.HighContrast (CoeffSpace IsSkewMat adaptedMean aspectRatio aspectRatio_nonneg
  bigLambdaRef blockLogDet blockScale exists_isSkewMat_bigLambdaRef_eq isUnit_det_lowerRight
  lambdaRef matLoewnerLE_specBound_smul_one matSqrt posDef_lowerRight schurSkew skewCorrectedForm
  specBound)
open HCPolySupport.HighContrast (aspectRatio_nonneg)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! Local reconstructions of the `private` helpers of
`HCPoly/Entry/Analysis/ReferenceComparison.lean`
and `HCPoly/Entry/Analysis/InverseJensen.lean`, needed here because those declarations are private
there. -/
section RCHelpers

open Matrix
open scoped MatrixOrder

/-- Local copy of `Analysis.hermitian_smul` (private there): scalar multiples of a Hermitian
real matrix are Hermitian. -/
private theorem rc_hermitian_smul {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (c : ℝ) :
    (c • M).IsHermitian := by
  change (c • M)ᴴ = c • M
  rw [Matrix.conjTranspose_smul, star_trivial, hM.eq]

/-- Local copy of `Analysis.full_eq` (private there). -/
private theorem rc_full_eq {d : ℕ} (E : BlockMat d) :
    toFullBlockMat E = Matrix.fromBlocks E.upperLeft E.upperRight E.lowerLeft E.lowerRight := by
  ext (i | i) (j | j) <;> rfl

/-- Local copy of `Analysis.swap_full` (private there). -/
private theorem rc_swap_full (d : ℕ) :
    toFullBlockMat (blockSwap d) = Matrix.fromBlocks (0 : Mat d) 1 1 0 := by
  rw [rc_full_eq]
  rfl

/-- Local copy of `Analysis.scalar_diag_eq` (private there). -/
private theorem rc_scalar_diag_eq {d : ℕ} (a b : ℝ) :
    Matrix.fromBlocks (a • (1 : Mat d)) 0 0 (b • (1 : Mat d)) =
      Matrix.diagonal (Sum.elim (fun _ : Fin d => a) (fun _ : Fin d => b)) := by
  ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply]

/-- Local copy of `Analysis.scalar_diag_pos` (private there). -/
private theorem rc_scalar_diag_pos {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Matrix.fromBlocks (a • (1 : Mat d)) 0 0 (b • (1 : Mat d))).PosDef := by
  rw [rc_scalar_diag_eq]
  exact Matrix.PosDef.diagonal (fun i => by cases i <;> assumption)

/-- Local copy of `Analysis.scalar_diag_inv` (private there). -/
private theorem rc_scalar_diag_inv {d : ℕ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Matrix.fromBlocks (a • (1 : Mat d)) 0 0 (b • (1 : Mat d)))⁻¹ =
      Matrix.fromBlocks (a⁻¹ • (1 : Mat d)) 0 0 (b⁻¹ • (1 : Mat d)) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb,
    one_smul, one_mul, Matrix.fromBlocks_one]

/-- Local copy of `Analysis.swap_fromBlocks` (private there), rebuilt from the public
`Analysis.swapConj_eq_blockReflect`. -/
private theorem rc_swap_fromBlocks {d : ℕ} (A B C D : Mat d) :
    toFullBlockMat (blockSwap d) * Matrix.fromBlocks A B C D *
      toFullBlockMat (blockSwap d) = Matrix.fromBlocks D C B A := by
  have h := congrArg toFullBlockMat
    (Analysis.swapConj_eq_blockReflect (ofFullBlockMat (Matrix.fromBlocks A B C D)))
  calc
    _ = toFullBlockMat (blockReflect (ofFullBlockMat (Matrix.fromBlocks A B C D))) := by
      simpa only [toFullBlockMat_ofFullBlockMat] using h
    _ = _ := by ext (i | i) (j | j) <;> rfl

/-- Local copy of `Analysis.two_diag_bound` (private there). -/
private theorem rc_two_diag_bound {d : ℕ} {A B C D : Mat d}
    (hp : (Matrix.fromBlocks A B C D).PosSemidef) {a b : ℝ}
    (ha : A ≤ a • (1 : Mat d)) (hb : D ≤ b • (1 : Mat d)) :
    Matrix.fromBlocks A B C D ≤
      Matrix.fromBlocks ((2 * a) • (1 : Mat d)) 0 0 ((2 * b) • (1 : Mat d)) := by
  have hdiag : (Matrix.fromBlocks ((2 * a) • (1 : Mat d)) 0 0
      ((2 * b) • (1 : Mat d))).IsHermitian := by
    rw [rc_scalar_diag_eq]
    exact Matrix.isHermitian_diagonal _
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hdiag.sub hp.isHermitian) ?_)
  intro x
  have h0 := hp.dotProduct_mulVec_nonneg (Sum.elim (x ∘ Sum.inl) (-(x ∘ Sum.inr)))
  have h1 := (Matrix.le_iff.mp ha).dotProduct_mulVec_nonneg (x ∘ Sum.inl)
  have h2 := (Matrix.le_iff.mp hb).dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h1 h2
  rw [← Sum.elim_comp_inl_inr x]
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.fromBlocks_mulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_neg, Matrix.zero_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, zero_add, add_zero,
    sumElim_dotProduct_sumElim, dotProduct_add, dotProduct_sub,
    dotProduct_neg, neg_dotProduct, dotProduct_smul, smul_eq_mul] at h0 ⊢
  linarith only [h0, h1, h2]

/-- Local copy of `Analysis.four_product_bound` (private there), rebuilt from the public
`HCPolySupport.HighContrast.inv_le_inv_of_le` / `HCPolySupport.HighContrast.conj_le_conj'` toolkit
in place of the file-private
`inv_le_inv_of_le` / `star_left_conjugate_le_conjugate`. -/
private theorem rc_four_product_bound {d : ℕ} {A B C D : Mat d}
    (hp : (Matrix.fromBlocks A B C D).PosDef) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : A ≤ a • (1 : Mat d)) (hD : D ≤ b • (1 : Mat d)) :
    Matrix.fromBlocks A B C D ≤ (4 * a * b) •
      (toFullBlockMat (blockSwap d) * (Matrix.fromBlocks A B C D)⁻¹ *
        toFullBlockMat (blockSwap d)) := by
  have ha2 : 0 < 2 * a := mul_pos (by norm_num) ha
  have hb2 : 0 < 2 * b := mul_pos (by norm_num) hb
  have hu := rc_two_diag_bound hp.posSemidef hA hD
  have hi := HCPolySupport.HighContrast.inv_le_inv_of_le hp (rc_scalar_diag_pos ha2 hb2) hu
  have hr := HCPolySupport.HighContrast.conj_le_conj' (BlockGeometricMean.swapFullHerm d) hi
  have heq : (4 * a * b) • (toFullBlockMat (blockSwap d) *
      (Matrix.fromBlocks ((2 * a) • (1 : Mat d)) 0 0 ((2 * b) • (1 : Mat d)))⁻¹ *
        toFullBlockMat (blockSwap d)) =
      Matrix.fromBlocks ((2 * a) • (1 : Mat d)) 0 0 ((2 * b) • (1 : Mat d)) := by
    rw [rc_scalar_diag_inv ha2.ne' hb2.ne', rc_swap_fromBlocks]
    simp only [Matrix.fromBlocks_smul, smul_zero, smul_smul]
    congr 2 <;> field_simp [ha.ne', hb.ne'] <;> ring
  have hscale := smul_le_smul_of_nonneg_left hr (by positivity : 0 ≤ 4 * a * b)
  rw [heq] at hscale
  exact hu.trans hscale

/-- Local copy of `Analysis.schur_cancel` (private there). -/
private theorem rc_schur_cancel {d : ℕ} {E : BlockMat d} (hs : IsSymmetricBlockMat E)
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

/-- Local copy of `Analysis.skewCorrectedForm_eq` (private there). -/
private theorem rc_skewCorrectedForm_eq {d : ℕ} {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) :
    skewCorrectedForm E h = E.upperLeft + E.upperRight * h +
      hᴴ * E.lowerLeft + hᴴ * E.lowerRight * h := by
  obtain ⟨hk, hk'⟩ := rc_schur_cancel hs hp
  change E.upperLeft - (schurSkew E)ᵀ * E.lowerRight * schurSkew E +
    (schurSkew E - h)ᵀ * E.lowerRight * (schurSkew E - h) = _
  simp only [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.conjTranspose_sub,
    mul_sub, sub_mul]
  rw [hk', mul_assoc hᴴ E.lowerRight, hk]
  simp only [neg_mul, mul_neg]
  abel

/-- Local copy of `Analysis.shear_full` (private there). -/
private theorem rc_shear_full {d : ℕ} (h : Mat d) :
    toFullBlockMat (Book.Ch02.blockG h) = Matrix.fromBlocks (1 : Mat d) 0 h 1 := by
  rw [rc_full_eq]
  rfl

/-- Local copy of `Analysis.shear_mul_neg` (private there). -/
private theorem rc_shear_mul_neg {d : ℕ} (h : Mat d) :
    toFullBlockMat (Book.Ch02.blockG h) * toFullBlockMat (Book.Ch02.blockG (-h)) = 1 := by
  rw [rc_shear_full, rc_shear_full, Matrix.fromBlocks_multiply]
  simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add,
    add_neg_cancel, Matrix.fromBlocks_one]

/-- Local copy of `Analysis.shear_unit` (private there). -/
private theorem rc_shear_unit {d : ℕ} (h : Mat d) :
    IsUnit (toFullBlockMat (Book.Ch02.blockG h)) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (rc_shear_mul_neg h))

/-- Local copy of `Analysis.shear_inv` (private there). -/
private theorem rc_shear_inv {d : ℕ} (h : Mat d) :
    (toFullBlockMat (Book.Ch02.blockG h))⁻¹ = toFullBlockMat (Book.Ch02.blockG (-h)) :=
  Matrix.inv_eq_right_inv (rc_shear_mul_neg h)

/-- Local copy of `Analysis.shear_swapConj` (private there). -/
private theorem rc_shear_swapConj {d : ℕ} (E : BlockMat d) (h : Mat d) (hh : IsSkewMat h) :
    (toFullBlockMat (Book.Ch02.blockG h))ᴴ *
      (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d)) *
      toFullBlockMat (Book.Ch02.blockG h) =
    toFullBlockMat (blockSwap d) *
      ((toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat E *
        toFullBlockMat (Book.Ch02.blockG h))⁻¹ * toFullBlockMat (blockSwap d) := by
  have hleft : (toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat (blockSwap d) =
      toFullBlockMat (blockSwap d) * (toFullBlockMat (Book.Ch02.blockG h))⁻¹ := by
    rw [rc_shear_inv]
    rw [rc_shear_full, rc_shear_full, rc_swap_full, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    have hh' : hᴴ = -h := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using! hh
    simp only [hh', Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add]
  have hright := congrArg Matrix.conjTranspose hleft
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    BlockGeometricMean.swapFullHerm d, Matrix.conjTranspose_nonsing_inv] at hright
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc
    _ = ((toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat (blockSwap d)) *
        (toFullBlockMat E)⁻¹ * (toFullBlockMat (blockSwap d) *
          toFullBlockMat (Book.Ch02.blockG h)) := by simp only [mul_assoc]
    _ = _ := by rw [hleft, hright]; simp only [mul_assoc]

/-- Local copy of `Analysis.shear_blocks` (private there). -/
private theorem rc_shear_blocks {d : ℕ} {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) :
    (toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat E *
      toFullBlockMat (Book.Ch02.blockG h) =
    Matrix.fromBlocks (skewCorrectedForm E h) (E.upperRight + hᴴ * E.lowerRight)
      (E.lowerLeft + E.lowerRight * h) E.lowerRight := by
  rw [rc_shear_full, rc_full_eq, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, rc_skewCorrectedForm_eq hs hp]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_mul]
  congr 1
  abel

/-- Local copy of `Analysis.shear_pos` (private there). -/
private theorem rc_shear_pos {d : ℕ} {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) :
    ((toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat E *
      toFullBlockMat (Book.Ch02.blockG h)).PosDef :=
  (posDef_toFullBlockMat hs hp).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit (rc_shear_unit h))

/-- Local copy of `Analysis.upper_pos` (private there). -/
private theorem rc_upper_pos {d : ℕ} {A B C D : Mat d} (hp : (Matrix.fromBlocks A B C D).PosDef) :
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

/-- Local copy of `Analysis.corrected_pos` (private there). -/
private theorem rc_corrected_pos {d : ℕ} {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) : (skewCorrectedForm E h).PosDef := by
  have he := rc_shear_pos hs hp h
  rw [rc_shear_blocks hs hp] at he
  exact rc_upper_pos he

/-- Local copy of `InverseJensen`'s private `determinant_mono`, rebuilt from the public
`Recurrence.one_le_normalize` / `det_normalized_eq_div` /
`Recurrence.trace_sub_one_le_det_sub_one` toolkit
already in this namespace (`HCPoly/Entry/Multiscale/DriftAdvance.lean`). -/
private theorem det_le_det_of_posDef_of_le {ι : Type*} [Fintype ι] [DecidableEq ι] {F G : Matrix ι ι ℝ}
    (hF : F.PosDef) (hG : G.PosDef) (hGF : G ≤ F) : G.det ≤ F.det := by
  let T := matSqrt G⁻¹
  have hT : T.PosDef := matSqrt_inv_posDef_full hG
  have hN : (T * F * T).IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul T hF.isHermitian
    rwa [hT.isHermitian.eq] at h
  have hi : (1 : Matrix ι ι ℝ) ≤ T * F * T := Recurrence.one_le_normalize hG hGF
  have ht := (Matrix.le_iff.mp hi).trace_nonneg
  have hd := Recurrence.trace_sub_one_le_det_sub_one hN hi
  have hone : (1 : ℝ) ≤ (T * F * T).det := by linarith only [hd, ht]
  rw [show (T * F * T).det = F.det / G.det from det_normalized_eq_div F G hG] at hone
  exact (one_le_div hG.det_pos).mp hone

end RCHelpers
/-! Reference-comparison and inverse-Jensen goals of `p.global.selection`, built from the `rc_*`
helpers
above. -/
section RCGoals

open Matrix
open scoped MatrixOrder

/-- `p.global.selection` reference comparison `𝐄 ≤ 6Π · 𝐑 𝐄⁻¹ 𝐑`, `Π = aspectRatio E`, proved
directly from
`exists_isSkewMat_bigLambdaRef_eq` and the `rc_*` reconstructions below. -/
theorem refBlock_le_six_aspect {d : ℕ} (E : BlockMat d) (hEs : IsSymmetricBlockMat E)
    (hE : Book.Ch02.BlockPosDef E) :
    BlockMatLoewnerLE E
      (blockScale (6 * aspectRatio E)
        (ofFullBlockMat
          (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d))))  := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    intro X
    have hz : ∀ Y : BlockVec 0, blockVecDot X Y = 0 := by
      intro Y
      simp [blockVecDot, vecDot]
    simp [hz]
  · have : NeZero d := ⟨hdpos.ne'⟩
    obtain ⟨h, hh, hΛ⟩ := exists_isSkewMat_bigLambdaRef_eq hE
    have hp := posDef_toFullBlockMat hEs hE
    have hD := posDef_lowerRight hEs hE
    have hΛpos := Analysis.bigLambdaRef_pos hEs hE
    have hLpos : 0 < specBound E.lowerRight := inv_pos.mp (Analysis.lambdaRef_pos hEs hE)
    have hA : skewCorrectedForm E h ≤ bigLambdaRef E • (1 : Mat d) := by
      apply (BlockGeometricMean.matLE_iff (rc_corrected_pos hEs hE h).isHermitian
        (rc_hermitian_smul Matrix.isHermitian_one _)).2
      rw [hΛ]
      exact matLoewnerLE_specBound_smul_one _
    have hDle : E.lowerRight ≤ specBound E.lowerRight • (1 : Mat d) :=
      (BlockGeometricMean.matLE_iff hD.isHermitian (rc_hermitian_smul Matrix.isHermitian_one _)).2
        (matLoewnerLE_specBound_smul_one _)
    have hsp := rc_shear_pos hEs hE h
    rw [rc_shear_blocks hEs hE] at hsp
    have hfour := rc_four_product_bound hsp hΛpos hLpos hA hDle
    rw [← rc_shear_blocks hEs hE, ← rc_shear_swapConj E h hh] at hfour
    have hπ : aspectRatio E = bigLambdaRef E * specBound E.lowerRight := by
      simp only [aspectRatio, lambdaRef, div_inv_eq_mul]
    have hfull : toFullBlockMat E ≤ (4 * aspectRatio E) •
        (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d)) := by
      apply Matrix.le_iff.mpr
      apply (rc_shear_unit h).posSemidef_star_left_conjugate_iff.mp
      have hs := Matrix.le_iff.mp hfour
      simpa only [Matrix.star_eq_conjTranspose, mul_sub, sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, hπ, mul_assoc] using hs
    have hπ0 := aspectRatio_nonneg E
    have hspos := Analysis.swapConj_posDef hp
    have hlast := smul_le_smul_of_nonneg_right
      (by linarith only [hπ0] : 4 * aspectRatio E ≤ 6 * aspectRatio E)
      (by simpa only [toFullBlockMat_ofFullBlockMat] using hspos.posSemidef.nonneg)
    apply (Annealed.fullBlock_le_iff hp.isHermitian (by
      rw [HCPolySupport.HighContrast.toFullBlockMat_blockScale]; exact rc_hermitian_smul hspos.isHermitian _)).1
    simpa only [HCPolySupport.HighContrast.toFullBlockMat_blockScale, toFullBlockMat_ofFullBlockMat] using hfull.trans hlast

/-- `p.global.selection` upper bound: `det 𝐀 ≤ 2^{2d} det 𝐄 ≤ (24Π)^d` from `𝐀 ≤ 2𝐄`, `𝐄 ≤ 6Π
𝐑𝐄⁻¹𝐑` and
`det 𝐄 · det(𝐑𝐄⁻¹𝐑) = 1`. -/
theorem blockLogDet_le_of_initial_sandwich {d : ℕ} (E A : BlockMat d) (hEs : IsSymmetricBlockMat E)
    (hE : Book.Ch02.BlockPosDef E) (hAs : IsSymmetricBlockMat A) (hA : Book.Ch02.BlockPosDef A)
    (hAR : 0 < aspectRatio E)
    (hsix : BlockMatLoewnerLE E
      (blockScale (6 * aspectRatio E)
        (ofFullBlockMat
          (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d)))))
    (hup : BlockMatLoewnerLE A (blockScale 2 E)) :
    blockLogDet A ≤ (d : ℝ) * Real.log (24 * aspectRatio E)  := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have : IsEmpty (BlockCoord 0) :=
      ⟨fun x => Sum.elim (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0) x⟩
    simp [blockLogDet, Matrix.det_isEmpty]
  · have : NeZero d := ⟨hdpos.ne'⟩
    have hEfull : (toFullBlockMat E).PosDef := posDef_toFullBlockMat hEs hE
    have hAfull : (toFullBlockMat A).PosDef := posDef_toFullBlockMat hAs hA
    have h12 : (1 : ℝ) + 1 = 2 := by norm_num
    have hup' : BlockMatLoewnerLE A (blockScale (1 + 1) E) := by rw [h12]; exact hup
    have hstep1 := blockLogDet_le_of_sandwich E A 1 (by norm_num) hEs hE hAs hA hup'
    rw [h12] at hstep1
    have h6pos : 0 < 6 * aspectRatio E := by linarith only [hAR]
    have hR'pos : (toFullBlockMat (ofFullBlockMat (toFullBlockMat (blockSwap d) *
        (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d)))).PosDef :=
      Analysis.swapConj_posDef hEfull
    have hsixFull : toFullBlockMat E ≤ (6 * aspectRatio E) • toFullBlockMat
        (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
          toFullBlockMat (blockSwap d))) := by
      have h := (Annealed.fullBlock_le_iff hEfull.isHermitian (by
        rw [HCPolySupport.HighContrast.toFullBlockMat_blockScale]; exact rc_hermitian_smul hR'pos.isHermitian _)).2 hsix
      rwa [HCPolySupport.HighContrast.toFullBlockMat_blockScale] at h
    have hd := det_le_det_of_posDef_of_le (hR'pos.smul h6pos) hEfull hsixFull
    rw [Matrix.det_smul, Analysis.det_swapConj] at hd
    have hn : Fintype.card (BlockCoord d) = 2 * d := by simp [BlockCoord, two_mul]
    rw [hn] at hd
    have hs := mul_le_mul_of_nonneg_right hd hEfull.det_pos.le
    rw [mul_assoc, inv_mul_cancel₀ hEfull.det_pos.ne', mul_one] at hs
    have he : (6 * aspectRatio E) ^ (2 * d) = ((6 * aspectRatio E) ^ d) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm d 2]
    rw [he, ← sq] at hs
    have hdetE_le : (toFullBlockMat E).det ≤ (6 * aspectRatio E) ^ d :=
      (sq_le_sq₀ hEfull.det_pos.le (pow_nonneg h6pos.le _)).mp hs
    have hstep2 : blockLogDet E ≤ (d : ℝ) * Real.log (6 * aspectRatio E) := by
      unfold blockLogDet
      calc Real.log (toFullBlockMat E).det ≤ Real.log ((6 * aspectRatio E) ^ d) :=
            Real.log_le_log hEfull.det_pos hdetE_le
        _ = (d : ℝ) * Real.log (6 * aspectRatio E) := by rw [Real.log_pow]
    have hlog2 : Real.log (24 * aspectRatio E) =
        Real.log (6 * aspectRatio E) + 2 * Real.log 2 := by
      have h4 : (24 : ℝ) * aspectRatio E = 4 * (6 * aspectRatio E) := by ring
      rw [h4, Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) h6pos.ne']
      have h4sq : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [h4sq, Real.log_pow]
      push_cast
      ring
    calc blockLogDet A ≤ blockLogDet E + 2 * (d : ℝ) * Real.log 2 := hstep1
      _ ≤ (d : ℝ) * Real.log (6 * aspectRatio E) + 2 * (d : ℝ) * Real.log 2 := by
          linarith only [hstep2]
      _ = (d : ℝ) * Real.log (24 * aspectRatio E) := by rw [hlog2]; ring

end RCGoals

end

end HCPolySupport.HighContrast.Multiscale
