/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.BlockSwapReflection

/-!
# High-contrast homogenization: Entry.Analysis.ReferenceComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Reference block comparison

These are deterministic bounds for the block carriers and reference constants.
The source statements are near `e.reference.aspect.ratio` and `e.two.grid.whitney.source`,
`p.initial.fixed.grid.scale` and `p.global.selection`.
The source argument is Lemma `l.bfE.bounds` of the companion paper HC.
The swap, shear and Schur algebra these bounds run on is
`HCPoly/Entry/Analysis/BlockSwapReflection.lean`.

Reference order remains an explicit premise; this module does not derive it from the dagger.
Schur factorization identifies the inverse flux block, giving `1 ≤ refContrast E`.
An attained skew minimizer gives `refContrast E ≤ aspectRatio E` and strictly positive
reference constants. For the comparison, positive block quadratic forms give domination by
twice the scalar diagonal bounds after a skew shear. Inversion and reflection then give a
`4 * aspectRatio E` bound, which implies the exported, literal `6 * aspectRatio E` bound.
This is the direct route: the sharper HC excess estimate `e.grok`
with coefficient `1 + 6 * (refContrast E - 1)` is not delivered.

The determinant is the ordinary determinant of the full `2d` matrix. Its comparison with the
reciprocal determinant first bounds its square and therefore gives the printed exponent `d`.
The weaker exponent `2 * d` is recorded separately.
No probability law, quantitative ellipticity constant, or annealed premise enters these bounds.
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

private theorem specBound_pos [NeZero d] {A : Mat d} (hp : A.PosDef) : 0 < specBound A := by
  let i : Fin d := ⟨0, NeZero.pos d⟩
  have ht := (matLoewnerLE_smul_one_iff A (specBound A)).1
    (matLoewnerLE_specBound_smul_one A) (Pi.single i 1)
  have ht' : A i i ≤ specBound A := by
    simpa [vecDot, vecNormSq, matVecMul, Pi.single_apply, mul_ite,
      Finset.sum_ite_eq'] using ht
  exact hp.diag_pos.trans_le ht'

/-- The reference lower ellipticity constant is strictly positive. -/
theorem lambdaRef_pos [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) : 0 < lambdaRef E :=
  inv_pos.mpr (specBound_pos (posDef_lowerRight hsymm hpos))

/-- The attained reference upper ellipticity constant is strictly positive. -/
theorem bigLambdaRef_pos [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) : 0 < bigLambdaRef E := by
  obtain ⟨h, _, he⟩ := exists_isSkewMat_bigLambdaRef_eq hpos
  rw [he]
  exact specBound_pos (posDef_skewCorrectedForm hsymm hpos h)

private theorem scalar_inv (c : ℝ) (hc : c ≠ 0) :
    (c • (1 : Mat d))⁻¹ = c⁻¹ • (1 : Mat d) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, one_mul]

/-- Minimizing the intrinsic contrast is bounded by the product of the two reference norms. -/
theorem refContrast_le_aspectRatio [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) :
    refContrast E ≤ aspectRatio E := by
  obtain ⟨h, hh, hΛ⟩ := exists_isSkewMat_bigLambdaRef_eq hpos
  have hD := posDef_lowerRight hsymm hpos
  have hL := specBound_pos hD
  have hΛpos := bigLambdaRef_pos hsymm hpos
  have hDle : E.lowerRight ≤ specBound E.lowerRight • (1 : Mat d) :=
    (matrix_le_iff_matLoewnerLE hD.isHermitian (isHermitian_smul Matrix.isHermitian_one _)).2
      (matLoewnerLE_specBound_smul_one E.lowerRight)
  have hDi := inv_le_inv_of_posDef_le hD (Matrix.PosDef.one.smul hL) hDle
  rw [scalar_inv _ hL.ne'] at hDi
  have hstep := smul_le_smul_of_nonneg_left hDi (mul_nonneg hΛpos.le hL.le)
  have hcancel : (bigLambdaRef E * specBound E.lowerRight) •
      ((specBound E.lowerRight)⁻¹ • (1 : Mat d)) = bigLambdaRef E • (1 : Mat d) := by
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hL.ne', mul_one]
  rw [hcancel] at hstep
  have hKle : skewCorrectedForm E h ≤ bigLambdaRef E • (1 : Mat d) := by
    apply (matrix_le_iff_matLoewnerLE (posDef_skewCorrectedForm hsymm hpos h).isHermitian
      (isHermitian_smul Matrix.isHermitian_one _)).2
    rw [hΛ]
    exact matLoewnerLE_specBound_smul_one _
  change blockContrast E ≤ bigLambdaRef E / (specBound E.lowerRight)⁻¹
  rw [div_inv_eq_mul]
  exact blockContrast_le (mul_nonneg hΛpos.le hL.le) hh
    ((matrix_le_iff_matLoewnerLE (posDef_skewCorrectedForm hsymm hpos h).isHermitian
      (isHermitian_smul hD.inv.isHermitian _)).1 (hKle.trans hstep))

private theorem schurSigmaStar_le_schurSigma {E : BlockMat d}
    (hs : IsSymmetricBlockMat E) (hp : Book.Ch02.BlockPosDef E)
    (ho : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d))) E) :
    schurSigmaStar E ≤ schurSigma E := by
  have hflux : MatLoewnerLE ((schurSigma E)⁻¹) E.lowerRight := by
    intro x
    have h := ho (0, x)
    simp only [blockVecDot_inr] at h
    rw [swapConj_lowerRight hs hp] at h
    exact h
  have hi := inv_le_inv_of_posDef_le (posDef_schurSigma hs hp).inv (posDef_lowerRight hs hp)
    ((matrix_le_iff_matLoewnerLE (posDef_schurSigma hs hp).inv.isHermitian
      (posDef_lowerRight hs hp).isHermitian).2 hflux)
  simpa only [Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (posDef_schurSigma hs hp).isUnit), schurSigmaStar] using hi

/-- The Schur complement is dominated in the Loewner order by every skew-corrected form:
`schurSigma E ≤ skewCorrectedForm E h` for an arbitrary skew correction `h`. -/
theorem schurSigma_le_corrected {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) :
    schurSigma E ≤ skewCorrectedForm E h := by
  apply Matrix.le_iff.mpr
  have hq := (posDef_lowerRight hs hp).posSemidef.conjTranspose_mul_mul_same (schurSkew E - h)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, skewCorrectedForm,
    add_sub_cancel_left] using! hq

/-- Reference order forces the attained intrinsic contrast to be at least one. -/
theorem one_le_refContrast [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (horder : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d))) E) :
    1 ≤ refContrast E := by
  obtain ⟨h, _, he⟩ := exists_isSkewMat_blockContrast_eq hsymm hpos
  obtain ⟨hRs, hRdet, hRR⟩ := matSqrt_lowerRight_spec hsymm hpos
  have htconj := matLoewnerLE_specBound_smul_one
    (matSqrt E.lowerRight * skewCorrectedForm E h * matSqrt E.lowerRight)
  rw [← he] at htconj
  have ht : MatLoewnerLE (skewCorrectedForm E h) (refContrast E • schurSigmaStar E) :=
    (matLoewnerLE_smul_iff_conj hRs hRR hRdet (refContrast E)).2 htconj
  have hl := (schurSigmaStar_le_schurSigma hsymm hpos horder).trans
    (schurSigma_le_corrected hsymm hpos h)
  have hu := (matrix_le_iff_matLoewnerLE (posDef_skewCorrectedForm hsymm hpos h).isHermitian
    (isHermitian_smul (posDef_lowerRight hsymm hpos).inv.isHermitian _)).2 ht
  have hboth := Matrix.le_iff.mp (hl.trans hu)
  let x : Vec d := Pi.single ⟨0, NeZero.pos d⟩ 1
  have hx : x ≠ 0 := by simp [x]
  have hq := (posDef_lowerRight hsymm hpos).inv.dotProduct_mulVec_pos hx
  have htq := hboth.dotProduct_mulVec_nonneg x
  simp only [star_trivial, schurSigmaStar, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at htq hq
  nlinarith only [htq, hq]

/-- The printed aspect ratio lower bound, under reference order. -/
theorem one_le_aspectRatio [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (horder : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d))) E) :
    1 ≤ aspectRatio E :=
  (one_le_refContrast hsymm hpos horder).trans (refContrast_le_aspectRatio hsymm hpos)

/-- Positivity and the lower bound for the logarithmic argument used downstream. -/
theorem aspectRatio_pos_and_three_le [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (horder : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d))) E) :
    0 < aspectRatio E ∧ 3 ≤ 2 + aspectRatio E := by
  have h := one_le_aspectRatio hsymm hpos horder
  constructor <;> linarith only [h]

private theorem scalar_diag_eq (a b : ℝ) :
    Matrix.fromBlocks (a • (1 : Mat d)) 0 0 (b • (1 : Mat d)) =
      Matrix.diagonal (Sum.elim (fun _ : Fin d => a) (fun _ : Fin d => b)) := by
  ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply]

private theorem scalar_diag_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Matrix.fromBlocks (a • (1 : Mat d)) 0 0 (b • (1 : Mat d))).PosDef := by
  rw [scalar_diag_eq]
  exact Matrix.PosDef.diagonal (fun i => by cases i <;> assumption)

private theorem scalar_diag_inv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Matrix.fromBlocks (a • (1 : Mat d)) 0 0 (b • (1 : Mat d)))⁻¹ =
      Matrix.fromBlocks (a⁻¹ • (1 : Mat d)) 0 0 (b⁻¹ • (1 : Mat d)) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb,
    one_smul, one_mul, Matrix.fromBlocks_one]

private theorem two_diag_bound {A B C D : Mat d}
    (hp : (Matrix.fromBlocks A B C D).PosSemidef) {a b : ℝ}
    (ha : A ≤ a • (1 : Mat d)) (hb : D ≤ b • (1 : Mat d)) :
    Matrix.fromBlocks A B C D ≤
      Matrix.fromBlocks ((2 * a) • (1 : Mat d)) 0 0 ((2 * b) • (1 : Mat d)) := by
  have hdiag : (Matrix.fromBlocks ((2 * a) • (1 : Mat d)) 0 0
      ((2 * b) • (1 : Mat d))).IsHermitian := by
    rw [scalar_diag_eq]
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

private theorem four_product_bound {A B C D : Mat d}
    (hp : (Matrix.fromBlocks A B C D).PosDef) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : A ≤ a • (1 : Mat d)) (hD : D ≤ b • (1 : Mat d)) :
    Matrix.fromBlocks A B C D ≤ (4 * a * b) •
      (toFullBlockMat (blockSwap d) * (Matrix.fromBlocks A B C D)⁻¹ *
        toFullBlockMat (blockSwap d)) := by
  have ha2 : 0 < 2 * a := mul_pos (by norm_num) ha
  have hb2 : 0 < 2 * b := mul_pos (by norm_num) hb
  have hu := two_diag_bound hp.posSemidef hA hD
  have hi := inv_le_inv_of_posDef_le hp (scalar_diag_pos ha2 hb2) hu
  have hr := star_left_conjugate_le_conjugate hi (toFullBlockMat (blockSwap d))
  rw [show star (toFullBlockMat (blockSwap d)) = toFullBlockMat (blockSwap d)
    from (isHermitian_toFullBlockMat_blockSwap d).eq] at hr
  have hscale := smul_le_smul_of_nonneg_left hr (by positivity : 0 ≤ 4 * a * b)
  have heq : (4 * a * b) • (toFullBlockMat (blockSwap d) *
      (Matrix.fromBlocks ((2 * a) • (1 : Mat d)) 0 0 ((2 * b) • (1 : Mat d)))⁻¹ *
        toFullBlockMat (blockSwap d)) =
      Matrix.fromBlocks ((2 * a) • (1 : Mat d)) 0 0 ((2 * b) • (1 : Mat d)) := by
    rw [scalar_diag_inv ha2.ne' hb2.ne', blockSwap_conj_fromBlocks]
    simp only [Matrix.fromBlocks_smul, smul_zero, smul_smul]
    congr 2 <;> field_simp [ha.ne', hb.ne'] <;> ring
  rw [heq] at hscale
  exact hu.trans hscale

private theorem full_scale (c : ℝ) (E : BlockMat d) :
    toFullBlockMat (blockScale c E) = c • toFullBlockMat E := by
  ext (i | i) (j | j) <;> rfl

/-- The printed factor-six comparison. The proof uses diagonal domination after an attained
skew shear, directly; the sharper HC excess estimate `e.grok` is not asserted here. -/
theorem refBlock_le_six_aspectRatio_smul_swapConj [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (horder : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d))) E) :
    BlockMatLoewnerLE E (blockScale (6 * aspectRatio E)
      (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
        toFullBlockMat (blockSwap d)))) := by
  obtain ⟨h, hh, hΛ⟩ := exists_isSkewMat_bigLambdaRef_eq hpos
  have hp := posDef_toFullBlockMat_of_blockPosDef hsymm hpos
  have hD := posDef_lowerRight hsymm hpos
  have hΛpos := bigLambdaRef_pos hsymm hpos
  have hLpos := specBound_pos hD
  have hA : skewCorrectedForm E h ≤ bigLambdaRef E • (1 : Mat d) := by
    apply (matrix_le_iff_matLoewnerLE (posDef_skewCorrectedForm hsymm hpos h).isHermitian
      (isHermitian_smul Matrix.isHermitian_one _)).2
    rw [hΛ]
    exact matLoewnerLE_specBound_smul_one _
  have hDle : E.lowerRight ≤ specBound E.lowerRight • (1 : Mat d) :=
    (matrix_le_iff_matLoewnerLE hD.isHermitian (isHermitian_smul Matrix.isHermitian_one _)).2
      (matLoewnerLE_specBound_smul_one _)
  have hsp := posDef_blockG_conj hsymm hpos h
  rw [blockG_conj_eq_fromBlocks hsymm hpos] at hsp
  have hfour := four_product_bound hsp hΛpos hLpos hA hDle
  rw [← blockG_conj_eq_fromBlocks hsymm hpos, ← blockG_conj_swapConj_eq E h hh] at hfour
  have hπ : aspectRatio E = bigLambdaRef E * specBound E.lowerRight := by
    simp only [aspectRatio, lambdaRef, div_inv_eq_mul]
  have hfull : toFullBlockMat E ≤ (4 * aspectRatio E) •
      (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d)) := by
    apply Matrix.le_iff.mpr
    apply (isUnit_toFullBlockMat_blockG h).posSemidef_star_left_conjugate_iff.mp
    have hs := Matrix.le_iff.mp hfour
    simpa only [Matrix.star_eq_conjTranspose, mul_sub, sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, hπ, mul_assoc] using hs
  have hπ0 := (aspectRatio_pos_and_three_le hsymm hpos horder).1.le
  have hspos := swapConj_posDef hp
  have hlast := smul_le_smul_of_nonneg_right
    (by linarith only [hπ0] : 4 * aspectRatio E ≤ 6 * aspectRatio E)
    (by simpa only [toFullBlockMat_ofFullBlockMat] using hspos.posSemidef.nonneg)
  apply (toFullBlockMat_le_iff hp.isHermitian (by
    rw [full_scale]; exact isHermitian_smul hspos.isHermitian _)).1
  simpa only [full_scale, toFullBlockMat_ofFullBlockMat] using hfull.trans hlast
end
end HCPolySupport.HighContrast.Analysis
