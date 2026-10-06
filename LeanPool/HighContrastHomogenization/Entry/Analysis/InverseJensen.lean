/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AnnealedBlockOrder
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.AdjointSymmetry.BasicAdjoint
public import LeanPool.HighContrastHomogenization.Annealed.Contrast
public import LeanPool.HighContrastHomogenization.Geometry.BlockBridge
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.DetTransport

/-!
# High-contrast homogenization: Entry.Analysis.InverseJensen

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section
/-!
# Inverse Jensen and the annealed primal–adjoint order

Ordinary support for `p.global.selection`
and near `e.two.grid.source.normalization`, on the CG block and coefficient carriers.
The pathwise input is derived from response nonnegativity for both the original and
adjoint coefficient fields. The deterministic two-sign reduction uses Mathlib's Schur
complement and elementary quadratic identities; it needs no new spectral theorem.

Inverse Jensen integrates a fixed variational test vector and then uses the attained
maximum. The inverse entries are separately proved integrable, by domination from the
pathwise order and the measurable determinant/adjugate formula. Deterministic swap
conjugation commutes with the entrywise integral; inversion is never commuted with it.

The rounded-grid endpoints discharge integrability and positive definiteness under the
standing stationary dagger law. The version
`adaptedMean_swapConj_le_of_integrable` also covers the literal Euclidean grid: it takes
any invertible grid and the existing `HasIntegrableCoarseBlock` receipt, and the
inverse-conjugate order it supplies gives the determinant lower bound for those grids.
This keeps the rounded-grid order independent of the Euclidean-grid identification.
No unit-range or extra source-window premise is needed here.

The generic matrix results include empty finite index sets. Actual adapted domains
require `NeZero d`; the standing-law corollaries carry `2 ≤ d`. Strict positivity is
proved before every use of inverse cancellation and determinant positivity. The
reference-block order for `E` is not asserted by this file.
-/

open Matrix MeasureTheory
open scoped MatrixOrder
open HCPolySupport.HighContrast.CG

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedMean
  blockPosDef_annealedBlock blockScale coarseBlock coarseBlock_eq_of_ae_eq
  isSymmetricBlockMat_coarseBlockMatrix matSqrt toFullBlockMat_eq_blockMatEntry)
namespace HCPolySupport.HighContrast.Analysis

private theorem quadratic_completion {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) (x y : ι → ℝ) :
    2 * (x ⬝ᵥ y) - y ⬝ᵥ M.mulVec y =
      x ⬝ᵥ M⁻¹.mulVec x -
        (y - M⁻¹.mulVec x) ⬝ᵥ M.mulVec (y - M⁻¹.mulVec x) := by
  have hMx : M.mulVec (M⁻¹.mulVec x) = x := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv M (M.isUnit_iff_isUnit_det.mp hM.isUnit), one_mulVec]
  have hsym : (M⁻¹.mulVec x) ⬝ᵥ M.mulVec y = x ⬝ᵥ y := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [show M.transpose = M from by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial]
      using! hM.isHermitian, hMx]
  simp only [mulVec_sub, dotProduct_sub, sub_dotProduct, hMx, hsym]
  rw [dotProduct_comm y x, dotProduct_comm (M⁻¹.mulVec x) x]
  ring

/-- Every variational test lies below the inverse quadratic form. -/
theorem two_inner_sub_quadratic_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) (x y : ι → ℝ) :
    2 * (x ⬝ᵥ y) - y ⬝ᵥ M.mulVec y ≤ x ⬝ᵥ M⁻¹.mulVec x := by
  rw [quadratic_completion hM]
  have hp := hM.posSemidef.dotProduct_mulVec_nonneg (y - M⁻¹.mulVec x)
  simpa only [star_trivial, sub_le_self_iff] using hp

/-- The inverse quadratic form is the attained maximum of the affine-quadratic tests. -/
theorem isGreatest_two_inner_sub_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) (x : ι → ℝ) :
    IsGreatest {t : ℝ | ∃ y : ι → ℝ, t = 2 * (x ⬝ᵥ y) - y ⬝ᵥ M.mulVec y}
      (x ⬝ᵥ M⁻¹.mulVec x) := by
  refine ⟨⟨M⁻¹.mulVec x, ?_⟩, ?_⟩
  · rw [quadratic_completion hM]
    simp
  · rintro t ⟨y, rfl⟩
    exact two_inner_sub_quadratic_le hM x y

private theorem integrable_quadratic {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} {A : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, Integrable (fun a => A a i j) P) (x : ι → ℝ) :
    Integrable (fun a => x ⬝ᵥ (A a).mulVec x) P := by
  simp only [dotProduct, mulVec]
  exact integrable_finsetSum _ fun i _ =>
    (integrable_finsetSum _ fun j _ => (hA i j).mul_const (x j)).const_mul (x i)

private theorem integral_quadratic {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} {A : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, Integrable (fun a => A a i j) P) (x : ι → ℝ) :
    (∫ a, x ⬝ᵥ (A a).mulVec x ∂P) =
      x ⬝ᵥ (Matrix.of fun i j => ∫ a, A a i j ∂P).mulVec x := by
  simp only [dotProduct, mulVec, Matrix.of_apply]
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_finsetSum _ fun j _ => (hA i j).mul_const (x j)).const_mul (x i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => (hA i j).mul_const (x j))]
  simp only [integral_mul_const]

/-- Inverse Jensen: a fixed variational test vector is integrated before maximizing. -/
theorem inner_inv_integral_le_integral_inner_inv {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A : Ω → Matrix ι ι ℝ)
    (hAE : ∀ᵐ a ∂P, (A a).PosDef)
    (hA : ∀ i j, Integrable (fun a => A a i j) P)
    (hAinv : ∀ i j, Integrable (fun a => (A a)⁻¹ i j) P)
    (hbar : (Matrix.of fun i j => ∫ a, A a i j ∂P).PosDef)
    (x : ι → ℝ) :
    x ⬝ᵥ (Matrix.of fun i j => ∫ a, A a i j ∂P)⁻¹.mulVec x ≤
      x ⬝ᵥ (Matrix.of fun i j => ∫ a, (A a)⁻¹ i j ∂P).mulVec x := by
  obtain ⟨y, hy⟩ := (isGreatest_two_inner_sub_quadratic hbar x).1
  rw [hy, ← integral_quadratic hA y, ← integral_quadratic hAinv x]
  have hleft := (integrable_const (2 * (x ⬝ᵥ y))).sub (integrable_quadratic hA y)
  have hright := integrable_quadratic hAinv x
  have heq : 2 * (x ⬝ᵥ y) - (∫ a, y ⬝ᵥ (A a).mulVec y ∂P) =
      ∫ a, 2 * (x ⬝ᵥ y) - y ⬝ᵥ (A a).mulVec y ∂P := by
    rw [integral_sub (integrable_const _) (integrable_quadratic hA y)]
    simp only [integral_const, probReal_univ, one_smul]
  rw [heq]
  apply integral_mono_ae hleft hright
  filter_upwards [hAE] with a ha
  exact two_inner_sub_quadratic_le ha x y

private theorem symmetric_inv_congr_le_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F B : Matrix ι ι ℝ} (hF : F.PosDef) (hB : B.IsHermitian) :
    B * F⁻¹ * B ≤ F ↔ B ≤ F ∧ -B ≤ F := by
  let := hF.isUnit.invertible
  have hBF : Bᴴ = B := hB
  have hBt : Bᵀ = B := by simpa only [conjTranspose_eq_transpose_of_trivial] using! hB
  have hcross (x y : ι → ℝ) : y ⬝ᵥ B.mulVec x = x ⬝ᵥ B.mulVec y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hBt, dotProduct_comm]
  have hschur := Matrix.PosDef.fromBlocks₁₁ B F hF
  rw [hBF] at hschur
  rw [Matrix.le_iff, ← hschur]
  constructor
  · intro h
    constructor
    · apply Matrix.le_iff.mpr
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hF.1.sub hB) ?_
      intro x
      have hx := h.dotProduct_mulVec_nonneg (Sum.elim x (-x))
      simp only [star_trivial, Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim,
        Function.comp_def, Sum.elim_inl, Sum.elim_inr, mulVec_neg, dotProduct_add, dotProduct_neg,
        neg_dotProduct, neg_neg] at hx
      simp only [star_trivial, sub_mulVec, dotProduct_sub]
      linarith only [hx]
    · apply Matrix.le_iff.mpr
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hF.1.sub hB.neg) ?_
      intro x
      have hx := h.dotProduct_mulVec_nonneg (Sum.elim x x)
      simp only [star_trivial, Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim,
        Function.comp_def, Sum.elim_inl, Sum.elim_inr, dotProduct_add] at hx
      simp only [star_trivial, sub_mulVec, neg_mulVec, dotProduct_sub, dotProduct_neg]
      linarith only [hx]
  · rintro ⟨hp, hn⟩
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact Matrix.IsHermitian.fromBlocks hF.1 hBF hF.1
    · intro z
      let x := z ∘ Sum.inl
      let y := z ∘ Sum.inr
      have hplus := (Matrix.le_iff.mp hn).dotProduct_mulVec_nonneg (x + y)
      have hminus := (Matrix.le_iff.mp hp).dotProduct_mulVec_nonneg (x - y)
      simp only [star_trivial, sub_mulVec, neg_mulVec, mulVec_add, mulVec_sub,
        dotProduct_sub, dotProduct_add, sub_dotProduct, add_dotProduct,
        dotProduct_neg, hcross y x] at hplus hminus
      rw [← Sum.elim_comp_inl_inr z]
      simp only [star_trivial, Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim,
        dotProduct_add]
      change 0 ≤ x ⬝ᵥ F.mulVec x + x ⬝ᵥ B.mulVec y +
        (y ⬝ᵥ B.mulVec x + y ⬝ᵥ F.mulVec y)
      rw [hcross]
      linarith only [hplus, hminus, hcross y x]

private theorem swap_hermitian (d : ℕ) : (toFullBlockMat (blockSwap d)).IsHermitian := by
  apply (toFullBlockMat_isHermitian_iff _).2
  intro α β
  cases α <;> cases β <;>
    simp [blockSwap, Book.Ch02.blockR, blockMatEntry, Matrix.one_apply, eq_comm]

private theorem swap_square (d : ℕ) :
    toFullBlockMat (blockSwap d) * toFullBlockMat (blockSwap d) = 1 := by
  have he : toFullBlockMat (blockSwap d) =
      Matrix.fromBlocks (0 : Mat d) (1 : Mat d) (1 : Mat d) 0 := by
    ext α β
    cases α <;> cases β <;> rfl
  rw [he, Matrix.fromBlocks_multiply]
  simp

private theorem full_scale_neg (d : ℕ) :
    toFullBlockMat (blockScale (-1) (blockSwap d)) = -toFullBlockMat (blockSwap d) := by
  ext α β
  cases α <;> cases β <;> simp [toFullBlockMat, blockScale]

/-- The two signs characterize the inverse-conjugate order, by the Schur complement. -/
theorem blockMatLoewnerLE_swapConj_inv_iff {d : ℕ} {F : BlockMat d}
    (hsymm : IsSymmetricBlockMat F) (hpos : (toFullBlockMat F).PosDef) :
    BlockMatLoewnerLE
        (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ *
          toFullBlockMat (blockSwap d))) F ↔
      (BlockMatLoewnerLE (blockSwap d) F ∧
        BlockMatLoewnerLE (blockScale (-1) (blockSwap d)) F) := by
  have hR := swap_hermitian d
  have hF := (toFullBlockMat_isHermitian_iff F).2 hsymm
  have hconj : (toFullBlockMat (ofFullBlockMat
      (toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ *
        toFullBlockMat (blockSwap d)))).IsHermitian := by
    simpa only [toFullBlockMat_ofFullBlockMat, hR.eq] using
      (hpos.inv.posSemidef.conjTranspose_mul_mul_same (toFullBlockMat (blockSwap d))).1
  rw [← Annealed.fullBlock_le_iff hconj hF, toFullBlockMat_ofFullBlockMat,
    symmetric_inv_congr_le_iff hpos hR, Annealed.fullBlock_le_iff hR hF]
  have hn : (toFullBlockMat (blockScale (-1) (blockSwap d))).IsHermitian := by
    rw [full_scale_neg]
    exact hR.neg
  rw [← Annealed.fullBlock_le_iff hn hF, full_scale_neg]

private theorem negative_swap_le_of_response {d : ℕ} {U : Set (Vec d)}
    {f : CoeffField d} {F : BlockMat d}
    (hresp : ∀ p r, ResponseJ U p r f =
      (1 / 2 : ℝ) * blockVecDot (-p, r) (blockMatVecMul F (-p, r)) - vecDot p r) :
    BlockMatLoewnerLE (blockScale (-1) (blockSwap d)) F := by
  intro X
  have h := responseJ_nonneg U (-X.1) X.2 f
  rw [hresp, neg_neg, vecDot_neg_left] at h
  change (1 / 2 : ℝ) * blockVecDot X
    (blockMatVecMul (blockScale (-1) (blockSwap d)) X) ≤ _
  have he : blockVecDot X (blockMatVecMul (blockScale (-1) (blockSwap d)) X) =
      -(2 * vecDot X.1 X.2) := by
    simp [blockScale, blockSwap, Book.Ch02.blockR, blockMatVecMul, blockVecDot,
      matVecMul, vecDot, Matrix.one_apply, mul_comm]
    ring
  rw [he]
  simpa only [Prod.mk.eta] using (by linarith only [h] :
    (1 / 2 : ℝ) * -(2 * vecDot X.1 X.2) ≤
      (1 / 2 : ℝ) * blockVecDot (X.1, X.2) (blockMatVecMul F (X.1, X.2)))

private theorem both_signs_coarseBlock {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d) (a : CoeffSpace d) :
    BlockMatLoewnerLE (blockSwap d) (coarseBlock (HighContrast.adaptedCellTranslate q j y) a) ∧
      BlockMatLoewnerLE (blockScale (-1) (blockSwap d))
        (coarseBlock (HighContrast.adaptedCellTranslate q j y) a) := by
  have hneg := negative_swap_le_of_response (Annealed.responseJ_eq_coarseBlock_adapted q hq j y a)
  refine ⟨?_, hneg⟩
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq j y a
  rw [coarseBlock_eq_of_ae_eq a hae, Annealed.adaptedCellTranslate_eq_cg_affine]
  rw [Annealed.adaptedCellTranslate_eq_cg_affine] at hEll
  have hc := isCoarseBlockMatrix_affine_openCube q hq j y f hEll
  have hadj := coarseBlockMatrix_adjointCoeffField_of_exists ⟨_, hc⟩
  have hr := responseJ_eq_block_quadratic_affine_openCube q hq j y
    (adjointCoeffField f) (isEllipticFieldOn_adjointCoeffField hEll)
  have hn := negative_swap_le_of_response hr
  rw [hadj] at hn
  intro X
  have h := hn (blockVecFlipFlux X)
  rw [blockMatVecMul_blockMatFlipFlux, blockVecDot_blockVecFlipFlux_right,
    blockVecFlipFlux_flipFlux] at h
  have he : blockVecDot (blockVecFlipFlux X)
      (blockMatVecMul (blockScale (-1) (blockSwap d)) (blockVecFlipFlux X)) =
      blockVecDot X (blockMatVecMul (blockSwap d) X) := by
    simp [blockVecFlipFlux, blockScale, blockSwap, Book.Ch02.blockR,
      blockMatVecMul, blockVecDot, matVecMul, vecDot, Matrix.one_apply, mul_comm]
  rw [he] at h
  exact h

private theorem abs_entry_le_half_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (i j : ι) :
    |M i j| ≤ (M i i + M j j) / 2 := by
  have hp := hM.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have hn := hM.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  have hsym : M j i = M i j := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using congrArg (fun N => N i j) hM.1
  simp only [star_trivial, mulVec_add, mulVec_sub, dotProduct_add, dotProduct_sub,
    add_dotProduct, sub_dotProduct, single_dotProduct, mulVec_single_one, Matrix.col_apply,
      one_mul, hsym] at hp hn
  exact abs_le.mpr ⟨by linarith only [hp], by linarith only [hn]⟩

private theorem diagonal_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Matrix ι ι ℝ} (h : M ≤ N) (i : ι) : M i i ≤ N i i := by
  have hn := (Matrix.le_iff.mp h).diag_nonneg (i := i)
  exact sub_nonneg.mp hn

private theorem inverse_entry_aestronglyMeasurable {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    {P : Measure Ω} {A : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, Integrable (fun a => A a i j) P) (i j : ι) :
    AEStronglyMeasurable (fun a => (A a)⁻¹ i j) P := by
  let : MeasurableSpace (Matrix ι ι ℝ) := inferInstanceAs (MeasurableSpace (ι → ι → ℝ))
  let : OpensMeasurableSpace (Matrix ι ι ℝ) :=
    inferInstanceAs (OpensMeasurableSpace (ι → ι → ℝ))
  have hm : AEMeasurable A P :=
    AEMeasurable.of_eval fun i => AEMeasurable.of_eval fun j => (hA i j).aemeasurable
  have hd : AEMeasurable (fun a => (A a).det) P :=
    continuous_id.matrix_det.measurable.comp_aemeasurable hm
  have ha : AEMeasurable (fun a => (A a).adjugate i j) P :=
    (continuous_id.matrix_adjugate.matrix_elem i j).measurable.comp_aemeasurable hm
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul] using!
    (hd.inv.mul ha).aestronglyMeasurable

private theorem integrable_inverse_of_bound {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    {P : Measure Ω} {A N : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, Integrable (fun a => A a i j) P)
    (hN : ∀ i j, Integrable (fun a => N a i j) P)
    (hpos : ∀ᵐ a ∂P, (A a).PosDef)
    (hbound : ∀ᵐ a ∂P, (A a)⁻¹ ≤ N a) (i j : ι) :
    Integrable (fun a => (A a)⁻¹ i j) P := by
  apply ((hN i i).add (hN j j) |>.div_const 2).mono'
    (inverse_entry_aestronglyMeasurable hA i j)
  filter_upwards [hpos, hbound] with a hp hb
  rw [Real.norm_eq_abs]
  exact (abs_entry_le_half_diag hp.inv.posSemidef i j).trans
    (by dsimp only [Pi.add_apply]; linarith only [diagonal_mono hb i, diagonal_mono hb j])

/-- Pathwise primal–adjoint order on the actual qualitative coefficient carrier. -/
theorem blockMatLoewnerLE_swapConj_coarseBlock {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d) (a : CoeffSpace d) :
    BlockMatLoewnerLE
      (ofFullBlockMat (toFullBlockMat (blockSwap d) *
        (toFullBlockMat (coarseBlock (HighContrast.adaptedCellTranslate q j y) a))⁻¹ *
        toFullBlockMat (blockSwap d)))
      (coarseBlock (HighContrast.adaptedCellTranslate q j y) a) := by
  have hs := isSymmetricBlockMat_coarseBlockMatrix (HighContrast.adaptedCellTranslate q j y) (⇑a.1)
  have hp := posDef_toFullBlockMat hs
    (Annealed.blockPosDef_coarseBlock_adapted q hq j y a)
  exact (blockMatLoewnerLE_swapConj_inv_iff hs hp).2 (both_signs_coarseBlock q hq j y a)

private theorem matrix_congruence_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Matrix ι ι ℝ} (h : M ≤ N) (B : Matrix ι ι ℝ) : Bᴴ * M * B ≤ Bᴴ * N * B := by
  apply Matrix.le_iff.mpr
  simpa only [mul_sub, sub_mul] using (Matrix.le_iff.mp h).conjTranspose_mul_mul_same B

/-- The inverse entries are integrable by the pathwise order, not by an inverse/mean exchange. -/
theorem integrable_inv_coarseBlock_adapted {d : ℕ} [NeZero d]
    {P : Measure (CoeffSpace d)} (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (hint : HasIntegrableCoarseBlock P (HighContrast.adaptedCellTranslate q j y))
    (α β : BlockCoord d) :
    Integrable (fun a =>
      (toFullBlockMat (coarseBlock (HighContrast.adaptedCellTranslate q j y) a))⁻¹ α β) P := by
  let A := fun a => toFullBlockMat (coarseBlock (HighContrast.adaptedCellTranslate q j y) a)
  let R := toFullBlockMat (blockSwap d)
  have hR : R.IsHermitian := swap_hermitian d
  have hRR : R * R = 1 := swap_square d
  have hp (a : CoeffSpace d) : (A a).PosDef :=
    posDef_toFullBlockMat
      (isSymmetricBlockMat_coarseBlockMatrix _ (⇑a.1))
      (Annealed.blockPosDef_coarseBlock_adapted q hq j y a)
  have hi : ∀ α β, Integrable (fun a => A a α β) P := by
    simpa only [A, toFullBlockMat_eq_blockMatEntry] using! hint
  have hN : ∀ α β, Integrable (fun a => (R * A a * R) α β) P :=
    Annealed.integrable_fullBlock_mul hint R R
  apply integrable_inverse_of_bound hi hN (ae_of_all P hp) _ α β
  apply ae_of_all
  intro a
  have hs : (toFullBlockMat (ofFullBlockMat (R * (A a)⁻¹ * R))).IsHermitian := by
    simpa only [toFullBlockMat_ofFullBlockMat, hR.eq] using
      ((hp a).inv.posSemidef.conjTranspose_mul_mul_same R).1
  have h := (Annealed.fullBlock_le_iff hs (hp a).1).2
    (blockMatLoewnerLE_swapConj_coarseBlock q hq j y a)
  rw [toFullBlockMat_ofFullBlockMat] at h
  have hc := matrix_congruence_mono h R
  rw [hR.eq] at hc
  have he : R * (R * (A a)⁻¹ * R) * R = (A a)⁻¹ := by
    calc
      R * (R * (A a)⁻¹ * R) * R = (R * R) * (A a)⁻¹ * (R * R) := by simp only [mul_assoc]
      _ = _ := by rw [hRR, one_mul, mul_one]
  rwa [he] at hc

private theorem integral_swap_conjugate {d : ℕ} {P : Measure (CoeffSpace d)}
    {A : CoeffSpace d → FullBlockMat d}
    (hA : ∀ α β, Integrable (fun a => A a α β) P) :
    (fun α β => ∫ a, (toFullBlockMat (blockSwap d) * A a *
      toFullBlockMat (blockSwap d)) α β ∂P) =
        toFullBlockMat (blockSwap d) * (Matrix.of fun α β => ∫ a, A a α β ∂P) *
          toFullBlockMat (blockSwap d) := by
  have hi : ∀ α β, Integrable (fun a => blockMatEntry (ofFullBlockMat (A a)) α β) P := by
    simpa only [blockMatEntry_ofFullBlockMat] using hA
  simpa only [toFullBlockMat_ofFullBlockMat, blockMatEntry_ofFullBlockMat] using
    Annealed.integral_fullBlock_mul hi (toFullBlockMat (blockSwap d)) (toFullBlockMat (blockSwap d))

/-- Any invertible grid, including the literal Euclidean grid, with its finite-mean receipt. -/
theorem adaptedMean_swapConj_le_of_integrable {d : ℕ} [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (q : Mat d) (hq : IsUnit q) (j : ℤ)
    (hint : HasIntegrableCoarseBlock P (HighContrast.adaptedCell q j)) :
    BlockMatLoewnerLE
      (ofFullBlockMat (toFullBlockMat (blockSwap d) *
        (toFullBlockMat (adaptedMean P q j))⁻¹ * toFullBlockMat (blockSwap d)))
      (adaptedMean P q j) := by
  let U := HighContrast.adaptedCell q j
  let A := fun a => toFullBlockMat (coarseBlock U a)
  let R := toFullBlockMat (blockSwap d)
  let M := Matrix.of fun α β => ∫ a, (A a)⁻¹ α β ∂P
  have hR : R.IsHermitian := swap_hermitian d
  have hp (a : CoeffSpace d) : Book.Ch02.BlockPosDef (coarseBlock U a) := by
    simpa [U, HighContrast.adaptedCellTranslate] using
      Annealed.blockPosDef_coarseBlock_adapted q hq j 0 a
  have hAp (a : CoeffSpace d) : (A a).PosDef :=
    posDef_toFullBlockMat (isSymmetricBlockMat_coarseBlockMatrix U (⇑a.1)) (hp a)
  have hbar : (toFullBlockMat (adaptedMean P q j)).PosDef :=
    posDef_toFullBlockMat (isSymmetricBlockMat_annealedBlock P U)
      (blockPosDef_annealedBlock hint hp)
  have hA : ∀ α β, Integrable (fun a => A a α β) P := by
    simpa only [A, toFullBlockMat_eq_blockMatEntry] using! hint
  have hAi : ∀ α β, Integrable (fun a => (A a)⁻¹ α β) P := by
    intro α β
    have hi : HasIntegrableCoarseBlock P (HighContrast.adaptedCellTranslate q j 0) := by
      simpa [HighContrast.adaptedCellTranslate] using hint
    simpa [A, U, HighContrast.adaptedCellTranslate] using
      integrable_inv_coarseBlock_adapted q hq j 0 hi α β
  have he : (Matrix.of fun α β => ∫ a, A a α β ∂P) =
      toFullBlockMat (adaptedMean P q j) := by
    simpa only [A, U, toFullBlockMat_eq_blockMatEntry, adaptedMean] using!
      Annealed.fullBlock_integral_coarseBlock P U
  have hM : M.IsHermitian := by
    ext α β
    change (∫ a, (A a)⁻¹ β α ∂P) = ∫ a, (A a)⁻¹ α β ∂P
    apply integral_congr_ae
    exact ae_of_all P fun a => by
      simpa only [conjTranspose_apply, star_trivial] using
        congrArg (fun N => N α β) (hAp a).inv.1
  have hJ : (toFullBlockMat (adaptedMean P q j))⁻¹ ≤ M := by
    apply Matrix.le_iff.mpr
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hM.sub hbar.inv.1) ?_
    intro x
    have hj := inner_inv_integral_le_integral_inner_inv A (ae_of_all P hAp) hA hAi
      (he.symm ▸ hbar) x
    rw [he] at hj
    simpa only [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg] using hj
  have hCJ := matrix_congruence_mono hJ R
  rw [hR.eq] at hCJ
  have hCi : ∀ α β, Integrable (fun a => blockMatEntry
      (ofFullBlockMat (R * (A a)⁻¹ * R)) α β) P := by
    have hi : ∀ α β, Integrable (fun a => blockMatEntry (ofFullBlockMat ((A a)⁻¹)) α β) P := by
      simpa only [blockMatEntry_ofFullBlockMat] using hAi
    simpa only [blockMatEntry_ofFullBlockMat, toFullBlockMat_ofFullBlockMat] using
      Annealed.integrable_fullBlock_mul hi R R
  have hpath : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat (R * (A a)⁻¹ * R)) (coarseBlock U a) :=
    ae_of_all P fun a => by
      simpa [A, U, R, HighContrast.adaptedCellTranslate] using
        blockMatLoewnerLE_swapConj_coarseBlock q hq j 0 a
  have hI := blockMatLoewnerLE_integral hCi hint hpath
  have hcomm := integral_swap_conjugate hAi
  have hmean : ofFullBlockMat (Matrix.of fun α β => ∫ a,
      blockMatEntry (coarseBlock U a) α β ∂P) = adaptedMean P q j := by
    rw [Annealed.fullBlock_integral_coarseBlock]
    exact ofFullBlockMat_toFullBlockMat _
  simp only [blockMatEntry_ofFullBlockMat] at hI
  rw [hcomm, hmean] at hI
  have hC1 : (toFullBlockMat (ofFullBlockMat
      (R * (toFullBlockMat (adaptedMean P q j))⁻¹ * R))).IsHermitian := by
    simpa only [toFullBlockMat_ofFullBlockMat, hR.eq] using
      (hbar.inv.posSemidef.conjTranspose_mul_mul_same R).1
  have hC2 : (toFullBlockMat (ofFullBlockMat (R * M * R))).IsHermitian := by
    simpa only [toFullBlockMat_ofFullBlockMat, hR.eq] using
      Matrix.isHermitian_conjTranspose_mul_mul R hM
  have hB := (Annealed.fullBlock_le_iff hC1 hC2).1 (by
    simpa only [toFullBlockMat_ofFullBlockMat] using hCJ)
  exact fun X => (hB X).trans (hI X)

private theorem determinant_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F G : Matrix ι ι ℝ} (hF : F.PosDef) (hG : G.PosDef) (hGF : G ≤ F) :
    G.det ≤ F.det := by
  let T := matSqrt G⁻¹
  have hT : T.PosDef := Multiscale.matSqrt_inv_posDef_full hG
  have hN : (T * F * T).IsHermitian := by
    simpa only [hT.1.eq] using Matrix.isHermitian_conjTranspose_mul_mul T hF.1
  have hi : (1 : Matrix ι ι ℝ) ≤ T * F * T := Recurrence.one_le_normalize hG hGF
  have ht := (Matrix.le_iff.mp hi).trace_nonneg
  have hd := Recurrence.trace_sub_one_le_det_sub_one hN hi
  have hone : 1 ≤ (T * F * T).det := by linarith only [hd, ht]
  rw [show (T * F * T).det = F.det / G.det from
    Multiscale.det_normalized_eq_div F G hG] at hone
  exact (one_le_div hG.det_pos).mp hone

private theorem one_le_det_of_swapConj {d : ℕ} {F : BlockMat d}
    (hF : (toFullBlockMat F).PosDef)
    (horder : BlockMatLoewnerLE
      (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ *
        toFullBlockMat (blockSwap d))) F) :
    1 ≤ (toFullBlockMat F).det := by
  let R := toFullBlockMat (blockSwap d)
  let A := toFullBlockMat F
  have hR : R.IsHermitian := swap_hermitian d
  have hRR : R.det * R.det = 1 := by
    rw [← Matrix.det_mul, show R * R = 1 from swap_square d, Matrix.det_one]
  have hRu : IsUnit R := R.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr (by
    intro hz
    rw [hz, zero_mul] at hRR
    norm_num at hRR))
  have hG : (R * A⁻¹ * R).PosDef := by
    simpa only [hR.eq] using hF.inv.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_iff_isUnit.mpr hRu)
  have hle : R * A⁻¹ * R ≤ A := by
    have hs : (toFullBlockMat (ofFullBlockMat (R * A⁻¹ * R))).IsHermitian := by
      simpa only [toFullBlockMat_ofFullBlockMat] using hG.1
    simpa only [toFullBlockMat_ofFullBlockMat] using (Annealed.fullBlock_le_iff hs hF.1).2 horder
  have hdet : (R * A⁻¹ * R).det = A.det⁻¹ := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    calc
      R.det * A.det⁻¹ * R.det = (R.det * R.det) * A.det⁻¹ := by ring
      _ = _ := by rw [hRR, one_mul]
  have hd := determinant_mono hF hG hle
  rw [hdet] at hd
  have hpos : 0 < A.det := hF.det_pos
  have hm := mul_le_mul_of_nonneg_left hd hpos.le
  rw [mul_inv_cancel₀ hpos.ne'] at hm
  nlinarith only [hm, hpos]

/-- The annealed primal–adjoint order under the standing stationary dagger law. -/
theorem adaptedMean_swapConj_le {d : ℕ} (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) :
    BlockMatLoewnerLE
      (ofFullBlockMat (toFullBlockMat (blockSwap d) *
        (toFullBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j))⁻¹ *
          toFullBlockMat (blockSwap d)))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j) := by
  let : NeZero d := ⟨by omega⟩
  apply adaptedMean_swapConj_le_of_integrable _ (Geometry.isUnit_roundedGrid hjStar hm)
  simpa [HighContrast.adaptedCellTranslate] using
    Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j 0

/-- The full doubled determinant of the actual adapted mean is at least one. -/
theorem one_le_det_adaptedMean {d : ℕ} (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) :
    1 ≤ (toFullBlockMat (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j)).det := by
  exact one_le_det_of_swapConj
    (Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar m hm j)
    (adaptedMean_swapConj_le hd P γ E Ψ K S hstat hdag jStar hjStar m hm j)

end HCPolySupport.HighContrast.Analysis
