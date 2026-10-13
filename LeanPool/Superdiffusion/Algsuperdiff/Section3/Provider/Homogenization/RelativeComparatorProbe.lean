/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.RelativeNormalization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Block.CompletedSquares
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ToLambdasUpper
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.ObservationScaleFiniteCoverDepth
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.VarianceBridge
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.QuadraticStability.CauchySchwarz
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.NormalizedBlocks
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.FiniteBasis
public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section57.NormalizedResponseEllipticity
public import LeanPool.Superdiffusion.Support.HighContrast.Variance.Projection

/-!
# RelativeComparatorProbe

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Relative comparator probe

This module isolates the deterministic comparator algebra needed by the
finite-corridor mean consumer. Its sole public endpoint controls the actual
same-cutoff relative-origin starred fluctuation probe by the physical cutoff
homogenization error. The consumer imports and applies that endpoint directly.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.Book.Ch02
open _root_.HCPolySupport.Book.Ch05.Section54.VarianceBoundGoodScale
open scoped MatrixOrder

noncomputable section

private theorem coarseStarredInv_comparator_quadratic_sub_one_sq_le
    {d : ℕ} [NeZero d] (R : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d)
    (sigma : Observable.PositiveScalar) (P : BlockVec d)
    (hPunit :
      blockVecDot P
          (blockMatVecMul
            (Book.Ch02.constantBlockMatrix
              (Observable.isotropicComparatorMatrix sigma)) P) = 1) :
    let U : Domain d := Book.Ch02.cubeDomain R
    let a : CoeffOn U := F.coeffOn R
    let AstarInv : BlockMat d := Book.Ch02.coarseStarredBlockMatrixInv U a
    let C0 : BlockMat d :=
      Book.Ch02.constantBlockMatrix (Observable.isotropicComparatorMatrix sigma)
    let Qv : BlockVec d := blockMatVecMul C0 P
    let H : ℝ := Book.Ch02.normalizedBlockResponseMax R F
      (Observable.isotropicComparatorMatrix sigma)
    (blockVecDot Qv (blockMatVecMul AstarInv Qv) - 1) ^ (2 : ℕ) ≤
      6 * (H + H ^ (2 : ℕ)) := by
  let U : Domain d := Book.Ch02.cubeDomain R
  let a : CoeffOn U := F.coeffOn R
  let A : BlockMat d := Book.Ch02.coarseBlockMatrix U a
  let AstarInv : BlockMat d := Book.Ch02.coarseStarredBlockMatrixInv U a
  let Ainv : BlockMat d := Provider.Block.coarseBlockMatrixInv U a
  let C0 : BlockMat d :=
    Book.Ch02.constantBlockMatrix (Observable.isotropicComparatorMatrix sigma)
  let Qv : BlockVec d := blockMatVecMul C0 P
  let Y : BlockVec d := blockMatVecMul Ainv Qv
  let x : ℝ := blockVecDot P (blockMatVecMul A P)
  let r : ℝ := blockVecDot Qv (blockMatVecMul AstarInv Qv)
  let rinv : ℝ := blockVecDot Qv (blockMatVecMul Ainv Qv)
  let H : ℝ := Book.Ch02.normalizedBlockResponseMax R F
    (Observable.isotropicComparatorMatrix sigma)
  have hP_ne : P ≠ 0 := by
    intro hP
    subst P
    norm_num [C0, Qv, blockVecDot, blockMatVecMul, vecDot, matVecMul] at hPunit
  have hQv_ne : Qv ≠ 0 := by
    intro hQv
    have hpair : blockVecDot P Qv = 1 := by
      simpa only [Qv, C0] using hPunit
    rw [hQv] at hpair
    norm_num [blockVecDot, vecDot] at hpair
  have hApos : Book.Ch02.BlockPosDef A := by
    exact (Book.Ch02.blockCoarseMatrixTheory U a).block_matrix_posDef
  have hApsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul A Z) := by
    intro Z
    by_cases hZ : Z = 0
    · subst Z
      simp [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
    · exact (hApos Z hZ).le
  have hA_symm : IsSymmetricBlockMat A := by
    exact Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U a
  have hcancel : blockMatVecMul A Y = Qv := by
    simpa only [A, Y, Ainv] using
      (Provider.Block.blockMatVecMul_coarseBlockMatrix_coarseBlockMatrixInv
        U a Qv)
  have hx_pos : 0 < x := by
    exact hApos P hP_ne
  have hYquad : blockVecDot Y (blockMatVecMul A Y) = rinv := by
    rw [hcancel, blockVecDot_comm]
  have hrinv_nonneg : 0 ≤ rinv := by
    rw [← hYquad]
    exact hApsd Y
  have hcs :=
    abs_blockVecDot_blockMatVecMul_le_of_isSymmetricBlockMat
      hA_symm hApsd P Y
  have hleft : blockVecDot P (blockMatVecMul A Y) = 1 := by
    rw [hcancel]
    simpa only [Qv, C0] using hPunit
  have hright : 0 ≤
      Real.sqrt (blockVecDot P (blockMatVecMul A P)) *
        Real.sqrt (blockVecDot Y (blockMatVecMul A Y)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcs_sq :=
    (sq_le_sq₀ (abs_nonneg (blockVecDot P (blockMatVecMul A Y))) hright).2 hcs
  rw [hleft, abs_one, one_pow, mul_pow, Real.sq_sqrt hx_pos.le,
    hYquad, Real.sq_sqrt hrinv_nonneg] at hcs_sq
  have hprod_inv : 1 ≤ x * rinv := by
    simpa [pow_two] using hcs_sq
  have hrinv_le_r : rinv ≤ r := by
    have hJnonneg := Book.Ch02.doubledResponseJ_nonneg U a Y Qv
    rw [Provider.Block.doubledResponseJ_eq_primal_completed_square] at hJnonneg
    have hdiff := blockVecDot_blockMatVecMul_ofFullBlockMat_sub AstarInv Ainv Qv
    rw [hdiff] at hJnonneg
    have hzero : Y - blockMatVecMul Ainv Qv = 0 := by
      simp [Y]
    rw [hzero] at hJnonneg
    have hzeroquad :
        blockVecDot (0 : BlockVec d)
            (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) 0) = 0 := by
      simp [blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left]
    rw [hzeroquad, mul_zero, add_zero] at hJnonneg
    change 0 ≤ (1 / 2 : ℝ) * (r - rinv) at hJnonneg
    linarith
  have hprod : 1 ≤ x * r := by
    exact hprod_inv.trans (mul_le_mul_of_nonneg_left hrinv_le_r hx_pos.le)
  have hH_nonneg : 0 ≤ H := by
    exact Book.Ch02.normalizedBlockResponseMax_nonneg R F
      (Observable.isotropicComparatorMatrix sigma)
  have hmem :
      Book.Ch02.doubledResponseJ U a P Qv ∈
        Book.Ch02.normalizedBlockResponseValueSet R F
          (Observable.isotropicComparatorMatrix sigma) := by
    simpa only [U, a, Qv, C0] using
      (Book.Ch02.normalizedBlockResponseValueSet_mem_of_constantBlockQuadratic_eq_one
        R F
        (by
          simpa only [Observable.isotropicComparatorMatrix] using
            isEllipticMatrix_scalarMatrix sigma.property)
        P hPunit)
  have hJ_le : Book.Ch02.doubledResponseJ U a P Qv ≤ H := by
    unfold H Book.Ch02.normalizedBlockResponseMax
    exact le_csSup
      (Provider.ErrorComparison.normalizedBlockResponseValueSet_scalarMatrix_bddAbove
        R F sigma.property)
      (by simpa only [Observable.isotropicComparatorMatrix] using hmem)
  have hsum : x + r - 2 ≤ 2 * H := by
    have hsplit := (Book.Ch02.blockCoarseMatrixTheory U a).doubled_response_splitting P Qv
    rw [hsplit] at hJ_le
    have hpair : blockVecDot P Qv = 1 := by
      simpa only [Qv, C0] using hPunit
    rw [hpair] at hJ_le
    change (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * r - 1 ≤ H at hJ_le
    linarith
  have hr_pos : 0 < r := by
    by_contra hr
    have hr_nonpos : r ≤ 0 := le_of_not_gt hr
    have : x * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx_pos.le hr_nonpos
    linarith
  have hf : Provider.ErrorComparison.invMulSubOneSq r ≤ 2 * H := by
    have hprod' : 1 ≤ r * x := by simpa [mul_comm] using hprod
    exact
      (Provider.ErrorComparison.invMulSubOneSq_le_add_sub_two hr_pos hprod').trans
        (by linarith [hsum])
  have hsq : (r - 1) ^ (2 : ℕ) ≤ 2 * H * r := by
    have hmul := mul_le_mul_of_nonneg_left hf hr_pos.le
    rw [Provider.ErrorComparison.invMulSubOneSq, ← mul_assoc,
      mul_inv_cancel₀ hr_pos.ne', one_mul] at hmul
    nlinarith
  have hr_upper : r ≤ 3 / 2 + 3 * H := by
    have hlinear :=
      Provider.ErrorComparison.le_one_add_of_invMulSubOneSq_le
        hr_pos (mul_nonneg (by norm_num) hH_nonneg) (by norm_num : (0 : ℝ) < 2) hf
    nlinarith
  dsimp only
  nlinarith [hsq, mul_nonneg hH_nonneg hH_nonneg]

private theorem fullBlockQuadratic_starredCoarse_sub_comparator_sq_le_of_unit
    {d : ℕ} [NeZero d] (R : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d)
    (sigma : Observable.PositiveScalar) (q : FullBlockVec d)
    (hq : dotProduct q q = 1) :
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
    let A : BlockMat d := Book.Ch02.coarseBlockMatrix
      (Book.Ch02.cubeDomain R) (F.coeffOn R)
    let H : ℝ := Book.Ch02.normalizedBlockResponseMax R F a0
    (fullBlockQuadratic
      (CFC.sqrt B *
        (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect C0)) *
          CFC.sqrt B) q) ^ (2 : ℕ) ≤
      6 * (H + H ^ (2 : ℕ)) := by
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
  let A : BlockMat d := Book.Ch02.coarseBlockMatrix
    (Book.Ch02.cubeDomain R) (F.coeffOn R)
  let S : FullBlockMat d := Book.Ch02.constantFullBlockMatrixSqrt a0
  let D : FullBlockMat d := Book.Ch02.constantFullBlockMatrixInvSqrt a0
  let P : BlockVec d := ofFullBlockVec (Matrix.mulVec D q)
  let Qv : BlockVec d := ofFullBlockVec (Matrix.mulVec S q)
  let H : ℝ := Book.Ch02.normalizedBlockResponseMax R F a0
  have hQv : blockMatVecMul C0 P = Qv := by
    dsimp only [C0, P, Qv, S, D, a0]
    change blockMatVecMul
      (Book.Ch02.constantBlockMatrix (scalarMatrix (d := d) (sigma : ℝ)))
      (ofFullBlockVec (Matrix.mulVec
        (Book.Ch02.constantFullBlockMatrixInvSqrt
          (scalarMatrix (d := d) (sigma : ℝ))) q)) =
      ofFullBlockVec (Matrix.mulVec
        (Book.Ch02.constantFullBlockMatrixSqrt
          (scalarMatrix (d := d) (sigma : ℝ))) q)
    rw [Book.Ch02.constantBlockMatrix_scalarMatrix sigma.property]
    rw [Provider.ErrorComparison.ofFullBlockVec_constantFullBlockMatrixInvSqrt_scalarMatrix
      sigma.property]
    rw [Provider.ErrorComparison.ofFullBlockVec_constantFullBlockMatrixSqrt_scalarMatrix
      sigma.property]
    ext i
    · simp [blockMatVecMul, zero_matVecMul, matVecMul_scalarMatrix]
      field_simp [ne_of_gt (Real.sqrt_pos.2 sigma.property)]
      rw [Real.sq_sqrt sigma.property.le]
    · simp [blockMatVecMul, zero_matVecMul, matVecMul_scalarMatrix]
      field_simp [ne_of_gt (Real.sqrt_pos.2 sigma.property)]
      rw [Real.sq_sqrt sigma.property.le]
      field_simp [ne_of_gt sigma.property]
  have hreflectQv : blockMatVecMul (blockReflect C0) Qv = P := by
    dsimp only [C0, P, Qv, S, D, a0]
    change blockMatVecMul
      (blockReflect
        (Book.Ch02.constantBlockMatrix (scalarMatrix (d := d) (sigma : ℝ))))
      (ofFullBlockVec (Matrix.mulVec
        (Book.Ch02.constantFullBlockMatrixSqrt
          (scalarMatrix (d := d) (sigma : ℝ))) q)) =
      ofFullBlockVec (Matrix.mulVec
        (Book.Ch02.constantFullBlockMatrixInvSqrt
          (scalarMatrix (d := d) (sigma : ℝ))) q)
    rw [Book.Ch02.constantBlockMatrix_scalarMatrix sigma.property]
    rw [Provider.ErrorComparison.ofFullBlockVec_constantFullBlockMatrixSqrt_scalarMatrix
      sigma.property]
    rw [Provider.ErrorComparison.ofFullBlockVec_constantFullBlockMatrixInvSqrt_scalarMatrix
      sigma.property]
    ext i
    · simp [blockReflect, blockMatVecMul, zero_matVecMul, matVecMul_scalarMatrix]
      field_simp [ne_of_gt (Real.sqrt_pos.2 sigma.property)]
      rw [Real.sq_sqrt sigma.property.le]
      field_simp [ne_of_gt sigma.property]
    · simp [blockReflect, blockMatVecMul, zero_matVecMul, matVecMul_scalarMatrix]
      field_simp [ne_of_gt (Real.sqrt_pos.2 sigma.property)]
      rw [Real.sq_sqrt sigma.property.le]
  have hnorm : Book.Ch02.fullBlockVecNormSq q = 1 := by
    simpa [Book.Ch02.fullBlockVecNormSq, dotProduct, pow_two] using hq
  have hpair : blockVecDot P Qv = 1 := by
    have hnormalizers :=
      Book.Ch05.Section57.blockVecDot_scalarConstantNormalizers_eq_fullBlockVecNormSq
        sigma.property q
    rw [← hnorm]
    simpa [P, Qv, S, D, a0, Observable.isotropicComparatorMatrix] using hnormalizers
  have hPunit : blockVecDot P (blockMatVecMul C0 P) = 1 := by
    rw [hQv]
    exact hpair
  have hcore :=
    coarseStarredInv_comparator_quadratic_sub_one_sq_le R F sigma P hPunit
  have hstar :
      Book.Ch02.coarseStarredBlockMatrixInv
          (Book.Ch02.cubeDomain R) (F.coeffOn R) = blockReflect A := by
    simpa only [A] using
      (Book.Ch02.blockCoarseMatrixTheory
        (Book.Ch02.cubeDomain R) (F.coeffOn R)).starred_inverse_formula
  have hSdiag : S = Matrix.diagonal
      (Book.Ch05.Section56.scalarFullBlockSqrtDiag
        (d := d) (sigma : ℝ) (sigma : ℝ)) := by
    dsimp only [S, a0]
    change Book.Ch02.constantFullBlockMatrixSqrt
      (scalarMatrix (d := d) (sigma : ℝ)) = _
    simpa only using
      (Book.Ch05.Section57.constantFullBlockMatrixSqrt_scalarMatrix_eq_scalarFullBlockSqrt
        sigma.property)
  have hquad :
      fullBlockQuadratic
          (S * (toFullBlockMat (blockReflect A) -
            toFullBlockMat (blockReflect C0)) * S) q =
        blockVecDot Qv (blockMatVecMul (blockReflect A) Qv) - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, fullBlockQuadratic_sub]
    rw [hSdiag]
    rw [diagonalForm_eq_dotProduct,
      diagonalForm_eq_dotProduct]
    rw [← hSdiag]
    rw [hreflectQv]
    change blockVecDot Qv (blockMatVecMul (blockReflect A) Qv) -
      blockVecDot Qv P = _
    rw [blockVecDot_comm Qv P, hpair]
  dsimp only
  change (fullBlockQuadratic
    (S * (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect C0)) * S) q) ^
      (2 : ℕ) ≤ 6 * (H + H ^ (2 : ℕ))
  rw [hquad]
  dsimp only at hcore
  change
    (blockVecDot (blockMatVecMul C0 P)
      (blockMatVecMul
        (Book.Ch02.coarseStarredBlockMatrixInv
          (Book.Ch02.cubeDomain R) (F.coeffOn R))
        (blockMatVecMul C0 P)) - 1) ^ (2 : ℕ) ≤
      6 * (H + H ^ (2 : ℕ)) at hcore
  rw [hQv, hstar] at hcore
  exact hcore

private theorem fullBlockQuadratic_starredCoarse_sub_comparator_sq_le
    {d : ℕ} [NeZero d] (R : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d)
    (sigma : Observable.PositiveScalar) (q : FullBlockVec d) :
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
    let A : BlockMat d := Book.Ch02.coarseBlockMatrix
      (Book.Ch02.cubeDomain R) (F.coeffOn R)
    let H : ℝ := Book.Ch02.normalizedBlockResponseMax R F a0
    (fullBlockQuadratic
      (CFC.sqrt B *
        (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect C0)) *
          CFC.sqrt B) q) ^ (2 : ℕ) ≤
      6 * (dotProduct q q) ^ (2 : ℕ) * (H + H ^ (2 : ℕ)) := by
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
  let A : BlockMat d := Book.Ch02.coarseBlockMatrix
    (Book.Ch02.cubeDomain R) (F.coeffOn R)
  let H : ℝ := Book.Ch02.normalizedBlockResponseMax R F a0
  let Mq : FullBlockMat d :=
    CFC.sqrt B *
      (toFullBlockMat (blockReflect A) - toFullBlockMat (blockReflect C0)) *
        CFC.sqrt B
  by_cases hqzero : q = 0
  · subst q
    simp [fullBlockQuadratic, dotProduct]
  · have hdotPos : 0 < dotProduct q q := by
      simpa only [star_trivial] using
        (Matrix.dotProduct_self_star_pos_iff (v := q)).2 hqzero
    let t : ℝ := Real.sqrt (dotProduct q q)
    let u : FullBlockVec d := t⁻¹ • q
    have htPos : 0 < t := Real.sqrt_pos.2 hdotPos
    have htSq : t ^ (2 : ℕ) = dotProduct q q := by
      exact Real.sq_sqrt hdotPos.le
    have hu : dotProduct u u = 1 := by
      dsimp only [u]
      rw [smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      field_simp [htPos.ne']
      nlinarith [htSq]
    have hunit :=
      fullBlockQuadratic_starredCoarse_sub_comparator_sq_le_of_unit
        R F sigma u hu
    have htu : t • u = q := by
      dsimp only [u]
      ext alpha
      simp only [smul_eq_mul, Pi.smul_apply]
      field_simp [htPos.ne']
    have hscale :=
      Book.Ch05.Section57.fullBlockQuadratic_vec_smul Mq t u
    rw [htu] at hscale
    dsimp only at hunit
    change (fullBlockQuadratic Mq u) ^ (2 : ℕ) ≤
      6 * (H + H ^ (2 : ℕ)) at hunit
    dsimp only
    change (fullBlockQuadratic Mq q) ^ (2 : ℕ) ≤
      6 * (dotProduct q q) ^ (2 : ℕ) * (H + H ^ (2 : ℕ))
    calc
      (fullBlockQuadratic Mq q) ^ (2 : ℕ) =
          t ^ (4 : ℕ) * (fullBlockQuadratic Mq u) ^ (2 : ℕ) := by
        rw [hscale]
        ring
      _ ≤ t ^ (4 : ℕ) * (6 * (H + H ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hunit (pow_nonneg htPos.le 4)
      _ = 6 * (dotProduct q q) ^ (2 : ℕ) * (H + H ^ (2 : ℕ)) := by
        rw [show t ^ (4 : ℕ) = (dotProduct q q) ^ (2 : ℕ) by
          nlinarith [htSq]]
        ring

/-- The relative-origin starred comparator probe is controlled by the physical
cutoff homogenization error at the same cutoff. -/
theorem fullBlockQuadratic_starredFluctuation_relativeOrigin_sq_le_error
    {d : ℕ} [NeZero d] (M : ABKModel d) (L : ℤ)
    {s : ℝ} (hs : 0 < s) (omega : Cutoff.CutoffSample d)
    (q : FullBlockVec d) :
    let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
    let h : ℤ := L + c
    let sigma := Annealed.sigmaBar M L
    let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
    let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
    let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
    let R : TriadicCube d := originCube d (-c)
    let aRel : RegCoeffField d :=
      dilateReg (-h) (Cutoff.coefficientCutoff M.nu L omega)
    (fullBlockQuadratic
      (starredFluctuationMatrix B C0 (cubeSet R) aRel) q) ^ (2 : ℕ) ≤
      6 * (dotProduct q q) ^ (2 : ℕ) *
        ((Observable.cutoffHomogenizationErrorRaw M L L s sigma omega) ^ (2 : ℕ) +
          (Observable.cutoffHomogenizationErrorRaw M L L s sigma omega) ^ (4 : ℕ)) := by
  let c : ℤ := Cutoff.cutoffRelativeNormalizationShift d
  let h : ℤ := L + c
  let sigma := Annealed.sigmaBar M L
  let a0 : Mat d := Observable.isotropicComparatorMatrix sigma
  let B : FullBlockMat d := Book.Ch02.constantFullBlockMatrix a0
  let C0 : BlockMat d := Book.Ch02.constantBlockMatrix a0
  let R : TriadicCube d := originCube d (-c)
  let aPhys : RegCoeffField d := Cutoff.coefficientCutoff M.nu L omega
  let haPhys : Book.Ch04.AELocallyUniformlyEllipticField aPhys :=
    Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M L omega
  let aRel : RegCoeffField d := dilateReg (-h) aPhys
  let haRel : Book.Ch04.AELocallyUniformlyEllipticField aRel :=
    Cutoff.aelocallyUniformlyEllipticField_dilateReg haPhys (-h)
  let Fphys : Book.Ch02.TriadicCoeffFamily d :=
    Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aPhys haPhys
  let Frel : Book.Ch02.TriadicCoeffFamily d :=
    Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aRel haRel
  let Fdil : Book.Ch02.TriadicCoeffFamily d :=
    Book.Ch02.TriadicCoeffFamily.dilate (-h) Fphys
  have hR : Book.Ch02.dilateCube (-h) (originCube d L) = R := by
    simp [R, h, c, Book.Ch02.dilateCube, originCube]
  have hrelDil : Book.Ch02.TriadicCoeffFamily.AEEq Frel Fdil := by
    simpa only [Frel, Fdil, Fphys, aRel, haRel] using
      Cutoff.triadicCoeffFamily_dilateReg_aeeq_dilate haPhys (-h)
  have herr :
      Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 2) Frel a0 =
        Observable.cutoffHomogenizationErrorRaw M L L s sigma omega := by
    calc
      _ = Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 2) Fdil a0 :=
        Book.Ch02.HomogenizationErrorOnCube_eq_ofAEEq hrelDil R s
          .infinity (.finite 2) a0
      _ = Book.Ch02.HomogenizationErrorOnCube (originCube d L) s .infinity
          (.finite 2) Fphys a0 := by
        rw [← hR]
        exact Book.Ch02.HomogenizationErrorOnCube_dilate
          (Book.Ch02.TriadicCoeffFamily.isDilation_dilate (-h) Fphys)
          (originCube d L) s .infinity (.finite 2) a0
      _ = Book.Ch02.HomogenizationErrorOnCube (originCube d L) s .infinity
          (.finite 2) (Cutoff.coefficientCutoffTriadicCoeffFamily M L omega) a0 :=
        Book.Ch02.HomogenizationErrorOnCube_eq_ofAEEq
          (Cutoff.coefficientCutoff_canonicalFamily_aeeq M L omega)
          (originCube d L) s .infinity (.finite 2) a0
      _ = Observable.cutoffHomogenizationErrorRaw M L L s sigma omega := by
        rw [Observable.cutoffHomogenizationErrorRaw_characterization]
  have hcoarse : coarseBlockMatrix (cubeSet R) aRel.toFun =
      Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain R) (Frel.coeffOn R) :=
    Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_chapterCoarse
      haRel R
  let H : ℝ := Book.Ch02.normalizedBlockResponseMax R Frel a0
  have hHnonneg : 0 ≤ H :=
    Book.Ch02.normalizedBlockResponseMax_nonneg R Frel a0
  have hHerror : H ≤
      (Observable.cutoffHomogenizationErrorRaw M L L s sigma omega) ^ (2 : ℕ) := by
    have hlocal :=
      Book.Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale_of_le
        R (le_refl R.scale) Frel a0
    have hmax :=
      ObservationScaleFiniteCoverInternal.maxDescendantNormalizedBlockResponseAtDepth_le_error_sq
        R hs Frel a0 0
    calc
      H ≤ Book.Ch02.maxDescendantNormalizedBlockResponseAtScale R R.scale Frel a0 := by
        simpa only [H] using hlocal
      _ ≤ (Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite 2) Frel a0) ^
          (2 : ℕ) := by simpa using hmax
      _ = (Observable.cutoffHomogenizationErrorRaw M L L s sigma omega) ^
          (2 : ℕ) := by rw [herr]
  have hcore :=
    fullBlockQuadratic_starredCoarse_sub_comparator_sq_le R Frel sigma q
  dsimp only at hcore
  have hXeq :
      fullBlockQuadratic (starredFluctuationMatrix B C0 (cubeSet R) aRel) q =
        fullBlockQuadratic
          (CFC.sqrt B *
            (toFullBlockMat (blockReflect
                (Book.Ch02.coarseBlockMatrix
                  (Book.Ch02.cubeDomain R) (Frel.coeffOn R))) -
              toFullBlockMat (blockReflect C0)) *
            CFC.sqrt B) q := by
    simp only [starredFluctuationMatrix, starredInverseCoarseBlockMatrix,
      hcoarse, B, C0]
  have hHsq : H ^ (2 : ℕ) ≤
      (Observable.cutoffHomogenizationErrorRaw M L L s sigma omega) ^ (4 : ℕ) := by
    have hp := pow_le_pow_left₀ hHnonneg hHerror 2
    nlinarith
  dsimp only
  rw [hXeq]
  exact hcore.trans (mul_le_mul_of_nonneg_left
    (add_le_add hHerror hHsq)
    (mul_nonneg (by norm_num) (sq_nonneg (dotProduct q q))))

end

end Algsuperdiff.Section3.Provider.Homogenization
