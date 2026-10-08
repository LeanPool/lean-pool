/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormMaximum
public import LeanPool.HighContrastHomogenization.Geometry.AnnealedSharpOrder

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Energy comparison for the diagonal weak estimate

The energy map is used with a self-dual diagonal metric.  Two successive
relative-size comparisons, reversed by the sharp involution, give the precise
coefficient multiplying the starred coarse response.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-- Two relative-size comparisons reverse under the sharp involution. -/
private theorem matrix_le_mul_relSize_fullBlockSharp [NeZero d]
    {M E A : FullBlockMat d} (hM : M.PosDef) (hE : E.PosDef)
    (hA : A.PosDef) (hMsharp : fullBlockSharp M = M) :
    M ≤ (relSize E M * relSize A E) • fullBlockSharp A := by
  set k : ℝ := relSize E M with hk
  set e : ℝ := relSize A E with he
  have hkpos : 0 < k := by rw [hk]; exact relSize_pos hE hM
  have hepos : 0 < e := by rw [he]; exact relSize_pos hA hE
  have hEM : E ≤ k • M := by
    rw [hk]
    exact le_relSize_smul hE.posSemidef hM
  have hAE : A ≤ e • E := by
    rw [he]
    exact le_relSize_smul hA.posSemidef hE
  have hsharpEM : k⁻¹ • M ≤ fullBlockSharp E := by
    have h := fullBlockSharp_le_fullBlockSharp hE (hM.smul hkpos) hEM
    rwa [fullBlockSharp_smul hM hkpos, hMsharp] at h
  have hMsharpE : M ≤ k • fullBlockSharp E := by
    have h := smul_le_smul_of_le hkpos.le hsharpEM
    rw [smul_smul, mul_inv_cancel₀ hkpos.ne', one_smul] at h
    exact h
  have hsharpAE : e⁻¹ • fullBlockSharp E ≤ fullBlockSharp A := by
    have h := fullBlockSharp_le_fullBlockSharp hA (hE.smul hepos) hAE
    rwa [fullBlockSharp_smul hE hepos] at h
  have hEsharpA : fullBlockSharp E ≤ e • fullBlockSharp A := by
    have h := smul_le_smul_of_le hepos.le hsharpAE
    rw [smul_smul, mul_inv_cancel₀ hepos.ne', one_smul] at h
    exact h
  have hscaled := smul_le_smul_of_le hkpos.le hEsharpA
  rw [smul_smul] at hscaled
  exact hMsharpE.trans hscaled

/-- The diagonal metric is bounded by the sharp response with coefficient
`K_{M,E}^2 |E^{-1/2}AE^{-1/2}|`. -/
theorem diagonalMetric_le_scaled_blockSharp [NeZero d] {m : Mat d} (hm : m.PosDef)
    {E A : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hA : IsSymmetricBlockMat A) (hApd : BlockPosDef A) :
    BlockMatLoewnerLE (blockDiag m m⁻¹)
      (blockScale
        (diagonalWeakMetricFactor m E ^ 2 * blockSize A E)
        (blockSharp A)) := by
  let M : BlockMat d := blockDiag m m⁻¹
  have hMsymm : IsSymmetricBlockMat M :=
    isSymmetricBlockMat_diagonalMetric hm
  have hMpd : BlockPosDef M := blockPosDef_diagonalMetric hm
  have hMfull := posDef_toFullBlockMat hMsymm hMpd
  have hEfull := posDef_toFullBlockMat hE hEpd
  have hAfull := posDef_toFullBlockMat hA hApd
  have hMsharpBlock : blockSharp M = M := by
    rw [blockSharp, blockMatInv_metric_eq_blockReflect
      (isUnit_det_of_posDef hm), blockReflect_blockReflect]
  have hMsharp : fullBlockSharp (toFullBlockMat M) = toFullBlockMat M := by
    rw [← toFullBlockMat_blockSharp, hMsharpBlock]
  have hmatrix := matrix_le_mul_relSize_fullBlockSharp
    hMfull hEfull hAfull hMsharp
  have hk : diagonalWeakMetricFactor m E ^ 2 =
      relSize (toFullBlockMat E) (toFullBlockMat M) := by
    rw [sq_diagonalWeakMetricFactor hm hE]
    exact blockSize_eq_relSize hE hMsymm hMpd hEfull.posSemidef
  have he : blockSize A E =
      relSize (toFullBlockMat A) (toFullBlockMat E) :=
    blockSize_eq_relSize hA hE hEpd hAfull.posSemidef
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale, toFullBlockMat_blockSharp, hk, he]
  exact hmatrix

/-- The starred Chapter 2 coarse response is the sharp of its ordinary coarse
response on the flattened carrier. -/
theorem toFullBlockMat_coarseStarredBlockMatrix_eq_fullBlockSharp
    (U : Domain d) (a : CoeffOn U) :
    toFullBlockMat (Book.Ch02.coarseStarredBlockMatrix U a) =
      fullBlockSharp (toFullBlockMat (Book.Ch02.coarseBlockMatrix U a)) := by
  have hA : (toFullBlockMat (Book.Ch02.coarseBlockMatrix U a)).PosDef :=
    posDef_toFullBlockMat (Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix U a)
      (Book.Ch02.blockCoarseMatrixTheory U a).block_matrix_posDef
  rw [Book.Ch02.coarseStarredBlockMatrix, toFullBlockMat_blockMatInv,
    Book.Ch02.coarseStarredBlockMatrixInv_eq_blockReflect,
    toFullBlockMat_blockReflect, refl_conj_inv hA]

/-- The energy-map comparison coefficient on an aligned cell, expressed only
through its response block and the deterministic reference. -/
theorem diagonalMetric_le_scaled_coarseStarred_adaptedCellAt [NeZero d]
    {q : Mat d} (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ)
    {a : CoeffSpace d} {c : CoeffOn (adaptedDomainAt hq k w)}
    (hc : Book.Ch02.coarseBlockMatrix (adaptedDomainAt hq k w) c =
      adaptedResponse q k w a)
    {m : Mat d} (hm : m.PosDef) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) :
    BlockMatLoewnerLE (blockDiag m m⁻¹)
      (blockScale
        (diagonalWeakMetricFactor m E ^ 2 *
          blockSize (adaptedResponse q k w a) E)
        (Book.Ch02.coarseStarredBlockMatrix (adaptedDomainAt hq k w) c)) := by
  have hbase := diagonalMetric_le_scaled_blockSharp hm hE hEpd
    (Recurrence.isSymmetricBlockMat_adaptedResponse q k w a)
    (Recurrence.blockPosDef_adaptedResponse hq k w a)
  have hstar :
      Book.Ch02.coarseStarredBlockMatrix (adaptedDomainAt hq k w) c =
        blockSharp (adaptedResponse q k w a) := by
    refine toFullBlockMat_injective ?_
    rw [toFullBlockMat_coarseStarredBlockMatrix_eq_fullBlockSharp,
      hc, toFullBlockMat_blockSharp]
  rw [hstar]
  exact hbase

/-- The metric square of the average of a doubled response field on one
aligned cell is controlled by its cell energy. -/
theorem metricBlockNormSq_average_le_adaptedCellAt [NeZero d]
    {q : Mat d} (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ)
    {a : CoeffSpace d} {c : CoeffOn (adaptedDomainAt hq k w)}
    (hc : Book.Ch02.coarseBlockMatrix (adaptedDomainAt hq k w) c =
      adaptedResponse q k w a)
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (adaptedCellAt q k w) c.toCoeffField)
    {Y : DoubledField d}
    (hY : IsDoubledResponseField (adaptedDomainAt hq k w) c Y)
    {m : Mat d} (hm : m.PosDef) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) :
    metricBlockNormSq m
        ((Book.Ch02.averageVec (adaptedDomainAt hq k w) Y.potential,
          Book.Ch02.averageVec (adaptedDomainAt hq k w) Y.flux) : BlockVec d) ≤
      diagonalWeakMetricFactor m E ^ 2 *
        blockSize (adaptedResponse q k w a) E *
          Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
            blockVecDot (Y.eval x)
              (blockMatVecMul (blockMatrixField c x) (Y.eval x))) := by
  have hmap := energy_map_metric_le c hEll hY m
    (mul_nonneg (sq_nonneg _) (PortableHistory.blockSize_nonneg
      (Recurrence.isSymmetricBlockMat_adaptedResponse q k w a) hE hEpd))
    (diagonalMetric_le_scaled_coarseStarred_adaptedCellAt
      hq k w hc hm hE hEpd)
  rw [metricBlockNormSq]
  linarith only [hmap]

end

end Response
end HighContrast
end HCPolySupport
