/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormMaximum
public import LeanPool.HighContrastHomogenization.Provider.Persistence.EuclideanTransfer
public import LeanPool.HighContrastHomogenization.Provider.Transport.FillingExhaustion
public import LeanPool.HighContrastHomogenization.Provider.Transport.TransportMeanDomination

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.AdaptedCellExcessFilling

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Excess domination through an adapted-cell filling

The maximal filling of one adapted cell by cells of another grid is an
exhaustion in both doubled orientations.  Consequently, a uniform bound on the
weighted excess of every finite set of filling rows passes to the coarse block
of the target cell.  This is the deterministic boundary-layer step used when a
cube response row is compared with a response row on an adapted grid.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem sum_sum_mul {I J : Type*} (R : Finset I) (Z : I → Finset J)
    (f : I → J → ℝ) (c : ℝ) :
    (∑ i ∈ R, ∑ j ∈ Z i, f i j * c) =
      (∑ i ∈ R, ∑ j ∈ Z i, f i j) * c := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]

private theorem blockMatLoewnerLE_one_add_blockExcess
    {H F : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hHps : (toFullBlockMat H).PosSemidef)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) :
    BlockMatLoewnerLE H (blockScale (1 + blockExcess H F) F) := by
  have hsize := Response.blockSize_le_one_add_blockExcess hH hHps hF hFpd
  have hup := (PortableHistory.blockSize_sandwich hH hF hFpd).1
  have hbase : BlockMatLoewnerLE H (blockScale (blockSize H F) F) := by
    refine blockMatLoewnerLE_of_le ?_
    simpa only [toFullBlockMat_blockScale] using hup
  exact Persistence.blockMatLoewnerLE_blockScale_mono hH hF hFpd hsize hbase

private theorem weighted_half_quadratic_le_one_add_blockExcess
    {H F : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hHps : (toFullBlockMat H).PosSemidef)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F)
    {c : ℝ} (hc : 0 ≤ c) (X : BlockVec d) :
    c * (1 / 2 * blockVecDot X (blockMatVecMul H X)) ≤
      c * ((1 + blockExcess H F) *
        (1 / 2 * blockVecDot X (blockMatVecMul F X))) := by
  have hle := blockMatLoewnerLE_one_add_blockExcess hH hHps hF hFpd X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hle
  have hweighted := mul_le_mul_of_nonneg_left hle hc
  exact hweighted.trans_eq (by ring)

private theorem weighted_half_quadratic_reflect_le_one_add_blockExcess
    {H F : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hHps : (toFullBlockMat H).PosSemidef)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F)
    {c : ℝ} (hc : 0 ≤ c) (X : BlockVec d) :
    c * (1 / 2 * blockVecDot X (blockMatVecMul (blockReflect H) X)) ≤
      c * ((1 + blockExcess H F) *
        (1 / 2 * blockVecDot X (blockMatVecMul (blockReflect F) X))) := by
  have hle := Transport.blockMatLoewnerLE_blockReflect
    (blockMatLoewnerLE_one_add_blockExcess hH hHps hF hFpd)
  have hle' : BlockMatLoewnerLE (blockReflect H)
      (blockScale (1 + blockExcess H F) (blockReflect F)) := by
    simpa only [Transport.blockScale_blockReflect] using hle
  have hquad := hle' X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hquad
  have hweighted := mul_le_mul_of_nonneg_left hquad hc
  exact hweighted.trans_eq (by ring)

/-- If every finite collection of rows in a maximal filling has weighted cell
excess at most `E`, then the target cell has excess at most `E`.  The same cell
excess controls the reflected response, so the exhaustion is supplied in both
orientations without a second hypothesis. -/
theorem blockExcess_coarseBlock_adaptedCellTranslate_le_of_filling_rows
    [NeZero d] {p q : Mat d} (hp : p.PosDef) (hq : q.PosDef)
    {n j : ℤ} {y : Vec d} {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ r, ↑(Z r) = Transport.fillingIndex q n (adaptedCellTranslate p j y) r)
    {F : BlockMat d} (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) (a : CoeffSpace d)
    {E : ℝ} (hE : 0 ≤ E)
    (hrows : ∀ J : ℤ, J ≤ n →
      ∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal *
          blockExcess (coarseBlock (adaptedCellAt q r w) a) F ≤ E) :
    blockExcess (coarseBlock (adaptedCellTranslate p j y) a) F ≤ E := by
  classical
  let W : Set (Vec d) := adaptedCellTranslate p j y
  have hFfull : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hF hFpd
  have hFquad : ∀ X : BlockVec d,
      0 ≤ 1 / 2 * blockVecDot X (blockMatVecMul F X) := by
    intro X
    have hqf := hFfull.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec X)
    rw [blockVecDot_blockMatVecMul_eq_dotProduct]
    simp only [star_trivial] at hqf
    linarith only [hqf]
  have hT : ∀ (X : BlockVec d) (J : ℤ), J ≤ n →
      (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X))) ≤
        1 / 2 * blockVecDot X (blockMatVecMul (blockScale (1 + E) F) X) := by
    intro X J hJn
    have hmass := Transport.sum_relative_volume_le_one hp hq
      (R := Finset.Icc J n) hZ
    have hrow := hrows J hJn
    have hcoef :
        (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
          (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate p j y)).toReal *
            (1 + blockExcess (coarseBlock (adaptedCellAt q r w) a) F)) ≤
          1 + E := by
      have hexpand :
          (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
            (volume (adaptedCellAt q r w)).toReal /
                (volume (adaptedCellTranslate p j y)).toReal *
              (1 + blockExcess (coarseBlock (adaptedCellAt q r w) a) F)) =
            (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
              (volume (adaptedCellAt q r w)).toReal /
                (volume (adaptedCellTranslate p j y)).toReal) +
            ∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
              (volume (adaptedCellAt q r w)).toReal /
                  (volume (adaptedCellTranslate p j y)).toReal *
                blockExcess (coarseBlock (adaptedCellAt q r w) a) F := by
        simp_rw [mul_add, mul_one, Finset.sum_add_distrib]
      rw [hexpand]
      linarith only [hmass, hrow]
    have hterm : ∀ r ∈ Finset.Icc J n, ∀ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate p j y)).toReal *
            (1 / 2 * blockVecDot X
              (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X)) ≤
          (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate p j y)).toReal *
            ((1 + blockExcess (coarseBlock (adaptedCellAt q r w) a) F) *
              (1 / 2 * blockVecDot X (blockMatVecMul F X))) := by
      intro r _ w _
      have hcellSym := isSymmetricBlockMat_coarseBlock (adaptedCellAt q r w) a
      have hcellPsd := (posDef_toFullBlockMat hcellSym
        (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq r w a)).posSemidef
      exact weighted_half_quadratic_le_one_add_blockExcess hcellSym hcellPsd hF hFpd
        (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) X
    refine le_trans (Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun w hw =>
      hterm r hr w hw) ?_
    have hfactor :
        (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
          (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate p j y)).toReal *
            ((1 + blockExcess (coarseBlock (adaptedCellAt q r w) a) F) *
              (1 / 2 * blockVecDot X (blockMatVecMul F X)))) =
          (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
            (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate p j y)).toReal *
                (1 + blockExcess (coarseBlock (adaptedCellAt q r w) a) F)) *
              (1 / 2 * blockVecDot X (blockMatVecMul F X)) := by
      simpa only [mul_assoc] using
        sum_sum_mul (Finset.Icc J n) Z
          (fun r w =>
            (volume (adaptedCellAt q r w)).toReal /
                (volume (adaptedCellTranslate p j y)).toReal *
              (1 + blockExcess (coarseBlock (adaptedCellAt q r w) a) F))
          (1 / 2 * blockVecDot X (blockMatVecMul F X))
    rw [hfactor, Sharp.blockVecDot_blockMatVecMul_blockScale]
    exact (mul_le_mul_of_nonneg_right hcoef (hFquad X)).trans_eq (by ring)
  have hTstar : ∀ (X : BlockVec d) (J : ℤ), J ≤ n →
      (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate p j y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseStarInv (adaptedCellAt q r w) a) X))) ≤
        1 / 2 * blockVecDot X
          (blockMatVecMul (blockScale (1 + E) (blockReflect F)) X) := by
    intro X J hJn
    have hmass := Transport.sum_relative_volume_le_one hp hq
      (R := Finset.Icc J n) hZ
    have hrow := hrows J hJn
    have hcoef :
        (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
          (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate p j y)).toReal *
            (1 + blockExcess (coarseBlock (adaptedCellAt q r w) a) F)) ≤
          1 + E := by
      have hexpand :
          (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
            (volume (adaptedCellAt q r w)).toReal /
                (volume (adaptedCellTranslate p j y)).toReal *
              (1 + blockExcess (coarseBlock (adaptedCellAt q r w) a) F)) =
            (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
              (volume (adaptedCellAt q r w)).toReal /
                (volume (adaptedCellTranslate p j y)).toReal) +
            ∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
              (volume (adaptedCellAt q r w)).toReal /
                  (volume (adaptedCellTranslate p j y)).toReal *
                blockExcess (coarseBlock (adaptedCellAt q r w) a) F := by
        simp_rw [mul_add, mul_one, Finset.sum_add_distrib]
      rw [hexpand]
      linarith only [hmass, hrow]
    have hterm : ∀ r ∈ Finset.Icc J n, ∀ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate p j y)).toReal *
            (1 / 2 * blockVecDot X
              (blockMatVecMul (coarseStarInv (adaptedCellAt q r w) a) X)) ≤
          (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate p j y)).toReal *
            ((1 + blockExcess (coarseBlock (adaptedCellAt q r w) a) F) *
              (1 / 2 * blockVecDot X (blockMatVecMul (blockReflect F) X))) := by
      intro r _ w _
      have hcellSym := isSymmetricBlockMat_coarseBlock (adaptedCellAt q r w) a
      have hcellPsd := (posDef_toFullBlockMat hcellSym
        (Recurrence.blockPosDef_coarseBlock_adaptedCellAt hq r w a)).posSemidef
      simpa only [Transport.coarseStarInv_eq_blockReflect] using
        weighted_half_quadratic_reflect_le_one_add_blockExcess hcellSym hcellPsd hF hFpd
          (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) X
    refine le_trans (Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun w hw =>
      hterm r hr w hw) ?_
    have hfactor :
        (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
          (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate p j y)).toReal *
            ((1 + blockExcess (coarseBlock (adaptedCellAt q r w) a) F) *
              (1 / 2 * blockVecDot X (blockMatVecMul (blockReflect F) X)))) =
          (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
            (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate p j y)).toReal *
                (1 + blockExcess (coarseBlock (adaptedCellAt q r w) a) F)) *
              (1 / 2 * blockVecDot X (blockMatVecMul (blockReflect F) X)) := by
      simpa only [mul_assoc] using
        sum_sum_mul (Finset.Icc J n) Z
          (fun r w =>
            (volume (adaptedCellAt q r w)).toReal /
                (volume (adaptedCellTranslate p j y)).toReal *
              (1 + blockExcess (coarseBlock (adaptedCellAt q r w) a) F))
          (1 / 2 * blockVecDot X (blockMatVecMul (blockReflect F) X))
    rw [hfactor, Sharp.blockVecDot_blockMatVecMul_blockScale]
    have hFstarQuad : 0 ≤
        1 / 2 * blockVecDot X (blockMatVecMul (blockReflect F) X) := by
      have hpd := posDef_toFullBlockMat
        (isSymmetricBlockMat_blockReflect hF) (Transport.blockPosDef_blockReflect hFpd)
      have hqf := hpd.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec X)
      rw [blockVecDot_blockMatVecMul_eq_dotProduct]
      simp only [star_trivial] at hqf
      linarith only [hqf]
    exact (mul_le_mul_of_nonneg_right hcoef hFstarQuad).trans_eq (by ring)
  have hexhaust := Transport.grid_transport_exhaustion hp hq hZ a
    (isSymmetricBlockMat_blockScale (1 + E) hF)
    (isSymmetricBlockMat_blockScale (1 + E) (isSymmetricBlockMat_blockReflect hF))
    hT hTstar
  have htargetSym := isSymmetricBlockMat_coarseBlock W a
  have htargetOrder : BlockMatLoewnerLE (coarseBlock W a) (blockScale (1 + E) F) :=
    blockMatLoewnerLE_of_le hexhaust.2.1
  have hrel : relSize (toFullBlockMat (coarseBlock W a)) (toFullBlockMat F) ≤ 1 + E := by
    refine (relSize_le_iff hexhaust.1 hFfull (by linarith only [hE])).mpr ?_
    have hle := le_of_blockMatLoewnerLE htargetSym
      (isSymmetricBlockMat_blockScale (1 + E) hF) htargetOrder
    rwa [toFullBlockMat_blockScale] at hle
  rw [blockExcess_eq htargetSym hF hFpd hexhaust.1]
  exact max_le (by linarith only [hrel]) hE

end

end HighContrast
end HCPolySupport
