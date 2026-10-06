/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterCellBounds

/-!
# High-contrast homogenization: Provider.Entry.AdapterCellRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The rows of the Euclidean filling of an adapted cell

*The pathwise rows majorant.*  The rows of a finite range of generations are kept
whole and only the tail below an arbitrary cutoff is paid crudely; this is the
form the averaging of `e.two.grid.whitney.average` consumes.  Only the tail
below the cutoff is paid crudely, in the majorant of `AdapterMajorant`.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The pathwise majorant of the Euclidean filling of a translated adapted
cell.**  The coarse response of the target lies below the weighted rows of the
filling from an arbitrary cutoff up to the starting generation, plus the crude
tail of `AdapterMajorant`, whose coefficient is affine in the source scale. -/
theorem ae_coarseBlock_adaptedCellTranslate_le_rows [NeZero d]
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ} (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {q : Mat d} (hq : q.PosDef) {nn M J : ℤ} {y : Vec d} (hM : 0 ≤ M) (hJn : J ≤ nn)
    (hMsub : adaptedCellTranslate q nn y ⊆ centeredCube d M)
    {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ s, ↑(Z s) = Transport.fillingIndex (1 : Mat d) nn (adaptedCellTranslate q nn y) s) :
    ∀ᵐ a ∂P, toFullBlockMat (coarseBlock (adaptedCellTranslate q nn y) a) ≤
      (∑ r ∈ Finset.Icc J nn, ∑ w ∈ Z r,
        ((volume (adaptedCellAt (1 : Mat d) r w)).toReal /
            (volume (adaptedCellTranslate q nn y)).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) r w) a)) +
        ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
          (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) *
            ((3 : ℝ) ^ (-nn) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) • toFullBlockMat E := by
  classical
  have hg0 : 0 ≤ g := hdag.g_mem.1
  have hg1 : g < 1 := hdag.g_mem.2
  have hinv0 : (0 : ℝ) ≤ (1 - g)⁻¹ := inv_nonneg.mpr (by linarith only [hg1])
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  have hnorm : ‖q⁻¹ * (1 : Mat d)‖ = ‖q⁻¹‖ := by rw [Matrix.mul_one]
  have hEfull : (toFullBlockMat E).PosDef :=
    posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef
  have hCd0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖ := by positivity
  have hth0 : ∀ (r : ℤ) (w : Fin d → ℤ),
      (0 : ℝ) ≤ (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
        (volume (adaptedCellTranslate q nn y)).toReal :=
    fun _ _ => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  filter_upwards [ae_coarseBlock_standardCell_le_of_subset hdag M] with a ha
  have hS0 : 0 ≤ S a := hdag.source_nonneg a
  have hcbel0 : (0 : ℝ) ≤ (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
      (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) *
        ((3 : ℝ) ^ (-nn) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)))) := by
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a := by positivity
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-nn) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)) := by positivity
    exact mul_nonneg hCd0
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hinv0) h1) h2)
  have hcellps : ∀ (r : ℤ) (w : Fin d → ℤ),
      (toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) r w) a)).PosSemidef :=
    fun r w => Transport.posSemidef_toFullBlockMat_coarseBlock
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hone r w)
      (Recurrence.volume_adaptedCellAt_pos hone r w).ne' a
  set Mm : FullBlockMat d :=
    (∑ r ∈ Finset.Icc J nn, ∑ w ∈ Z r,
      ((volume (adaptedCellAt (1 : Mat d) r w)).toReal /
          (volume (adaptedCellTranslate q nn y)).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt (1 : Mat d) r w) a)) +
      ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) *
          ((3 : ℝ) ^ (-nn) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) • toFullBlockMat E with hMm
  have hMps : Mm.PosSemidef := by
    rw [hMm]
    refine Matrix.PosSemidef.add (posSemidef_finsetSum fun r _ => ?_)
      (hEfull.posSemidef.smul hcbel0)
    exact posSemidef_finsetSum fun w _ => (hcellps r w).smul (hth0 r w)
  have hMsym : IsSymmetricBlockMat (ofFullBlockMat Mm) := by
    refine isSymmetricBlockMat_of_posSemidef ?_
    rwa [toFullBlockMat_ofFullBlockMat]
  have hT : ∀ (X : BlockVec d) (J' : ℤ), J' ≤ nn →
      (∑ r ∈ Finset.Icc J' nn, ∑ w ∈ Z r,
        (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
            (volume (adaptedCellTranslate q nn y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt (1 : Mat d) r w) a) X))) ≤
        1 / 2 * blockVecDot X (blockMatVecMul (ofFullBlockMat Mm) X) := by
    intro X J' _
    have hE0 : 0 ≤ 1 / 2 * blockVecDot X (blockMatVecMul E X) := by
      have hx := hEfull.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec X)
      rw [blockVecDot_blockMatVecMul_eq_dotProduct]
      simp only [star_trivial] at hx
      linarith only [hx]
    have hrow0 : ∀ r : ℤ, (0 : ℝ) ≤ ∑ w ∈ Z r,
        (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
            (volume (adaptedCellTranslate q nn y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt (1 : Mat d) r w) a) X)) := fun r =>
      Finset.sum_nonneg fun w _ => mul_nonneg (hth0 r w)
        (Transport.zero_le_blockQuadratic_coarseBlock
          (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hone r w)
          (Recurrence.volume_adaptedCellAt_pos hone r w).ne' a X)
    have hG0 : (0 : ℝ) ≤ 1 / 2 * (((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) *
          ((3 : ℝ) ^ (-nn) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) *
        blockVecDot X (blockMatVecMul E X)) := by
      have hq2 : (0 : ℝ) ≤ blockVecDot X (blockMatVecMul E X) := by linarith only [hE0]
      have := mul_nonneg hcbel0 hq2
      linarith only [this]
    have hbelow : ∀ J'' : ℤ, (∑ r ∈ Finset.Ico J'' J, ∑ w ∈ Z r,
        (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
            (volume (adaptedCellTranslate q nn y)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt (1 : Mat d) r w) a) X))) ≤
        1 / 2 * (((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
          (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ J + (3 : ℝ) ^ M + 3 * S a) *
            ((3 : ℝ) ^ (-nn) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) *
          blockVecDot X (blockMatVecMul E X)) := by
      intro J''
      have hstep : ∀ r ∈ Finset.Ico J'' J,
          (∑ w ∈ Z r, (volume (adaptedCellAt (1 : Mat d) r w)).toReal /
              (volume (adaptedCellTranslate q nn y)).toReal *
            (1 / 2 * blockVecDot X
              (blockMatVecMul (coarseBlock (adaptedCellAt (1 : Mat d) r w) a) X))) ≤
            ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (3 : ℝ) ^ (r - nn)) *
              ((1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-r)) ^ g *
                (1 / 2 * blockVecDot X (blockMatVecMul E X))) := by
        intro r hr
        have hrn : r < nn := lt_of_lt_of_le (Finset.mem_Ico.mp hr).2 hJn
        refine sum_weight_mul_le (mul_nonneg (Real.rpow_nonneg (by positivity) g) hE0)
          (cell_le hZ hMsub ha X) ?_
        have hle := Transport.sum_relative_volume_row_le hq hone hrn (hZ r)
        rw [hnorm] at hle
        exact hle
      refine le_trans (Finset.sum_le_sum hstep) ?_
      have hrw : ∀ r ∈ Finset.Ico J'' J,
          ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (3 : ℝ) ^ (r - nn)) *
              ((1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-r)) ^ g *
                (1 / 2 * blockVecDot X (blockMatVecMul E X)))
            = ((6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
                (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
              ((3 : ℝ) ^ (r - nn) *
                (1 + ((3 : ℝ) ^ M + 3 * S a) * (3 : ℝ) ^ (-r)) ^ g) :=
        fun r _ => by ring
      rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
      have htail := sum_crude_below_le hg0 hg1 hM hS0 nn J J''
      have hfac : (0 : ℝ) ≤ (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) *
          (1 / 2 * blockVecDot X (blockMatVecMul E X)) := mul_nonneg hCd0 hE0
      refine le_trans (mul_le_mul_of_nonneg_left htail hfac) (le_of_eq ?_)
      ring
    rw [hMm, half_blockQuadratic_majorant]
    exact sum_Icc_le_of_belowStart hJn hrow0 hG0 hbelow J'
  have hfinal := le_of_blockMatLoewnerLE (isSymmetricBlockMat_coarseBlock _ a) hMsym
    fun X => Transport.blockQuadratic_coarseBlock_le_of_forall_filling_rows hq hone hZ a X (hT X)
  rw [toFullBlockMat_ofFullBlockMat, hMm] at hfinal
  exact hfinal

end

end Entry
end HighContrast
end HCPolySupport
