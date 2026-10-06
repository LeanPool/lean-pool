/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterCellMean

/-!
# High-contrast homogenization: Provider.Entry.AdapterReverseRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adapted filling of a Euclidean cube

The second estimate of the comparison between adapted and Euclidean cubes:

`F_m - E_n^q ≤ C_AE𝔢_qΓ_{g,S}(n)3^{-(m-n)}𝐄`  for `ℓ_al ≤ n < m`.

Here the Euclidean cube `□_m` is the target and the *adapted* cells fill it, so
the printed cross-grid factor is `|q|`, at most `(100/99)𝔢_q` by
`e.rounded.grid.bounds`.  The rows read as follows.

*The starting row.*  The scale-`n` cells of the filling are integer translates of
`⋄_n^q` — this is the aligned-subdivision property of the coarse block taken
from HC — so each has annealed block exactly `E_n^q`, and the rows together
carry relative volume at most one.

*The rows below the starting scale.*  A cell there is an adapted cell of a lower
generation, which `e.coarse.ellipticity` does not bound directly: the coarse
ellipticity condition speaks of standard cubes.  What bounds it is its own
Euclidean filling, and `Entry.annealedBlock_adaptedCellAt_le` performs that
reading once and for all,
at the cost of the one geometric series `(1-g)^{-1}` the filling carries.  The
cross-grid row weight `C_d|q|3^{r-m}` against that bound is then summed by
`Entry.sum_belowSplit_le` at the printed rate `20Γ_{g,S}(n)3^{-(m-n)}`.

The consequence for the constant is recorded where it is exhibited: this half's
constant carries the extra `(1-g)^{-1}` of the composed reading, so the constant
of the comparison is `C_AE(d,g)` rather than the printed `C_AE(d)`.  The frozen
consumer obligation of `p.response.transfer` binds the constant
after the burn exponent, so the dependence is admissible there.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The pathwise rows majorant of a Euclidean cube -/

/-- **The pathwise majorant of the adapted filling of a Euclidean cube.**  The
coarse response of `□_m` lies below the weighted rows of the adapted filling from
an arbitrary cutoff up to the starting generation, plus a tail whose coefficient
is affine in the source scale.  Each cell below the cutoff is paid by its own
Euclidean filling, through the pathwise elliptic bound of `AdapterCellBounds`. -/
theorem ae_coarseBlock_centeredCube_le_rows [NeZero d] {P : Measure (CoeffSpace d)}
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {q : Mat d} (hq : q.PosDef)
    {n m J : ℤ} (hm : 0 ≤ m) (hJn : J ≤ n) {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ s, ↑(Z s) = Transport.fillingIndex q n (adaptedCellTranslate (1 : Mat d) m 0) s) :
    ∀ᵐ a ∂P, toFullBlockMat (coarseBlock (adaptedCellTranslate (1 : Mat d) m 0) a) ≤
      (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
        ((volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate (1 : Mat d) m 0)).toReal) •
          toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)) +
        ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
          ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
            ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a) *
            (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)))))) •
          toFullBlockMat E := by
  classical
  have hg0 : 0 ≤ g := hdag.g_mem.1
  have hg1 : g < 1 := hdag.g_mem.2
  have hinv0 : (0 : ℝ) ≤ (1 - g)⁻¹ := inv_nonneg.mpr (by linarith only [hg1])
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  have hnorm : ‖(1 : Mat d)⁻¹ * q‖ = ‖q‖ := by rw [inv_one, Matrix.one_mul]
  have hEfull : (toFullBlockMat E).PosDef :=
    posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef
  have hCq0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * ‖q‖ := by positivity
  have hB0 : (0 : ℝ) ≤ 2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1 := by
    have h1 : (0 : ℝ) ≤ 2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) := by positivity
    have := mul_nonneg h1 hinv0
    linarith only [this]
  have hth0 : ∀ (r : ℤ) (w : Fin d → ℤ),
      (0 : ℝ) ≤ (volume (adaptedCellAt q r w)).toReal /
        (volume (adaptedCellTranslate (1 : Mat d) m 0)).toReal :=
    fun _ _ => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have htarget : adaptedCellTranslate (1 : Mat d) m 0 = centeredCube d m :=
    adaptedCellTranslate_one_zero m
  filter_upwards [ae_forall_coarseBlock_adaptedCellAt_le_blockScale hdag hq hm] with a ha
  have hS0 : 0 ≤ S a := hdag.source_nonneg a
  have hA0 : (0 : ℝ) ≤ (3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a := by positivity
  have hcbel0 : (0 : ℝ) ≤ (6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
      ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
        ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a) *
        (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))))) := by
    have h2 : (0 : ℝ) ≤ 2 * (1 - g)⁻¹ *
        ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g))) := by
      have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)) := by positivity
      exact mul_nonneg (mul_nonneg (by norm_num) hinv0) h3
    exact mul_nonneg hCq0 (mul_nonneg (mul_nonneg hB0 hA0) h2)
  have hcellps : ∀ (r : ℤ) (w : Fin d → ℤ),
      (toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)).PosSemidef :=
    fun r w => Transport.posSemidef_toFullBlockMat_coarseBlock
      (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq r w)
      (Recurrence.volume_adaptedCellAt_pos hq r w).ne' a
  set Mm : FullBlockMat d :=
    (∑ r ∈ Finset.Icc J n, ∑ w ∈ Z r,
      ((volume (adaptedCellAt q r w)).toReal /
          (volume (adaptedCellTranslate (1 : Mat d) m 0)).toReal) •
        toFullBlockMat (coarseBlock (adaptedCellAt q r w) a)) +
      ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
        ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
          ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a) *
          (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)))))) •
        toFullBlockMat E with hMm
  have hMps : Mm.PosSemidef := by
    rw [hMm]
    refine Matrix.PosSemidef.add (posSemidef_finsetSum fun r _ => ?_)
      (hEfull.posSemidef.smul hcbel0)
    exact posSemidef_finsetSum fun w _ => (hcellps r w).smul (hth0 r w)
  have hMsym : IsSymmetricBlockMat (ofFullBlockMat Mm) := by
    refine isSymmetricBlockMat_of_posSemidef ?_
    rwa [toFullBlockMat_ofFullBlockMat]
  have hT : ∀ (X : BlockVec d) (J' : ℤ), J' ≤ n →
      (∑ r ∈ Finset.Icc J' n, ∑ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate (1 : Mat d) m 0)).toReal *
          (1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X))) ≤
        1 / 2 * blockVecDot X (blockMatVecMul (ofFullBlockMat Mm) X) := by
    intro X J' _
    have hE0 : 0 ≤ 1 / 2 * blockVecDot X (blockMatVecMul E X) := by
      have hx := hEfull.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec X)
      rw [blockVecDot_blockMatVecMul_eq_dotProduct]
      simp only [star_trivial] at hx
      linarith only [hx]
    have hrow0 : ∀ r : ℤ, (0 : ℝ) ≤ ∑ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate (1 : Mat d) m 0)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X)) := fun r =>
      Finset.sum_nonneg fun w _ => mul_nonneg (hth0 r w)
        (Transport.zero_le_blockQuadratic_coarseBlock
          (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq r w)
          (Recurrence.volume_adaptedCellAt_pos hq r w).ne' a X)
    have hG0 : (0 : ℝ) ≤ 1 / 2 * (((6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
        ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
          ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a) *
          (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)))))) *
        blockVecDot X (blockMatVecMul E X)) := by
      have hq2 : (0 : ℝ) ≤ blockVecDot X (blockMatVecMul E X) := by linarith only [hE0]
      have := mul_nonneg hcbel0 hq2
      linarith only [this]
    have hbelow : ∀ J'' : ℤ, (∑ r ∈ Finset.Ico J'' J, ∑ w ∈ Z r,
        (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellTranslate (1 : Mat d) m 0)).toReal *
          (1 / 2 * blockVecDot X
            (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X))) ≤
        1 / 2 * (((6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
          ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
            ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a) *
            (2 * (1 - g)⁻¹ * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ ((J : ℝ) * (1 - g)))))) *
          blockVecDot X (blockMatVecMul E X)) := by
      intro J''
      have hstep : ∀ r ∈ Finset.Ico J'' J,
          (∑ w ∈ Z r, (volume (adaptedCellAt q r w)).toReal /
              (volume (adaptedCellTranslate (1 : Mat d) m 0)).toReal *
            (1 / 2 * blockVecDot X
              (blockMatVecMul (coarseBlock (adaptedCellAt q r w) a) X))) ≤
            ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) * (3 : ℝ) ^ (r - m)) *
              (((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
                  ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a)) *
                (((3 : ℝ) ^ (-r)) ^ g *
                  (1 / 2 * blockVecDot X (blockMatVecMul E X)))) := by
        intro r hr
        have hrJ : r < J := (Finset.mem_Ico.mp hr).2
        have hrn : r < n := lt_of_lt_of_le hrJ hJn
        refine sum_weight_mul_le ?_ ?_ ?_
        · exact mul_nonneg (mul_nonneg hB0 hA0)
            (mul_nonneg (Real.rpow_nonneg (by positivity) g) hE0)
        · intro w hw
          have hmem : w ∈ Transport.fillingIndex q n (adaptedCellTranslate (1 : Mat d) m 0) r := by
            rw [← hZ r]
            exact Finset.mem_coe.mpr hw
          have hsub : adaptedCellAt q r w ⊆ centeredCube d m := by
            rw [← htarget]
            exact Transport.adaptedCellAt_subset_of_mem_fillingIndex hmem
          have hcell := ha r w hsub X
          rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hcell
          have hmono : (2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
              ((3 : ℝ) ^ (-r)) ^ g * ((3 : ℝ) ^ r + (3 : ℝ) ^ m + 3 * S a) *
              (1 / 2 * blockVecDot X (blockMatVecMul E X)) ≤
              ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
                  ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a)) *
                (((3 : ℝ) ^ (-r)) ^ g *
                  (1 / 2 * blockVecDot X (blockMatVecMul E X))) := by
            have hrJle : (3 : ℝ) ^ r ≤ (3 : ℝ) ^ J :=
              zpow_le_zpow_right₀ (by norm_num) (le_of_lt hrJ)
            have hfac : (0 : ℝ) ≤ (2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
                (((3 : ℝ) ^ (-r)) ^ g *
                  (1 / 2 * blockVecDot X (blockMatVecMul E X))) :=
              mul_nonneg hB0 (mul_nonneg (Real.rpow_nonneg (by positivity) g) hE0)
            nlinarith only [hrJle, hfac]
          linarith only [hcell, hmono]
        · have hle := Transport.sum_relative_volume_row_le hone hq hrn (hZ r)
          rw [hnorm] at hle
          exact hle
      refine le_trans (Finset.sum_le_sum hstep) ?_
      have hrw : ∀ r ∈ Finset.Ico J'' J,
          ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) * (3 : ℝ) ^ (r - m)) *
              (((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
                  ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a)) *
                (((3 : ℝ) ^ (-r)) ^ g *
                  (1 / 2 * blockVecDot X (blockMatVecMul E X))))
            = ((6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
                ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
                  ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a)) *
                (1 / 2 * blockVecDot X (blockMatVecMul E X))) *
              ((3 : ℝ) ^ (r - m) * ((3 : ℝ) ^ (-r)) ^ g) :=
        fun r _ => by ring
      rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
      have htail := sum_crude_zpow_below_le hg0 hg1 m J J''
      have hfac : (0 : ℝ) ≤ (6 * (d : ℝ) * Real.sqrt d * ‖q‖) *
          ((2 * (6 * (d : ℝ) * Real.sqrt d * ‖q⁻¹‖) * (1 - g)⁻¹ + 1) *
            ((3 : ℝ) ^ J + (3 : ℝ) ^ m + 3 * S a)) *
          (1 / 2 * blockVecDot X (blockMatVecMul E X)) :=
        mul_nonneg (mul_nonneg hCq0 (mul_nonneg hB0 hA0)) hE0
      refine le_trans (mul_le_mul_of_nonneg_left htail hfac) (le_of_eq ?_)
      ring
    rw [hMm, half_blockQuadratic_majorant]
    exact sum_Icc_le_of_belowStart hJn hrow0 hG0 hbelow J'
  have hfinal := le_of_blockMatLoewnerLE (isSymmetricBlockMat_coarseBlock _ a) hMsym
    fun X => Transport.blockQuadratic_coarseBlock_le_of_forall_filling_rows hone hq hZ a X (hT X)
  rw [toFullBlockMat_ofFullBlockMat, hMm] at hfinal
  exact hfinal
end

end Entry
end HighContrast
end HCPolySupport
