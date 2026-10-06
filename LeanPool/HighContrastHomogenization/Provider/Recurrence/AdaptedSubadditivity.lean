/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedResponseSubadditivity
public import LeanPool.HighContrastHomogenization.Geometry.BlockBridge

/-!
# High-contrast homogenization: Provider.Recurrence.AdaptedSubadditivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coarse block is subadditive over the aligned subdivision

This is the subadditivity among the coarse-block properties taken from HC, in
the form the fixed-grid recurrence consumes it at its averaging step: for a
rounded grid `q`, scales `j ≤ p`, and the aligned subdivision of `⋄_p^q` into
its `3^{d(p-j)}` scale-`j` children,
`𝐀(⋄_p^q) ≤ 3^{-d(p-j)} Σ_w 𝐀(z_w + ⋄_j^q)`, which is the first display of
`e.fixed.geometry.parent.child` with the uniform weights `|U_i| / |U|` of a
subdivision into cells of equal volume.

Nothing here is specific to the grid beyond the geometry already recorded: the
children are nonempty bounded open convex domains contained in the parent,
pairwise disjoint, and covering the parent up to a null set, which is exactly the
hypothesis of the general subadditivity of the companion file; and they are
translates of one another, so their common volume collapses the printed weight
`|U_i| / |U|` to `3^{-d(p-j)}`.  A field of the coefficient space enters through a
measurable everywhere elliptic representative, which changes no coarse block.

The conclusion is recorded twice: as the quadratic-form inequality that defines
the Loewner order on doubled blocks, and as the Loewner inequality itself between
the flattened matrices, where the average on the right is the honest matrix
average of the printed display.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The size of the aligned subdivision -/

/-- The index set of the aligned subdivision has `3^{d(p-j)}` elements, so it is
nonempty. -/
theorem card_alignedIndex {q : Mat d} (hq : q.PosDef) {j p : ℤ} (hjp : j ≤ p)
    {Z : Finset (Fin d → ℤ)}
    (hZ : (↑Z : Set (Fin d → ℤ)) = {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p}) :
    Z.card = 3 ^ (d * (p - j).toNat) := by
  rw [← Set.ncard_coe_finset, hZ]
  exact ncard_adaptedCellCenter_mem hq hjp

/-! ## The printed display, as a quadratic-form inequality -/

/-- **Subadditivity of the coarse block over the aligned subdivision.**  This is
`e.fixed.geometry.parent.child` at the aligned subdivision of the adapted cubes,
in the quadratic form that defines the Loewner order on doubled blocks. -/
theorem coarseBlock_adaptedCell_le_average [NeZero d] {q : Mat d} (hq : q.PosDef)
    {j p : ℤ} (hjp : j ≤ p) {Z : Finset (Fin d → ℤ)}
    (hZ : (↑Z : Set (Fin d → ℤ)) = {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p})
    (a : CoeffSpace d) (X : BlockVec d) :
    1 / 2 * blockVecDot X (blockMatVecMul (coarseBlock (adaptedCell q p) a) X) ≤
      (Z.card : ℝ)⁻¹ *
        ∑ w ∈ Z, 1 / 2 *
          blockVecDot X (blockMatVecMul (coarseBlock (adaptedCellAt q j w) a) X) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hfm, hfell, hae⟩ :=
    exists_pointwise_elliptic_representative a.2
      (isOpenBoundedConvexDomain_adaptedCell hq p).isBoundedDomain.isBounded
  have hrep : ∀ U : Set (Vec d), coarseBlock U a = coarseBlockMatrix U f :=
    fun U => coarseBlock_eq_of_ae_eq a hae
  have hcardpos : (0 : ℝ) < (Z.card : ℝ) := by
    have : 0 < Z.card := by rw [card_alignedIndex hq hjp hZ]; positivity
    exact_mod_cast this
  have hmemZ : ∀ w ∈ Z, adaptedCellCenter q j w ∈ adaptedCell q p := by
    intro w hw
    have hwZ : w ∈ (↑Z : Set (Fin d → ℤ)) := Finset.mem_coe.mpr hw
    rwa [hZ] at hwZ
  have hc : ∀ w ∈ Z, IsOpenBoundedConvexDomain (adaptedCellAt q j w) :=
    fun w _ => isOpenBoundedConvexDomain_adaptedCellAt hq j w
  have hsub : ∀ w ∈ Z, adaptedCellAt q j w ⊆ adaptedCell q p :=
    fun w hw => adaptedCellAt_subset_adaptedCell hq hjp (hmemZ w hw)
  have hdisj : (↑Z : Set (Fin d → ℤ)).PairwiseDisjoint (adaptedCellAt q j) :=
    fun w _ w' _ hww => disjoint_adaptedCellAt hq j hww
  have hnull : volume (adaptedCell q p \
      ⋃ w ∈ (↑Z : Set (Fin d → ℤ)), adaptedCellAt q j w) = 0 := by
    rw [hZ]
    exact volume_adaptedCell_diff_iUnion_adaptedCellAt hq hjp
  have hcell0 : ∀ w ∈ Z, volume (adaptedCellAt q j w) ≠ 0 :=
    fun w _ => (volume_adaptedCellAt_pos hq j w).ne'
  have hparent : volume (adaptedCell q p) = Z.card • volume (adaptedCell q j) := by
    rw [measure_eq_sum_of_aePartition (fun w hw => (hc w hw).isOpen.measurableSet) hsub
      hdisj hnull, Finset.sum_congr rfl fun w _ => volume_adaptedCellAt q j w,
      Finset.sum_const]
  have hweight : ∀ w ∈ Z, (volume (adaptedCellAt q j w)).toReal /
      (volume (adaptedCell q p)).toReal = (Z.card : ℝ)⁻¹ := by
    intro w _
    have hjpos : (0 : ℝ) < (volume (adaptedCell q j)).toReal :=
      toReal_volume_adaptedCell_pos hq j
    rw [volume_adaptedCellAt, hparent, nsmul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_natCast]
    field_simp
  have hbase := blockQuadratic_le_sum_weight_of_aePartition (lam := lam) (Lam := Lam)
    (isOpenBoundedConvexDomain_adaptedCell hq p)
    (isEllipticFieldOn_of_measurable hfm hfell
      (isOpenBoundedConvexDomain_adaptedCell hq p).isOpen.measurableSet)
    (volume_adaptedCell_pos hq p).ne' hc hsub hdisj hnull hcell0 X
  simp only [hrep]
  refine le_trans hbase (le_of_eq ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w hw => by rw [hweight w hw]

/-! ## The printed display, as a Loewner inequality of matrices -/

/-- **`𝐀(⋄_p^q) ≤ 3^{-d(p-j)} Σ_w 𝐀(z_w + ⋄_j^q)`.**  The first display of
`e.fixed.geometry.parent.child` over the aligned subdivision, in the Loewner
order of the flattened doubled blocks. -/
theorem toFullBlockMat_coarseBlock_adaptedCell_le_average [NeZero d] {q : Mat d}
    (hq : q.PosDef) {j p : ℤ} (hjp : j ≤ p) {Z : Finset (Fin d → ℤ)}
    (hZ : (↑Z : Set (Fin d → ℤ)) = {w : Fin d → ℤ | adaptedCellCenter q j w ∈ adaptedCell q p})
    (a : CoeffSpace d) :
    toFullBlockMat (coarseBlock (adaptedCell q p) a) ≤
      (Z.card : ℝ)⁻¹ • ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) := by
  classical
  have hHermCell : ∀ w : Fin d → ℤ,
      (toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)).IsHermitian :=
    fun w => isHermitian_toFullBlockMat (isSymmetricBlockMat_coarseBlockMatrix _ _)
  have hHermS :
      (∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)).IsHermitian :=
    Finset.sum_induction _ Matrix.IsHermitian (fun _ _ => Matrix.IsHermitian.add)
      Matrix.isHermitian_zero fun w _ => hHermCell w
  have hHermAvg :
      ((Z.card : ℝ)⁻¹ •
        ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a)).IsHermitian := by
    show ((Z.card : ℝ)⁻¹ • _)ᴴ = _
    rw [Matrix.conjTranspose_smul, hHermS, star_trivial]
  have hHermP : (toFullBlockMat (coarseBlock (adaptedCell q p) a)).IsHermitian :=
    isHermitian_toFullBlockMat (isSymmetricBlockMat_coarseBlockMatrix _ _)
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hHermAvg.sub hHermP) fun x => ?_)
  have hxA : ∀ A : BlockMat d, x ⬝ᵥ toFullBlockMat A *ᵥ x =
      blockVecDot (ofFullBlockVec x) (blockMatVecMul A (ofFullBlockVec x)) := by
    intro A
    rw [blockVecDot_blockMatVecMul_eq_dotProduct, toFullBlockVec_ofFullBlockVec]
  have hquad := coarseBlock_adaptedCell_le_average hq hjp hZ a (ofFullBlockVec x)
  have hhalf : ∑ w ∈ Z, 1 / 2 *
        blockVecDot (ofFullBlockVec x)
          (blockMatVecMul (coarseBlock (adaptedCellAt q j w) a) (ofFullBlockVec x)) =
      1 / 2 * ∑ w ∈ Z,
        blockVecDot (ofFullBlockVec x)
          (blockMatVecMul (coarseBlock (adaptedCellAt q j w) a) (ofFullBlockVec x)) := by
    rw [Finset.mul_sum]
  rw [Matrix.sub_mulVec, dotProduct_sub]
  simp only [star_trivial]
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sum_mulVec, dotProduct_sum, smul_eq_mul,
    hxA]
  simp only [hxA]
  rw [hhalf] at hquad
  linarith only [hquad]

/-! ## The positivity and subadditivity clauses together -/

end

end Recurrence
end HighContrast
end HCPolySupport
