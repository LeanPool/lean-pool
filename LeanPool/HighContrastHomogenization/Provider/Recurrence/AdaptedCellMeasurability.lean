/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.CellMuMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.Scalarization

/-!
# High-contrast homogenization: Provider.Recurrence.AdaptedCellMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Consumers of the measurability clause over adapted cells

The measurability of the variational coarse block holds unconditionally
on every adapted cell.  This file records what the fixed-grid estimates draw
from it, together with the symmetry of the annealed block, which needs nothing
at all.

The annealed block inherits pathwise symmetry: its entries are integrals of the
entries of the response, and the response is symmetric on every cell, so the
adapted means `E_r^q` are symmetric with no hypothesis.

The scalarization display of `l.fixed.geometry.matrix.averaging` carries a
measurability binder on the `4d²` entries of the *normalized centered* block
`F^{-1/2}(𝐀 - E)F^{-1/2}`.  Normalization and centering are a fixed affine map
of the entries, so that binder is discharged by the measurability clause on
`𝐀(U; ·)` itself.  With the clause now proved on the adapted cells, the display
applies to the centered moment `v_r^q` and to the centered aligned responses
`X_z` of the fixed-grid recurrence with no hypothesis beyond the grid's own.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The annealed block is symmetric -/

/-- **The annealed block of any cell is symmetric.**  Its entries are the
integrals of the entries of the coarse response, which is symmetric pathwise, so
no integrability or measurability hypothesis enters. -/
theorem isSymmetricBlockMat_annealedBlock (P : Measure (CoeffSpace d))
    (U : Set (Vec d)) : IsSymmetricBlockMat (annealedBlock P U) := by
  intro α β
  rw [blockMatEntry_annealedBlock, blockMatEntry_annealedBlock]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a =>
    isSymmetricBlockMat_coarseBlockMatrix U (⇑a.1) α β)

/-- **The adapted mean `E_r^q` is symmetric**, with no hypothesis. -/
theorem isSymmetricBlockMat_adaptedMean (P : Measure (CoeffSpace d)) (q : Mat d)
    (r : ℤ) : IsSymmetricBlockMat (adaptedMean P q r) :=
  isSymmetricBlockMat_annealedBlock P (adaptedCell q r)

/-! ## The normalized centered block is an affine image of the response -/

/-- The entries of a normalized doubled block, expanded as a double sum over the
entries of the block itself. -/
theorem toFullBlockMat_normalizedBlock_apply (H F : BlockMat d) (α β : BlockCoord d) :
    toFullBlockMat (normalizedBlock H F) α β =
      ∑ γ : BlockCoord d, ∑ δ : BlockCoord d,
        matSqrt ((toFullBlockMat F)⁻¹) α δ * toFullBlockMat H δ γ *
          matSqrt ((toFullBlockMat F)⁻¹) γ β := by
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
  simp only [Matrix.mul_apply, Finset.sum_mul]

/-- The entries of a difference of doubled blocks. -/
theorem toFullBlockMat_blockSub_apply (A B : BlockMat d) (α β : BlockCoord d) :
    toFullBlockMat (blockSub A B) α β = toFullBlockMat A α β - toFullBlockMat B α β := by
  cases α <;> cases β <;> rfl

/-- **The measurability binder of the scalarization display is discharged by the
measurability clause.**  The normalized centered block `F^{-1/2}(𝐀 - E)F^{-1/2}`
has entries that are fixed real-linear combinations of the entries of `𝐀`, so
their measurability is exactly `HasMeasurableCoarseBlock`. -/
theorem aestronglyMeasurable_toFullBlockMat_normalizedBlock_blockSub
    {P : Measure (CoeffSpace d)} {U : Set (Vec d)}
    (hmeas : HasMeasurableCoarseBlock P U) (E F : BlockMat d) (α β : BlockCoord d) :
    AEStronglyMeasurable
      (fun a => toFullBlockMat (normalizedBlock (blockSub (coarseBlock U a) E) F) α β) P := by
  have hentry : ∀ γ δ : BlockCoord d,
      AEStronglyMeasurable
        (fun a : CoeffSpace d => toFullBlockMat (coarseBlock U a) δ γ) P :=
    fun γ δ => hmeas δ γ
  have hfun : (fun a : CoeffSpace d =>
        toFullBlockMat (normalizedBlock (blockSub (coarseBlock U a) E) F) α β) =
      fun a : CoeffSpace d => ∑ γ : BlockCoord d, ∑ δ : BlockCoord d,
        matSqrt ((toFullBlockMat F)⁻¹) α δ *
            (toFullBlockMat (coarseBlock U a) δ γ - toFullBlockMat E δ γ) *
          matSqrt ((toFullBlockMat F)⁻¹) γ β := by
    funext a
    rw [toFullBlockMat_normalizedBlock_apply]
    exact Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => by
      rw [toFullBlockMat_blockSub_apply]
  have hsum : AEStronglyMeasurable
      (∑ γ : BlockCoord d, ∑ δ : BlockCoord d, fun a : CoeffSpace d =>
        matSqrt ((toFullBlockMat F)⁻¹) α δ *
            (toFullBlockMat (coarseBlock U a) δ γ - toFullBlockMat E δ γ) *
          matSqrt ((toFullBlockMat F)⁻¹) γ β) P :=
    Finset.aestronglyMeasurable_sum _ fun γ _ =>
      Finset.aestronglyMeasurable_sum _ fun δ _ =>
        (((hentry γ δ).sub aestronglyMeasurable_const).const_mul _).mul_const _
  rw [hfun]
  refine hsum.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only [Finset.sum_apply]

/-! ## The scalarization display on a measurable cell -/

/-! ## The fixed-grid moments -/

end

end Recurrence
end HighContrast
end HCPolySupport
