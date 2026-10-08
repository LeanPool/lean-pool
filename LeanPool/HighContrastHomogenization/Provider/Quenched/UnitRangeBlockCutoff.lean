/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeMeanBlock

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeBlockCutoff

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The local block cutoff

The concentration estimate needs an observable that is bounded, local to its own
cell, below the coarse block at every sample, and equal to the coarse block on
the event that the source has burnt in.  The printed argument uses a smooth
spectral cutoff of the normalized block; the smoothness is there only to bound
the multiplicative derivative that the printed mixing hypothesis asks for, and
unit range supplies exact independence instead.

On this carrier the cutoff may therefore be taken to be the hard one that keeps
the block when all of its entries respect a threshold and discards it otherwise.
It is local, because the branch condition is a finite conjunction of conditions
on entries that are already known to be local; it is bounded by the threshold; it
is below the block at every sample, the discarded branch being the zero block and
the coarse block being positive; and the coarse-ellipticity datum makes the
branch condition hold on the burnt-in event, so nothing is discarded there.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The cutoff -/

open Classical in
/-- The local block cutoff at the level `B`: the block itself when every entry
respects the level, and the zero block otherwise. -/
@[expose]
def blockCutoff (B : ℝ) (H : BlockMat d) : BlockMat d :=
  if ∀ α β : BlockCoord d, |blockMatEntry H α β| ≤ B then H else blockScale 0 H

open Classical in
theorem blockMatEntry_blockCutoff (B : ℝ) (H : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry (blockCutoff B H) α β =
      if ∀ α' β' : BlockCoord d, |blockMatEntry H α' β'| ≤ B then
        blockMatEntry H α β else 0 := by
  rw [blockCutoff]
  split
  · rfl
  · rw [blockMatEntry_blockScale, zero_mul]

/-- The cutoff keeps the block when the level is respected. -/
theorem blockCutoff_eq_self {B : ℝ} {H : BlockMat d}
    (h : ∀ α β : BlockCoord d, |blockMatEntry H α β| ≤ B) : blockCutoff B H = H := by
  rw [blockCutoff, ite_eq_left h]

/-- The cutoff respects its level. -/
theorem abs_blockMatEntry_blockCutoff_le {B : ℝ} (hB : 0 ≤ B) (H : BlockMat d)
    (α β : BlockCoord d) : |blockMatEntry (blockCutoff B H) α β| ≤ B := by
  classical
  rw [blockMatEntry_blockCutoff]
  split
  · rename_i hcond
    exact hcond α β
  · simpa using hB

/-- The cutoff is below the block at every sample. -/
theorem blockMatLoewnerLE_blockCutoff {B : ℝ} {H : BlockMat d}
    (hH : Book.Ch02.BlockPosDef H) : BlockMatLoewnerLE (blockCutoff B H) H := by
  classical
  rw [blockCutoff]
  split
  · exact fun X => le_rfl
  · intro X
    rw [blockVecDot_blockMatVecMul_blockScale, zero_mul]
    have := blockVecDot_nonneg_of_blockPosDef hH X
    linarith only [this]

/-! ## Locality -/

/-! ## The cutoff is inactive on the burnt-in event -/

/-! ## Integrability -/

end

end Quenched
end HighContrast
end HCPolySupport
