/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.ScaleMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Transport.FillingExhaustion

/-!
# High-contrast homogenization: Provider.Quenched.CoarseExcessMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Measurability of the normalized coarse-block excess

The rows of the annealed-to-quenched endgame
(`e.random.quenched.row`) are built from the normalized
excess of the coarse response over the homogenized block, maximized over the
standard cells centered inside an outer cube.  On the coefficient space the
coarse response is positive semidefinite, so its excess is the positive part of
the relative size already carried by the coarse-block measurability engine.  This
file records that identity and the two measurability statements it yields.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- On a positive semidefinite block the normalized excess is the positive part
of the relative size. -/
theorem blockExcess_eq_max_blockSize_sub_one {H F : BlockMat d}
    (hH : IsSymmetricBlockMat H) (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) (hHps : (toFullBlockMat H).PosSemidef) :
    blockExcess H F = max (blockSize H F - 1) 0 := by
  rw [blockExcess_eq hH hF hFpd hHps, PortableHistory.blockSize_eq_norm hH hF hFpd,
    Recurrence.toFullBlockMat_normalizedBlock]
  rfl

/-- The normalized excess of the coarse response on a bounded open convex cell is
measurable. -/
theorem measurable_blockExcess_coarseBlock [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hUvol : 0 < (volume U).toReal)
    {F : BlockMat d} (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) :
    Measurable fun a : CoeffSpace d => blockExcess (coarseBlock U a) F := by
  have hU0 : volume U ≠ 0 := by
    intro h
    rw [h] at hUvol
    simp only [ENNReal.toReal_zero, lt_self_iff_false] at hUvol
  have heq : (fun a : CoeffSpace d => blockExcess (coarseBlock U a) F) =
      fun a : CoeffSpace d => max (blockSize (coarseBlock U a) F - 1) 0 := by
    funext a
    exact blockExcess_eq_max_blockSize_sub_one
      (isSymmetricBlockMat_coarseBlock U a) hF hFpd
      (Transport.posSemidef_toFullBlockMat_coarseBlock hU hU0 a)
  rw [heq]
  exact ((Window.measurable_blockSize_coarseBlock hU.isOpen hU.isBoundedDomain
    hUvol hF hFpd).sub_const 1).max measurable_const

end

end Quenched
end HighContrast
end HCPolySupport
