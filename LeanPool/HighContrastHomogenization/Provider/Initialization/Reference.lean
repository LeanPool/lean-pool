/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio
public import LeanPool.HighContrastHomogenization.Geometry.SizeAlignment
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockOrder

/-!
# High-contrast homogenization: Provider.Initialization.Reference

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Reference-block facts used by source initialization

The coarse ellipticity assumption reaches an actual centered coarse block.
That block is self-dominating under sharp, and sharp reverses the reference
comparison, which yields the printed order `E♯ ≤ E`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Initialization

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

private theorem exists_le_zpow_three (x : ℝ) : ∃ m : ℤ, x ≤ (3 : ℝ) ^ m := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 3)
  exact ⟨(n : ℤ), by rw [zpow_natCast]; exact hn.le⟩

/-- The reference block dominates its sharp whenever it occurs in a coarse
ellipticity assumption at a probability law. -/
theorem blockMatLoewnerLE_blockSharp_reference [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    BlockMatLoewnerLE (blockSharp E) E := by
  obtain ⟨a, ha⟩ :=
    (blockMatLoewnerLE_coarseBlock_centeredCube_of_coarseEllipticityDagger hdag).exists
  obtain ⟨m, hm⟩ := exists_le_zpow_three (S a)
  have hAE : BlockMatLoewnerLE (coarseBlock (centeredCube d m) a) E := ha m hm
  have hAsymm : IsSymmetricBlockMat (coarseBlock (centeredCube d m) a) :=
    isSymmetricBlockMat_coarseBlockMatrix _ _
  have hApd : Book.Ch02.BlockPosDef (coarseBlock (centeredCube d m) a) :=
    blockPosDef_coarseBlock m a
  have hAsharp : BlockMatLoewnerLE
      (blockSharp (coarseBlock (centeredCube d m) a))
      (coarseBlock (centeredCube d m) a) :=
    Sharp.blockMatLoewnerLE_blockSharp_coarseBlock_of_nonempty
      (isOpenBoundedConvexDomain_openCubeSet (originCube d m))
      ⟨standardCellCenter (d := d) m 0,
        standardCellCenter_zero_mem_centeredCube m m⟩ a
  have hreverse : BlockMatLoewnerLE (blockSharp E)
      (blockSharp (coarseBlock (centeredCube d m) a)) :=
    blockMatLoewnerLE_blockSharp_of_le hAsymm hdag.refBlock_isSymm hApd
      hdag.refBlock_posDef hAE
  exact hreverse.trans (hAsharp.trans hAE)

/-- A positive block above its sharp has reference ratio at least one. -/
theorem one_le_kappaRef {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    [Nonempty (Fin d)] :
    1 ≤ kappaRef E := by
  have hEfull : (toFullBlockMat E).PosDef := posDef_toFullBlockMat hE hEpd
  have hsharpFull : (toFullBlockMat (blockSharp E)).PosDef := by
    rw [toFullBlockMat_blockSharp]
    exact posDef_fullBlockSharp hEfull
  have hsharpSymm : IsSymmetricBlockMat (blockSharp E) :=
    isSymmetricBlockMat_of_posSemidef hsharpFull.posSemidef
  have hsharpPd : Book.Ch02.BlockPosDef (blockSharp E) :=
    (blockPosDef_iff_posDef hsharpSymm).mpr hsharpFull
  rw [kappaRef, blockSize_eq_relSize hE hsharpSymm hsharpPd hEfull.posSemidef]
  calc
    1 = relSize (toFullBlockMat (blockSharp E))
        (toFullBlockMat (blockSharp E)) := (relSize_self_eq_one hsharpFull).symm
    _ ≤ relSize (toFullBlockMat E) (toFullBlockMat (blockSharp E)) :=
      relSize_mono_left hsharpFull.posSemidef hEfull.posSemidef hsharpFull
        (le_of_blockMatLoewnerLE hsharpSymm hE hsharp)

/-- The reference block is bounded by its sharp with the intrinsic reference
ratio as the exact dilation. -/
theorem blockMatLoewnerLE_reference_kappaRef_blockSharp
    {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) :
    BlockMatLoewnerLE E (blockScale (kappaRef E) (blockSharp E)) := by
  have hEfull : (toFullBlockMat E).PosDef := posDef_toFullBlockMat hE hEpd
  have hsharpFull : (toFullBlockMat (blockSharp E)).PosDef := by
    rw [toFullBlockMat_blockSharp]
    exact posDef_fullBlockSharp hEfull
  have hsharpSymm : IsSymmetricBlockMat (blockSharp E) :=
    isSymmetricBlockMat_of_posSemidef hsharpFull.posSemidef
  have hsharpPd : Book.Ch02.BlockPosDef (blockSharp E) :=
    (blockPosDef_iff_posDef hsharpSymm).mpr hsharpFull
  refine blockMatLoewnerLE_of_le ?_
  rw [kappaRef, blockSize_eq_relSize hE hsharpSymm hsharpPd hEfull.posSemidef,
    toFullBlockMat_blockScale]
  exact le_relSize_smul hEfull.posSemidef hsharpFull

/-- The identity-grid constant is at least one under the reference sharp
order. -/
theorem one_le_initIdentityConst {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    [Nonempty (Fin d)] :
    1 ≤ initIdentityConst E := by
  have hkappa := one_le_kappaRef hE hEpd hsharp
  rw [initIdentityConst]
  linarith only [hkappa]

/-- The last reference comparison is the arithmetic consequence of the two
intrinsic-contrast comparisons preceding it. -/
theorem one_add_six_refContrast_sub_one_le {E : BlockMat d}
    (haspect : refContrast E ≤ aspectRatio E) :
    1 + 6 * (refContrast E - 1) ≤ 6 * aspectRatio E := by
  linarith only [haspect]

/-- The printed identity-grid upper bound follows once the canonical entry
ratio is bounded by six times the aspect ratio. -/
theorem initIdentityConst_le {E : BlockMat d}
    (hkappa : kappaRef E ≤ 6 * aspectRatio E) :
    initIdentityConst E ≤ 24 * aspectRatio E := by
  rw [initIdentityConst]
  linarith only [hkappa]

end

end Initialization
end HighContrast
end HCPolySupport
