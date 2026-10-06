/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioMonotone
public import LeanPool.HighContrastHomogenization.Geometry.CoarseSchurBridge

/-!
# High-contrast homogenization: Geometry.ReferenceAspectRatio

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The reference aspect ratio of `e.coarse.ellipticity` is at least one

The reference block `E` of the coarse ellipticity assumption dominates the coarse
response of every standard aligned cube, with a discount factor `3^{g(m-k)}`
that is one at the scale of the cube itself.  So `E` dominates the coarse
response of a centered triadic cube at some field of the coefficient space,
provided one such field is reachable — which is exactly what a probability law
supplies, since the assumption's bound holds almost surely and the source scale
`S` is finite at every field.

The Schur blocks of a realized coarse response are ordered, so its aspect ratio
is at least one; the aspect ratio is monotone; hence `1 ≤ Π(E)`.  This is the
lower bound `Θ ≥ 1` the reference text uses, obtained without assuming the
ordering of the reference block itself.

The hypothesis that the law is a probability measure is not cosmetic: at the
zero measure the assumption is satisfied by a reference block with `Π = 1/4`,
because nothing is then reachable.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The trivial dilation of a doubled block matrix. -/
theorem blockScale_one (E : BlockMat d) : blockScale 1 E = E := by
  cases E
  simp [blockScale]

/-- Every real number is below some integral power of three. -/
private theorem exists_le_zpow_three (x : ℝ) : ∃ m : ℤ, x ≤ (3 : ℝ) ^ m := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 3)
  exact ⟨(n : ℤ), by rw [zpow_natCast]; exact hn.le⟩

/-- **The assumption is undiscounted at the scale of the cube.**  Taking the
standard aligned cube to be the centered cube itself makes the discount factor
`3^{g(m-k)}` equal to one, so `e.coarse.ellipticity` bounds the coarse
response of `□_m` by the reference block. -/
theorem blockMatLoewnerLE_coarseBlock_centeredCube_of_coarseEllipticityDagger
    {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    ∀ᵐ a ∂P, ∀ m : ℤ, S a ≤ (3 : ℝ) ^ m →
      BlockMatLoewnerLE (coarseBlock (centeredCube d m) a) E := by
  filter_upwards [hdag.coarse_bound] with a ha m hm
  have h := ha m hm m le_rfl 0 (standardCellCenter_zero_mem_centeredCube m m)
  rwa [standardCell_zero, sub_self, mul_zero, Real.rpow_zero, blockScale_one] at h

/-- **The reference aspect ratio is at least one.**  Under
`e.coarse.ellipticity` at a probability law, the reference block dominates
the coarse response of a centered triadic cube at some field of the coefficient
space; that response has ordered Schur blocks, hence aspect ratio at least one,
and the aspect ratio is monotone. -/
theorem one_le_aspectRatio_of_coarseEllipticityDagger [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    1 ≤ aspectRatio E := by
  obtain ⟨a, ha⟩ :=
    (blockMatLoewnerLE_coarseBlock_centeredCube_of_coarseEllipticityDagger hdag).exists
  obtain ⟨m, hm⟩ := exists_le_zpow_three (S a)
  refine le_trans (one_le_aspectRatio_coarseBlock_centeredCube m a) ?_
  exact aspectRatio_mono (isSymmetricBlockMat_coarseBlockMatrix (centeredCube d m) ⇑a.1)
    (blockPosDef_coarseBlock m a) hdag.refBlock_isSymm hdag.refBlock_posDef (ha m hm)

end

end HighContrast
end HCPolySupport
