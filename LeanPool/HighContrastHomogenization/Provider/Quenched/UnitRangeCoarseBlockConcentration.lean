/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeConcentration

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeCoarseBlockConcentration

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Concentration for the coarse block readouts

The observables the endgame averages are readouts of the coarse block response
of the standard aligned cubes of `e.coarse.ellipticity`.  Two properties are
needed before the concentration-for-sums estimate applies to them: each readout
must be measurable for the local sigma-field of its own cube, and it must be
bounded and centred.

Locality holds for every entry of the coarse block of a bounded open cell of
positive volume, so in particular on the standard aligned cubes.  Boundedness
does not: on the high-contrast coefficient class the coarse block is not
uniformly bounded, its size being controlled only through the reference block
and the source scale.  The estimate is therefore applied to the *truncated*
readout, exactly as the printed derivation of the concentration condition does:
a cutoff at a level `B` is applied first, the truncated readout is centred at its
own mean and normalized by its own range, and the resulting family satisfies the
hypotheses of the concentration estimate with dimensional constants.

The truncation level is a parameter of the statements below; nothing here fixes
it, and no dimensional constant depends on it.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The truncated, centred, normalized readout -/

/-! ## Concentration for truncated local readouts -/

/-! ## The coarse block readout -/

/-- Every entry of the coarse block response of a standard aligned cube is
measurable for the local sigma-field of that cube. -/
theorem measurable_blockMatEntry_coarseBlock_standardCell (k : ℤ) (w : Fin d → ℤ)
    (α β : BlockCoord d) :
    @Measurable (CoeffSpace d) ℝ (coeffSigma d (standardCell d k w)) _
      fun a : CoeffSpace d => blockMatEntry (coarseBlock (standardCell d k w) a) α β := by
  have hU : IsOpenBoundedConvexDomain (standardCell d k w) :=
    isOpenBoundedConvexDomain_openCubeSet (translateCube w (originCube d k))
  have hUvol : 0 < (volume (standardCell d k w)).toReal := by
    change 0 < (volume (openCubeSet (translateCube w (originCube d k)))).toReal
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos _
  exact Recurrence.measurable_blockMatEntry_coarseBlock_coeffSigma hU.isOpen hU.isBoundedDomain
    hUvol α β

end

end Quenched
end HighContrast
end HCPolySupport
