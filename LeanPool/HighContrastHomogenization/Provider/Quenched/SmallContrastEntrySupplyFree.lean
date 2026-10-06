/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupply
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSingleCellVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourceMomentDeepened
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceLagged

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEntrySupplyFree

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The free-threshold entry supply

The corrected (s-free) analogue of `entry_lagged_variance_supply_of_block_split`: the
window-coupled moment availability `𝔪₂(K) ≤ 3^{jb+G-s_K}` is replaced by
the **burn-in condition** — the anchor sits deep enough past the growth
witness that the deepened moment excess `3^{-MΔ}·crude` is at most one,
for a free reserve order `M`.  Past the burn-in both deepened moments are
at most `2`, so the supply value is **`growthBar`-free**: the proved entry
conclusion with the crude moments replaced by the absolute constants `2`
and `√2`.  This is the free-threshold mechanism: the `K`-content leaves the
lag channel entirely and
is paid once, in the threshold, as the burn-in depth.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- Loewner monotonicity of the scaled reference in the scalar. -/
theorem blockScale_loewner_mono {E : BlockMat d}
    (hquad : ∀ X : BlockVec d,
      0 ≤ blockVecDot X (blockMatVecMul E X))
    {c c' : ℝ} (hcc : c ≤ c') :
    BlockMatLoewnerLE (blockScale c E) (blockScale c' E) := by
  intro X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale,
    Sharp.blockVecDot_blockMatVecMul_blockScale]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hcc) (hquad X)]

end

end HCPolySupport.HighContrast.Quenched
