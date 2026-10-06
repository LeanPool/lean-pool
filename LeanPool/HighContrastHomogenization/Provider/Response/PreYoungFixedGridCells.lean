/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowMeanEstimates
public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterCellBounds
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyRows

/-!
# High-contrast homogenization: Provider.Response.PreYoungFixedGridCells

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Aligned-cell integrability on a fixed rounded grid

The pre-Young chain obtains the integrable coarse blocks of the
aligned source cells from the window multiplier, through the literal carrier
equality `q = roundedGrid jStar m0` tying the grid's rounding scale to the
moving source alignment.  The paper's fixed-grid recurrence
(`q = roundedGrid lAl m0` with `lAl` fixed and the generation window moving)
cannot satisfy that equality, so the fixed-grid chain replaces the window
multiplier by the exact integrability carrier below, constructed here directly
from the coarse ellipticity `e.coarse.ellipticity`.
-/

namespace HCPolySupport.HighContrast.Response.FixedGrid

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The aligned-cell integrability carrier.**  Every aligned subcell of
either source cell of the window `{s, t}` has an integrable coarse response.
This is exactly the content that the moving-window chain draws from the
window multiplier, isolated from the multiplier's carrier equality. -/
@[expose]
def AlignedCellsIntegrable (P : Measure (CoeffSpace d)) (q : Mat d)
    (s t : ℤ) : Prop :=
  ∀ ⦃k v : ℤ⦄, k ≤ v → v ≤ t → v = s ∨ v = t →
    ∀ ⦃w : Fin d → ℤ⦄, w ∈ alignedIndex q k v →
      HasIntegrableCoarseBlock P (adaptedCellAt q k w)

/-- Under the coarse ellipticity `e.coarse.ellipticity`, every adapted
cell of every positive-definite grid has an integrable coarse response; in
particular the aligned-cell integrability carrier holds on every window. -/
theorem alignedCellsIntegrable_of_dagger [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {q : Mat d} (hq : q.PosDef) (s t : ℤ) :
    AlignedCellsIntegrable P q s t := by
  intro k v _hkv _hvt _hvs w _hw
  have hmeas : HasMeasurableCoarseBlock P
      (adaptedCellTranslate q k (adaptedCellCenter q k w)) :=
    Transport.hasMeasurableCoarseBlock_adaptedCellTranslate P hq k _
  have hint :=
    Entry.hasIntegrableCoarseBlock_adaptedCellTranslate_of_dagger hdag hq hmeas
  simpa only [← Transport.adaptedCellAt_eq_adaptedCellTranslate] using hint

end

end HCPolySupport.HighContrast.Response.FixedGrid
