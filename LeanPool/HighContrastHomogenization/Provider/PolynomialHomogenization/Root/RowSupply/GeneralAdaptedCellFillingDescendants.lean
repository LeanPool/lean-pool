/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.AffineAdaptedCellResponseFilling
public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedLinearOscillation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.GeneralAdaptedCellFillingDescendants

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Common-parent descendants for a general adapted filling

Once an arbitrary adapted target is enclosed in one cell of the filling grid,
every selected filling cell corresponds to a descendant of the associated
reference origin cube.  This is the geometric bridge from the general filling
to `maxDescendantNormalizedBlockResponseAtScale`.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

variable {d : ℕ}

/-- A cell selected by a general `q`-grid filling of a `p`-adapted target is a
reference descendant of any enclosing `q`-grid parent above the filling's
starting scale. -/
theorem translateCube_mem_descendantsAtScale_originCube_of_mem_adaptedTarget_filling
    [NeZero d] {p q : Mat d} (hq : q.PosDef)
    {n j M : ℤ} (hnM : n ≤ M) {y : Vec d}
    {Z : ℤ → Finset (Fin d → ℤ)}
    (hZ : ∀ r, ↑(Z r) = Transport.fillingIndex q n
      (adaptedCellTranslate p j y) r)
    (hEnclose : adaptedCellTranslate p j y ⊆ adaptedCell q M)
    {r : ℤ} {w : Fin d → ℤ} (hw : w ∈ Z r) :
    translateCube w (originCube d r) ∈
      descendantsAtScale (originCube d M) r := by
  have hwFill : w ∈ Transport.fillingIndex q n (adaptedCellTranslate p j y) r := by
    rw [← hZ r]
    exact Finset.mem_coe.mpr hw
  have hrM : r ≤ M := (Transport.le_of_mem_fillingIndex hwFill).trans hnM
  have hcenterCell : adaptedCellCenter q r w ∈ adaptedCellAt q r w := by
    rw [Recurrence.adaptedCellAt_eq_image, Recurrence.adaptedCellCenter_eq]
    exact ⟨standardCellCenter r w, Recurrence.standardCellCenter_mem_standardCell r w, rfl⟩
  have hcenterParent : adaptedCellCenter q r w ∈ adaptedCell q M :=
    hEnclose (Transport.adaptedCellAt_subset_of_mem_fillingIndex hwFill hcenterCell)
  have hwAligned : w ∈ Response.alignedIndex q r M :=
    (Response.mem_alignedIndex_iff hq hrM).mpr hcenterParent
  have hDepth :=
    Response.translateCube_mem_descendantsAtDepth_of_mem_alignedIndex
      hq hrM hwAligned
  rw [mem_descendantsAtScale_iff hrM]
  simpa only [originCube] using hDepth

end

end RowSupply
end HighContrast
end HCPolySupport
