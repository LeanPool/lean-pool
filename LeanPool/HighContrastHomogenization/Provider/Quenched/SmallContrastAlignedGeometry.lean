/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Selection.EnclosureGeometry
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNorm

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastAlignedGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Aligned-cell enclosure for the cap geometry

Every aligned adapted cell read by the row and weak caps sits inside the
generation cube after one further enlargement: the center lies in the parent
cell, hence in the parent's enlarged cube, and the cell itself adds at most
one more cell radius.  This discharges the `hgeom` hypotheses of the
small-contrast row and weak caps at the account's grid-norm witness
`‖q‖·√d ≤ 3^G`, with the cap enlargement `G + 1`.
-/

namespace HCPolySupport.HighContrast.Quenched

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The aligned-cell enclosure.**  An aligned adapted cell at scale
`k ≤ p ≤ t` whose center lies in the parent cell `⋄_p^q` is contained in the
centered cube at generation `t` enlarged by `G + 1`. -/
theorem adaptedCellAt_subset_centeredCube_succ (hd : 1 ≤ d) {q : Mat d}
    (hq : q.PosDef) {G : ℕ}
    (hqnorm : ‖q‖ * Real.sqrt d ≤ (3 : ℝ) ^ G)
    {k p t : ℤ} (hkp : k ≤ p) (hpt : p ≤ t) {w : Fin d → ℤ}
    (hw : w ∈ Response.alignedIndex q k p) :
    adaptedCellAt q k w ⊆ centeredCube d (t + ((G + 1 : ℕ) : ℤ)) := by
  have hcen : adaptedCellCenter q k w ∈ adaptedCell q p :=
    (Response.mem_alignedIndex_iff hq hkp).mp hw
  have hcenCube : adaptedCellCenter q k w ∈ centeredCube d (p + (G : ℤ)) :=
    Selection.adaptedCell_subset_centeredCube_add hd hqnorm hcen
  have hcellCube : adaptedCell q k ⊆ centeredCube d (k + (G : ℤ)) :=
    Selection.adaptedCell_subset_centeredCube_add hd hqnorm
  rintro x ⟨y, hy, rfl⟩
  have hyCube : y ∈ centeredCube d (k + (G : ℤ)) := hcellCube hy
  have hcen0 : (3 : ℝ) ^ k • matVecMul q (fun i => (w i : ℝ)) =
      adaptedCellCenter q k w := rfl
  rw [hcen0]
  change adaptedCellCenter q k w + y ∈ centeredCube d (t + ((G + 1 : ℕ) : ℤ))
  rw [Recurrence.mem_centeredCube_iff] at hcenCube hyCube ⊢
  have hpow : ∀ m : ℤ, m ≤ t →
      (3 : ℝ) ^ (m + (G : ℤ)) ≤ (3 : ℝ) ^ (t + (G : ℤ)) := by
    intro m hm
    exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
  have hp3 : (3 : ℝ) ^ (p + (G : ℤ)) ≤ (3 : ℝ) ^ (t + (G : ℤ)) :=
    hpow p hpt
  have hk3 : (3 : ℝ) ^ (k + (G : ℤ)) ≤ (3 : ℝ) ^ (t + (G : ℤ)) :=
    hpow k (hkp.trans hpt)
  have hsucc : (3 : ℝ) ^ (t + ((G + 1 : ℕ) : ℤ)) =
      (3 : ℝ) ^ (t + (G : ℤ)) * 3 := by
    rw [show t + ((G + 1 : ℕ) : ℤ) = (t + (G : ℤ)) + 1 from by push_cast; ring,
      zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (t + (G : ℤ)) :=
    zpow_pos (by norm_num) _
  intro i
  have hci := hcenCube i
  have hyi := hyCube i
  have hxi : (adaptedCellCenter q k w + y) i =
      adaptedCellCenter q k w i + y i := rfl
  rw [hxi]
  constructor
  · rw [hsucc]
    linarith only [hci.1, hyi.1, hp3, hk3, hpos]
  · rw [hsucc]
    linarith only [hci.2, hyi.2, hp3, hk3, hpos]

/-- The enclosure in the exact `hgeom` shape consumed by the small-contrast
row and weak caps, at the cap enlargement `G + 1`. -/
theorem aligned_hgeom_of_grid_norm (hd : 1 ≤ d) {q : Mat d} (hq : q.PosDef)
    {G : ℕ} (hqnorm : ‖q‖ * Real.sqrt d ≤ (3 : ℝ) ^ G)
    {p t : ℤ} (hpt : p ≤ t) :
    ∀ k : ℤ, k ≤ p → ∀ w ∈ Response.alignedIndex q k p,
      adaptedCellAt q k w ⊆ centeredCube d (t + ((G + 1 : ℕ) : ℤ)) :=
  fun _k hkp _w hw =>
    adaptedCellAt_subset_centeredCube_succ hd hq hqnorm hkp hpt hw

end

end HCPolySupport.HighContrast.Quenched
