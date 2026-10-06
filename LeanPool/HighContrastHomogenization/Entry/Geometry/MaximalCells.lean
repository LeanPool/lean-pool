/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.AdaptedCell
public import LeanPool.HighContrastHomogenization.Entry.Geometry.MaximalCellsDef
public import LeanPool.HighContrastHomogenization.Setup.Geometry
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyCells

/-!
# High-contrast homogenization: Entry.Geometry.MaximalCells

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Maximal standard aligned cubes in a set

The family of `l.source.whitney`: the standard aligned
cubes contained in a set `W` with generation at most `j`, and the maximal ones among them.
This file has the order-theoretic part: the parent of a maximal cube of generation `< j`
escapes `W`, and distinct maximal cubes are disjoint.

The definitions `IsCellIn`, `IsMaximalCellIn`, `maximalCellIndices` and `maximalCellPairs` live
in the definition-only leaf `HCPoly.Entry.Geometry.MaximalCellsDef` (imported here), so that they
can
be stated without these proofs.
-/

open HCPolySupport.HighContrast (standardCell)
namespace HCPolySupport.HighContrast.Geometry

open MeasureTheory

variable {d : ℕ}

theorem IsMaximalCellIn.le {W : Set (Vec d)} {j k : ℤ} {w : Fin d → ℤ}
    (h : IsMaximalCellIn W j k w) : k ≤ j := h.1.1

theorem IsMaximalCellIn.subset {W : Set (Vec d)} {j k : ℤ} {w : Fin d → ℤ}
    (h : IsMaximalCellIn W j k w) : standardCell d k w ⊆ W := h.1.2

/-- The parent of a maximal cube of generation `k < j` is not contained in `W`. -/
theorem IsMaximalCellIn.parent_not_subset [NeZero d] {W : Set (Vec d)} {j k : ℤ}
    {w : Fin d → ℤ} (h : IsMaximalCellIn W j k w) (hkj : k < j) :
    ¬ standardCell d (k + 1) (Transport.gridParent w) ⊆ W := by
  intro hsub
  have heq := h.2 (k + 1) (Transport.gridParent w) ⟨by omega, hsub⟩ (Transport.standardCell_subset_parent k w)
  have := (eq_of_standardCell_eq heq).1
  omega

/-- Maximal cubes with distinct index pairs are disjoint. -/
theorem IsMaximalCellIn.disjoint [NeZero d] {W : Set (Vec d)} {j k k' : ℤ}
    {w w' : Fin d → ℤ} (h : IsMaximalCellIn W j k w) (h' : IsMaximalCellIn W j k' w')
    (hne : (k, w) ≠ (k', w')) :
    Disjoint (standardCell d k w) (standardCell d k' w') := by
  -- by symmetry, reduce to `k ≤ k'`
  have key : ∀ {k k' : ℤ} {w w' : Fin d → ℤ}, IsMaximalCellIn W j k w →
      IsMaximalCellIn W j k' w' → (k, w) ≠ (k', w') → k ≤ k' →
      Disjoint (standardCell d k w) (standardCell d k' w') := by
    intro k k' w w' h h' hne hkk'
    rcases standardCell_subset_or_disjoint hkk' w w' with hsub | hdis
    · exfalso
      have heq := h.2 k' w' h'.1 hsub
      obtain ⟨rfl, rfl⟩ := eq_of_standardCell_eq heq
      exact hne rfl
    · exact hdis
  rcases le_total k k' with hkk' | hkk'
  · exact key h h' hne hkk'
  · exact (key h' h (Ne.symm hne) hkk').symm

/-- The maximal cubes form a pairwise disjoint family indexed by their index pairs. -/
theorem pairwiseDisjoint_maximalCellPairs [NeZero d] (W : Set (Vec d)) (j : ℤ) :
    (maximalCellPairs W j).PairwiseDisjoint fun p => standardCell d p.1 p.2 :=
  fun _ hp _ hp' hne => IsMaximalCellIn.disjoint hp hp' hne

/-- The maximal cubes of one generation are pairwise disjoint. -/
theorem pairwiseDisjoint_maximalCellIndices [NeZero d] (W : Set (Vec d)) (j r : ℤ) :
    (maximalCellIndices W j r).PairwiseDisjoint fun w => standardCell d r w :=
  fun _ hw _ hw' hne => IsMaximalCellIn.disjoint hw hw' (by simpa using hne)

/-- A cube of the family containing a point `x` and of largest generation among those is
maximal. -/
theorem isMaximalCellIn_of_greatest {W : Set (Vec d)} {j k : ℤ} {w : Fin d → ℤ} {x : Vec d}
    (hk : IsCellIn W j k w) (hx : x ∈ standardCell d k w)
    (hgreatest : ∀ k' w', IsCellIn W j k' w' → x ∈ standardCell d k' w' → k' ≤ k) :
    IsMaximalCellIn W j k w := by
  refine ⟨hk, fun k' w' hk' hsub => ?_⟩
  have hk'le : k' ≤ k := hgreatest k' w' hk' (hsub hx)
  exact Set.Subset.antisymm (standardCell_subset_of_mem hk'le (hsub hx) hx) hsub

/-- Every cube of the family lies in a maximal one containing any given point of it. -/
theorem exists_isMaximalCellIn_of_isCellIn {W : Set (Vec d)} {j k : ℤ} {w : Fin d → ℤ}
    {x : Vec d} (hk : IsCellIn W j k w) (hx : x ∈ standardCell d k w) :
    ∃ k' w', IsMaximalCellIn W j k' w' ∧ x ∈ standardCell d k' w' := by
  obtain ⟨k', ⟨w', hk', hx'⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun k' => ∃ w', IsCellIn W j k' w' ∧ x ∈ standardCell d k' w')
    ⟨j, fun k' ⟨_, hk', _⟩ => hk'.1⟩ ⟨k, w, hk, hx⟩
  exact ⟨k', w', isMaximalCellIn_of_greatest hk' hx'
    fun k'' w'' hk'' hx'' => hmax k'' ⟨w'', hk'', hx''⟩, hx'⟩

end HCPolySupport.HighContrast.Geometry
