/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.AdaptedCellTransport
public import LeanPool.HighContrastHomogenization.Entry.Geometry.SourceWhitneyDecomposition
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyCells

/-!
# High-contrast homogenization: Entry.Geometry.AdaptedMaximalCells

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Maximal adapted cells

Order-theoretic facts for the actual adapted maximal-cell predicate, transported
from the standard maximal-cell family through an invertible adapted grid: the
maximal adapted cells are pairwise disjoint, their index set is the maximal
standard-cell index set of the affine preimage, their center set is finite when
the region has finite volume, and the part of an open region missed by the
maximal cells off the affine grid faces is null. These are the cell-ordering and
covering facts behind the Whitney partition between adapted grids
`l.two.grid.whitney`, and they also supply the capped adapted covering used by
`p.response.transfer`.
-/

open HCPolySupport.HighContrast (adaptedCellCenter)
open HCPolySupport.HighContrast (standardCell standardCellCenter)
namespace HCPolySupport.HighContrast.Geometry

open MeasureTheory

variable {d : ℕ}

theorem IsMaximalAdaptedCellIn.subset {W : Set (Vec d)} {q : Mat d} {n r : ℤ}
    {w : Fin d → ℤ} (h : IsMaximalAdaptedCellIn W q n r w) :
    adaptedCellAtCenter q r w ⊆ W :=
  h.1.2

theorem matVecMul_injective_of_isUnit (q : Mat d) (hq : IsUnit q) :
    Function.Injective (matVecMul q : Vec d → Vec d) := by
  intro x y hxy
  rw [matVecMul_eq_mulVec, matVecMul_eq_mulVec] at hxy
  exact Matrix.mulVec_injective_iff_isUnit.mpr hq hxy

theorem IsMaximalAdaptedCellIn.disjoint [NeZero d] {W : Set (Vec d)} {q : Mat d}
    (hq : IsUnit q) {n r r' : ℤ} {w w' : Fin d → ℤ}
    (h : IsMaximalAdaptedCellIn W q n r w)
    (h' : IsMaximalAdaptedCellIn W q n r' w') (hne : (r, w) ≠ (r', w')) :
    Disjoint (adaptedCellAtCenter q r w) (adaptedCellAtCenter q r' w') := by
  have hstd := (isMaximalAdaptedCellIn_iff_isMaximalCellIn_preimage W q hq n r w).mp h
  have hstd' := (isMaximalAdaptedCellIn_iff_isMaximalCellIn_preimage W q hq n r' w').mp h'
  have hdis := IsMaximalCellIn.disjoint hstd hstd' hne
  rw [adaptedCellAtCenter_eq_affine_standardCell, adaptedCellAtCenter_eq_affine_standardCell]
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
  have h_inj := matVecMul_injective_of_isUnit q hq hvu
  exact Set.disjoint_left.mp hdis hu (by simpa [h_inj] using hv)

theorem pairwiseDisjoint_maximalAdaptedCellPairs [NeZero d] (W : Set (Vec d)) (q : Mat d)
    (hq : IsUnit q) (n : ℤ) :
    ({p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q n p.1 p.2}).PairwiseDisjoint
      fun p => adaptedCellAtCenter q p.1 p.2 :=
  fun _ hp _ hp' hne => IsMaximalAdaptedCellIn.disjoint hq hp hp' hne

theorem pairwiseDisjoint_maximalAdaptedCellIndices [NeZero d] (W : Set (Vec d)) (q : Mat d)
    (hq : IsUnit q) (n r : ℤ) :
    (maximalAdaptedCellIndices W q n r).PairwiseDisjoint fun w => adaptedCellAtCenter q r w :=
  fun _ hw _ hw' hne => IsMaximalAdaptedCellIn.disjoint hq hw hw' (by simpa using hne)

theorem isMaximalCellIn_iff_parent_not_subset [NeZero d] {W : Set (Vec d)}
    (n r : ℤ) (w : Fin d → ℤ) :
    IsMaximalCellIn W n r w ↔
      r ≤ n ∧ standardCell d r w ⊆ W ∧
        (r = n ∨ ¬ standardCell d (r + 1) (Transport.gridParent w) ⊆ W) := by
  constructor
  · intro h
    refine ⟨h.le, h.subset, ?_⟩
    by_cases hrn : r = n
    · exact Or.inl hrn
    · exact Or.inr (h.parent_not_subset (lt_of_le_of_ne h.le hrn))
  · rintro ⟨hrn, hsubW, hparent⟩
    refine ⟨⟨hrn, hsubW⟩, ?_⟩
    intro r' w' hcell hsub
    have hx : standardCellCenter r w ∈ standardCell d r' w' :=
      hsub (Recurrence.standardCellCenter_mem_standardCell r w)
    rcases lt_trichotomy r' r with hlt | heq | hgt
    · have hle : r' ≤ r := hlt.le
      rcases standardCell_subset_or_disjoint hle w' w with hback | hdis
      · exact Set.Subset.antisymm hback hsub
      · exact False.elim (Set.disjoint_left.mp hdis hx
        (Recurrence.standardCellCenter_mem_standardCell r w))
    · subst heq
      rcases standardCell_subset_or_disjoint (le_refl r') w' w with hback | hdis
      · exact Set.Subset.antisymm hback hsub
      · exact False.elim (Set.disjoint_left.mp hdis hx
        (Recurrence.standardCellCenter_mem_standardCell r' w))
    · have hrlt : r < n := hgt.trans_le hcell.1
      rcases hparent with hr_eq | hparent_not
      · omega
      · have hparent_le : r + 1 ≤ r' := by omega
        have hx_parent : standardCellCenter r w ∈ standardCell d (r + 1) (Transport.gridParent w) :=
          Transport.standardCell_subset_parent r w
            (Recurrence.standardCellCenter_mem_standardCell r w)
        rcases standardCell_subset_or_disjoint hparent_le (Transport.gridParent w) w' with
          hpar_sub | hdis
        · exact False.elim (hparent_not (hpar_sub.trans hcell.2))
        · exact False.elim (Set.disjoint_left.mp hdis hx_parent hx)

theorem isMaximalAdaptedCellIn_iff_parent_not_subset [NeZero d] {W : Set (Vec d)}
    {q : Mat d} (hq : IsUnit q) (n r : ℤ) (w : Fin d → ℤ) :
    IsMaximalAdaptedCellIn W q n r w ↔
      r ≤ n ∧ adaptedCellAtCenter q r w ⊆ W ∧
        (r = n ∨ ¬ adaptedCellAtCenter q (r + 1) (Transport.gridParent w) ⊆ W) := by
  rw [isMaximalAdaptedCellIn_iff_isMaximalCellIn_preimage W q hq n r w,
    isMaximalCellIn_iff_parent_not_subset (W := (matVecMul q) ⁻¹' W) n r w,
    standardCell_subset_preimage_iff_adaptedCellAtCenter_subset W q r w,
    standardCell_subset_preimage_iff_adaptedCellAtCenter_subset W q (r + 1)
      (Transport.gridParent w)]

/-- An interior point off all affine grid faces has a contained cell below any prescribed cap.
Smallness is measured with the ambient sup metric. -/
theorem exists_isAdaptedCellIn_of_isOpen {W : Set (Vec d)} {q : Mat d}
    (hq : IsUnit q) (hW : IsOpen W) (n : ℤ) {x : Vec d} (hxW : x ∈ W)
    (hxN : x ∉ matVecMul q '' ⋃ k : ℤ, gridFaces d k) :
    ∃ r w, IsAdaptedCellIn W q n r w ∧ x ∈ adaptedCellAtCenter q r w := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq
  let u : Vec d := Matrix.mulVec q⁻¹ x
  have hqu : matVecMul q u = x := by
    dsimp [u]
    rw [matVecMul_eq_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv q hdet,
      Matrix.one_mulVec]
  have huW : u ∈ (matVecMul q) ⁻¹' W := by
    simpa [Set.mem_preimage, hqu] using hxW
  have huN : u ∉ ⋃ k : ℤ, gridFaces d k := by
    intro hu
    exact hxN ⟨u, hu, hqu⟩
  have hpreopen : IsOpen ((matVecMul q) ⁻¹' W) := by
    exact hW.preimage (by
      simpa [matVecMul_eq_mulVec] using!
        (Continuous.matrix_mulVec continuous_const continuous_id : Continuous fun x : Vec d =>
          Matrix.mulVec q x))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hpreopen u huW
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((3 : ℝ) ^ n / ε) (by norm_num : (1 : ℝ) < 3)
  set k : ℤ := n - (m : ℤ) with hk
  have hkn : k ≤ n := by omega
  have h3k : (3 : ℝ) ^ k < ε := by
    rw [hk, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast,
      div_lt_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ m)]
    exact (mul_comm ((3 : ℝ) ^ m) ε) ▸ (div_lt_iff₀ hε).mp hm
  have huk : u ∉ gridFaces d k := fun h => huN (Set.mem_iUnion.mpr ⟨k, h⟩)
  obtain ⟨w, hw⟩ := exists_mem_standardCell_of_not_mem_gridFaces huk
  have hsub : standardCell d k w ⊆ (matVecMul q) ⁻¹' W :=
    (standardCell_subset_ball hw).trans ((Metric.ball_subset_ball h3k.le).trans hball)
  refine ⟨k, w, IsCellIn.of_standard_preimage ⟨hkn, hsub⟩, ?_⟩
  rw [← hqu, adaptedCellAtCenter_eq_affine_standardCell]
  exact ⟨u, hw, rfl⟩

/-- Lift a contained adapted cell through standard maximal existence at the same cap. -/
theorem exists_isMaximalAdaptedCellIn_of_isAdaptedCellIn {W : Set (Vec d)} {q : Mat d}
    (hq : IsUnit q) {n r : ℤ} {w : Fin d → ℤ} {x : Vec d}
    (hw : IsAdaptedCellIn W q n r w) (hx : x ∈ adaptedCellAtCenter q r w) :
    ∃ r' w', IsMaximalAdaptedCellIn W q n r' w' ∧ x ∈ adaptedCellAtCenter q r' w' := by
  rw [adaptedCellAtCenter_eq_affine_standardCell] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨r', w', hmax, hu'⟩ :=
    exists_isMaximalCellIn_of_isCellIn (IsAdaptedCellIn.to_standard_preimage hw) hu
  refine ⟨r', w',
    (isMaximalAdaptedCellIn_iff_isMaximalCellIn_preimage W q hq n r' w').mpr hmax, ?_⟩
  rw [adaptedCellAtCenter_eq_affine_standardCell]
  exact ⟨u, hu', rfl⟩

theorem volume_diff_iUnion_maximalAdaptedCells_of_isOpen
    {W : Set (Vec d)} {q : Mat d} (hq : IsUnit q) (hW : IsOpen W) (n : ℤ) :
    volume (W \
      ⋃ p ∈ {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q n p.1 p.2},
        adaptedCellAtCenter q p.1 p.2) = 0 := by
  refine measure_mono_null (t := matVecMul q '' ⋃ k : ℤ, gridFaces d k) ?_
    (volume_image_iUnion_gridFaces q)
  rintro x ⟨hxW, hxU⟩
  by_contra hxN
  obtain ⟨r, w, hw, hxw⟩ := exists_isAdaptedCellIn_of_isOpen hq hW n hxW hxN
  obtain ⟨r', w', hmax, hxw'⟩ := exists_isMaximalAdaptedCellIn_of_isAdaptedCellIn hq hw hxw
  exact hxU (Set.mem_iUnion₂.mpr ⟨(r', w'), hmax, hxw'⟩)

theorem finite_maximalAdaptedCellCenters_of_finite_indices {W : Set (Vec d)} {q : Mat d}
    {n r : ℤ} (hfin : (maximalAdaptedCellIndices W q n r).Finite) :
    (maximalAdaptedCellCenters W q n r).Finite := by
  simpa [maximalAdaptedCellCenters] using hfin.image (adaptedCellCenter q r)

theorem maximalAdaptedCellCenters_eq_image_indices (W : Set (Vec d)) (q : Mat d)
    (n r : ℤ) :
    maximalAdaptedCellCenters W q n r =
      adaptedCellCenter q r '' maximalAdaptedCellIndices W q n r := by
  rfl

theorem maximalAdaptedCellIndices_eq_maximalCellIndices_preimage
    (W : Set (Vec d)) (q : Mat d) (hq : IsUnit q) (n r : ℤ) :
    maximalAdaptedCellIndices W q n r =
      maximalCellIndices ((matVecMul q) ⁻¹' W) n r := by
  ext w
  exact isMaximalAdaptedCellIn_iff_isMaximalCellIn_preimage W q hq n r w

theorem finite_maximalAdaptedCellIndices_of_volume_ne_top [NeZero d]
    {W : Set (Vec d)} {q : Mat d} (hq : IsUnit q) (hW : volume W ≠ ⊤) (n r : ℤ) :
    (maximalAdaptedCellIndices W q n r).Finite := by
  rw [maximalAdaptedCellIndices_eq_maximalCellIndices_preimage W q hq n r]
  exact finite_maximalCellIndices (volume_preimage_matVecMul_ne_top hq hW) n r

theorem finite_maximalAdaptedCellCenters_of_volume_ne_top [NeZero d]
    {W : Set (Vec d)} {q : Mat d} (hq : IsUnit q) (hW : volume W ≠ ⊤) (n r : ℤ) :
    (maximalAdaptedCellCenters W q n r).Finite :=
  finite_maximalAdaptedCellCenters_of_finite_indices
    (finite_maximalAdaptedCellIndices_of_volume_ne_top hq hW n r)

/-- The actual center row and its standard preimage row have the same cardinality. -/
theorem ncard_maximalAdaptedCellCenters_eq_preimage {W : Set (Vec d)}
    {q : Mat d} (hq : IsUnit q) (n r : ℤ) :
    (maximalAdaptedCellCenters W q n r).ncard =
      (maximalCellIndices ((matVecMul q) ⁻¹' W) n r).ncard := by
  rw [maximalAdaptedCellCenters_eq_image_indices,
    Set.ncard_image_of_injective _ (adaptedCellCenter_injective q r hq),
    maximalAdaptedCellIndices_eq_maximalCellIndices_preimage W q hq n r]

/-- Below the cap, parent escape controls distance to the complement in `q`-coordinates. -/
theorem exists_not_mem_preimage_of_mem_maximalAdaptedCell [NeZero d]
    {W : Set (Vec d)} {q : Mat d} (hq : IsUnit q) {n r : ℤ} (hr : r < n)
    {w : Fin d → ℤ} (hw : IsMaximalAdaptedCellIn W q n r w)
    {x : Vec d} (hx : x ∈ standardCell d r w) :
    ∃ x', x' ∉ (matVecMul q) ⁻¹' W ∧
      ∑ i, (x i - x' i) ^ 2 ≤ (Real.sqrt d * (3 : ℝ) ^ (r + 1)) ^ 2 :=
  exists_not_mem_of_mem_maximalCell hr
    ((isMaximalAdaptedCellIn_iff_isMaximalCellIn_preimage W q hq n r w).mp hw) hx

end HCPolySupport.HighContrast.Geometry
