/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AlignedSubdivision

/-!
# High-contrast homogenization: Provider.Recurrence.AdaptedCellDomain

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adapted cell as a bounded open convex domain

The coarse-response formalism taken from HC is developed over
bounded open convex domains: the variational identity that reads the coarse
block off the response functional, the restriction of an `a`-harmonic
competitor, and the upper bound that makes the response functional a genuine
supremum all take that hypothesis.  The adapted cubes of a rounded geometry
are linear images of triadic cubes under an invertible
grid map, so they are bounded open convex domains as well, and this file records
that.

An invertible grid map is an open map because its image is the preimage under
the inverse map, which is continuous; it preserves boundedness because a linear
map moves the coordinate bound by the sum of the absolute entries; and it
preserves convexity because it is linear.  Cubes are nonempty because they
contain their centers, and a nonempty open set has positive volume, so the
volume normalizations of the response functional are legitimate on every adapted
cell.  Finally, the aligned cells at one scale are translates of each other, so
they all have the same volume — the fact that turns the weights
`|U_i| / |U|` of `e.fixed.geometry.parent.child` into the uniform weights
`3^{-d(p-j)}` of the recurrence.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-! ## Linear images under an invertible grid map -/

/-- The image of a set under an invertible grid map is the preimage under the
inverse map. -/
theorem image_matVecMul_eq_preimage_inv {q : Mat d} (hq : q.PosDef) (S : Set (Vec d)) :
    matVecMul q '' S = matVecMul q⁻¹ ⁻¹' S := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyy : matVecMul q⁻¹ (matVecMul q y) = y := by
      show q⁻¹ *ᵥ q *ᵥ y = y
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    simpa [Set.mem_preimage, hyy] using hy
  · intro hx
    refine ⟨matVecMul q⁻¹ x, hx, ?_⟩
    show q *ᵥ q⁻¹ *ᵥ x = x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- An invertible grid map is an open map. -/
theorem isOpen_image_matVecMul {q : Mat d} (hq : q.PosDef) {S : Set (Vec d)}
    (hS : IsOpen S) : IsOpen (matVecMul q '' S) := by
  rw [image_matVecMul_eq_preimage_inv hq]
  exact hS.preimage (Matrix.mulVecLin q⁻¹).continuous_of_finiteDimensional

/-- A linear map moves a coordinate bound by the sum of the absolute entries. -/
theorem isBoundedDomain_image_matVecMul (M : Mat d) {S : Set (Vec d)}
    (hS : IsBoundedDomain S) : IsBoundedDomain (matVecMul M '' S) := by
  obtain ⟨R, hR, hRS⟩ := hS
  refine ⟨(∑ i : Fin d, ∑ j : Fin d, |M i j|) * R + 1, by positivity, ?_⟩
  rintro x ⟨y, hy, rfl⟩ i
  have hrow : ∑ j : Fin d, |M i j| ≤ ∑ i : Fin d, ∑ j : Fin d, |M i j| :=
    Finset.single_le_sum (f := fun i : Fin d => ∑ j : Fin d, |M i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hsum : |∑ j : Fin d, M i j * y j| ≤ ∑ j : Fin d, |M i j| * R :=
    le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hRS y hy j) (abs_nonneg _))
  have hfin : ∑ j : Fin d, |M i j| * R = (∑ j : Fin d, |M i j|) * R :=
    (Finset.sum_mul _ _ _).symm
  have hmono : (∑ j : Fin d, |M i j|) * R ≤ (∑ i : Fin d, ∑ j : Fin d, |M i j|) * R :=
    mul_le_mul_of_nonneg_right hrow hR.le
  have hentry : matVecMul M y i = ∑ j : Fin d, M i j * y j := rfl
  rw [hentry]
  rw [hfin] at hsum
  linarith only [hsum, hmono]

/-- **The invertible linear image of a bounded open convex domain is one.** -/
theorem isOpenBoundedConvexDomain_image_matVecMul {q : Mat d} (hq : q.PosDef)
    {S : Set (Vec d)} (hS : IsOpenBoundedConvexDomain S) :
    IsOpenBoundedConvexDomain (matVecMul q '' S) :=
  ⟨isOpen_image_matVecMul hq hS.isOpen,
    isBoundedDomain_image_matVecMul q hS.isBoundedDomain,
    hS.convex.linear_image (Matrix.mulVecLin q)⟩

/-! ## Cubes contain their centers -/

/-- A standard aligned cube contains its center. -/
theorem standardCellCenter_mem_standardCell (k : ℤ) (w : Fin d → ℤ) :
    standardCellCenter k w ∈ standardCell d k w := by
  rw [mem_standardCell_iff]
  intro i
  have h : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hc : standardCellCenter k w i = (3 : ℝ) ^ k * (w i : ℝ) := rfl
  rw [hc]
  constructor <;> nlinarith only [h]

/-- A standard aligned cube is nonempty. -/
theorem standardCell_nonempty (k : ℤ) (w : Fin d → ℤ) :
    (standardCell d k w).Nonempty :=
  ⟨standardCellCenter k w, standardCellCenter_mem_standardCell k w⟩

/-- A centered triadic cube is nonempty. -/
theorem centeredCube_nonempty (k : ℤ) : (centeredCube d k).Nonempty := by
  rw [← standardCell_zero]
  exact standardCell_nonempty k 0

/-! ## The adapted cells are domains -/

/-- **The adapted cell `⋄_k^q` is a bounded open convex domain.** -/
theorem isOpenBoundedConvexDomain_adaptedCell {q : Mat d} (hq : q.PosDef) (k : ℤ) :
    IsOpenBoundedConvexDomain (adaptedCell q k) :=
  isOpenBoundedConvexDomain_image_matVecMul hq
    (isOpenBoundedConvexDomain_openCubeSet (originCube d k))

/-- **An aligned adapted cell is a bounded open convex domain.** -/
theorem isOpenBoundedConvexDomain_adaptedCellAt {q : Mat d} (hq : q.PosDef) (k : ℤ)
    (w : Fin d → ℤ) : IsOpenBoundedConvexDomain (adaptedCellAt q k w) := by
  rw [adaptedCellAt_eq_image]
  exact isOpenBoundedConvexDomain_image_matVecMul hq
    (isOpenBoundedConvexDomain_openCubeSet (translateCube w (originCube d k)))

/-- An adapted cell is nonempty. -/
theorem adaptedCell_nonempty (q : Mat d) (k : ℤ) : (adaptedCell q k).Nonempty :=
  (centeredCube_nonempty k).image (matVecMul q)

/-- An aligned adapted cell is nonempty. -/
theorem adaptedCellAt_nonempty (q : Mat d) (k : ℤ) (w : Fin d → ℤ) :
    (adaptedCellAt q k w).Nonempty := by
  rw [adaptedCellAt_eq_image]
  exact (standardCell_nonempty k w).image (matVecMul q)

/-! ## Volumes of adapted cells -/

/-- An adapted cell has positive volume. -/
theorem volume_adaptedCell_pos {q : Mat d} (hq : q.PosDef) (k : ℤ) :
    0 < volume (adaptedCell q k) :=
  (isOpenBoundedConvexDomain_adaptedCell hq k).isOpen.measure_pos volume
    (adaptedCell_nonempty q k)

/-- An aligned adapted cell has positive volume. -/
theorem volume_adaptedCellAt_pos {q : Mat d} (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ) :
    0 < volume (adaptedCellAt q k w) :=
  (isOpenBoundedConvexDomain_adaptedCellAt hq k w).isOpen.measure_pos volume
    (adaptedCellAt_nonempty q k w)

/-- An adapted cell has finite volume. -/
theorem volume_adaptedCell_lt_top {q : Mat d} (hq : q.PosDef) (k : ℤ) :
    volume (adaptedCell q k) < ⊤ :=
  (isOpenBoundedConvexDomain_adaptedCell hq k).volume_lt_top

/-- The volume normalization of an adapted cell is a positive real. -/
theorem toReal_volume_adaptedCell_pos {q : Mat d} (hq : q.PosDef) (k : ℤ) :
    0 < (volume (adaptedCell q k)).toReal :=
  ENNReal.toReal_pos (volume_adaptedCell_pos hq k).ne'
    (volume_adaptedCell_lt_top hq k).ne

/-- **The aligned cells at one scale all have the volume of the cell at the
origin**, being translates of it.  This is what turns the weights `|U_i| / |U|`
of `e.fixed.geometry.parent.child` into uniform weights. -/
theorem volume_adaptedCellAt (q : Mat d) (k : ℤ) (w : Fin d → ℤ) :
    volume (adaptedCellAt q k w) = volume (adaptedCell q k) := by
  have himg : adaptedCellAt q k w =
      (fun x => adaptedCellCenter q k w + x) '' adaptedCell q k := rfl
  rw [himg, Set.image_add_left]
  exact measure_preimage_add volume _ _

end

end Recurrence
end HighContrast
end HCPolySupport
