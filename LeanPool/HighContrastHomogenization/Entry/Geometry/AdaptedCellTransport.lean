/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.AdaptedCell
public import LeanPool.HighContrastHomogenization.Entry.Geometry.MaximalCells
public import LeanPool.HighContrastHomogenization.Entry.Setup.AdaptedGridCells

/-!
# High-contrast homogenization: Entry.Geometry.AdaptedCellTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Transport for adapted cells

For an invertible matrix `q`, an adapted cell is the image of the corresponding
standard cell under the linear map `matVecMul q`: the center of the adapted cell
is the image of the standard center, and its volume is `|det q|` times the
standard volume. Preimages along `matVecMul q` convert adapted cells into
standard cells and back, preserving inclusion, disjointness and maximality, so
that the maximal adapted cells of a set are exactly the transported maximal
standard cells. These are the geometric support lemmas for the adapted Whitney
partitions of `l.two.grid.whitney`.
-/

open HCPolySupport.HighContrast (adaptedCellCenter)
open HCPolySupport.HighContrast (adaptedCellTranslate centeredCube standardCell
  standardCellCenter)
namespace HCPolySupport.HighContrast.Geometry

open MeasureTheory

variable {d : ℕ}

theorem adaptedCellAtCenter_eq_affine_standardCell
    (q : Mat d) (r : ℤ) (w : Fin d → ℤ) :
    adaptedCellAtCenter q r w = matVecMul q '' standardCell d r w := by
  ext x
  constructor
  · intro hx
    rcases mem_adaptedCellTranslate_iff.mp hx with ⟨v, hv, hvx⟩
    refine ⟨standardCellCenter r w + v, ?_, ?_⟩
    · rw [Recurrence.standardCell_eq_image]
      exact ⟨v, hv, rfl⟩
    · rw [← hvx, Recurrence.adaptedCellCenter_eq]
      ext i
      simp [matVecMul, mul_add, Finset.sum_add_distrib]
  · rintro ⟨u, hu, rfl⟩
    change matVecMul q u ∈ adaptedCellTranslate q r (adaptedCellCenter q r w)
    rw [mem_adaptedCellTranslate_iff]
    rw [Recurrence.standardCell_eq_image] at hu
    rcases hu with ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    rw [Recurrence.adaptedCellCenter_eq]
    ext i
    simp [matVecMul, mul_add, Finset.sum_add_distrib]

theorem adaptedCellCenter_injective (q : Mat d) (r : ℤ) (hq : IsUnit q) :
    Function.Injective (adaptedCellCenter q r : (Fin d → ℤ) → Vec d) := by
  intro w w' h
  have hmul :
      matVecMul q (fun i => (w i : ℝ)) =
        matVecMul q (fun i => (w' i : ℝ)) := by
    have hscale : (3 : ℝ) ^ r ≠ 0 := by positivity
    funext i
    have hi := congrFun h i
    change ((3 : ℝ) ^ r • matVecMul q (fun i => (w i : ℝ))) i =
      ((3 : ℝ) ^ r • matVecMul q (fun i => (w' i : ℝ))) i at hi
    simp only [Pi.smul_apply, smul_eq_mul] at hi
    exact mul_left_cancel₀ hscale hi
  have hvec :
      (fun i : Fin d => (w i : ℝ)) = fun i : Fin d => (w' i : ℝ) := by
    rw [matVecMul_eq_mulVec, matVecMul_eq_mulVec] at hmul
    exact Matrix.mulVec_injective_iff_isUnit.mpr hq hmul
  funext i
  exact_mod_cast congrFun hvec i

theorem volume_adaptedCellAtCenter (q : Mat d) (r : ℤ) (w : Fin d → ℤ) :
    volume (adaptedCellAtCenter q r w)
      = ENNReal.ofReal |q.det| * ENNReal.ofReal ((3 : ℝ) ^ r) ^ d := by
  unfold adaptedCellAtCenter
  rw [volume_adaptedCellTranslate]

theorem volume_adaptedCellAtCenter_ne_top (q : Mat d) (r : ℤ) (w : Fin d → ℤ) :
    volume (adaptedCellAtCenter q r w) ≠ ⊤ := by
  rw [volume_adaptedCellAtCenter]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem preimage_matVecMul_adaptedCellTranslate_eq
    {q q' : Mat d} (hq : IsUnit q) (j : ℤ) (y : Vec d) :
    (matVecMul q) ⁻¹' adaptedCellTranslate q' j y =
      adaptedCellTranslate (q⁻¹ * q') j (matVecMul q⁻¹ y) := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq
  have hinj : Function.Injective (fun x : Vec d => Matrix.mulVec q x) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hq
  ext x
  rw [Set.mem_preimage, mem_adaptedCellTranslate_iff, mem_adaptedCellTranslate_iff]
  constructor
  · rintro ⟨v, hv, hvx⟩
    refine ⟨v, hv, ?_⟩
    have hmul :
        Matrix.mulVec q (matVecMul q⁻¹ y + matVecMul (q⁻¹ * q') v) =
          Matrix.mulVec q x := by
      rw [matVecMul_eq_mulVec, matVecMul_eq_mulVec]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv q hdet, Matrix.one_mulVec]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv q hdet, Matrix.one_mul]
      simpa [matVecMul_eq_mulVec] using hvx
    simpa [matVecMul_eq_mulVec] using hinj hmul
  · rintro ⟨v, hv, hvx⟩
    refine ⟨v, hv, ?_⟩
    rw [← hvx]
    rw [matVecMul_eq_mulVec q', matVecMul_eq_mulVec q, matVecMul_eq_mulVec q⁻¹,
      matVecMul_eq_mulVec (q⁻¹ * q'),
      Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv q hdet, Matrix.one_mulVec]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv q hdet, Matrix.one_mul]

theorem preimage_matVecMul_eq_image_inv
    {q : Mat d} (hq : IsUnit q) (W : Set (Vec d)) :
    (matVecMul q) ⁻¹' W = matVecMul q⁻¹ '' W := by
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq
  ext x
  constructor
  · intro hx
    refine ⟨matVecMul q x, hx, ?_⟩
    rw [matVecMul_eq_mulVec q⁻¹, matVecMul_eq_mulVec q, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul q hdet, Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    have : matVecMul q (matVecMul q⁻¹ y) = y := by
      rw [matVecMul_eq_mulVec q, matVecMul_eq_mulVec q⁻¹, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv q hdet, Matrix.one_mulVec]
    simpa [Set.mem_preimage, this] using hy

theorem volume_preimage_matVecMul_ne_top
    {q : Mat d} (hq : IsUnit q) {W : Set (Vec d)} (hW : volume W ≠ ⊤) :
    volume ((matVecMul q) ⁻¹' W) ≠ ⊤ := by
  rw [preimage_matVecMul_eq_image_inv hq W]
  have himage :
      matVecMul q⁻¹ '' W = (fun v : Vec d => (0 : Vec d) + matVecMul q⁻¹ v) '' W := by
    ext x
    simp
  rw [himage, Transport.volume_image_affine]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW

theorem IsAdaptedCellIn.to_standard_preimage {W : Set (Vec d)} {q : Mat d}
    {n r : ℤ} {w : Fin d → ℤ} (h : IsAdaptedCellIn W q n r w) :
    IsCellIn ((matVecMul q) ⁻¹' W) n r w := by
  refine ⟨h.1, ?_⟩
  intro x hx
  exact h.2 ((adaptedCellAtCenter_eq_affine_standardCell q r w).symm ▸ ⟨x, hx, rfl⟩)

theorem IsCellIn.of_standard_preimage {W : Set (Vec d)} {q : Mat d}
    {n r : ℤ} {w : Fin d → ℤ}
    (h : IsCellIn ((matVecMul q) ⁻¹' W) n r w) :
    IsAdaptedCellIn W q n r w := by
  refine ⟨h.1, ?_⟩
  rw [adaptedCellAtCenter_eq_affine_standardCell]
  rintro x ⟨u, hu, rfl⟩
  exact h.2 hu

theorem standardCell_subset_preimage_iff_adaptedCellAtCenter_subset
    (W : Set (Vec d)) (q : Mat d) (r : ℤ) (w : Fin d → ℤ) :
    standardCell d r w ⊆ (matVecMul q) ⁻¹' W ↔ adaptedCellAtCenter q r w ⊆ W := by
  constructor
  · intro h x hx
    rw [adaptedCellAtCenter_eq_affine_standardCell] at hx
    rcases hx with ⟨u, hu, rfl⟩
    exact h hu
  · intro h x hx
    exact h ((adaptedCellAtCenter_eq_affine_standardCell q r w).symm ▸ ⟨x, hx, rfl⟩)

theorem isMaximalAdaptedCellIn_iff_isMaximalCellIn_preimage
    (W : Set (Vec d)) (q : Mat d) (hq : IsUnit q) (n r : ℤ) (w : Fin d → ℤ) :
    IsMaximalAdaptedCellIn W q n r w ↔
      IsMaximalCellIn ((matVecMul q) ⁻¹' W) n r w := by
  constructor
  · intro h
    refine ⟨IsAdaptedCellIn.to_standard_preimage h.1, ?_⟩
    intro r' w' hcell hsub
    have hadapt : IsAdaptedCellIn W q n r' w' := IsCellIn.of_standard_preimage hcell
    have hsubA : adaptedCellAtCenter q r w ⊆ adaptedCellAtCenter q r' w' := by
      rw [adaptedCellAtCenter_eq_affine_standardCell, adaptedCellAtCenter_eq_affine_standardCell]
      exact Set.image_mono hsub
    have heq := h.2 r' w' hadapt hsubA
    have himage := congrArg (Set.preimage (matVecMul q)) heq
    rw [adaptedCellAtCenter_eq_affine_standardCell, adaptedCellAtCenter_eq_affine_standardCell]
      at himage
    ext x
    constructor <;> intro hx
    · have : matVecMul q x ∈ matVecMul q '' standardCell d r w := by
        change x ∈ matVecMul q ⁻¹' (matVecMul q '' standardCell d r w)
        rw [← himage]
        exact ⟨x, hx, rfl⟩
      rcases this with ⟨y, hy, hyx⟩
      have hy_eq : y = x := by
        rw [matVecMul_eq_mulVec, matVecMul_eq_mulVec] at hyx
        exact Matrix.mulVec_injective_iff_isUnit.mpr hq hyx
      simpa [hy_eq] using hy
    · have : matVecMul q x ∈ matVecMul q '' standardCell d r' w' := by
        change x ∈ matVecMul q ⁻¹' (matVecMul q '' standardCell d r' w')
        rw [himage]
        exact ⟨x, hx, rfl⟩
      rcases this with ⟨y, hy, hyx⟩
      have hy_eq : y = x := by
        rw [matVecMul_eq_mulVec, matVecMul_eq_mulVec] at hyx
        exact Matrix.mulVec_injective_iff_isUnit.mpr hq hyx
      simpa [hy_eq] using hy
  · intro h
    refine ⟨IsCellIn.of_standard_preimage h.1, ?_⟩
    intro r' w' hcell hsub
    have hstd : IsCellIn ((matVecMul q) ⁻¹' W) n r' w' :=
      IsAdaptedCellIn.to_standard_preimage hcell
    have hsubS : standardCell d r w ⊆ standardCell d r' w' := by
      intro x hx
      have hxA : matVecMul q x ∈ adaptedCellAtCenter q r w := by
        rw [adaptedCellAtCenter_eq_affine_standardCell]
        exact ⟨x, hx, rfl⟩
      have hxA' := hsub hxA
      rw [adaptedCellAtCenter_eq_affine_standardCell] at hxA'
      rcases hxA' with ⟨y, hy, hyx⟩
      have hy_eq : y = x := by
        rw [matVecMul_eq_mulVec, matVecMul_eq_mulVec] at hyx
        exact Matrix.mulVec_injective_iff_isUnit.mpr hq hyx
      simpa [hy_eq] using hy
    have heq := h.2 r' w' hstd hsubS
    rw [adaptedCellAtCenter_eq_affine_standardCell, adaptedCellAtCenter_eq_affine_standardCell]
    rw [heq]

/-- Aligned adapted cells in one invertible grid are nested or disjoint. -/
theorem adaptedCellAtCenter_subset_or_disjoint {q : Mat d} (hq : IsUnit q)
    {r r' : ℤ} (hrr' : r ≤ r') (w w' : Fin d → ℤ) :
    adaptedCellAtCenter q r w ⊆ adaptedCellAtCenter q r' w' ∨
      Disjoint (adaptedCellAtCenter q r w) (adaptedCellAtCenter q r' w') := by
  rw [adaptedCellAtCenter_eq_affine_standardCell, adaptedCellAtCenter_eq_affine_standardCell]
  rcases standardCell_subset_or_disjoint hrr' w w' with hsub | hdis
  · exact Or.inl (Set.image_mono hsub)
  · refine Or.inr (Set.disjoint_left.mpr ?_)
    rintro x ⟨u, hu, rfl⟩ ⟨v, hv, h⟩
    have hvu := Matrix.mulVec_injective_iff_isUnit.mpr hq h
    exact Set.disjoint_left.mp hdis hu (hvu ▸ hv)

/-- The affine image of all grid faces, over every integer generation, is null. -/
theorem volume_image_iUnion_gridFaces (q : Mat d) :
    volume (matVecMul q '' ⋃ k : ℤ, gridFaces d k) = 0 := by
  have himage : matVecMul q '' (⋃ k : ℤ, gridFaces d k) =
      (fun v : Vec d => (0 : Vec d) + matVecMul q v) '' (⋃ k : ℤ, gridFaces d k) := by
    simp only [zero_add]
  rw [himage, Transport.volume_image_affine, measure_iUnion_null (fun k => volume_gridFaces k),
    mul_zero]

end HCPolySupport.HighContrast.Geometry
