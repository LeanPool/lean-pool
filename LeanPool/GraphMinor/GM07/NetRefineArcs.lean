/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.NetSwapArcs

/-!
# The smaller arcs in a subdivided paired side

Subdivide a paired side at the parameter of a new seam vertex,
as in VII (2.6), page 218. The smaller arcs inherit internal
disjointness from the old sides. The two pieces of one side
have disjoint open parts and meet only at the subdivision point.
-/

public section
namespace GraphMinor.GM07
open Set Surface

/-- The closed subarc with its increasing affine parameter, used
when subdividing the paired sides of the refined seam graph in
VII (2.6), page 218. -/
@[expose] def sidePiece {X : Type*} [TopologicalSpace X]
    (a : Curve X) (u v : unitInterval) : Curve X :=
  ⟨a ∘ Icc.convexComb u v, a.continuous.comp (Icc.continuous_convexComb u v)⟩

/-- The first point of a side piece is its first old parameter. -/
@[simp] theorem sidePiece_zero {X : Type*} [TopologicalSpace X]
    (a : Curve X) (u v : unitInterval) : sidePiece a u v 0 = a u :=
  congrArg a (Icc.convexComb_zero u v)

/-- The last point of a side piece is its last old parameter. -/
@[simp] theorem sidePiece_one {X : Type*} [TopologicalSpace X]
    (a : Curve X) (u v : unitInterval) : sidePiece a u v 1 = a v :=
  congrArg a (Icc.convexComb_one u v)

/-- The continuous side piece has the same parameter as `pieceA`. -/
theorem sidePiece_eq_pieceA {X : Type*} [TopologicalSpace X]
    (a : Curve X) (u v : unitInterval) :
    (sidePiece a u v : unitInterval → X) = pieceA a u.val v.val := by
  let ap : Path (a 0) (a 1) := { toContinuousMap := a, source' := rfl, target' := rfl }
  exact (pieceA_eq_subpath ap u v).symm

/-- Taking the whole interval leaves the curve unchanged. -/
theorem sidePiece_zero_one {X : Type*} [TopologicalSpace X] (a : Curve X) :
    sidePiece a 0 1 = a := by
  ext t
  exact congrArg a (Icc.convexComb_zero_one t)

/-- A nondegenerate subarc of an injective side is injective. -/
theorem sidePiece_injective {X : Type*} [TopologicalSpace X]
    (a : Curve X) (ha : Function.Injective a) {u v : unitInterval} (huv : u < v) :
    Function.Injective (sidePiece a u v) := by
  rw [sidePiece_eq_pieceA]
  exact (isArcMap_pieceA ⟨a.continuous, ha⟩ u.property.1 huv v.property.2).2

/-- The range of a subarc is contained in the range of its old side. -/
theorem range_sidePiece_subset {X : Type*} [TopologicalSpace X]
    (a : Curve X) (u v : unitInterval) : range (sidePiece a u v) ⊆ range a := by
  rintro x ⟨t, rfl⟩
  exact mem_range_self (Icc.convexComb u v t)

/-- Open subarc points are open points of the old side. -/
theorem image_sidePiece_Ioo_subset {X : Type*} [TopologicalSpace X]
    (a : Curve X) {u v : unitInterval} (huv : u < v) :
    sidePiece a u v '' Ioo (0 : unitInterval) 1 ⊆ a '' Ioo (0 : unitInterval) 1 := by
  rw [sidePiece_eq_pieceA, image_pieceA_Ioo_unitInterval a u v huv]
  rintro x ⟨t, ht, rfl⟩
  exact ⟨t, ⟨(unitInterval.nonneg u).trans_lt ht.1,
    ht.2.trans_le (unitInterval.le_one v)⟩, rfl⟩

/-- Smaller arcs from internally disjoint old sides remain internally
disjoint, including when an endpoint of one piece lies inside its old side. -/
theorem sidePieces_internally_disjoint
    {X : Type*} [TopologicalSpace X] (a b : Curve X)
    (hab : ∀ t ∈ Ioo (0 : unitInterval) 1, a t ∉ range b)
    {u v : unitInterval} (huv : u < v) (m n : unitInterval) :
    ∀ t ∈ Ioo (0 : unitInterval) 1, sidePiece a u v t ∉ range (sidePiece b m n) := by
  intro t ht hbt
  obtain ⟨r, hr, hrt⟩ := image_sidePiece_Ioo_subset a huv ⟨t, ht, rfl⟩
  exact hab r hr (hrt.symm ▸ range_sidePiece_subset b m n hbt)

/-- The open first piece of one side misses its entire second piece. -/
theorem sidePiece_left_disjoint_right
    {X : Type*} [TopologicalSpace X] (a : Curve X) (ha : Function.Injective a)
    {w : unitInterval} (hw : 0 < w) :
    ∀ t ∈ Ioo (0 : unitInterval) 1, sidePiece a 0 w t ∉ range (sidePiece a w 1) := by
  intro t ht hRight
  have hLeft : sidePiece a 0 w t ∈ a '' Ioo 0 w := by
    rw [← image_pieceA_Ioo_unitInterval a 0 w hw, ← sidePiece_eq_pieceA]
    exact ⟨t, ht, rfl⟩
  obtain ⟨r, hr, hrt⟩ := hLeft
  have hRight' : sidePiece a 0 w t ∈ a '' Icc w 1 := by
    rw [sidePiece_eq_pieceA, range_pieceA_unitInterval a w 1 (unitInterval.le_one w)] at hRight
    exact hRight
  obtain ⟨s, hs, hst⟩ := hRight'
  have hsr : s = r := ha (hst.trans hrt.symm)
  exact (not_le_of_gt hr.2) (hsr ▸ hs.1)

/-- The open second piece of one side misses its entire first piece. -/
theorem sidePiece_right_disjoint_left
    {X : Type*} [TopologicalSpace X] (a : Curve X) (ha : Function.Injective a)
    {w : unitInterval} (hw : w < 1) :
    ∀ t ∈ Ioo (0 : unitInterval) 1, sidePiece a w 1 t ∉ range (sidePiece a 0 w) := by
  intro t ht hLeft
  have hRight : sidePiece a w 1 t ∈ a '' Ioo w 1 := by
    rw [← image_pieceA_Ioo_unitInterval a w 1 hw, ← sidePiece_eq_pieceA]
    exact ⟨t, ht, rfl⟩
  obtain ⟨r, hr, hrt⟩ := hRight
  have hLeft' : sidePiece a w 1 t ∈ a '' Icc 0 w := by
    rw [sidePiece_eq_pieceA, range_pieceA_unitInterval a 0 w (unitInterval.nonneg w)] at hLeft
    exact hLeft
  obtain ⟨s, hs, hst⟩ := hLeft'
  have hsr : s = r := ha (hst.trans hrt.symm)
  exact (not_le_of_gt hr.1) (hsr ▸ hs.2)

/-- Subdivide the selected side into its first piece and an additional
last piece. All other sides keep their original index and map. This
indexes the refined paired arcs of VII (2.6), page 218. -/
@[expose] def splitCurveFamily {X : Type*} [TopologicalSpace X] {r : ℕ}
    (a : Fin r → Curve X) (i : Fin r) (w : unitInterval) : Fin (r + 1) → Curve X :=
  Fin.lastCases (sidePiece (a i) w 1) (fun j => if j = i then sidePiece (a i) 0 w else a j)

/-- Every smaller side inherits its old side's range and open part. -/
theorem splitCurveFamily_range_subset
    {X : Type*} [TopologicalSpace X] {r : ℕ} (a : Fin r → Curve X)
    (i : Fin r) {w : unitInterval} (hw0 : 0 < w) (hw1 : w < 1) :
    ∀ j, ∃ k, range (splitCurveFamily a i w j) ⊆ range (a k) ∧
      splitCurveFamily a i w j '' Ioo (0 : unitInterval) 1 ⊆ a k '' Ioo (0 : unitInterval) 1 := by
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · refine ⟨i, ?_⟩
    simpa only [splitCurveFamily, Fin.lastCases_last] using
      And.intro (range_sidePiece_subset (a i) w 1) (image_sidePiece_Ioo_subset (a i) hw1)
  · by_cases hj : j = i
    · subst j
      refine ⟨i, ?_⟩
      simpa only [splitCurveFamily, Fin.lastCases_castSucc, ite_true] using
        And.intro (range_sidePiece_subset (a i) 0 w) (image_sidePiece_Ioo_subset (a i) hw0)
    · refine ⟨j, ?_⟩
      simp only [splitCurveFamily, Fin.lastCases_castSucc, ite_eq_right hj]
      exact ⟨Subset.rfl, Subset.rfl⟩

/-- All subdivided sides stay injective. -/
theorem splitCurveFamily_injective
    {X : Type*} [TopologicalSpace X] {r : ℕ} (a : Fin r → Curve X)
    (ha : ∀ j, Function.Injective (a j)) (i : Fin r)
    {w : unitInterval} (hw0 : 0 < w) (hw1 : w < 1) :
    ∀ j, Function.Injective (splitCurveFamily a i w j) := by
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa only [splitCurveFamily, Fin.lastCases_last] using sidePiece_injective (a i) (ha i) hw1
  · by_cases hj : j = i
    · subst j
      simpa [splitCurveFamily] using
        sidePiece_injective (a i) (ha i) hw0
    · simpa only [splitCurveFamily, Fin.lastCases_castSucc, ite_eq_right hj] using ha j

/-- Subdividing two families preserves disjointness between the families. -/
theorem splitCurveFamilies_internally_disjoint
    {X : Type*} [TopologicalSpace X] {r : ℕ} (a b : Fin r → Curve X)
    (hab : ∀ j k, ∀ t ∈ Ioo (0 : unitInterval) 1, a j t ∉ range (b k))
    (i : Fin r) {w : unitInterval} (hw0 : 0 < w) (hw1 : w < 1) :
    ∀ j k, ∀ t ∈ Ioo (0 : unitInterval) 1,
      splitCurveFamily a i w j t ∉ range (splitCurveFamily b i w k) := by
  intro j k t ht hkt
  obtain ⟨j₀, _, hj₀⟩ := splitCurveFamily_range_subset a i hw0 hw1 j
  obtain ⟨k₀, hk₀, _⟩ := splitCurveFamily_range_subset b i hw0 hw1 k
  obtain ⟨s, hs, hst⟩ := hj₀ ⟨t, ht, rfl⟩
  exact hab j₀ k₀ s hs (hst.symm ▸ hk₀ hkt)

/-- The two pieces of the selected side remain internally disjoint
from each other and from every unselected side. -/
theorem splitCurveFamily_internally_disjoint
    {X : Type*} [TopologicalSpace X] {r : ℕ} (a : Fin r → Curve X)
    (ha : ∀ j, Function.Injective (a j))
    (hab : ∀ j k, j ≠ k → ∀ t ∈ Ioo (0 : unitInterval) 1, a j t ∉ range (a k))
    (i : Fin r) {w : unitInterval} (hw0 : 0 < w) (hw1 : w < 1) :
    ∀ j k, j ≠ k → ∀ t ∈ Ioo (0 : unitInterval) 1,
      splitCurveFamily a i w j t ∉ range (splitCurveFamily a i w k) := by
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · intro h; exact (h rfl).elim
    · intro _
      simp only [splitCurveFamily, Fin.lastCases_last, Fin.lastCases_castSucc]
      by_cases hk : k = i
      · subst k
        rw [ite_eq_left rfl]
        exact sidePiece_right_disjoint_left _ (ha i) hw1
      · rw [ite_eq_right hk]
        simpa only [sidePiece_zero_one] using
          sidePieces_internally_disjoint (a i) (a k) (hab i k (fun h => hk h.symm)) hw1 0 1
  · intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · intro _
      simp only [splitCurveFamily, Fin.lastCases_last, Fin.lastCases_castSucc]
      by_cases hj : j = i
      · subst j
        rw [ite_eq_left rfl]
        exact sidePiece_left_disjoint_right _ (ha i) hw0
      · rw [ite_eq_right hj]
        simpa only [sidePiece_zero_one] using
          sidePieces_internally_disjoint (a j) (a i) (hab j i hj)
            (show (0 : unitInterval) < 1 from zero_lt_one) w 1
    · intro hjk
      have hjk' : j ≠ k := fun h => hjk (congrArg Fin.castSucc h)
      simp only [splitCurveFamily, Fin.lastCases_castSucc]
      by_cases hj : j = i
      · subst j
        have hk : k ≠ i := hjk'.symm
        rw [ite_eq_left rfl, ite_eq_right hk]
        simpa only [sidePiece_zero_one] using
          sidePieces_internally_disjoint (a i) (a k) (hab i k hjk') hw0 0 1
      · rw [ite_eq_right hj]
        by_cases hk : k = i
        · subst k
          rw [ite_eq_left rfl]
          simpa only [sidePiece_zero_one] using
            sidePieces_internally_disjoint (a j) (a i) (hab j i hj)
              (show (0 : unitInterval) < 1 from zero_lt_one) 0 w
        · rw [ite_eq_right hk]
          exact hab j k hjk'

/-- Subdividing a family adds exactly the image of the subdivision
point to its endpoint images. This is the new vertex of the refined
seam graph in VII (2.6), page 218. -/
theorem splitCurveFamily_endpoint_images
    {X Y : Type*} [TopologicalSpace X] {r : ℕ} (a : Fin r → Curve X)
    (i : Fin r) (w : unitInterval) (φ : X → Y) :
    {z | ∃ j, φ (splitCurveFamily a i w j 0) = z ∨ φ (splitCurveFamily a i w j 1) = z} =
      {z | ∃ j, φ (a j 0) = z ∨ φ (a j 1) = z} ∪ {φ (a i w)} := by
  ext z
  constructor
  · rintro ⟨j, hj⟩
    revert hj
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [splitCurveFamily, Fin.lastCases_last, sidePiece_zero, sidePiece_one]
      rintro (hw | h1)
      · exact Or.inr hw.symm
      · exact Or.inl ⟨i, Or.inr h1⟩
    · by_cases hji : j = i
      · subst j
        simp only [splitCurveFamily, Fin.lastCases_castSucc, ite_true, sidePiece_zero,
          sidePiece_one]
        rintro (h0 | hw)
        · exact Or.inl ⟨i, Or.inl h0⟩
        · exact Or.inr hw.symm
      · simp only [splitCurveFamily, Fin.lastCases_castSucc, ite_eq_right hji]
        exact fun hj => Or.inl ⟨j, hj⟩
  · rintro (⟨j, hj⟩ | hw)
    · by_cases hji : j = i
      · subst j
        rcases hj with h0 | h1
        · refine ⟨i.castSucc, Or.inl ?_⟩
          simpa only [splitCurveFamily, Fin.lastCases_castSucc, ite_true, sidePiece_zero] using h0
        · refine ⟨Fin.last r, Or.inr ?_⟩
          simpa only [splitCurveFamily, Fin.lastCases_last, sidePiece_one] using h1
      · refine ⟨j.castSucc, ?_⟩
        simpa only [splitCurveFamily, Fin.lastCases_castSucc, ite_eq_right hji] using hj
    · refine ⟨Fin.last r, Or.inl ?_⟩
      simpa only [splitCurveFamily, Fin.lastCases_last, sidePiece_zero] using
        (mem_singleton_iff.mp hw).symm

end GraphMinor.GM07
