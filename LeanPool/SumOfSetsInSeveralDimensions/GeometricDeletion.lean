/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.SumOfSetsInSeveralDimensions.AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Removing the origin from the summands

This is Lemma 2.1 of Ruzsa's paper. Let `X, Y ⊆ ℝ^D` be finite sets with at least two points that
contain `0` and whose other elements are lexicographically positive. Write `X' = X \ {0}` and
`Y' = Y \ {0}`, let `d` be the affine dimension of `X + Y` and let `U` be the vector span of
`X' + Y'`. The lemma `geometric_deletion_cases` states that one of the following holds.

* `X' + Y'` has dimension `d` and `|X + Y| ≥ |X' + Y'| + d + 1`. The points of `X + Y` outside
  `X' + Y'` are `0` and the points of `C = (X' ∪ Y') \ (X' + Y')`. Every point of `X + Y` is a sum
  of points of `C`, by induction along the lexicographic order, so `C` has at least `d` points.
* `X' + Y'` has dimension `d - 1` and `|X + Y| ≥ |Y| + |X' + Y'|`. Here `X'` has a point outside
  `U`, and `Y` is disjoint from `X' + Y'`.
* `X' + Y` has dimension `d - 1` and `|X + Y| ≥ |Y| + |X' + Y|`. Here `X' + Y'` has dimension
  `d - 2`, and `Y` is disjoint from `X' + Y`.
* `X + Y'` has dimension `d - 1` and `|X + Y| ≥ |X| + |X + Y'|`. Here `X' ⊆ U`, and `X` is disjoint
  from `X + Y'`.
-/

public section

namespace SumOfSetsInSeveralDimensions

open Finset
open scoped Pointwise

variable {D d : ℕ} {X Y : Finset (Fin D → ℝ)} {x₀ y₀ : Fin D → ℝ}

private lemma affineDim_le_finrank_of_sub_mem {S : Finset (Fin D → ℝ)}
    {U : Submodule ℝ (Fin D → ℝ)} {p : Fin D → ℝ} (hp : p ∈ S) (hS : ∀ x ∈ S, x - p ∈ U) :
    S.affineDim ≤ Module.finrank ℝ U := by
  rw [affineDim_eq_finrank_vectorSpan, vectorSpan_eq_span_vsub_set_right ℝ (mem_coe.2 hp)]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact hS x hx

private lemma affineDim_add_le_finrank (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    {W : Submodule ℝ (Fin D → ℝ)} (hX : ∀ x ∈ X, x ∈ W) (hY : ∀ y ∈ Y, y ∈ W) :
    (X + Y).affineDim ≤ Module.finrank ℝ W := by
  refine affineDim_le_finrank_of_sub_mem (p := 0) (by simpa using add_mem_add h0X h0Y) ?_
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hz
  simpa using W.add_mem (hX x hx) (hY y hy)

private lemma finrank_sup_span_singleton_le (U : Submodule ℝ (Fin D → ℝ)) (v : Fin D → ℝ) :
    Module.finrank ℝ ↥(U ⊔ ℝ ∙ v) ≤ Module.finrank ℝ U + 1 := by
  apply (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
  gcongr
  simpa using finrank_span_le_card ({v} : Set (Fin D → ℝ))

private lemma toLex_nonneg (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y) {y : Fin D → ℝ} (hy : y ∈ Y) :
    0 ≤ toLex y := by
  obtain rfl | hy0 := eq_or_ne y 0
  · simp
  · exact (hposY y hy hy0).le

private lemma add_ne_zero_of_ne_zero_left (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y) {x y : Fin D → ℝ} (hx : x ∈ X) (hx0 : x ≠ 0)
    (hy : y ∈ Y) : x + y ≠ 0 := by
  intro h
  have h' := add_pos_of_pos_of_nonneg (hposX x hx hx0) (toLex_nonneg hposY hy)
  rw [← toLex_add, h, toLex_zero] at h'
  exact lt_irrefl 0 h'

private lemma zero_notMem_erase_add_erase (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y) : (0 : Fin D → ℝ) ∉ X.erase 0 + Y.erase 0 := by
  intro h
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_add.1 h
  exact add_ne_zero_of_ne_zero_left hposX hposY (mem_of_mem_erase hx) (ne_of_mem_erase hx)
    (mem_of_mem_erase hy) hxy

/-! ### The case in which the dimension does not drop -/

private noncomputable def deletedComplement (X Y : Finset (Fin D → ℝ)) : Finset (Fin D → ℝ) :=
  (X.erase 0 ∪ Y.erase 0) \ (X.erase 0 + Y.erase 0)

private lemma disjoint_deletedComplement :
    Disjoint (X.erase 0 + Y.erase 0) (deletedComplement X Y) :=
  disjoint_sdiff

private lemma mem_erase_union_erase {x y : Fin D → ℝ} (hx : x ∈ X) (hy : y ∈ Y) (h0 : x + y ≠ 0)
    (h : x + y ∉ X.erase 0 + Y.erase 0) : x + y ∈ X.erase 0 ∪ Y.erase 0 := by
  obtain rfl | hx0 := eq_or_ne x 0
  · simp_all
  obtain rfl | hy0 := eq_or_ne y 0
  · simp_all
  exact absurd (add_mem_add (mem_erase.2 ⟨hx0, hx⟩) (mem_erase.2 ⟨hy0, hy⟩)) h

private lemma mem_span_deletedComplement (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x) (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y)
    {z : Fin D → ℝ} (hz : z ∈ X + Y) :
    z ∈ Submodule.span ℝ (deletedComplement X Y : Set (Fin D → ℝ)) := by
  classical
  by_contra hzC
  obtain ⟨w, hw, hmin⟩ := exists_min_image
    ((X + Y).filter (· ∉ Submodule.span ℝ (deletedComplement X Y : Set (Fin D → ℝ)))) toLex
    ⟨z, mem_filter.2 ⟨hz, hzC⟩⟩
  obtain ⟨hwXY, hwC⟩ := mem_filter.1 hw
  have hlt : ∀ v ∈ X + Y, toLex v < toLex w →
      v ∈ Submodule.span ℝ (deletedComplement X Y : Set (Fin D → ℝ)) := by
    intro v hv hvw
    by_contra hvC
    exact (hmin v (mem_filter.2 ⟨hv, hvC⟩)).not_gt hvw
  apply hwC
  by_cases hw' : w ∈ X.erase 0 + Y.erase 0
  · obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hw'
    apply Submodule.add_mem
    · apply hlt x (by simpa using add_mem_add (mem_of_mem_erase hx) h0Y)
      rw [toLex_add]
      exact lt_add_of_pos_right _ (hposY y (mem_of_mem_erase hy) (ne_of_mem_erase hy))
    · apply hlt y (by simpa using add_mem_add h0X (mem_of_mem_erase hy))
      rw [toLex_add]
      exact lt_add_of_pos_left _ (hposX x (mem_of_mem_erase hx) (ne_of_mem_erase hx))
  · obtain rfl | hw0 := eq_or_ne w 0
    · exact Submodule.zero_mem _
    apply Submodule.subset_span
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hwXY
    exact mem_sdiff.2 ⟨mem_erase_union_erase hx hy hw0 hw', hw'⟩

private lemma insert_union_deletedComplement_subset (h0X : 0 ∈ X) (h0Y : 0 ∈ Y) :
    insert 0 (X.erase 0 + Y.erase 0 ∪ deletedComplement X Y) ⊆ X + Y := by
  intro z hz
  obtain rfl | hz | hz := by simpa only [mem_insert, mem_union] using hz
  · simpa using add_mem_add h0X h0Y
  · exact add_subset_add (erase_subset _ _) (erase_subset _ _) hz
  · obtain hz | hz := mem_union.1 (mem_sdiff.1 hz).1
    · simpa using add_mem_add (mem_of_mem_erase hz) h0Y
    · simpa using add_mem_add h0X (mem_of_mem_erase hz)

private lemma card_erase_add_erase_add_le (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x) (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y) :
    #(X.erase 0 + Y.erase 0) + (X + Y).affineDim + 1 ≤ #(X + Y) := by
  have hC : (X + Y).affineDim ≤ #(deletedComplement X Y) := by
    refine (affineDim_le_finrank_of_sub_mem (p := 0)
      (by simpa using add_mem_add h0X h0Y) ?_).trans (finrank_span_finset_le_card _)
    intro z hz
    simpa using mem_span_deletedComplement h0X h0Y hposX hposY hz
  refine le_trans ?_ (card_le_card (insert_union_deletedComplement_subset h0X h0Y))
  rw [card_insert_of_notMem, card_union_of_disjoint disjoint_deletedComplement]
  · grind
  · rw [mem_union, not_or]
    exact ⟨zero_notMem_erase_add_erase hposX hposY, fun h ↦ by simp [deletedComplement] at h⟩

/-! ### The cases in which the dimension drops -/

/-- The vector span `U` of `X' + Y'`. -/
private noncomputable def deletedSpan (X Y : Finset (Fin D → ℝ)) : Submodule ℝ (Fin D → ℝ) :=
  vectorSpan ℝ (↑(X.erase 0 + Y.erase 0) : Set (Fin D → ℝ))

private lemma finrank_deletedSpan :
    Module.finrank ℝ (deletedSpan X Y) = (X.erase 0 + Y.erase 0).affineDim :=
  (affineDim_eq_finrank_vectorSpan _).symm

private lemma sub_mem_deletedSpan_left (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    {x : Fin D → ℝ} (hx : x ∈ X.erase 0) : x - x₀ ∈ deletedSpan X Y := by
  simpa [deletedSpan] using vsub_mem_vectorSpan ℝ (mem_coe.2 (add_mem_add hx hy₀))
    (mem_coe.2 (add_mem_add hx₀ hy₀))

private lemma sub_mem_deletedSpan_right (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    {y : Fin D → ℝ} (hy : y ∈ Y.erase 0) : y - y₀ ∈ deletedSpan X Y := by
  simpa [deletedSpan] using vsub_mem_vectorSpan ℝ (mem_coe.2 (add_mem_add hx₀ hy))
    (mem_coe.2 (add_mem_add hx₀ hy₀))

private lemma sub_add_mem_deletedSpan (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    {z : Fin D → ℝ} (hz : z ∈ X.erase 0 + Y.erase 0) : z - (x₀ + y₀) ∈ deletedSpan X Y :=
  vsub_mem_vectorSpan ℝ (mem_coe.2 hz) (mem_coe.2 (add_mem_add hx₀ hy₀))

private lemma mem_of_le_left (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    {W : Submodule ℝ (Fin D → ℝ)} (hUW : deletedSpan X Y ≤ W) (hx₀W : x₀ ∈ W) {x : Fin D → ℝ}
    (hx : x ∈ X) : x ∈ W := by
  obtain rfl | hx0 := eq_or_ne x 0
  · exact W.zero_mem
  rw [← sub_add_cancel x x₀]
  exact W.add_mem (hUW (sub_mem_deletedSpan_left hx₀ hy₀ (mem_erase.2 ⟨hx0, hx⟩))) hx₀W

private lemma mem_of_le_right (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0)
    {W : Submodule ℝ (Fin D → ℝ)} (hUW : deletedSpan X Y ≤ W) (hy₀W : y₀ ∈ W) {y : Fin D → ℝ}
    (hy : y ∈ Y) : y ∈ W := by
  obtain rfl | hy0 := eq_or_ne y 0
  · exact W.zero_mem
  rw [← sub_add_cancel y y₀]
  exact W.add_mem (hUW (sub_mem_deletedSpan_right hx₀ hy₀ (mem_erase.2 ⟨hy0, hy⟩))) hy₀W

private lemma affineDim_add_le_add_two (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0) :
    (X + Y).affineDim ≤ (X.erase 0 + Y.erase 0).affineDim + 2 := by
  refine (affineDim_add_le_finrank h0X h0Y
    (W := deletedSpan X Y ⊔ ℝ ∙ x₀ ⊔ ℝ ∙ y₀) ?_ ?_).trans ?_
  · intro x hx
    exact mem_of_le_left hx₀ hy₀ (le_sup_left.trans le_sup_left)
      (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x₀))) hx
  · intro y hy
    exact mem_of_le_right hx₀ hy₀ (le_sup_left.trans le_sup_left)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y₀)) hy
  · grind [finrank_sup_span_singleton_le (deletedSpan X Y ⊔ ℝ ∙ x₀) y₀,
      finrank_sup_span_singleton_le (deletedSpan X Y) x₀, finrank_deletedSpan (X := X) (Y := Y)]

/-- The case in which `x₀ ∈ U`: then `X ⊆ U`, and `X + Y'` lies in the translate `U + y₀`, which
does not meet `U`. -/
private lemma deletion_right_of_mem (h0X : 0 ∈ X) (h0Y : 0 ∈ Y) (hx₀ : x₀ ∈ X.erase 0)
    (hy₀ : y₀ ∈ Y.erase 0) (hdim : (X + Y).affineDim = d)
    (hlt : (X.erase 0 + Y.erase 0).affineDim < d) (hxU : x₀ ∈ deletedSpan X Y) :
    (X + Y.erase 0).affineDim = d - 1 ∧ #X + #(X + Y.erase 0) ≤ #(X + Y) := by
  have hX : ∀ x ∈ X, x ∈ deletedSpan X Y := fun x hx ↦ mem_of_le_left hx₀ hy₀ le_rfl hxU hx
  have hyU : y₀ ∉ deletedSpan X Y := by
    intro hyU
    grind [affineDim_add_le_finrank h0X h0Y hX
      (fun y hy ↦ mem_of_le_right hx₀ hy₀ le_rfl hyU hy), finrank_deletedSpan (X := X) (Y := Y)]
  have hd : d ≤ (X.erase 0 + Y.erase 0).affineDim + 1 := by
    grind [affineDim_add_le_finrank h0X h0Y (W := deletedSpan X Y ⊔ ℝ ∙ y₀)
      (fun x hx ↦ Submodule.mem_sup_left (hX x hx))
      (fun y hy ↦ mem_of_le_right hx₀ hy₀ le_sup_left
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y₀)) hy),
      finrank_sup_span_singleton_le (deletedSpan X Y) y₀, finrank_deletedSpan (X := X) (Y := Y)]
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine (affineDim_le_finrank_of_sub_mem (U := deletedSpan X Y)
      (by simpa using add_mem_add h0X hy₀) ?_).trans ?_
    · intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hz
      rw [add_sub_assoc]
      exact Submodule.add_mem _ (hX x hx) (sub_mem_deletedSpan_right hx₀ hy₀ hy)
    · grind [finrank_deletedSpan (X := X) (Y := Y)]
  · grind [affineDim_mono (add_subset_add_right (t := Y.erase 0) (erase_subset 0 X))]
  · rw [← card_union_of_disjoint]
    · refine card_le_card (union_subset ?_ (add_subset_add_left (erase_subset _ _)))
      intro x hx
      simpa using add_mem_add hx h0Y
    · rw [disjoint_left]
      intro z hz hzY
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hzY
      apply hyU
      rw [(by abel : y₀ = x + y - x - (y - y₀))]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ (hX _ hz) (hX x hx))
        (sub_mem_deletedSpan_right hx₀ hy₀ hy)

/-- The case in which `x₀ ∉ U` and `U` has dimension `d - 1`: `Y` does not meet `X' + Y'`. -/
private lemma card_add_card_erase_add_erase_le (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y) (h0X : 0 ∈ X) (hx₀ : x₀ ∈ X.erase 0)
    (hy₀ : y₀ ∈ Y.erase 0) (hxU : x₀ ∉ deletedSpan X Y) :
    #Y + #(X.erase 0 + Y.erase 0) ≤ #(X + Y) := by
  rw [← card_union_of_disjoint]
  · refine card_le_card (union_subset ?_ (add_subset_add (erase_subset _ _) (erase_subset _ _)))
    intro y hy
    simpa using add_mem_add h0X hy
  · rw [disjoint_left]
    intro z hzY hz
    have hz0 : z ≠ 0 := fun h ↦ zero_notMem_erase_add_erase hposX hposY (h ▸ hz)
    apply hxU
    rw [(by abel : x₀ = z - y₀ - (z - (x₀ + y₀)))]
    exact Submodule.sub_mem _ (sub_mem_deletedSpan_right hx₀ hy₀ (mem_erase.2 ⟨hz0, hzY⟩))
      (sub_add_mem_deletedSpan hx₀ hy₀ hz)

private lemma notMem_sup_of_affineDim_eq (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hx₀ : x₀ ∈ X.erase 0) (hy₀ : y₀ ∈ Y.erase 0) (hdim : (X + Y).affineDim = d)
    (hdel : (X.erase 0 + Y.erase 0).affineDim + 2 = d) :
    y₀ ∉ deletedSpan X Y ⊔ ℝ ∙ x₀ := by
  intro hyW
  grind [affineDim_add_le_finrank h0X h0Y
    (fun x hx ↦ mem_of_le_left hx₀ hy₀ le_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x₀)) hx)
    (fun y hy ↦ mem_of_le_right hx₀ hy₀ le_sup_left hyW hy),
    finrank_sup_span_singleton_le (deletedSpan X Y) x₀, finrank_deletedSpan (X := X) (Y := Y)]

private lemma affineDim_erase_add_eq (h0Y : 0 ∈ Y) (hx₀ : x₀ ∈ X.erase 0)
    (hy₀ : y₀ ∈ Y.erase 0) (hyW : y₀ ∉ deletedSpan X Y ⊔ ℝ ∙ x₀) :
    (X.erase 0 + Y).affineDim = (X.erase 0 + Y.erase 0).affineDim + 1 := by
  rw [← finrank_deletedSpan, ← Submodule.finrank_sup_span_singleton
    (fun h ↦ hyW (Submodule.mem_sup_left h))]
  apply le_antisymm
  · refine affineDim_le_finrank_of_sub_mem (by simpa using add_mem_add hx₀ h0Y) ?_
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hz
    rw [add_sub_right_comm]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (sub_mem_deletedSpan_left hx₀ hy₀ hx))
      (mem_of_le_right hx₀ hy₀ le_sup_left
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y₀)) hy)
  · rw [affineDim_eq_finrank_vectorSpan]
    apply Submodule.finrank_mono
    refine sup_le (vectorSpan_mono ℝ (coe_subset.2 (add_subset_add_left (erase_subset _ _)))) ?_
    rw [Submodule.span_singleton_le_iff_mem]
    simpa using vsub_mem_vectorSpan ℝ (mem_coe.2 (add_mem_add hx₀ (mem_of_mem_erase hy₀)))
      (mem_coe.2 (add_mem_add hx₀ h0Y))

/-- The case in which `x₀ ∉ U` and `U` has dimension `d - 2`: `Y` does not meet `X' + Y`. -/
private lemma card_add_card_erase_add_le (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x)
    (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y) (h0X : 0 ∈ X) (hx₀ : x₀ ∈ X.erase 0)
    (hy₀ : y₀ ∈ Y.erase 0) (hxU : x₀ ∉ deletedSpan X Y) (hyW : y₀ ∉ deletedSpan X Y ⊔ ℝ ∙ x₀) :
    #Y + #(X.erase 0 + Y) ≤ #(X + Y) := by
  rw [← card_union_of_disjoint]
  · refine card_le_card (union_subset ?_ (add_subset_add_right (erase_subset _ _)))
    intro y hy
    simpa using add_mem_add h0X hy
  · rw [disjoint_left]
    intro z hzY hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_add.1 hz
    have hz0 := add_ne_zero_of_ne_zero_left hposX hposY (mem_of_mem_erase hx) (ne_of_mem_erase hx)
      hy
    obtain rfl | hy0 := eq_or_ne y 0
    · apply hyW
      rw [add_zero] at hzY hz0
      rw [(by abel : y₀ = x - x₀ - (x - y₀) + x₀)]
      exact Submodule.add_mem_sup (Submodule.sub_mem _ (sub_mem_deletedSpan_left hx₀ hy₀ hx)
        (sub_mem_deletedSpan_right hx₀ hy₀ (mem_erase.2 ⟨hz0, hzY⟩)))
        (Submodule.mem_span_singleton_self x₀)
    · apply hxU
      rw [(by abel : x₀ = x + y - y₀ - (y - y₀) - (x - x₀))]
      exact Submodule.sub_mem _ (Submodule.sub_mem _
        (sub_mem_deletedSpan_right hx₀ hy₀ (mem_erase.2 ⟨hz0, hzY⟩))
        (sub_mem_deletedSpan_right hx₀ hy₀ (mem_erase.2 ⟨hy0, hy⟩)))
        (sub_mem_deletedSpan_left hx₀ hy₀ hx)

/-- **Lemma 2.1 of Ruzsa.** Let `X` and `Y` contain `0`, have at least two points each, and have
all other elements lexicographically positive, and let `X + Y` have affine dimension `d`. Then
removing `0` from `X`, from `Y` or from both gives a sumset of dimension `d` with at least `d + 1`
fewer points, or a sumset of dimension `d - 1` with at least `|Y|` or `|X|` fewer points, as
listed in the statement. -/
lemma geometric_deletion_cases (h0X : 0 ∈ X) (h0Y : 0 ∈ Y)
    (hposX : ∀ x ∈ X, x ≠ 0 → 0 < toLex x) (hposY : ∀ y ∈ Y, y ≠ 0 → 0 < toLex y)
    (hXcard : 2 ≤ #X) (hYcard : 2 ≤ #Y) (hdim : (X + Y).affineDim = d) :
    ((X.erase 0 + Y.erase 0).affineDim = d ∧
      #(X.erase 0 + Y.erase 0) + d + 1 ≤ #(X + Y)) ∨
      ((X.erase 0 + Y.erase 0).affineDim = d - 1 ∧
        #Y + #(X.erase 0 + Y.erase 0) ≤ #(X + Y)) ∨
      ((X.erase 0 + Y).affineDim = d - 1 ∧ #Y + #(X.erase 0 + Y) ≤ #(X + Y)) ∨
      ((X + Y.erase 0).affineDim = d - 1 ∧ #X + #(X + Y.erase 0) ≤ #(X + Y)) := by
  obtain hdel | hdel := eq_or_ne ((X.erase 0 + Y.erase 0).affineDim) d
  · left
    refine ⟨hdel, ?_⟩
    grind [card_erase_add_erase_add_le h0X h0Y hposX hposY]
  right
  have hlt : (X.erase 0 + Y.erase 0).affineDim < d := by
    grind [affineDim_mono (add_subset_add (erase_subset 0 X) (erase_subset 0 Y))]
  obtain ⟨x₀, hx₀⟩ : (X.erase 0).Nonempty := by
    rw [← card_pos, card_erase_of_mem h0X]
    grind
  obtain ⟨y₀, hy₀⟩ : (Y.erase 0).Nonempty := by
    rw [← card_pos, card_erase_of_mem h0Y]
    grind
  by_cases hxU : x₀ ∈ deletedSpan X Y
  · right
    right
    exact deletion_right_of_mem h0X h0Y hx₀ hy₀ hdim hlt hxU
  obtain hcodim | hcodim : (X.erase 0 + Y.erase 0).affineDim + 1 = d ∨
      (X.erase 0 + Y.erase 0).affineDim + 2 = d := by
    grind [affineDim_add_le_add_two h0X h0Y hx₀ hy₀]
  · left
    exact ⟨by grind, card_add_card_erase_add_erase_le hposX hposY h0X hx₀ hy₀ hxU⟩
  · right
    left
    have hyW := notMem_sup_of_affineDim_eq h0X h0Y hx₀ hy₀ hdim hcodim
    exact ⟨by grind [affineDim_erase_add_eq h0Y hx₀ hy₀ hyW],
      card_add_card_erase_add_le hposX hposY h0X hx₀ hy₀ hxU hyW⟩

end SumOfSetsInSeveralDimensions
