/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.SumOfSetsInSeveralDimensions.AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine dimension of a sumset

The affine dimension of `A + B` is at least the affine dimensions of `A` and of `B` when both
sets are nonempty, and at least the affine dimension of `A ∪ B` minus one.

## Main statements

* `Finset.affineDim_le_affineDim_add_right`, `Finset.affineDim_le_affineDim_add_left`: the
  affine dimensions of `A` and `B` are at most that of `A + B`.
* `Finset.affineDim_add_eq_of_left_eq`: if `A ⊆ ℝ^D` has affine dimension `D`, so has `A + B`.
* `Finset.affineDim_union_le_sum_add_one`: the affine dimension of `A ∪ B` is at most that
  of `A + B` plus one.
-/

public section

namespace Finset

open scoped Pointwise

variable {D : ℕ}

/-- The affine dimension of `A` is at most that of `A + B` when `B` is nonempty. -/
lemma affineDim_le_affineDim_add_right (A : Finset (Fin D → ℝ))
    {B : Finset (Fin D → ℝ)} (hB : B.Nonempty) : A.affineDim ≤ (A + B).affineDim := by
  obtain ⟨b, hb⟩ := hB
  rw [← affineDim_image_add_right b A]
  apply affineDim_mono
  rw [image_subset_iff]
  intro a ha
  exact add_mem_add ha hb

/-- The affine dimension of `B` is at most that of `A + B` when `A` is nonempty. -/
lemma affineDim_le_affineDim_add_left {A : Finset (Fin D → ℝ)} (hA : A.Nonempty)
    (B : Finset (Fin D → ℝ)) : B.affineDim ≤ (A + B).affineDim := by
  rw [add_comm]
  exact affineDim_le_affineDim_add_right B hA

/-- If `A ⊆ ℝ^D` has affine dimension `D` and `B` is nonempty, then `A + B` has affine
dimension `D`. -/
lemma affineDim_add_eq_of_left_eq {A B : Finset (Fin D → ℝ)} (hB : B.Nonempty)
    (hA : A.affineDim = D) : (A + B).affineDim = D :=
  le_antisymm (affineDim_le _)
    (hA.symm.trans_le (affineDim_le_affineDim_add_right A hB))

private lemma vectorSpan_union_le {A B : Finset (Fin D → ℝ)} {a b : Fin D → ℝ} (ha : a ∈ A)
    (hb : b ∈ B) :
    vectorSpan ℝ (↑(A ∪ B) : Set (Fin D → ℝ)) ≤
      vectorSpan ℝ (↑(A + B) : Set (Fin D → ℝ)) ⊔ Submodule.span ℝ {b - a} := by
  rw [vectorSpan_eq_span_vsub_set_right ℝ (p := a) (by simp [ha]), Submodule.span_le]
  rintro v ⟨x, hx, rfl⟩
  simp only [vsub_eq_sub, SetLike.mem_coe]
  obtain hx | hx := mem_union.1 hx
  · apply le_sup_left (b := Submodule.span ℝ {b - a})
    simpa using vsub_mem_vectorSpan ℝ (mem_coe.2 (add_mem_add hx hb))
      (mem_coe.2 (add_mem_add ha hb))
  · rw [← sub_add_sub_cancel x b a]
    apply Submodule.add_mem_sup _ (Submodule.mem_span_singleton_self _)
    simpa using vsub_mem_vectorSpan ℝ (mem_coe.2 (add_mem_add ha hx))
      (mem_coe.2 (add_mem_add ha hb))

/-- The affine span of `A ∪ B` has dimension at most one more than the affine span of `A + B`. -/
lemma affineDim_union_le_sum_add_one {A B : Finset (Fin D → ℝ)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (A ∪ B).affineDim ≤ (A + B).affineDim + 1 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  rw [affineDim_eq_finrank_vectorSpan, affineDim_eq_finrank_vectorSpan]
  apply (Submodule.finrank_mono (vectorSpan_union_le ha hb)).trans
  apply (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
  gcongr
  simpa using finrank_span_le_card ({b - a} : Set (Fin D → ℝ))

end Finset
