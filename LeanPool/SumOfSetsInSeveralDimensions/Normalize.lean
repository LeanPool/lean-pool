/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.SumOfSetsInSeveralDimensions.AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Tactic.Abel

/-!
# Translating a set so that its lexicographic minimum is the origin

Order `ℝ^D` lexicographically. The translate `normalize S` of a nonempty finite set `S` by minus
its least element contains `0`, and its other elements are positive. Cardinalities of sets and
sumsets and the affine dimension of a sumset do not change under this translation.
-/

public section

namespace SumOfSetsInSeveralDimensions

open Finset
open scoped Pointwise

variable {D : ℕ}

private noncomputable def lexMin (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) : Fin D → ℝ :=
  ofLex ((S.image toLex).min' (hS.image toLex))

private lemma lexMin_mem {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) : lexMin S hS ∈ S := by
  obtain ⟨x, hx, hxmin⟩ := mem_image.1 (min'_mem (S.image toLex) (hS.image toLex))
  rwa [lexMin, ← hxmin, ofLex_toLex]

private lemma lexMin_le {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) {x : Fin D → ℝ}
    (hx : x ∈ S) : toLex (lexMin S hS) ≤ toLex x := by
  rw [lexMin, toLex_ofLex]
  exact min'_le _ _ (mem_image_of_mem toLex hx)

private lemma lexMin_sub_pos {S : Finset (Fin D → ℝ)} (hS : S.Nonempty)
    {x : Fin D → ℝ} (hx : x ∈ S) (hne : x ≠ lexMin S hS) :
    0 < toLex (x - lexMin S hS) := by
  rw [toLex_sub, sub_pos]
  apply (lexMin_le hS hx).lt_of_ne
  simpa using hne.symm

/-- The translate of a nonempty finite set `S ⊆ ℝ^D` by minus its lexicographically least
element. -/
noncomputable def normalize (S : Finset (Fin D → ℝ)) (hS : S.Nonempty) : Finset (Fin D → ℝ) :=
  S.image fun x ↦ x - lexMin S hS

/-- Translation does not change the number of points. -/
lemma normalize_card {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) : #(normalize S hS) = #S :=
  card_image_of_injective _ (sub_left_injective (b := lexMin S hS))

/-- The translated set contains the origin. -/
lemma zero_mem_normalize {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) : 0 ∈ normalize S hS :=
  mem_image.2 ⟨lexMin S hS, lexMin_mem hS, sub_self _⟩

/-- The translated set is nonempty. -/
lemma normalize_nonempty {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) :
    (normalize S hS).Nonempty :=
  ⟨0, zero_mem_normalize hS⟩

/-- The nonzero elements of the translated set are lexicographically positive. -/
lemma normalize_pos_of_ne_zero {S : Finset (Fin D → ℝ)} (hS : S.Nonempty)
    {x : Fin D → ℝ} (hx : x ∈ normalize S hS) (hx0 : x ≠ 0) : 0 < toLex x := by
  obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
  apply lexMin_sub_pos hS hy
  rintro rfl
  exact hx0 (sub_self _)

private lemma normalize_add {A B : Finset (Fin D → ℝ)} (hA : A.Nonempty) (hB : B.Nonempty) :
    normalize A hA + normalize B hB =
      (A + B).image fun x ↦ x - (lexMin A hA + lexMin B hB) := by
  ext x
  simp only [normalize, mem_add, mem_image]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by abel⟩
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨a - lexMin A hA, ⟨a, ha, rfl⟩, b - lexMin B hB, ⟨b, hb, rfl⟩, by abel⟩

/-- The sum of the translates of `A` and `B` has as many points as `A + B`. -/
lemma normalize_add_card {A B : Finset (Fin D → ℝ)} (hA : A.Nonempty) (hB : B.Nonempty) :
    #(normalize A hA + normalize B hB) = #(A + B) := by
  rw [normalize_add]
  exact card_image_of_injective _ sub_left_injective

/-- The sum of the translates of `A` and `B` has the affine dimension of `A + B`. -/
lemma normalize_add_dim {A B : Finset (Fin D → ℝ)} (hA : A.Nonempty) (hB : B.Nonempty) :
    (normalize A hA + normalize B hB).affineDim = (A + B).affineDim := by
  rw [normalize_add, affineDim_image_sub]

end SumOfSetsInSeveralDimensions
