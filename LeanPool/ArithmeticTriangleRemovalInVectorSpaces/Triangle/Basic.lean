/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Triangles

A triangle in an abelian group is a triple `(x, y, z)` with `x + y + z = 0`. This file defines the
set of triangles of `X × Y × Z` for finite sets `X`, `Y` and `Z`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.triangles X Y Z`: the triangles in `X × Y × Z`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.card_triangles_le_card_sq`: there are at most `#G ^ 2`
  triangles.
* `ArithmeticTriangleRemovalInVectorSpaces.card_triangles_erase_left`: removing a vertex `v` from
  `X` removes the triangles whose first vertex is `v`, and similarly for `Y` and `Z`.
* `ArithmeticTriangleRemovalInVectorSpaces.card_triangles_piFinset`: the triangles of the
  coordinatewise powers `X ^ k`, `Y ^ k` and `Z ^ k` number `#(triangles X Y Z) ^ k`.
-/

@[expose] public section

open Finset

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The triangles of `X × Y × Z`: the triples `(x, y, z)` with `x + y + z = 0`. -/
def triangles (X Y Z : Finset G) : Finset (G × G × G) :=
  (X ×ˢ Y ×ˢ Z).filter fun (x, y, z) ↦ x + y + z = 0

variable {X Y Z X' Y' Z' : Finset G} {x y z : G}

@[simp]
lemma mem_triangles : (x, y, z) ∈ triangles X Y Z ↔ x ∈ X ∧ y ∈ Y ∧ z ∈ Z ∧ x + y + z = 0 := by
  simp [triangles, and_assoc]

lemma triangles_eq_empty_iff :
    triangles X Y Z = ∅ ↔ ∀ x ∈ X, ∀ y ∈ Y, ∀ z ∈ Z, x + y + z ≠ 0 := by
  simp only [eq_empty_iff_forall_notMem, Prod.forall, mem_triangles]
  grind

lemma triangles_mono (hX : X' ⊆ X) (hY : Y' ⊆ Y) (hZ : Z' ⊆ Z) :
    triangles X' Y' Z' ⊆ triangles X Y Z :=
  filter_subset_filter _ (product_subset_product hX (product_subset_product hY hZ))

/-- A triangle is determined by its first two vertices, so there are at most `#G ^ 2` triangles. -/
lemma card_triangles_le_card_sq [Fintype G] (X Y Z : Finset G) :
    #(triangles X Y Z) ≤ Fintype.card G ^ 2 := by
  rw [sq, ← Fintype.card_prod, ← card_univ]
  refine card_le_card_of_injOn (fun (x, y, _) ↦ (x, y)) (fun _ _ ↦ mem_univ _) ?_
  rintro ⟨x, y, z⟩ ht ⟨x', y', z'⟩ ht' h
  simp only [mem_coe, mem_triangles, Prod.mk.injEq] at ht ht' h ⊢
  grind

/-- Removing a vertex `v` from `X` removes the triangles whose first vertex is `v`. -/
lemma card_triangles_erase_left (X Y Z : Finset G) (v : G) :
    #(triangles (X.erase v) Y Z) + #((triangles X Y Z).filter fun (x, _, _) ↦ x = v) =
      #(triangles X Y Z) := by
  rw [add_comm, ← card_filter_add_card_filter_not (s := triangles X Y Z) fun (x, _, _) ↦ x = v]
  congr 2
  ext ⟨x, y, z⟩
  simp only [mem_triangles, mem_filter, mem_erase]
  grind

/-- Removing a vertex `v` from `Y` removes the triangles whose second vertex is `v`. -/
lemma card_triangles_erase_middle (X Y Z : Finset G) (v : G) :
    #(triangles X (Y.erase v) Z) + #((triangles X Y Z).filter fun (_, y, _) ↦ y = v) =
      #(triangles X Y Z) := by
  rw [add_comm, ← card_filter_add_card_filter_not (s := triangles X Y Z) fun (_, y, _) ↦ y = v]
  congr 2
  ext ⟨x, y, z⟩
  simp only [mem_triangles, mem_filter, mem_erase]
  grind

/-- Removing a vertex `v` from `Z` removes the triangles whose third vertex is `v`. -/
lemma card_triangles_erase_right (X Y Z : Finset G) (v : G) :
    #(triangles X Y (Z.erase v)) + #((triangles X Y Z).filter fun (_, _, z) ↦ z = v) =
      #(triangles X Y Z) := by
  rw [add_comm, ← card_filter_add_card_filter_not (s := triangles X Y Z) fun (_, _, z) ↦ z = v]
  congr 2
  ext ⟨x, y, z⟩
  simp only [mem_triangles, mem_filter, mem_erase]
  grind

/-- The triangles of the coordinatewise powers `X ^ k`, `Y ^ k` and `Z ^ k` are the `k`-tuples of
triangles of `X × Y × Z`. -/
lemma card_triangles_piFinset (X Y Z : Finset G) (k : ℕ) :
    #(triangles (Fintype.piFinset fun _ : Fin k ↦ X) (Fintype.piFinset fun _ ↦ Y)
      (Fintype.piFinset fun _ ↦ Z)) = #(triangles X Y Z) ^ k := by
  rw [← Fintype.card_piFinset_const]
  symm
  apply card_equiv ((Equiv.arrowProdEquivProdArrow _ _ _).trans
    ((Equiv.refl _).prodCongr (Equiv.arrowProdEquivProdArrow _ _ _)))
  simp [triangles, funext_iff, forall_and]

end ArithmeticTriangleRemovalInVectorSpaces
