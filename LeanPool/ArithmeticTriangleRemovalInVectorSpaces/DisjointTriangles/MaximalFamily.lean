/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Triangle.Basic
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.DisjointTriangles.TensorPower

/-!
# Removing a maximum family of vertex-disjoint triangles

Let `S` be a family of vertex-disjoint triangles of `X × Y × Z` of maximum size. Removing the
vertices of `S` from `X`, `Y` and `Z` leaves no triangle, and costs at most `3 * #S` elements. By
Theorem 3 of Fox and Lovász, `X × Y × Z` contains at least `(#S / #V) ^ C p * #V ^ 2` triangles.
This proves Theorem 1 of Fox and Lovász in every finite vector space over `ZMod p`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.IsVertexDisjoint S`: no two triangles of `S` share a
  vertex.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.triangles_sdiff_image_eq_empty`: removing the vertices
  of a maximum family of vertex-disjoint triangles leaves no triangle.
* `ArithmeticTriangleRemovalInVectorSpaces.three_mul_card_le_of_card_triangles_lt`: a family of
  vertex-disjoint triangles in `X × Y × Z` has at most `ε * #V / 3` members when `X × Y × Z` has
  fewer than `(ε / 3) ^ C p * #V ^ 2` triangles.
* `ArithmeticTriangleRemovalInVectorSpaces.exists_subset_card_sdiff_add_le_of_card_triangles_lt`:
  the arithmetic triangle removal lemma with `δ = (ε / 3) ^ C p`.
-/

public section

open Finset Function

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {V : Type*}

/-- A family of triangles is vertex-disjoint if no two of its triangles share a first, second or
third vertex: each of the three projections is injective on it. -/
private def IsVertexDisjoint (S : Finset (V × V × V)) : Prop :=
  Set.InjOn (fun ((x, _, _) : V × V × V) ↦ x) S ∧
    Set.InjOn (fun ((_, y, _) : V × V × V) ↦ y) S ∧ Set.InjOn (fun ((_, _, z) : V × V × V) ↦ z) S

/-- Removing the vertices of `S` from `X` removes at most `#S` elements. -/
private lemma card_sdiff_sdiff_image_le {α : Type*} [DecidableEq α] (X : Finset α)
    (S : Finset (V × V × V)) (f : V × V × V → α) : #(X \ (X \ S.image f)) ≤ #S := by
  rw [sdiff_sdiff_right_self]
  grw [card_le_card (inf_le_right : X ⊓ S.image f ≤ _), card_image_le]

variable [DecidableEq V] {S : Finset (V × V × V)} {x y z : V}

/-- Adding a triangle that shares no vertex with the triangles of a vertex-disjoint family keeps
the family vertex-disjoint. -/
private lemma IsVertexDisjoint.insert (hS : IsVertexDisjoint S)
    (hx : x ∉ S.image fun (x, _, _) ↦ x) (hy : y ∉ S.image fun (_, y, _) ↦ y)
    (hz : z ∉ S.image fun (_, _, z) ↦ z) : IsVertexDisjoint (insert (x, y, z) S) := by
  obtain ⟨h₁, h₂, h₃⟩ := hS
  have hnot : (x, y, z) ∉ S := fun h ↦ hx (mem_image_of_mem _ h)
  rw [IsVertexDisjoint, coe_insert, Set.injOn_insert (by simpa using hnot),
    Set.injOn_insert (by simpa using hnot), Set.injOn_insert (by simpa using hnot)]
  exact ⟨⟨h₁, by simpa using hx⟩, ⟨h₂, by simpa using hy⟩, h₃, by simpa using hz⟩

variable [AddCommGroup V] {X Y Z : Finset V}

/-- Removing the vertices of a maximum family `S` of vertex-disjoint triangles leaves no
triangle. -/
private lemma triangles_sdiff_image_eq_empty (hST : S ⊆ triangles X Y Z) (hS : IsVertexDisjoint S)
    (hmax : ∀ S' ⊆ triangles X Y Z, IsVertexDisjoint S' → #S' ≤ #S) :
    triangles (X \ S.image fun (x, _, _) ↦ x) (Y \ S.image fun (_, y, _) ↦ y)
      (Z \ S.image fun (_, _, z) ↦ z) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro ⟨x, y, z⟩ ht
  simp only [mem_triangles, mem_sdiff] at ht
  obtain ⟨⟨hx, hxS⟩, ⟨hy, hyS⟩, ⟨hz, hzS⟩, hsum⟩ := ht
  have h := hmax _ (insert_subset (mem_triangles.2 ⟨hx, hy, hz, hsum⟩) hST)
    (hS.insert hxS hyS hzS)
  rw [card_insert_of_notMem fun h ↦ hxS (mem_image_of_mem _ h)] at h
  grind

variable {p : ℕ} [Fact p.Prime] [Module (ZMod p) V] [Fintype V]

/-- **Theorem 3 for a family of triangles.** If `X × Y × Z` contains a family `S` of
vertex-disjoint triangles, then it contains at least `(#S / #V) ^ C p * #V ^ 2` triangles. -/
private lemma div_rpow_C_mul_sq_le_card_triangles_of_isVertexDisjoint (hST : S ⊆ triangles X Y Z)
    (hS : IsVertexDisjoint S) :
    ((#S : ℝ) / Fintype.card V) ^ C p * Fintype.card V ^ 2 ≤ #(triangles X Y Z) := by
  obtain ⟨h₁, h₂, h₃⟩ := hS
  have h := div_rpow_C_mul_sq_le_card_triangles (p := p) (X := X) (Y := Y) (Z := Z) h₁.injective
    h₂.injective h₃.injective ?_ ?_ ?_ ?_
  · simpa using h
  all_goals
    rintro ⟨⟨x, y, z⟩, ht⟩
    have := hST ht
    simp_all

/-- If `X × Y × Z` contains a family `S` of vertex-disjoint triangles and fewer than
`(ε / 3) ^ C p * #V ^ 2` triangles, then `3 * #S ≤ ε * #V`. -/
private lemma three_mul_card_le_of_card_triangles_lt {ε : ℝ} (hε : 0 ≤ ε)
    (hST : S ⊆ triangles X Y Z)
    (hS : IsVertexDisjoint S) (h : #(triangles X Y Z) < (ε / 3) ^ C p * Fintype.card V ^ 2) :
    3 * #S ≤ ε * Fintype.card V := by
  by_contra! hlt
  have hC : 0 ≤ C p := by
    rw [C]
    linarith [one_div_pos.2 (c_pos (Fact.out : p.Prime).two_le)]
  have hεS : ε / 3 ≤ #S / Fintype.card V := by
    rw [div_le_div_iff₀ (by norm_num) (Nat.cast_pos.2 Fintype.card_pos)]
    linarith
  have h' := div_rpow_C_mul_sq_le_card_triangles_of_isVertexDisjoint (p := p) hST hS
  grw [← hεS] at h'
  linarith

/-- **Theorem 1 of Fox and Lovász** in a finite vector space `V` over `ZMod p`. If `X × Y × Z` has
fewer than `(ε / 3) ^ C p * #V ^ 2` triangles, then removing at most `ε * #V` elements from `X`,
`Y` and `Z` leaves no triangle. -/
lemma exists_subset_card_sdiff_add_le_of_card_triangles_lt {ε : ℝ} (hε : 0 ≤ ε)
    (h : #(triangles X Y Z) < (ε / 3) ^ C p * Fintype.card V ^ 2) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, ∃ Z' ⊆ Z,
      #(X \ X') + #(Y \ Y') + #(Z \ Z') ≤ ε * Fintype.card V ∧ triangles X' Y' Z' = ∅ := by
  classical
  obtain ⟨S, hS, hmax⟩ := exists_max_image ((triangles X Y Z).powerset.filter IsVertexDisjoint)
    card ⟨∅, by simp [IsVertexDisjoint]⟩
  obtain ⟨hST, hS⟩ : S ⊆ triangles X Y Z ∧ IsVertexDisjoint S := by simpa using hS
  refine ⟨_, sdiff_subset, _, sdiff_subset, _, sdiff_subset, ?_,
    triangles_sdiff_image_eq_empty hST hS fun S' hS' hdisj ↦ hmax S' (by simp [hS', hdisj])⟩
  linarith [three_mul_card_le_of_card_triangles_lt hε hST hS h,
    (Nat.cast_le (α := ℝ)).2 (card_sdiff_sdiff_image_le X S fun (x, _, _) ↦ x),
    (Nat.cast_le (α := ℝ)).2 (card_sdiff_sdiff_image_le Y S fun (_, y, _) ↦ y),
    (Nat.cast_le (α := ℝ)).2 (card_sdiff_sdiff_image_le Z S fun (_, _, z) ↦ z)]

end ArithmeticTriangleRemovalInVectorSpaces
