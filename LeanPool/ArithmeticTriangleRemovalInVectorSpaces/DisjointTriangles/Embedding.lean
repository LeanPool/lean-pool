/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Triangle.Basic
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.DisjointTriangles.Pruning

/-!
# Lifting triangles to general position

Fox and Lovász map `x ↦ (x, 1, 0)`, `y ↦ (y, -1, 1)` and `z ↦ (z, 0, -1)` into
`V × ZMod p × ZMod p`. The map preserves triangles, the first two vertices of each lifted triangle
are linearly independent, and their span contains the first two vertices of no other lifted
triangle. The pruning bound therefore holds for all `X`, `Y` and `Z`, with `#V` replaced by
`p ^ 2 * #V`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.lift p a b x`: the vector `(x, a, b)`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.card_triangles_image_lift`: lifting preserves the number
  of triangles.
* `ArithmeticTriangleRemovalInVectorSpaces.linearIndependent_of_mem_triangles_image_lift`: the
  first two vertices of a triangle of the lifted sets are linearly independent.
* `ArithmeticTriangleRemovalInVectorSpaces.eq_of_mem_span_of_mem_triangles_image_lift`: their span
  contains the first two vertices of no other triangle of the lifted sets.
* `ArithmeticTriangleRemovalInVectorSpaces.rpow_le_mul_card_rpow_mul_card_triangles_rpow`: the
  pruning bound `(η * m / 2) ^ (1 + c p) ≤ 125 * p ^ 2 * (p ^ 2 * #V) ^ (1 - c p) * D ^ c p` for
  `m` vertex-disjoint triangles in `X × Y × Z`.
-/

public section

open Finset Function Submodule

namespace ArithmeticTriangleRemovalInVectorSpaces

variable {V : Type*}

/-- The vector `(x, a, b)` of `V × ZMod p × ZMod p`. -/
private def lift (p : ℕ) (a b : ZMod p) (x : V) : V × ZMod p × ZMod p :=
  (x, a, b)

private lemma lift_injective (p : ℕ) (a b : ZMod p) : Injective (lift (V := V) p a b) :=
  fun _ _ h ↦ congrArg Prod.fst h

variable [AddCommGroup V] {p : ℕ}

/-- Lifting `X`, `Y` and `Z` preserves the number of triangles. -/
private lemma card_triangles_image_lift [DecidableEq V] (X Y Z : Finset V) :
    #(triangles (X.image (lift p 1 0)) (Y.image (lift p (-1) 1)) (Z.image (lift p 0 (-1)))) =
      #(triangles X Y Z) := by
  symm
  refine card_nbij' (fun (x, y, z) ↦ (lift p 1 0 x, lift p (-1) 1 y, lift p 0 (-1) z))
    (fun ((x, _), (y, _), (z, _)) ↦ (x, y, z)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y, z⟩ h
    simp only [mem_coe, mem_triangles, mem_image] at h ⊢
    obtain ⟨hx, hy, hz, h⟩ := h
    refine ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ⟨z, hz, rfl⟩, ?_⟩
    simp [lift, Prod.ext_iff, h]
  · rintro ⟨a, b, c⟩ h
    simp only [mem_coe, mem_triangles, mem_image] at h ⊢
    obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ⟨z, hz, rfl⟩, h⟩ := h
    simp only [lift, Prod.ext_iff, Prod.fst_add, Prod.fst_zero] at h ⊢
    obtain ⟨h, -⟩ := h
    exact ⟨hx, hy, hz, h⟩
  · rintro ⟨x, y, z⟩ -
    rfl
  · rintro ⟨a, b, c⟩ h
    simp only [mem_coe, mem_triangles, mem_image] at h
    obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ⟨z, hz, rfl⟩, -⟩ := h
    rfl

variable [Module (ZMod p) V]

/-- The first two vertices `(x, 1, 0)` and `(y, -1, 1)` of a lifted triangle are linearly
independent. -/
private lemma linearIndependent_lift (x y : V) :
    LinearIndependent (ZMod p) ![lift p 1 0 x, lift p (-1) 1 y] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  simp only [lift, Prod.ext_iff, Prod.smul_mk, Prod.fst_add, Prod.snd_add, Prod.fst_zero,
    Prod.snd_zero, smul_eq_mul] at h
  grind

/-- If `(x', 1, 0)` lies in the span of `(x, 1, 0)` and `(y, -1, 1)`, then `x' = x`. -/
private lemma eq_of_lift_mem_span_left {x y x' : V}
    (h : lift p 1 0 x' ∈ span (ZMod p) {lift p 1 0 x, lift p (-1) 1 y}) : x' = x := by
  obtain ⟨s, t, h⟩ := mem_span_pair.1 h
  simp only [lift, Prod.ext_iff, Prod.smul_mk, Prod.fst_add, Prod.snd_add, smul_eq_mul] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  obtain rfl : t = 0 := by simpa using h₃
  obtain rfl : s = 1 := by simpa using h₂
  simpa using h₁.symm

/-- If `(y', -1, 1)` lies in the span of `(x, 1, 0)` and `(y, -1, 1)`, then `y' = y`. -/
private lemma eq_of_lift_mem_span_right {x y y' : V}
    (h : lift p (-1) 1 y' ∈ span (ZMod p) {lift p 1 0 x, lift p (-1) 1 y}) : y' = y := by
  obtain ⟨s, t, h⟩ := mem_span_pair.1 h
  simp only [lift, Prod.ext_iff, Prod.smul_mk, Prod.fst_add, Prod.snd_add, smul_eq_mul] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  obtain rfl : t = 1 := by simpa using h₃
  obtain rfl : s = 0 := by simpa using h₂
  simpa using h₁.symm

variable [DecidableEq V] {X Y Z : Finset V}

section GeneralPosition

variable {a b c a' b' c' : V × ZMod p × ZMod p}

/-- The first two vertices of a triangle of the lifted sets are linearly independent. -/
private lemma linearIndependent_of_mem_triangles_image_lift
    (h : (a, b, c) ∈
      triangles (X.image (lift p 1 0)) (Y.image (lift p (-1) 1)) (Z.image (lift p 0 (-1)))) :
    LinearIndependent (ZMod p) ![a, b] := by
  simp only [mem_triangles, mem_image] at h
  obtain ⟨⟨x, -, rfl⟩, ⟨y, -, rfl⟩, -⟩ := h
  exact linearIndependent_lift x y

/-- The span of the first two vertices of a triangle of the lifted sets contains the first two
vertices of no other triangle of the lifted sets. -/
private lemma eq_of_mem_span_of_mem_triangles_image_lift
    (h : (a, b, c) ∈
      triangles (X.image (lift p 1 0)) (Y.image (lift p (-1) 1)) (Z.image (lift p 0 (-1))))
    (h' : (a', b', c') ∈
      triangles (X.image (lift p 1 0)) (Y.image (lift p (-1) 1)) (Z.image (lift p 0 (-1))))
    (ha : a' ∈ span (ZMod p) {a, b}) (hb : b' ∈ span (ZMod p) {a, b}) : a' = a ∧ b' = b := by
  simp only [mem_triangles, mem_image] at h h'
  obtain ⟨⟨x, -, rfl⟩, ⟨y, -, rfl⟩, -⟩ := h
  obtain ⟨⟨x', -, rfl⟩, ⟨y', -, rfl⟩, -⟩ := h'
  rw [eq_of_lift_mem_span_left ha, eq_of_lift_mem_span_right hb]
  exact ⟨rfl, rfl⟩

end GeneralPosition

variable [Fact p.Prime] [Fintype V] {ι : Type*} [Fintype ι] {x y z : ι → V}

/-- **Pruning in general position.** If `X × Y × Z` contains `m` vertex-disjoint triangles
`(x i, y i, z i)`, then
`(η * m / 2) ^ (1 + c p) ≤ 125 * p ^ 2 * (p ^ 2 * #V) ^ (1 - c p) * D ^ c p`, where
`η = c p / (1 + c p)` and `D` is the number of triangles. -/
lemma rpow_le_mul_card_rpow_mul_card_triangles_rpow (hx : Injective x) (hy : Injective y)
    (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z)
    (hsum : ∀ i, x i + y i + z i = 0) :
    (c p / (1 + c p) * Fintype.card ι / 2) ^ (1 + c p) ≤
      125 * p ^ 2 * (p ^ 2 * Fintype.card V) ^ (1 - c p) * #(triangles X Y Z) ^ c p := by
  have h := rpow_le_mul_rpow_mul_card_triangles_rpow (p := p)
    (fun _ _ _ ↦ linearIndependent_of_mem_triangles_image_lift)
    (fun _ _ _ h _ _ _ h' ↦ eq_of_mem_span_of_mem_triangles_image_lift h h')
    ((lift_injective _ _ _).comp hx) ((lift_injective _ _ _).comp hy)
    ((lift_injective _ _ _).comp hz) (fun i ↦ mem_image_of_mem _ (hxX i))
    (fun i ↦ mem_image_of_mem _ (hyY i)) (fun i ↦ mem_image_of_mem _ (hzZ i))
    (fun i ↦ by simp [lift, Prod.ext_iff, hsum i])
  rw [card_triangles_image_lift, Fintype.card_prod, Fintype.card_prod, ZMod.card] at h
  convert h using 4
  push_cast
  ring

end ArithmeticTriangleRemovalInVectorSpaces
