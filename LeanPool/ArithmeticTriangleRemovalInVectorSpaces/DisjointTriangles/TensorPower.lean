/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.Exponent
public import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.Triangle.Basic
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.DisjointTriangles.Embedding
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.DisjointTriangles.Pruning
import LeanPool.ArithmeticTriangleRemovalInVectorSpaces.MulticoloredSumFree.TensorPower
import Mathlib.Tactic.Positivity.Finset

/-!
# Many triangles from disjoint triangles

This file proves Theorem 3 of Fox and Lovász: if `X × Y × Z` contains `m` vertex-disjoint
triangles in a finite vector space `V` over `ZMod p`, then it contains at least
`(m / #V) ^ C p * #V ^ 2` triangles. The pruning bound gives this up to a constant factor. The
`k`-th coordinatewise powers of `X`, `Y` and `Z` contain `m ^ k` vertex-disjoint triangles and
`D ^ k` triangles in a space of size `#V ^ k`, and letting `k` grow removes the constant factor.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.rpow_le_mul_card_pow_rpow_mul_card_triangles_pow_rpow`:
  the pruning bound for the `k`-th coordinatewise powers of `X`, `Y` and `Z`.
* `ArithmeticTriangleRemovalInVectorSpaces.card_rpow_le_card_rpow_mul_card_triangles_rpow`: the
  bound `m ^ (1 + c p) ≤ #V ^ (1 - c p) * D ^ c p`.
* `ArithmeticTriangleRemovalInVectorSpaces.div_rpow_C_mul_sq_le_card_triangles`: Theorem 3 of Fox
  and Lovász.
-/

public section

open Finset Function

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- If `m ^ (1 + c) ≤ N ^ (1 - c) * D ^ c`, then `(m / N) ^ (1 + 1 / c) * N ^ 2 ≤ D`. -/
private lemma div_rpow_one_add_one_div_mul_sq_le {m N D c : ℝ} (hc : 0 < c) (hm : 0 ≤ m)
    (hN : 0 < N) (hD : 0 ≤ D) (h : m ^ (1 + c) ≤ N ^ (1 - c) * D ^ c) :
    (m / N) ^ (1 + 1 / c) * N ^ 2 ≤ D := by
  have h' := Real.rpow_le_rpow (by positivity) h (by positivity : 0 ≤ 1 / c)
  rw [← Real.rpow_mul hm, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hN.le,
    ← Real.rpow_mul hD, mul_one_div_cancel hc.ne', Real.rpow_one,
    (by grind : (1 + c) * (1 / c) = 1 + 1 / c), (by grind : (1 - c) * (1 / c) = 1 / c - 1),
    Real.rpow_sub hN, Real.rpow_one] at h'
  rw [Real.div_rpow hm hN.le, Real.rpow_add hN, Real.rpow_one]
  field_simp at h' ⊢
  linarith

variable {p : ℕ} [Fact p.Prime] {V ι : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
  [DecidableEq V] [Fintype ι] {x y z : ι → V} {X Y Z : Finset V}

/-- The pruning bound for the `k`-th coordinatewise powers of `X`, `Y` and `Z`, which contain the
`m ^ k` vertex-disjoint triangles `(x ∘ I, y ∘ I, z ∘ I)` and `D ^ k` triangles in a space of size
`#V ^ k`. -/
private lemma rpow_le_mul_card_pow_rpow_mul_card_triangles_pow_rpow (hx : Injective x)
    (hy : Injective y)
    (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z)
    (hsum : ∀ i, x i + y i + z i = 0) (k : ℕ) :
    (c p / (1 + c p) * Fintype.card ι ^ k / 2) ^ (1 + c p) ≤
      125 * p ^ 2 * (p ^ 2 * Fintype.card V ^ k) ^ (1 - c p) * (#(triangles X Y Z) ^ k) ^ c p := by
  have h := rpow_le_mul_card_rpow_mul_card_triangles_rpow (p := p)
    (X := Fintype.piFinset fun _ : Fin k ↦ X) (Y := Fintype.piFinset fun _ ↦ Y)
    (Z := Fintype.piFinset fun _ ↦ Z) hx.comp_left hy.comp_left hz.comp_left
    (fun I ↦ Fintype.mem_piFinset.2 fun t ↦ hxX (I t))
    (fun I ↦ Fintype.mem_piFinset.2 fun t ↦ hyY (I t))
    (fun I ↦ Fintype.mem_piFinset.2 fun t ↦ hzZ (I t)) (fun I ↦ funext fun t ↦ hsum (I t))
  rw [card_triangles_piFinset, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin] at h
  exact_mod_cast h

/-- If `X × Y × Z` contains `m` vertex-disjoint triangles `(x i, y i, z i)` and `D` triangles in
total, then `m ^ (1 + c p) ≤ #V ^ (1 - c p) * D ^ c p`. -/
private lemma card_rpow_le_card_rpow_mul_card_triangles_rpow (hx : Injective x) (hy : Injective y)
    (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z)
    (hsum : ∀ i, x i + y i + z i = 0) :
    (Fintype.card ι : ℝ) ^ (1 + c p) ≤
      Fintype.card V ^ (1 - c p) * #(triangles X Y Z) ^ c p := by
  have hc := c_pos (Fact.out : p.Prime).two_le
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Fintype.card_eq_zero, Nat.cast_zero, Real.zero_rpow (by linarith : 1 + c p ≠ 0)]
    positivity
  have hD := card_triangles_pos hxX hyY hzZ hsum
  refine le_of_forall_pow_le_mul_pow (M := 125 * p ^ 2 * ((p : ℝ) ^ 2) ^ (1 - c p) /
    (c p / (1 + c p) / 2) ^ (1 + c p)) (by positivity) ?_
  intro k
  have h := rpow_le_mul_card_pow_rpow_mul_card_triangles_pow_rpow (p := p) hx hy hz hxX hyY hzZ
    hsum k
  rw [mul_div_right_comm, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_pow_comm (Nat.cast_nonneg (Fintype.card ι)),
    ← Real.rpow_pow_comm (Nat.cast_nonneg (Fintype.card V)),
    ← Real.rpow_pow_comm (Nat.cast_nonneg #(triangles X Y Z))] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_pow]
  linarith

/-- **Theorem 3 of Fox and Lovász.** If `X × Y × Z` contains `m` vertex-disjoint triangles
`(x i, y i, z i)` in a finite vector space `V` over `ZMod p`, then it contains at least
`(m / #V) ^ C p * #V ^ 2` triangles. -/
lemma div_rpow_C_mul_sq_le_card_triangles (hx : Injective x) (hy : Injective y)
    (hz : Injective z) (hxX : ∀ i, x i ∈ X) (hyY : ∀ i, y i ∈ Y) (hzZ : ∀ i, z i ∈ Z)
    (hsum : ∀ i, x i + y i + z i = 0) :
    ((Fintype.card ι : ℝ) / Fintype.card V) ^ C p * Fintype.card V ^ 2 ≤ #(triangles X Y Z) :=
  div_rpow_one_add_one_div_mul_sq_le (c_pos (Fact.out : p.Prime).two_le) (Nat.cast_nonneg _)
    (Nat.cast_pos.2 Fintype.card_pos) (Nat.cast_nonneg _)
    (card_rpow_le_card_rpow_mul_card_triangles_rpow hx hy hz hxX hyY hzZ hsum)

end ArithmeticTriangleRemovalInVectorSpaces
