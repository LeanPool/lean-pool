/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Int

/-! The R419 fractional witness and the R433 exposing dual for H54. -/

@[expose] public section

open Finset

namespace GapExtremal.R434.H54

/-- The three local indices of a candidate triangle, in part order. -/
abbrev Triangle := Fin 5 × Fin 5 × Fin 5
/-- The edge kind and two local endpoint indices. -/
abbrev Edge := Fin 3 × Fin 5 × Fin 5

/-- The seven triangles removed from the tripartite template. -/
def deleted : List Triangle :=
  [(2, 2, 2), (1, 2, 1), (3, 1, 4), (0, 3, 1), (0, 4, 0), (2, 3, 0), (4, 0, 3)]

/-- Edge indices 0, 1 and 2 refer to the pairs of parts 01, 12 and 02. -/
def onEdge (t : Triangle) (e : Edge) : Bool :=
  if e.1 = 0 then decide (e.2 = (t.1, t.2.1))
  else if e.1 = 1 then decide (e.2 = (t.2.1, t.2.2))
  else decide (e.2 = (t.1, t.2.2))

/-- Template edges left after removing the edges of the deleted triangles. -/
def edges : Finset Edge :=
  univ.filter fun e => !deleted.any (onEdge · e)

/-- The triangles supported by the remaining template edges. -/
def triangles : Finset Triangle :=
  univ.filter fun t =>
    (0, t.1, t.2.1) ∈ edges ∧ (1, t.2.1, t.2.2) ∈ edges ∧ (2, t.1, t.2.2) ∈ edges

/-- The support of the explicit fractional triangle packing. -/
def support : Finset Triangle :=
  {(0,0,2),(0,0,4),(0,1,2),(0,1,3),(0,2,3),(0,2,4),
   (1,0,0),(1,0,2),(1,1,0),(1,1,2),(1,3,3),(1,3,4),(1,4,3),(1,4,4),
   (2,0,1),(2,0,4),(2,1,1),(2,1,3),(2,4,3),(2,4,4),
   (3,0,0),(3,0,1),(3,2,0),(3,2,3),(3,3,2),(3,3,3),(3,4,1),(3,4,2),
   (4,1,0),(4,1,1),(4,2,0),(4,2,4),(4,3,2),(4,3,4),(4,4,1),(4,4,2)}

/-- The integer edge price in the finite dual certificate. -/
def price (e : Edge) : ℤ :=
  match e.1.val, e.2.1.val, e.2.2.val with
  | 0,0,2 => 3
  | 0,2,4 => 1
  | 0,3,0 => 1
  | 0,3,3 => -2
  | 0,3,4 => -1
  | 0,4,1 => 1
  | 0,4,3 => -2
  | 0,4,4 => -1
  | 1,0,0 => -1
  | 1,0,4 => 1
  | 1,1,0 => -1
  | 1,1,3 => 1
  | 1,2,3 => -2
  | 1,2,4 => -2
  | 1,3,2 => 2
  | 1,4,1 => 2
  | 1,4,2 => 1
  | 2,0,3 => -1
  | 2,0,4 => -1
  | 2,1,0 => 1
  | 2,2,3 => -1
  | 2,2,4 => -1
  | 2,3,1 => -1
  | 2,3,3 => 2
  | 2,4,1 => -1
  | 2,4,4 => 2
  | _,_,_ => 0

/-- The total assigned weight of triangles meeting a given edge. -/
def load (S : Finset Triangle) (x : Triangle → ℤ) (e : Edge) : ℤ :=
  ∑ t ∈ S.filter (onEdge · e), x t

/-- The total certificate price of the edges of a triangle. -/
def triPrice (t : Triangle) : ℤ :=
  ∑ e ∈ edges.filter (fun e => onEdge t e), price e

theorem edge_count : edges.card = 54 := by decide +kernel
theorem triangle_count : triangles.card = 45 := by decide +kernel
theorem support_count : support.card = 36 := by decide +kernel
theorem support_valid : support ⊆ triangles := by decide +kernel
theorem balanced_edge_counts : ∀ i : Fin 3, (edges.filter (fun e => e.1 = i)).card = 18 := by
  decide +kernel

theorem twice_on_each_edge : ∀ e : Edge, e ∈ edges →
    (support.filter (onEdge · e)).card = 2 := by decide +kernel

theorem price_sum : ∑ e ∈ edges, price e = 0 := by decide +kernel

theorem price_support : ∀ t : Triangle, t ∈ triangles →
    0 ≤ triPrice t ∧ (t ∉ support → 0 < triPrice t) := by decide +kernel

theorem support_price_zero : ∀ t : Triangle, t ∈ support → triPrice t = 0 := by
  decide +kernel

theorem no_integral_cover (x : Triangle → ℤ)
    (hn : ∀ t ∈ triangles, 0 ≤ x t)
    (hc : ∀ e ∈ edges, load triangles x e = 1) : False := by
  classical
  have exchange :
      ∑ t ∈ triangles, x t * triPrice t = ∑ e ∈ edges, price e * load triangles x e := by
    simp only [triPrice, load, sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro t ht
    split <;> simp [*, mul_comm]
  have hzero : ∑ t ∈ triangles, x t * triPrice t = 0 := by
    rw [exchange, ← price_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [hc e he, mul_one]
  have hx : ∀ t ∈ triangles, t ∉ support → x t = 0 := by
    intro t ht hs
    have hnon : ∀ u ∈ triangles, 0 ≤ x u * triPrice u :=
      fun u hu => mul_nonneg (hn u hu) (price_support u hu).1
    have hle : x t * triPrice t ≤ 0 :=
      hzero ▸ Finset.single_le_sum (f := fun u => x u * triPrice u) hnon ht
    exact le_antisymm (nonpos_of_mul_nonpos_left hle ((price_support t ht).2 hs)) (hn t ht)
  have hs : ∀ e ∈ edges, load support x e = 1 := by
    intro e he
    rw [← hc e he]
    unfold load
    apply Finset.sum_subset (Finset.filter_subset_filter _ support_valid)
    intro t ht hnot
    rw [Finset.mem_filter] at ht
    exact hx t ht.1 fun h => hnot (Finset.mem_filter.mpr ⟨h, ht.2⟩)
  have h1 := hs (1,2,3) (by decide +kernel)
  have h2 := hs (0,0,2) (by decide +kernel)
  have h3 := hs (2,0,4) (by decide +kernel)
  have h4 := hs (0,0,0) (by decide +kernel)
  have h5 := hs (1,0,2) (by decide +kernel)
  have h6 := hs (0,1,0) (by decide +kernel)
  have h7 := hs (1,0,0) (by decide +kernel)
  have h8 := hs (2,3,0) (by decide +kernel)
  have h9 := hs (0,3,2) (by decide +kernel)
  have pair_sum (e : Edge) (a b : Triangle) (hab : a ≠ b)
      (hpair : support.filter (onEdge · e) = {a, b}) (h : load support x e = 1) :
      x a + x b = 1 := by
    unfold load at h
    rwa [hpair, Finset.sum_pair hab] at h
  have p1 := pair_sum (1,2,3) (3,2,3) (0,2,3) (by decide) (by decide +kernel) h1
  have p2 := pair_sum (0,0,2) (0,2,3) (0,2,4) (by decide) (by decide +kernel) h2
  have p3 := pair_sum (2,0,4) (0,2,4) (0,0,4) (by decide) (by decide +kernel) h3
  have p4 := pair_sum (0,0,0) (0,0,4) (0,0,2) (by decide) (by decide +kernel) h4
  have p5 := pair_sum (1,0,2) (0,0,2) (1,0,2) (by decide) (by decide +kernel) h5
  have p6 := pair_sum (0,1,0) (1,0,2) (1,0,0) (by decide) (by decide +kernel) h6
  have p7 := pair_sum (1,0,0) (1,0,0) (3,0,0) (by decide) (by decide +kernel) h7
  have p8 := pair_sum (2,3,0) (3,0,0) (3,2,0) (by decide) (by decide +kernel) h8
  have p9 := pair_sum (0,3,2) (3,2,0) (3,2,3) (by decide) (by decide +kernel) h9
  omega

end GapExtremal.R434.H54
