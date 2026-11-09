/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren and OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren, OpenAI
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

/-!
# Pointwise charges for signed double-star weights

The energy of one edge is bounded by its center, crossing, or leak charges. This scalar
partition argument is independent of graph Laplacians and can compile before their
spectral infrastructure. Both double-star certificates use the same interior estimate.
-/

@[expose] public section

namespace ACMax.Pointwise

/-- Each conditional square is a nonnegative charge. -/
theorem square_charge_nonneg (condition : Prop) [Decidable condition] (weight : ℝ) :
    0 ≤ if condition then weight ^ 2 else 0 := by
  split
  · exact sq_nonneg _
  · exact le_rfl

/-- A charge is bounded by any nonnegative prefix and suffix added to it. -/
theorem le_add_nonnegative_charges {left charge right value : ℝ}
    (hleft : 0 ≤ left) (hright : 0 ≤ right) (hvalue : value ≤ charge) :
    value ≤ left + charge + right :=
  hvalue.trans ((le_add_of_nonneg_left hleft).trans (le_add_of_nonneg_right hright))

/-- Same-sign nonnegative weights pay at most the sum of their squared charges. -/
theorem nonnegative_sub_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
  nlinarith only [mul_nonneg ha hb]

open Classical in
/-- Bound one signed edge using two centers, two disjoint partner classes, and their leaks. -/
theorem double_star_edge_bound {V : Type*} (u v i j : V) (A B : Finset V)
    (au av : ℝ) (p q x : V → ℝ)
    (hp : ∀ w ∈ A, 0 ≤ p w) (hq : ∀ w ∈ B, 0 ≤ q w)
    (hAB : ∀ w ∈ A, w ∉ B)
    (hxu : x u = au) (hxv : x v = -av)
    (hxA : ∀ w ∈ A, x w = p w) (hxB : ∀ w ∈ B, x w = -q w)
    (hxZ : ∀ w, w ≠ u → w ≠ v → w ∉ A → w ∉ B → x w = 0)
    (huj : i = u → j ∈ A) (hjuA : j = u → i ∈ A)
    (hvj : i = v → j ∈ B) (hjvB : j = v → i ∈ B) :
    (x i - x j) ^ 2 ≤
      (if i = u then (au - p j) ^ 2 else 0)
      + (if j = u then (au - p i) ^ 2 else 0)
      + (if i = v then (av - q j) ^ 2 else 0)
      + (if j = v then (av - q i) ^ 2 else 0)
      + (if i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
      + (if i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0)
      + (if i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
      + (if j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
      + (if i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
      + (if j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0) := by
  classical
  -- Nonnegativity of every summand.
  have nn1 := square_charge_nonneg (i = u) ((au - p j))
  have nn2 := square_charge_nonneg (j = u) ((au - p i))
  have nn3 := square_charge_nonneg (i = v) ((av - q j))
  have nn4 := square_charge_nonneg (j = v) ((av - q i))
  have nn5 := square_charge_nonneg (i ∈ A ∧ j ∈ B) ((p i + q j))
  have nn6 := square_charge_nonneg (i ∈ B ∧ j ∈ A) ((p j + q i))
  have nn7 := square_charge_nonneg (i ∈ A ∧ j ≠ u ∧ j ∉ B) (p i)
  have nn8 := square_charge_nonneg (j ∈ A ∧ i ≠ u ∧ i ∉ B) (p j)
  have nn9 := square_charge_nonneg (i ∈ B ∧ j ≠ v ∧ j ∉ A) (q i)
  have nn10 := square_charge_nonneg (j ∈ B ∧ i ≠ v ∧ i ∉ A) (q j)
  have prefixNonneg2 := add_nonneg nn1 nn2
  have prefixNonneg3 := add_nonneg prefixNonneg2 nn3
  have prefixNonneg4 := add_nonneg prefixNonneg3 nn4
  have prefixNonneg5 := add_nonneg prefixNonneg4 nn5
  have prefixNonneg6 := add_nonneg prefixNonneg5 nn6
  have prefixNonneg7 := add_nonneg prefixNonneg6 nn7
  have prefixNonneg8 := add_nonneg prefixNonneg7 nn8
  have prefixNonneg9 := add_nonneg prefixNonneg8 nn9
  have prefixNonneg10 := add_nonneg prefixNonneg9 nn10
  have suffixNonneg9 := add_nonneg nn9 nn10
  have suffixNonneg8 := add_nonneg nn8 suffixNonneg9
  have suffixNonneg7 := add_nonneg nn7 suffixNonneg8
  have suffixNonneg6 := add_nonneg nn6 suffixNonneg7
  have suffixNonneg5 := add_nonneg nn5 suffixNonneg6
  have suffixNonneg4 := add_nonneg nn4 suffixNonneg5
  have suffixNonneg3 := add_nonneg nn3 suffixNonneg4
  have suffixNonneg2 := add_nonneg nn2 suffixNonneg3
  by_cases hiu : i = u
  · -- `u → N(u)` edge.
    have hjA : j ∈ A := huj hiu
    have e1 : (if i = u then (au - p j) ^ 2 else 0) = (au - p j) ^ 2 :=
      ite_eq_left hiu
    have hxi : x i = au := by rw [hiu]; exact hxu
    rw [hxi, hxA j hjA]
    simpa only [add_assoc, zero_add, add_zero] using
      le_add_nonnegative_charges (le_refl (0 : ℝ)) suffixNonneg2 e1.ge
  · by_cases hju : j = u
    · -- `N(u) → u` edge.
      have hiA : i ∈ A := hjuA hju
      have e2 : (if j = u then (au - p i) ^ 2 else 0) = (au - p i) ^ 2 :=
        ite_eq_left hju
      have hxj : x j = au := by rw [hju]; exact hxu
      have hval : (p i - au) ^ 2 = (au - p i) ^ 2 := by ring
      rw [hxj, hxA i hiA, hval]
      simpa only [add_assoc, zero_add, add_zero] using
        le_add_nonnegative_charges nn1 suffixNonneg3 e2.ge
    · by_cases hiv : i = v
      · -- `v → N(v)` edge.
        have hjB : j ∈ B := hvj hiv
        have e3 : (if i = v then (av - q j) ^ 2 else 0) = (av - q j) ^ 2 :=
          ite_eq_left hiv
        have hxi : x i = -av := by rw [hiv]; exact hxv
        have hval : (-av - -(q j)) ^ 2 = (av - q j) ^ 2 := by ring
        rw [hxi, hxB j hjB, hval]
        simpa only [add_assoc, zero_add, add_zero] using
          le_add_nonnegative_charges prefixNonneg2 suffixNonneg4 e3.ge
      · by_cases hjv : j = v
        · -- `N(v) → v` edge.
          have hiB : i ∈ B := hjvB hjv
          have e4 : (if j = v then (av - q i) ^ 2 else 0)
              = (av - q i) ^ 2 := ite_eq_left hjv
          have hxj : x j = -av := by rw [hjv]; exact hxv
          have hval : (-(q i) - -av) ^ 2 = (av - q i) ^ 2 := by ring
          rw [hxj, hxB i hiB, hval]
          simpa only [add_assoc, zero_add, add_zero] using
            le_add_nonnegative_charges prefixNonneg3 suffixNonneg5 e4.ge
        · -- Neither endpoint is a centre.
          by_cases hiA : i ∈ A
          · by_cases hjB : j ∈ B
            · -- cross edge `N(u) → N(v)`.
              have e5 : (if i ∈ A ∧ j ∈ B then (p i + q j) ^ 2 else 0)
                  = (p i + q j) ^ 2 := ite_eq_left ⟨hiA, hjB⟩
              have hval : (p i - -(q j)) ^ 2 = (p i + q j) ^ 2 := by ring
              rw [hxA i hiA, hxB j hjB, hval]
              simpa only [add_assoc, zero_add, add_zero] using
                le_add_nonnegative_charges prefixNonneg4 suffixNonneg6 e5.ge
            · by_cases hjA : j ∈ A
              · -- internal `N(u)` edge: charge both slots.
                have e7 : (if i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
                    = p i ^ 2 := ite_eq_left ⟨hiA, hju, hjB⟩
                have e8 : (if j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
                    = p j ^ 2 := ite_eq_left ⟨hjA, hiu, hAB i hiA⟩
                have hb : (p i - p j) ^ 2 ≤ p i ^ 2 + p j ^ 2 := by
                  exact nonnegative_sub_sq_le (hp i hiA) (hp j hjA)
                rw [hxA i hiA, hxA j hjA]
                simpa only [add_assoc, zero_add, add_zero] using
                  le_add_nonnegative_charges prefixNonneg6 suffixNonneg9 (hb.trans (add_le_add
                    e7.ge e8.ge))
              · -- leak `N(u) → Z`.
                have e7 : (if i ∈ A ∧ j ≠ u ∧ j ∉ B then p i ^ 2 else 0)
                    = p i ^ 2 := ite_eq_left ⟨hiA, hju, hjB⟩
                have hval : (p i - 0) ^ 2 = p i ^ 2 := by ring
                rw [hxA i hiA, hxZ j hju hjv hjA hjB, hval]
                simpa only [add_assoc, zero_add, add_zero] using
                  le_add_nonnegative_charges prefixNonneg6 suffixNonneg8 e7.ge
          · by_cases hiB : i ∈ B
            · by_cases hjA : j ∈ A
              · -- cross edge `N(v) → N(u)`.
                have e6 : (if i ∈ B ∧ j ∈ A then (p j + q i) ^ 2 else 0)
                    = (p j + q i) ^ 2 := ite_eq_left ⟨hiB, hjA⟩
                have hval : (-(q i) - p j) ^ 2 = (p j + q i) ^ 2 := by ring
                rw [hxB i hiB, hxA j hjA, hval]
                simpa only [add_assoc, zero_add, add_zero] using
                  le_add_nonnegative_charges prefixNonneg5 suffixNonneg7 e6.ge
              · by_cases hjB : j ∈ B
                · -- internal `N(v)` edge.
                  have e9 : (if i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
                      = q i ^ 2 := ite_eq_left ⟨hiB, hjv, hjA⟩
                  have e10 : (if j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0)
                      = q j ^ 2 := ite_eq_left ⟨hjB, hiv, hiA⟩
                  have hb : (-(q i) - -(q j)) ^ 2 ≤ q i ^ 2 + q j ^ 2 := by
                    rw [neg_sub_neg, sub_sq_comm]
                    exact nonnegative_sub_sq_le (hq i hiB) (hq j hjB)
                  rw [hxB i hiB, hxB j hjB]
                  simpa only [add_assoc, zero_add, add_zero] using
                    le_add_nonnegative_charges prefixNonneg8 (le_refl (0 : ℝ)) (hb.trans
                      (add_le_add e9.ge e10.ge))
                · -- leak `N(v) → Z`.
                  have e9 : (if i ∈ B ∧ j ≠ v ∧ j ∉ A then q i ^ 2 else 0)
                      = q i ^ 2 := ite_eq_left ⟨hiB, hjv, hjA⟩
                  have hval : (-(q i) - 0) ^ 2 = q i ^ 2 := by ring
                  rw [hxB i hiB, hxZ j hju hjv hjA hjB, hval]
                  simpa only [add_assoc, zero_add, add_zero] using
                    le_add_nonnegative_charges prefixNonneg8 nn10 e9.ge
            · by_cases hjA : j ∈ A
              · -- leak `Z → N(u)`.
                have e8 : (if j ∈ A ∧ i ≠ u ∧ i ∉ B then p j ^ 2 else 0)
                    = p j ^ 2 := ite_eq_left ⟨hjA, hiu, hiB⟩
                have hval : (0 - p j) ^ 2 = p j ^ 2 := by ring
                rw [hxZ i hiu hiv hiA hiB, hxA j hjA, hval]
                simpa only [add_assoc, zero_add, add_zero] using
                  le_add_nonnegative_charges prefixNonneg7 suffixNonneg9 e8.ge
              · by_cases hjB : j ∈ B
                · -- leak `Z → N(v)`.
                  have e10 : (if j ∈ B ∧ i ≠ v ∧ i ∉ A then q j ^ 2 else 0)
                      = q j ^ 2 := ite_eq_left ⟨hjB, hiv, hiA⟩
                  have hval : (0 - -(q j)) ^ 2 = q j ^ 2 := by ring
                  rw [hxZ i hiu hiv hiA hiB, hxB j hjB, hval]
                  simpa only [add_assoc, zero_add, add_zero] using
                    le_add_nonnegative_charges prefixNonneg9 (le_refl (0 : ℝ)) e10.ge
                · -- `Z → Z`: zero.
                  rw [hxZ i hiu hiv hiA hiB, hxZ j hju hjv hjA hjB]
                  norm_num
                  exact prefixNonneg10

end ACMax.Pointwise
