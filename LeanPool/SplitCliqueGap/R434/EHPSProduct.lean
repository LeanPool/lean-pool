/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.EHPSClasses
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Cartesian powers of the EHPS support, with colour and energy estimates. -/

@[expose] public section

open Finset
open scoped BigOperators

namespace GapExtremal.R434.EHPS

/-- The grid obtained by taking `j` independent two-dimensional coordinates. -/
abbrev ProductGrid (m j : ℕ) := Fin j → Grid m
/-- An optional exterior coordinate and its class. -/
abbrev ProductClass (j : ℕ) := Option (Fin j × Class)

/-- The product of the admissible grid supports in all coordinates. -/
noncomputable def productSupport (ε : ℝ) (m j : ℕ) [NeZero m] :
    Finset (ProductGrid m j) := by
  classical
  exact univ.filter fun a => ∀ i, Region ε (gridPoint m (a i))

theorem mem_productSupport {ε : ℝ} {m j : ℕ} [NeZero m] {a : ProductGrid m j} :
    a ∈ productSupport ε m j ↔ ∀ i, Region ε (gridPoint m (a i)) := by
  classical
  simp [productSupport]

/-- The class from the first coordinate outside the support, when one exists. -/
noncomputable def productColour (ε : ℝ) (m j : ℕ) (a : ProductGrid m j) :
    ProductClass j := by
  classical
  exact if h : ∃ i, ¬ Region ε (gridPoint m (a i)) then
    some (h.choose, colour ε m (a h.choose))
    else none

/-- The coordinatewise inverse of two on the product grid of odd side length. -/
def productHalf (m j : ℕ) : ProductGrid m j :=
  fun _ => (oddHalf m, oddHalf m)

theorem productHalf_spec {m j : ℕ} (hm : Odd m) :
    2 * productHalf m j = 1 := by
  funext i
  exact Prod.ext (two_mul_oddHalf hm) (two_mul_oddHalf hm)

theorem productClass_count (j : ℕ) : Fintype.card (ProductClass j) = 8748 * j + 1 := by
  simp [Nat.mul_comm]

theorem product_mid_outside {ε : ℝ} {m j : ℕ} [NeZero m] (hm : Odd m)
    {a b : ProductGrid m j} (ha : a ∉ productSupport ε m j)
    (hb : b ∉ productSupport ε m j) (hc : productColour ε m j a = productColour ε m j b) :
    productHalf m j * (a + b) ∉ productSupport ε m j := by
  classical
  have ha' : ∃ i, ¬ Region ε (gridPoint m (a i)) :=
    not_forall.mp (fun h => ha (mem_productSupport.mpr h))
  have hb' : ∃ i, ¬ Region ε (gridPoint m (b i)) :=
    not_forall.mp (fun h => hb (mem_productSupport.mpr h))
  simp only [productColour, dite_eq_left ha', dite_eq_left hb', Option.some.injEq] at hc
  have hi : ha'.choose = hb'.choose := congrArg Prod.fst hc
  have hci := congrArg Prod.snd hc
  rw [← hi] at hci
  intro ht
  apply ha'.choose_spec
  exact (region_mid_of_colour hm hci).mp ((mem_productSupport.mp ht) ha'.choose)

/-- The sum of the coordinate grid potentials. -/
noncomputable def productPotential (ε : ℝ) (m j : ℕ) (a : ProductGrid m j) : ℝ :=
  ∑ i, gridPotential ε m (a i)

theorem product_potential_bounds {ε : ℝ} {m j : ℕ} [NeZero m]
    (hε : 0 < ε) (hε₁ : ε ≤ 1) {a : ProductGrid m j} (ha : a ∈ productSupport ε m j) :
    0 ≤ productPotential ε m j a ∧ productPotential ε m j a ≤
      (j : ℝ) * (100 * (m : ℝ) ^ 2 / ε ^ 2) := by
  constructor
  · exact sum_nonneg fun i _ => (grid_potential_bounds hε hε₁ (mem_productSupport.mp ha i)).1
  · calc
      productPotential ε m j a ≤ ∑ _i : Fin j, 100 * (m : ℝ) ^ 2 / ε ^ 2 :=
        sum_le_sum fun i _ => (grid_potential_bounds hε hε₁ (mem_productSupport.mp ha i)).2
      _ = _ := by simp

theorem product_potential_midpoint {ε : ℝ} {m j : ℕ} [NeZero m]
    (hm : Odd m) (hε : 0 < ε) (hε₁ : ε ≤ 1) {a b c : ProductGrid m j}
    (ha : a ∈ productSupport ε m j) (hb : b ∈ productSupport ε m j)
    (hc : c ∈ productSupport ε m j) (hne : a ≠ c) (heq : a + c = 2 * b) :
    1 ≤ productPotential ε m j a + productPotential ε m j c - 2 * productPotential ε m j b := by
  classical
  let d (i : Fin j) := gridPotential ε m (a i) + gridPotential ε m (c i) -
    2 * gridPotential ε m (b i)
  have hcoord (i : Fin j) : a i + c i = 2 * b i := congrFun heq i
  have hsome (i : Fin j) (hi : a i ≠ c i) : 1 ≤ d i :=
    grid_potential_midpoint hε hε₁ (mem_productSupport.mp ha i) (mem_productSupport.mp hb i)
      (mem_productSupport.mp hc i) hi (congrArg Prod.fst (hcoord i))
      (congrArg Prod.snd (hcoord i))
  have hall (i : Fin j) : 0 ≤ d i := by
    by_cases hi : a i = c i
    · have hh : (2 : Grid m) * (oddHalf m, oddHalf m) = 1 :=
        Prod.ext (two_mul_oddHalf hm) (two_mul_oddHalf hm)
      have hx : a i = b i := by
        have h2 := hcoord i
        rw [← hi, ← two_mul] at h2
        have hs := congrArg (fun x : Grid m => (oddHalf m, oddHalf m) * x) h2
        simpa only [← mul_assoc, mul_comm (oddHalf m, oddHalf m) (2 : Grid m), hh, one_mul] using hs
      have hz : d i = 0 := by
        simp only [d, ← hi, ← hx]
        ring
      rw [hz]
    · exact zero_le_one.trans (hsome i hi)
  have hn : ∃ i, a i ≠ c i := not_forall.mp (fun h => hne (funext h))
  obtain ⟨i, hi⟩ := hn
  have hs : 1 ≤ ∑ x, d x :=
    (hsome i hi).trans (single_le_sum (fun x _ => hall x) (mem_univ i))
  simpa only [d, sum_sub_distrib, sum_add_distrib, ← Finset.mul_sum, productPotential] using hs

end GapExtremal.R434.EHPS
