/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.TwoSided.AllPairsCore

/-!
# The all-pairs inequality from the antipodal inequality (`allPairs_of_antipodal`)

Step 2 of the proof of Proposition 5.2 of the paper (all sets of free coordinates).

`allPairs_core` (file `AllPairsCore.lean`) is the sum of the antipodal inequality over all
subcubes with a fixed set `F` of free coordinates.  Here the inequalities `allPairs_core` are
added over all `F`:

* left side: for fixed `x`, `F ↦ x^F` is a bijection from sets of coordinates to points,
  with inverse `y ↦ diffSet x y` (`sum_allPairsTerm`);
* right side: each coordinate lies in exactly half of all sets (`two_mul_sum_finset_sum`).
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For fixed `x`, `F ↦ x^F` is a bijection from sets of coordinates to points. -/
def flipEquiv (x : Cube ι) : Finset ι ≃ Cube ι where
  toFun F := flipSet x F
  invFun y := diffSet x y
  left_inv F := diffSet_flipSet x F
  right_inv y := flipSet_diffSet x y

/-- The terms of `x` in all the inequalities `allPairs_core` are the terms of the pairs `(x, y)`. -/
lemma sum_allPairsTerm (g : Cube ι → Bool) (w : ι → ℝ) (lam : Cube ι → ι → ℝ) (x : Cube ι) :
    ∑ F : Finset ι, allPairsTerm g w lam F x
      = ∑ y, if g x = true ∧ g y = false then
          (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹ else 0 := by
  apply Fintype.sum_equiv (flipEquiv x)
  intro F
  change allPairsTerm g w lam F x = if g x = true ∧ g (flipSet x F) = false then
    (∑ j ∈ diffSet x (flipSet x F), w j * lam x j * lam (flipSet x F) j)⁻¹ else 0
  rw [diffSet_flipSet]
  rfl

omit [DecidableEq ι] in
/-- Each coordinate lies in exactly half of all sets. -/
lemma two_mul_sum_finset_sum (β : ι → ℝ) :
    2 * ∑ F : Finset ι, ∑ j ∈ F, β j = 2 ^ Fintype.card ι * ∑ j, β j := by
  classical
  have hcompl : ∑ F : Finset ι, ∑ j ∈ Fᶜ, β j = ∑ F : Finset ι, ∑ j ∈ F, β j :=
    Fintype.sum_bijective (compl : Finset ι → Finset ι) compl_bijective
      (fun F => ∑ j ∈ Fᶜ, β j) (fun F => ∑ j ∈ F, β j) (fun _ => rfl)
  calc 2 * ∑ F : Finset ι, ∑ j ∈ F, β j
      = ∑ F : Finset ι, ∑ j ∈ F, β j + ∑ F : Finset ι, ∑ j ∈ Fᶜ, β j := by
        rw [hcompl]; ring
    _ = ∑ F : Finset ι, (∑ j ∈ F, β j + ∑ j ∈ Fᶜ, β j) := Finset.sum_add_distrib.symm
    _ = ∑ _F : Finset ι, ∑ j, β j := by
        apply Finset.sum_congr rfl
        intro F _
        exact Finset.sum_add_sum_compl F β
    _ = 2 ^ Fintype.card ι * ∑ j, β j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul]
        push_cast
        ring

/-- The all-pairs inequality (the inequality of Proposition 5.2 of the paper, multiplied by `2`)
from the antipodal inequality (Theorem 4.3). -/
theorem allPairs_of_antipodal : AntipodalInequality → AllPairsInequality := by
  intro hAntipodal ι _ _ g w hw lam hlam
  -- the left side as a sum of the terms of all the inequalities `allPairs_core`
  have hL : ∑ x ∈ univ.filter (fun x : Cube ι => g x = true),
        ∑ y ∈ univ.filter (fun y : Cube ι => g y = false),
          (∑ j ∈ diffSet x y, w j * lam x j * lam y j)⁻¹
      = ∑ x, ∑ F : Finset ι, allPairsTerm g w lam F x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : g x = true
    · rw [ite_eq_left hx, sum_allPairsTerm, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : g y = false
      · rw [ite_eq_left hy, ite_eq_left ⟨hx, hy⟩]
      · rw [ite_eq_right hy, ite_eq_right (fun h => hy h.2)]
    · rw [ite_eq_right hx, sum_allPairsTerm]
      symm
      apply Finset.sum_eq_zero
      intro y _
      rw [ite_eq_right (fun h => hx h.1)]
  -- `allPairs_core` for every `F`, added up
  have hF : ∑ F : Finset ι, ∑ x, allPairsTerm g w lam F x
      ≤ ∑ F : Finset ι, ∑ j ∈ F, (bdry g j : ℝ) / w j :=
    Finset.sum_le_sum fun F _ => allPairs_core hAntipodal g w hw lam hlam F
  rw [hL, Finset.sum_comm]
  calc 2 * ∑ F : Finset ι, ∑ x, allPairsTerm g w lam F x
      ≤ 2 * ∑ F : Finset ι, ∑ j ∈ F, (bdry g j : ℝ) / w j := by linarith
    _ = 2 ^ Fintype.card ι * ∑ j, (bdry g j : ℝ) / w j :=
        two_mul_sum_finset_sum (fun j => (bdry g j : ℝ) / w j)

end AaronsonAmbainis
