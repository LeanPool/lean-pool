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
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.TwoSided.Basic

/-!
# The overlap lemma and the boundary/influence identity

The overlap lemma (Lemma 4.1 of the paper; `overlap`, `overlap_pos`) and the identity
`b_j(g) = 2^(n-1) I_j(g)` (Lemma 2.1; `two_mul_bdry`).
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The overlap lemma (Lemma 4.1 of the paper): rows at points with different values overlap on
the difference set. -/
lemma overlap {g : Cube ι → Bool} {p q : Cube ι} (hpq : g p ≠ g q) {x y : ι → ℝ}
    (hx : IsRow g p x) (hy : IsRow g q y) :
    1 ≤ ∑ j ∈ diffSet p q, min (x j) (y j) := by
  -- `T` is the set `S` of the proof in the paper: `{j ∈ Δ : x_j ≤ y_j}`
  obtain ⟨T, hT⟩ : ∃ T : Finset ι, T = (diffSet p q).filter (fun j => x j ≤ y j) := ⟨_, rfl⟩
  have hTsub : T ⊆ diffSet p q := by
    rw [hT]
    exact Finset.filter_subset _ _
  -- `p^T = q^(Δ \ T)`
  have hr : flipSet p T = flipSet q (diffSet p q \ T) := by
    funext i
    simp only [flipSet]
    by_cases hi : i ∈ diffSet p q
    · have hpi : p i ≠ q i := mem_diffSet.mp hi
      by_cases hiT : i ∈ T
      · have hiT' : i ∉ diffSet p q \ T := fun h => (Finset.mem_sdiff.mp h).2 hiT
        rw [ite_eq_left hiT, ite_eq_right hiT']
        cases hp : p i <;> cases hq : q i <;> simp_all
      · have hiT' : i ∈ diffSet p q \ T := Finset.mem_sdiff.mpr ⟨hi, hiT⟩
        rw [ite_eq_right hiT, ite_eq_left hiT']
        cases hp : p i <;> cases hq : q i <;> simp_all
    · have hpi : p i = q i := by
        by_contra h
        exact hi (mem_diffSet.mpr h)
      have h1 : i ∉ T := fun h => hi (hTsub h)
      have h2 : i ∉ diffSet p q \ T := fun h => hi (Finset.mem_sdiff.mp h).1
      rw [ite_eq_right h1, ite_eq_right h2, hpi]
  -- the sum of minima is `y(Δ \ T) + x(T)`
  have hsplit : ∑ j ∈ diffSet p q \ T, y j + ∑ j ∈ T, x j
      = ∑ j ∈ diffSet p q, min (x j) (y j) := by
    rw [← Finset.sum_sdiff hTsub]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨hjΔ, hjT⟩ := Finset.mem_sdiff.mp hj
      have hnot : ¬ x j ≤ y j := fun h => hjT (by rw [hT]; exact Finset.mem_filter.mpr ⟨hjΔ, h⟩)
      exact (min_eq_right (le_of_not_ge hnot)).symm
    · apply Finset.sum_congr rfl
      intro j hj
      rw [hT] at hj
      exact (min_eq_left (Finset.mem_filter.mp hj).2).symm
  rw [← hsplit]
  have hxT : 0 ≤ ∑ j ∈ T, x j := Finset.sum_nonneg fun j _ => hx.1 j
  have hyT : 0 ≤ ∑ j ∈ diffSet p q \ T, y j := Finset.sum_nonneg fun j _ => hy.1 j
  by_cases hg : g (flipSet p T) = g p
  · have hne : g (flipSet q (diffSet p q \ T)) ≠ g q := by
      rw [← hr, hg]
      exact hpq
    have h1 := hy.2 _ hne
    linarith
  · have h1 := hx.2 T hg
    linarith

/-- Consequence of the overlap lemma: the weighted overlap is positive. -/
lemma overlap_pos {g : Cube ι → Bool} {p q : Cube ι} (hpq : g p ≠ g q) {x y : ι → ℝ}
    (hx : IsRow g p x) (hy : IsRow g q y) {w : ι → ℝ} (hw : ∀ j, 0 < w j) :
    0 < ∑ j ∈ diffSet p q, w j * x j * y j := by
  have h1 := overlap hpq hx hy
  obtain ⟨j, hj, hjpos⟩ : ∃ j ∈ diffSet p q, 0 < min (x j) (y j) := by
    by_contra hcon
    have h2 : ∑ j ∈ diffSet p q, min (x j) (y j) ≤ 0 :=
      Finset.sum_nonpos fun j hj => not_lt.mp fun hp => hcon ⟨j, hj, hp⟩
    linarith
  have hxj : 0 < x j := lt_of_lt_of_le hjpos (min_le_left _ _)
  have hyj : 0 < y j := lt_of_lt_of_le hjpos (min_le_right _ _)
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (mul_nonneg (hw i).le (hx.1 i)) (hy.1 i)
  · exact ⟨j, hj, mul_pos (mul_pos (hw j) hxj) hyj⟩

/-- The points where flipping `j` changes `g` are twice the bichromatic `j`-edges. -/
lemma card_sensitive (g : Cube ι → Bool) (j : ι) :
    (univ.filter fun x : Cube ι => g (flipSet x {j}) ≠ g x).card = 2 * bdry g j := by
  have hsplit : (univ.filter fun x : Cube ι => g (flipSet x {j}) ≠ g x)
      = (univ.filter fun x : Cube ι => g x = true ∧ g (flipSet x {j}) = false)
        ∪ (univ.filter fun x : Cube ι => g x = false ∧ g (flipSet x {j}) = true) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    cases hx : g x <;> cases hy : g (flipSet x {j}) <;> simp
  have hdisj : Disjoint (univ.filter fun x : Cube ι => g x = true ∧ g (flipSet x {j}) = false)
      (univ.filter fun x : Cube ι => g x = false ∧ g (flipSet x {j}) = true) := by
    rw [Finset.disjoint_filter]
    intro x _ h1 h2
    rw [h1.1] at h2
    exact Bool.noConfusion h2.1
  have hB : (univ.filter fun x : Cube ι => g x = false ∧ g (flipSet x {j}) = true).card
      = (univ.filter fun x : Cube ι => g x = true ∧ g (flipSet x {j}) = false).card := by
    apply Finset.card_bij (fun x _ => flipSet x {j})
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [flipSet_flipSet_self]
      exact ⟨hx.2, hx.1⟩
    · intro x _ y _ h
      have h' := congrArg (fun z => flipSet z {j}) h
      simpa [flipSet_flipSet_self] using h'
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨flipSet y {j}, ?_, flipSet_flipSet_self y {j}⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [flipSet_flipSet_self]
      exact ⟨hy.2, hy.1⟩
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hB]
  unfold bdry
  ring

/-- Lemma 2.1 of the paper: `2 b_j(g) = 2^n I_j(g)`, that is, `b_j(g) = 2^(n-1) I_j(g)`. -/
lemma two_mul_bdry (g : Cube ι → Bool) (j : ι) :
    2 * (bdry g j : ℝ) = 2 ^ Fintype.card ι * infl g j := by
  have h2 : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  unfold infl
  rw [card_sensitive]
  push_cast
  field_simp

end AaronsonAmbainis
