/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondVertexDomains
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent

-- [TABLET NODE: P5432T1EdgeLedger]

/-!
# P5432T1EdgeLedger

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5432T1EdgeLedger (K : DiamondParameter) (D : Finset GaussianInt)
    (hD : ∀ x, x ∈ D ↔ x ∈ DiamondVertexDomains K true) :
    let edge := fun x y : GaussianInt =>
      x ∈ D ∧ y ∈ D ∧ FourNeighborAdjacent x y ∧
        (x.re.natAbs < y.re.natAbs ∨
          (x.re = y.re ∧ ¬ Even (x.re + x.im) ∧ Even (y.re + y.im)))
    let rank := fun x : GaussianInt =>
      2 * x.re.natAbs + if Even (x.re + x.im) then 1 else 0
    (∀ x y, edge x y → x ∈ D ∧ y ∈ D ∧ FourNeighborAdjacent x y) ∧
    (∀ x ∈ D, ∀ y ∈ D, FourNeighborAdjacent x y →
      (edge x y ∧ ¬ edge y x) ∨ (edge y x ∧ ¬ edge x y)) ∧
    (∀ x y, edge x y → rank x < rank y) ∧
    (∀ x ∈ D,
      ((D.filter fun y => @decide (edge y x) (Classical.propDecidable _)).card : Int) =
        if x.re = 0 then (if Even (x.re + x.im) then 2 else 0)
        else (if Even (x.re + x.im) then 3 else 1)) := by
-- BODY
  classical
  let edge := fun x y : GaussianInt =>
    x ∈ D ∧ y ∈ D ∧ FourNeighborAdjacent x y ∧
      (x.re.natAbs < y.re.natAbs ∨
        (x.re = y.re ∧ ¬ Even (x.re+x.im) ∧ Even (y.re+y.im)))
  let rank := fun x : GaussianInt =>
    2 * x.re.natAbs + if Even (x.re+x.im) then 1 else 0
  change (∀ x y, edge x y → _) ∧ (∀ x ∈ D, ∀ y ∈ D, _ → _) ∧
    (∀ x y, edge x y → rank x < rank y) ∧ _
  have increasing : ∀ x y, edge x y → rank x < rank y := by
    intro x y he
    rcases he.2.2.2 with h | ⟨heq, ho, he⟩
    · dsimp [rank]
      split_ifs <;> omega
    · dsimp only [rank]
      rw [ite_eq_right ho, ite_eq_left he, heq]
      omega
  have symm (x y : GaussianInt) (h : FourNeighborAdjacent x y) :
      FourNeighborAdjacent y x := by
    rcases h with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl (by abel))
    · exact Or.inl (by abel)
    · exact Or.inr (Or.inr (Or.inr (by abel)))
    · exact Or.inr (Or.inr (Or.inl (by abel)))
  refine ⟨(fun x y he => ⟨he.1, he.2.1, he.2.2.1⟩), ?_, increasing, ?_⟩
  · intro x hx y hy ha
    have choice :
        (x.re.natAbs < y.re.natAbs ∨
          (x.re = y.re ∧ ¬ Even (x.re+x.im) ∧ Even (y.re+y.im))) ∨
        (y.re.natAbs < x.re.natAbs ∨
          (y.re = x.re ∧ ¬ Even (y.re+y.im) ∧ Even (x.re+x.im))) := by
      have ax := Int.natCast_natAbs x.re
      have ay := Int.natCast_natAbs y.re
      simp only [Int.even_iff]
      rcases ha with rfl | rfl | rfl | rfl <;>
        norm_num at ay ⊢ <;>
        simp only [abs_eq_max_neg] at ax ay <;> omega
    rcases choice with h | h
    · have he : edge x y := ⟨hx, hy, ha, h⟩
      exact Or.inl ⟨he, fun hr => (Nat.lt_asymm (increasing x y he))
        (increasing y x hr)⟩
    · have he : edge y x := ⟨hy, hx, symm x y ha, h⟩
      exact Or.inr ⟨he, fun hr => (Nat.lt_asymm (increasing y x he))
        (increasing x y hr)⟩
  · intro x hx
    have inner (z : GaussianInt) : z ∈ D ↔
        |z.re| + |z.im - (K.1 : Int)| ≤ (K.1 : Int) - 1 := by
      rw [hD]
      change Int.natAbs z.re + Int.natAbs (z.im - (K.1 : Int)) ≤ K.1 - 1 ↔ _
      have hk := K.2
      have ha := Int.natCast_natAbs z.re
      have hb := Int.natCast_natAbs (z.im - (K.1 : Int))
      omega
    have hxI := (inner x).mp hx
    have slack (he : Even (x.re+x.im)) :
        |x.re| + |x.im - (K.1 : Int)| ≤ (K.1 : Int) - 2 := by
      have hp := Int.even_iff.mp he
      simp only [abs_eq_max_neg] at hxI ⊢
      omega
    have left_mem (hp : 0 < x.re) : x-1 ∈ D := by
      rw [inner]
      norm_num
      simp only [abs_eq_max_neg] at hxI ⊢
      omega
    have right_mem (hp : x.re < 0) : x+1 ∈ D := by
      rw [inner]
      norm_num
      simp only [abs_eq_max_neg] at hxI ⊢
      omega
    have vertical_mem (he : Even (x.re+x.im)) :
        x+⟨0, 1⟩ ∈ D ∧ x-⟨0, 1⟩ ∈ D := by
      have hs := slack he
      constructor <;> rw [inner] <;> norm_num <;>
        simp only [abs_eq_max_neg] at hs ⊢ <;> omega
    have character (y : GaussianInt) (ha : FourNeighborAdjacent y x) :
        (y.re.natAbs < x.re.natAbs ∨
          (y.re = x.re ∧ ¬ Even (y.re+y.im) ∧ Even (x.re+x.im))) ↔
        (0 < x.re ∧ y = x-1) ∨ (x.re < 0 ∧ y = x+1) ∨
          (Even (x.re+x.im) ∧ (y = x+⟨0, 1⟩ ∨ y = x-⟨0, 1⟩)) := by
      have ax := Int.natCast_natAbs x.re
      have ay := Int.natCast_natAbs y.re
      rcases symm y x ha with rfl | rfl | rfl | rfl <;>
        simp only [Int.even_iff, Zsqrtd.ext_iff] <;>
        norm_num at ay ⊢ <;>
        simp only [abs_eq_max_neg] at ax ay <;> omega
    have incoming (y : GaussianInt) : edge y x ↔
        (0 < x.re ∧ y = x-1) ∨ (x.re < 0 ∧ y = x+1) ∨
          (Even (x.re+x.im) ∧ (y = x+⟨0, 1⟩ ∨ y = x-⟨0, 1⟩)) := by
      constructor
      · intro he
        exact (character y he.2.2.1).mp he.2.2.2
      · intro hi
        have hy : y ∈ D := by
          rcases hi with ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | ⟨he, rfl | rfl⟩
          · exact left_mem hp
          · exact right_mem hp
          · exact (vertical_mem he).1
          · exact (vertical_mem he).2
        have ha : FourNeighborAdjacent y x := by
          apply symm x y
          rcases hi with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl | rfl⟩
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
        exact ⟨hy, hx, ha, (character y ha).mpr hi⟩
    have filter_eq :
        D.filter (fun y => @decide (edge y x) (Classical.propDecidable _)) =
          (if 0 < x.re then {x-1} else if x.re < 0 then {x+1} else ∅) ∪
          (if Even (x.re+x.im) then {x+⟨0, 1⟩, x-⟨0, 1⟩} else ∅) := by
      ext y
      simp only [Finset.mem_filter, decide_eq_true_eq]
      have elim : (y ∈ D ∧ edge y x) ↔ edge y x :=
        ⟨And.right, fun he => ⟨he.1, he⟩⟩
      rw [elim, incoming]
      by_cases hp : 0 < x.re <;> by_cases hn : x.re < 0 <;>
        by_cases he : Even (x.re+x.im) <;>
        simp [hp, hn, he, or_left_comm] <;> omega
    have n1 : x+⟨0, 1⟩ ≠ x-1 := by simp [Zsqrtd.ext_iff]
    have n2 : x+⟨0, 1⟩ ≠ x+1 := by simp [Zsqrtd.ext_iff]
    have n3 : x+⟨0, 1⟩ ≠ x-⟨0, 1⟩ := by simp [Zsqrtd.ext_iff]; omega
    have n4 : x-1 ≠ x-⟨0, 1⟩ := by simp [Zsqrtd.ext_iff]
    have n5 : x+1 ≠ x-⟨0, 1⟩ := by simp [Zsqrtd.ext_iff]
    rw [filter_eq]
    by_cases hp : 0 < x.re <;> by_cases hn : x.re < 0 <;>
      by_cases he : Even (x.re+x.im)
    all_goals
      simp only [hp, hn, he, ↓reduceIte]
      norm_num [n1, n2, n3, n4, n5]
      omega

end ApollonianSuperharmonic

end
