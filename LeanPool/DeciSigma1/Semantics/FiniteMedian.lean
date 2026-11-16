/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Satisfiability.Decide
public import LeanPool.DeciSigma1.Semantics.Median
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Medians of finite trees

The median of three finite trees is finite. This module computes it by recursion on the trees
(`median`) and proves that it represents `treeMedian` (`median_toTree`). It is used to transfer the
symmetrization of solutions to finite trees.

## Main declarations

- `FiniteMedian.median`: the median of three finite trees.
- `FiniteMedian.median_toTree`: it represents the median of the corresponding trees.
-/

@[expose] public section


namespace DeciSigma1.Semantics.FiniteMedian

open DeciSigma1.Semantics.Tree

variable {n : ℕ}

/-! ## The finite median -/

/-- The root symbol of a finite tree. -/
def rootLabel : FTree n → Sym
  | .bot => .bot
  | .top => .top
  | .node _ => .f

/-- The `i`-th child of a node; a leaf is its own child. -/
def child : FTree n → Fin n → FTree n
  | .node a, i => a i
  | .bot, _ => .bot
  | .top, _ => .top

@[simp] theorem rootLabel_bot : rootLabel (.bot : FTree n) = .bot := rfl
@[simp] theorem rootLabel_top : rootLabel (.top : FTree n) = .top := rfl
@[simp] theorem child_bot (i : Fin n) : child (.bot : FTree n) i = .bot := rfl
@[simp] theorem child_top (i : Fin n) : child (.top : FTree n) i = .top := rfl
@[simp] theorem child_node (a : Fin n → FTree n) (i : Fin n) : child (.node a) i = a i := rfl

theorem height_child_le (t : FTree n) (i : Fin n) : (child t i).height ≤ t.height := by
  cases t with
  | bot => simp
  | top => simp
  | node a => exact (FTree.height_child_lt a i).le

theorem height_child_lt_of_root {t : FTree n} (h : rootLabel t = .f) (i : Fin n) :
    (child t i).height < t.height := by
  cases t with
  | bot => simp at h
  | top => simp at h
  | node a => exact FTree.height_child_lt a i

/-- A constructor median needs a constructor input. -/
theorem medianSym_eq_f {a b c : Sym} (h : medianSym a b c = .f) :
    a = .f ∨ b = .f ∨ c = .f := by
  revert h
  cases a <;> cases b <;> cases c <;> decide

theorem median_decreasing {a b c : FTree n}
    (h : medianSym (rootLabel a) (rootLabel b) (rootLabel c) = .f) (i : Fin n) :
    (child a i).height + (child b i).height + (child c i).height <
      a.height + b.height + c.height := by
  have ha := height_child_le a i
  have hb := height_child_le b i
  have hc := height_child_le c i
  rcases medianSym_eq_f h with h | h | h
  · have := height_child_lt_of_root h i; omega
  · have := height_child_lt_of_root h i; omega
  · have := height_child_lt_of_root h i; omega

/-- The median of three finite trees, computed from the root down. -/
def median (a b c : FTree n) : FTree n :=
  if _h : medianSym (rootLabel a) (rootLabel b) (rootLabel c) = .f then
    .node fun i => median (child a i) (child b i) (child c i)
  else if medianSym (rootLabel a) (rootLabel b) (rootLabel c) = .bot then .bot else .top
termination_by a.height + b.height + c.height
decreasing_by exact median_decreasing _h i

theorem median_of_bot {a b c : FTree n}
    (h : medianSym (rootLabel a) (rootLabel b) (rootLabel c) = .bot) : median a b c = .bot := by
  rw [median]; simp [h]

theorem median_of_top {a b c : FTree n}
    (h : medianSym (rootLabel a) (rootLabel b) (rootLabel c) = .top) : median a b c = .top := by
  rw [median]; simp [h]

theorem median_of_f {a b c : FTree n}
    (h : medianSym (rootLabel a) (rootLabel b) (rootLabel c) = .f) :
    median a b c = .node fun i => median (child a i) (child b i) (child c i) := by
  rw [median]; simp [h]

@[simp] theorem extendedLabel_toTree_nil (t : FTree n) :
    extendedLabel t.toTree [] = rootLabel t := by
  cases t <;> rfl

theorem extendedLabel_toTree_cons (t : FTree n) (i : Fin n) (w : List (Fin n)) :
    extendedLabel t.toTree (i :: w) = extendedLabel (child t i).toTree w := by
  cases t <;> simp

/-- The extended labels of the finite median are the medians of the extended labels. -/
theorem extendedLabel_median (a b c : FTree n) (w : List (Fin n)) :
    extendedLabel (median a b c).toTree w =
      medianSym (extendedLabel a.toTree w) (extendedLabel b.toTree w)
          (extendedLabel c.toTree w) := by
  induction w generalizing a b c with
  | nil =>
    simp only [extendedLabel_toTree_nil]
    cases hm : medianSym (rootLabel a) (rootLabel b) (rootLabel c)
    · rw [median_of_bot hm]; rfl
    · rw [median_of_f hm]; rfl
    · rw [median_of_top hm]; rfl
  | cons i w ih =>
    have habs : ∀ t : FTree n, rootLabel t ≠ .f →
        extendedLabel t.toTree (i :: w) = rootLabel t := fun t ht => by
      have h := extendedLabel_absorb t.toTree [] (i :: w) (by simpa using ht)
      simpa using h
    cases hm : medianSym (rootLabel a) (rootLabel b) (rootLabel c) with
    | bot =>
      rw [median_of_bot hm]
      have h := medianSym_absorb (rootLabel a) (rootLabel b) (rootLabel c)
        (extendedLabel a.toTree (i :: w)) (extendedLabel b.toTree (i :: w))
            (extendedLabel c.toTree (i :: w))
        (habs a) (habs b) (habs c) (by rw [hm]; decide)
      rw [h, hm]; simp
    | top =>
      rw [median_of_top hm]
      have h := medianSym_absorb (rootLabel a) (rootLabel b) (rootLabel c)
        (extendedLabel a.toTree (i :: w)) (extendedLabel b.toTree (i :: w))
            (extendedLabel c.toTree (i :: w))
        (habs a) (habs b) (habs c) (by rw [hm]; decide)
      rw [h, hm]; simp
    | f =>
      rw [median_of_f hm, extendedLabel_toTree_cons, child_node, ih, extendedLabel_toTree_cons a,
        extendedLabel_toTree_cons b, extendedLabel_toTree_cons c]

/-- The finite median represents the median of the corresponding trees. -/
@[simp] theorem median_toTree (a b c : FTree n) :
    (median a b c).toTree = treeMedian a.toTree b.toTree c.toTree := by
  apply extendedLabel_injective
  funext w
  rw [extendedLabel_median, extendedLabel_treeMedian]

end DeciSigma1.Semantics.FiniteMedian
