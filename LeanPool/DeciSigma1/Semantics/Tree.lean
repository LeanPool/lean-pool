/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Order.Lattice

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Trees over `{⊥, f, ⊤}`

Types of non-structural subtyping are possibly infinite trees over the constants `⊥` and `⊤` and one
constructor `f` of arity `n`. A tree is represented by its labeling function: a partial map from
paths (words over `Fin n`) to labels that is defined at the root and defined at `π ++ [i]` exactly
when `π` is labeled `f`. This module defines these trees, their constructors and subtrees, the
covariant non-structural order `Tree.CovLe` (for every path in both domains the labels are ordered
by `⊥ < f < ⊤`), and finite trees as finite terms (`FTree`).

## Main declarations

- `Sym`: the labels `⊥`, `f`, `⊤`, linearly ordered by `⊥ < f < ⊤`.
- `IsLivePrefix`: a path all of whose proper prefixes are labeled `f`.
- `Tree`, `Tree.bot`, `Tree.top`, `Tree.node`, `Tree.subtree`: trees and their constructors.
- `Tree.CovLe`: the covariant non-structural order, a partial order on `Tree n`.
- `FTree`, `FTree.toTree`: finite trees.
-/

@[expose] public section


namespace DeciSigma1.Semantics

/-- The labels of tree nodes: the constants `⊥` and `⊤` and the constructor `f`. -/
inductive Sym where
  | bot | f | top
  deriving DecidableEq, Repr

namespace Sym

/-- The ranks `⊥ ↦ 0`, `f ↦ 1`, `⊤ ↦ 2`, which define the order `⊥ < f < ⊤`. -/
def rank : Sym → Nat
  | bot => 0
  | f => 1
  | top => 2

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]

instance : LinearOrder Sym := LinearOrder.lift' rank rank_injective

@[simp] theorem bot_le (a : Sym) : bot ≤ a := by cases a <;> decide
@[simp] theorem le_top (a : Sym) : a ≤ top := by cases a <;> decide

@[simp] theorem le_bot_iff (a : Sym) : a ≤ bot ↔ a = bot := by
  cases a <;> decide

@[simp] theorem top_le_iff (a : Sym) : top ≤ a ↔ a = top := by
  cases a <;> decide

end Sym

section LivePrefix

variable {n : ℕ}

/-- A path `π` is live for a labeling when every proper prefix of `π` is labeled `f`; these are
the paths that remain when the labeling is pruned to a tree. -/
def IsLivePrefix (labels : List (Fin n) → Sym) (π : List (Fin n)) : Prop :=
  ∀ τ, τ <+: π → τ ≠ π → labels τ = .f

@[simp] theorem isLivePrefix_nil (labels : List (Fin n) → Sym) : IsLivePrefix labels [] := by
  intro τ hp hn
  exact False.elim (hn (List.prefix_nil.mp hp))

theorem isLivePrefix_append_singleton (labels : List (Fin n) → Sym)
    (π : List (Fin n)) (i : Fin n) :
    IsLivePrefix labels (π ++ [i]) ↔ IsLivePrefix labels π ∧ labels π = .f := by
  constructor
  · intro h
    have hlen : π ≠ π ++ [i] := by intro he; have := congrArg List.length he; simp at this
    refine ⟨?_, h π (List.prefix_append _ _) hlen⟩
    intro τ hp hn
    apply h τ (hp.trans (List.prefix_append _ _))
    intro he
    have := hp.length_le
    simp [he] at this
  · rintro ⟨h, hf⟩ τ hp hn
    have hlen : τ.length ≤ π.length := by
      have hle := hp.length_le
      have hneq : τ.length ≠ (π ++ [i]).length := fun he => hn (hp.eq_of_length he)
      simp only [List.length_append, List.length_singleton] at hle hneq
      omega
    have hprefix : τ <+: π :=
      List.prefix_of_prefix_length_le hp (List.prefix_append _ _) hlen
    by_cases he : τ = π
    · simpa [he] using hf
    · exact h τ hprefix he

end LivePrefix

end DeciSigma1.Semantics

namespace DeciSigma1.Semantics

/-! ## Path domains -/

/-- A tree over `{⊥, f, ⊤}` with a constructor of arity `n`, given by the label `fn π` of each path
`π` in its domain. The root is in the domain, and `π ++ [i]` is in the domain exactly when `π` is
labeled `f`. -/
structure Tree (n : ℕ) where
  /-- Partial node labelling; absent nodes have value `none`. -/
  fn : List (Fin n) → Option Sym
  wf : fn [] ≠ none ∧ ∀ π i, (fn (π ++ [i])).isSome ↔ fn π = some Sym.f

namespace Tree

variable {n : ℕ}

@[ext] theorem ext {t u : Tree n} (h : t.fn = u.fn) : t = u := by
  cases t
  cases u
  cases h
  rfl

theorem root_isSome (t : Tree n) : (t.fn []).isSome :=
  Option.isSome_iff_ne_none.mpr t.wf.1

theorem child_isSome_iff (t : Tree n) (π : List (Fin n)) (i : Fin n) :
    (t.fn (π ++ [i])).isSome ↔ t.fn π = some Sym.f := t.wf.2 π i

/-- Removing any suffix preserves membership in the domain. -/
theorem domain_append_left (t : Tree n) (π ρ : List (Fin n))
    (h : (t.fn (π ++ ρ)).isSome) : (t.fn π).isSome := by
  induction ρ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton ρ i ih =>
    have hf : t.fn (π ++ ρ) = some Sym.f :=
      (t.child_isSome_iff (π ++ ρ) i).mp (by simpa [List.append_assoc] using h)
    exact ih (by simp [hf])

/-- Every proper prefix of a path in the domain is labeled `f`. -/
theorem label_eq_f_of_proper_prefix (t : Tree n) {π ρ : List (Fin n)}
    (hprefix : π.IsPrefix ρ) (hne : π ≠ ρ) (h : (t.fn ρ).isSome) :
    t.fn π = some Sym.f := by
  obtain ⟨σ, rfl⟩ := hprefix
  cases σ with
  | nil => simp at hne
  | cons i σ =>
    apply (t.child_isSome_iff π i).mp
    exact t.domain_append_left (π ++ [i]) σ (by simpa [List.append_assoc] using h)

/-! ## Constructors and subtrees -/

/-- The tree `⊥`. -/
def bot : Tree n where
  fn
    | [] => some Sym.bot
    | _ :: _ => none
  wf := by
    constructor
    · simp
    · intro π i; cases π <;> simp

/-- The tree `⊤`. -/
def top : Tree n where
  fn
    | [] => some Sym.top
    | _ :: _ => none
  wf := by
    constructor
    · simp
    · intro π i; cases π <;> simp

/-- The tree `f(a 0, …, a (n - 1))`. -/
def node (a : Fin n → Tree n) : Tree n where
  fn
    | [] => some Sym.f
    | i :: w => (a i).fn w
  wf := by
    constructor
    · simp
    · intro w i
      cases w with
      | nil => simpa using (a i).root_isSome
      | cons j w => exact (a j).child_isSome_iff w i

@[simp] theorem bot_fn_nil : (bot : Tree n).fn [] = some Sym.bot := rfl
@[simp] theorem bot_fn_cons (i : Fin n) (π : List (Fin n)) :
    (bot : Tree n).fn (i :: π) = none := rfl
@[simp] theorem top_fn_nil : (top : Tree n).fn [] = some Sym.top := rfl
@[simp] theorem top_fn_cons (i : Fin n) (π : List (Fin n)) :
    (top : Tree n).fn (i :: π) = none := rfl
@[simp] theorem node_fn_nil (a : Fin n → Tree n) : (node a).fn [] = some Sym.f := rfl
@[simp] theorem node_fn_cons (a : Fin n → Tree n) (i : Fin n) (w : List (Fin n)) :
    (node a).fn (i :: w) = (a i).fn w := rfl

/-- The subtree of `t` at the path `π`, if `π` is in the domain of `t`. -/
def subtree (t : Tree n) (π : List (Fin n)) : Option (Tree n) :=
  if h : (t.fn π).isSome then
    some {
      fn := fun ρ => t.fn (π ++ ρ)
      wf := by
        constructor
        · simpa using Option.isSome_iff_ne_none.mp h
        · intro ρ i
          simpa [List.append_assoc] using t.child_isSome_iff (π ++ ρ) i
    }
  else none

@[simp] theorem subtree_isSome_iff (t : Tree n) (π : List (Fin n)) :
    (t.subtree π).isSome ↔ (t.fn π).isSome := by
  unfold subtree
  split <;> simp_all

theorem subtree_fn {t u : Tree n} {π : List (Fin n)} (h : t.subtree π = some u)
    (ρ : List (Fin n)) : u.fn ρ = t.fn (π ++ ρ) := by
  unfold subtree at h
  split at h
  · cases Option.some.inj h
    rfl
  · contradiction

/-- A tree whose root is `⊥` or `⊤` has no nonempty paths in its domain. -/
theorem fn_cons_eq_none_of_root_ne_f (t : Tree n) (h : t.fn [] ≠ some Sym.f)
    (i : Fin n) (π : List (Fin n)) : t.fn (i :: π) = none := by
  by_contra hsome
  apply h
  apply (t.child_isSome_iff [] i).mp
  exact t.domain_append_left [i] π (Option.isSome_iff_ne_none.mpr hsome)

@[simp] theorem root_eq_bot_iff (t : Tree n) : t.fn [] = some Sym.bot ↔ t = bot := by
  constructor
  · intro h
    apply ext
    funext π
    cases π with
    | nil => exact h
    | cons i π =>
      exact t.fn_cons_eq_none_of_root_ne_f (by simp [h]) i π
  · rintro rfl
    rfl

@[simp] theorem root_eq_top_iff (t : Tree n) : t.fn [] = some Sym.top ↔ t = top := by
  constructor
  · intro h
    apply ext
    funext π
    cases π with
    | nil => exact h
    | cons i π =>
      exact t.fn_cons_eq_none_of_root_ne_f (by simp [h]) i π
  · rintro rfl
    rfl

/-- A child of a tree whose root is the constructor. -/
def branch (t : Tree n) (i : Fin n) (h : t.fn [] = some Sym.f) : Tree n where
  fn := fun π => t.fn (i :: π)
  wf := by
    constructor
    · exact Option.isSome_iff_ne_none.mp ((t.child_isSome_iff [] i).mpr h)
    · intro π j
      exact t.child_isSome_iff (i :: π) j

theorem eq_node_of_root_eq_f (t : Tree n) (h : t.fn [] = some Sym.f) :
    t = node (fun i => t.branch i h) := by
  apply ext
  funext π
  cases π with
  | nil => exact h
  | cons i π => rfl

theorem eq_bot_or_eq_top_or_node (t : Tree n) :
    t = bot ∨ t = top ∨ ∃ a, t = node a := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp t.root_isSome
  cases s with
  | bot => exact Or.inl ((root_eq_bot_iff t).mp hs)
  | top => exact Or.inr (Or.inl ((root_eq_top_iff t).mp hs))
  | f => exact Or.inr (Or.inr ⟨_, t.eq_node_of_root_eq_f hs⟩)

@[simp] theorem node_eq_node_iff (a b : Fin n → Tree n) :
    node a = node b ↔ a = b := by
  constructor
  · intro h
    funext i
    apply ext
    funext w
    exact congrArg (fun t : Tree n => t.fn (i :: w)) h
  · rintro rfl; rfl

@[simp] theorem bot_ne_top : (bot : Tree n) ≠ top := by
  intro h
  have := congrArg (fun t : Tree n => t.fn []) h
  simp at this

@[simp] theorem node_ne_bot (a : Fin n → Tree n) : node a ≠ bot := by
  intro h
  have := congrArg (fun t : Tree n => t.fn []) h
  simp at this

@[simp] theorem node_ne_top (a : Fin n → Tree n) : node a ≠ top := by
  intro h
  have := congrArg (fun t : Tree n => t.fn []) h
  simp at this

@[simp] theorem top_ne_bot : (top : Tree n) ≠ bot := bot_ne_top.symm
@[simp] theorem bot_ne_node (a : Fin n → Tree n) : bot ≠ node a := (node_ne_bot a).symm
@[simp] theorem top_ne_node (a : Fin n → Tree n) : top ≠ node a := (node_ne_top a).symm

/-! ## The non-structural partial order -/

/-- The covariant non-structural order: at every path in the domains of both trees, the label of `t`
is at most the label of `u`. -/
def CovLe (t u : Tree n) : Prop :=
  ∀ π a b, t.fn π = some a → u.fn π = some b → a ≤ b

instance : LE (Tree n) := ⟨Tree.CovLe⟩

theorem le_refl (t : Tree n) : t ≤ t := by
  intro π a b ha hb
  have : a = b := Option.some.inj (ha.symm.trans hb)
  exact this.le

/-- A path shared by the endpoints of two comparisons also occurs in the middle. -/
theorem middle_isSome {t u v : Tree n} (htu : t ≤ u) (huv : u ≤ v)
    (π : List (Fin n)) (ht : (t.fn π).isSome) (hv : (v.fn π).isSome) :
    (u.fn π).isSome := by
  induction π using List.reverseRecOn with
  | nil => exact u.root_isSome
  | append_singleton π i ih =>
    have ht' := (t.child_isSome_iff π i).mp ht
    have hv' := (v.child_isSome_iff π i).mp hv
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (ih (by simp [ht']) (by simp [hv']))
    have hb' : b = Sym.f := _root_.le_antisymm (huv π b Sym.f hb hv')
      (htu π Sym.f b ht' hb)
    exact (u.child_isSome_iff π i).mpr (by simpa [hb'] using hb)

theorem le_trans {t u v : Tree n} (htu : t ≤ u) (huv : u ≤ v) : t ≤ v := by
  intro π a c ha hc
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
    (middle_isSome htu huv π (by simp [ha]) (by simp [hc]))
  exact _root_.le_trans (htu π a b ha hb) (huv π b c hb hc)

theorem le_antisymm {t u : Tree n} (htu : t ≤ u) (hut : u ≤ t) : t = u := by
  have labels : ∀ π a b, t.fn π = some a → u.fn π = some b → a = b := by
    intro π a b ha hb
    exact _root_.le_antisymm (htu π a b ha hb) (hut π b a hb ha)
  apply ext
  funext π
  induction π using List.reverseRecOn with
  | nil =>
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp t.root_isSome
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp u.root_isSome
    rw [ha, hb, labels [] a b ha hb]
  | append_singleton π i ih =>
    have hd : (t.fn (π ++ [i])).isSome ↔ (u.fn (π ++ [i])).isSome := by
      rw [child_isSome_iff, child_isSome_iff, ih]
    cases ht : t.fn (π ++ [i]) <;> cases hu : u.fn (π ++ [i])
    · rfl
    · simp [ht, hu] at hd
    · simp [ht, hu] at hd
    · exact congrArg some (labels _ _ _ ht hu)

instance : PartialOrder (Tree n) where
  le := Tree.CovLe
  le_refl := Tree.le_refl
  le_trans := fun _ _ _ => Tree.le_trans
  le_antisymm := fun _ _ => Tree.le_antisymm

@[simp] theorem bot_le (t : Tree n) : bot ≤ t := by
  intro π a b ha hb
  cases π with
  | nil => simp only [bot_fn_nil, Option.some.injEq] at ha; subst a; exact Sym.bot_le b
  | cons i π => simp at ha

@[simp] theorem le_top (t : Tree n) : t ≤ top := by
  intro π a b ha hb
  cases π with
  | nil => simp only [top_fn_nil, Option.some.injEq] at hb; subst b; exact Sym.le_top a
  | cons i π => simp at hb

@[simp] theorem le_bot_iff (t : Tree n) : t ≤ bot ↔ t = bot :=
  ⟨fun h => le_antisymm h (bot_le t), fun h => h ▸ le_refl bot⟩

@[simp] theorem top_le_iff (t : Tree n) : top ≤ t ↔ t = top :=
  ⟨fun h => le_antisymm (le_top t) h, fun h => h ▸ le_refl top⟩

@[simp] theorem node_le_node_iff (a b : Fin n → Tree n) :
    node a ≤ node b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro h i w x y hx hy
    exact h (i :: w) x y hx hy
  · intro h w x y hx hy
    cases w with
    | nil => exact (Option.some.inj (hx.symm.trans hy)).le
    | cons i w => exact h i w x y hx hy

theorem le_iff_root_cases (t u : Tree n) :
    t ≤ u ↔ t = bot ∨ u = top ∨
      ∃ a b, t = node a ∧ u = node b ∧ ∀ i, a i ≤ b i := by
  constructor
  · intro h
    rcases t.eq_bot_or_eq_top_or_node with ht | ht | ⟨a, rfl⟩
    · exact Or.inl ht
    · subst t; exact Or.inr (Or.inl ((top_le_iff u).mp h))
    · rcases u.eq_bot_or_eq_top_or_node with hu | hu | ⟨b, rfl⟩
      · subst u; exact False.elim (node_ne_bot a ((le_bot_iff _).mp h))
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr ⟨a, b, rfl, rfl, (node_le_node_iff ..).mp h⟩)
  · rintro (rfl | rfl | ⟨a, b, rfl, rfl, h⟩)
    · exact bot_le u
    · exact le_top t
    · exact (node_le_node_iff ..).mpr h

end Tree

end DeciSigma1.Semantics

namespace DeciSigma1.Semantics

/-- Finite trees over `{⊥, f, ⊤}`, as terms. -/
inductive FTree (n : ℕ) where
  | bot
  | top
  | node (children : Fin n → FTree n)

namespace FTree
variable {n : ℕ}

/-- The tree denoted by a finite term. -/
def toTree : FTree n → Tree n
  | bot => Tree.bot
  | top => Tree.top
  | node a => Tree.node (fun i => toTree (a i))

@[simp] theorem toTree_bot : toTree (bot : FTree n) = Tree.bot := rfl
@[simp] theorem toTree_top : toTree (top : FTree n) = Tree.top := rfl
@[simp] theorem toTree_node (a : Fin n → FTree n) :
    toTree (node a) = Tree.node (fun i => toTree (a i)) := rfl

end FTree
end DeciSigma1.Semantics
