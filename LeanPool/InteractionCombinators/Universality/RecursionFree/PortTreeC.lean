/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.PortTree

/-!
# A computable tree at a port (Fig. 6, page 86)

Lafont 1997, Section 2.4, Fig. 6, journal page 86 (PDF page 18): a side `φ` of a decomposition in
expanded form is one tree at each port. `Rule.portTree` (`PortTree.lean`) picks that tree with a
classical choice, which makes every construction built on it noncomputable. This file gives a
computable twin.

* `PortTreeC.otherOf x e` — the other side of the equation `e` if one side is the leaf `x`.
* `PortTreeC.onlyOr d M` — the element of a multiset with one element, and `d` otherwise.
* `Rule.portTreeC φ p` — the only tree `t` with `p = t` in `φ.net`, and the leaf `p` otherwise.
  It needs only the decidable equality of the names, not of the symbols.
* `Rule.portTreeC_eq`, `Rule.portTreeC_eq_portTree` — on a linear side in expanded form it is
  `Rule.portTree`; `Rule.portTreeC_of_not_exists` — with no equation at `p` it is the leaf `p`,
  as `Rule.portTree` is.

Without linearity the two may differ: if the same equation `p = t` occurs twice in `φ.net`, the
twin gives the leaf `p` and `Rule.portTree` gives `t`.

Contents, in the order of the file:

1. The other side of an equation: the definitions `isLeaf`, `otherPair`, `otherOf`, and the
   lemmas `isLeaf_iff`, `otherPair_comm`, `eq_of_otherOf`, `otherOf_mk`,
   `card_filterMap_otherOf_le`.
2. The element of a multiset with one element: the definitions `onlyOrList`, `onlyOr`, and the
   lemmas `onlyOrList_perm`, `onlyOr_singleton`, `onlyOr_zero`, `onlyOr_eq_or_mem`.
3. Definition: `Rule.portTreeC`, the computable tree at a port.
4. Auxiliary lemmas: `Rule.portTreeC_eq_of_linear`, `Rule.portTreeC_eq`,
   `Rule.portTreeC_of_not_exists`, `Rule.portTreeC_eq_or_mem`, `Rule.portTree_of_not_exists`.
5. Main result: `Rule.portTreeC_eq_portTree`, the twin is `Rule.portTree` on a linear side in
   expanded form.
-/

@[expose] public section

namespace INet

-- the signature, and the numbers of principal and auxiliary ports of a side
variable {S : Signature} {a k : ℕ}

open Term ExpandedIso

namespace PortTreeC

-- the names, with a decidable equality
variable {ν : Type} [DecidableEq ν]

-- ============================================================================================
-- 1. The other side of an equation
-- ============================================================================================

/-- Whether a tree is the leaf `x`, tested by a match on the tree, so that only the decidable
equality of the names is used (Fig. 6, page 86). -/
def isLeaf
    -- the name of the leaf
    (x : ν) :
    Term S ν → Bool
  | .var y => decide (y = x)
  | .app _ _ => false

-- `isLeaf x t` holds exactly when `t` is the leaf `x`
theorem isLeaf_iff
    {x : ν}
    {t : Term S ν} :
    isLeaf x t = true ↔ t = .var x := by
  cases t <;> simp [isLeaf]

/-- The other side of an equation one side of which is the leaf `x`, as a function on ordered
pairs (Fig. 6, page 86). -/
def otherPair
    -- the name of the leaf
    (x : ν)
    -- the two sides of the equation, in order
    (t u : Term S ν) :
    Option (Term S ν) :=
  if isLeaf x t then some u else if isLeaf x u then some t else none

-- `otherPair x` does not depend on the order of the two sides
theorem otherPair_comm
    (x : ν)
    (t u : Term S ν) :
    otherPair x t u = otherPair x u t := by
  unfold otherPair
  cases ht : isLeaf x t <;> cases hu : isLeaf x u <;> simp only [Bool.false_eq_true,
    ↓reduceIte]
  rw [isLeaf_iff.1 ht, isLeaf_iff.1 hu]

/-- The other side of the equation `e`, if one side of `e` is the leaf `x` (Fig. 6, page 86). -/
def otherOf
    -- the name of the leaf
    (x : ν) :
    Sym2 (Term S ν) → Option (Term S ν) :=
  Sym2.lift ⟨otherPair x, otherPair_comm x⟩

/-- `otherOf x e` gives `u` only if `e` is the equation `x = u` (Fig. 6, page 86). -/
theorem eq_of_otherOf
    -- the leaf, the equation and the tree
    {x : ν}
    {e : Sym2 (Term S ν)}
    {u : Term S ν}
    -- `otherOf x` gives `u` on `e`
    (h : otherOf x e = some u) :
    e = s(Term.var x, u) := by
  induction e using Sym2.ind with
  | _ t t' =>
    simp only [otherOf, Sym2.lift_mk, otherPair] at h
    split_ifs at h with h₁ h₂
    · cases h; rw [isLeaf_iff.1 h₁]
    · cases h; rw [isLeaf_iff.1 h₂, Sym2.eq_swap]

/-- `otherOf x` gives `u` on the equation `x = u` (Fig. 6, page 86). -/
theorem otherOf_mk
    (x : ν)
    (u : Term S ν) :
    otherOf x s(Term.var x, u) = some u := by
  simp [otherOf, otherPair, isLeaf]

/-- The trees given by `otherOf x` on a net are at most as many as the occurrences of `x`
(Fig. 6, page 86). -/
theorem card_filterMap_otherOf_le
    -- the name and the net
    (x : ν)
    (N : Net S ν) :
    Multiset.card (N.filterMap (otherOf x)) ≤ N.vars.count x := by
  induction N using Multiset.induction_on with
  | empty => simp
  | cons e N ih =>
    rw [Net.vars_cons, Multiset.count_add]
    cases h : otherOf x e with
    | none => rw [Multiset.filterMap_cons_none _ _ h]; omega
    | some u =>
      rw [Multiset.filterMap_cons_some _ _ _ h, Multiset.card_cons]
      have hx : x ∈ eqVars e := by rw [eq_of_otherOf h]; simp
      have := Multiset.one_le_count_iff_mem.2 hx
      omega

-- ============================================================================================
-- 2. The element of a multiset with one element
-- ============================================================================================

-- the type of the elements
variable {α : Type}

/-- The element of a list of length one, and `d` otherwise. -/
def onlyOrList
    -- the default value
    (d : α) :
    List α → α
  | [x] => x
  | _ => d

-- `onlyOrList d` gives the same value on two permutations of a list
theorem onlyOrList_perm
    -- the default value
    (d : α)
    -- two lists, one a permutation of the other
    {l₁ l₂ : List α}
    (h : l₁.Perm l₂) :
    onlyOrList d l₁ = onlyOrList d l₂ := by
  rcases l₁ with _ | ⟨x, _ | ⟨y, r⟩⟩
  · rw [List.nil_perm.1 h]
  · rw [List.singleton_perm.1 h]
  · rcases l₂ with _ | ⟨x', _ | ⟨y', r'⟩⟩
    · exact absurd h.length_eq (by simp)
    · exact absurd h.length_eq (by simp)
    · rfl

/-- The element of a multiset with one element, and `d` otherwise (Fig. 6, page 86). -/
def onlyOr
    -- the default value
    (d : α)
    -- the multiset
    (M : Multiset α) :
    α :=
  Quotient.liftOn M (onlyOrList d) fun _ _ h => onlyOrList_perm d h

-- on a multiset with one element `x`, `onlyOr` gives `x`
@[simp] theorem onlyOr_singleton
    (d x : α) :
    onlyOr d {x} = x := rfl

-- on the empty multiset, `onlyOr` gives the default value
@[simp] theorem onlyOr_zero
    (d : α) :
    onlyOr d 0 = d := rfl

/-- `onlyOr d M` is `d` or an element of `M`. -/
theorem onlyOr_eq_or_mem
    -- the default value and the multiset
    (d : α)
    (M : Multiset α) :
    -- the value is the default, or an element of `M`
    onlyOr d M = d ∨
      onlyOr d M ∈ M := by
  induction M using Quotient.inductionOn with
  | h l =>
    rcases l with _ | ⟨x, _ | ⟨y, r⟩⟩
    · exact Or.inl rfl
    · exact Or.inr (Multiset.mem_singleton_self x)
    · exact Or.inl rfl

end PortTreeC

open PortTreeC

-- ============================================================================================
-- 3. Definition: the computable tree at a port
-- ============================================================================================

/-- The tree rooted at the port `p` of a side `φ` (Fig. 6, page 86), computably: the tree `t` of
the equation `p = t` of `φ.net` if there is exactly one such equation, and the leaf `p` otherwise.
On a linear side in expanded form it is `Rule.portTree` (`Rule.portTreeC_eq_portTree`). -/
def Rule.portTreeC
    -- the side
    (φ : Rule S a k)
    -- the port, principal or auxiliary
    (p : Fin a ⊕ Fin k) :
    Term S (Fin a ⊕ Fin k ⊕ Fin φ.internal) :=
  onlyOr (Term.var (port p)) (φ.net.filterMap (otherOf (port p)))

-- ============================================================================================
-- 4. Auxiliary lemmas: what the tree at a port is
-- ============================================================================================

/-- In a linear side, `portTreeC φ p` is the tree of an equation rooted at `p`: linearity alone
makes that equation unique (Fig. 6, page 86). -/
theorem Rule.portTreeC_eq_of_linear
    -- the side, linear
    {φ : Rule S a k}
    (hl : φ.Linear)
    -- an equation `p = t` of the side
    {p : Fin a ⊕ Fin k}
    {t : Term S (Fin a ⊕ Fin k ⊕ Fin φ.internal)}
    (ht : s(Term.var (port p), t) ∈ φ.net) :
    φ.portTreeC p = t := by
  have hc : φ.net.vars.count (port p) = 1 := by
    rcases p with i | j
    · exact hl.left i
    · exact hl.right j
  have hmem : t ∈ φ.net.filterMap (otherOf (port p)) :=
    (Multiset.mem_filterMap _ _).2 ⟨_, ht, otherOf_mk _ _⟩
  have hle := card_filterMap_otherOf_le (port p) φ.net
  have hpos := Multiset.card_pos_iff_exists_mem.2 ⟨t, hmem⟩
  obtain ⟨u, hu⟩ :=
    Multiset.card_eq_one.1 (show Multiset.card (φ.net.filterMap (otherOf (port p))) = 1 by omega)
  rw [hu, Multiset.mem_singleton] at hmem
  unfold portTreeC
  rw [hu, hmem, onlyOr_singleton]

/-- In a linear side in expanded form, `portTreeC φ p` is the tree of the equation rooted at `p`,
as `Rule.portTree_eq` says of `portTree` (Fig. 6, page 86). -/
theorem Rule.portTreeC_eq
    -- the side, in expanded form and linear
    {φ : Rule S a k}
    (_he : φ.Expanded)
    (hl : φ.Linear)
    -- an equation `p = t` of the side
    {p : Fin a ⊕ Fin k}
    {t : Term S (Fin a ⊕ Fin k ⊕ Fin φ.internal)}
    (ht : s(Term.var (port p), t) ∈ φ.net) :
    φ.portTreeC p = t :=
  Rule.portTreeC_eq_of_linear hl ht

/-- With no equation rooted at `p`, `portTreeC φ p` is the leaf `p`, with no hypothesis on `φ`
(Fig. 6, page 86). -/
theorem Rule.portTreeC_of_not_exists
    -- the side and the port
    {φ : Rule S a k}
    {p : Fin a ⊕ Fin k}
    -- no equation of the side is rooted at `p`
    (h : ¬ ∃ t, s(Term.var (port p), t) ∈ φ.net) :
    φ.portTreeC p = Term.var (port p) := by
  have h0 : φ.net.filterMap (otherOf (port p)) = 0 :=
    Multiset.eq_zero_of_forall_notMem fun u hu => by
      obtain ⟨e, he, heu⟩ := (Multiset.mem_filterMap _ _).1 hu
      exact h ⟨u, eq_of_otherOf heu ▸ he⟩
  unfold portTreeC
  rw [h0, onlyOr_zero]

/-- `portTreeC φ p` is the leaf `p` or the tree of an equation `p = t` of `φ`, with no hypothesis
on `φ` (Fig. 6, page 86). -/
theorem Rule.portTreeC_eq_or_mem
    -- the side and the port
    (φ : Rule S a k)
    (p : Fin a ⊕ Fin k) :
    -- the tree at `p` is the leaf `p`,
    φ.portTreeC p = Term.var (port p) ∨
      -- or the other side of an equation of `φ` rooted at `p`
      s(Term.var (port p), φ.portTreeC p) ∈ φ.net := by
  rcases onlyOr_eq_or_mem (Term.var (port p)) (φ.net.filterMap (otherOf (port p))) with h | h
  · exact Or.inl h
  · obtain ⟨e, he, heu⟩ := (Multiset.mem_filterMap _ _).1 h
    rw [eq_of_otherOf heu] at he
    exact Or.inr he

/-- With no equation rooted at `p`, `portTree φ p` is the leaf `p` (Fig. 6, page 86). -/
theorem Rule.portTree_of_not_exists
    -- the side and the port
    {φ : Rule S a k}
    {p : Fin a ⊕ Fin k}
    -- no equation of the side is rooted at `p`
    (h : ¬ ∃ t, s(Term.var (port p), t) ∈ φ.net) :
    φ.portTree p = Term.var (port p) := by
  unfold portTree
  simp only [h, dite_false]

-- ============================================================================================
-- 5. Main result: the computable twin is `Rule.portTree`
-- ============================================================================================

/-- On a linear side in expanded form the computable twin is `Rule.portTree` (Fig. 6, page 86). -/
theorem Rule.portTreeC_eq_portTree
    -- the side, in expanded form and linear
    {φ : Rule S a k}
    (he : φ.Expanded)
    (hl : φ.Linear) :
    φ.portTreeC = φ.portTree := by
  funext p
  by_cases h : ∃ t, s(Term.var (port p), t) ∈ φ.net
  · obtain ⟨t, ht⟩ := h
    rw [Rule.portTreeC_eq he hl ht, Rule.portTree_eq he hl ht]
  · rw [Rule.portTreeC_of_not_exists h, Rule.portTree_of_not_exists h]

end INet
