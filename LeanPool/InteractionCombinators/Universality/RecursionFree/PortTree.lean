/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.ExpandedRoot

/-!
# The tree rooted at a port (Fig. 6, page 86)

Lafont 1997, Section 2.4, Fig. 6, journal page 86 (PDF page 18). A side `φ` in expanded form
(`Rule.Expanded`) and linear is one tree per port (`Rule.Expanded.existsUnique_root`).

* `Rule.portTree φ p` — the tree rooted at the port `p` of `φ` (`Rule.portTree_eq`: it is the
  tree of the equation `p = t` of an expanded linear side).
* `Rule.Expanded.net_eq_portTree`, `Rule.Expanded.sum_vars_portTree` — such a side is the
  equations `p = portTree φ p`, whose leaves are its internal wires, each twice.

Its computable twin `Rule.portTreeC` is in `PortTreeC.lean`.

Contents, in the order of the file:

1. Definition: `Rule.portTree`, the tree rooted at a port of a side.
2. Auxiliary lemma: `Rule.portTree_eq`, in an expanded linear side `portTree φ p` is the tree of
   the equation rooted at `p`.
3. Main results: `Rule.Expanded.net_eq_portTree`, an expanded linear side is the equations
   `p = portTree φ p` with internal leaves; `Rule.Expanded.sum_vars_portTree`, each internal wire
   is a leaf exactly twice.
-/

@[expose] public section

namespace INet

-- the signature, and the numbers of auxiliary ports of the two cells of a rule
variable {S : Signature} {a k : ℕ}

open Term ExpandedIso

-- ============================================================================================
-- 1. Definition: the tree rooted at a port
-- ============================================================================================

open Classical in
/-- The tree rooted at the port `p` of a side `φ` of a decomposition (Fig. 6, page 86): the tree
`t` of an equation `p = t` of `φ.net`, if there is one, and the leaf `p` otherwise. For a linear
side in expanded form the equation exists and is unique (`Rule.portTree_eq`). -/
noncomputable def Rule.portTree
    -- the side
    (φ : Rule S a k)
    -- the port
    (p : Fin a ⊕ Fin k) :
    Term S (Fin a ⊕ Fin k ⊕ Fin φ.internal) :=
  if h : ∃ t, s(Term.var (port p), t) ∈ φ.net then h.choose else Term.var (port p)

-- ============================================================================================
-- 2. Auxiliary lemma: the tree of the equation rooted at a port
-- ============================================================================================

/-- In a linear side in expanded form, `portTree φ p` is the tree of the equation rooted at `p`
(Fig. 6, page 86). -/
theorem Rule.portTree_eq
    -- the side: in expanded form, and linear
    {φ : Rule S a k}
    (he : φ.Expanded)
    (hl : φ.Linear)
    -- an equation `p = t` of the side
    {p : Fin a ⊕ Fin k}
    {t : Term S (Fin a ⊕ Fin k ⊕ Fin φ.internal)}
    (ht : s(Term.var (port p), t) ∈ φ.net) :
    φ.portTree p = t := by
  have h : ∃ t, s(Term.var (port p), t) ∈ φ.net := ⟨t, ht⟩
  unfold portTree
  split_ifs
  exact (he.existsUnique_root hl p).unique h.choose_spec ht

-- ============================================================================================
-- 3. Main results: a side is its port trees
-- ============================================================================================

/-- A linear side in expanded form is the equations `p = portTree φ p`, one per port, and the
leaves of these trees are internal wires (Fig. 6, page 86). -/
theorem Rule.Expanded.net_eq_portTree
    -- the side: in expanded form, and linear
    {φ : Rule S a k}
    (he : φ.Expanded)
    (hl : φ.Linear) :
    -- the side is the equations `p = portTree φ p`, one per port
    φ.net = (Finset.univ.val.map fun p => s(Term.var (port p), φ.portTree p))
    -- and every leaf of these trees is an internal wire
    ∧ ∀ p, ∀ x ∈ (φ.portTree p).vars, ∃ w, x = .inr (.inr w) := by
  obtain ⟨T, hT, hN⟩ := he.exists_trees hl
  have hpt : ∀ p, φ.portTree p = T p := fun p =>
    Rule.portTree_eq he hl (by rw [hN]; exact Multiset.mem_map.2 ⟨p, Finset.mem_univ_val _, rfl⟩)
  simp only [hpt]
  exact ⟨hN, hT⟩

/-- The leaves of the trees of a linear side in expanded form are its internal wires, each twice
(Fig. 6, page 86). -/
theorem Rule.Expanded.sum_vars_portTree
    -- the side: in expanded form, and linear
    {φ : Rule S a k}
    (he : φ.Expanded)
    (hl : φ.Linear) :
    -- the leaves of all the port trees are the internal wires, each twice
    ∑ p, (φ.portTree p).vars
      = 2 • Finset.univ.val.map fun w : Fin φ.internal =>
          (.inr (.inr w) : Fin a ⊕ Fin k ⊕ Fin φ.internal) := by
  obtain ⟨hN, hT⟩ := he.net_eq_portTree hl
  have hinj : Function.Injective fun w : Fin φ.internal =>
      (.inr (.inr w) : Fin a ⊕ Fin k ⊕ Fin φ.internal) := fun _ _ h => by simpa using h
  ext x
  rw [Multiset.count_nsmul]
  rcases x with i | j | w
  · rw [Multiset.count_eq_zero.2, Multiset.count_eq_zero.2]
    · simp
    · rw [Multiset.mem_sum]
      rintro ⟨p, -, hp⟩
      obtain ⟨w, hw⟩ := hT p _ hp
      cases hw
  · rw [Multiset.count_eq_zero.2, Multiset.count_eq_zero.2]
    · simp
    · rw [Multiset.mem_sum]
      rintro ⟨p, -, hp⟩
      obtain ⟨w, hw⟩ := hT p _ hp
      cases hw
  · rw [count_internal (n := φ.internal) (N := φ.net) hl hN w,
      Multiset.count_map_eq_count' _ _ hinj, Multiset.count_eq_one_of_mem Finset.univ.nodup
        (Finset.mem_univ_val _)]

end INet
