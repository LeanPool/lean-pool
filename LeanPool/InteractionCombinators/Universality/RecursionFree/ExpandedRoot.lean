/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.ExpandedIso

/-!
# In a linear expanded rule, each port roots exactly one equation

Fig. 6 (Lafont 1997, page 86) reads the side `φ_{i,j}` of a rule as one tree per auxiliary port.
For a rule in expanded form (`Rule.Expanded`, `RecursionFree/ExpandedIso.lean`) this reading is
exact:

* `Rule.Expanded.existsUnique_root`: for each auxiliary port `p` there is exactly one tree `t` with
  `p = t` in the net;
* `Rule.Expanded.exists_trees`: the net is the multiset of the equations `p = T p`, one per port,
  every leaf of `T p` an internal wire;
* `Rule.Expanded.card_eq`: a linear expanded rule has exactly `a + b` equations.

Contents, in the order of the file:

1. Auxiliary lemma: `Rule.Expanded.exists_trees`, the net of a linear expanded rule is one tree
   per auxiliary port.
2. Main results: `Rule.Expanded.existsUnique_root` (each port roots exactly one equation) and
   `Rule.Expanded.card_eq` (there are `a + b` equations).
-/

@[expose] public section

namespace INet

variable {S : Signature} {a b : ℕ}

open Term ExpandedIso

-- ============================================================================================
-- 1. Auxiliary lemma: the trees of an expanded rule
-- ============================================================================================

/-- **Trees of an expanded rule** (page 86). The net of a linear rule in expanded form is one
equation `p = T p` for each auxiliary port `p`, where every leaf of `T p` is an internal wire. -/
theorem Rule.Expanded.exists_trees
    -- the rule: in expanded form and linear
    {r : Rule S a b}
    (he : r.Expanded)
    (hl : r.Linear) :
    -- one tree `T p` for each auxiliary port `p`
    ∃ T : Fin a ⊕ Fin b → Term S (Fin a ⊕ Fin b ⊕ Fin r.internal),
      -- every leaf of every tree is an internal wire
      (∀ p, ∀ x ∈ (T p).vars, ∃ w, x = .inr (.inr w))
      -- and the net is the equations `p = T p`, one per port
      ∧ r.net = Finset.univ.val.map fun p => s(var (port p), T p) :=
  exists_shape (n := r.internal) (N := r.net) hl he

-- ============================================================================================
-- 2. Main results: one equation per port
-- ============================================================================================

/-- **One equation per port** (page 86). In a linear rule in expanded form, each auxiliary port `p`
is the root of exactly one equation `p = t` of the net. -/
theorem Rule.Expanded.existsUnique_root
    -- the rule: in expanded form and linear
    {r : Rule S a b}
    (he : r.Expanded)
    (hl : r.Linear)
    -- an auxiliary port
    (p : Fin a ⊕ Fin b) :
    -- exactly one tree `t` with `p = t` in the net
    ∃! t : Term S (Fin a ⊕ Fin b ⊕ Fin r.internal), s(var (port p), t) ∈ r.net := by
  classical
  obtain ⟨T, -, hT⟩ := he.exists_trees hl
  refine ⟨T p, ?_, fun t ht => ?_⟩
  · rw [hT]; exact Multiset.mem_map.2 ⟨p, Finset.mem_univ_val _, rfl⟩
  · have hmem : s(var (port p), T p) ∈ r.net := by
      rw [hT]; exact Multiset.mem_map.2 ⟨p, Finset.mem_univ_val _, rfl⟩
    have hee := eq_of_mem_of_count_one ht hmem (x := port p) (by simp) (by simp)
      (count_port (n := r.internal) (N := r.net) hl p)
    exact Sym2.congr_right.1 hee

/-- A linear rule in expanded form has exactly `a + b` equations, one per auxiliary port
(page 86). -/
theorem Rule.Expanded.card_eq
    -- the rule: in expanded form and linear
    {r : Rule S a b}
    (he : r.Expanded)
    (hl : r.Linear) :
    -- the net has `a + b` equations
    Multiset.card r.net = a + b := by
  obtain ⟨T, -, hT⟩ := he.exists_trees hl
  rw [hT, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]

end INet
