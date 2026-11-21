/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.Decomposition
public import LeanPool.InteractionCombinators.Universality.RecursionFree.ExpandedIso

/-!
# A rule `α`–`α` read from the other cell (page 86)

Lafont 1997, page 86 (PDF page 18): "To sum up, one can assume that in all cases
`φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`, and `σ_{i,j}` is involutive"; Fig. 7. Issue #66, part 4.

The symmetric decomposition of a rule of a symbol with itself is
`Rule.exists_symm_decomposition_of_symmPerm` in `RecursionFree/SymmPerm.lean`: a linear reduced
rule `r : Rule S a a` whose net, read from the other cell, is the same graph up to a permutation
of the internal wires (`Rule.SymmPerm`, the condition of `System.WellFormed.symm`) has a
decomposition `(φ, φ, σ)` with `σ` involutive whose plug is `r`. Its proof assembles three parts:

1. `Rule.exists_expanded` (`RecursionFree/Expand.lean`): `r` is `Equiv` to an expanded rule `r'`;
2. the symmetry passes to `r'`, and `r'.swap` is linear and expanded, so
   `Rule.exists_perm_of_equiv` (`RecursionFree/ExpandedIso.lean`) makes it literal:
   `r'.swap.net = r'.net` renamed by a permutation of the internal wires;
3. `Rule.SymmLit.exists_symm_decomposition` (`RecursionFree/DecompositionSymmLiteral.lean`)
   applies to `r'`.

This file gives the lemmas about `r.swap`, the rule read from the other cell, that the second
part needs.

Contents, in the order of the file:

1. Auxiliary lemmas: `DecompositionSymm.swap_net`, `DecompositionSymm.swapName_map`,
   `DecompositionSymm.swap_linear`, `DecompositionSymm.swap_expanded`. Reading a rule from the
   other cell is a renaming of its names, which commutes with renaming the internal wires and
   keeps a rule linear and expanded.
-/

@[expose] public section

namespace INet

variable {S : Signature} {a : ℕ}

open Term

namespace DecompositionSymm

-- ============================================================================================
-- 1. Auxiliary lemmas: a rule read from the other cell
-- ============================================================================================

/-- The net of `r.swap` is the net of `r` renamed by `Rule.swapName`. -/
theorem swap_net
    -- a rule between a symbol of arity `a` and one of arity `b`
    {b : ℕ}
    (r : Rule S a b) :
    r.swap.net = r.net.bind fun x => var (Rule.swapName x) := rfl

/-- Renaming the internal wires commutes with exchanging the two groups of ports. -/
theorem swapName_map
    -- the renaming of the internal wires
    {b n m : ℕ}
    (f : Fin n → Fin m)
    -- a name of a rule: a port of the first cell, a port of the second, or an internal wire
    (x : Fin a ⊕ Fin b ⊕ Fin n) :
    Rule.swapName (Sum.map id (Sum.map id f) x)
      = Sum.map id (Sum.map id f) (Rule.swapName x) := by
  rcases x with i | j | w <;> rfl

/-- A rule read from the other cell is linear when the rule is. -/
theorem swap_linear
    -- a linear rule
    {b : ℕ}
    (r : Rule S a b)
    (hl : r.Linear) :
    r.swap.Linear := by
  classical
  have hv : Net.vars (show Net S (Fin b ⊕ Fin a ⊕ Fin r.internal) from r.swap.net) =
      r.net.vars.map Rule.swapName :=
    Net.vars_bind_var _ _
  refine ⟨fun j => ?_, fun i => ?_, fun w => ?_⟩
  · change (Net.vars (show Net S (Fin b ⊕ Fin a ⊕ Fin r.internal) from r.swap.net)).count
      (.inl j) = 1
    rw [hv, show (.inl j : Fin b ⊕ Fin a ⊕ Fin r.internal) = Rule.swapName (.inr (.inl j)) from rfl,
      Multiset.count_map_eq_count' _ _ Rule.swapName_injective]
    exact hl.right j
  · change (Net.vars (show Net S (Fin b ⊕ Fin a ⊕ Fin r.internal) from r.swap.net)).count
      (.inr (.inl i)) = 1
    rw [hv, show (.inr (.inl i) : Fin b ⊕ Fin a ⊕ Fin r.internal) = Rule.swapName (.inl i) from rfl,
      Multiset.count_map_eq_count' _ _ Rule.swapName_injective]
    exact hl.left i
  · let w' : Fin r.internal := w
    change (Net.vars (show Net S (Fin b ⊕ Fin a ⊕ Fin r.internal) from r.swap.net)).count
      (.inr (.inr w')) = 2
    rw [hv, show (.inr (.inr w') : Fin b ⊕ Fin a ⊕ Fin r.internal) =
        Rule.swapName (.inr (.inr w')) from rfl,
      Multiset.count_map_eq_count' _ _ Rule.swapName_injective]
    exact hl.internal w'

/-- A rule read from the other cell is in expanded form when the rule is. -/
theorem swap_expanded
    -- a rule in expanded form
    {b : ℕ}
    (r : Rule S a b)
    (he : r.Expanded) :
    r.swap.Expanded := by
  change ∀ e ∈ (show Net S (Fin b ⊕ Fin a ⊕ Fin r.internal) from r.swap.net), ∃ p t,
    e = s(Term.var p, t) ∧ (∀ w : Fin r.internal, p ≠ .inr (.inr w)) ∧
      ∀ x ∈ Term.vars (S := S) t, ∃ w : Fin r.internal, x = .inr (.inr w)
  intro e hmem
  obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.1 hmem
  obtain ⟨p, t, rfl, hp, ht⟩ := he e₀ he₀
  refine ⟨Rule.swapName p, t.bind fun x => var (Rule.swapName x), rfl, ?_, ?_⟩
  · intro w h
    rcases p with i | j | w'
    · cases h
    · cases h
    · exact hp w' rfl
  · intro x hx
    rw [Term.vars_bind] at hx
    obtain ⟨y, hy, hxy⟩ := Multiset.mem_bind.1 hx
    obtain ⟨w, rfl⟩ := ht y hy
    simp only [vars_var, Multiset.mem_singleton] at hxy
    exact ⟨w, hxy⟩

end DecompositionSymm

end INet
