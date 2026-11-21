/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Core.Net

/-!
# Small facts about the names of a net

Shared by many files, which used to carry their own copies.

* `Net.vars_bind_var` — the names of a renamed net are the renamed names.
* `Net.linear_of_forall_mem` — linearity checked on the names that occur only. This is the form in
  which `decide` proves linearity of a concrete net over `ℕ`: `Net.Linear` quantifies over every
  natural number, and `unfold Net.Linear; decide` cannot check that, while the bounded quantifier
  `∀ y ∈ N.vars` is decidable.
* `Equiv.eq_of_not_linear_any` — a net that is not linear is equivalent only to itself.

Contents, in the order of the file:

1. Auxiliary lemmas on names: `Net.vars_bind_var`, `Net.linear_of_forall_mem`.
2. Equivalence of a net that is not linear: `Equiv.eq_of_not_linear_any`.
-/

@[expose] public section

namespace INet

variable {S : Signature}

-- ============================================================================================
-- 1. Auxiliary lemmas on names
-- ============================================================================================

/-- The names of a net renamed by `f` (every name `x` replaced by `f x`) are the names of the net,
renamed by `f`. Names are an artefact of the text (Lafont 1997, Section 1.1, pages 71 and 72). -/
theorem Net.vars_bind_var
    -- the renaming, and the net it is applied to
    {ν μ : Type}
    (f : ν → μ)
    (N : Net S ν) :
    (N.bind fun x => (Term.var (f x) : Term S μ)).vars = N.vars.map f := by
  rw [Net.vars_bind]
  simp [Multiset.bind_singleton]

/-- A net is linear (every name occurs at most twice, Lafont 1997, Section 1.1, page 71) as soon
as every name that occurs in it occurs at most twice: a name that does not occur has count `0`.
The hypothesis quantifies over a finite multiset, so `decide` checks it on a concrete net. -/
theorem Net.linear_of_forall_mem
    -- the net
    {ν : Type} [DecidableEq ν]
    {N : Net S ν}
    -- every name that occurs in it occurs at most twice
    (h : ∀ y ∈ N.vars, N.vars.count y ≤ 2) :
    N.Linear := fun y => by
  by_cases hy : y ∈ N.vars
  · exact h y hy
  · rw [Multiset.count_eq_zero.2 hy]; omega

-- ============================================================================================
-- 2. Equivalence of a net that is not linear
-- ============================================================================================

/-- A net that is not linear is equivalent only to itself: no wire substitution applies to it
(wire substitution joins the two occurrences of a name, a wire of Lafont 1997, Section 1.1,
page 71). -/
theorem Equiv.eq_of_not_linear_any
    -- two equivalent nets
    {ν : Type} [DecidableEq ν]
    {N M : Net S ν}
    (h : Equiv N M)
    -- the first one is not linear
    (hN : ¬ N.Linear) :
    -- then they are equal
    N = M := by
  induction h with
  | rel _ _ h => exact absurd h.linear_left hN
  | refl _ => rfl
  | symm K L h ih => exact (ih fun hK => hN (Equiv.linear h hK)).symm
  | trans K M L h₁ _ ih₁ ih₂ =>
    rw [ih₁ hN]
    exact ih₂ fun hM => hN ((Equiv.symm h₁).linear hM)

end INet
