/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.General.CodeData
public import LeanPool.InteractionCombinators.Universality.RecursionFree.PlugsExpand

/-!
# The two sides of a rule from decomposition data without an order (pages 85–86, 90)

Lafont 1997, pages 85–86 (PDF pages 17–18): "one can assume that in all cases
`φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`, and `σ_{i,j}` is involutive"; page 90 (Section 2.7,
Fig. 10): the general translation uses the same decomposition, with no order.

The well-formedness hypothesis is needed: `Comb.CodeDataReview.sysBoth_sides_disagree`
(`Checks/Universality/General/CodeDataReview.lean`) gives decomposition data of a system that is not
well formed whose two sides disagree.

Contents, in the order of the file:

1. Auxiliary lemmas: the raw sides of a rule, for a well-formed system `I`, decomposition data
   `D : I.DecData` and a rule `α`–`β`.
   * `System.DecData.rawψ_self` — for `α = β`, the side `ψ` is the side `φ`.
   * `System.DecData.rawSide_swap_of_rule` — the side of `β` against `α` is the `ψ` of the
     decomposition of `α`–`β`.
   * `System.DecData.sides_of_rule` — the two raw sides, with the same `σ`, plug back the rule.
2. Main result: `System.DecData.sides_expand` — **the two expanded sides** `D.side α β`,
   `D.side β α` are both defined, share `k` and `σ`, and plug back the rule. This is the input
   `hs`, `hs'` of `codeCells_meet_end` and the `Plugs` used at the end of the compatibility proof
   of Fig. 10.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

namespace System.DecData

-- the interaction system, and its decomposition data
variable {I : System S} (D : I.DecData)

-- ============================================================================================
-- 1. Auxiliary lemmas: the raw sides of a rule
-- ============================================================================================

/-- **The two sides of a rule plug back into it** (pages 85–86, Fig. 10). In a well-formed system,
for a rule `α`–`β`: the side of `α` against `β` is the `φ` of its decomposition, the side of `β`
against `α` is its `ψ`, the two carry the same permutation (`σ_{j,i} = σ_{i,j}`), and plugging the
first against the second through it gives back the rule. -/
theorem sides_of_rule
    -- the system is well formed
    (hI : I.WellFormed)
    -- a rule `r` between `α` and `β`
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (h : I.rule α β = some r) :
    -- the side of `α` against `β` is the `φ` of the decomposition,
    D.rawSide α β = some (D.rawφ α β r h) ∧
      -- the side of `β` against `α` is its `ψ`,
      D.rawSide β α = some (D.rawψ β α r h) ∧
      -- the two carry the same permutation,
      (D.rawψ β α r h).σ = (D.rawφ α β r h).σ ∧
      -- and the first plugged against the second through it gives back the rule
      (⟨(D.rawφ α β r h).k, (D.rawφ α β r h).φ, (D.rawψ β α r h).φ, (D.rawφ α β r h).σ⟩ :
        Decomposition S (S.arity α) (S.arity β)).Plugs r :=
  ⟨D.rawSide_of_rule h, D.rawSide_swap_of_rule hI h, rfl, D.plug α β r h⟩

-- ============================================================================================
-- 2. Main result: the two expanded sides of a rule
-- ============================================================================================

/-- **The two expanded sides of a rule share `k` and `σ` and plug back into it** (pages 85–86 and
90, Fig. 10). In a well-formed system, for a rule `α`–`β`, the expanded side `D.side α β` of `α`
against `β` and the expanded side `D.side β α` of `β` against `α` are both defined, have the same
number `k` of middle wires and the same involution `σ` (page 86, `σ_{j,i} = σ_{i,j}`), and plugging
the first against the second through `σ` gives back the rule. No recursion-freeness is assumed:
this is the general case of Section 2.7. -/
theorem sides_expand
    -- the system is well formed
    (hI : I.WellFormed)
    -- a rule `r` between `α` and `β`
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (h : I.rule α β = some r) :
    -- there are a number `k` of middle wires, two sides `φ`, `ψ` with `k` middle ports, both
    -- linear and expanded, and an involution `σ` of the middle wires, such that
    ∃ (k : ℕ) (φ : Rule S (S.arity α) k) (ψ : Rule S (S.arity β) k) (σ : Equiv.Perm (Fin k))
      (hσ : Function.Involutive σ) (hl : φ.Linear) (he : φ.Expanded)
      (hl' : ψ.Linear) (he' : ψ.Expanded),
      -- the expanded side of `α` against `β` is `φ` with `σ`,
      D.side α β = some ⟨k, φ, σ, hl, he, hσ⟩ ∧
      -- the expanded side of `β` against `α` is `ψ` with the same `σ`,
      D.side β α = some ⟨k, ψ, σ, hl', he', hσ⟩ ∧
      -- and `φ` plugged against `ψ` through `σ` gives back the rule
      (⟨k, φ, ψ, σ⟩ : Decomposition S (S.arity α) (S.arity β)).Plugs r := by
  obtain ⟨hφ, hψ, -, hP⟩ := D.sides_of_rule hI h
  obtain ⟨ι₁, hι₁, h₁⟩ := (D.rawφ α β r h).expand_spec
  obtain ⟨ι₂, hι₂, h₂⟩ := (D.rawψ β α r h).expand_spec
  refine ⟨(D.rawφ α β r h).k, (D.rawφ α β r h).expand.φ, (D.rawψ β α r h).expand.φ,
    (D.rawφ α β r h).σ, (D.rawφ α β r h).involutive, (D.rawφ α β r h).expand.linear,
    (D.rawφ α β r h).expand.expanded, (D.rawψ β α r h).expand.linear,
    (D.rawψ β α r h).expand.expanded, ?_, ?_, ?_⟩
  · rw [side_eq, hφ]
    rfl
  · rw [side_eq, hψ]
    rfl
  · exact Decomposition.Plugs.of_expand
      (D := ⟨(D.rawφ α β r h).k, (D.rawφ α β r h).φ, (D.rawψ β α r h).φ, (D.rawφ α β r h).σ⟩)
      hP (D.rawφ α β r h).linear (D.rawψ β α r h).linear hι₁ hι₂ h₁ h₂

end System.DecData

end INet
