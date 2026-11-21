/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.RecursionFree
public import LeanPool.InteractionCombinators.Universality.RuleSides

/-!
# Sides of recursion-free rules

The recursion-free translation uses the shared rule sides with the order forgotten.
The rank bounds on the cells of each chosen side persist after expansion.
-/

@[expose] public section

namespace INet

variable {S : Signature}

namespace System.RecursionFreeData

variable {I : System S} (D : I.RecursionFreeData)

/-- The side `φ` of the decomposition of a rule `α`–`β`, on the ports of `α` (page 86). -/
def rawφ
    -- the two symbols
    (α β : S.Sym)
    -- the rule `α`–`β` of the system
    (r : Rule S (S.arity α) (S.arity β))
    (h : I.rule α β = some r) :
    RawSide S (S.arity α) :=
  D.toDecData.rawφ α β r h

/-- The side `ψ` of the decomposition of a rule `β`–`α`, on the ports of `α`: the side `φ_{α,β}`
read from the rule `β`–`α` (page 86, `φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`). -/
def rawψ
    -- the two symbols
    (α β : S.Sym)
    -- the rule `β`–`α` of the system
    (r : Rule S (S.arity β) (S.arity α))
    (h : I.rule β α = some r) :
    RawSide S (S.arity α) :=
  D.toDecData.rawψ α β r h

/-- The side `φ_{α,β}` of `α` against `β` (page 86): the `φ` of the rule `α`–`β` if it exists,
otherwise the `ψ` of the rule `β`–`α` if it exists, otherwise nothing. -/
noncomputable def rawSide
    -- the cell `α` whose side is taken, against `β`
    (α β : S.Sym) :
    Option (RawSide S (S.arity α)) :=
  D.toDecData.rawSide α β

/-- The side `φ_{α,β}` in expanded form (page 86). -/
noncomputable def side
    -- the cell `α` whose side is taken, against `β`
    (α β : S.Sym) :
    Option (ExpSide S (S.arity α)) :=
  D.toDecData.side α β

/-- With a rule `α`–`β`, the side of `α` against `β` is the `φ` of its decomposition. -/
theorem rawSide_of_rule
    -- the two symbols, and the rule `α`–`β` of the system
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (h : I.rule α β = some r) :
    -- the side is the `φ` of the decomposition of `α`–`β`
    D.rawSide α β = some (D.rawφ α β r h) :=
  D.toDecData.rawSide_of_rule h

/-- Without a rule `α`–`β` but with a rule `β`–`α`, the side of `α` against `β` is the `ψ` of the
decomposition of `β`–`α` (page 86, `φ_{j,i} = ψ_{i,j}`). -/
theorem rawSide_of_rule_swap
    -- the two symbols: no rule `α`–`β`
    {α β : S.Sym}
    (h₀ : I.rule α β = none)
    -- the rule `β`–`α` of the system
    {r : Rule S (S.arity β) (S.arity α)}
    (h : I.rule β α = some r) :
    -- the side is the `ψ` of the decomposition of `β`–`α`
    D.rawSide α β = some (D.rawψ α β r h) :=
  D.toDecData.rawSide_of_rule_swap h₀ h

/-- Without a rule between `α` and `β`, there is no side. -/
theorem rawSide_eq_none
    -- the two symbols, with no rule `α`–`β` and no rule `β`–`α`
    {α β : S.Sym}
    (h₀ : I.rule α β = none)
    (h₁ : I.rule β α = none) :
    -- there is no side
    D.rawSide α β = none :=
  D.toDecData.rawSide_eq_none h₀ h₁

/-- The side chosen for `α` against `β` is the expanded form of `rawSide` (page 86). -/
theorem side_eq
    -- the cell `α` whose side is taken, against `β`
    (α β : S.Sym) :
    -- the side is the expanded form of the raw side
    D.side α β = (D.rawSide α β).map RawSide.expand := rfl

/-- Every cell of the side `φ_{α,β}` has rank `< rank β` (page 86): `rank_φ` for the rule
`α`–`β`, `rank_ψ` for the rule `β`–`α`. -/
theorem rank_rawSide
    -- the two symbols, and the side `s` of `α` against `β`
    {α β : S.Sym}
    {s : RawSide S (S.arity α)}
    (hs : D.rawSide α β = some s) :
    -- every cell of the side has rank `< rank β`
    ∀ γ ∈ s.φ.net.cells, D.rank γ < D.rank β := by
  unfold rawSide System.DecData.rawSide at hs
  split_ifs at hs with h h'
  · cases hs; exact D.rank_φ α β _ h.choose_spec
  · cases hs; exact D.rank_ψ β α _ h'.choose_spec

-- ============================================================================================
-- 4. Main result: the rank of the cells of a side
-- ============================================================================================

/-- **The side `φ_{α,β}`, expanded, has only cells of rank `< rank β`** (page 86): the bound of
`rank_rawSide`, kept by the expanded form. -/
theorem rank_side
    -- the two symbols, and the expanded side `s` of `α` against `β`
    {α β : S.Sym}
    {s : ExpSide S (S.arity α)}
    (hs : D.side α β = some s) :
    -- every cell of the side has rank `< rank β`
    ∀ γ ∈ s.φ.net.cells, D.rank γ < D.rank β := by
  obtain ⟨s₀, hs₀, rfl⟩ := Option.map_eq_some_iff.1 hs
  intro γ hγ
  rw [show s₀.expand.φ.net.cells = _ from s₀.cells_expand] at hγ
  exact D.rank_rawSide hs₀ γ hγ

/-- The sides of a recursion-free system (page 86) are those of its data with the order
forgotten (page 90). -/
theorem rawSide_toDecData :
    D.toDecData.rawSide = D.rawSide := rfl

/-- The expanded sides of a recursion-free system (page 86) are those of its data with the order
forgotten (page 90): stage 5 is a special case. -/
theorem side_toDecData :
    D.toDecData.side = D.side := rfl

end System.RecursionFreeData

end INet
