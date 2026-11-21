/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.RecursionFree
public import LeanPool.InteractionCombinators.Universality.RecursionFree.Expand

/-!
# The side `φ_{i,j}` of a recursion-free system, chosen expanded (page 86)

Lafont 1997, Section 2.4, journal page 86 (PDF page 18). The package `Γ_{i,j}` of Fig. 6 is built
from the side `φ_{i,j}` of the rule `α_i`–`α_j` on the ports of `α_i`, and from `σ_{i,j}`. A
system in this development has at most one of the rules `α`–`β`, `β`–`α` (`System.WellFormed`),
so the side of `α` against `β` is read from the one rule that exists (page 86, "`φ_{j,i} = ψ_{i,j}`,
`σ_{j,i} = σ_{i,j}`"):

* the `φ` of the decomposition of `α`–`β`, if `I.rule α β = some r`;
* otherwise the `ψ` of the decomposition of `β`–`α`, if `I.rule β α = some r`;
* nothing if neither rule exists.

Fig. 6 needs it in expanded form (one tree per port), which `Rule.exists_expanded` gives.

Contents, in the order of the file:

1. Definitions: `RawSide`, `ExpSide` (a side with its permutation, linear and reduced, resp.
   linear and expanded), `RawSide.expand` (the expanded form), and
   `System.RecursionFreeData.rawφ`, `.rawψ`, `.rawSide`, `.side` (the side of `α` against `β`).
2. Auxiliary lemmas on the expanded form: `RawSide.expand_k`, `RawSide.expand_spec` (the injective
   renaming `ι` and the `Equiv` of `Rule.exists_expanded`, kept for the later proof of Fig. 7),
   `RawSide.cells_expand`.
3. Auxiliary lemmas on the chosen side: `rawSide_of_rule`, `rawSide_of_rule_swap`,
   `rawSide_eq_none` (which side is chosen), `side_eq`, `rank_rawSide`.
4. Main result: `rank_side`, every cell of `φ_{α,β}` has rank `< rank β` (page 86).
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Definitions: the sides, and the side of `α` against `β`
-- ============================================================================================

/-- A side of a decomposition (page 85) with its permutation of the middle wires: linear and
reduced, the permutation involutive (page 86). -/
structure RawSide (S : Signature) (a : ℕ) where
  /-- The number of middle wires. -/
  k : ℕ
  /-- The side, on the `a` ports of the cell and the `k` middle wires. -/
  φ : Rule S a k
  /-- The permutation of the middle wires. -/
  σ : Equiv.Perm (Fin k)
  -- the side is linear and reduced, the permutation an involution
  linear : φ.Linear
  reduced : φ.Reduced
  involutive : Function.Involutive σ

/-- A side of a decomposition with its permutation, linear and in expanded form (page 86), the
input of `gamma`. -/
structure ExpSide (S : Signature) (a : ℕ) where
  /-- The number of middle wires. -/
  k : ℕ
  /-- The side, on the `a` ports of the cell and the `k` middle wires. -/
  φ : Rule S a k
  /-- The permutation of the middle wires. -/
  σ : Equiv.Perm (Fin k)
  -- the side is linear and expanded, the permutation an involution
  linear : φ.Linear
  expanded : φ.Expanded
  involutive : Function.Involutive σ

namespace RawSide

variable {a : ℕ}

/-- The expanded form of a side (page 86), chosen by `Rule.exists_expanded`; the permutation is
kept. -/
noncomputable def expand
    -- a side on the `a` ports of a cell
    (s : RawSide S a) :
    ExpSide S a where
  k := s.k
  φ := (s.φ.exists_expanded s.linear s.reduced).choose
  σ := s.σ
  linear := (s.φ.exists_expanded s.linear s.reduced).choose_spec.choose_spec.2.1
  expanded := (s.φ.exists_expanded s.linear s.reduced).choose_spec.choose_spec.2.2.1
  involutive := s.involutive

end RawSide

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
  ⟨_, (D.dec α β r h).φ, (D.dec α β r h).σ, (D.linear α β r h).1, (D.reduced α β r h).1,
    D.involutive α β r h⟩

/-- The side `ψ` of the decomposition of a rule `β`–`α`, on the ports of `α`: the side `φ_{α,β}`
read from the rule `β`–`α` (page 86, `φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`). -/
def rawψ
    -- the two symbols
    (α β : S.Sym)
    -- the rule `β`–`α` of the system
    (r : Rule S (S.arity β) (S.arity α))
    (h : I.rule β α = some r) :
    RawSide S (S.arity α) :=
  ⟨_, (D.dec β α r h).ψ, (D.dec β α r h).σ, (D.linear β α r h).2, (D.reduced β α r h).2,
    D.involutive β α r h⟩

open Classical in
/-- The side `φ_{α,β}` of `α` against `β` (page 86): the `φ` of the rule `α`–`β` if it exists,
otherwise the `ψ` of the rule `β`–`α` if it exists, otherwise nothing. -/
noncomputable def rawSide
    -- the cell `α` whose side is taken, against `β`
    (α β : S.Sym) :
    Option (RawSide S (S.arity α)) :=
  if h : ∃ r, I.rule α β = some r then some (D.rawφ α β h.choose h.choose_spec)
  else if h' : ∃ r, I.rule β α = some r then some (D.rawψ α β h'.choose h'.choose_spec)
  else none

/-- The side `φ_{α,β}` in expanded form (page 86). -/
noncomputable def side
    -- the cell `α` whose side is taken, against `β`
    (α β : S.Sym) :
    Option (ExpSide S (S.arity α)) :=
  (D.rawSide α β).map RawSide.expand

end System.RecursionFreeData

-- ============================================================================================
-- 2. Auxiliary lemmas: the expanded form of a side
-- ============================================================================================

namespace RawSide

variable {a : ℕ}

/-- The expanded side has the middle wires and the permutation of the side (page 86). -/
theorem expand_k
    -- a side on the `a` ports of a cell
    (s : RawSide S a) :
    -- the expanded side has the same number of middle wires
    s.expand.k = s.k := rfl

/-- **The expanded side plugs back** (page 86): it is `Equiv` to the side, up to an injective
renaming `ι` of the internal wires of the side (`Rule.exists_expanded`). -/
theorem expand_spec
    -- a side on the `a` ports of a cell
    (s : RawSide S a) :
    -- a renaming `ι` of the internal wires of the side into those of the expanded side
    ∃ ι : Fin s.φ.internal → Fin s.expand.φ.internal,
      -- `ι` is injective
      Function.Injective ι
      -- and the expanded side is `Equiv` to the side renamed by `ι`
      ∧ Equiv (show Net S (Fin a ⊕ Fin s.k ⊕ Fin s.expand.φ.internal) from s.expand.φ.net)
          (s.φ.net.bind fun x => Term.var (Sum.map id (Sum.map id ι) x)) := by
  obtain ⟨ι, hι, -, -, hE⟩ := (s.φ.exists_expanded s.linear s.reduced).choose_spec
  exact ⟨ι, hι, hE⟩

/-- The expanded side has the cells of the side (`Equiv.cells_eq`). -/
theorem cells_expand
    -- a side on the `a` ports of a cell
    (s : RawSide S a) :
    -- the cells of the expanded side are the cells of the side
    (show Net S (Fin a ⊕ Fin s.k ⊕ Fin s.expand.φ.internal) from s.expand.φ.net).cells
      = s.φ.net.cells := by
  obtain ⟨ι, -, hE⟩ := s.expand_spec
  rw [hE.cells_eq, Net.cells_bind_var]

end RawSide

-- ============================================================================================
-- 3. Auxiliary lemmas: which side is chosen
-- ============================================================================================

namespace System.RecursionFreeData

variable {I : System S} (D : I.RecursionFreeData)

/-- With a rule `α`–`β`, the side of `α` against `β` is the `φ` of its decomposition. -/
theorem rawSide_of_rule
    -- the two symbols, and the rule `α`–`β` of the system
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (h : I.rule α β = some r) :
    -- the side is the `φ` of the decomposition of `α`–`β`
    D.rawSide α β = some (D.rawφ α β r h) := by
  have hc : ∃ r, I.rule α β = some r := ⟨r, h⟩
  have e : hc.choose = r := Option.some.inj (hc.choose_spec.symm.trans h)
  rw [rawSide, dite_eq_left_of_eq_true (eq_true hc)]
  subst e
  rfl

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
    D.rawSide α β = some (D.rawψ α β r h) := by
  have hn : ¬ ∃ r, I.rule α β = some r := by rintro ⟨r', h'⟩; rw [h₀] at h'; cases h'
  have hc : ∃ r, I.rule β α = some r := ⟨r, h⟩
  have e : hc.choose = r := Option.some.inj (hc.choose_spec.symm.trans h)
  rw [rawSide, dite_eq_right_of_eq_false (eq_false hn), dite_eq_left_of_eq_true (eq_true hc)]
  subst e
  rfl

/-- Without a rule between `α` and `β`, there is no side. -/
theorem rawSide_eq_none
    -- the two symbols, with no rule `α`–`β` and no rule `β`–`α`
    {α β : S.Sym}
    (h₀ : I.rule α β = none)
    (h₁ : I.rule β α = none) :
    -- there is no side
    D.rawSide α β = none := by
  have hn : ¬ ∃ r, I.rule α β = some r := by rintro ⟨r', h'⟩; rw [h₀] at h'; cases h'
  have hn' : ¬ ∃ r, I.rule β α = some r := by rintro ⟨r', h'⟩; rw [h₁] at h'; cases h'
  rw [rawSide, dite_eq_right_of_eq_false (eq_false hn), dite_eq_right_of_eq_false (eq_false hn')]

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
  unfold rawSide at hs
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

end System.RecursionFreeData

end INet
