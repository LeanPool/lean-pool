/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: shared data for the two universality constructions. -/

module

public import LeanPool.InteractionCombinators.Universality.DecompositionData
public import LeanPool.InteractionCombinators.Universality.RecursionFree.Expand

/-!
# Choosing and expanding the sides of a rule

Lafont’s two translations choose the factor on the cell’s auxiliary ports from the rule
in either orientation. Each chosen factor is then expanded while keeping its wire permutation.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

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

namespace System.DecData

-- the decomposition data of the system
variable {I : System S} (D : I.DecData)

/-- The side `φ` of the decomposition of a rule `α`–`β`, on the ports of `α` (page 86). -/
def rawφ
    -- the two symbols
    (α β : S.Sym)
    -- the rule `α`–`β`
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
    -- the rule `β`–`α`
    (r : Rule S (S.arity β) (S.arity α))
    (h : I.rule β α = some r) :
    RawSide S (S.arity α) :=
  ⟨_, (D.dec β α r h).ψ, (D.dec β α r h).σ, (D.linear β α r h).2, (D.reduced β α r h).2,
    D.involutive β α r h⟩

open Classical in
/-- The side `φ_{α,β}` of `α` against `β` (page 86): the `φ` of the rule `α`–`β` if it exists,
otherwise the `ψ` of the rule `β`–`α` if it exists, otherwise nothing. -/
noncomputable def rawSide
    -- the symbol whose side it is, and the symbol it faces
    (α β : S.Sym) :
    Option (RawSide S (S.arity α)) :=
  if h : ∃ r, I.rule α β = some r then some (D.rawφ α β h.choose h.choose_spec)
  else if h' : ∃ r, I.rule β α = some r then some (D.rawψ α β h'.choose h'.choose_spec)
  else none

/-- The side `φ_{α,β}` in expanded form (page 86), the input of Fig. 10 (page 90). -/
noncomputable def side
    -- the symbol whose side it is, and the symbol it faces
    (α β : S.Sym) :
    Option (ExpSide S (S.arity α)) :=
  (D.rawSide α β).map RawSide.expand

/-- With a rule `α`–`β`, the side of `α` against `β` is the `φ` of its decomposition
(page 86). -/
theorem rawSide_of_rule
    -- a rule `α`–`β`
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (h : I.rule α β = some r) :
    -- the side of `α` against `β` is its `φ`
    D.rawSide α β = some (D.rawφ α β r h) := by
  have hc : ∃ r, I.rule α β = some r := ⟨r, h⟩
  have e : hc.choose = r := Option.some.inj (hc.choose_spec.symm.trans h)
  rw [rawSide, dite_eq_left_of_eq_true (eq_true hc)]
  subst e
  rfl

/-- Without a rule `α`–`β` but with a rule `β`–`α`, the side of `α` against `β` is the `ψ` of the
decomposition of `β`–`α` (page 86, `φ_{j,i} = ψ_{i,j}`). -/
theorem rawSide_of_rule_swap
    -- no rule `α`–`β`
    {α β : S.Sym}
    (h₀ : I.rule α β = none)
    -- a rule `β`–`α`
    {r : Rule S (S.arity β) (S.arity α)}
    (h : I.rule β α = some r) :
    -- the side of `α` against `β` is the `ψ` of the rule `β`–`α`
    D.rawSide α β = some (D.rawψ α β r h) := by
  have hn : ¬ ∃ r, I.rule α β = some r := by rintro ⟨r', h'⟩; rw [h₀] at h'; cases h'
  have hc : ∃ r, I.rule β α = some r := ⟨r, h⟩
  have e : hc.choose = r := Option.some.inj (hc.choose_spec.symm.trans h)
  rw [rawSide, dite_eq_right_of_eq_false (eq_false hn), dite_eq_left_of_eq_true (eq_true hc)]
  subst e
  rfl

/-- Without a rule between `α` and `β`, there is no side (page 86). -/
theorem rawSide_eq_none
    -- no rule `α`–`β` and no rule `β`–`α`
    {α β : S.Sym}
    (h₀ : I.rule α β = none)
    (h₁ : I.rule β α = none) :
    -- `α` has no side against `β`
    D.rawSide α β = none := by
  have hn : ¬ ∃ r, I.rule α β = some r := by rintro ⟨r', h'⟩; rw [h₀] at h'; cases h'
  have hn' : ¬ ∃ r, I.rule β α = some r := by rintro ⟨r', h'⟩; rw [h₁] at h'; cases h'
  rw [rawSide, dite_eq_right_of_eq_false (eq_false hn), dite_eq_right_of_eq_false (eq_false hn')]

/-- The side chosen for `α` against `β` is the expanded form of `rawSide` (page 86). -/
theorem side_eq
    -- the symbol whose side it is, and the symbol it faces
    (α β : S.Sym) :
    D.side α β = (D.rawSide α β).map RawSide.expand := rfl

/-- There is a side of `α` against `β` exactly when there is a rule `α`–`β` or a rule `β`–`α`
(page 86). -/
theorem side_isSome_iff
    -- the symbol whose side it is, and the symbol it faces
    (α β : S.Sym) :
    -- `α` has a side against `β`
    (D.side α β).isSome
      -- if and only if there is a rule `α`–`β` or a rule `β`–`α`
      ↔ (∃ r, I.rule α β = some r) ∨ ∃ r, I.rule β α = some r := by
  rw [side_eq, Option.isSome_map, rawSide]
  split_ifs with h h'
  · exact iff_of_true rfl (Or.inl h)
  · exact iff_of_true rfl (Or.inr h')
  · exact iff_of_false (by simp) (by rintro (h₁ | h₁) <;> contradiction)

/-- For a rule `α`–`α`, the side `ψ` is the side `φ` (page 86, `φ_{i,i} = ψ_{i,i}`). -/
theorem rawψ_self
    -- a rule `r` between `α` and itself
    {α : S.Sym}
    {r : Rule S (S.arity α) (S.arity α)}
    (h : I.rule α α = some r) :
    D.rawψ α α r h = D.rawφ α α r h := by
  have e := D.self α r h
  unfold rawψ rawφ
  congr 1

/-- **The side of `β` against `α`, for a rule `α`–`β`, is the `ψ` of its decomposition** (page 86,
`φ_{j,i} = ψ_{i,j}`), in a well-formed system: for `α ≠ β` there is no rule `β`–`α`
(`WellFormed.unique`), for `α = β` the field `self` applies. -/
theorem rawSide_swap_of_rule
    -- the system is well formed
    (hI : I.WellFormed)
    -- a rule `r` between `α` and `β`
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (h : I.rule α β = some r) :
    D.rawSide β α = some (D.rawψ β α r h) := by
  by_cases hab : α = β
  · subst hab
    rw [D.rawSide_of_rule h, D.rawψ_self h]
  · exact D.rawSide_of_rule_swap (hI.unique α β hab (by simp [h])) h

end System.DecData

end INet
