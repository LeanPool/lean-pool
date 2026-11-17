/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Semantics.PrefixSet
public import Mathlib.Data.Fintype.Basic

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Flat constraints over `{⊥, f}`

Flat literals over `{⊥, f}` with variables in an arbitrary type: variable inequalities `x ≤ y`,
constructor bounds `f(a) ≤ x` and `x ≤ f(a)`, and equations `x = ⊥`. They are interpreted in trees
over `{⊥, f}`, represented by their sets of constructor positions (`PrefixSet`) and ordered by
inclusion.

## Main declarations

- `TopFree.Lit`, `TopFree.Lit.Holds`, `TopFree.Sat`: literals and their satisfaction.
-/

@[expose] public section


namespace DeciSigma1.Constraints.TopFree

open DeciSigma1.Semantics
variable {n : ℕ}

/-- Flat literals over `{⊥, f}` with variables in `V`: `x ≤ y`, `f(a) ≤ x`, `x ≤ f(a)` and
`x = ⊥`. -/
inductive Lit (n : ℕ) (V : Type*) where
  | le (u v : V)
  | fLe (a : Fin n → V) (u : V)
  | leF (u : V) (a : Fin n → V)
  | eqBot (u : V)
  deriving DecidableEq

/-- Satisfaction of a literal by an assignment of trees over `{⊥, f}`. -/
def Lit.Holds {V : Type*} (ρ : V → PrefixSet n) : Lit n V → Prop
  | .le u v => ρ u ≤ ρ v
  | .fLe a u => PrefixSet.node (ρ ∘ a) ≤ ρ u
  | .leF u a => ρ u ≤ PrefixSet.node (ρ ∘ a)
  | .eqBot u => ρ u = PrefixSet.bot

/-- Satisfaction of a finite conjunction of literals. -/
def Sat {V : Type*} (ρ : V → PrefixSet n) (Γ : List (Lit n V)) : Prop :=
  ∀ l ∈ Γ, l.Holds ρ

end DeciSigma1.Constraints.TopFree
