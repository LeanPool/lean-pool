/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import Mathlib.Data.Fintype.Basic
public import LeanPool.DeciSigma1.Semantics.Order
import Mathlib.Tactic.Bound.Init

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Flat subtype constraints

A constraint is a finite conjunction of literals `LitT n V` with variables in an arbitrary type:
variable inequalities, constructor bounds, and equations to `⊥` or `⊤`. Satisfaction is defined
for a variance `c` through `Tree.Le c`, and covariantly through the order of `Tree`.

## Main declarations

- `LitT`, `LitT.map`: flat literals and variable renaming.
- `HoldsT`, `SatT`: satisfaction with variance.
- `Covariant.Holds`, `Covariant.Sat`: covariant satisfaction.
-/

@[expose] public section


namespace DeciSigma1.Constraints
open DeciSigma1.Semantics

variable {n : ℕ}

/-- Flat literals over `{⊥, f, ⊤}` with variables in `V`: `x ≤ y`, `f(a) ≤ x`, `x ≤ f(a)`, `x = ⊥`
and `x = ⊤`. -/
inductive LitT (n : ℕ) (V : Type*) where
  | le (u v : V)
  | fLe (a : Fin n → V) (u : V)
  | leF (u : V) (a : Fin n → V)
  | eqBot (u : V)
  | eqTop (u : V)
  deriving DecidableEq

/-- Rename the variables of a literal. -/
def LitT.map {V W : Type*} (f : V → W) : LitT n V → LitT n W
  | .le u v => .le (f u) (f v)
  | .fLe a u => .fLe (f ∘ a) (f u)
  | .leF u a => .leF (f u) (f ∘ a)
  | .eqBot u => .eqBot (f u)
  | .eqTop u => .eqTop (f u)

/-- Satisfaction of a literal by an assignment, with variance `c`. -/
def HoldsT {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n) : LitT n V → Prop
  | .le u v => Tree.Le c (ρ u) (ρ v)
  | .fLe a u => Tree.Le c (Semantics.Tree.node (ρ ∘ a)) (ρ u)
  | .leF u a => Tree.Le c (ρ u) (Semantics.Tree.node (ρ ∘ a))
  | .eqBot u => ρ u = Tree.bot
  | .eqTop u => ρ u = Tree.top

@[simp] theorem holdsT_map {V W : Type*} (c : Fin n → Bool)
    (f : V → W) (ρ : W → Semantics.Tree n) (l : LitT n V) :
    HoldsT c ρ (l.map f) ↔ HoldsT c (ρ ∘ f) l := by cases l <;> rfl

/-- Satisfaction of a finite conjunction of literals, with variance `c`. -/
def SatT {V : Type*} (c : Fin n → Bool) (ρ : V → Semantics.Tree n)
    (Γ : List (LitT n V)) : Prop := ∀ l ∈ Γ, HoldsT c ρ l

/-- Covariant satisfaction of a literal. -/
def Covariant.Holds {V : Type*} (ρ : V → Semantics.Tree n) : LitT n V → Prop
  | .le x y => ρ x ≤ ρ y
  | .leF x a => ρ x ≤ Semantics.Tree.node (ρ ∘ a)
  | .fLe a x => Semantics.Tree.node (ρ ∘ a) ≤ ρ x
  | .eqBot x => ρ x = Tree.bot
  | .eqTop x => ρ x = Tree.top

/-- Covariant satisfaction of a finite conjunction. -/
def Covariant.Sat {V : Type*} (ρ : V → Semantics.Tree n) (Γ : List (LitT n V)) : Prop :=
  ∀ l ∈ Γ, Holds ρ l

@[simp] theorem holds_false {V : Type*} (ρ : V → Semantics.Tree n) (l : LitT n V) :
    HoldsT (fun _ => false) ρ l ↔ Covariant.Holds ρ l := by
  cases l <;> simp [HoldsT, Covariant.Holds]

@[simp] theorem sat_false {V : Type*} (ρ : V → Semantics.Tree n) (Γ : List (LitT n V)) :
    SatT (fun _ => false) ρ Γ ↔ Covariant.Sat ρ Γ := by simp [SatT, Covariant.Sat]

end DeciSigma1.Constraints
