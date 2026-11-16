/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Entailment.Guard
public import LeanPool.DeciSigma1.Full.Decide
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Deciding disjunctive entailment over `{⊥, f}`

Disjunctive entailment over `{⊥, f}` is the entailment of the guarded constraint over
`{⊥, f, ⊤}` with a covariant constructor (`disjEntailsIn_iff_guarded`,
`disjEntailsIn_finite_iff_guarded`), which is decided by `Full.decideDisjEntails` over
arbitrary trees and by `Full.decideDisjEntailsFin` over finite trees. The guarded constraint
lists every variable; the variables of a finite type are given without an order, and the
decision does not depend on the order chosen. Over regular trees the entailment agrees with
entailment over arbitrary trees.

## Main declarations

- `Entailment.decideDisjEntails`: the decision procedure over arbitrary trees.
- `Entailment.decideDisjEntailsReg`: the decision procedure over regular trees.
- `Entailment.decideDisjEntailsFin`: the decision procedure over finite trees.
-/

@[expose] public section


namespace DeciSigma1.Entailment

open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics

variable {n : ℕ} {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}

/-- A proposition is decidable when it is equivalent, for every list `vs` of all variables, to a
decidable proposition `r vs`. The list is formed from the elements of `V`, which come without an
order; the answer does not depend on the order. -/
def decideOfAllVariables {p : Prop} (r : List V → Prop) (dec : ∀ vs, Decidable (r vs))
    (h : ∀ vs : List V, (∀ v, v ∈ vs) → (p ↔ r vs)) : Decidable p :=
  Quotient.recOnSubsingleton (motive := fun vs : Multiset V => (∀ v, v ∈ vs) → Decidable p)
    Finset.univ.val (fun vs hvs => @decidable_of_iff _ _ (h vs hvs).symm (dec vs))
    Finset.mem_univ_val

/-- Disjunctive entailment over `{⊥, f}` is decidable over arbitrary trees, uniformly in the
number of queries: the decision procedure for `{⊥, f, ⊤}` is applied to the guarded constraint,
formed with any list of all variables. -/
def decideDisjEntails (Γ : List (Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsIn (fun _ => True) Γ q) :=
  decideOfAllVariables _
    (fun vs => Full.decideDisjEntails (fun _ => false) (guarded vs Γ) (guardedQueries q))
    (fun _ hvs => disjEntailsIn_iff_guarded hvs Γ q)

/-- Disjunctive entailment over `{⊥, f}` is decidable over regular trees, where it agrees with
entailment over arbitrary trees. -/
def decideDisjEntailsReg (Γ : List (Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsIn IsRegularTree Γ q) :=
  @decidable_of_iff _ _ (disjEntailsIn_regular_iff Γ q).symm (decideDisjEntails Γ q)

/-- Disjunctive entailment over `{⊥, f}` is decidable over finite trees, uniformly in the
number of queries: the decision procedure for finite trees over `{⊥, f, ⊤}` is applied to the
guarded constraint. -/
def decideDisjEntailsFin (Γ : List (Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsIn IsFiniteTree Γ q) :=
  decideOfAllVariables _
    (fun vs => Full.decideDisjEntailsFin (fun _ => false) (guarded vs Γ) (guardedQueries q))
    (fun _ hvs => disjEntailsIn_finite_iff_guarded hvs Γ q)

end DeciSigma1.Entailment
