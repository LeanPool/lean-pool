/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: shared data for the two universality constructions. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.Decomposition

/-!
# Normalized decompositions of interaction rules

Lafont’s general and recursion-free translations use the same normalized rule decompositions.
These data record the factorization and its correctness conditions independently of any rank.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

/-- Plugging the two sides of `D` through its permutation gives back the rule `r`, up to `Equiv`
and an injective renaming of the internal wires of `r`: the form in which
`Rule.plug_decompose` states it for the canonical decomposition (page 85). -/
def Decomposition.Plugs
    -- the numbers of auxiliary ports of the two cells
    {a b : ℕ}
    -- the decomposition and the rule
    (D : Decomposition S a b)
    (r : Rule S a b) :
    Prop :=
  -- there is a renaming `ι` of the internal wires of `r` into those of the plugged sides
  ∃ ι : Fin r.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal,
    -- that is injective,
    Function.Injective ι ∧
    -- and the plugged sides are the same graph as `r` renamed by `ι`
    Equiv (Rule.plug D.φ D.ψ D.σ).net (r.net.bind fun x => var (Sum.map id (Sum.map id ι) x))

/-- The decomposition data of an interaction system (Lafont 1997, pages 85–86), without an order
(page 90): a decomposition of every rule, normalised as on page 86 — its sides linear and
reduced, `σ` involutive, `ψ = φ` for a rule `α`–`α`, `σ = 1` for a rule `α`–`β` with
`α ≠ β`. -/
structure System.DecData
    -- the interaction system
    (I : System S) where
  /-- The decomposition chosen for each rule. -/
  dec : ∀ α β (r : Rule S (S.arity α) (S.arity β)), I.rule α β = some r →
    Decomposition S (S.arity α) (S.arity β)
  /-- Plugging the sides gives back the rule (page 85). -/
  plug : ∀ α β r (h : I.rule α β = some r), (dec α β r h).Plugs r
  /-- The sides are linear. -/
  linear : ∀ α β r (h : I.rule α β = some r), (dec α β r h).φ.Linear ∧ (dec α β r h).ψ.Linear
  /-- The sides are reduced nets (page 85). -/
  reduced : ∀ α β r (h : I.rule α β = some r),
    (dec α β r h).φ.Reduced ∧ (dec α β r h).ψ.Reduced
  /-- `σ_{i,j}` is involutive (page 86). -/
  involutive : ∀ α β r (h : I.rule α β = some r), Function.Involutive (dec α β r h).σ
  /-- For a rule `α_i`–`α_i`, `φ_{i,i} = ψ_{i,i}` (page 86, `φ_{j,i} = ψ_{i,j}` with `i = j`). -/
  self : ∀ α r (h : I.rule α α = some r), (dec α α r h).ψ = (dec α α r h).φ
  /-- For a rule `α_i`–`α_j` with `i ≠ j`, `σ_{i,j}` is an identity (page 86). -/
  ne : ∀ α β r (h : I.rule α β = some r), α ≠ β → (dec α β r h).σ = 1

end INet
