/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Sym.Sym2.Init

/-!
# Finite Strict Growth Reaches Terminal

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem FiniteStrictGrowthReachesTerminal
    {V : Type*} [Finite V] (State Terminal : Finset V → Prop)
    (grow : ∀ X, State X → ¬ Terminal X →
      ∃ Y, State Y ∧ X < Y)
    {X0 : Finset V} (hX0 : State X0) :
    ∃ X, State X ∧ Terminal X := by
  classical
  let := Fintype.ofFinite V
  suffices hgo : ∀ X, State X → ∃ Y, State Y ∧ Terminal Y by
    exact hgo X0 hX0
  intro X
  induction X using
      (measure (fun X : Finset V => Fintype.card V - X.card)).wf.induction with
  | h X ih =>
    intro hX
    by_cases hterminal : Terminal X
    · exact ⟨X, hX, hterminal⟩
    · obtain ⟨Y, hY, hXY⟩ := grow X hX hterminal
      apply ih Y
      · have hcard : X.card < Y.card := Finset.card_lt_card hXY
        have hYcard : Y.card ≤ Fintype.card V := Finset.card_le_univ Y
        have hXcard : X.card < Fintype.card V := lt_of_lt_of_le hcard hYcard
        exact Nat.sub_lt_sub_left hXcard hcard
      · exact hY

end GoldbergSeymour

end
