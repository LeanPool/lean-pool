/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Bound.Init

/-!
# Shared facts for ExtensionBaseClaim45Singleton

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ExtensionBaseClaim45Singleton

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev rho0UnaffectedStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
        ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] {G : LooplessMultigraph V E}
          {k : ℕ} {e0 : E} (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k)
          (deltaN beta : Fin k),
          let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
          ∀ (c : Fin k) (_ : c ≠ beta) (_ : c ≠ deltaN) (f : E),
            rho0 f = some c ↔ rho1 f = some c

/-- A common proof used by the branches of this transport or construction argument. -/
theorem rho0_unaffected.{u_1, u_2} : rho0UnaffectedStatement.{u_1, u_2} := by
  classical
  intro V E _ _ G k e0 TjPrime rho1 deltaN beta rho0 c hcb hcd f
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  unfold rho0 OutsideTreeColorSwap
  by_cases ht : TreeIncidentEdge TjPrime f
  · simp [ht]
  · simp only [ite_eq_right ht]
    by_cases hfb : rho1 f = some beta
    · rw [ite_eq_left hfb]
      constructor
      · intro h
        exact False.elim (hcd (Option.some.inj h).symm)
      · intro h
        exact False.elim (hcb (Option.some.inj (h.symm.trans hfb)))
    · rw [ite_eq_right hfb]
      by_cases hfd : rho1 f = some deltaN
      · rw [ite_eq_left hfd]
        constructor
        · intro h
          exact False.elim (hcb (Option.some.inj h).symm)
        · intro h
          exact False.elim (hcd (Option.some.inj (h.symm.trans hfd)))
      · rw [ite_eq_right hfd]

end GoldbergSeymour.SharedFacts.ExtensionBaseClaim45Singleton

end
