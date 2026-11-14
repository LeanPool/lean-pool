/-
Copyright (c) 2026 Wesley Pegden and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden, Lean Pool contributors
-/
module

public import LeanPool.GoldbergSeymour.Degree
public import LeanPool.GoldbergSeymour.MissingColors
public import Mathlib.Data.Fintype.Card

/-!
# Color and degree bounds

General color-counting facts extracted from the proofs in Wesley Pegden's Trellis formalization
at 88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. No properness or criticality assumption is needed.
-/

@[expose] public section

namespace GoldbergSeymour

/-- Distinct present colors require distinct incident edges, including in a multigraph. -/
theorem PresentColors.card_le_degree {V E : Type*} [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k) (v : V) :
    (PresentColors G phi v).card ≤ Degree G v := by
  classical
  have chooseEdge (c : {c : Fin k // c ∈ PresentColors G phi v}) :
      ∃ edge, Incident G v edge ∧ phi edge = some c.1 := by
    simpa [PresentColors] using c.property
  let select : {c : Fin k // c ∈ PresentColors G phi v} →
      {edge : E // Incident G v edge} := fun c =>
    ⟨Classical.choose (chooseEdge c), (Classical.choose_spec (chooseEdge c)).1⟩
  have selectColor : ∀ c, phi (select c).1 = some c.1 := by
    intro c
    exact (Classical.choose_spec (chooseEdge c)).2
  have injective : Function.Injective select := by
    intro a b equal
    apply Subtype.ext
    apply Option.some.inj
    calc
      some (a : Fin k) = phi (select a).1 := (selectColor a).symm
      _ = phi (select b).1 := by rw [equal]
      _ = some (b : Fin k) := selectColor b
  have bound := Fintype.card_le_of_injective select injective
  simpa [Degree, Fintype.card_subtype] using bound

/-- A palette larger than the degree leaves a missing color, for any partial coloring. -/
theorem MissingColors.nonempty_of_degree_lt {V E : Type*} [Fintype E]
    (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k) (v : V)
    (bound : Degree G v < k) : (MissingColors G phi v).Nonempty := by
  classical
  have present := PresentColors.card_le_degree G phi v
  have strict : (PresentColors G phi v).card < (Finset.univ : Finset (Fin k)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using present.trans_lt bound
  exact Finset.sdiff_nonempty.mpr (fun subset => (not_lt_of_ge (Finset.card_le_card subset)) strict)

end GoldbergSeymour

end
