/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorPathComponent

/-!
# P2880_T1_Kempe Orientation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2880_T1_KempeOrientation
    {V E : Type*} (G : LooplessMultigraph V E)
    {k : Nat} (mu : PartialEdgeColoring E k) (alpha beta : Fin k)
    (hne : alpha ≠ beta) :
    TwoColorIncidenceGraph G mu alpha beta =
      TwoColorIncidenceGraph G mu beta alpha ∧
    (∀ z, TwoColorComponent G mu alpha beta z =
      TwoColorComponent G mu beta alpha z) ∧
    (∀ z, TwoColorComponentSwap G mu alpha beta z =
      TwoColorComponentSwap G mu beta alpha z) ∧
    (∀ z, TwoColorPathComponent G mu alpha beta z ↔
      TwoColorPathComponent G mu beta alpha z) := by
  classical
  have hgraph : TwoColorIncidenceGraph G mu alpha beta =
      TwoColorIncidenceGraph G mu beta alpha := by
    ext x y
    cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
  have hcomp : ∀ z, TwoColorComponent G mu alpha beta z =
      TwoColorComponent G mu beta alpha z := by
    intro z
    unfold TwoColorComponent
    rw [hgraph]
  refine ⟨hgraph, hcomp, ?_, ?_⟩
  · intro z
    funext e
    unfold TwoColorComponentSwap
    rw [← hcomp z]
    by_cases hc : Sum.inr e ∈ TwoColorComponent G mu alpha beta z
    · by_cases ha : mu e = some alpha
      · simp [hc, ha, hne]
      · by_cases hb : mu e = some beta
        · simp [hc, hb]
        · simp [hc, ha, hb]
    · simp [hc]
  · intro z
    unfold TwoColorPathComponent
    rw [hgraph, hcomp]
    simp only [ne_comm]

end GoldbergSeymour

end
