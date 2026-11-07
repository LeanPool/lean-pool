/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MissingColors
public import Mathlib.Basic.Finite.Sum
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring

/-!
# Missing Color Incidence Endpoint

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem MissingColorIncidenceEndpoint {V E : Type*}
     [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (_ : alpha ≠ beta)
    (hproper : IsProperEdgeColoring G phi) (v : V)
    (hmissing : alpha ∈ MissingColors G phi v) :
    @SimpleGraph.degree _ (TwoColorIncidenceGraph G phi alpha beta) (Sum.inl v)
      (Fintype.ofFinite _) ≤ 1 := by
  classical
  let _ := Fintype.ofFinite V
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have haAdj : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inl v) a :=
    by simpa [SimpleGraph.neighborFinset] using ha
  have hbAdj : (TwoColorIncidenceGraph G phi alpha beta).Adj (Sum.inl v) b :=
    by simpa [SimpleGraph.neighborFinset] using hb
  cases a with
  | inl a => simp [TwoColorIncidenceGraph] at haAdj
  | inr a =>
    cases b with
    | inl b => simp [TwoColorIncidenceGraph] at hbAdj
    | inr b =>
      by_contra hab
      have haData := haAdj
      have hbData := hbAdj
      simp only [TwoColorIncidenceGraph] at haData hbData
      rcases haData with ⟨haIncident, haColor⟩
      rcases hbData with ⟨hbIncident, hbColor⟩
      have haNot : ¬ phi a = some alpha := by
        intro haAlpha
        have hpresent : alpha ∈ PresentColors G phi v := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨a, haIncident, haAlpha⟩
        have hnotpresent : alpha ∉ PresentColors G phi v := by
          simpa [MissingColors] using hmissing
        exact hnotpresent hpresent
      have haBeta : phi a = some beta := haColor.resolve_left haNot
      have hbBeta : phi b = some beta := hbColor.resolve_left (by
        intro hbAlpha
        have hpresent : alpha ∈ PresentColors G phi v := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨b, hbIncident, hbAlpha⟩
        have hnotpresent : alpha ∉ PresentColors G phi v := by
          simpa [MissingColors] using hmissing
        exact hnotpresent hpresent)
      have hadj : AdjacentEdges G a b := ⟨v, haIncident, hbIncident⟩
      have habEdges : a ≠ b := by
        intro habEdges
        exact hab (congrArg Sum.inr habEdges)
      exact (hproper habEdges hadj haBeta) hbBeta

end GoldbergSeymour

end
