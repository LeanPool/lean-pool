/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Two Color Component Swap Missing Behavior

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TwoColorComponentSwapMissingBehavior {V E : Type*}
    [Finite V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (_ : IsProperEdgeColoring G phi) (z : Sum V E) :
    let C := TwoColorComponent G phi alpha beta z
    let phi' := TwoColorComponentSwap G phi alpha beta z
    (∀ v : V, Sum.inl v ∉ C → MissingColors G phi' v = MissingColors G phi v) ∧
      (∀ v : V,
          Sum.inl v ∈ C → alpha ∈ MissingColors G phi v → beta ∈ MissingColors G phi' v) ∧
        (∀ v : V,
            Sum.inl v ∈ C → beta ∈ MissingColors G phi v → alpha ∈ MissingColors G phi' v) ∧
          ∀ v : V,
            ∀ c : Fin k,
              c ≠ alpha →
                c ≠ beta → (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors G phi v) := by
  classical
  let _ := Fintype.ofFinite V
  dsimp only
  let H := TwoColorIncidenceGraph G phi alpha beta
  let C := TwoColorComponent G phi alpha beta z
  let phi' := TwoColorComponentSwap G phi alpha beta z
  have vertex_of_edge {v : V} {e : E} (heC : Sum.inr e ∈ C)
      (hve : Incident G v e)
      (hecolor : phi e = some alpha ∨ phi e = some beta) :
      Sum.inl v ∈ C := by
    change H.connectedComponentMk (Sum.inr e) = H.connectedComponentMk z at heC
    change H.connectedComponentMk (Sum.inl v) = H.connectedComponentMk z
    have hadj : H.Adj (Sum.inl v) (Sum.inr e) := by
      simpa [H, TwoColorIncidenceGraph] using And.intro hve hecolor
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans heC
  have edge_of_vertex {v : V} {e : E} (hvC : Sum.inl v ∈ C)
      (hve : Incident G v e)
      (hecolor : phi e = some alpha ∨ phi e = some beta) :
      Sum.inr e ∈ C := by
    change H.connectedComponentMk (Sum.inl v) = H.connectedComponentMk z at hvC
    change H.connectedComponentMk (Sum.inr e) = H.connectedComponentMk z
    have hadj : H.Adj (Sum.inr e) (Sum.inl v) := by
      simpa [H, TwoColorIncidenceGraph] using And.intro hve hecolor
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hvC
  have fixed_outside_vertex {v : V} (hvC : Sum.inl v ∉ C) {e : E}
      (hve : Incident G v e) : phi' e = phi e := by
    by_cases heC : Sum.inr e ∈ C
    · by_cases hea : phi e = some alpha
      · exact False.elim (hvC (vertex_of_edge heC hve (Or.inl hea)))
      · by_cases heb : phi e = some beta
        · exact False.elim (hvC (vertex_of_edge heC hve (Or.inr heb)))
        · simp [phi', TwoColorComponentSwap, C, heC, hea, heb]
    · simp [phi', TwoColorComponentSwap, C, heC]
  have unaffected_value (e : E) (c : Fin k) (hca : c ≠ alpha) (hcb : c ≠ beta) :
      phi' e = some c ↔ phi e = some c := by
    by_cases heC : Sum.inr e ∈ C
    · by_cases hea : phi e = some alpha
      · simp [phi', TwoColorComponentSwap, C, heC, hea, hca.symm, hcb.symm]
      · by_cases heb : phi e = some beta
        · simp [phi', TwoColorComponentSwap, C, heC, heb, hne.symm,
            hca.symm, hcb.symm]
        · simp [phi', TwoColorComponentSwap, C, heC, hea, heb]
    · simp [phi', TwoColorComponentSwap, C, heC]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hvC
    apply Finset.ext
    intro c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    constructor
    · intro hc hold
      rcases hold with ⟨e, hve, hec⟩
      exact hc ⟨e, hve, (fixed_outside_vertex hvC hve).trans hec⟩
    · intro hc hnew
      rcases hnew with ⟨e, hve, hec⟩
      exact hc ⟨e, hve, (fixed_outside_vertex hvC hve).symm.trans hec⟩
  · intro v hvC haMissing
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hbPresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hbPresent
    rcases hbPresent with ⟨e, hve, hnew⟩
    by_cases heC : Sum.inr e ∈ C
    · have hold : phi e = some alpha := by
        by_cases hea : phi e = some alpha
        · exact hea
        · by_cases heb : phi e = some beta
          · have hba : beta = alpha := by
              simpa [phi', TwoColorComponentSwap, C, heC, hea, heb, hne] using hnew
            exact False.elim (hne hba.symm)
          · have : phi e = some beta := by
              simp [TwoColorComponentSwap, C, heC, hea, heb] at hnew
            exact False.elim (heb this)
      have haNotPresent : alpha ∉ PresentColors G phi v := by
        simpa [MissingColors] using haMissing
      exact haNotPresent
          (by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨e, hve, hold⟩)
    · have hold : phi e = some beta := by
        simpa [phi', TwoColorComponentSwap, C, heC] using hnew
      exact heC (edge_of_vertex hvC hve (Or.inr hold))
  · intro v hvC hbMissing
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro haPresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at haPresent
    rcases haPresent with ⟨e, hve, hnew⟩
    by_cases heC : Sum.inr e ∈ C
    · have hold : phi e = some beta := by
        by_cases hea : phi e = some alpha
        · have hba : beta = alpha := by
            simpa [phi', TwoColorComponentSwap, C, heC, hea, hne] using hnew
          exact False.elim (hne hba.symm)
        · by_cases heb : phi e = some beta
          · exact heb
          · have : phi e = some alpha := by
              simp [TwoColorComponentSwap, C, heC, hea, heb] at hnew
            exact False.elim (hea this)
      have hbNotPresent : beta ∉ PresentColors G phi v := by
        simpa [MissingColors] using hbMissing
      exact hbNotPresent
          (by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨e, hve, hold⟩)
    · have hold : phi e = some alpha := by
        simpa [phi', TwoColorComponentSwap, C, heC] using hnew
      exact heC (edge_of_vertex hvC hve (Or.inl hold))
  · intro v c hca hcb
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    constructor
    · intro hc hold
      rcases hold with ⟨e, hve, hec⟩
      exact hc ⟨e, hve, (unaffected_value e c hca hcb).mpr hec⟩
    · intro hc hnew
      rcases hnew with ⟨e, hve, hec⟩
      exact hc ⟨e, hve, (unaffected_value e c hca hcb).mp hec⟩

end GoldbergSeymour

end
