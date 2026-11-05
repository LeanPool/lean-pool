/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Present Colors Under Component Swaps

Shared facts extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 and generalized during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A component swap preserves every present color other than its two swap colors. -/
theorem TwoColorComponentSwapPreservesOther {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k}
    {v : V} {alpha beta c : Fin k} {z : Sum V E}
    (hc : c ∈ PresentColors G phi v) (hca : c ≠ alpha) (hcb : c ≠ beta) :
    c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v := by
  classical
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  rcases hc with ⟨edge, incident, colored⟩
  refine ⟨edge, incident, ?_⟩
  by_cases member : Sum.inr edge ∈ TwoColorComponent G phi alpha beta z
  · simp [TwoColorComponentSwap, member, colored, hca, hcb]
  · simpa [TwoColorComponentSwap, member] using colored

/-- If both swap colors occur at a vertex, every present color survives the component swap. -/
theorem TwoColorComponentSwapPreservesPresent {V E : Type*} [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k}
    {v : V} {alpha beta : Fin k} {z : Sum V E}
    (halpha : alpha ∈ PresentColors G phi v) (hbeta : beta ∈ PresentColors G phi v)
    (c : Fin k) (hc : c ∈ PresentColors G phi v) :
    c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v := by
  classical
  by_cases hca : c = alpha
  · subst c
    by_cases hvK : Sum.inl v ∈ TwoColorComponent G phi alpha beta z
    · obtain ⟨e, hev, heColor⟩ := by
        simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] using hbeta
      have heK : Sum.inr e ∈ TwoColorComponent G phi alpha beta z := by
        let H := TwoColorIncidenceGraph G phi alpha beta
        have hadj : H.Adj (Sum.inl v) (Sum.inr e) := by
          simpa [H, TwoColorIncidenceGraph] using
            And.intro hev (Or.inr heColor)
        change H.connectedComponentMk (Sum.inr e) = H.connectedComponentMk z
        change H.connectedComponentMk (Sum.inl v) = H.connectedComponentMk z
          at hvK
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hadj).symm.trans hvK
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨e, hev, by
        simp [TwoColorComponentSwap, heK, heColor]⟩
    · obtain ⟨e, hev, heColor⟩ := by
        simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and] using halpha
      have heK : Sum.inr e ∉ TwoColorComponent G phi alpha beta z := by
        intro heK
        apply hvK
        let H := TwoColorIncidenceGraph G phi alpha beta
        have hadj : H.Adj (Sum.inl v) (Sum.inr e) := by
          simpa [H, TwoColorIncidenceGraph] using
            And.intro hev (Or.inl heColor)
        change H.connectedComponentMk (Sum.inr e) = H.connectedComponentMk z
          at heK
        change H.connectedComponentMk (Sum.inl v) = H.connectedComponentMk z
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hadj).trans heK
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨e, hev, by
        simpa [TwoColorComponentSwap, heK] using heColor⟩
  · by_cases hcb : c = beta
    · subst c
      by_cases hvK : Sum.inl v ∈ TwoColorComponent G phi alpha beta z
      · obtain ⟨e, hev, heColor⟩ := by
          simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and] using halpha
        have heK : Sum.inr e ∈ TwoColorComponent G phi alpha beta z := by
          let H := TwoColorIncidenceGraph G phi alpha beta
          have hadj : H.Adj (Sum.inl v) (Sum.inr e) := by
            simpa [H, TwoColorIncidenceGraph] using
              And.intro hev (Or.inl heColor)
          change H.connectedComponentMk (Sum.inr e) = H.connectedComponentMk z
          change H.connectedComponentMk (Sum.inl v) = H.connectedComponentMk z
            at hvK
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hadj).symm.trans hvK
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨e, hev, by
          simp [TwoColorComponentSwap, heK, heColor]⟩
      · obtain ⟨e, hev, heColor⟩ := by
          simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and] using hbeta
        have heK : Sum.inr e ∉ TwoColorComponent G phi alpha beta z := by
          intro heK
          apply hvK
          let H := TwoColorIncidenceGraph G phi alpha beta
          have hadj : H.Adj (Sum.inl v) (Sum.inr e) := by
            simpa [H, TwoColorIncidenceGraph] using
              And.intro hev (Or.inr heColor)
          change H.connectedComponentMk (Sum.inr e) = H.connectedComponentMk z
            at heK
          change H.connectedComponentMk (Sum.inl v) = H.connectedComponentMk z
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hadj).trans heK
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨e, hev, by
          simpa [TwoColorComponentSwap, heK] using heColor⟩
    · exact TwoColorComponentSwapPreservesOther hc hca hcb


end GoldbergSeymour

end
