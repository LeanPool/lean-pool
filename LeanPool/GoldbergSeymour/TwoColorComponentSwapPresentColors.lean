/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MissingColors

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
  exact ⟨edge, incident, (TwoColorComponentSwap.otherColor_iff hca hcb edge).mpr colored⟩

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

/-- Swapping at a root exchanges a present color with a missing color there. -/
theorem TwoColorComponentSwapExchangesRootColors.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Fintype E] {G :
    LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k} {v : V} {alpha beta : Fin
    k}, alpha ≠ beta → beta ∈ MissingColors G phi v → alpha ∈ PresentColors G phi v → alpha ∈
    MissingColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v ∧ beta ∈
    PresentColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v := by
  classical
  intro V E _ G k phi v alpha beta hne hbeta halpha
  have hbetaNotPresent : beta ∉ PresentColors G phi v := by
    simpa [MissingColors] using hbeta
  obtain ⟨eAlpha, heAlphaIncident, heAlphaColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] using halpha
  have heAlphaComponent : Sum.inr eAlpha ∈
      TwoColorComponent G phi alpha beta (Sum.inl v) := by
    let H := TwoColorIncidenceGraph G phi alpha beta
    have hadj : H.Adj (Sum.inl v) (Sum.inr eAlpha) := by
      simpa [H, TwoColorIncidenceGraph] using
        And.intro heAlphaIncident (Or.inl heAlphaColor)
    change H.connectedComponentMk (Sum.inr eAlpha) =
      H.connectedComponentMk (Sum.inl v)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hadj).symm
  constructor
  · unfold MissingColors
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hp
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    rcases hp with ⟨e, hev, heColor⟩
    by_cases heK :
        Sum.inr e ∈ TwoColorComponent G phi alpha beta (Sum.inl v)
    · have heBeta : phi e = some beta := by
        unfold TwoColorComponentSwap at heColor
        rw [ite_eq_left heK] at heColor
        by_cases heAlpha : phi e = some alpha
        · rw [ite_eq_left heAlpha] at heColor
          exact False.elim (hne (Option.some.inj heColor).symm)
        · by_cases heBeta : phi e = some beta
          · exact heBeta
          · rw [ite_eq_right heAlpha, ite_eq_right heBeta] at heColor
            exact False.elim (heAlpha heColor)
      apply hbetaNotPresent
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨e, hev, heBeta⟩
    · have heOldAlpha : phi e = some alpha := by
        simpa [TwoColorComponentSwap, heK] using heColor
      have heAdj : (TwoColorIncidenceGraph G phi alpha beta).Adj
          (Sum.inl v) (Sum.inr e) := by
        simpa [TwoColorIncidenceGraph] using
          And.intro hev (Or.inl heOldAlpha)
      apply heK
      change (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
          (Sum.inr e) =
        (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
          (Sum.inl v)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        heAdj).symm
  · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨eAlpha, heAlphaIncident, by
      simp [TwoColorComponentSwap, heAlphaComponent, heAlphaColor]⟩

end GoldbergSeymour

end
