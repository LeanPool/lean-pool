/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ETTStrongInterchangeable
public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent
public import LeanPool.GoldbergSeymour.TwoColorPathComponentNotCycle

/-!
# Extension Base Algorithm BSingle Step

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseAlgorithmBSingleStep {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (t : Fin ett.rounds) (terminalSupport : V)
    (phi : PartialEdgeColoring E k) (u : V) (alpha beta : Fin k)
    (hproper : IsProperEdgeColoring G phi)
    (hSI : ETTStrongInterchangeable ett t terminalSupport phi alpha beta)
    (hbetaMissing : beta ∈ MissingColors G phi u)
    (halphaPresent : alpha ∈ PresentColors G phi u)
    (hterminalAlphaPresent : alpha ∈ PresentColors G phi terminalSupport)
    (hterminalBetaPresent : beta ∈ PresentColors G phi terminalSupport) :
    TwoColorNontrivialPathComponent G phi alpha beta (Sum.inl u) ∧
      (∀ w : V,
        w ∈ TreeSequenceVertexSet
            (ett.series.data.tree t.succ.castSucc) →
        Sum.inl w ∈ TwoColorComponent G phi alpha beta (Sum.inl u) →
        w = terminalSupport) ∧
      (Sum.inl terminalSupport ∈
          TwoColorComponent G phi alpha beta (Sum.inl u) →
        ¬ Set.Subsingleton
          ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
            (Sum.inl terminalSupport))) := by
  classical
  let H := TwoColorIncidenceGraph G phi alpha beta
  let C := TwoColorComponent G phi alpha beta (Sum.inl u)
  have hne : alpha ≠ beta := hSI.1
  have hbetaNotPresent : beta ∉ PresentColors G phi u :=
    (Finset.mem_sdiff.mp hbetaMissing).2
  obtain ⟨eAlpha, heAlphaIncident, heAlphaColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      using halphaPresent
  have heAlphaAdj : H.Adj (Sum.inl u) (Sum.inr eAlpha) := by
    simpa [H, TwoColorIncidenceGraph] using
      And.intro heAlphaIncident (Or.inl heAlphaColor)
  have heAlphaComponent : Sum.inr eAlpha ∈ C := by
    change H.connectedComponentMk (Sum.inr eAlpha) =
      H.connectedComponentMk (Sum.inl u)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      heAlphaAdj).symm
  have huComponent : Sum.inl u ∈ C := by
    rfl
  have huSubsingleton : Set.Subsingleton (H.neighborSet (Sum.inl u)) := by
    intro x hx y hy
    cases x with
    | inl x =>
        simp [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph] at hx
    | inr e =>
        cases y with
        | inl y =>
            simp [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph] at hy
        | inr f =>
            have hxData : Incident G u e ∧
                (phi e = some alpha ∨ phi e = some beta) := by
              simpa [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph]
                using hx
            have hyData : Incident G u f ∧
                (phi f = some alpha ∨ phi f = some beta) := by
              simpa [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph]
                using hy
            have heColor : phi e = some alpha := by
              rcases hxData.2 with he | he
              · exact he
              · exact False.elim (hbetaNotPresent (by
                  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                    true_and]
                  exact ⟨e, hxData.1, he⟩))
            have hfColor : phi f = some alpha := by
              rcases hyData.2 with hf | hf
              · exact hf
              · exact False.elim (hbetaNotPresent (by
                  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
                    true_and]
                  exact ⟨f, hyData.1, hf⟩))
            congr 1
            by_contra hef
            exact (hproper hef ⟨u, hxData.1, hyData.1⟩ heColor) hfColor
  have hpath : TwoColorPathComponent G phi alpha beta (Sum.inl u) := by
    refine ⟨hne, Sum.inl u, huComponent, ?_⟩
    simpa [H] using huSubsingleton
  have hnontrivial : TwoColorNontrivialPathComponent G phi alpha beta
      (Sum.inl u) := by
    exact ⟨hpath, eAlpha, heAlphaComponent⟩
  refine ⟨hnontrivial, ?_, ?_⟩
  · intro w hwTree hwComponent
    by_contra hwne
    obtain ⟨hcycle, -, -⟩ := hSI.2.2.2.choose_spec.2.2.2 w hwTree hwne
    have huInW : Sum.inl u ∈
        TwoColorComponent G phi alpha beta (Sum.inl w) := by
      change H.connectedComponentMk (Sum.inl u) =
        H.connectedComponentMk (Sum.inl w)
      change H.connectedComponentMk (Sum.inl w) =
        H.connectedComponentMk (Sum.inl u) at hwComponent
      exact hwComponent.symm
    have hpathW : TwoColorPathComponent G phi alpha beta (Sum.inl w) := by
      refine ⟨hne, Sum.inl u, huInW, ?_⟩
      simpa [H] using huSubsingleton
    exact (TwoColorPathComponentNotCycle G phi alpha beta (Sum.inl w)
      hpathW) hcycle
  · intro hterminalComponent hsub
    obtain ⟨eAlphaN, heAlphaNIncident, heAlphaNColor⟩ := by
      simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        using hterminalAlphaPresent
    obtain ⟨eBetaN, heBetaNIncident, heBetaNColor⟩ := by
      simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        using hterminalBetaPresent
    have hedgeNe : eAlphaN ≠ eBetaN := by
      intro heq
      subst eBetaN
      exact hne (Option.some.inj (heAlphaNColor.symm.trans heBetaNColor))
    have hAlphaNeighbor : Sum.inr eAlphaN ∈
        H.neighborSet (Sum.inl terminalSupport) := by
      simpa [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph] using
        And.intro heAlphaNIncident (Or.inl heAlphaNColor)
    have hBetaNeighbor : Sum.inr eBetaN ∈
        H.neighborSet (Sum.inl terminalSupport) := by
      simpa [SimpleGraph.mem_neighborSet, H, TwoColorIncidenceGraph] using
        And.intro heBetaNIncident (Or.inr heBetaNColor)
    have hnodes := hsub hAlphaNeighbor hBetaNeighbor
    exact hedgeNe (Sum.inr.inj hnodes)

end GoldbergSeymour

end
