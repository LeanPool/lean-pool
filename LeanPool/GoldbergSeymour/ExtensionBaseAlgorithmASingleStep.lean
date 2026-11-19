/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeInterchangeableFacts

public import LeanPool.GoldbergSeymour.ETTStrongInterchangeable

public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper

public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent

/-!
# Extension Base Algorithm ASingle Step

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseAlgorithmASingleStep {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (t : Fin ett.rounds) (vt : V) (phi : PartialEdgeColoring E k)
    (gammaT deltaT : Fin k)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hSI : ETTStrongInterchangeable ett t vt phi gammaT deltaT)
    (_ : vt ∈ TreeSequenceVertexSet
      (ett.series.data.tree t.succ.castSucc))
    (hdeltaMissing : deltaT ∈ MissingColors G phi vt)
    (hgammaPresent : gammaT ∈ PresentColors G phi vt) :
    TwoColorNontrivialPathComponent G phi gammaT deltaT (Sum.inl vt) ∧
      (∀ w : V,
        w ∈ TreeSequenceVertexSet
            (ett.series.data.tree t.succ.castSucc) →
        (Sum.inl w ∈ TwoColorComponent G phi gammaT deltaT (Sum.inl vt) ↔
          w = vt)) ∧
      IsProperEdgeColoring G
        (TwoColorComponentSwap G phi gammaT deltaT (Sum.inl vt)) ∧
      IsOneEdgeUncolored
        (TwoColorComponentSwap G phi gammaT deltaT (Sum.inl vt)) e0 := by
  classical
  let H := TwoColorIncidenceGraph G phi gammaT deltaT
  let C := TwoColorComponent G phi gammaT deltaT (Sum.inl vt)
  have hne : gammaT ≠ deltaT := hSI.1
  obtain ⟨eGamma, heGammaIncident, heGammaColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      using hgammaPresent
  have heGammaAdj : H.Adj (Sum.inl vt) (Sum.inr eGamma) := by
    simpa [H, TwoColorIncidenceGraph] using
      And.intro heGammaIncident (Or.inl heGammaColor)
  have heGammaComponent : Sum.inr eGamma ∈ C := by
    change H.connectedComponentMk (Sum.inr eGamma) =
      H.connectedComponentMk (Sum.inl vt)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      heGammaAdj).symm
  have hvtComponent : Sum.inl vt ∈ C := by
    rfl
  have hvtSubsingleton : Set.Subsingleton (H.neighborSet (Sum.inl vt)) := by
    exact TwoColorIncidenceGraph.neighborSet_subsingleton_of_missing hproper (Or.inr hdeltaMissing)
  have hpath : TwoColorPathComponent G phi gammaT deltaT (Sum.inl vt) := by
    refine ⟨hne, Sum.inl vt, hvtComponent, ?_⟩
    simpa [H] using hvtSubsingleton
  have hnontrivial : TwoColorNontrivialPathComponent G phi gammaT deltaT
      (Sum.inl vt) := by
    exact ⟨hpath, eGamma, heGammaComponent⟩
  have hproperSwap : IsProperEdgeColoring G
      (TwoColorComponentSwap G phi gammaT deltaT (Sum.inl vt)) := by
    exact TwoColorComponentSwapProper G phi gammaT deltaT hne hproper
      (Sum.inl vt)
  have honeSwap : IsOneEdgeUncolored
      (TwoColorComponentSwap G phi gammaT deltaT (Sum.inl vt)) e0 := by
    unfold IsOneEdgeUncolored at hone ⊢
    constructor
    · simp [TwoColorComponentSwap, hone.1]
    · intro e he0
      obtain ⟨c, hc⟩ := hone.2 e he0
      by_cases heC : Sum.inr e ∈ C
      · by_cases heGamma' : phi e = some gammaT
        · exact ⟨deltaT, by
            simp [TwoColorComponentSwap, C, heC, heGamma']⟩
        · by_cases heDelta' : phi e = some deltaT
          · exact ⟨gammaT, by
              simp [TwoColorComponentSwap, C, heC, heDelta']⟩
          · exact ⟨c, by
              simpa [TwoColorComponentSwap, C, heC, heGamma', heDelta'] using hc⟩
      · exact ⟨c, by
          simpa [TwoColorComponentSwap, C, heC] using hc⟩
  refine ⟨hnontrivial, ?_, hproperSwap, honeSwap⟩
  intro w hwTree
  constructor
  · intro hwComponent
    by_contra hneW
    obtain ⟨hcycle, havoid, hrest⟩ :=
      hSI.2.2.2.choose_spec.2.2.2 w hwTree hneW
    have hvtInW : Sum.inl vt ∈
        TwoColorComponent G phi gammaT deltaT (Sum.inl w) := by
      change H.connectedComponentMk (Sum.inl vt) =
        H.connectedComponentMk (Sum.inl w)
      change H.connectedComponentMk (Sum.inl w) =
        H.connectedComponentMk (Sum.inl vt) at hwComponent
      exact hwComponent.symm
    exact havoid hvtInW
  · intro hwEq
    subst w
    exact hvtComponent

end GoldbergSeymour

end
