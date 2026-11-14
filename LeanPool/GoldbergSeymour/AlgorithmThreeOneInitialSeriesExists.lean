/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GlobalMaximumTripleExists
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovTreeFromLengthOnePrefix

/-!
# Algorithm Three One Initial Series Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem AlgorithmThreeOneInitialSeriesExists
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 <= k) :
    exists (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (series : TashkinovSeries G k 0 e0 phi),
      GlobalMaximumTriple G k e0 phi T ∧
      series.data.tree 0 = TreeSequencePrefix T 1 (by omega) T.positive ∧
      series.data.tree 1 = T ∧
      series.data.coloring 0 = phi ∧
      series.data.stored 0 = ∅ ∧
      series.data.connectingEdges 0 = ∅ ∧
      series.data.kind 0 = none ∧
      series.data.chosenVertex 0 = none ∧
      series.data.outsideVertex 0 = none ∧
      series.data.delta 0 = none ∧
      series.data.gamma 0 = none ∧
      (TreeSequenceVertexSet (series.data.tree 1)).card = TashkinovOrder G ∧
      3 <= (TreeSequenceVertexSet (series.data.tree 1)).card ∧
      Odd (TreeSequenceVertexSet (series.data.tree 1)).card ∧
      ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (series.data.tree 1)) ∧
      ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet (series.data.tree 1)) := by
  classical
  obtain ⟨e0, phi, T, hglobal⟩ :=
    GlobalMaximumTripleExists G k hcritical hindex hdegree
  let seed := TreeSequencePrefix T 1 (by omega) T.positive
  have hroute : TashkinovAugmentationSequence phi seed T := by
    exact TashkinovTreeFromLengthOnePrefix phi T hglobal.2.1
  have hfacts := ScheideGlobalMaximumOrder G k e0 phi T hglobal
  let data : TashkinovSeriesData G k 0 e0 := {
    tree := Fin.cases seed (fun _ => T)
    coloring := fun _ => phi
    stored := fun _ => ∅
    connectingEdges := fun _ => ∅
    kind := fun _ => none
    chosenVertex := fun _ => none
    outsideVertex := fun _ => none
    delta := fun _ => none
    gamma := fun _ => none }
  have dataTreeZero : data.tree 0 = seed := by
    rfl
  have dataTreeOne : data.tree 1 = T := by
    rfl
  let series : TashkinovSeries G k 0 e0 phi := {
    data := data
    certified := by
      intro i
      have hi : i = 0 := by
        apply Fin.ext
        omega
      subst i
      apply TashkinovSeriesStep.initial hglobal.1
      · simp [data, seed, TreeSequencePrefix]
      · simp [data]
      · simp [data]
      · simp [data]
      · simp [data]
      · simp [data]
      · simp [data]
      · simp [data]
      · simp [data]
      · rw [dataTreeZero, dataTreeOne]
        exact ⟨hroute, hfacts.2.2.2.2⟩ }
  have seriesTreeOne : series.data.tree 1 = T := by
    simpa [series] using dataTreeOne
  refine ⟨e0, phi, T, series, hglobal, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [series, seed] using dataTreeZero
  · simpa [series] using dataTreeOne
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [seriesTreeOne]
    exact hfacts.1.symm
  · rw [seriesTreeOne]
    exact hfacts.2.1
  · rw [seriesTreeOne]
    exact hfacts.2.2.1
  · rw [seriesTreeOne]
    exact hfacts.2.2.2.1
  · rw [seriesTreeOne]
    exact hfacts.2.2.2.2

end GoldbergSeymour

end
