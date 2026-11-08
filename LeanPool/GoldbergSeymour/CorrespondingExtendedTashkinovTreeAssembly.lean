/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree
public import LeanPool.GoldbergSeymour.TashkinovSeriesAppend
public import LeanPool.GoldbergSeymour.TashkinovSeriesCast
public import LeanPool.GoldbergSeymour.TashkinovSeriesStability

/-!+# Assembling corresponding extended trees

General structural facts extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input replacementInput generating sigma : PartialEdgeColoring E k}
    {tree replacementTree finalTree : TreeSequence G e0}

/-- A certified series with matching ladder data and stability presents a corresponding tree. -/
def CorrespondingExtendedTashkinovTree.ofSeries
    (base : ExtendedTashkinovTree G k e0 input tree generating)
    (series : TashkinovSeries G k base.rounds e0 replacementInput)
    (above : TreeSequenceInitialSegment
      (series.data.tree (Fin.last base.rounds).castSucc) replacementTree)
    (strict : (series.data.tree (Fin.last base.rounds).castSucc).length < replacementTree.length)
    (below : TreeSequenceInitialSegment replacementTree
      (series.data.tree (Fin.last (base.rounds + 1))))
    (coloring : sigma = series.data.coloring (Fin.last base.rounds))
    (trees : ∀ index : Fin base.rounds, series.data.tree index.succ.castSucc =
      base.series.data.tree index.succ.castSucc)
    (metadata : ∀ index : Fin (base.rounds + 1),
      series.data.stored index = base.series.data.stored index ∧
      series.data.connectingEdges index = base.series.data.connectingEdges index ∧
      series.data.kind index = base.series.data.kind index)
    (stable : ∀ index : Fin base.rounds,
      StableColoring (base.series.data.tree index.succ.castSucc)
        (TashkinovStoredColors base.series.data index.succ)
        (base.series.data.coloring index.succ) (series.data.coloring index.succ)) :
    CorrespondingExtendedTashkinovTree G k e0 base sigma replacementTree where
  replacementInput := replacementInput
  replacementSeries := series
  replacementETT := {
    rounds := base.rounds
    roundsPositive := base.roundsPositive
    series := series
    abovePenultimate := above
    strictAbovePenultimate := strict
    belowFinal := below
    generatingColoring := coloring }
  rungAgreement := rfl
  seriesPresentation := HEq.rfl
  finalGeneratingColoring := coloring
  ladderTreesAgree := trees
  storedColorsAgree := fun index => (metadata index).1
  connectingEdgesAgree := fun index => (metadata index).2.1
  extensionKindsAgree := fun index => (metadata index).2.2
  replacementProper := fun index => (series.coloringProperties index).1
  replacementOneUncolored := fun index => (series.coloringProperties index).2
  replacementStable := stable

/-- Appending one certified step to a corresponding earlier extends the correspondence.

The round cast, agreement of all metadata and ladder trees, stability transport, and record
assembly are independent of the kind of extension certified by `lastStep`.
-/
theorem CorrespondingExtendedTashkinovTree.nonempty_of_append
    (base : ExtendedTashkinovTree G k e0 input tree generating)
    {prefixTree : TreeSequence G e0} {prefixGenerating prefixSigma : PartialEdgeColoring E k}
    (earlier : ExtendedTashkinovTree G k e0 input prefixTree prefixGenerating)
    (correspondence : CorrespondingExtendedTashkinovTree G k e0 earlier prefixSigma prefixTree)
    (rounds : earlier.rounds + 1 = base.rounds)
    (prefixTrees : ∀ index : Fin (earlier.rounds + 2), earlier.series.data.tree index =
      base.series.data.tree (Fin.castLE (by omega) index))
    (prefixMetadata : ∀ index : Fin (earlier.rounds + 1),
      earlier.series.data.stored index = base.series.data.stored (Fin.castLE (by omega) index) ∧
      earlier.series.data.connectingEdges index =
        base.series.data.connectingEdges (Fin.castLE (by omega) index) ∧
      earlier.series.data.kind index = base.series.data.kind (Fin.castLE (by omega) index))
    (prefixStored : ∀ index : Fin (earlier.rounds + 1),
      TashkinovStoredColors earlier.series.data index =
        TashkinovStoredColors base.series.data (Fin.castLE (by omega) index))
    (prefixColorings : ∀ index : Fin (earlier.rounds + 1), earlier.series.data.coloring index =
      base.series.data.coloring (Fin.castLE (by omega) index))
    (penultimate : correspondence.replacementSeries.data.tree (Fin.last (earlier.rounds + 1)) =
      base.series.data.tree (Fin.last base.rounds).castSucc)
    (above : TreeSequenceInitialSegment
      (base.series.data.tree (Fin.last base.rounds).castSucc) replacementTree)
    (strict : (base.series.data.tree (Fin.last base.rounds).castSucc).length <
      replacementTree.length)
    (below : TreeSequenceInitialSegment replacementTree finalTree)
    (stable : StableColoring (base.series.data.tree (Fin.last base.rounds).castSucc)
      (TashkinovStoredColors base.series.data (Fin.last base.rounds))
      (base.series.data.coloring (Fin.last base.rounds)) sigma)
    (stored : Finset (Fin k)) (edges : Finset E) (kind : Option TashkinovExtensionKind)
    (vertex outside : Option V) (delta gamma : Option (Fin k))
    (lastMetadata : stored = base.series.data.stored (Fin.last base.rounds) ∧
      edges = base.series.data.connectingEdges (Fin.last base.rounds) ∧
      kind = base.series.data.kind (Fin.last base.rounds))
    (lastStep : TashkinovSeriesStep G k (earlier.rounds + 1) e0 correspondence.replacementInput
      (TashkinovSeriesDataAppend correspondence.replacementSeries.data finalTree sigma
        stored edges kind vertex outside delta gamma) (Fin.last (earlier.rounds + 1))) :
    Nonempty (CorrespondingExtendedTashkinovTree G k e0 base sigma replacementTree) := by
  obtain ⟨extended, dataEqual⟩ := TashkinovSeriesAppend G k earlier.rounds e0
    correspondence.replacementInput correspondence.replacementSeries finalTree sigma
    stored edges kind vertex outside delta gamma lastStep
  let appended := TashkinovSeriesDataAppend correspondence.replacementSeries.data finalTree sigma
    stored edges kind vertex outside delta gamma
  let series := extended.castRounds rounds
  have castData : series.data = appended.castRounds rounds := by
    rw [TashkinovSeries.castRounds_data, dataEqual]
  have lastTree : series.data.tree (Fin.last (base.rounds + 1)) = finalTree := by
    rw [TashkinovSeries.castRounds_finalTree, dataEqual]
    simp only [TashkinovSeriesDataAppend, Fin.lastCases_last]
  have lastColor : series.data.coloring (Fin.last base.rounds) = sigma := by
    rw [TashkinovSeries.castRounds_finalColoring, dataEqual]
    simp only [TashkinovSeriesDataAppend, Fin.lastCases_last]
  have penultimateTree : series.data.tree (Fin.last base.rounds).castSucc =
      base.series.data.tree (Fin.last base.rounds).castSucc := by
    rw [TashkinovSeries.castRounds_penultimateTree, dataEqual]
    simpa only [TashkinovSeriesDataAppend, Fin.lastCases_castSucc] using penultimate
  have metadata : ∀ index : Fin (base.rounds + 1),
      series.data.stored index = base.series.data.stored index ∧
      series.data.connectingEdges index = base.series.data.connectingEdges index ∧
      series.data.kind index = base.series.data.kind index := by
    simp only [castData]
    apply TashkinovSeriesData.castMetadataAgreement base.series.data appended rounds
    · intro index
      simp only [appended, TashkinovSeriesDataAppend, Fin.lastCases_castSucc]
      exact ⟨(correspondence.storedColorsAgree index).trans (prefixMetadata index).1,
        (correspondence.connectingEdgesAgree index).trans (prefixMetadata index).2.1,
        (correspondence.extensionKindsAgree index).trans (prefixMetadata index).2.2⟩
    · simpa only [appended, TashkinovSeriesDataAppend, Fin.lastCases_last] using lastMetadata
  have trees : ∀ index : Fin base.rounds, series.data.tree index.succ.castSucc =
      base.series.data.tree index.succ.castSucc := by
    simp only [castData]
    apply TashkinovSeriesData.castTreeAgreement base.series.data appended rounds
    · intro index
      simp only [appended, TashkinovSeriesDataAppend, Fin.lastCases_castSucc]
      exact (correspondence.ladderTreesAgree index).trans (prefixTrees index.succ.castSucc)
    · simpa only [castData] using penultimateTree
  have allStable := TashkinovSeriesData.stabilityOfPrefix base.series.data series.data.coloring
    earlier.series.data correspondence.replacementSeries.data.coloring rounds prefixTrees
    prefixStored prefixColorings
    (TashkinovSeriesData.prefixColoringOfCast rounds
      correspondence.replacementSeries.data.coloring sigma series.data.coloring (by
        intro index
        rw [TashkinovSeries.castRounds_coloring, dataEqual]
        rfl))
    correspondence.replacementStable (by rw [lastColor]; exact stable)
  exact ⟨CorrespondingExtendedTashkinovTree.ofSeries base series
    (by rw [penultimateTree]; exact above) (by rw [penultimateTree]; exact strict)
    (by rw [lastTree]; exact below) lastColor.symm trees metadata allStable⟩

end GoldbergSeymour

end
