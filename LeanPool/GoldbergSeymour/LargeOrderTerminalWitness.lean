/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AlgorithmThreeOneInitialSeriesExists
public import LeanPool.GoldbergSeymour.AlgorithmThreeOneStepExists
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.PositiveWellDefinedness
public import LeanPool.GoldbergSeymour.CertifiedSeriesRoundsBound
public import LeanPool.GoldbergSeymour.TashkinovSeriesDataAppend
public import LeanPool.GoldbergSeymour.TashkinovSeriesFinalETTExists
public import LeanPool.GoldbergSeymour.TechnicalTheoremLarge

/-!
# Large Order Terminal Witness

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem LargeOrderTerminalWitness
    {V E : Type*} [Fintype V] [Fintype E]
     [DecidableEq E]
    (G : LooplessMultigraph V E) (k : Nat)
    (hcritical : Critical G) (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 <= k)
    (hlarge : 11 <= TashkinovOrder G) :
    exists (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V),
      IsProperEdgeColoring G phi /\ IsOneEdgeUncolored phi e0 /\
      (forall v, v ∈ G.ends e0 -> v ∈ X) /\
      ColoredVertexSetElementary G phi X /\
      ColoredVertexSetStronglyClosed G phi X := by
  classical
  have endpointsInTree : forall (e0 : E) (R : TreeSequence G e0) (v : V),
      v ∈ G.ends e0 -> v ∈ TreeSequenceVertexSet R := by
    intro e0 R v hv
    obtain ⟨i, hi⟩ := R.attaches ⟨0, R.positive⟩
    have iz : i = ⟨0, by omega⟩ := Fin.eq_zero i
    subst i
    rw [← R.first_edge] at hv
    rw [hi] at hv
    simp only [Sym2.mem_iff] at hv
    rcases hv with hv | hv
    · subst v
      simp [TreeSequenceVertexSet]
    · simp only [TreeSequenceVertexSet, Finset.mem_image]
      exact ⟨_, Finset.mem_univ _, hv.symm⟩
  obtain ⟨e0, phi, T0, initial, hglobal, htreeZero, htreeOne,
      hcolor, hstored, hedges, hkind, hchosen, houtside, hdelta, hgamma,
      hfirstMaximum, hfirstThree, hfirstOdd, hfirstElementary,
      hfirstClosed⟩ :=
    AlgorithmThreeOneInitialSeriesExists G k hcritical hindex hdegree
  have hproper : IsProperEdgeColoring G phi := hglobal.1.2.2.2.1
  have hone : IsOneEdgeUncolored phi e0 := hglobal.1.2.2.2.2
  by_cases hfirstStrong : ColoredVertexSetStronglyClosed G phi
      (TreeSequenceVertexSet (initial.data.tree 1))
  · exact ⟨e0, phi, TreeSequenceVertexSet (initial.data.tree 1), hproper,
      hone, endpointsInTree e0 (initial.data.tree 1), hfirstElementary,
      hfirstStrong⟩
  · obtain ⟨newTree, newColoring, newStored, newConnectingEdges,
        newKind, newChosenVertex, newOutsideVertex, newDelta, newGamma,
        firstPositiveSeries, hfirstAppend, hfirstStrict⟩ :=
      have lastColor : Fin.last 0 = (0 : Fin 1) := by
        ext
        rfl
      have lastTree : Fin.last (0 + 1) = (1 : Fin 2) := by
        ext
        rfl
      AlgorithmThreeOneStepExists G k 0 e0 phi initial hdegree
        (by rw [lastColor, hcolor]; exact hproper)
        (by rw [lastColor, hcolor]; exact hone)
        (by rw [lastColor, hcolor, lastTree]; exact hfirstClosed)
        (by rw [lastColor, hcolor, lastTree]; exact hfirstStrong)
    obtain ⟨rawFirstETT, hrawRounds, hrawSeries⟩ :=
      TashkinovSeriesFinalETTExists G k 1 e0 phi firstPositiveSeries (by omega)
    cases rawFirstETT with
    | mk rawRounds rawPositive rawSeries rawAbove rawStrict rawBelow rawGenerating =>
      dsimp at hrawRounds
      subst rawRounds
      have rawSeriesEq : rawSeries = firstPositiveSeries := eq_of_heq hrawSeries
      subst rawSeries
      let firstETT : ExtendedTashkinovTree G k e0 phi
          (firstPositiveSeries.data.tree (Fin.last (1 + 1)))
          (firstPositiveSeries.data.coloring (Fin.last 1)) := {
        rounds := 1
        roundsPositive := rawPositive
        series := firstPositiveSeries
        abovePenultimate := rawAbove
        strictAbovePenultimate := rawStrict
        belowFinal := rawBelow
        generatingColoring := rawGenerating }
      have hfirstMP : MaximumProperty firstETT := by
        unfold MaximumProperty
        constructor
        · change (TreeSequenceVertexSet (firstPositiveSeries.data.tree 1)).card =
            TashkinovOrder G
          rw [hfirstAppend]
          have firstIndex : (1 : Fin (1 + 2)) = (1 : Fin (0 + 2)).castSucc := by
            ext
            rfl
          rw [firstIndex]
          simpa only [TashkinovSeriesDataAppend, Fin.lastCases_castSucc] using
            hfirstMaximum
        · intro i hi hlast
          dsimp [firstETT] at hlast
          omega
      let Attainable : Nat -> Prop := fun n =>
        exists (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
          (generating : PartialEdgeColoring E k)
          (ett : ExtendedTashkinovTree G k e0 input T generating),
          ett.rounds = n /\
          T = ett.series.data.tree (Fin.last (ett.rounds + 1)) /\
          MaximumProperty ett
      let candidates := (Finset.range (Fintype.card V)).filter Attainable
      have hfirstAttainable : Attainable 1 := by
        exact ⟨phi, firstPositiveSeries.data.tree (Fin.last (1 + 1)),
          firstPositiveSeries.data.coloring (Fin.last 1), firstETT, rfl, rfl,
          hfirstMP⟩
      have hfirstBound : 1 < Fintype.card V := by
        have hb := CertifiedSeriesRoundsBound G k 1 e0 phi
          firstPositiveSeries
        omega
      have honeMem : 1 ∈ candidates := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hfirstBound,
          hfirstAttainable⟩
      have hcandidatesNonempty : candidates.Nonempty := ⟨1, honeMem⟩
      let n := candidates.max' hcandidatesNonempty
      have hnMem : n ∈ candidates := Finset.max'_mem candidates hcandidatesNonempty
      have hnAttainable : Attainable n := (Finset.mem_filter.mp hnMem).2
      obtain ⟨inputN, TN, generatingN, ettN, hroundsN, hfinalN, hMPN⟩ :=
        hnAttainable
      obtain normalized | extended :=
        PositiveWellDefinedness G k e0 inputN TN generatingN ettN
          hfinalN hMPN hdegree hlarge
      · obtain ⟨replacementInput, replacementSeries, normalizedETT,
          hnormalizedRounds, hnormalizedSeries, hnormalizedProper,
          hnormalizedOne, hnormalizedClosed, hnormalizedStrong,
          hnormalizedMP, hnormalizedTerminal⟩ := normalized
        have hnormalizedElementary : ColoredVertexSetElementary G
            (replacementSeries.data.coloring (Fin.last ettN.rounds))
            (TreeSequenceVertexSet
              (replacementSeries.data.tree (Fin.last (ettN.rounds + 1)))) := by
          exact (TechnicalTheoremLarge G k e0 replacementInput
            (replacementSeries.data.tree (Fin.last (ettN.rounds + 1)))
            (replacementSeries.data.coloring (Fin.last ettN.rounds))
            normalizedETT hnormalizedMP hdegree hlarge).1
        exact ⟨e0, replacementSeries.data.coloring (Fin.last ettN.rounds),
          TreeSequenceVertexSet
            (replacementSeries.data.tree (Fin.last (ettN.rounds + 1))),
          hnormalizedProper, hnormalizedOne,
          endpointsInTree e0
            (replacementSeries.data.tree (Fin.last (ettN.rounds + 1))),
          hnormalizedElementary, hnormalizedStrong⟩
      · obtain ⟨replacementInput, extendedSeries, extendedETT,
          hextendedRounds, hextendedSeries, hextendedProper, hextendedOne,
          hextendedClosed, hextendedMP⟩ := extended
        have hextendedFinal :
            extendedSeries.data.tree (Fin.last ((ettN.rounds + 1) + 1)) =
              extendedETT.series.data.tree
                (Fin.last (extendedETT.rounds + 1)) := by
          cases extendedETT with
          | mk extendedRounds extendedPositive extendedData extendedAbove
              extendedStrict extendedBelow extendedGenerating =>
            dsimp at hextendedRounds
            subst extendedRounds
            have extendedDataEq : extendedData = extendedSeries :=
              eq_of_heq hextendedSeries
            subst extendedData
            rfl
        have hextendedAttainable : Attainable (n + 1) := by
          refine ⟨replacementInput,
            extendedSeries.data.tree (Fin.last ((ettN.rounds + 1) + 1)),
            extendedSeries.data.coloring (Fin.last (ettN.rounds + 1)),
            extendedETT, ?_, hextendedFinal, hextendedMP⟩
          omega
        have hextendedBound : n + 1 < Fintype.card V := by
          have hb := CertifiedSeriesRoundsBound G k
            (ettN.rounds + 1) e0 replacementInput extendedSeries
          omega
        have hextendedMem : n + 1 ∈ candidates := by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hextendedBound, hextendedAttainable⟩
        have hmax := Finset.le_max' candidates (n + 1) hextendedMem
        have himpossible : n + 1 <= n := by
          simpa only [n] using hmax
        omega

end GoldbergSeymour

end
