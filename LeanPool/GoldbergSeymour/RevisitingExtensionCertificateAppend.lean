/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificate
public import LeanPool.GoldbergSeymour.TashkinovSeriesDataAppend

/-!
# Revisiting Extension Certificate Append

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem RevisitingExtensionCertificateAppend {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (data : TashkinovSeriesData G k rounds e0)
    (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k))
    (i : Fin (rounds + 1)) : let appended :=
      (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma)
    (∀ cert : RevisitingExtensionCertificate appended i.castSucc,
      ∃ oldCert : RevisitingExtensionCertificate data i,
        oldCert.gamma = cert.gamma ∧ oldCert.delta = cert.delta ∧
        oldCert.edge = cert.edge ∧
        oldCert.insideEndpoint = cert.insideEndpoint ∧
        oldCert.outsideEndpoint = cert.outsideEndpoint) ∧
    (∀ cert : RevisitingExtensionCertificate data i,
      ∃ newCert : RevisitingExtensionCertificate appended i.castSucc,
        newCert.gamma = cert.gamma ∧ newCert.delta = cert.delta ∧
        newCert.edge = cert.edge ∧
        newCert.insideEndpoint = cert.insideEndpoint ∧
        newCert.outsideEndpoint = cert.outsideEndpoint) := by
  let appended := TashkinovSeriesDataAppend data newTree newColoring
    newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
    newDelta newGamma
  constructor
  · intro cert
    let oldEarlier : Fin (rounds + 1) :=
      ⟨cert.earlier.val, lt_of_le_of_lt cert.earlierAtMost i.isLt⟩
    have earlierEq : cert.earlier = oldEarlier.castSucc := by ext; rfl
    let Package (phi : PartialEdgeColoring E k)
        (earlierTree currentTree : TreeSequence G e0) : Prop :=
      ∃ cycle : TwoColorCycle G phi cert.gamma cert.delta,
        (∃ v ∈ TreeSequenceVertexSet earlierTree,
          Sum.inl v ∈ cycle.walk.support) ∧
        (∃ u ∉ TreeSequenceVertexSet currentTree,
          Sum.inl u ∈ cycle.walk.support) ∧
        Sum.inr cert.edge ∈ cycle.walk.support ∧
        cert.edge ∈ BoundaryEdges G (TreeSequenceVertexSet currentTree) ∧
        cert.insideEndpoint ∈ TreeSequenceVertexSet currentTree ∧
        cert.outsideEndpoint ∉ TreeSequenceVertexSet currentTree ∧
        cert.returnVertex ∈ TreeSequenceVertexSet earlierTree ∧
        ∃ returnPath : (TwoColorIncidenceGraph G phi cert.gamma cert.delta).Walk
            (Sum.inr cert.edge) (Sum.inl cert.returnVertex),
          returnPath.IsPath ∧
          (∀ z ∈ returnPath.support, z ∈ cycle.walk.support) ∧
          (∀ v, Sum.inl v ∈ returnPath.support →
            v ∈ TreeSequenceVertexSet currentTree)
    have newPackage : Package (appended.coloring i.castSucc)
        (appended.tree cert.earlier.castSucc)
        (appended.tree i.castSucc.succ) := by
      exact ⟨cert.cycle, cert.meetsEarlier, cert.leavesCurrent,
        cert.edgeOnCycle, cert.edgeBoundary, cert.insideInCurrent,
        cert.outsideNotCurrent, cert.returnInEarlier, cert.returnPath,
        cert.returnPathIsPath, cert.returnPathOnCycle, cert.returnPathInternal⟩
    have colorEq : appended.coloring i.castSucc = data.coloring i := by
      simp [appended, TashkinovSeriesDataAppend]
    have earlierTreeEq : appended.tree cert.earlier.castSucc =
        data.tree oldEarlier.castSucc := by
      simp [appended, TashkinovSeriesDataAppend, earlierEq]
    have currentIndexEq : i.castSucc.succ = i.succ.castSucc := by ext; rfl
    have currentTreeEq : appended.tree i.castSucc.succ = data.tree i.succ := by
      calc
        appended.tree i.castSucc.succ = appended.tree i.succ.castSucc :=
          congrArg appended.tree currentIndexEq
        _ = data.tree i.succ := by
          simp only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc]
    have oldPackage : Package (data.coloring i)
        (data.tree oldEarlier.castSucc) (data.tree i.succ) := by
      rw [← colorEq, ← earlierTreeEq, ← currentTreeEq]
      exact newPackage
    rcases oldPackage with ⟨cycle, meetsEarlier, leavesCurrent, edgeOnCycle,
      edgeBoundary, insideInCurrent, outsideNotCurrent, returnInEarlier,
      returnPath, returnPathIsPath, returnPathOnCycle, returnPathInternal⟩
    refine ⟨{
      earlier := oldEarlier
      earlierPositive := cert.earlierPositive
      earlierAtMost := cert.earlierAtMost
      earlierPE := ?_
      interveningRevisiting := ?_
      gamma := cert.gamma
      delta := cert.delta
      earlierGamma := ?_
      earlierDelta := ?_
      cycle := cycle
      meetsEarlier := meetsEarlier
      leavesCurrent := leavesCurrent
      edge := cert.edge
      edgeOnCycle := edgeOnCycle
      edgeBoundary := edgeBoundary
      insideEndpoint := cert.insideEndpoint
      outsideEndpoint := cert.outsideEndpoint
      insideInCurrent := insideInCurrent
      outsideNotCurrent := outsideNotCurrent
      edgeEnds := cert.edgeEnds
      returnVertex := cert.returnVertex
      returnInEarlier := returnInEarlier
      returnPath := returnPath
      returnPathIsPath := returnPathIsPath
      returnPathOnCycle := returnPathOnCycle
      returnPathInternal := returnPathInternal
    }, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [appended, TashkinovSeriesDataAppend, earlierEq] using cert.earlierPE
    · intro j hjpos hjafter hjle
      simpa [appended, TashkinovSeriesDataAppend] using
        cert.interveningRevisiting j.castSucc hjpos hjafter hjle
    · simpa [appended, TashkinovSeriesDataAppend, earlierEq] using cert.earlierGamma
    · simpa [appended, TashkinovSeriesDataAppend, earlierEq] using cert.earlierDelta
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · intro cert
    let Package (phi : PartialEdgeColoring E k)
        (earlierTree currentTree : TreeSequence G e0) : Prop :=
      ∃ cycle : TwoColorCycle G phi cert.gamma cert.delta,
        (∃ v ∈ TreeSequenceVertexSet earlierTree,
          Sum.inl v ∈ cycle.walk.support) ∧
        (∃ u ∉ TreeSequenceVertexSet currentTree,
          Sum.inl u ∈ cycle.walk.support) ∧
        Sum.inr cert.edge ∈ cycle.walk.support ∧
        cert.edge ∈ BoundaryEdges G (TreeSequenceVertexSet currentTree) ∧
        cert.insideEndpoint ∈ TreeSequenceVertexSet currentTree ∧
        cert.outsideEndpoint ∉ TreeSequenceVertexSet currentTree ∧
        cert.returnVertex ∈ TreeSequenceVertexSet earlierTree ∧
        ∃ returnPath : (TwoColorIncidenceGraph G phi cert.gamma cert.delta).Walk
            (Sum.inr cert.edge) (Sum.inl cert.returnVertex),
          returnPath.IsPath ∧
          (∀ z ∈ returnPath.support, z ∈ cycle.walk.support) ∧
          (∀ v, Sum.inl v ∈ returnPath.support →
            v ∈ TreeSequenceVertexSet currentTree)
    have oldPackage : Package (data.coloring i)
        (data.tree cert.earlier.castSucc) (data.tree i.succ) := by
      exact ⟨cert.cycle, cert.meetsEarlier, cert.leavesCurrent,
        cert.edgeOnCycle, cert.edgeBoundary, cert.insideInCurrent,
        cert.outsideNotCurrent, cert.returnInEarlier, cert.returnPath,
        cert.returnPathIsPath, cert.returnPathOnCycle, cert.returnPathInternal⟩
    have colorEq : appended.coloring i.castSucc = data.coloring i := by
      simp [appended, TashkinovSeriesDataAppend]
    have earlierTreeEq : appended.tree cert.earlier.castSucc.castSucc =
        data.tree cert.earlier.castSucc := by
      simp [appended, TashkinovSeriesDataAppend]
    have currentIndexEq : i.castSucc.succ = i.succ.castSucc := by ext; rfl
    have currentTreeEq : appended.tree i.castSucc.succ = data.tree i.succ := by
      calc
        appended.tree i.castSucc.succ = appended.tree i.succ.castSucc :=
          congrArg appended.tree currentIndexEq
        _ = data.tree i.succ := by
          simp only [appended, TashkinovSeriesDataAppend,
            Fin.lastCases_castSucc]
    have newPackage : Package (appended.coloring i.castSucc)
        (appended.tree cert.earlier.castSucc.castSucc)
        (appended.tree i.castSucc.succ) := by
      rw [colorEq, earlierTreeEq, currentTreeEq]
      exact oldPackage
    rcases newPackage with ⟨cycle, meetsEarlier, leavesCurrent, edgeOnCycle,
      edgeBoundary, insideInCurrent, outsideNotCurrent, returnInEarlier,
      returnPath, returnPathIsPath, returnPathOnCycle, returnPathInternal⟩
    refine ⟨{
      earlier := cert.earlier.castSucc
      earlierPositive := cert.earlierPositive
      earlierAtMost := cert.earlierAtMost
      earlierPE := ?_
      interveningRevisiting := ?_
      gamma := cert.gamma
      delta := cert.delta
      earlierGamma := ?_
      earlierDelta := ?_
      cycle := cycle
      meetsEarlier := meetsEarlier
      leavesCurrent := leavesCurrent
      edge := cert.edge
      edgeOnCycle := edgeOnCycle
      edgeBoundary := edgeBoundary
      insideEndpoint := cert.insideEndpoint
      outsideEndpoint := cert.outsideEndpoint
      insideInCurrent := insideInCurrent
      outsideNotCurrent := outsideNotCurrent
      edgeEnds := cert.edgeEnds
      returnVertex := cert.returnVertex
      returnInEarlier := returnInEarlier
      returnPath := returnPath
      returnPathIsPath := returnPathIsPath
      returnPathOnCycle := returnPathOnCycle
      returnPathInternal := returnPathInternal
    }, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [appended, TashkinovSeriesDataAppend] using cert.earlierPE
    · intro j hjpos hjafter hjle
      let oldJ : Fin (rounds + 1) := ⟨j.val, lt_of_le_of_lt hjle i.isLt⟩
      have jEq : j = oldJ.castSucc := by ext; rfl
      simpa [appended, TashkinovSeriesDataAppend, jEq] using
        cert.interveningRevisiting oldJ hjpos hjafter hjle
    · simpa [appended, TashkinovSeriesDataAppend] using cert.earlierGamma
    · simpa [appended, TashkinovSeriesDataAppend] using cert.earlierDelta
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

end GoldbergSeymour

end
