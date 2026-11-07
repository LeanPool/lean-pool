/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesDataPrefix
public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificate

/-!
# Revisiting certificates and series prefixes

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- A prefix cannot introduce a revisiting certificate absent from the original series data. -/
theorem TashkinovSeriesDataPrefix.noRevisiting {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (data : TashkinovSeriesData G k rounds e0) (m : ℕ) (hm : m ≤ rounds) (idx : Fin rounds)
    (noRevisiting : ¬Nonempty (RevisitingExtensionCertificate data idx.castSucc))
    (hidx : idx.val < m) :
    let idx' : Fin m := ⟨idx.val, hidx⟩;
    ¬Nonempty (RevisitingExtensionCertificate (TashkinovSeriesDataPrefix m hm data) idx'.castSucc)
    := by
  classical
  intro idx'
  have hprev : (TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc =
      data.coloring idx.castSucc := rfl
  have htreeCurrent : (TashkinovSeriesDataPrefix m hm data).tree idx'.castSucc.succ =
      data.tree idx.castSucc.succ := rfl
  rintro ⟨r⟩
  apply noRevisiting
  let earlier' : Fin (rounds + 1) := Fin.castLE (by omega) r.earlier
  have hkindEarlier : (TashkinovSeriesDataPrefix m hm data).kind
      r.earlier = data.kind earlier' := by rfl
  have hgammaEarlier : (TashkinovSeriesDataPrefix m hm data).gamma
      r.earlier = data.gamma earlier' := by rfl
  have hdeltaEarlier : (TashkinovSeriesDataPrefix m hm data).delta
      r.earlier = data.delta earlier' := by rfl
  have htreeEarlier : (TashkinovSeriesDataPrefix m hm data).tree
      r.earlier.castSucc = data.tree earlier'.castSucc := by rfl
  let cycle' : TwoColorCycle G (data.coloring idx.castSucc)
      r.gamma r.delta := {
    base := r.cycle.base
    walk := @Eq.ndrec (PartialEdgeColoring E k)
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
      (fun phi => (TwoColorIncidenceGraph G phi r.gamma r.delta).Walk
        r.cycle.base r.cycle.base)
      r.cycle.walk (data.coloring idx.castSucc) hprev
    isCycle := by
      dsimp
      cases hprev
      exact r.cycle.isCycle
  }
  let returnPath' : (TwoColorIncidenceGraph G (data.coloring idx.castSucc)
      r.gamma r.delta).Walk (Sum.inr r.edge) (Sum.inl r.returnVertex) :=
    @Eq.ndrec (PartialEdgeColoring E k)
      ((TashkinovSeriesDataPrefix m hm data).coloring idx'.castSucc)
      (fun phi => (TwoColorIncidenceGraph G phi r.gamma r.delta).Walk
        (Sum.inr r.edge) (Sum.inl r.returnVertex))
      r.returnPath (data.coloring idx.castSucc) hprev
  refine ⟨{
    earlier := earlier'
    earlierPositive := by simpa [earlier'] using r.earlierPositive
    earlierAtMost := by simpa [earlier', idx'] using r.earlierAtMost
    earlierPE := by
      simpa [hkindEarlier] using r.earlierPE
    interveningRevisiting := ?_
    gamma := r.gamma
    delta := r.delta
    earlierGamma := by
      simpa [hgammaEarlier] using r.earlierGamma
    earlierDelta := by
      simpa [hdeltaEarlier] using r.earlierDelta
    cycle := cycle'
    meetsEarlier := by
      rcases r.meetsEarlier with ⟨v, hv, hc⟩
      refine ⟨v, ?_, ?_⟩
      · rwa [htreeEarlier] at hv
      · dsimp [cycle']
        cases hprev
        exact hc
    leavesCurrent := by
      rcases r.leavesCurrent with ⟨v, hv, hc⟩
      refine ⟨v, ?_, ?_⟩
      · rwa [htreeCurrent] at hv
      · dsimp [cycle']
        cases hprev
        exact hc
    edge := r.edge
    edgeOnCycle := by
      dsimp [cycle']
      cases hprev
      exact r.edgeOnCycle
    edgeBoundary := by
      simpa only [htreeCurrent] using r.edgeBoundary
    insideEndpoint := r.insideEndpoint
    outsideEndpoint := r.outsideEndpoint
    insideInCurrent := by
      simpa only [htreeCurrent] using r.insideInCurrent
    outsideNotCurrent := by
      simpa only [htreeCurrent] using r.outsideNotCurrent
    edgeEnds := r.edgeEnds
    returnVertex := r.returnVertex
    returnInEarlier := by
      simpa [htreeEarlier] using r.returnInEarlier
    returnPath := returnPath'
    returnPathIsPath := by
      dsimp [returnPath']
      cases hprev
      exact r.returnPathIsPath
    returnPathOnCycle := by
      dsimp [returnPath', cycle']
      cases hprev
      exact r.returnPathOnCycle
    returnPathInternal := by
      intro v hv
      have hv' : Sum.inl v ∈ r.returnPath.support := by
        dsimp [returnPath'] at hv
        cases hprev
        exact hv
      simpa only [htreeCurrent] using r.returnPathInternal v hv'
  }⟩
  intro j hjpos hjafter hjatMost
  have hjle : j.val ≤ idx.val := by
    simpa [idx'] using hjatMost
  have hjm : j.val < m + 1 := by omega
  let j' : Fin (m + 1) := ⟨j.val, hjm⟩
  have hstep := r.interveningRevisiting j' (by simpa [j'] using hjpos)
    (by simpa [j', earlier'] using hjafter)
    (by simpa [j', idx'] using hjatMost)
  have hkindJ : (TashkinovSeriesDataPrefix m hm data).kind j' =
      data.kind j := by rfl
  simpa [hkindJ] using hstep

end GoldbergSeymour

end
