/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ETTStrongInterchangeable
public import LeanPool.GoldbergSeymour.EarlierPECycleFirstNonrevisitingInternal

public import LeanPool.GoldbergSeymour.ExtensionBaseActiveIndices

public import LeanPool.GoldbergSeymour.TwoColorInterchangeableDistinctComponentCycle
public import LeanPool.GoldbergSeymour.TwoColorNontrivialPathComponent

public import LeanPool.GoldbergSeymour.ParallelStepRootComponentSetup
public import LeanPool.GoldbergSeymour.StableSeriesCycleComponentTransport

/-!
# Extension Base Claim Strong Interchangeable

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseClaimStrongInterchangeable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds)
    (hqTerminal : q.val + 1 = ett.rounds)
    (hqKind : ett.series.data.kind q.succ =
      some TashkinovExtensionKind.PE)
    (_ : ett.series.data.chosenVertex q.succ = some terminalSupport)
    (hLowerInterchange : ∀ (t : Fin ett.rounds) (vt : V)
      (gamma delta : Fin k),
      t ∈ ExtensionBaseActiveIndices ett terminalSupport hterminalSupport →
      t.val < q.val →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gamma →
      ett.series.data.delta t.succ = some delta →
      TreeInterchangeable G (ett.series.data.tree t.succ.succ)
        (ett.series.data.coloring t.succ) gamma delta)
    (sigma : PartialEdgeColoring E k)
    (hsigmaProper : IsProperEdgeColoring G sigma)
    (hsigmaOne : IsOneEdgeUncolored sigma e0)
    (hsigmaStable : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.succ)
      (ett.series.data.coloring q.succ) sigma) :
    ∀ (t : Fin ett.rounds) (vt : V) (gamma delta : Fin k), t ∈ ExtensionBaseActiveIndices ett
        terminalSupport hterminalSupport → t.val < q.val → ett.series.data.chosenVertex t.succ =
        some vt → ett.series.data.gamma t.succ = some gamma → ett.series.data.delta t.succ = some
        delta → ETTStrongInterchangeable ett t vt sigma gamma delta := by
  classical
  intro t vt gamma delta htActive htq htVertex htGamma htDelta
  have htKind : ett.series.data.kind t.succ =
      some TashkinovExtensionKind.PE := by
    simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] at htActive
    exact htActive.2.1
  obtain ⟨hcolors, htProper, htSegment, hsupport, hrootPath, hrootOnly,
      hnonisolated⟩ :=
    ParallelStepRootComponentSetup ett.series t vt gamma delta
      htKind htVertex htGamma htDelta
  have hcycles :
    ∀ v : V, v ∈ TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc) → v ≠ vt →
        TwoColorComponentCycle G (ett.series.data.coloring t.succ) gamma delta (Sum.inl v) ∧
        Sum.inl vt ∉ TwoColorComponent G (ett.series.data.coloring t.succ) gamma delta (Sum.inl v)
  := by
    intro v hv hne
    have hsupportNext :=
      TreeSequenceInitialSegmentVertexSetSubset htSegment hsupport
    have hvNext := TreeSequenceInitialSegmentVertexSetSubset htSegment hv
    have hdistinct : TwoColorComponent G (ett.series.data.coloring t.succ)
        gamma delta (Sum.inl vt) ≠
        TwoColorComponent G (ett.series.data.coloring t.succ)
          gamma delta (Sum.inl v) := by
      intro heq
      apply hne
      apply (hrootOnly v hv).mp
      rw [heq]
      rfl
    have hcycle := TwoColorInterchangeableDistinctComponentCycle G
      (ett.series.data.tree t.succ.succ)
      (ett.series.data.coloring t.succ) gamma delta htProper
      (Sum.inl vt) (Sum.inl v) hrootPath
      (hLowerInterchange t vt gamma delta htActive htq htVertex htGamma htDelta)
      ⟨vt, hsupportNext, by rfl⟩ ⟨v, hvNext, by rfl⟩ hdistinct
    refine ⟨hcycle, ?_⟩
    intro hs
    apply hne
    apply (hrootOnly v hv).mp
    change (TwoColorIncidenceGraph G (ett.series.data.coloring t.succ)
        gamma delta).connectedComponentMk (Sum.inl vt) =
      (TwoColorIncidenceGraph G (ett.series.data.coloring t.succ)
        gamma delta).connectedComponentMk (Sum.inl v) at hs
    change (TwoColorIncidenceGraph G (ett.series.data.coloring t.succ)
        gamma delta).connectedComponentMk (Sum.inl v) =
      (TwoColorIncidenceGraph G (ett.series.data.coloring t.succ)
        gamma delta).connectedComponentMk (Sum.inl vt)
    exact hs.symm
  let candidates : Finset (Fin ett.rounds) := Finset.univ.filter fun p =>
    t.val < p.val ∧
      ett.series.data.kind p.succ ≠ some TashkinovExtensionKind.RE
  have qMem : q ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, htq, ?_⟩
    rw [hqKind]
    simp
  have candidatesNonempty : candidates.Nonempty := ⟨q, qMem⟩
  let epsilon : Fin ett.rounds := candidates.min' candidatesNonempty
  have epsilonMem : epsilon ∈ candidates :=
    Finset.min'_mem candidates candidatesNonempty
  have htEpsilon : t.val < epsilon.val :=
    (Finset.mem_filter.mp epsilonMem).2.1
  have hepsilonKind : ett.series.data.kind epsilon.succ ≠
      some TashkinovExtensionKind.RE :=
    (Finset.mem_filter.mp epsilonMem).2.2
  have hepsilonQ : epsilon.val ≤ q.val :=
    Finset.min'_le candidates q qMem
  have hintervening : ∀ r : Fin ett.rounds, t.val < r.val →
      r.val < epsilon.val →
      ett.series.data.kind r.succ = some TashkinovExtensionKind.RE := by
    intro r htr hre
    by_contra hrNot
    have hrMem : r ∈ candidates := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, htr, hrNot⟩
    have her : epsilon ≤ r := Finset.min'_le candidates r hrMem
    omega
  have hcontained :
    ∀ v : V, v ∈ TreeSequenceVertexSet (ett.series.data.tree t.succ.castSucc) → v ≠ vt →
    ∀ w : V, Sum.inl w ∈ TwoColorComponent G (ett.series.data.coloring t.succ) gamma delta
        (Sum.inl v) → w ∈ TreeSequenceVertexSet (ett.series.data.tree epsilon.succ.castSucc) := by
    intro v hv hne w hw
    obtain ⟨cycle, hcycleSupport⟩ := (hcycles v hv hne).1
    have htEarlier : t.succ ≠ Fin.last ett.rounds := by
      intro heq
      have hval := congrArg Fin.val heq
      simp only [Fin.val_succ, Fin.val_last] at hval
      omega
    have hqLast : q.succ = Fin.last ett.rounds := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    have hcycleMeets : ∃ x ∈ TreeSequenceVertexSet
        (ett.series.data.tree t.succ.castSucc),
        Sum.inl x ∈ cycle.walk.support := by
      refine ⟨v, hv, ?_⟩
      exact (hcycleSupport (Sum.inl v)).2 (by rfl)
    obtain ⟨p, htp, hpKind, hpBetween, -, hpInternal⟩ :=
      EarlierPECycleFirstNonrevisitingInternal G k ett.rounds e0 input
        ett.series t htEarlier gamma delta htKind htGamma htDelta cycle
        hcycleMeets (by simpa [hqLast] using hqKind)
    have hpNotRE : ett.series.data.kind p.succ ≠
        some TashkinovExtensionKind.RE := by
      intro hpRE
      rcases hpKind with hpSE | hpPE
      · rw [hpSE] at hpRE
        cases hpRE
      · rw [hpPE] at hpRE
        cases hpRE
    have hpMem : p ∈ candidates :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, htp, hpNotRE⟩
    have hepsilonLeP : epsilon ≤ p :=
      Finset.min'_le candidates p hpMem
    have hpLeEpsilon : p ≤ epsilon := by
      by_contra hnot
      have hepsLtP : epsilon.val < p.val := by omega
      exact hepsilonKind (hpBetween epsilon htEpsilon hepsLtP)
    have hpEq : p = epsilon := le_antisymm hpLeEpsilon hepsilonLeP
    subst p
    obtain ⟨node, hnodeSupport, hnodeAdj⟩ :=
      SimpleGraph.adj_of_mem_walk_support cycle.walk
        cycle.isCycle.not_nil ((hcycleSupport (Sum.inl w)).2 hw)
    cases node with
    | inl u =>
        simp [TwoColorIncidenceGraph] at hnodeAdj
    | inr f =>
        have hdata : Incident G w f ∧
            (ett.series.data.coloring t.succ f = some gamma ∨
              ett.series.data.coloring t.succ f = some delta) := by
          simpa [TwoColorIncidenceGraph] using hnodeAdj
        have hfAll :
    ∀ u, Incident G u f → u ∈ TreeSequenceVertexSet (ett.series.data.tree epsilon.succ.castSucc)
  := by
          simpa only [InternalEdges, Finset.mem_filter, Finset.mem_univ,
            true_and] using hpInternal f hnodeSupport
        exact hfAll w hdata.1
  refine ⟨hcolors, htKind, htVertex, epsilon, htEpsilon,
    hepsilonKind, hintervening, ?_⟩
  intro v hv hne
  obtain ⟨hcycle, havoid⟩ := hcycles v hv hne
  obtain ⟨hcomponent, hcycleSigma⟩ :=
    StableSeriesCycleComponentTransport ett.series t epsilon q gamma delta
      htEpsilon hepsilonQ htKind htGamma htDelta hintervening hqKind
      sigma hsigmaProper hsigmaOne hsigmaStable (Sum.inl v) hcycle
      (hcontained v hv hne)
  refine ⟨hcycleSigma, ?_, ?_⟩
  · rw [hcomponent]
    exact havoid
  · intro w hw
    apply hcontained v hv hne w
    rw [← hcomponent]
    exact hw

end GoldbergSeymour

end
