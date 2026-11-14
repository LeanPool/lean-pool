/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyBase

public import LeanPool.GoldbergSeymour.OrderedTreeUnionExists
public import LeanPool.GoldbergSeymour.TashkinovClosureExists

/-!
# Hierarchy Base Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_branch_59.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : Fin (ett.rounds + (1 : ℕ)) := n;
    ∀ (i : Fin ett.rounds), ett.series.data.kind i.succ = some TashkinovExtensionKind.SE → n =
        i.succ → Nonempty (HierarchyBase ett generating) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett n j i currentKind hj
  let Tn := ett.series.data.tree n.castSucc
  have hi : i.succ = n := by simpa [j] using hj.symm
  have htree : ett.series.data.tree i.succ.castSucc = Tn := by
    simp [Tn, hi]
  have hlen : 1 ≤ Tn.length := by
    rw [← htree]
    exact (ett.series.data.tree i.succ.castSucc).positive
  let support : Fin (Tn.length + 1) := ⟨1, by omega⟩
  refine ⟨{
    core := Tn
    closure := Tn
    supportPosition := support
    supportPositive := by dsimp [support]; omega
    terminalMissingColors := by simp [ett.generatingColoring]
    parallel := by
      dsimp [Tn, n]
      intro h
      have hh : ett.series.data.kind i.succ = some TashkinovExtensionKind.PE := by
        simpa [hi] using h
      rw [currentKind] at hh
      cases hh
    nonparallel := by
      dsimp [Tn, n]
      intro h
      rfl }⟩

private theorem helper_branch_89.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : Fin (ett.rounds + (1 : ℕ)) := n;
    ∀ (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)), ett.series.data.kind i.succ = some
        TashkinovExtensionKind.PE → ett.series.data.chosenVertex i.succ = some choice.vertex → n =
        i.succ → Nonempty (HierarchyBase ett generating) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett n j i choice currentKind currentVertex hj
  let Tn := ett.series.data.tree n.castSucc
  have hi : i.succ = n := by simpa [j] using hj.symm
  have htree : ett.series.data.tree i.succ.castSucc = Tn := by
    simp [Tn, hi]
  rcases choice.edgeDefective with ⟨alpha, alphaDefective, edgeMem⟩
  have cardLarge : 1 < (BoundaryColorEdges G choice.selected
      (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) alpha).card := by
    have hc : 2 ≤ (BoundaryColorEdges G choice.selected
        (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) alpha).card := by
      simpa [DefectiveColor] using alphaDefective
    omega
  obtain ⟨otherEdge, otherMem, otherNe⟩ :=
    Finset.exists_mem_ne cardLarge choice.edge
  have boundaryOther : ∃ w ∈ TreeSequenceVertexSet
      (ett.series.data.tree i.succ.castSucc), ∃ z ∉ TreeSequenceVertexSet
      (ett.series.data.tree i.succ.castSucc), G.ends otherEdge = s(w, z) := by
    have hm : (∃ u ∈ TreeSequenceVertexSet
        (ett.series.data.tree i.succ.castSucc), ∃ v ∉ TreeSequenceVertexSet
        (ett.series.data.tree i.succ.castSucc), G.ends otherEdge = s(u, v)) ∧
        choice.selected otherEdge = some alpha := by
      simpa [BoundaryColorEdges, BoundaryEdges] using otherMem
    exact hm.1
  obtain ⟨w, wInside, z, zOutside, otherEnds⟩ := boundaryOther
  have wDefective : DefectiveVertex G choice.selected
      (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) w := by
    refine ⟨wInside, otherEdge, ?_, ?_⟩
    · exact ⟨alpha, alphaDefective, otherMem⟩
    · unfold Incident
      rw [otherEnds]
      exact Sym2.mem_iff.mpr (Or.inl rfl)
  have orderChoice := choice.maximal choice.selected w choice.selectedProper
    choice.selectedOneUncolored choice.selectedStable wDefective
  have wne : w ≠ choice.vertex := by
    intro equal
    subst w
    have edgeIncidentOther : Incident G choice.vertex otherEdge := by
      unfold Incident
      rw [otherEnds]
      exact Sym2.mem_iff.mpr (Or.inl rfl)
    have adjacent : AdjacentEdges G choice.edge otherEdge :=
      ⟨choice.vertex, choice.edgeIncident, edgeIncidentOther⟩
    have otherColor : choice.selected otherEdge = some alpha := by
      have hm : (∃ u ∈ TreeSequenceVertexSet
          (ett.series.data.tree i.succ.castSucc), ∃ v ∉ TreeSequenceVertexSet
          (ett.series.data.tree i.succ.castSucc), G.ends otherEdge = s(u, v)) ∧
          choice.selected otherEdge = some alpha := by
        simpa [BoundaryColorEdges, BoundaryEdges] using otherMem
      exact hm.2
    have edgeAlpha : choice.selected choice.edge = some alpha := by
      have hm : (∃ u ∈ TreeSequenceVertexSet
          (ett.series.data.tree i.succ.castSucc), ∃ v ∉ TreeSequenceVertexSet
          (ett.series.data.tree i.succ.castSucc), G.ends choice.edge = s(u, v)) ∧
          choice.selected choice.edge = some alpha := by
        simpa [BoundaryColorEdges, BoundaryEdges] using edgeMem
      exact hm.2
    have alphaChoice : alpha = choice.color := by
      simpa [choice.edgeColor] using edgeAlpha.symm
    rw [alphaChoice] at otherColor
    exact (choice.selectedProper otherNe.symm adjacent choice.edgeColor)
      otherColor
  have orderStrict : TreeVertexOrder
      (ett.series.data.tree i.succ.castSucc) w choice.vertex := by
    rcases orderChoice with equal | order
    · exact (wne equal).elim
    · exact order
  rcases orderStrict with ⟨r, s, hr, hs, hrs⟩
  have supportPositive : 1 ≤ s.val := by omega
  have supportLe : s.val ≤ Tn.length := by
    have hl := congrArg TreeSequence.length htree
    omega
  have hlen : (ett.series.data.tree i.succ.castSucc).length = Tn.length :=
    congrArg TreeSequence.length htree
  let support : Fin (Tn.length + 1) :=
    Fin.cast (congrArg (fun q => q + 1) hlen) s
  have castVertexValue : ∀ (A B : TreeSequence G e0) (h : A = B)
      (x : Fin (A.length + 1)),
      (cast (congrArg (fun q => Fin (q.length + 1)) h) x).val = x.val := by
    intro A B h x
    cases h
    rfl
  have chosenAt : choice.vertex = Tn.vertex support := by
    have hv : HEq (Tn.vertex support)
        ((ett.series.data.tree i.succ.castSucc).vertex s) := by
      congr
      · exact htree.symm
      · dsimp [support]
        apply heq_of_cast_eq (congrArg (fun q => Fin (q.length + 1)) htree.symm)
        apply Fin.ext
        have hsfin : Fin.cast (congrArg (fun q => q + 1) hlen) s =
            ⟨s.val, by omega⟩ := by
          apply Fin.ext
          rfl
        rw [hsfin]
        exact castVertexValue _ _ htree.symm _
    exact hs.symm.trans (eq_of_heq hv).symm
  obtain ⟨closure, closureCert⟩ := TashkinovClosureExists generating
    (TreeSequencePrefix Tn support.val supportPositive (by omega))
  obtain ⟨core, unionCert⟩ := OrderedTreeUnionExists Tn closure
  refine ⟨{
    core := core
    closure := closure
    supportPosition := support
    supportPositive := supportPositive
    terminalMissingColors := by simp [ett.generatingColoring]
    parallel := by
      dsimp [Tn, n]
      intro h
      refine ⟨?_, ?_, unionCert⟩
      · simpa [n, hi, chosenAt] using currentVertex
      · exact closureCert
    nonparallel := by
      dsimp [Tn, n]
      intro h
      have hh : ett.series.data.kind i.succ = some TashkinovExtensionKind.PE := by
        simpa [n, hi] using currentKind
      exact (h (by simpa [n, hi] using hh)).elim }⟩

private theorem helper_branch_212.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let _ : Fin (ett.rounds + (1 : ℕ)) := n;
    ∀ (i : Fin ett.rounds), ett.series.data.kind i.succ = some TashkinovExtensionKind.RE → n =
        i.succ → Nonempty (HierarchyBase ett generating) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett n j i currentKind hj
  let Tn := ett.series.data.tree n.castSucc
  have hi : i.succ = n := by simpa [j] using hj.symm
  have htree : ett.series.data.tree i.succ.castSucc = Tn := by
    simp [Tn, hi]
  have hpos : 1 ≤ Tn.length := by
    rw [← htree]
    exact (ett.series.data.tree i.succ.castSucc).positive
  let support : Fin (Tn.length + 1) := ⟨1, by omega⟩
  refine ⟨{
    core := Tn
    closure := Tn
    supportPosition := support
    supportPositive := by dsimp [support]; omega
    terminalMissingColors := by simp [ett.generatingColoring]
    parallel := by
      dsimp [Tn, n]
      intro h
      have hh : ett.series.data.kind i.succ = some TashkinovExtensionKind.PE := by
        simpa [hi] using h
      rw [currentKind] at hh
      cases hh
    nonparallel := by
      dsimp [Tn, n]
      intro h
      rfl }⟩

theorem HierarchyBaseExists
    {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating) :
    Nonempty (HierarchyBase ett generating) := by
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  have cert := ett.series.certified n
  let j : Fin (ett.rounds + 1) := n
  generalize hj : n = j at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind
      initialVertex initialOutside initialDelta initialGamma initialClosure =>
      have hn : n = 0 := by simp [hj]
      have hne : n ≠ 0 := by
        intro h
        have hv : ett.rounds = 0 := by
          simpa [n] using congrArg Fin.val h
        have hp := ett.roundsPositive
        omega
      exact (hne hn).elim
  | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
          exact @helper_branch_59 V E inferInstance inferInstance inferInstance inferInstance G k
              e0 input T generating ett i currentKind hj
  | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable
      secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension =>
          exact @helper_branch_89 V E inferInstance inferInstance inferInstance inferInstance G k
              e0 input T generating ett i choice currentKind currentVertex hj
  | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      available currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension =>
          exact @helper_branch_212 V E inferInstance inferInstance inferInstance inferInstance G
              k e0 input T generating ett i currentKind hj
end GoldbergSeymour

end
