/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CombinedStableClosurePreserved

public import LeanPool.GoldbergSeymour.ParallelClosureUnionElementary
public import LeanPool.GoldbergSeymour.ParallelCommonMissingClosed

/-!
# Interchange PECommon Missing Closed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem InterchangePECommonMissingClosed_hproperGen_91.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
    LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
    TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
    e0 input T generating), 0 < ett.rounds → ett.series.data.kind (Fin.last ett.rounds) = some
    TashkinovExtensionKind.PE → let _ := Fin.last ett.rounds; generating =
    ett.series.data.coloring (Fin.last ett.rounds) → IsProperEdgeColoring G generating := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive hPE n hgen
  have hstep := ett.series.certified n
  generalize targetEq : n = target at hstep
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hn : n ≠ 0 := by simp [n]; omega
    exact (hn targetEq).elim
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    have hi : i.succ = n := by
      apply Fin.ext
      have hv := congrArg Fin.val targetEq
      simp at hv
      omega
    simpa [hgen, n, hi] using currentProper
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hlast : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by simpa [n] using hPE
    rw [targetEq, currentKind] at hlast
    contradiction
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hlast : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by simpa [n] using hPE
    rw [targetEq, currentKind] at hlast
    contradiction

private theorem InterchangePECommonMissingClosed_honeGen_131.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
    LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
    TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
    e0 input T generating), 0 < ett.rounds → ett.series.data.kind (Fin.last ett.rounds) = some
    TashkinovExtensionKind.PE → let _ := Fin.last ett.rounds; generating =
    ett.series.data.coloring (Fin.last ett.rounds) → IsOneEdgeUncolored generating e0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive hPE n hgen
  have hstep := ett.series.certified n
  generalize targetEq : n = target at hstep
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hn : n ≠ 0 := by simp [n]; omega
    exact (hn targetEq).elim
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
    have hi : i.succ = n := by
      apply Fin.ext
      have hv := congrArg Fin.val targetEq
      simp at hv
      omega
    simpa [hgen, n, hi] using currentOneUncolored
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hlast : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by simpa [n] using hPE
    rw [targetEq, currentKind] at hlast
    contradiction
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hlast : ett.series.data.kind n =
        some TashkinovExtensionKind.PE := by simpa [n] using hPE
    rw [targetEq, currentKind] at hlast
    contradiction

theorem InterchangePECommonMissingClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (base : HierarchyBase ett generating)
    (hproper : IsProperEdgeColoring G sigma)
    (hone : IsOneEdgeUncolored sigma e0)
    (hstable : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      generating sigma)
    (color : Fin k) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    color ∈ TreeMissingColors sigma Tn →
      color ∈ TreeMissingColors sigma base.closure →
      TreeColorSetClosed G sigma base.core {color} := by
  classical
  dsimp
  intro hcolorT hcolorR
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
  have hgen : generating = ett.series.data.coloring (Fin.last ett.rounds) :=
    ett.generatingColoring
  have hstableTree : StableColoring Tn
      (TashkinovStoredColors ett.series.data n) generating sigma := by
    simpa [Tn, n] using hstable.1
  have hproperGen : IsProperEdgeColoring G generating := by
    exact @InterchangePECommonMissingClosed_hproperGen_91 V E inferInstance inferInstance
        inferInstance G k e0 input T generating ett hpositive hPE hgen
  have honeGen : IsOneEdgeUncolored generating e0 := by
    exact @InterchangePECommonMissingClosed_honeGen_131 V E inferInstance inferInstance
        inferInstance G k e0 input T generating ett hpositive hPE hgen
  have hlowerElem : ColoredVertexSetElementary G
      (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
      (TreeSequenceVertexSet Tn) := by
    by_cases honeRound : ett.rounds = 1
    · have htech := TechnicalTheoremBase G k ett.rounds e0 input ett.series
      have hn : n = (⟨1, by omega⟩ : Fin (ett.rounds + 1)) := by
        apply Fin.ext
        simp [n, honeRound]
      have hTn : Tn = ett.series.data.tree ⟨1, by omega⟩ := by
        apply congrArg (fun i : Fin (ett.rounds + 2) => ett.series.data.tree i)
        apply Fin.ext
        simp [n, honeRound]
      have hcol : (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)) = 0 := by
        apply Fin.ext
        simp [honeRound]
      rw [hTn, hcol]
      exact htech.1
    · have hgt : 1 < ett.rounds := by omega
      obtain ⟨pred, hpredRound, hpredMP, htrees, hdata⟩ :=
        CertifiedETTPredecessor G k e0 input T generating ett hMP hgt
      have hpredElem := hlower pred (by omega) (by omega) hpredMP
      have htree : ColoredVertexSetElementary G
          (ett.series.data.coloring ⟨ett.rounds - 1, by omega⟩)
          (TreeSequenceVertexSet
            (ett.series.data.tree ⟨ett.rounds, by omega⟩)) := hpredElem.1
      have hidx : (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) =
          (Fin.last ett.rounds).castSucc := by
        apply Fin.ext
        rfl
      rw [hidx] at htree
      exact htree
  have hcommon := ParallelCommonMissingClosed G k e0 input T generating
      generating ett hpositive base hgen hPE hlowerElem
  have hgenCommon : color ∈ TreeMissingColors generating Tn := by
    have hs := hstable.1.2
    unfold TreeMissingColors at *
    rcases Finset.mem_biUnion.mp (show color ∈
      TreeMissingColors sigma Tn from hcolorT) with ⟨v, hv, hc⟩
    refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
    rw [← hs v hv]
    exact hc
  have hgenClosure : color ∈ TreeMissingColors generating base.closure := by
    have hs := hstable.2.2
    unfold TreeMissingColors at *
    rcases Finset.mem_biUnion.mp (show color ∈
      TreeMissingColors sigma base.closure from hcolorR) with ⟨v, hv, hc⟩
    refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
    rw [← hs v hv]
    exact hc
  have hstableRevTree : StableColoring Tn
        (TashkinovStoredColors ett.series.data n) sigma generating := by
    let a : {psi : PartialEdgeColoring E k //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨generating, hproperGen, honeGen⟩
    let b : {psi : PartialEdgeColoring E k //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨sigma, hproper, hone⟩
    have hab : StableColoring Tn
        (TashkinovStoredColors ett.series.data n) a.1 b.1 := by
      simpa [a, b] using hstableTree
    have hba := (sc2 G e0 Tn
      (TashkinovStoredColors ett.series.data n)).symm hab
    simpa [a, b] using hba
  have hstableRevClosure : StableColoring base.closure ∅ sigma generating := by
    let a : {psi : PartialEdgeColoring E k //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨generating, hproperGen, honeGen⟩
    let b : {psi : PartialEdgeColoring E k //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨sigma, hproper, hone⟩
    have hab : StableColoring base.closure ∅ a.1 b.1 := by
      simpa [a, b] using hstable.2
    have hba := (sc2 G e0 base.closure ∅).symm hab
    simpa [a, b] using hba
  obtain ⟨orderedUnion⟩ := (base.parallel hPE).2.2
  have coreVertices : TreeSequenceVertexSet base.core =
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet base.closure := by
    rw [← orderedUnion.vertexSet]
  unfold TreeColorSetClosed
  intro c hc
  have hcEq : c = color := by simpa using hc
  subst c
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have hgParts : g ∈ BoundaryEdges G (TreeSequenceVertexSet base.core) ∧
      sigma g = some color := by
    simpa [BoundaryColorEdges] using hg
  obtain ⟨hb, hcolorSigma⟩ := hgParts
  have hbParts : ∃ p ∈ TreeSequenceVertexSet base.core, ∃ r ∉
      TreeSequenceVertexSet base.core, G.ends g = s(p, r) := by
    simpa [BoundaryEdges] using hb
  obtain ⟨p, hp, r, hr, hends⟩ := hbParts
  have hxCore : TreeSequenceVertexSet Tn ⊆
      TreeSequenceVertexSet base.core := by
    rw [coreVertices]
    exact Finset.subset_union_left
  have hyCore : TreeSequenceVertexSet base.closure ⊆
      TreeSequenceVertexSet base.core := by
    rw [coreVertices]
    exact Finset.subset_union_right
  have incidentAt : Incident G p g := by
    change p ∈ G.ends g
    rw [hends]
    exact Sym2.mem_mk_left _ _
  have hgenBoundary : g ∈ BoundaryColorEdges G generating
      (TreeSequenceVertexSet base.core) color := by
    have hbgen : g ∈ BoundaryEdges G (TreeSequenceVertexSet base.core) := hb
    have hcoreColor : generating g = some color := by
      by_cases hpX : p ∈ TreeSequenceVertexSet Tn
      · have hinc : TreeIncidentEdge Tn g := ⟨p, hpX, incidentAt⟩
        have hmiss : color ∈ TreeMissingColors sigma Tn := by
          simpa [Tn, n] using hcolorT
        have heq := hstableRevTree.1 g hinc
          ⟨color, Finset.mem_union_left _ hmiss, hcolorSigma⟩
        exact heq.trans hcolorSigma
      · have hpY : p ∈ TreeSequenceVertexSet base.closure := by
          have hu : p ∈ TreeSequenceVertexSet Tn ∪
              TreeSequenceVertexSet base.closure := by
            rw [← coreVertices]
            exact hp
          exact (Finset.mem_union.mp hu).resolve_left hpX
        have hinc : TreeIncidentEdge base.closure g :=
          ⟨p, hpY, incidentAt⟩
        have hmiss : color ∈ TreeMissingColors sigma base.closure := hcolorR
        have heq := hstableRevClosure.1 g hinc
          ⟨color, Finset.mem_union_left _ hmiss, hcolorSigma⟩
        exact heq.trans hcolorSigma
    simp [BoundaryColorEdges, hbgen, hcoreColor]
  have hgenEmpty := hcommon color
    (Finset.mem_inter.mpr ⟨hgenCommon, hgenClosure⟩)
  rw [hgenEmpty] at hgenBoundary
  simp at hgenBoundary

end GoldbergSeymour

end
