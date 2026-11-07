/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ETTFirstAppearanceIndex

/-!
# Extension Rules PEFirst Appearance Bound

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionRulesPEFirstAppearanceBound {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (q : Fin ett.rounds) (v : V)
    (hkind : ett.series.data.kind q.succ = some TashkinovExtensionKind.PE)
    (hvertex : ett.series.data.chosenVertex q.succ = some v)
    (hvFinal : v ∈ TreeSequenceVertexSet T) :
    ETTFirstAppearanceIndex ett v hvFinal ≤ q.val + 1 := by
  classical
  generalize hindex : q.succ = target
  cases ett.series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero q hindex).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hbad : some TashkinovExtensionKind.SE =
        some TashkinovExtensionKind.PE :=
      currentKind.symm.trans (by simpa [hindex] using hkind)
    cases hbad
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hbad : some TashkinovExtensionKind.RE =
        some TashkinovExtensionKind.PE :=
      currentKind.symm.trans (by simpa [hindex] using hkind)
    cases hbad
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hi : i = q := by
      apply Fin.ext
      simpa using (congrArg Fin.val hindex).symm
    subst i
    have hv : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) := by
      have hvchoice : choice.vertex = v :=
        Option.some.inj (currentVertex.symm.trans (by simpa [hindex] using hvertex))
      simpa [hvchoice] using choice.vertexDefective.1
    unfold ETTFirstAppearanceIndex
    dsimp
    have hmem : q.castSucc ∈
        Finset.univ.filter (fun j : Fin (ett.rounds + 1) =>
          v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett j)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [ExtendedTashkinovLadderStage, Fin.lastCases_castSucc] using hv
    have hle := Finset.min'_le
      (Finset.univ.filter (fun j : Fin (ett.rounds + 1) =>
        v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett j)))
      q.castSucc hmem
    have hnat := Fin.le_iff_val_le_val.mp hle
    rw [Fin.val_castSucc] at hnat
    convert Nat.succ_le_succ hnat using 1
end GoldbergSeymour

end
