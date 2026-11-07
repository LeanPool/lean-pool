/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ParallelCommonMissingClosed
public import LeanPool.GoldbergSeymour.Step1ExitLegPresentation

/-!
# Step1Exit Leg Theta Zero Parallel

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma Step1ExitLegThetaZeroParallel {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ)
    (P : Step1ExitLegPresentation G k e0 n q)
    (hzero : P.hierarchy.dividerCount = 0)
    (hparallel : P.ett.series.data.kind (Fin.last P.ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hpre :
      let r : Fin P.ett.rounds := ⟨P.ett.rounds - 1, by
        have h := P.ett.roundsPositive
        omega⟩
      ColoredVertexSetElementary G
        (P.ett.series.data.coloring r.castSucc)
        (TreeSequenceVertexSet
          (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc))) :
    ∃ theta : Fin k,
      theta ≠ P.a ∧ theta ≠ P.b ∧
      theta ∈ TreeMissingColors P.phi
        (HierarchyStarredStage P.hierarchy
          (Fin.last P.hierarchy.dividerCount)) ∧
      TreeColorSetClosed G P.phi
        (HierarchyStarredStage P.hierarchy
          (Fin.last P.hierarchy.dividerCount)) {theta} ∧
      TreeColorSetClosed G P.phi P.T {theta} := by
  classical
  have hrounds : 0 < P.ett.rounds := Nat.lt_of_lt_of_le Nat.zero_lt_one P.ett.roundsPositive
  have hbase := P.good.parallelBase
  dsimp at hbase
  have hbound := hbase hparallel |>.2
  let n : Fin (P.ett.rounds + 1) := Fin.last P.ett.rounds
  let X : TreeSequence G e0 := P.ett.series.data.tree n.castSucc
  let S : Finset (Fin k) :=
    (TreeMissingColors P.phi X ∩ TreeMissingColors P.phi P.base.closure) \
      ((HierarchyStoredColorsAt P.hierarchy 0).biUnion (P.good.gamma 0))
  have hScard : 4 ≤ S.card := by simpa [S, X, n] using hbound
  have hnotall : ∃ theta ∈ S, theta ≠ P.a ∧ theta ≠ P.b := by
    by_contra h
    push Not at h
    have hsub : S ⊆ ({P.a, P.b} : Finset (Fin k)) := by
      intro theta htheta
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hta : theta = P.a
      · exact Or.inl hta
      · exact Or.inr ((h theta htheta) hta)
    have hcard : S.card ≤ 2 := by
      calc
        S.card ≤ ({P.a, P.b} : Finset (Fin k)).card := Finset.card_le_card hsub
        _ ≤ 2 := by simp [P.a_ne_b]
    omega
  obtain ⟨theta, hthetaS, hthetaA, hthetaB⟩ := hnotall
  change theta ∈
      (TreeMissingColors P.phi X ∩ TreeMissingColors P.phi P.base.closure) \
        ((HierarchyStoredColorsAt P.hierarchy 0).biUnion (P.good.gamma 0)) at hthetaS
  have hthetaSplit := hthetaS
  simp only [Finset.mem_sdiff, Finset.mem_inter] at hthetaSplit
  have hthetaMissingX : theta ∈ TreeMissingColors P.phi X := hthetaSplit.1.1
  have hthetaMissingClosure : theta ∈ TreeMissingColors P.phi P.base.closure :=
    hthetaSplit.1.2
  have hthetaNotInitialStored : theta ∉
      (HierarchyStoredColorsAt P.hierarchy 0).biUnion (P.good.gamma 0) :=
    hthetaSplit.2
  have hphi : P.phi = P.ett.series.data.coloring (Fin.last P.ett.rounds) :=
    P.ett.generatingColoring
  have hcommon := ParallelCommonMissingClosed G k e0 P.input P.T P.phi P.phi
    P.ett hrounds P.base hphi hparallel hpre
  have hcore : TreeColorSetClosed G P.phi P.base.core
      (TreeMissingColors P.phi X ∩ TreeMissingColors P.phi P.base.closure) := by
    simpa [X, n] using hcommon
  have hordered : Nonempty (OrderedTreeUnion X P.base.closure P.base.core) := by
    simpa [X, n] using (P.base.parallel hparallel).2.2
  obtain ⟨ordered⟩ := hordered
  have hcoreSet : TreeSequenceVertexSet P.base.core =
      TreeSequenceVertexSet X ∪ TreeSequenceVertexSet P.base.closure :=
    ordered.vertexSet
  have hXsub : TreeSequenceVertexSet X ⊆ TreeSequenceVertexSet P.base.core := by
    rw [hcoreSet]
    exact Finset.subset_union_left
  have hmissingCore : TreeMissingColors P.phi X ⊆
      TreeMissingColors P.phi P.base.core := by
    intro c hc
    unfold TreeMissingColors at hc ⊢
    obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
    apply Finset.mem_biUnion.mpr
    exact ⟨v, hXsub hv, hvc⟩
  have hthetaCore : theta ∈ TreeMissingColors P.phi P.base.core :=
    hmissingCore hthetaMissingX
  have hstar : HierarchyStarredStage P.hierarchy
      (Fin.last P.hierarchy.dividerCount) = P.base.core := by
    have hlast : Fin.last P.hierarchy.dividerCount =
        (⟨0, by omega⟩ : Fin (P.hierarchy.dividerCount + 1)) := by
      apply Fin.ext
      simp [hzero]
    rw [hlast]
    rfl
  have hthetaStar : theta ∈ TreeMissingColors P.phi
      (HierarchyStarredStage P.hierarchy (Fin.last P.hierarchy.dividerCount)) := by
    simpa [hstar] using hthetaCore
  have hclosedStar : TreeColorSetClosed G P.phi
      (HierarchyStarredStage P.hierarchy (Fin.last P.hierarchy.dividerCount)) {theta} := by
    rw [hstar]
    unfold TreeColorSetClosed at hcore ⊢
    intro c hc
    apply hcore c
    have hct : c = theta := Finset.mem_singleton.mp hc
    subst c
    exact Finset.mem_inter.mpr ⟨hthetaMissingX, hthetaMissingClosure⟩
  refine ⟨theta, hthetaA, hthetaB, hthetaStar, hclosedStar, ?_⟩
  have initialSubset : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hab x hx
    unfold TreeSequenceVertexSet at hx ⊢
    simp only [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨hlen, hvertices, hedges⟩ := hab
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, ?_⟩
    exact hvertices i
  have hXterm : TreeSequenceVertexSet X ⊆ TreeSequenceVertexSet P.T := by
    apply initialSubset
    have hidx : (⟨P.ett.rounds, by omega⟩ : Fin (P.ett.rounds + 2)) =
        (Fin.last P.ett.rounds).castSucc := by apply Fin.ext; rfl
    simpa [X, n, hidx] using P.ett.abovePenultimate
  have hthetaTerminal : theta ∈ TreeMissingColors P.phi P.T := by
    unfold TreeMissingColors at hthetaMissingX ⊢
    obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hthetaMissingX
    apply Finset.mem_biUnion.mpr
    exact ⟨v, hXterm hv, hvc⟩
  have hterm := P.terminalMinusClosed
  unfold TreeColorSetMinusClosed at hterm
  have hterminalStored : (HierarchyTerminalStoredColors P.hierarchy).biUnion
      (P.good.gamma (Fin.last P.hierarchy.dividerCount)) ⊆
      (HierarchyStoredColorsAt P.hierarchy 0).biUnion (P.good.gamma 0) := by
    have hcoreTerm : TreeSequenceVertexSet P.base.core ⊆
        TreeSequenceVertexSet P.T := by
      apply initialSubset
      have hstage : P.hierarchy.stage
          (⟨1, by omega⟩ : Fin (P.hierarchy.dividerCount + 2)) = P.T := by
        have hidx : (⟨1, by omega⟩ : Fin (P.hierarchy.dividerCount + 2)) =
            Fin.last (P.hierarchy.dividerCount + 1) := by
          apply Fin.ext
          simp [hzero]
        exact congrArg P.hierarchy.stage hidx |>.trans P.hierarchy.terminalStage
      have hinside := P.hierarchy.coreInsideFirst
      rw [hstage] at hinside
      exact hinside
    have hmissingCoreTerm : TreeMissingColors P.phi P.base.core ⊆
        TreeMissingColors P.phi P.T := by
      intro c hc
      unfold TreeMissingColors at hc ⊢
      obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
      apply Finset.mem_biUnion.mpr
      exact ⟨v, hcoreTerm hv, hvc⟩
    intro c hc
    simp only [HierarchyTerminalStoredColors, HierarchyStoredColorsAt] at hc ⊢
    simp only [Finset.mem_biUnion] at hc ⊢
    obtain ⟨x, hx, hcx⟩ := hc
    refine ⟨x, ?_, ?_⟩
    · simp only [Finset.mem_sdiff] at hx ⊢
      exact ⟨hx.1, fun hmiss => hx.2 (hmissingCoreTerm hmiss)⟩
    · have hlast : Fin.last P.hierarchy.dividerCount =
          (⟨0, by omega⟩ : Fin (P.hierarchy.dividerCount + 1)) := by
        apply Fin.ext
        simp [hzero]
      simpa [hlast] using hcx
  have hthetaNotStored : theta ∉
      (HierarchyTerminalStoredColors P.hierarchy).biUnion
        (P.good.gamma (Fin.last P.hierarchy.dividerCount)) := by
    intro ht
    apply hthetaSplit.2
    exact hterminalStored ht
  unfold TreeColorSetClosed at hterm ⊢
  intro c hc
  apply hterm c
  simp only [Finset.mem_singleton] at hc
  subst c
  exact Finset.mem_sdiff.mpr ⟨hthetaTerminal, hthetaNotStored⟩

end GoldbergSeymour

end
