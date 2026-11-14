/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyStoredColorsCardinality
public import LeanPool.GoldbergSeymour.Step1ExitLegPresentation
public import LeanPool.GoldbergSeymour.StableColoringEquivalence

/-!
# Step1Exit Leg Theta Zero Nonparallel

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_finish_62.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ) (P : Step1ExitLegPresentation G k e0 n
        q), P.hierarchy.dividerCount = (0 : ℕ) → P.ett.series.data.kind (Fin.last P.ett.rounds) ≠
        some TashkinovExtensionKind.PE → (1 : ℕ) ≤ P.ett.rounds → (
    ∀ c ∈ TreeMissingColors P.phi (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc),
        TreeColorSetClosed G P.phi (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc)
        { c }) →
    ∃ (theta : Fin k), theta ≠ P.a ∧ theta ≠ P.b ∧ theta ∈ TreeMissingColors P.phi
        (HierarchyStarredStage P.hierarchy (Fin.last P.hierarchy.dividerCount)) ∧
        TreeColorSetClosed G P.phi (HierarchyStarredStage P.hierarchy (Fin.last
        P.hierarchy.dividerCount)) { theta } ∧ TreeColorSetClosed G P.phi P.T { theta } := by
  classical
  intro V E _ _ _ _ G k e0 n q P hzero hnonparallel hr hclosed
  have hcore : P.base.core =
        P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc :=
      P.base.nonparallel hnonparallel
  have hstage : HierarchyStarredStage P.hierarchy
      (Fin.last P.hierarchy.dividerCount) = P.base.core := by
    have hz : Fin.last P.hierarchy.dividerCount = 0 := by
      apply Fin.ext
      simp [hzero]
    rw [hz]
    rfl
  have hfinal : ∀ c ∈ TreeMissingColors P.phi
      (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc),
      TreeColorSetClosed G P.phi
        (HierarchyStarredStage P.hierarchy
          (Fin.last P.hierarchy.dividerCount)) {c} := by
    intro c hc
    rw [hstage, hcore]
    exact hclosed c hc
  have hT : TreeSequenceInitialSegment
      (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc) P.T := by
    convert P.ett.abovePenultimate using 1
    apply congrArg P.ett.series.data.tree
    apply Fin.ext
    simp
  have hmiss : ∀ c ∈ TreeMissingColors P.phi
      (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc),
      c ∈ TreeMissingColors P.phi P.T := by
    intro c hc
    unfold TreeMissingColors at hc ⊢
    obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
    apply Finset.mem_biUnion.mpr
    have hv' : v ∈ TreeSequenceVertexSet P.T := by
      simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
      obtain ⟨x, hx⟩ := hv
      rcases hT with ⟨hlen, hvertices, hedges⟩
      refine ⟨Fin.castLE (Nat.succ_le_succ hlen) x, ?_⟩
      exact (hvertices x).trans hx
    exact ⟨v, hv', hvc⟩
  have hD : (HierarchyStoredColorsAt P.hierarchy 0).card ≤ P.ett.rounds :=
    HierarchyStoredColorsCardinality P.hierarchy 0
  let M := TreeMissingColors P.phi
      (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc)
  let D := (HierarchyStoredColorsAt P.hierarchy 0).biUnion
      (P.good.gamma 0)
  have hsub : D ⊆ M := by
    intro c hc
    obtain ⟨eta, heta, hgc⟩ := Finset.mem_biUnion.mp hc
    have hav := P.good.avoidance 0 eta heta hgc
    exact (Finset.mem_sdiff.mp hav).1
  have hDcard : D.card ≤ 2 * P.ett.rounds := by
    calc
      D.card ≤ ∑ eta ∈ HierarchyStoredColorsAt P.hierarchy 0,
          (P.good.gamma 0 eta).card := Finset.card_biUnion_le
      _ = 2 * (HierarchyStoredColorsAt P.hierarchy 0).card := by
        rw [Finset.sum_congr rfl (fun eta heta => P.good.twoColors 0 eta heta)]
        simp [Nat.mul_comm]
      _ ≤ 2 * P.ett.rounds := Nat.mul_le_mul_left 2 hD
  have hUcard : (D ∪ {P.a, P.b}).card ≤ 2 * P.ett.rounds + 2 := by
    calc
      (D ∪ {P.a, P.b}).card ≤ D.card + ({P.a, P.b} : Finset (Fin k)).card :=
        Finset.card_union_le D {P.a, P.b}
      _ ≤ 2 * P.ett.rounds + 2 := by simp [P.a_ne_b]; omega
  have hlarge : 2 * P.ett.rounds + 11 ≤ M.card := by
    simpa [M] using P.large
  have hnonempty : (M \ (D ∪ {P.a, P.b})).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff]
    have hiu : (M ∩ (D ∪ {P.a, P.b})).card ≤
        (D ∪ {P.a, P.b}).card := Finset.card_le_card Finset.inter_subset_right
    have hiu' : ((D ∪ {P.a, P.b}) ∩ M).card ≤
        (D ∪ {P.a, P.b}).card := by
      simpa [Finset.inter_comm] using hiu
    omega
  obtain ⟨theta, htheta⟩ := hnonempty
  have hthetaM : theta ∈ M := (Finset.mem_sdiff.mp htheta).1
  have hthetaAvoid : theta ∉ D := by
    intro ht
    exact (Finset.mem_sdiff.mp htheta).2 (Finset.mem_union_left _ ht)
  have hthetaA : theta ≠ P.a := by
    intro he
    exact (Finset.mem_sdiff.mp htheta).2 (Finset.mem_union_right _ (by simp [he]))
  have hthetaB : theta ≠ P.b := by
    intro he
    exact (Finset.mem_sdiff.mp htheta).2 (Finset.mem_union_right _ (by simp [he]))
  have htermD : (HierarchyTerminalStoredColors P.hierarchy).biUnion
      (P.good.gamma (Fin.last P.hierarchy.dividerCount)) ⊆ D := by
    intro c hc
    obtain ⟨eta, heta, hgc⟩ := Finset.mem_biUnion.mp hc
    have heta' := heta
    change eta ∈ TashkinovStoredColors P.ett.series.data (Fin.last P.ett.rounds) \
      TreeMissingColors P.phi P.T at heta'
    apply Finset.mem_biUnion.mpr
    refine ⟨eta, ?_, ?_⟩
    · have hetaParts := Finset.mem_sdiff.mp heta'
      refine Finset.mem_sdiff.mpr ⟨hetaParts.1, ?_⟩
      exact fun hxm => hetaParts.2 (hmiss eta (by
        simpa [hstage, hcore, HierarchyStarredStage] using hxm))
    · have hz : Fin.last P.hierarchy.dividerCount = 0 := by
        apply Fin.ext
        simp [hzero]
      simpa [hz] using hgc
  have hthetaTerm : theta ∈ TreeMissingColors P.phi P.T := hmiss theta hthetaM
  have htermClosed : TreeColorSetClosed G P.phi P.T {theta} := by
    unfold TreeColorSetClosed
    intro c hc
    have hct : c = theta := Finset.mem_singleton.mp hc
    subst c
    apply P.terminalMinusClosed
    · exact Finset.mem_sdiff.mpr ⟨hthetaTerm, fun hd => hthetaAvoid (htermD hd)
        ⟩
  have hthetaStage : theta ∈ TreeMissingColors P.phi
      (HierarchyStarredStage P.hierarchy
        (Fin.last P.hierarchy.dividerCount)) := by
    rw [hstage, hcore]
    exact hthetaM
  exact ⟨theta, hthetaA, hthetaB, hthetaStage,
    hfinal theta hthetaM, htermClosed⟩

private theorem helper_branch_197.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ) (P : Step1ExitLegPresentation G k e0
        n q), P.ett.series.data.kind (Fin.last P.ett.rounds) ≠ some TashkinovExtensionKind.PE →
    ∀ (hr : (1 : ℕ) ≤ P.ett.rounds),
    let i : Fin P.ett.rounds := (⟨P.ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬P.ett.rounds - (1 : ℕ) < P.ett.rounds) =>
    by
            omega
    ⟩ : Fin P.ett.rounds); i.succ = Fin.last P.ett.rounds → ((
    ∀ c ∈ TreeMissingColors P.phi (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc),
        TreeColorSetClosed G P.phi (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc)
        { c }) →
    ∃ (theta : Fin k), theta ≠ P.a ∧ theta ≠ P.b ∧ theta ∈ TreeMissingColors P.phi
        (HierarchyStarredStage P.hierarchy (Fin.last P.hierarchy.dividerCount)) ∧
        TreeColorSetClosed G P.phi (HierarchyStarredStage P.hierarchy (Fin.last
        P.hierarchy.dividerCount)) { theta } ∧ TreeColorSetClosed G P.phi P.T { theta }) →
    ∀ (ci : Fin P.ett.rounds), IsProperEdgeColoring G (P.ett.series.data.coloring ci.castSucc) →
        IsOneEdgeUncolored (P.ett.series.data.coloring ci.castSucc) e0 → ColoredVertexSetClosed G
        (P.ett.series.data.coloring ci.castSucc) (TreeSequenceVertexSet (P.ett.series.data.tree
        ci.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G (P.ett.series.data.coloring
        ci.castSucc) (TreeSequenceVertexSet (P.ett.series.data.tree ci.succ.castSucc)) → ¬Nonempty
        (RevisitingExtensionCertificate P.ett.series.data ci.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (P.ett.series.data.tree ci.succ.castSucc)
        (TashkinovStoredColors P.ett.series.data ci.castSucc) (P.ett.series.data.coloring
        ci.castSucc)), (
    ∀ (pi : PartialEdgeColoring E k), IsProperEdgeColoring G pi → IsOneEdgeUncolored pi e0 →
        StableColoring (P.ett.series.data.tree ci.succ.castSucc) (insert choice.color
        (TashkinovStoredColors P.ett.series.data ci.castSucc)) choice.selected pi → Disjoint
        (MissingColors G pi choice.otherEndpoint) (TreeMissingColors pi (P.ett.series.data.tree
        ci.succ.castSucc))) → P.ett.series.data.coloring ci.succ = choice.selected →
        P.ett.series.data.stored ci.succ = { choice.color } → P.ett.series.data.connectingEdges
        ci.succ = { choice.edge } → P.ett.series.data.kind ci.succ = some
        TashkinovExtensionKind.SE → P.ett.series.data.chosenVertex ci.succ = some choice.vertex →
        P.ett.series.data.outsideVertex ci.succ = some choice.otherEndpoint →
        P.ett.series.data.delta ci.succ = some choice.color → P.ett.series.data.gamma ci.succ =
        none →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (P.ett.series.data.tree
        ci.succ.castSucc) choice.edge adjoined → TashkinovClosure (P.ett.series.data.coloring
        ci.succ) adjoined (P.ett.series.data.tree ci.succ.succ) → TreeSequenceInitialSegment
        (P.ett.series.data.tree ci.succ.castSucc) (P.ett.series.data.tree ci.succ.succ) →
        (P.ett.series.data.tree ci.succ.castSucc).length < (P.ett.series.data.tree
        ci.succ.succ).length → i.succ = ci.succ →
    ∃ (theta : Fin k), theta ≠ P.a ∧ theta ≠ P.b ∧ theta ∈ TreeMissingColors P.phi
        (HierarchyStarredStage P.hierarchy (Fin.last P.hierarchy.dividerCount)) ∧
        TreeColorSetClosed G P.phi (HierarchyStarredStage P.hierarchy (Fin.last
        P.hierarchy.dividerCount)) { theta } ∧ TreeColorSetClosed G P.phi P.T { theta } := by
  classical
  intro V E _ _ _ _ G k e0 n q P hnonparallel hr i hi finish ci previousProper
      previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
      seriesAlternative currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension hs
  have hci : ci = i := by
    apply Fin.ext
    have hv := congrArg Fin.val hs
    simp at hv
    omega
  subst ci
  have hkind : P.ett.series.data.kind (Fin.last P.ett.rounds) ≠
      some TashkinovExtensionKind.PE := hnonparallel
  have htree : P.ett.series.data.tree i.succ.castSucc =
      P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc := by rw [hi]
  have hclosed : ∀ c ∈ TreeMissingColors P.phi
      (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc),
      TreeColorSetClosed G P.phi
        (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc) {c} := by
    intro c hc
    unfold TreeColorSetClosed
    intro d hd
    have hdc : d = c := Finset.mem_singleton.mp hd
    subst d
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hf' : f ∈ BoundaryEdges G
        (TreeSequenceVertexSet (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc)) ∧
        P.phi f = some c := by simpa [BoundaryColorEdges] using hf
    have hfb : f ∈ BoundaryEdges G
        (TreeSequenceVertexSet (P.ett.series.data.tree i.succ.castSucc)) := by
      rw [htree]
      exact hf'.1
    have hfu : ∃ u ∈ TreeSequenceVertexSet
        (P.ett.series.data.tree i.succ.castSucc), ∃ v ∉
        TreeSequenceVertexSet (P.ett.series.data.tree i.succ.castSucc),
        G.ends f = s(u, v) := by simpa [BoundaryEdges] using hfb
    obtain ⟨u, hu, v, hv, huv⟩ := hfu
    have hcPrior := hc
    rw [← htree] at hcPrior
    obtain ⟨w, hw, hwm⟩ := Finset.mem_biUnion.mp
      (by simpa [TreeMissingColors] using hcPrior)
    have hstable := choice.selectedStable
    let left : {psi : _ //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨P.ett.series.data.coloring i.castSucc, previousProper, previousOneUncolored⟩
    let right : {psi : _ //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨choice.selected, choice.selectedProper, choice.selectedOneUncolored⟩
    have hstableRev : StableColoring
        (P.ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors P.ett.series.data i.castSucc)
        choice.selected (P.ett.series.data.coloring i.castSucc) := by
      have hab : StableColoring
          (P.ett.series.data.tree i.succ.castSucc)
          (TashkinovStoredColors P.ett.series.data i.castSucc)
          left.1 right.1 := by simpa [left, right] using hstable
      have hba := (sc2 G e0 (P.ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors P.ett.series.data i.castSucc)).symm hab
      simpa [left, right] using hba
    have htreeIncident : TreeIncidentEdge
        (P.ett.series.data.tree i.succ.castSucc) f := by
      refine ⟨u, hu, ?_⟩
      unfold Incident
      rw [huv]
      exact Sym2.mem_iff.mpr (Or.inl rfl)
    have hselectedColor : choice.selected f = some c := by
      rw [← currentColoring, hi, ← P.ett.generatingColoring]
      exact hf'.2
    have hmissingSelected : c ∈ TreeMissingColors choice.selected
        (P.ett.series.data.tree i.succ.castSucc) := by
      unfold TreeMissingColors
      obtain ⟨w, hw, hwm⟩ := Finset.mem_biUnion.mp
        (by simpa [TreeMissingColors] using hcPrior)
      apply Finset.mem_biUnion.mpr
      refine ⟨w, hw, ?_⟩
      rw [P.ett.generatingColoring, ← hi, currentColoring] at hwm
      exact hwm
    have hmissingSelectedAt : c ∈ MissingColors G choice.selected w := by
      rw [P.ett.generatingColoring, ← hi, currentColoring] at hwm
      exact hwm
    have hmissingPiAt : c ∈ MissingColors G
        (P.ett.series.data.coloring i.castSucc) w := by
      exact (hstable.2 w hw).symm ▸ hmissingSelectedAt
    have hmissingPi : c ∈ TreeMissingColors
        (P.ett.series.data.coloring i.castSucc)
        (P.ett.series.data.tree i.succ.castSucc) := by
      unfold TreeMissingColors
      exact Finset.mem_biUnion.mpr ⟨w, hw, hmissingPiAt⟩
    have hpiColor : (P.ett.series.data.coloring i.castSucc) f = some c := by
      exact (hstableRev.1 f htreeIncident
        ⟨c, Finset.mem_union_left _ hmissingSelected, hselectedColor⟩).trans
          hselectedColor
    have hcf := previousClosed hfb hw hpiColor
    have hcm : c ∈ MissingColors G (P.ett.series.data.coloring i.castSucc) w := by
      exact hmissingPiAt
    exact hcf hcm
  exact finish hclosed

private theorem helper_branch_301.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ) (P : Step1ExitLegPresentation G k e0
        n q) (hr : (1 : ℕ) ≤ P.ett.rounds),
    let i : Fin P.ett.rounds := (⟨P.ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a :
        ¬P.ett.rounds - (1 : ℕ) < P.ett.rounds) =>
    by
            omega
    ⟩ : Fin P.ett.rounds); i.succ = Fin.last P.ett.rounds → ((
    ∀ c ∈ TreeMissingColors P.phi (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc),
        TreeColorSetClosed G P.phi (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc)
        { c }) →
    ∃ (theta : Fin k), theta ≠ P.a ∧ theta ≠ P.b ∧ theta ∈ TreeMissingColors P.phi
        (HierarchyStarredStage P.hierarchy (Fin.last P.hierarchy.dividerCount)) ∧
        TreeColorSetClosed G P.phi (HierarchyStarredStage P.hierarchy (Fin.last
        P.hierarchy.dividerCount)) { theta } ∧ TreeColorSetClosed G P.phi P.T { theta }) →
    ∀ (ci : Fin P.ett.rounds), IsProperEdgeColoring G (P.ett.series.data.coloring ci.castSucc) →
        IsOneEdgeUncolored (P.ett.series.data.coloring ci.castSucc) e0 → ColoredVertexSetClosed G
        (P.ett.series.data.coloring ci.castSucc) (TreeSequenceVertexSet (P.ett.series.data.tree
        ci.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G (P.ett.series.data.coloring
        ci.castSucc) (TreeSequenceVertexSet (P.ett.series.data.tree ci.succ.castSucc)) →
    ∀ (available : RevisitingExtensionCertificate P.ett.series.data ci.castSucc),
        P.ett.series.data.coloring ci.succ = P.ett.series.data.coloring ci.castSucc →
        P.ett.series.data.stored ci.succ = { available.delta, available.gamma } →
        P.ett.series.data.connectingEdges ci.succ = { available.edge } → P.ett.series.data.kind
        ci.succ = some TashkinovExtensionKind.RE → P.ett.series.data.chosenVertex ci.succ = some
        available.insideEndpoint → P.ett.series.data.outsideVertex ci.succ = some
        available.outsideEndpoint → P.ett.series.data.delta ci.succ = some available.delta →
        P.ett.series.data.gamma ci.succ = some available.gamma →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (P.ett.series.data.tree
        ci.succ.castSucc) available.edge adjoined → TashkinovClosure (P.ett.series.data.coloring
        ci.succ) adjoined (P.ett.series.data.tree ci.succ.succ) → TreeSequenceInitialSegment
        (P.ett.series.data.tree ci.succ.castSucc) (P.ett.series.data.tree ci.succ.succ) →
        (P.ett.series.data.tree ci.succ.castSucc).length < (P.ett.series.data.tree
        ci.succ.succ).length → i.succ = ci.succ →
    ∃ (theta : Fin k), theta ≠ P.a ∧ theta ≠ P.b ∧ theta ∈ TreeMissingColors P.phi
        (HierarchyStarredStage P.hierarchy (Fin.last P.hierarchy.dividerCount)) ∧
        TreeColorSetClosed G P.phi (HierarchyStarredStage P.hierarchy (Fin.last
        P.hierarchy.dividerCount)) { theta } ∧ TreeColorSetClosed G P.phi P.T { theta } := by
  classical
  intro V E _ _ _ _ G k e0 n q P hr i hi finish ci previousProper previousOneUncolored
      previousClosed previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension hs
  have hci : ci = i := by
    apply Fin.ext
    have hv := congrArg Fin.val hs
    simp at hv
    omega
  subst ci
  have htree : P.ett.series.data.tree i.succ.castSucc =
      P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc := by rw [hi]
  have hclosed : ∀ c ∈ TreeMissingColors P.phi
      (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc),
      TreeColorSetClosed G P.phi
        (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc) {c} := by
    intro c hc
    unfold TreeColorSetClosed
    intro d hd
    have hdc : d = c := Finset.mem_singleton.mp hd
    subst d
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hf' : f ∈ BoundaryEdges G
        (TreeSequenceVertexSet (P.ett.series.data.tree (Fin.last P.ett.rounds).castSucc)) ∧
        P.phi f = some c := by simpa [BoundaryColorEdges] using hf
    have hfb : f ∈ BoundaryEdges G
        (TreeSequenceVertexSet (P.ett.series.data.tree i.succ.castSucc)) := by
      rw [htree]
      exact hf'.1
    have hfu : ∃ u ∈ TreeSequenceVertexSet
        (P.ett.series.data.tree i.succ.castSucc), ∃ v ∉
        TreeSequenceVertexSet (P.ett.series.data.tree i.succ.castSucc),
        G.ends f = s(u, v) := by simpa [BoundaryEdges] using hfb
    obtain ⟨u, hu, v, hv, huv⟩ := hfu
    obtain ⟨w, hw, hwm⟩ := Finset.mem_biUnion.mp
      (by simpa [TreeMissingColors] using (show c ∈
        TreeMissingColors P.phi
          (P.ett.series.data.tree i.succ.castSucc) by
        rw [htree]
        exact hc))
    have hcm : c ∈ MissingColors G
        (P.ett.series.data.coloring i.castSucc) w := by
      rw [P.ett.generatingColoring, ← hi, currentColoring] at hwm
      exact hwm
    have hcol : (P.ett.series.data.coloring i.castSucc) f = some c := by
      rw [← currentColoring, hi, ← P.ett.generatingColoring]
      exact hf'.2
    exact (previousClosed hfb hw hcol) hcm
  exact finish hclosed

lemma Step1ExitLegThetaZeroNonparallel {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (n q : ℕ)
    (P : Step1ExitLegPresentation G k e0 n q)
    (hzero : P.hierarchy.dividerCount = 0)
    (hnonparallel : P.ett.series.data.kind (Fin.last P.ett.rounds) ≠
      some TashkinovExtensionKind.PE) :
    ∃ theta : Fin k,
    theta ≠ P.a ∧
      theta ≠ P.b ∧
        theta ∈
            TreeMissingColors P.phi
              (HierarchyStarredStage P.hierarchy (Fin.last P.hierarchy.dividerCount)) ∧
          TreeColorSetClosed G P.phi
              (HierarchyStarredStage P.hierarchy (Fin.last P.hierarchy.dividerCount))
              { theta } ∧
            TreeColorSetClosed G P.phi P.T { theta } := by
  classical
  have hr := P.ett.roundsPositive
  let i : Fin P.ett.rounds := ⟨P.ett.rounds - 1, by omega⟩
  have hi : i.succ = Fin.last P.ett.rounds := by
    ext
    simp [i]
    omega
  have finish := @helper_finish_62 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 n q P hzero hnonparallel hr
  have hcert := P.ett.series.certified i.succ
  generalize hs : i.succ = slot at hcert
  cases hcert with
  | initial triple seedLength initialColoring initialStored initialEdges initialKind
      initialVertex initialOutside initialDelta initialGamma initialClosure =>
      exact (Fin.succ_ne_zero i hs).elim
  | SE ci previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      exact @helper_branch_197 V E inferInstance inferInstance inferInstance inferInstance G k e0
          n q P hnonparallel hr hi finish ci previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternative currentColoring
          currentStored currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension strictExtension hs
  | PE ci previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex currentOutside
      currentDelta currentGamma closedExtension orderedExtension strictExtension =>
      have hkind := currentKind
      have hci : ci = i := by
        apply Fin.ext
        have hv := congrArg Fin.val hs
        simp at hv
        omega
      subst ci
      rw [hi] at hkind
      exact (hnonparallel hkind).elim
  | RE ci previousProper previousOneUncolored previousClosed previousNotStronglyClosed available
      currentColoring currentStored currentEdges currentKind currentVertex currentOutside
      currentDelta currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      exact @helper_branch_301 V E inferInstance inferInstance inferInstance inferInstance G k e0
          n q P hr hi finish ci previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored currentEdges
          currentKind currentVertex currentOutside currentDelta currentGamma adjoined
          adjoinedExactly closedExtension orderedExtension strictExtension hs
end GoldbergSeymour

end
