/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyInitialPairsNonPE
public import LeanPool.GoldbergSeymour.GoodHierarchyInitialPairsPE
public import LeanPool.GoldbergSeymour.StableColoringEquivalence
public import LeanPool.GoldbergSeymour.CorrespondingExtendedTashkinovTree

/-!
# Algorithm Five Five Initial Good Hierarchy

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem AlgorithmFiveFiveInitialGoodHierarchy_branch_196.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (J : TreeSequence G e0) (corrJ :
        CorrespondingExtendedTashkinovTree G k e0 ett phi J) (baseJ : HierarchyBase
        corrJ.replacementETT phi) (KJ : TashkinovHierarchy corrJ.replacementETT baseJ), baseJ.core
        = base.core → KJ.stage 0 = ett.series.data.tree (Fin.last ett.rounds).castSucc →
        (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE ∧ J =
        base.core ∨ (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E), ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
        TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f J) →
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc;
        corrJ.replacementETT.series.data.tree (Fin.last corrJ.replacementETT.rounds).castSucc = Tn
        → corrJ.replacementETT.series.data.kind (Fin.last corrJ.replacementETT.rounds) =
        ett.series.data.kind (Fin.last ett.rounds) → 2 * corrJ.replacementETT.rounds + 11 ≤
        (TreeMissingColors phi (corrJ.replacementETT.series.data.tree (Fin.last
        corrJ.replacementETT.rounds).castSucc)).card → KJ.stage (Fin.succ 0) = J →
        ¬ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
    ∃ (gamma : Fin k → Finset (Fin k)), (
    ∀ eta ∈ HierarchyStoredColorsAt KJ 0, (gamma eta).card = 2 ∧ gamma eta ⊆ TreeMissingColors phi
        Tn) ∧ (
    ∀ (eta theta : Fin k), eta ∈ HierarchyStoredColorsAt KJ 0 → theta ∈ HierarchyStoredColorsAt KJ
        0 → eta ≠ theta → Disjoint (gamma eta) (gamma theta)) ∧ (
    ∀ eta ∈ HierarchyStoredColorsAt KJ 0, Disjoint (gamma eta) (HierarchySegmentColors KJ 0 eta))
        ∧ (corrJ.replacementETT.series.data.kind (Fin.last corrJ.replacementETT.rounds) = some
        TashkinovExtensionKind.PE → ¬TreeColorSetMinusClosed G phi baseJ.core
        ((HierarchyStoredColorsAt KJ 0).biUnion gamma) ∧ 4 ≤ ((TreeMissingColors phi
        (corrJ.replacementETT.series.data.tree (Fin.last corrJ.replacementETT.rounds).castSucc) ∩
        TreeMissingColors phi baseJ.closure) \ (HierarchyStoredColorsAt KJ 0).biUnion gamma).card)
  := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base J corrJ baseJ KJ hbaseCore _ hseed Tn htree hkind
      hlargeJ hterminal hPE
  have hnonPEJ : corrJ.replacementETT.series.data.kind
      (Fin.last corrJ.replacementETT.rounds) ≠
      some TashkinovExtensionKind.PE := by
    simpa only [hkind] using hPE
  obtain ⟨gamma, hpairs, hd⟩ :=
    GoodHierarchyInitialPairsNonPE KJ hnonPEJ hlargeJ
  have hpairs' : ∀ eta, eta ∈ HierarchyStoredColorsAt KJ 0 →
      (gamma eta).card = 2 ∧ gamma eta ⊆ TreeMissingColors phi Tn := by
    simpa only [htree] using hpairs
  obtain ⟨hkinds, f, hf, hadjoin⟩ := hseed.resolve_left
    (fun h => hPE h.1)
  have hcore : baseJ.core = Tn :=
    hbaseCore.trans (base.nonparallel hPE)
  have hseedColor : ∃ c : Fin k,
      phi f = some c ∧ c ∉ TreeMissingColors phi Tn := by
    have hstep := ett.series.certified (Fin.last ett.rounds)
    generalize htarget : (Fin.last ett.rounds : Fin (ett.rounds + 1)) =
      target at hstep
    cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
        have hv := congrArg Fin.val htarget
        have := ett.roundsPositive
        simp only [Fin.val_last, Fin.val_zero] at hv
        omega
    | PE i pp po pc pn nr choice sa gamma gr ss sp so sr ew cc cp co
        cs ce ck cv coo cd cg closed ordered strict =>
        exact (hPE (by simpa only [htarget] using ck)).elim
    | SE i pp po pc pn nr choice sa cc cs ce ck cv co cd cg ad ae
        closed ordered strict =>
        have hi : i.succ = Fin.last ett.rounds := htarget.symm
        have he : f = choice.edge := by
          apply Finset.singleton_injective
          exact hf.symm.trans (by simpa only [hi] using ce)
        have hphi : phi = choice.selected :=
          ett.generatingColoring.trans (by simpa only [hi] using cc)
        have hreverse : StableColoring (ett.series.data.tree i.succ.castSucc)
            (TashkinovStoredColors ett.series.data i.castSucc)
            choice.selected (ett.series.data.coloring i.castSucc) :=
          (sc2 G e0 (ett.series.data.tree i.succ.castSucc)
            (TashkinovStoredColors ett.series.data i.castSucc)).symm
            (x := ⟨ett.series.data.coloring i.castSucc, pp, po⟩)
            (y := ⟨choice.selected, choice.selectedProper,
              choice.selectedOneUncolored⟩) choice.selectedStable
        have hclosed : ColoredVertexSetClosed G choice.selected
            (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) := by
          intro g c v hg hv hgc hmiss
          have hincident : TreeIncidentEdge
              (ett.series.data.tree i.succ.castSucc) g := by
            have hg' := hg
            simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
              true_and] at hg'
            obtain ⟨u, hu, w, hw, hends⟩ := hg'
            refine ⟨u, hu, ?_⟩
            simp [Incident, hends]
          have hm : c ∈ TreeMissingColors choice.selected
              (ett.series.data.tree i.succ.castSucc) :=
            Finset.mem_biUnion.mpr ⟨v, hv, hmiss⟩
          have hgc' := hreverse.1 g hincident
            ⟨c, Finset.mem_union_left _ hm, hgc⟩
          exact pc hg hv (hgc'.trans hgc) (by
            rw [hreverse.2 v hv]
            exact hmiss)
        have hb : choice.edge ∈ BoundaryEdges G
            (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) := by
          obtain ⟨c, hc, hec⟩ := choice.edgeDefective
          simp only [BoundaryColorEdges, Finset.mem_filter] at hec
          exact hec.1
        refine ⟨choice.color, ?_, ?_⟩
        · simpa only [hphi, he] using choice.edgeColor
        · have hnot : choice.color ∉ TreeMissingColors choice.selected
              (ett.series.data.tree i.succ.castSucc) := by
            intro hm
            obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hm
            exact hclosed hb hv choice.edgeColor hmv
          simpa only [Tn, hi, hphi] using hnot
    | RE i pp po pc pn available cc cs ce ck cv co cd cg ad ae
        closed ordered strict =>
        have hi : i.succ = Fin.last ett.rounds := htarget.symm
        have he : f = available.edge := by
          apply Finset.singleton_injective
          exact hf.symm.trans (by simpa only [hi] using ce)
        have hphi : phi = ett.series.data.coloring i.castSucc :=
          ett.generatingColoring.trans (by simpa only [hi] using cc)
        have hcolored : ∃ c : Fin k,
            ett.series.data.coloring i.castSucc available.edge = some c := by
          let rotated := available.cycle.walk.rotate
            (Sum.inr available.edge) available.edgeOnCycle
          have hrotated : rotated.IsCycle :=
            available.cycle.isCycle.rotate available.edgeOnCycle
          have hadj := rotated.adj_snd hrotated.not_nil
          cases hv : rotated.snd with
          | inl v =>
              rw [hv] at hadj
              rcases hadj.2 with hc | hc
              · exact ⟨available.gamma, hc⟩
              · exact ⟨available.delta, hc⟩
          | inr g =>
              rw [hv] at hadj
              exact hadj.elim
        obtain ⟨c, hc⟩ := hcolored
        refine ⟨c, by simpa only [hphi, he] using hc, ?_⟩
        have hnot : c ∉ TreeMissingColors
            (ett.series.data.coloring i.castSucc)
            (ett.series.data.tree i.succ.castSucc) := by
          intro hm
          obtain ⟨v, hv, hmv⟩ := Finset.mem_biUnion.mp hm
          exact pc available.edgeBoundary hv hc hmv
        simpa only [Tn, hi, hphi] using hnot
  obtain ⟨seedColor, hcolor, hnotMissing⟩ := hseedColor
  refine ⟨gamma, hpairs', hd, ?_, fun h => (hnonPEJ h).elim⟩
  intro eta heta
  apply Finset.disjoint_left.mpr
  intro c hcg hcs
  have hcs' : c ∈ Finset.univ.filter (fun c =>
      ∃ r : Fin J.length, Tn.length ≤ r.val ∧
        r.val < min (HierarchyFirstMissingPosition phi J eta).val J.length ∧
          phi (J.edge r) = some c) := by
    unfold HierarchySegmentColors at hcs
    dsimp only at hcs
    rw [hterminal] at hcs
    simpa only [HierarchyStarredStage, Fin.cases_zero, hcore] using hcs
  obtain ⟨_, r, hlo, hhi, hc⟩ := Finset.mem_filter.mp hcs'
  obtain ⟨hlen, hinitial, hedge⟩ := hadjoin
  change J.length = Tn.length + 1 at hlen
  have hr : r = Fin.cast hlen.symm (Fin.last Tn.length) := by
    apply Fin.ext
    have := r.isLt
    simp only [Fin.val_cast, Fin.val_last]
    omega
  rw [hr, hedge, hcolor] at hc
  have hec : seedColor = c := Option.some.inj hc
  exact hnotMissing (hec.symm ▸ (hpairs' eta heta).2 hcg)

theorem AlgorithmFiveFiveInitialGoodHierarchy {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (J : TreeSequence G e0)
    (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett phi J)
    (baseJ : HierarchyBase corrJ.replacementETT phi)
    (KJ : TashkinovHierarchy corrJ.replacementETT baseJ)
    (hbaseCore : baseJ.core = base.core)
    (hbaseClosure : baseJ.closure = base.closure)
    (hzero : KJ.dividerCount = 0)
    (_ : KJ.stage 0 =
      ett.series.data.tree (Fin.last ett.rounds).castSucc)
    (hseed :
      ((ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.PE ∧ J = base.core) ∨
        ((ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.SE ∨
            ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.RE) ∧
          ∃ f : E,
            ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f J)))
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (hparallelFacts :
      ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        (∃ alpha : Fin k,
          alpha ∈ TreeMissingColors phi base.core ∧
            ¬ TreeColorSetClosed G phi base.core {alpha}) ∧
        TreeColorSetClosed G phi base.core
          (TreeMissingColors phi
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
            TreeMissingColors phi base.closure) ∧
        4 ≤ (TreeMissingColors phi
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
            TreeMissingColors phi base.closure).card) :
    ∃ goodJ : GoodHierarchy KJ,
      HierarchyStageMissingColors KJ (Fin.last KJ.dividerCount) =
        TreeMissingColors phi
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∧
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE →
        ¬ TreeColorSetMinusClosed G phi base.core
            ((HierarchyStoredColorsAt KJ
              (Fin.last KJ.dividerCount)).biUnion
                (goodJ.gamma (Fin.last KJ.dividerCount))) ∧
          4 ≤ ((TreeMissingColors phi
                (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∩
              TreeMissingColors phi base.closure) \
            (HierarchyStoredColorsAt KJ
              (Fin.last KJ.dividerCount)).biUnion
                (goodJ.gamma (Fin.last KJ.dividerCount))).card) := by
  classical
  let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
  have htransport :
    ∀ (n : ℕ) (s : TashkinovSeries G k n e0 corrJ.replacementInput), n = ett.rounds → HEq s
        corrJ.replacementSeries → s.data.tree (Fin.last n).castSucc = Tn ∧ s.data.kind (Fin.last
        n) = ett.series.data.kind (Fin.last ett.rounds) := by
    intro n s hn hs
    subst n
    have hs' : s = corrJ.replacementSeries := eq_of_heq hs
    subst s
    refine ⟨?_, corrJ.extensionKindsAgree (Fin.last ett.rounds)⟩
    let i : Fin ett.rounds := ⟨ett.rounds - 1, by
      have := ett.roundsPositive
      omega⟩
    have hi : i.succ = Fin.last ett.rounds := by
      apply Fin.ext
      dsimp [i]
      have := ett.roundsPositive
      omega
    simpa only [hi] using corrJ.ladderTreesAgree i
  obtain ⟨htree, hkind⟩ := htransport corrJ.replacementETT.rounds
    corrJ.replacementETT.series corrJ.rungAgreement corrJ.seriesPresentation
  have hlargeJ : 2 * corrJ.replacementETT.rounds + 11 ≤
      (TreeMissingColors phi
        (corrJ.replacementETT.series.data.tree
          (Fin.last corrJ.replacementETT.rounds).castSucc)).card := by
    rw [htree, corrJ.rungAgreement]
    exact hlarge
  have hindex : ∀ j : Fin (KJ.dividerCount + 1), j = 0 := by
    intro j
    apply Fin.ext
    have := j.isLt
    simp only [Fin.val_zero]
    omega
  have hmissing : ∀ j : Fin (KJ.dividerCount + 1),
      HierarchyStageMissingColors KJ j = TreeMissingColors phi Tn := by
    intro j
    rw [hindex j]
    simpa only [HierarchyStageMissingColors, Fin.cases_zero] using
      congrArg (TreeMissingColors phi) htree
  have hterminal : KJ.stage (0 : Fin (KJ.dividerCount + 1)).succ = J := by
    have hi : (0 : Fin (KJ.dividerCount + 1)).succ =
        Fin.last (KJ.dividerCount + 1) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_zero, Fin.val_last]
      omega
    rw [hi]
    exact KJ.terminalStage
  obtain ⟨gamma, hpairs, hdisjoint, havoid, hparallel⟩ :
      ∃ gamma : Fin k → Finset (Fin k),
        (∀ eta, eta ∈ HierarchyStoredColorsAt KJ 0 →
          (gamma eta).card = 2 ∧ gamma eta ⊆ TreeMissingColors phi Tn) ∧
        (∀ eta theta, eta ∈ HierarchyStoredColorsAt KJ 0 →
          theta ∈ HierarchyStoredColorsAt KJ 0 → eta ≠ theta →
          Disjoint (gamma eta) (gamma theta)) ∧
        (∀ eta, eta ∈ HierarchyStoredColorsAt KJ 0 →
          Disjoint (gamma eta) (HierarchySegmentColors KJ 0 eta)) ∧
        (corrJ.replacementETT.series.data.kind
            (Fin.last corrJ.replacementETT.rounds) =
            some TashkinovExtensionKind.PE →
          ¬ TreeColorSetMinusClosed G phi baseJ.core
              ((HierarchyStoredColorsAt KJ 0).biUnion gamma) ∧
            4 ≤ ((TreeMissingColors phi
                (corrJ.replacementETT.series.data.tree
                  (Fin.last corrJ.replacementETT.rounds).castSucc) ∩
              TreeMissingColors phi baseJ.closure) \
                (HierarchyStoredColorsAt KJ 0).biUnion gamma).card) := by
    by_cases hPE : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE
    · have hPEJ := hkind.trans hPE
      obtain ⟨hnc, hcc, hfour⟩ := hparallelFacts hPE
      obtain ⟨gamma, hpairs, hd, hn, hf⟩ := GoodHierarchyInitialPairsPE KJ
        hPEJ hlargeJ (by simpa only [hbaseCore] using hnc)
        (by simpa only [htree, hbaseCore, hbaseClosure] using hcc)
        (by simpa only [htree, hbaseClosure] using hfour)
      have hJ : J = base.core := by
        rcases hseed with h | h
        · exact h.2
        · rcases h.1 with h | h <;> rw [hPE] at h <;> cases h
      have hstar : HierarchyStarredStage KJ 0 = J := by
        simpa only [HierarchyStarredStage, Fin.cases_zero, hbaseCore] using hJ.symm
      refine ⟨gamma, ?_, hd, ?_, fun _ => ⟨hn, hf⟩⟩
      · simpa only [htree] using hpairs
      · intro eta heta
        apply Finset.disjoint_left.mpr
        intro c hcg hcs
        obtain ⟨_, r, hlo, hhi, hc⟩ := Finset.mem_filter.mp hcs
        change (HierarchyStarredStage KJ 0).length ≤ r.val at hlo
        rw [hstar] at hlo
        have hr : r.val < J.length := by
          simpa only [hterminal] using r.isLt
        omega
    · exact @AlgorithmFiveFiveInitialGoodHierarchy_branch_196 V E inferInstance inferInstance
        inferInstance inferInstance G k e0 input T phi ett base J corrJ baseJ KJ hbaseCore (by
        assumption) hseed htree hkind hlargeJ hterminal hPE
  let goodJ : GoodHierarchy KJ := {
    gamma := fun _ => gamma
    twoColors := by
      intro j eta heta
      rw [hindex j] at heta
      exact (hpairs eta heta).1
    avoidance := by
      intro j eta heta c hc
      rw [hindex j] at heta ⊢
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, ?_⟩
      · rw [hmissing]
        exact (hpairs eta heta).2 hc
      · exact fun hs => Finset.disjoint_left.mp (havoid eta heta) hc hs
    disjointPairs := by
      intro j eta theta heta htheta hne
      rw [hindex j] at heta htheta
      exact hdisjoint eta theta heta htheta hne
    uniqueRefresh := by
      intro i
      have := i.isLt
      omega
    parallelBase := hparallel
    minusClosed := by
      intro i
      have := i.isLt
      omega }
  refine ⟨goodJ, hmissing _, ?_⟩
  intro hPE
  have hp := hparallel (hkind.trans hPE)
  simpa only [goodJ, hindex (Fin.last KJ.dividerCount), htree,
    hbaseCore, hbaseClosure] using hp

end GoldbergSeymour

end
