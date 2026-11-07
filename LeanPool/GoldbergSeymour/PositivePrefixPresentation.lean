/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyLEMStable
public import LeanPool.GoldbergSeymour.GoodHierarchyPrefixRepackage

/-!
# P2716_T1_Positive Prefix Presentation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2716_T1_PositivePrefixPresentation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (hlarge : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (alpha theta : Fin k)
    (hrecolor : OutsideKempeRecoloring T phi sigma alpha theta)
    (hd : 0 < H.dividerCount) :
    ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma
        (HierarchyStarredStage H (Fin.last H.dividerCount)),
      MaximumProperty corr.replacementETT ∧
      ∃ basePrefix : HierarchyBase corr.replacementETT sigma,
        ∃ K : TashkinovHierarchy corr.replacementETT basePrefix,
          ∃ goodPrefix : GoodHierarchy K,
            K.dividerCount = H.dividerCount - 1 ∧
            2 * corr.replacementETT.rounds + 11 ≤
              (TreeMissingColors sigma
                (corr.replacementETT.series.data.tree
                  (Fin.last corr.replacementETT.rounds).castSucc)).card ∧
            TreeColorSetMinusClosed G sigma
              (HierarchyStarredStage H (Fin.last H.dividerCount))
              ((HierarchyTerminalStoredColors K).biUnion
                (goodPrefix.gamma (Fin.last K.dividerCount))) := by
  classical
  have starPositive :
    ∀ {input' : PartialEdgeColoring E k} {generating' psi : PartialEdgeColoring E k}
        {other : ExtendedTashkinovTree G k e0 input' T generating'} {b : HierarchyBase other psi}
        (L : TashkinovHierarchy other b) (j : Fin (L.dividerCount + 1)), 0 < j.val →
        HierarchyStarredStage L j = L.stage j.castSucc := by
    intro input' generating' psi other b L j
    refine Fin.cases ?_ ?_ j
    · intro hj
      simp at hj
    · intro i hj
      rfl
  have treeOfSeriesEq {m n : ℕ} {psi : PartialEdgeColoring E k}
      (s : TashkinovSeries G k m e0 psi)
      (t : TashkinovSeries G k n e0 psi)
      (h : m = n) (hs : HEq s t) (j : Fin (m + 2)) :
      s.data.tree j = t.data.tree (Fin.cast (congrArg (fun a => a + 2) h) j) := by
    cases h
    cases hs
    rfl
  have storedOfSeriesEq {m n : ℕ} {psi : PartialEdgeColoring E k}
      (s : TashkinovSeries G k m e0 psi)
      (t : TashkinovSeries G k n e0 psi)
      (h : m = n) (hs : HEq s t) :
      TashkinovStoredColors s.data (Fin.last m) =
        TashkinovStoredColors t.data (Fin.last n) := by
    cases h
    cases hs
    rfl
  have ladderOfCorr : ∀ {U : TreeSequence G e0}
      (c : CorrespondingExtendedTashkinovTree G k e0 ett sigma U),
      c.replacementETT.series.data.tree (Fin.last c.replacementETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    intro U c
    have ht := treeOfSeriesEq c.replacementETT.series c.replacementSeries
      c.rungAgreement c.seriesPresentation (Fin.last c.replacementETT.rounds).castSucc
    let i : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
    have hi : Fin.cast (congrArg (fun a => a + 2) c.rungAgreement)
        (Fin.last c.replacementETT.rounds).castSucc = i.succ.castSucc := by
      apply Fin.ext
      dsimp [i]
      have hr := c.rungAgreement
      omega
    have hi' : i.succ.castSucc = (Fin.last ett.rounds).castSucc := by
      apply Fin.ext
      dsimp [i]
      omega
    rw [hi] at ht
    exact ht.trans ((c.ladderTreesAgree i).trans (congrArg ett.series.data.tree hi'))
  obtain ⟨proper, one, stable, invariant, c, cMP, b, L, goodL, same, terminal⟩ :=
    HierarchyLEMStable G k e0 input T phi sigma ett hMP hpositive hlower
      base H good hproper hone alpha theta hrecolor
  have count : H.dividerCount = L.dividerCount := same.1.2.1
  have stages : HEq H.stage L.stage := same.1.2.2.1
  let r : Fin (L.dividerCount + 1) := Fin.last L.dividerCount
  have hr : 1 ≤ r.val := by dsimp [r]; omega
  have treeEq : L.stage r.castSucc =
      HierarchyStarredStage H (Fin.last H.dividerCount) := by
    have stageEq := (Fin.heq_fun_iff (congrArg (fun q => q + 2) count)).mp
      stages (Fin.last H.dividerCount).castSucc
    have indexEq : Fin.cast (congrArg (fun q => q + 2) count)
        (Fin.last H.dividerCount).castSucc = r.castSucc := by
      apply Fin.ext
      dsimp [r]
      exact count
    change H.stage (Fin.last H.dividerCount).castSucc =
      L.stage (Fin.cast (congrArg (fun q => q + 2) count)
        (Fin.last H.dividerCount).castSucc) at stageEq
    rw [indexEq] at stageEq
    exact stageEq.symm.trans (starPositive H _ (by simpa using hd)).symm
  obtain ⟨ep, epMP, epRounds, epSeries, bp, core, closure, support,
      K, kcount, kstages, positions, goodK, gammaData, minus⟩ :=
    GoodHierarchyPrefixRepackage G k e0 c.replacementInput T sigma sigma
      c.replacementETT cMP b L goodL r hr
  have hstored : HierarchyTerminalStoredColors K = HierarchyStoredColorsAt L r := by
    unfold HierarchyTerminalStoredColors HierarchyStoredColorsAt
    dsimp only
    rw [storedOfSeriesEq ep.series c.replacementETT.series epRounds epSeries]
    rw [starPositive L r (by omega)]
  have gammaEq : goodK.gamma (Fin.last K.dividerCount) =
      goodL.gamma ⟨r.val - 1, by omega⟩ := by
    funext eta
    have hdta := (gammaData ⟨r.val - 1, by omega⟩).2 eta
    have hindex : Fin.cast (by omega)
        (⟨r.val - 1, by omega⟩ : Fin r.val) = Fin.last K.dividerCount := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_last]
      exact kcount.symm
    simpa only [hindex] using hdta
  have minusK : TreeColorSetMinusClosed G sigma (L.stage r.castSucc)
      ((HierarchyTerminalStoredColors K).biUnion
        (goodK.gamma (Fin.last K.dividerCount))) := by
    rw [hstored, gammaEq]
    exact minus
  let cp : CorrespondingExtendedTashkinovTree G k e0 ett sigma (L.stage r.castSucc) :=
    { replacementInput := c.replacementInput
      replacementSeries := c.replacementSeries
      replacementETT := ep
      rungAgreement := epRounds.trans c.rungAgreement
      seriesPresentation := epSeries.trans c.seriesPresentation
      finalGeneratingColoring := c.finalGeneratingColoring
      ladderTreesAgree := c.ladderTreesAgree
      storedColorsAgree := c.storedColorsAgree
      connectingEdgesAgree := c.connectingEdgesAgree
      extensionKindsAgree := c.extensionKindsAgree
      replacementProper := c.replacementProper
      replacementOneUncolored := c.replacementOneUncolored
      replacementStable := c.replacementStable }
  have large : 2 * cp.replacementETT.rounds + 11 ≤
      (TreeMissingColors sigma (cp.replacementETT.series.data.tree
        (Fin.last cp.replacementETT.rounds).castSucc)).card := by
    rw [ladderOfCorr cp, cp.rungAgreement]
    have TnInside : TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) ⊆
        TreeSequenceVertexSet T :=
      TreeSequenceInitialSegmentVertexSetSubset ett.abovePenultimate
    have missingEq : TreeMissingColors sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) =
        TreeMissingColors phi (ett.series.data.tree (Fin.last ett.rounds).castSucc) :=
      Finset.biUnion_congr rfl (fun v hv => stable.2 v (TnInside hv))
    rw [missingEq]
    exact hlarge
  have fewer : K.dividerCount = H.dividerCount - 1 := by
    dsimp [r] at kcount
    omega
  rw [← treeEq]
  exact ⟨cp, epMP, bp, K, goodK, fewer, large, minusK⟩

end GoldbergSeymour

end
