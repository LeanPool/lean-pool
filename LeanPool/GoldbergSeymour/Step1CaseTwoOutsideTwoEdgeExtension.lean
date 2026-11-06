/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdgeVertexSet

public import LeanPool.GoldbergSeymour.BoundaryMissingColorAugmentation
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyCommonOriginalBaseTransport
public import LeanPool.GoldbergSeymour.GoodHierarchySameDividerReconstruction
public import LeanPool.GoldbergSeymour.GoodHierarchySameDividerTransport
public import LeanPool.GoldbergSeymour.MaximumProperty
public import LeanPool.GoldbergSeymour.ModColoring
public import LeanPool.GoldbergSeymour.RestrictedAugmentationCorrespondingEndpoint

/-!
# Step1Case Two Outside Two Edge Extension

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_havoid_232.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi mu : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (C : TreeSequence G e0) (corrC : CorrespondingExtendedTashkinovTree G k e0
        ett mu C) (baseC : HierarchyBase corrC.replacementETT mu) (KC : TashkinovHierarchy
        corrC.replacementETT baseC) (goodC : GoodHierarchy KC) (beta _ : Fin k), beta ∉
        (HierarchyStoredColorsAt KC (Fin.last KC.dividerCount)).biUnion (goodC.gamma (Fin.last
        KC.dividerCount)) →
    ∀ (f₁ f₂ : E), f₁ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C) beta → f₂ ∈
        BoundaryColorEdges G mu (TreeSequenceVertexSet C) beta →
    ∀ (J₁ : TreeSequence G e0), TreeSequenceAdjoinEdge C f₁ J₁ →
    ∀ (J : TreeSequence G e0), TreeSequenceAdjoinEdge J₁ f₂ J → TashkinovAugmentationSequence mu C
        J →
    ∀ (corrJ : CorrespondingExtendedTashkinovTree G k e0 ett mu J) (baseJ : HierarchyBase
        corrJ.replacementETT mu) (_ : TashkinovHierarchy corrJ.replacementETT baseJ),
    ∀ eta ∈ HierarchyStoredColorsAt KC (Fin.last KC.dividerCount), Disjoint (goodC.gamma (Fin.last
        KC.dividerCount) eta) ({c : Fin k |
    ∃ (r : Fin J.length), (HierarchyStarredStage KC (Fin.last KC.dividerCount)).length ≤ (↑r : ℕ)
        ∧ (↑r : ℕ) < min (↑(HierarchyFirstMissingPosition mu J eta) : ℕ) J.length ∧ mu (J.edge r)
        = some c} : Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi mu ett C corrC baseC KC goodC beta gamma hbetaReserved f₁
      f₂ hf₁ hf₂ J₁ had₁ J had₂ hJU corrJ baseJ KJ eta heta
  apply Finset.disjoint_left.mpr
  intro c hcG hcSeg
  rcases (Finset.mem_filter.mp hcSeg).2 with ⟨r, hlo, hhi, hcol⟩
  have hprefix : TreeSequenceInitialSegment C J :=
    TashkinovAugmentationSequenceInitialSegment mu C J hJU
  have hcut := HierarchyFirstMissingPositionPrefixCutoff mu C J hprefix eta
    C.length le_rfl
  by_cases hsmall : r.val < C.length
  · let q : Fin C.length := ⟨r.val, hsmall⟩
    have hqlo : (HierarchyStarredStage KC (Fin.last KC.dividerCount)).length ≤ q.val := by
      simpa [q] using hlo
    have hqhi : q.val < min (HierarchyFirstMissingPosition mu C eta).val C.length := by
      have hpJ : r.val < (HierarchyFirstMissingPosition mu J eta).val := by omega
      rw [hcut]
      exact (lt_min_iff).2 ⟨hpJ, hsmall⟩
    have hqcol : mu (C.edge q) = some c := by
      have hedge := hprefix.2.2 q
      rw [← hedge]
      simpa [q] using hcol
    have hCseg : c ∈ HierarchySegmentColors KC (Fin.last KC.dividerCount) eta := by
      unfold HierarchySegmentColors
      have hterm : KC.stage (Fin.last KC.dividerCount).succ = C := by
        convert KC.terminalStage using 1
        apply congrArg KC.stage
        apply Fin.ext
        simp
      rw [hterm]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨q, hqlo, hqhi, hqcol⟩
    have havo := goodC.avoidance (Fin.last KC.dividerCount) eta heta hcG
    exact (Finset.mem_sdiff.mp havo).2 hCseg
  · have hlen₁ := had₁.1
    have hlen₂ := had₂.1
    have hlenJ : J.length = C.length + 2 := by omega
    have hr : r.val = C.length ∨ r.val = C.length + 1 := by omega
    rcases hr with hr | hr
    · have he : J.edge r = f₁ := by
        have hlast := had₁.2.2
        let j₁ : Fin J₁.length := Fin.cast hlen₁.symm (Fin.last C.length)
        have hlastJ : J.edge
            (Fin.castLE (by omega) j₁) = f₁ := by
          have hinit₂ := had₂.2.1
          calc
            J.edge (Fin.castLE (by omega) j₁) = J₁.edge j₁ := hinit₂.2.2 j₁
            _ = f₁ := hlast
        have hridx : r = Fin.castLE (by omega)
            j₁ := by
          apply Fin.ext
          exact hr.trans (by simp [j₁])
        rw [hridx]
        exact hlastJ
      rw [he] at hcol
      have hcolor : mu f₁ = some beta := (Finset.mem_filter.mp hf₁).2
      have hcb : c = beta := Option.some.inj (hcol.symm.trans hcolor)
      subst c
      have hbad : beta ∈ (HierarchyStoredColorsAt KC
          (Fin.last KC.dividerCount)).biUnion
            (goodC.gamma (Fin.last KC.dividerCount)) :=
        Finset.mem_biUnion.mpr ⟨eta, heta, hcG⟩
      exact hbetaReserved hbad
    · have he : J.edge r = f₂ := by
        have hlast := had₂.2.2
        have hlastJ : J.edge (Fin.cast hlen₂.symm (Fin.last J₁.length)) = f₂ := hlast
        have hridx : r = Fin.cast hlen₂.symm (Fin.last J₁.length) := by
          apply Fin.ext
          rw [hr]
          simp only [Fin.val_cast, Fin.val_last]
          exact hlen₁.symm
        rw [hridx]
        exact hlastJ
      rw [he] at hcol
      have hcolor : mu f₂ = some beta := (Finset.mem_filter.mp hf₂).2
      have hcb : c = beta := Option.some.inj (hcol.symm.trans hcolor)
      subst c
      have hbad : beta ∈ (HierarchyStoredColorsAt KC
          (Fin.last KC.dividerCount)).biUnion
            (goodC.gamma (Fin.last KC.dividerCount)) :=
        Finset.mem_biUnion.mpr ⟨eta, heta, hcG⟩
      exact hbetaReserved hbad

private theorem helper_terminalTreeEq_322.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi mu : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (C : TreeSequence G e0) (corrC : CorrespondingExtendedTashkinovTree G k e0
        ett mu C) (baseC : HierarchyBase corrC.replacementETT mu) (_ : TashkinovHierarchy
        corrC.replacementETT baseC) (J : TreeSequence G e0) (corrJ :
        CorrespondingExtendedTashkinovTree G k e0 ett mu J) (baseJ : HierarchyBase
        corrJ.replacementETT mu) (_ : TashkinovHierarchy corrJ.replacementETT baseJ)
        {U : TreeSequence G e0} (corr : CorrespondingExtendedTashkinovTree G k e0 ett mu U),
        corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by
  classical
  intro V E _ _ _ _ G k e0 input T phi mu ett C corrC baseC KC J corrJ baseJ KJ U corr
  let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds e0
      corr.replacementInput :=
    cast (congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput)
      corr.rungAgreement.symm) corr.replacementSeries
  have castTree {a b : ℕ} (h : a = b)
      (s : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 2)) :
      (cast (congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput) h)
        s).data.tree i = s.data.tree (Fin.cast (congrArg (fun n => n + 2) h.symm) i) := by
    cases h
    rfl
  have hseries : corr.replacementETT.series = replacementSeries := by
    exact ((cast_eq_iff_heq
      (e := congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput)
        corr.rungAgreement.symm)
      (a := corr.replacementSeries) (a' := corr.replacementETT.series)).2
      corr.seriesPresentation.symm).symm
  let terminalIndex : Fin corr.replacementETT.rounds :=
    Fin.cast corr.rungAgreement.symm
      ⟨ett.rounds - 1, by have hp := ett.roundsPositive; omega⟩
  have htree : corr.replacementETT.series.data.tree terminalIndex.succ.castSucc =
      ett.series.data.tree (Fin.last ett.rounds).castSucc := by
    rw [hseries]
    calc
      replacementSeries.data.tree terminalIndex.succ.castSucc =
          corr.replacementSeries.data.tree
            (Fin.cast (congrArg (fun n => n + 2) corr.rungAgreement)
              terminalIndex.succ.castSucc) :=
        by simpa [replacementSeries] using
          (castTree corr.rungAgreement.symm corr.replacementSeries
            terminalIndex.succ.castSucc)
      _ = ett.series.data.tree (Fin.last ett.rounds).castSucc := by
        convert corr.ladderTreesAgree (Fin.cast corr.rungAgreement terminalIndex) using 1
        · congr 1
        · congr 1
          apply Fin.ext
          have hp := ett.roundsPositive
          simp [terminalIndex, Nat.sub_add_cancel hp]
  have hi : (Fin.last corr.replacementETT.rounds).castSucc =
      terminalIndex.succ.castSucc := by
    apply Fin.ext
    have hp := ett.roundsPositive
    simp only [Fin.val_castSucc, Fin.val_last, Fin.cast_mk, Fin.succ_mk, Nat.sub_add_cancel hp,
        Fin.castSucc_mk,
  terminalIndex]
    exact corr.rungAgreement
  rw [hi]
  exact htree

lemma Step1CaseTwoOutsideTwoEdgeExtension {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi mu : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett)
    (C : TreeSequence G e0)
    (corrC : CorrespondingExtendedTashkinovTree G k e0 ett mu C)
    (baseC : HierarchyBase corrC.replacementETT mu)
    (KC : TashkinovHierarchy corrC.replacementETT baseC)
    (goodC : GoodHierarchy KC)
    (hmod : ModColoring ett mu)
    (_ : MaximumProperty corrC.replacementETT)
    (_ :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence mu
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) C) ∨
        ((ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.SE ∨
            ett.series.data.kind (Fin.last ett.rounds) =
              some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (seed : TreeSequence G e0),
            ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed ∧
            TashkinovAugmentationSequence mu seed C))
    (hlargeC : 2 * corrC.replacementETT.rounds + 11 ≤
      (TreeMissingColors mu
        (corrC.replacementETT.series.data.tree
          (Fin.last corrC.replacementETT.rounds).castSucc)).card)
    (beta gamma : Fin k)
    (hgammaReserved : gamma ∉ (HierarchyStoredColorsAt KC
      (Fin.last KC.dividerCount)).biUnion
        (goodC.gamma (Fin.last KC.dividerCount)))
    (hbetaReserved : beta ∉ (HierarchyStoredColorsAt KC
      (Fin.last KC.dividerCount)).biUnion
        (goodC.gamma (Fin.last KC.dividerCount)))
    (b₁ b₂ b₃ : V) (f₁ f₂ : E)
    (hbetaMissing : beta ∈ MissingColors G mu b₃)
    (hf₁ : f₁ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C) beta)
    (hf₂ : f₂ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C) beta)
    (_ : Incident G b₁ f₁) (_ : Incident G b₂ f₂)
    (houtsideDistinct : ∀ u₁ u₂, Incident G u₁ f₁ →
      u₁ ∉ TreeSequenceVertexSet C → Incident G u₂ f₂ →
      u₂ ∉ TreeSequenceVertexSet C → u₁ ≠ u₂)
    (hb₁ : b₁ ∈ TreeSequenceVertexSet C)
    (hb₂ : b₂ ∈ TreeSequenceVertexSet C)
    (hb₃ : b₃ ∈ TreeSequenceVertexSet C) :
    ∃ (J₁ J : TreeSequence G e0) (corrJ :
      CorrespondingExtendedTashkinovTree G k e0 ett mu J) (baseJ :
      HierarchyBase corrJ.replacementETT mu) (KJ :
      TashkinovHierarchy corrJ.replacementETT baseJ) (goodJ : GoodHierarchy KJ),
    MaximumProperty corrJ.replacementETT ∧
      KJ.dividerCount = KC.dividerCount ∧
        2 * corrJ.replacementETT.rounds + 11 ≤
            (TreeMissingColors mu
                (corrJ.replacementETT.series.data.tree
                  (Fin.last corrJ.replacementETT.rounds).castSucc)).card ∧
          gamma ∉
              (HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount)).biUnion
                (goodJ.gamma (Fin.last KJ.dividerCount)) ∧
            beta ∉
                (HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount)).biUnion
                  (goodJ.gamma (Fin.last KJ.dividerCount)) ∧
              TreeSequenceAdjoinEdge C f₁ J₁ ∧
                TreeSequenceAdjoinEdge J₁ f₂ J ∧
                  (∀ v, Incident G v f₁ → v ∈ TreeSequenceVertexSet J) ∧
                    (∀ v, Incident G v f₂ → v ∈ TreeSequenceVertexSet J) ∧
                      b₁ ∈ TreeSequenceVertexSet J ∧
                        b₂ ∈ TreeSequenceVertexSet J ∧ b₃ ∈ TreeSequenceVertexSet J := by
  classical
  have hb3missing : beta ∈ TreeMissingColors mu C := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨b₃, hb₃, hbetaMissing⟩
  obtain ⟨J₁, had₁, haug₁, _⟩ :=
    BoundaryMissingColorAugmentation G k e0 mu C beta f₁ hf₁ hb3missing
  have hends₁ : ∃ x y, x ∈ TreeSequenceVertexSet C ∧
      y ∉ TreeSequenceVertexSet C ∧ G.ends f₁ = s(x, y) := by
    simp only [BoundaryColorEdges, BoundaryEdges, Finset.mem_filter,
      Finset.mem_univ, true_and] at hf₁
    rcases hf₁.1 with ⟨x, hx, y, hy, hxy⟩
    refine ⟨x, y, hx, hy, ?_⟩
    simpa using hxy
  obtain ⟨x₁, y₁, hx₁, hy₁, hxy₁⟩ := hends₁
  have adjoin_vertex_set (A B : TreeSequence G e0) (f : E) (x y : V)
      (hxy : G.ends f = s(x, y))
      (hyA : y ∉ TreeSequenceVertexSet A)
      (hAB : TreeSequenceAdjoinEdge A f B) :
      TreeSequenceVertexSet B = insert y (TreeSequenceVertexSet A) := by
    exact @TreeSequenceAdjoinEdge.vertexSet_eq_insert (@V) (@E) inferInstance (@G) (@e0) (@A)
        (@B) (@f) (@x)
        (@y) (@hxy) (@hyA) (@hAB)
  have hJ1vertices : TreeSequenceVertexSet J₁ =
      insert y₁ (TreeSequenceVertexSet C) :=
    adjoin_vertex_set C J₁ f₁ x₁ y₁ hxy₁ hy₁ had₁
  have hboundary₂ : f₂ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet J₁) beta := by
    simp only [BoundaryColorEdges, BoundaryEdges, Finset.mem_filter,
      Finset.mem_univ, true_and] at hf₂ ⊢
    rcases hf₂.1 with ⟨x₂, hx₂, y₂, hy₂, hxy₂⟩
    have hy₂J₁ : y₂ ∉ TreeSequenceVertexSet J₁ := by
      rw [hJ1vertices]
      simp only [Finset.mem_insert, not_or]
      refine ⟨?_, hy₂⟩
      intro heq
      apply (houtsideDistinct y₁ y₂ (by
        change y₁ ∈ G.ends f₁
        rw [hxy₁]
        simp) hy₁ (by
        change y₂ ∈ G.ends f₂
        rw [hxy₂]
        simp) hy₂) heq.symm
    refine ⟨?_, hf₂.2⟩
    exact ⟨x₂, (by rw [hJ1vertices]; exact Finset.mem_insert_of_mem hx₂),
      y₂, hy₂J₁, hxy₂⟩
  have hb3missingJ₁ : beta ∈ TreeMissingColors mu J₁ := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    rw [hJ1vertices]
    exact ⟨b₃, Finset.mem_insert_of_mem hb₃, hbetaMissing⟩
  obtain ⟨J, had₂, haug₂, _⟩ :=
    BoundaryMissingColorAugmentation G k e0 mu J₁ beta f₂ hboundary₂ hb3missingJ₁
  have hJU : TashkinovAugmentationSequence mu C J := by
    exact Relation.ReflTransGen.head haug₁ (Relation.ReflTransGen.single haug₂)
  obtain ⟨corrJ, hMPCJ⟩ :=
    RestrictedAugmentationCorrespondingEndpoint G k e0 input T phi mu ett
      hmod hMP C J corrC hJU
  obtain ⟨baseJ, hcore, hclosure, hsupport⟩ :=
    GoodHierarchyCommonOriginalBaseTransport G k e0 input T phi mu ett C J
      corrC baseC corrJ
  obtain ⟨KJ, hcount, hstages, hdividers⟩ :=
    GoodHierarchySameDividerReconstruction G k e0 input T phi mu ett C J
      corrC baseC KC corrJ baseJ hcore hJU
  have havoid := @helper_havoid_232 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@mu) (@ett) (@C) (@corrC) (@baseC) (@KC)
      (@goodC) (@beta) (@gamma) (@hbetaReserved) (@f₁) (@f₂) (@hf₁) (@hf₂) (@J₁) (@had₁) (@J)
      (@had₂) (@hJU) (@corrJ) (@baseJ) (@KJ)
  obtain ⟨goodJ, hgamma⟩ :=
    GoodHierarchySameDividerTransport G k e0 input T phi mu ett C J corrC baseC
      KC goodC corrJ baseJ hcore hclosure KJ hcount hstages hJU havoid
  have terminalTreeEq := @helper_terminalTreeEq_322 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@mu) (@ett) (@C) (@corrC)
      (@baseC) (@KC) (@J) (@corrJ) (@baseJ) (@KJ)
  have hlargeJ : 2 * corrJ.replacementETT.rounds + 11 ≤
      (TreeMissingColors mu (corrJ.replacementETT.series.data.tree
        (Fin.last corrJ.replacementETT.rounds).castSucc)).card := by
    calc
      2 * corrJ.replacementETT.rounds + 11 =
          2 * corrC.replacementETT.rounds + 11 := by
            rw [corrJ.rungAgreement, corrC.rungAgreement]
      _ ≤ (TreeMissingColors mu (corrC.replacementETT.series.data.tree
          (Fin.last corrC.replacementETT.rounds).castSucc)).card := hlargeC
      _ = (TreeMissingColors mu (corrJ.replacementETT.series.data.tree
          (Fin.last corrJ.replacementETT.rounds).castSucc)).card := by
            rw [terminalTreeEq corrC, terminalTreeEq corrJ]
  have hstoredLast : HierarchyStoredColorsAt KJ (Fin.last KJ.dividerCount) =
      HierarchyStoredColorsAt KC (Fin.last KC.dividerCount) := by
    have h := (hstages (Fin.last KJ.dividerCount)).2.2.1
    simpa using h
  have hgammaLast : ∀ eta : Fin k,
      goodJ.gamma (Fin.last KJ.dividerCount) eta =
        goodC.gamma (Fin.last KC.dividerCount) eta := by
    intro eta
    simpa using hgamma (Fin.last KJ.dividerCount) eta
  have hbetaJ : beta ∉ (HierarchyStoredColorsAt KJ
      (Fin.last KJ.dividerCount)).biUnion (goodJ.gamma (Fin.last KJ.dividerCount)) := by
    intro hc
    rcases Finset.mem_biUnion.mp hc with ⟨eta, heta, hgammaEta⟩
    apply hbetaReserved
    apply Finset.mem_biUnion.mpr
    refine ⟨eta, hstoredLast ▸ heta, ?_⟩
    simpa only [hgammaLast eta] using hgammaEta
  have hgammaJ : gamma ∉ (HierarchyStoredColorsAt KJ
      (Fin.last KJ.dividerCount)).biUnion (goodJ.gamma (Fin.last KJ.dividerCount)) := by
    intro hc
    rcases Finset.mem_biUnion.mp hc with ⟨eta, heta, hgammaEta⟩
    apply hgammaReserved
    apply Finset.mem_biUnion.mpr
    refine ⟨eta, hstoredLast ▸ heta, ?_⟩
    simpa only [hgammaLast eta] using hgammaEta
  have hprefixCJ : TreeSequenceInitialSegment C J :=
    TashkinovAugmentationSequenceInitialSegment mu C J hJU
  have hsubsetCJ : TreeSequenceVertexSet C ⊆ TreeSequenceVertexSet J := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    refine ⟨Fin.castLE (Nat.succ_le_succ hprefixCJ.1) i, ?_⟩
    exact hprefixCJ.2.1 i
  have hends₂ : ∃ x₂ y₂, x₂ ∈ TreeSequenceVertexSet C ∧
      y₂ ∉ TreeSequenceVertexSet C ∧ G.ends f₂ = s(x₂, y₂) := by
    simp only [BoundaryColorEdges, BoundaryEdges, Finset.mem_filter,
      Finset.mem_univ, true_and] at hf₂
    rcases hf₂.1 with ⟨x, hx, y, hy, hxy⟩
    refine ⟨x, y, hx, hy, ?_⟩
    simpa using hxy
  obtain ⟨x₂, y₂, hx₂, hy₂, hxy₂⟩ := hends₂
  have hy₂J₁ : y₂ ∉ TreeSequenceVertexSet J₁ := by
    rw [hJ1vertices]
    simp only [Finset.mem_insert, not_or]
    refine ⟨?_, hy₂⟩
    intro heq
    exact (houtsideDistinct y₁ y₂ (by
      change y₁ ∈ G.ends f₁
      rw [hxy₁]
      simp) hy₁ (by
      change y₂ ∈ G.ends f₂
      rw [hxy₂]
      simp) hy₂) heq.symm
  have hJvertices : TreeSequenceVertexSet J =
      insert y₂ (TreeSequenceVertexSet J₁) :=
    adjoin_vertex_set J₁ J f₂ x₂ y₂ hxy₂
      hy₂J₁ had₂
  have hf₁J : ∀ v, Incident G v f₁ → v ∈ TreeSequenceVertexSet J := by
    intro v hv
    have hv' : v ∈ G.ends f₁ := hv
    rw [hxy₁] at hv'
    rcases (by simpa only [Sym2.mem_iff] using hv') with h | h
    · subst v
      simp [hJvertices, hJ1vertices, hx₁]
    · rw [hJvertices, hJ1vertices]
      subst v
      simp
  have hf₂J : ∀ v, Incident G v f₂ → v ∈ TreeSequenceVertexSet J := by
    intro v hv
    have hv' : v ∈ G.ends f₂ := hv
    rw [hxy₂] at hv'
    rcases (by simpa only [Sym2.mem_iff] using hv') with h | h
    · subst v
      rw [hJvertices]
      exact Finset.mem_insert_of_mem
        (by rw [hJ1vertices]; exact Finset.mem_insert_of_mem hx₂)
    · rw [hJvertices]
      subst v
      simp
  exact ⟨J₁, J, corrJ, baseJ, KJ, goodJ, hMPCJ, hcount, hlargeJ,
    hgammaJ, hbetaJ, had₁, had₂, hf₁J, hf₂J,
    hsubsetCJ hb₁, hsubsetCJ hb₂, hsubsetCJ hb₃⟩

end GoldbergSeymour

end
