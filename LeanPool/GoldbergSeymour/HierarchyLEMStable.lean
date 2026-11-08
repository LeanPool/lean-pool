/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyOutsideKempeStable
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.HierarchySplitter
public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColors
public import LeanPool.GoldbergSeymour.OutsideKempeGoodHierarchy
public import LeanPool.GoldbergSeymour.SameGoodHierarchy
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Hierarchy LEMStable

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hladder_156.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi), (0 : ℕ) < ett.rounds → StableColoring T (TashkinovStoredColors
        ett.series.data (Fin.last ett.rounds)) phi sigma → (
    ∀ (f : E), TreeIncidentEdge T f → sigma f = phi f) → TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) ⊆ TreeSequenceVertexSet T → (
    ∀ (f : E), TreeIncidentEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f →
        TreeIncidentEdge T f) → StableColoring (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
        (ett.series.data.coloring (Fin.last ett.rounds)) sigma := by
  classical
  intro V E _ _ _ G k e0 input T phi sigma ett hpositive hstab hfixed hsub hinc
  have hgen : ett.series.data.coloring (Fin.last ett.rounds) = phi :=
    ett.generatingColoring.symm
  constructor
  · intro f hf hx
    simpa [hgen] using hfixed f (hinc f hf)
  · intro v hv
    simpa [hgen] using hstab.2 v (hsub hv)

private theorem helper_transportSequence_234.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi), (0 : ℕ) < ett.rounds → StableColoring T (TashkinovStoredColors
        ett.series.data (Fin.last ett.rounds)) phi sigma → (
    ∀ (f : E), TreeIncidentEdge (ett.series.data.tree (Fin.last ett.rounds).castSucc) f →
        TreeIncidentEdge T f) →
    ∀ {A : TreeSequence G e0}, TashkinovAugmentationSequence phi A T →
        TashkinovAugmentationSequence sigma A T := by
  classical
  intro V E _ _ _ G k e0 input T phi sigma ett hpositive hstab hinc A hseq
  have vertexTransfer : ∀ {X Y : TreeSequence G e0},
      TashkinovAugmentation phi X Y →
      ∀ v, v ∈ TreeSequenceVertexSet X → v ∈ TreeSequenceVertexSet Y := by
    intro X Y step v member
    exact step.2.1.vertexSet_subset member
  have vertexInclusion : ∀ {X Y : TreeSequence G e0},
      TashkinovAugmentationSequence phi X Y →
      ∀ v, v ∈ TreeSequenceVertexSet X → v ∈ TreeSequenceVertexSet Y := by
    intro X Y hxy
    unfold TashkinovAugmentationSequence at hxy
    induction hxy using Relation.ReflTransGen.head_induction_on with
    | refl => intro v hv; exact hv
    | head hstep htail ih =>
      intro v hv
      rcases hstep with ⟨hlen, hsegment, c, hcolor, hmiss⟩
      exact ih v (vertexTransfer ⟨hlen, hsegment, c, hcolor, hmiss⟩ v hv)
  have segmentVertices : ∀ {X Y : TreeSequence G e0},
      TreeSequenceInitialSegment X Y →
      ∀ v, v ∈ TreeSequenceVertexSet X → v ∈ TreeSequenceVertexSet Y := by
    intro X Y segment v member
    exact segment.vertexSet_subset member
  unfold TashkinovAugmentationSequence at hseq ⊢
  induction hseq using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head X Y hstep htail ih =>
    have htailVertex := vertexInclusion htail
    rcases hstep with ⟨hlen, hsegment, c, hcolor, hmiss⟩
    refine Relation.ReflTransGen.head ?_ ih
    refine ⟨hlen, hsegment, c, ?_, ?_⟩
    · let hlast : Fin Y.length := Fin.cast hlen.symm (Fin.last X.length)
      have hcolor' : phi (Y.edge hlast) = some c := by
        dsimp [hlast]
        exact hcolor
      have hinc : TreeIncidentEdge T (Y.edge hlast) := by
        rcases Y.attaches hlast with ⟨i, hi⟩
        refine ⟨Y.vertex hlast.succ, ?_, ?_⟩
        · apply htailVertex
          simp [TreeSequenceVertexSet]
        · change Y.vertex hlast.succ ∈ G.ends (Y.edge hlast)
          rw [hi]
          exact Sym2.mem_mk_left _ _
      have heq := hstab.1 _ hinc
        ⟨c, Finset.mem_union_left _ (by
          unfold TreeMissingColors at hmiss ⊢
          rcases Finset.mem_biUnion.mp hmiss with ⟨v, hv, hvc⟩
          have hvY : v ∈ TreeSequenceVertexSet Y :=
            segmentVertices hsegment v hv
          exact Finset.mem_biUnion.mpr ⟨v, htailVertex v hvY, hvc⟩), hcolor'⟩
      exact heq.trans hcolor'
    · unfold TreeMissingColors at hmiss ⊢
      rcases Finset.mem_biUnion.mp hmiss with ⟨v, hv, hvc⟩
      have hvY : v ∈ TreeSequenceVertexSet Y := segmentVertices hsegment v hv
      refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
      rw [hstab.2 v (htailVertex v hvY)]
      exact hvc

private theorem helper_branch_346.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi), (0 : ℕ) < ett.rounds → TreeSequenceInitialSegment (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) T → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → B.length ≤ A.length → TreeSequenceInitialSegment B A) → (
    ∀ (coloring : PartialEdgeColoring E k) (A B C : TreeSequence G e0),
        TashkinovAugmentationSequence coloring A C → TreeSequenceInitialSegment A B →
        TreeSequenceInitialSegment B C → TashkinovAugmentationSequence coloring A B) → (
    ∀ {A : TreeSequence G e0}, TashkinovAugmentationSequence phi A T →
        TashkinovAugmentationSequence sigma A T) → (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentationSequence phi A B →
        TreeSequenceInitialSegment A B) →
    ∀ (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)), ett.series.data.connectingEdges i.succ =
        ({ choice.edge } : Finset E) → ett.series.data.kind i.succ = some
        TashkinovExtensionKind.SE →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (ett.series.data.tree
        i.succ.castSucc) choice.edge adjoined → TashkinovClosure (ett.series.data.coloring i.succ)
        adjoined (ett.series.data.tree i.succ.succ) → (ett.series.data.tree
        i.succ.castSucc).length < (ett.series.data.tree i.succ.succ).length → Fin.last ett.rounds
        = i.succ → ett.series.data.kind i.succ = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma (ett.series.data.tree i.succ.castSucc) T ∨
        (ett.series.data.kind i.succ = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
        i.succ = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges i.succ = ({ f } : Finset
        E) ∧ TreeSequenceAdjoinEdge (ett.series.data.tree i.succ.castSucc) f seed ∧
        TashkinovAugmentationSequence sigma seed T := by
  classical
  intro V E _ _ _ G k e0 input T phi sigma ett hpositive hsegOuter commonSegment restrictSequence
      transportSequence sequenceSegment i choice currentEdges currentKind adjoined
      adjoinedExactly closedExtension strictExtension hindex
  have hindex2 : (Fin.last (ett.rounds + 1) : Fin (ett.rounds + 1 + 1)) =
      i.succ.succ := by
    apply Fin.ext
    have hv := congrArg Fin.val hindex
    simp at hv ⊢
    omega
  right
  refine ⟨Or.inl currentKind, choice.edge, adjoined, currentEdges,
    adjoinedExactly, ?_⟩
  have hold : TashkinovAugmentationSequence phi adjoined
      (ett.series.data.tree i.succ.succ) := by
    simpa [← hindex, ett.generatingColoring] using closedExtension.1
  have hab : TreeSequenceInitialSegment adjoined T := by
    have ha := sequenceSegment hold
    have hc : TreeSequenceInitialSegment T
        (ett.series.data.tree i.succ.succ) := by
      have hh := ett.belowFinal
      rw [hindex2] at hh
      exact hh
    rcases adjoinedExactly with ⟨hlen, hinit, hedge⟩
    have hstrict := ett.strictAbovePenultimate
    have hstrict' :
        (ett.series.data.tree i.succ.castSucc).length < T.length := by
      have hi : i.succ.castSucc = (Fin.last ett.rounds).castSucc := by
        apply Fin.ext
        simp [hindex]
      rw [hi]
      have hj : (Fin.last ett.rounds).castSucc =
          (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
        apply Fin.ext
        rfl
      rw [hj]
      exact hstrict
    exact commonSegment hc ha (by
      rcases hsegOuter with ⟨hbound, _, _⟩
      omega)
  exact transportSequence (restrictSequence phi adjoined T
    (ett.series.data.tree i.succ.succ) hold hab (by
      have hh := ett.belowFinal
      rw [hindex2] at hh
      exact hh))

private theorem helper_branch_392.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi), (0 : ℕ) < ett.rounds → TreeColoringInvariant T phi sigma →
        TreeSequenceInitialSegment (ett.series.data.tree (Fin.last ett.rounds).castSucc) T → (
    ∀ (coloring : PartialEdgeColoring E k) (A B C : TreeSequence G e0),
        TashkinovAugmentationSequence coloring A C → TreeSequenceInitialSegment A B →
        TreeSequenceInitialSegment B C → TashkinovAugmentationSequence coloring A B) → (
    ∀ {A : TreeSequence G e0}, TashkinovAugmentationSequence phi A T →
        TashkinovAugmentationSequence sigma A T) →
    ∀ (i : Fin ett.rounds), ett.series.data.kind i.succ = some TashkinovExtensionKind.PE →
        TashkinovClosure (ett.series.data.coloring i.succ) (ett.series.data.tree i.succ.castSucc)
        (ett.series.data.tree i.succ.succ) → (ett.series.data.tree i.succ.castSucc).length <
        (ett.series.data.tree i.succ.succ).length → Fin.last ett.rounds = i.succ →
        ett.series.data.kind i.succ = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma (ett.series.data.tree i.succ.castSucc) T ∨
        (ett.series.data.kind i.succ = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
        i.succ = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges i.succ = ({ f } : Finset
        E) ∧ TreeSequenceAdjoinEdge (ett.series.data.tree i.succ.castSucc) f seed ∧
        TashkinovAugmentationSequence sigma seed T := by
  classical
  intro V E _ _ _ G k e0 input T phi sigma ett hpositive _ hsegOuter restrictSequence
      transportSequence i currentKind closedExtension strictExtension hindex
  have hindex2 : (Fin.last (ett.rounds + 1) : Fin (ett.rounds + 1 + 1)) =
      i.succ.succ := by
    apply Fin.ext
    have hv := congrArg Fin.val hindex
    simp only [Fin.val_last, Fin.val_succ] at hv ⊢
    omega
  left
  refine ⟨currentKind, ?_⟩
  have hold : TashkinovAugmentationSequence phi
      (ett.series.data.tree i.succ.castSucc)
      (ett.series.data.tree i.succ.succ) := by
    simpa [← hindex, ett.generatingColoring] using closedExtension.1
  have hseg : TreeSequenceInitialSegment
      (ett.series.data.tree i.succ.castSucc) T := by
    have hh := hsegOuter
    rw [hindex] at hh
    exact hh
  have hfinal : TreeSequenceInitialSegment T
      (ett.series.data.tree i.succ.succ) := by
    have hh := ett.belowFinal
    rw [hindex2] at hh
    exact hh
  have hpart := restrictSequence phi
      (ett.series.data.tree i.succ.castSucc) T
      (ett.series.data.tree i.succ.succ) hold hseg hfinal
  exact transportSequence (by simpa [hindex] using hpart)

private theorem helper_branch_424.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi), (0 : ℕ) < ett.rounds → TreeSequenceInitialSegment (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) T → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → B.length ≤ A.length → TreeSequenceInitialSegment B A) → (
    ∀ (coloring : PartialEdgeColoring E k) (A B C : TreeSequence G e0),
        TashkinovAugmentationSequence coloring A C → TreeSequenceInitialSegment A B →
        TreeSequenceInitialSegment B C → TashkinovAugmentationSequence coloring A B) → (
    ∀ {A : TreeSequence G e0}, TashkinovAugmentationSequence phi A T →
        TashkinovAugmentationSequence sigma A T) → (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentationSequence phi A B →
        TreeSequenceInitialSegment A B) →
    ∀ (i : Fin ett.rounds) (available : RevisitingExtensionCertificate ett.series.data
        i.castSucc), ett.series.data.connectingEdges i.succ = ({ available.edge } : Finset E) →
        ett.series.data.kind i.succ = some TashkinovExtensionKind.RE →
    ∀ (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (ett.series.data.tree
        i.succ.castSucc) available.edge adjoined → TashkinovClosure (ett.series.data.coloring
        i.succ) adjoined (ett.series.data.tree i.succ.succ) → (ett.series.data.tree
        i.succ.castSucc).length < (ett.series.data.tree i.succ.succ).length → Fin.last ett.rounds
        = i.succ → ett.series.data.kind i.succ = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma (ett.series.data.tree i.succ.castSucc) T ∨
        (ett.series.data.kind i.succ = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
        i.succ = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges i.succ = ({ f } : Finset
        E) ∧ TreeSequenceAdjoinEdge (ett.series.data.tree i.succ.castSucc) f seed ∧
        TashkinovAugmentationSequence sigma seed T := by
  classical
  intro V E _ _ _ G k e0 input T phi sigma ett hpositive hsegOuter commonSegment restrictSequence
      transportSequence sequenceSegment i available currentEdges currentKind adjoined
      adjoinedExactly closedExtension strictExtension hindex
  have hindex2 : (Fin.last (ett.rounds + 1) : Fin (ett.rounds + 1 + 1)) =
      i.succ.succ := by
    apply Fin.ext
    have hv := congrArg Fin.val hindex
    simp only [Fin.val_last, Fin.val_succ] at hv ⊢
    omega
  right
  refine ⟨Or.inr currentKind, available.edge, adjoined, currentEdges,
    adjoinedExactly, ?_⟩
  have hold : TashkinovAugmentationSequence phi adjoined
      (ett.series.data.tree i.succ.succ) := by
    simpa [← hindex, ett.generatingColoring] using closedExtension.1
  have hab : TreeSequenceInitialSegment adjoined T := by
    have ha := sequenceSegment hold
    have hc : TreeSequenceInitialSegment T
        (ett.series.data.tree i.succ.succ) := by
      have hh := ett.belowFinal
      rw [hindex2] at hh
      exact hh
    rcases adjoinedExactly with ⟨hlen, hinit, hedge⟩
    have hstrict := ett.strictAbovePenultimate
    have hstrict' :
        (ett.series.data.tree i.succ.castSucc).length < T.length := by
      have hi : i.succ.castSucc = (Fin.last ett.rounds).castSucc := by
        apply Fin.ext
        simp [hindex]
      rw [hi]
      have hj : (Fin.last ett.rounds).castSucc =
          (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) := by
        apply Fin.ext
        rfl
      rw [hj]
      exact hstrict
    exact commonSegment hc ha (by
      rcases hsegOuter with ⟨hbound, _, _⟩
      omega)
  exact transportSequence (restrictSequence phi adjoined T
    (ett.series.data.tree i.succ.succ) hold hab (by
      have hh := ett.belowFinal
      rw [hindex2] at hh
      exact hh))

private theorem helper_hseries_501.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi), (0 : ℕ) < ett.rounds →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds e0
        corr.replacementInput := cast (congrArg (fun (n : ℕ) ↦ TashkinovSeries G k n e0
        corr.replacementInput) (
    by
            have := CorrespondingExtendedTashkinovTree.rungAgreement corr
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    )) corr.replacementSeries; corr.replacementETT.series = replacementSeries := by
  classical
  intro V E _ _ _ G k e0 input T phi sigma ett hpositive corr replacementSeries
  exact ((cast_eq_iff_heq
    (e := congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput)
      corr.rungAgreement.symm)
    (a := corr.replacementSeries) (a' := corr.replacementETT.series)).2
    corr.seriesPresentation.symm).symm

private theorem helper_htree_510.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi) (hpositive : (0 : ℕ) < ett.rounds) (corr :
        CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds e0
        corr.replacementInput := cast (congrArg (fun (n : ℕ) ↦ TashkinovSeries G k n e0
        corr.replacementInput) (
    by
              have := CorrespondingExtendedTashkinovTree.rungAgreement corr
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    )) corr.replacementSeries; (
    ∀ {a b : ℕ} (h : a = b) (s : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (2
        : ℕ))), (cast (congrArg (fun (n : ℕ) ↦ TashkinovSeries G k n e0 corr.replacementInput) h)
        s).data.tree i = s.data.tree (Fin.cast (
    by omega
    ) i)) → corr.replacementETT.series = replacementSeries →
    let terminalIndex : Fin corr.replacementETT.rounds := Fin.cast (
    by
                have := CorrespondingExtendedTashkinovTree.rungAgreement corr
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) (⟨ett.rounds - (1 : ℕ),
    by
                  have _ : (1 : ℕ) ≤ ett.rounds := ett.roundsPositive
                  omega
    ⟩ : Fin ett.rounds); corr.replacementETT.series.data.tree terminalIndex.succ.castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc := by
  classical
  intro V E _ _ _ G k e0 input T phi sigma ett hpositive corr replacementSeries castTree hseries
      terminalIndex
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
        simp [terminalIndex]
        omega

private theorem helper_hstored_528.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi), (0 : ℕ) < ett.rounds →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds e0
        corr.replacementInput := cast (congrArg (fun (n : ℕ) ↦ TashkinovSeries G k n e0
        corr.replacementInput) (
    by
            have := CorrespondingExtendedTashkinovTree.rungAgreement corr
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    )) corr.replacementSeries; (
    ∀ {a b : ℕ} (h : a = b) (s : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (cast (congrArg (fun (n : ℕ) ↦ TashkinovSeries G k n e0 corr.replacementInput) h)
        s).data.stored i = s.data.stored (Fin.cast (
    by omega
    ) i)) → corr.replacementETT.series = replacementSeries →
    ∀ (i : Fin (corr.replacementETT.rounds + (1 : ℕ))), corr.replacementETT.series.data.stored i =
        ett.series.data.stored (Fin.cast (
    by
            have := CorrespondingExtendedTashkinovTree.rungAgreement corr
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) i) := by
  classical
  intro V E _ _ _ G k e0 input T phi sigma ett hpositive corr replacementSeries castStored hseries i
  rw [hseries]
  exact (castStored corr.rungAgreement.symm corr.replacementSeries i).trans
    (corr.storedColorsAgree (Fin.cast (congrArg (fun n => n + 1)
      corr.rungAgreement) i))

private theorem helper_hkindEq_536.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi), (0 : ℕ) < ett.rounds →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds e0
        corr.replacementInput := cast (congrArg (fun (n : ℕ) ↦ TashkinovSeries G k n e0
        corr.replacementInput) (
    by
            have := CorrespondingExtendedTashkinovTree.rungAgreement corr
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    )) corr.replacementSeries; (
    ∀ {a b : ℕ} (h : a = b) (s : TashkinovSeries G k a e0 corr.replacementInput) (i : Fin (b + (1
        : ℕ))), (cast (congrArg (fun (n : ℕ) ↦ TashkinovSeries G k n e0 corr.replacementInput) h)
        s).data.kind i = s.data.kind (Fin.cast (
    by omega
    ) i)) → corr.replacementETT.series = replacementSeries →
    ∀ (i : Fin (corr.replacementETT.rounds + (1 : ℕ))), corr.replacementETT.series.data.kind i =
        ett.series.data.kind (Fin.cast (
    by
            have := CorrespondingExtendedTashkinovTree.rungAgreement corr
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) i) := by
  classical
  intro V E _ _ _ G k e0 input T phi sigma ett hpositive corr replacementSeries castKind hseries i
  rw [hseries]
  exact (castKind corr.rungAgreement.symm corr.replacementSeries i).trans
    (corr.extensionKindsAgree (Fin.cast (congrArg (fun n => n + 1)
      corr.rungAgreement) i))

private theorem helper_htreeFinal_544.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi) (hpositive : (0 : ℕ) < ett.rounds) (corr :
        CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    let terminalIndex : Fin corr.replacementETT.rounds := Fin.cast (
    by
            have := CorrespondingExtendedTashkinovTree.rungAgreement corr
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ) (⟨ett.rounds - (1 : ℕ),
    by have _ : (1 : ℕ) ≤ ett.rounds := ett.roundsPositive; omega
    ⟩ : Fin ett.rounds); corr.replacementETT.series.data.tree terminalIndex.succ.castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc → corr.replacementETT.series.data.tree
        (Fin.last corr.replacementETT.rounds).castSucc = ett.series.data.tree (Fin.last
        ett.rounds).castSucc := by
  classical
  intro V E _ _ _ G k e0 input T phi sigma ett hpositive corr terminalIndex htree
  have hi : (Fin.last corr.replacementETT.rounds).castSucc =
      terminalIndex.succ.castSucc := by
    apply Fin.ext
    simp [terminalIndex]
    have hr : corr.replacementETT.rounds = ett.rounds := corr.rungAgreement
    omega
  rw [hi]
  exact htree

private theorem helper_branch_563.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi), MaximumProperty ett → (0 : ℕ) < ett.rounds →
        LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good : GoodHierarchy H),
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 →
    ∀ (alpha beta : Fin k), OutsideKempeRecoloring T phi sigma alpha beta → IsProperEdgeColoring G
        sigma → IsOneEdgeUncolored sigma e0 → (ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.PE → CombinedStableColoring (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) base.closure (TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds)) phi sigma) → (ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence sigma (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) T ∨ (ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (seed : TreeSequence G e0), ett.series.data.connectingEdges (Fin.last ett.rounds) =
        ({ f } : Finset E) ∧ TreeSequenceAdjoinEdge (ett.series.data.tree (Fin.last
        ett.rounds).castSucc) f seed ∧ TashkinovAugmentationSequence sigma seed T) →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T),
    let _ : TashkinovSeries G k corr.replacementETT.rounds e0 corr.replacementInput := cast
        (congrArg (fun (n : ℕ) ↦ TashkinovSeries G k n e0 corr.replacementInput) (
    by
            have := CorrespondingExtendedTashkinovTree.rungAgreement corr
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    )) corr.replacementSeries; ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.PE →
    ∃ (corrFinal : CorrespondingExtendedTashkinovTree G k e0 ett sigma T) (_ : MaximumProperty
        corrFinal.replacementETT) (baseSigma : HierarchyBase corrFinal.replacementETT sigma) (K :
        TashkinovHierarchy corrFinal.replacementETT baseSigma) (goodSigma : GoodHierarchy K),
        SameGoodHierarchy good goodSigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi sigma ett hMP hpositive hlower base H good hproper hone
      alpha beta hrecolor hsigma honeSigma hcomb eligible corr replacementSeries hpe
  have hsplit := HierarchySplitter G k e0 input T phi sigma ett hMP
      hpositive hlower base H hpe hproper hone hsigma honeSigma
      (hcomb hpe) (by
        rcases eligible with h | h
        · exact h.2
        · rcases h.1 with hs | hr
          · exfalso
            rw [hpe] at hs
            cases hs
          · exfalso
            rw [hpe] at hr
            cases hr)
  rcases hsplit with ⟨corr', hmax', baseSigma, K, hsame⟩
  have hg : ∃ goodSigma : GoodHierarchy K,
      SameGoodHierarchy good goodSigma :=
    OutsideKempeGoodHierarchy G k e0 T phi sigma
      ett corr'.replacementETT base baseSigma H K hsame good
      hproper hone alpha beta hrecolor corr'.rungAgreement.symm
      (by
        intro i
        have hs : corr'.replacementETT.series =
            cast (congrArg (fun n => TashkinovSeries G k n e0
              corr'.replacementInput) corr'.rungAgreement.symm)
              corr'.replacementSeries := by
          exact ((cast_eq_iff_heq
            (e := congrArg (fun n => TashkinovSeries G k n e0
              corr'.replacementInput) corr'.rungAgreement.symm)
            (a := corr'.replacementSeries)
            (a' := corr'.replacementETT.series)).2
            corr'.seriesPresentation.symm).symm
        rw [hs]
        have hc := corr'.storedColorsAgree i
        have castStep {a b : ℕ} (h : a = b)
            (s : TashkinovSeries G k a e0 corr'.replacementInput)
            (j : Fin (b + 1)) :
            (cast (congrArg (fun n => TashkinovSeries G k n e0
              corr'.replacementInput) h) s).data.stored j =
              s.data.stored (Fin.cast (congrArg (fun n => n + 1) h.symm) j) := by
          cases h
          rfl
        exact hc.symm.trans
          (castStep corr'.rungAgreement.symm corr'.replacementSeries
            (Fin.cast (congrArg (fun n => n + 1) corr'.rungAgreement.symm) i)).symm)
  rcases hg with ⟨goodSigma, hsg⟩
  exact ⟨corr', hmax', baseSigma, K, goodSigma, hsg⟩

private theorem helper_branch_608.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi), (0 : ℕ) < ett.rounds →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good : GoodHierarchy H),
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 →
    ∀ (alpha beta : Fin k), OutsideKempeRecoloring T phi sigma alpha beta →
    ∀ (corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T), MaximumProperty
        corr.replacementETT → (
    ∀ (i : Fin (corr.replacementETT.rounds + (1 : ℕ))), corr.replacementETT.series.data.stored i =
        ett.series.data.stored (Fin.cast (
    by
                have :=
                  CorrespondingExtendedTashkinovTree.rungAgreement corr
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i)) → (
    ∀ (i : Fin (corr.replacementETT.rounds + (1 : ℕ))), corr.replacementETT.series.data.kind i =
        ett.series.data.kind (Fin.cast (
    by
                have :=
                  CorrespondingExtendedTashkinovTree.rungAgreement corr
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ) i)) → corr.replacementETT.series.data.tree (Fin.last corr.replacementETT.rounds).castSucc =
        ett.series.data.tree (Fin.last ett.rounds).castSucc → ¬ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.PE →
    ∃ (corrFinal : CorrespondingExtendedTashkinovTree G k e0 ett sigma T) (_ : MaximumProperty
        corrFinal.replacementETT) (baseSigma : HierarchyBase corrFinal.replacementETT sigma) (K :
        TashkinovHierarchy corrFinal.replacementETT baseSigma) (goodSigma : GoodHierarchy K),
        SameGoodHierarchy good goodSigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi sigma ett hpositive base H good hproper hone alpha beta
      hrecolor corr hmax hstored hkindEq htreeFinal hpe
  let baseSigma : HierarchyBase corr.replacementETT sigma :=
    { core := base.core
      closure := base.closure
      supportPosition := Fin.cast (congrArg (fun X => X.length + 1)
        htreeFinal.symm) base.supportPosition
      supportPositive := base.supportPositive
      terminalMissingColors := by rfl
      parallel := by
        dsimp
        intro hp
        have hnot := hkindEq (Fin.last corr.replacementETT.rounds)
        have hk : corr.replacementETT.series.data.kind
            (Fin.last corr.replacementETT.rounds) =
            ett.series.data.kind (Fin.last ett.rounds) := by
          simpa [corr.rungAgreement] using hnot
        exfalso
        exact hpe (by simpa [hk] using hp)
      nonparallel := by
        dsimp
        intro hn
        have hc := base.nonparallel hpe
        simpa [htreeFinal] using hc }
  let K : TashkinovHierarchy corr.replacementETT baseSigma :=
    { dividerCount := H.dividerCount
      stage := H.stage
      baseStage := by simpa [htreeFinal] using H.baseStage
      terminalStage := H.terminalStage
      nested := H.nested
      strict := H.strict
      dividerPosition := H.dividerPosition
      dividerPositive := H.dividerPositive
      dividerIncreasing := H.dividerIncreasing
      dividerStage := H.dividerStage
      coreInsideFirst := by simpa [baseSigma] using H.coreInsideFirst }
  have hsame : SameHierarchyStages H K := by
    dsimp [SameHierarchyStages, K, baseSigma]
    refine ⟨rfl, rfl, heq_of_eq rfl, heq_of_eq rfl, ?_, ?_⟩
    · constructor <;> intro h
      · have hnot := hkindEq (Fin.last corr.replacementETT.rounds)
        have hk : corr.replacementETT.series.data.kind
            (Fin.last corr.replacementETT.rounds) =
            ett.series.data.kind (Fin.last ett.rounds) := by
          simpa [corr.rungAgreement] using hnot
        exact hk ▸ h
      · have hnot := hkindEq (Fin.last corr.replacementETT.rounds)
        have hk : corr.replacementETT.series.data.kind
            (Fin.last corr.replacementETT.rounds) =
            ett.series.data.kind (Fin.last ett.rounds) := by
          simpa [corr.rungAgreement] using hnot
        exact hk.symm ▸ h
    · intro hp
      exact False.elim (hpe hp)
  have hg := OutsideKempeGoodHierarchy G k e0 T phi sigma
      ett corr.replacementETT base baseSigma H K hsame good
      hproper hone alpha beta hrecolor corr.rungAgreement.symm (by
        intro i
        exact (hstored (Fin.cast (congrArg (fun n => n + 1)
          corr.rungAgreement.symm) i)).symm)
  rcases hg with ⟨goodSigma, hsg⟩
  exact ⟨corr, hmax, baseSigma, K, goodSigma, hsg⟩

private theorem helper_missingEq_673.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi sigma : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T phi), (0 : ℕ) < ett.rounds → StableColoring T (TashkinovStoredColors
        ett.series.data (Fin.last ett.rounds)) phi sigma → TreeMissingColors phi T =
        TreeMissingColors sigma T := by
  classical
  intro V E _ _ _ G k e0 input T phi sigma ett hpositive hstab
  ext c
  simp only [TreeMissingColors, Finset.mem_biUnion]
  constructor <;> rintro ⟨v, hv, hc⟩
  · exact ⟨v, hv, (Finset.ext_iff.mp (hstab.2 v hv) c).mpr hc⟩
  · exact ⟨v, hv, (Finset.ext_iff.mp (hstab.2 v hv) c).mp hc⟩

private theorem helper_hi_686.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi), (0 : ℕ) < ett.rounds →
    ∀ f ∈ BoundaryEdges G (TreeSequenceVertexSet T), TreeIncidentEdge T f := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive f hbase
  unfold BoundaryEdges at hbase
  simp only [Finset.mem_filter] at hbase
  rcases hbase with ⟨_, ⟨u, hu, v, hv, he⟩⟩
  refine ⟨u, hu, ?_⟩
  change u ∈ G.ends f
  rw [he]
  exact Sym2.mem_mk_left _ _

theorem HierarchyLEMStable {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base)
    (good : GoodHierarchy H)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (alpha beta : Fin k)
    (hrecolor : OutsideKempeRecoloring T phi sigma alpha beta) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Dn := TashkinovStoredColors ett.series.data n
    IsProperEdgeColoring G sigma ∧
      IsOneEdgeUncolored sigma e0 ∧
        StableColoring T Dn phi sigma ∧
          TreeColoringInvariant T phi sigma ∧
            ∃ corr : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
              MaximumProperty corr.replacementETT ∧
                ∃ baseSigma : HierarchyBase corr.replacementETT sigma,
                  ∃ K : TashkinovHierarchy corr.replacementETT baseSigma,
                    ∃ goodSigma : GoodHierarchy K,
                      SameGoodHierarchy good goodSigma ∧
                        (TreeColorSetMinusClosed G phi T
                            ((HierarchyTerminalStoredColors H).biUnion
                              (good.gamma (Fin.last H.dividerCount))) →
                          TreeColorSetMinusClosed G sigma T
                            ((HierarchyTerminalStoredColors H).biUnion
                              (good.gamma (Fin.last H.dividerCount)))) := by
  dsimp
  have hstable := HierarchyOutsideKempeStable G k e0 input T phi sigma ett base H
    hproper hone alpha beta hrecolor
  have hdetail := OutsideKempeRecoloringStable G e0 T
    (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma alpha beta
    hproper hone hrecolor
  rcases hstable with ⟨hsigma, honeSigma, hstab, hinv, hcomb⟩
  rcases hdetail with ⟨_, _, _, _, hfixed⟩
  have hsegOuter := ett.abovePenultimate
  have hsub := hsegOuter.vertexSet_subset
  have hinc : ∀ f, TreeIncidentEdge
      (ett.series.data.tree (Fin.last ett.rounds).castSucc) f →
      TreeIncidentEdge T f := by
    intro f hf
    rcases hf with ⟨v, hv, hi⟩
    exact ⟨v, hsub hv, hi⟩
  have commonSegment := @TreeSequenceInitialSegment.of_common_extension V E G e0
  have hladder :=
    @helper_hladder_156 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@sigma) (@ett) (@hpositive) (@hstab) (@hfixed) (@hsub) (@hinc)
  have restrictSequence :=
    @TashkinovAugmentationSequenceRestrict V E inferInstance G k e0
  have transportSequence :=
    @helper_transportSequence_234 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@phi) (@sigma) (@ett) (@hpositive) (@hstab) (@hinc)
  have sequenceSegment {A B : TreeSequence G e0}
      (sequence : TashkinovAugmentationSequence phi A B) : TreeSequenceInitialSegment A B :=
    TashkinovAugmentationSequenceInitialSegment phi A B sequence
  have eligible :
      (ett.series.data.kind (Fin.last ett.rounds) =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence sigma
          (ett.series.data.tree (Fin.last ett.rounds).castSucc) T) ∨
      ((ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind (Fin.last ett.rounds) =
            some TashkinovExtensionKind.RE) ∧
        ∃ f seed,
          ett.series.data.connectingEdges (Fin.last ett.rounds) = {f} ∧
            TreeSequenceAdjoinEdge
              (ett.series.data.tree (Fin.last ett.rounds).castSucc) f seed ∧
            TashkinovAugmentationSequence sigma seed T) := by
      have hstep := ett.series.certified (Fin.last ett.rounds)
      generalize hindex : Fin.last ett.rounds = index at hstep
      cases hstep with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
        have hz : (Fin.last ett.rounds : Fin (ett.rounds + 1)) = 0 := hindex
        have hr : ett.rounds = 0 := by
          have := congrArg Fin.val hz
          simpa using this
        omega
      | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
            exact @helper_branch_346 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                (@k) (@e0) (@input) (@T) (@phi) (@sigma) (@ett) (@hpositive) (@hsegOuter)
                (@commonSegment) (@restrictSequence) (@transportSequence) (@sequenceSegment) (@i)
                (@choice) (@currentEdges) (@currentKind) (@adjoined) (@adjoinedExactly)
                (@closedExtension) (@strictExtension) (@hindex)
      | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        gamma gammaRule secondStable secondStableProper secondStableOneUncolored
        secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_392 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@e0) (@input) (@T) (@phi) (@sigma) (@ett) (@hpositive) (by assumption)
              (@hsegOuter) (@restrictSequence) (@transportSequence) (@i) (@currentKind)
              (@closedExtension) (@strictExtension) (@hindex)
      | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
            exact @helper_branch_424 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                (@k) (@e0) (@input) (@T) (@phi) (@sigma) (@ett) (@hpositive) (@hsegOuter)
                (@commonSegment) (@restrictSequence) (@transportSequence) (@sequenceSegment) (@i)
                (@available) (@currentEdges) (@currentKind) (@adjoined) (@adjoinedExactly)
                (@closedExtension) (@strictExtension) (@hindex)
  have hmod : ModColoring ett sigma := Td G k e0 input T phi ett hMP
    hpositive hlower sigma hsigma honeSigma hladder
  have hcand := hmod.2.2 T hsegOuter ett.strictAbovePenultimate eligible
  rcases hcand with ⟨corr⟩
  have hmax : MaximumProperty corr.replacementETT :=
    MaximumPropertyTransport G k e0 ett sigma hmod T corr hMP
  let replacementSeries : TashkinovSeries G k corr.replacementETT.rounds e0
      corr.replacementInput :=
    cast (congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput)
      corr.rungAgreement.symm) corr.replacementSeries
  have castStored {a b : ℕ} (h : a = b)
      (s : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)) :
      (cast (congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput) h)
        s).data.stored i = s.data.stored (Fin.cast (congrArg (fun n => n + 1) h.symm) i) := by
    cases h
    rfl
  have castKind {a b : ℕ} (h : a = b)
      (s : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 1)) :
      (cast (congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput) h)
        s).data.kind i = s.data.kind (Fin.cast (congrArg (fun n => n + 1) h.symm) i) := by
    cases h
    rfl
  have castTree {a b : ℕ} (h : a = b)
      (s : TashkinovSeries G k a e0 corr.replacementInput)
      (i : Fin (b + 2)) :
      (cast (congrArg (fun n => TashkinovSeries G k n e0 corr.replacementInput) h)
        s).data.tree i = s.data.tree (Fin.cast (congrArg (fun n => n + 2) h.symm) i) := by
    cases h
    rfl
  have hseries :=
    @helper_hseries_501 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@sigma) (@ett) (@hpositive) (@corr)
  let terminalIndex : Fin corr.replacementETT.rounds :=
    Fin.cast corr.rungAgreement.symm
      ⟨ett.rounds - 1, by have hp := ett.roundsPositive; omega⟩
  have htree :=
    @helper_htree_510 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@sigma) (@ett) (@hpositive) (@corr) (@castTree) (@hseries)
  have hstored :=
    @helper_hstored_528 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@sigma) (@ett) (@hpositive) (@corr) (@castStored) (@hseries)
  have hkindEq :=
    @helper_hkindEq_536 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@sigma) (@ett) (@hpositive) (@corr) (@castKind) (@hseries)
  have htreeFinal :=
    @helper_htreeFinal_544 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@sigma) (@ett) (@hpositive) (@corr) (@htree)
  have hgoodData : ∃ corrFinal : CorrespondingExtendedTashkinovTree G k e0 ett sigma T,
      ∃ hmaxFinal : MaximumProperty corrFinal.replacementETT,
      ∃ baseSigma : HierarchyBase corrFinal.replacementETT sigma,
      ∃ K : TashkinovHierarchy corrFinal.replacementETT baseSigma,
        ∃ goodSigma : GoodHierarchy K,
          SameGoodHierarchy good goodSigma := by
    by_cases hpe : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE
    · exact @helper_branch_563 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@sigma) (@ett) (@hMP) (@hpositive) (@hlower)
        (@base) (@H) (@good) (@hproper) (@hone) (@alpha) (@beta) (@hrecolor) (@hsigma)
        (@honeSigma) (@hcomb) (@eligible) (@corr) (@hpe)
    · exact @helper_branch_608 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@sigma) (@ett) (@hpositive) (@base) (@H) (@good)
        (@hproper) (@hone) (@alpha) (@beta) (@hrecolor) (@corr) (@hmax) (@hstored) (@hkindEq)
        (@htreeFinal) (@hpe)
  rcases hgoodData with ⟨corrFinal, hmaxFinal, baseSigma, K, goodSigma, hsg⟩
  refine ⟨hsigma, honeSigma, hstab, hinv, corrFinal, hmaxFinal, baseSigma, K,
    goodSigma, hsg, ?_⟩
  intro hclosed
  unfold TreeColorSetMinusClosed at hclosed ⊢
  have missingEq :=
    @helper_missingEq_673 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@phi) (@sigma) (@ett) (@hpositive) (@hstab)
  rw [missingEq] at hclosed
  intro alpha ha
  have hc := hclosed alpha ha
  rw [Finset.eq_empty_iff_forall_notMem] at hc ⊢
  intro f hf
  simp only [BoundaryColorEdges, Finset.mem_filter] at hf
  have hbase : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := hf.1
  have hi :=
    @helper_hi_686 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0) (@input)
        (@T) (@phi) (@ett) (@hpositive) (@f) (@hbase)
  have hphi : phi f = some alpha := by
    exact (hfixed f hi).symm ▸ hf.2
  apply hc f
  simp only [BoundaryColorEdges, Finset.mem_filter]
  exact ⟨hbase, hphi⟩

end GoldbergSeymour

end
