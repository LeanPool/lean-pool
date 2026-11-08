/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeriesTerminalRoute

public import LeanPool.GoldbergSeymour.HierarchyTreeFacts

public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentFacts

public import LeanPool.GoldbergSeymour.TreeSequenceFirstMissingPositionInvariant

public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint
public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColors
public import LeanPool.GoldbergSeymour.Td
public import LeanPool.GoldbergSeymour.OutsideExitTransport
public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColorsSubsetLast
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceColoringTransport
public import LeanPool.GoldbergSeymour.HierarchyFirstMissingPositionPrefixCutoff
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis

/-!
# Step1Case One Outside Star

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_chosenAgree_381.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (hpositive : (0 : ℕ) < ett.rounds) (i₁ i₂ : Fin (T.length + (1 : ℕ)))
      (_ : (↑i₁ : ℕ) < (↑i₂ : ℕ)) (_ : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ))
      (_ : (↑i₂ : ℕ) ≤ T.length),
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    (∀ {r : ℕ} {inp : PartialEdgeColoring E k} (s : TashkinovSeries G k r e0 inp)
        (q : Fin r),
        s.data.kind q.succ = some TashkinovExtensionKind.PE →
          ∃ (v : V) (u : V) (f : E),
            s.data.chosenVertex q.succ = some v ∧
              s.data.connectingEdges q.succ = ({ f } : Finset E) ∧
                v ∈ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
                  u ∉ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
                    G.ends f = s(v, u)) →
    ∀ (newInput : PartialEdgeColoring E k)
      (newSeries : TashkinovSeries G k ett.rounds e0 newInput),
    (∀ (i : Fin (ett.rounds + (1 : ℕ))),
        newSeries.data.connectingEdges i = ett.series.data.connectingEdges i) →
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    q.succ = Fin.last ett.rounds →
    newSeries.data.tree (Fin.last ett.rounds).castSucc = Tn →
    newSeries.data.kind (Fin.last ett.rounds) = ett.series.data.kind (Fin.last ett.rounds) →
    ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
    newSeries.data.chosenVertex (Fin.last ett.rounds) =
      ett.series.data.chosenVertex (Fin.last ett.rounds) := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive i₁ i₂ hiorder hspos hsT Tn peSupport newInput
      newSeries hedges q hq htree hkind hp
  obtain ⟨v, u, f, hv, hf, hvin, huout, hends⟩ :=
    peSupport ett.series q (by simpa [hq] using hp)
  obtain ⟨v', u', f', hv', hf', hvin', huout', hends'⟩ :=
    peSupport newSeries q (by simpa [hq] using hkind.trans hp)
  have hedge : f' = f := by
    have hh := hedges q.succ
    rw [hf', hf] at hh
    simpa using hh
  have hvEq : v' = v := by
    rcases Sym2.eq_iff.mp (hends'.symm.trans (hedge ▸ hends)) with h | h
    · exact h.1
    · have hin : v ∈ TreeSequenceVertexSet (newSeries.data.tree q.succ.castSucc) := by
        simpa [hq, htree, Tn] using hvin
      exact False.elim (huout' (h.2 ▸ hin))
  simpa [hq] using hv'.trans ((congrArg some hvEq).trans hv.symm)

private theorem helper_closureVertices_400.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (i₁ i₂ : Fin (T.length + (1 : ℕ)))
      (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ)) (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ)),
    let Bminus : TreeSequence G e0 :=
      TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          have := Fin.isLt i₂
          have := GoldbergSeymour.TreeSequence.positive T
          omega);
    TreeSequenceInitialSegment base.core Bminus →
    ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
    TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet Bminus := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base i₁ i₂ hiorder hspos Bminus coreToB hp
  obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hp
  intro v hv
  apply TreeSequenceInitialSegmentVertexSetSubset coreToB
  rw [u.vertexSet]
  exact Finset.mem_union_right _ hv

private theorem helper_divBound_489.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi),
    (0 : ℕ) < ett.rounds →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (beta : Fin k)
      (b₂ : V) (gamma : Fin k) (sigma : PartialEdgeColoring E k)
      (i₁ i₂ : Fin (T.length + (1 : ℕ))) (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ))
      (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ)) (hsT : (↑i₂ : ℕ) ≤ T.length),
    let Bminus : TreeSequence G e0 :=
      TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          have := Fin.isLt i₂
          have := GoldbergSeymour.TreeSequence.positive T
          omega);
    let C : TreeSequence G e0 :=
      TreeSequencePrefix T (↑i₂ : ℕ)
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          have := Fin.isLt i₂
          have := GoldbergSeymour.TreeSequence.positive T
          omega)
        hsT;
    let mu : PartialEdgeColoring E k :=
      TwoColorComponentSwap G sigma gamma beta (Sum.inl b₂);
    TreeSequenceInitialSegment Bminus C →
    (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
        TreeSequenceInitialSegment (H.stage j.castSucc) Bminus) →
    ∀ (newInput : PartialEdgeColoring E k)
      (newSeries : TashkinovSeries G k ett.rounds e0 newInput) (rp : (1 : ℕ) ≤ ett.1)
      (above :
        TreeSequenceInitialSegment
          (newSeries.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))) C)
      (strict :
        (newSeries.data.tree
              (⟨ett.1, by
                  have := above.1
                  omega⟩ :
                Fin (ett.1 + (2 : ℕ)))).length <
          C.length)
      (below :
        TreeSequenceInitialSegment C (newSeries.data.tree (Fin.last (ett.1 + (1 : ℕ)))))
      (gen : mu = newSeries.data.coloring (Fin.last ett.1)),
    { rounds := ett.1, roundsPositive := rp, series := newSeries, abovePenultimate := above,
            strictAbovePenultimate := strict, belowFinal := below,
            generatingColoring := gen :
            ExtendedTashkinovTree G k e0 newInput C mu }.series ≍
        newSeries →
    ∀ (i : Fin H.dividerCount),
    (↑(H.dividerPosition i) : ℕ) ≤ C.length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive base H beta b₂ gamma sigma i₁ i₂ hiorder
      hspos hsT Bminus C mu hBtoC stageToB newInput newSeries rp above strict below gen hs i
  have hl := congrArg TreeSequence.length (H.dividerStage i)
  change (H.stage ⟨i.val + 1, by omega⟩).length = (H.dividerPosition i).val at hl
  have hs := stageToB i.succ
  rw [← hl]
  exact le_trans hs.1 hBtoC.1

private theorem helper_boundaryFixed_658.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (beta : Fin k) (b₂ : V) (gamma : Fin k)
      (sigma : PartialEdgeColoring E k) (i₁ i₂ : Fin (T.length + (1 : ℕ)))
      (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ)) (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ)),
    let Bminus : TreeSequence G e0 :=
      TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          have := Fin.isLt i₂
          have := GoldbergSeymour.TreeSequence.positive T
          omega);
    let mu : PartialEdgeColoring E k :=
      TwoColorComponentSwap G sigma gamma beta (Sum.inl b₂);
    (∀ (f : E), TreeIncidentEdge Bminus f → mu f = phi f) →
    ∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet Bminus →
    ∀ e ∈ BoundaryEdges G (TreeSequenceVertexSet S),
    mu e = phi e := by
  classical
  intro V E _ _ G k e0 T phi beta b₂ gamma sigma i₁ i₂ hiorder hspos Bminus mu hfixed S hS e he
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨v, hv, w, hw, hends⟩ := he
  apply hfixed
  refine ⟨v, hS hv, ?_⟩
  change v ∈ G.ends e
  rw [hends]; exact Sym2.mem_mk_left _ _

private theorem helper_minusEq_668.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (beta : Fin k) (b₂ : V) (gamma : Fin k)
      (sigma : PartialEdgeColoring E k) (i₁ i₂ : Fin (T.length + (1 : ℕ)))
      (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ)) (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ)),
    let Bminus : TreeSequence G e0 :=
      TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          have := Fin.isLt i₂
          have := GoldbergSeymour.TreeSequence.positive T
          omega);
    let mu : PartialEdgeColoring E k :=
      TwoColorComponentSwap G sigma gamma beta (Sum.inl b₂);
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet Bminus →
          TreeMissingColors mu S = TreeMissingColors phi S) →
    (∀ (S : TreeSequence G e0),
        TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet Bminus →
          ∀ e ∈ BoundaryEdges G (TreeSequenceVertexSet S), mu e = phi e) →
    ∀ (S : TreeSequence G e0),
    TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet Bminus →
    ∀ (D : Finset (Fin k)),
    TreeColorSetMinusClosed G mu S D ↔ TreeColorSetMinusClosed G phi S D := by
  classical
  intro V E _ _ G k e0 T phi beta b₂ gamma sigma i₁ i₂ hiorder hspos Bminus mu missingEq
      boundaryFixed S hS D
  have hb (c : Fin k) : BoundaryColorEdges G mu (TreeSequenceVertexSet S) c =
      BoundaryColorEdges G phi (TreeSequenceVertexSet S) c := by
    ext e
    simp only [BoundaryColorEdges, Finset.mem_filter]
    exact and_congr_right (fun he => by rw [boundaryFixed S hS e he])
  unfold TreeColorSetMinusClosed TreeColorSetClosed
  rw [missingEq S hS]
  simp only [hb]

private theorem helper_closureMu_658.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (beta : Fin k) (b₂ : V) (gamma : Fin k)
      (sigma : PartialEdgeColoring E k) (i₁ i₂ : Fin (T.length + (1 : ℕ)))
      (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ)) (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ)),
    let Bminus : TreeSequence G e0 :=
      TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos
        (by
          omega);
    let mu : PartialEdgeColoring E k :=
      TwoColorComponentSwap G sigma gamma beta (Sum.inl b₂);
    (∀ (f : E), TreeIncidentEdge Bminus f → mu f = phi f) →
    (∀ v ∈ TreeSequenceVertexSet Bminus, MissingColors G mu v = MissingColors G phi v) →
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    (∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))),
        S.vertex i ∈ TreeSequenceVertexSet S) →
    (ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
        TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet Bminus) →
    ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
    TashkinovClosure mu
      (TreeSequencePrefix Tn (↑base.supportPosition : ℕ) base.supportPositive
        (Nat.le_of_lt_succ base.supportPosition.isLt))
      base.closure := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base beta b₂ gamma sigma i₁ i₂ hiorder hspos Bminus mu
      hfixed hmissingFixed Tn vertexMem closureVertices hp
  have hc := (base.parallel hp).2.1
  have sub := closureVertices hp
  have transport {S : TreeSequence G e0}
      (route : TashkinovAugmentationSequence phi S base.closure) :
      TashkinovAugmentationSequence mu S base.closure := by
    unfold TashkinovAugmentationSequence at route ⊢
    induction route using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.refl
    | @head S U step tail ih =>
      have hUR := TashkinovAugmentationSequenceInitialSegment phi U base.closure tail
      have hUV := TreeSequenceInitialSegmentVertexSetSubset hUR
      obtain ⟨hlen, hSU, c, hcolor, hmiss⟩ := step
      refine Relation.ReflTransGen.head ⟨hlen, hSU, c, ?_, ?_⟩ ih
      · let j : Fin U.length := Fin.cast hlen.symm (Fin.last S.length)
        obtain ⟨i, hi⟩ := U.attaches j
        have hiB : TreeIncidentEdge Bminus (U.edge j) := by
          refine ⟨U.vertex j.succ, sub (hUV (vertexMem _ _)), ?_⟩
          change U.vertex j.succ ∈ G.ends (U.edge j)
          rw [hi]; exact Sym2.mem_mk_left _ _
        exact (hfixed (U.edge j) hiB).trans hcolor
      · unfold TreeMissingColors at hmiss ⊢
        obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hmiss
        refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
        rw [hmissingFixed v
          (sub (hUV (TreeSequenceInitialSegmentVertexSetSubset hSU hv)))]
        exact hvc
  refine ⟨transport hc.1, ?_⟩
  intro e c v he hv hcolor hmiss
  have hb := he
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  obtain ⟨u, hu, w, hw, hends⟩ := hb
  have hiB : TreeIncidentEdge Bminus e := by
    refine ⟨u, sub hu, ?_⟩
    change u ∈ G.ends e
    rw [hends]; exact Sym2.mem_mk_left _ _
  apply hc.2 he hv ((hfixed e hiB).symm.trans hcolor)
  rw [← hmissingFixed v (sub hv)]
  exact hmiss

private theorem helper_strict_833.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (_ : (0 : ℕ) < ett.rounds) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (i₁ i₂ : Fin (T.length + (1 : ℕ)))
      (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ)) (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ))
      (hsT : (↑i₂ : ℕ) ≤ T.length),
    let Bminus : TreeSequence G e0 :=
      TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos (by omega);
    let C : TreeSequence G e0 := TreeSequencePrefix T (↑i₂ : ℕ) (by omega) hsT;
    ∀ (_ : Bminus.length < C.length)
      (_ :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
          TreeSequenceInitialSegment (H.stage j.castSucc) Bminus)
      (newInput : PartialEdgeColoring E k)
      (newSeries : TashkinovSeries G k ett.rounds e0 newInput)
      (_ :
        (newSeries.data.tree (⟨ett.1, by omega⟩ : Fin (ett.1 + (2 : ℕ)))).length <
          C.length),
    let stageC : Fin (H.dividerCount + (2 : ℕ)) → TreeSequence G e0 :=
      fun (j : Fin (H.dividerCount + (2 : ℕ))) ↦
      if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then C else H.stage j;
    ∀
      (_ :
        ∀ (j : Fin (H.dividerCount + (2 : ℕ))) (_ : (↑j : ℕ) ≤ H.dividerCount),
          stageC j = H.stage j)
      (_ : stageC (Fin.last (H.dividerCount + (1 : ℕ))) = C)
      (j : Fin (H.dividerCount + (1 : ℕ))),
    (stageC j.castSucc).length < (stageC j.succ).length := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive base H i₁ i₂ hiorder hspos hsT Bminus C
      hBCstrict stageToB newInput newSeries strict stageC stageOld stageLast j
  rw [stageOld j.castSucc (by have := j.isLt; simp; omega)]
  by_cases hj : j.val = H.dividerCount
  · have he : j.succ = Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
    rw [he, stageLast]
    exact lt_of_le_of_lt (stageToB j).1 hBCstrict
  · rw [stageOld j.succ (by simp; have := j.isLt; omega)]
    exact H.strict j

private theorem helper_nested_879.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (_ : (0 : ℕ) < ett.rounds) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (i₁ i₂ : Fin (T.length + (1 : ℕ)))
      (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ)) (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ))
      (hsT : (↑i₂ : ℕ) ≤ T.length),
    let Bminus : TreeSequence G e0 :=
      TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos (by omega);
    let C : TreeSequence G e0 := TreeSequencePrefix T (↑i₂ : ℕ) (by omega) hsT;
    ∀
      (_ :
        ∀ {S U W : TreeSequence G e0},
          TreeSequenceInitialSegment S U →
            TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W)
      (_ : TreeSequenceInitialSegment Bminus C)
      (_ :
        ∀ (j : Fin (H.dividerCount + (1 : ℕ))),
          TreeSequenceInitialSegment (H.stage j.castSucc) Bminus)
      (newInput : PartialEdgeColoring E k) (_ : TashkinovSeries G k ett.rounds e0 newInput),
    let stageC : Fin (H.dividerCount + (2 : ℕ)) → TreeSequence G e0 :=
      fun (j : Fin (H.dividerCount + (2 : ℕ))) ↦
      if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then C else H.stage j;
    ∀
      (_ :
        ∀ (j : Fin (H.dividerCount + (2 : ℕ))) (_ : (↑j : ℕ) ≤ H.dividerCount),
          stageC j = H.stage j)
      (_ : stageC (Fin.last (H.dividerCount + (1 : ℕ))) = C)
      (j : Fin (H.dividerCount + (1 : ℕ))),
    TreeSequenceInitialSegment (stageC j.castSucc) (stageC j.succ) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive base H i₁ i₂ hiorder hspos hsT Bminus C
      segTrans hBtoC stageToB newInput newSeries stageC stageOld stageLast j
  rw [stageOld j.castSucc (by have := j.isLt; simp; omega)]
  by_cases hj : j.val = H.dividerCount
  · have he : j.succ = Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
    rw [he, stageLast]
    exact segTrans (stageToB j) hBtoC
  · rw [stageOld j.succ (by simp; have := j.isLt; omega)]
    exact H.nested j

private theorem helper_dividerStage_937.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (_ : (0 : ℕ) < ett.rounds) (base : HierarchyBase ett phi)
      (H : TashkinovHierarchy ett base) (i₁ i₂ : Fin (T.length + (1 : ℕ)))
      (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ)) (_ : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ))
      (hsT : (↑i₂ : ℕ) ≤ T.length),
    let C : TreeSequence G e0 := TreeSequencePrefix T (↑i₂ : ℕ) (by omega) hsT;
    ∀ (newInput : PartialEdgeColoring E k) (_ : TashkinovSeries G k ett.rounds e0 newInput),
    let stageC : Fin (H.dividerCount + (2 : ℕ)) → TreeSequence G e0 :=
      fun (j : Fin (H.dividerCount + (2 : ℕ))) ↦
      if (↑j : ℕ) = H.dividerCount + (1 : ℕ) then C else H.stage j;
    ∀
      (_ :
        ∀ (j : Fin (H.dividerCount + (2 : ℕ))) (_ : (↑j : ℕ) ≤ H.dividerCount),
          stageC j = H.stage j)
      (divBound : ∀ (i : Fin H.dividerCount), (↑(H.dividerPosition i) : ℕ) ≤ C.length)
      (i : Fin H.dividerCount),
    stageC (⟨(↑i : ℕ) + (1 : ℕ), by omega⟩ : Fin (H.dividerCount + (2 : ℕ))) =
      TreeSequencePrefix C
        (↑(⟨(↑(H.dividerPosition i) : ℕ), Nat.lt_succ_of_le (divBound i)⟩ :
              Fin (C.length + (1 : ℕ))) :
          ℕ)
        (H.dividerPositive i)
        (Nat.le_of_lt_succ
          (⟨(↑(H.dividerPosition i) : ℕ), Nat.lt_succ_of_le (divBound i)⟩ :
              Fin (C.length + (1 : ℕ))).isLt) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive base H i₁ i₂ hiorder hspos hsT C newInput
      newSeries stageC stageOld divBound i
  rw [stageOld ⟨i.val + 1, by omega⟩
    (by change i.val + 1 ≤ H.dividerCount; omega), H.dividerStage i]
  rw [TreeSequencePrefix, TreeSequencePrefix]
  congr 1

private theorem hierarchySegmentColorsMono
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input input' phi mu generating generating' : PartialEdgeColoring E k}
    {T C : TreeSequence G e0}
    {ett : ExtendedTashkinovTree G k e0 input T generating}
    {ett' : ExtendedTashkinovTree G k e0 input' C generating'}
    {base : HierarchyBase ett phi} {base' : HierarchyBase ett' mu}
    (H : TashkinovHierarchy ett base) (K : TashkinovHierarchy ett' base')
    (j : Fin (H.dividerCount + 1)) (j' : Fin (K.dividerCount + 1)) (eta : Fin k)
    (hstar : HierarchyStarredStage K j' = HierarchyStarredStage H j)
    (hUW : TreeSequenceInitialSegment (K.stage j'.succ) (H.stage j.succ))
    (hUC : TreeSequenceInitialSegment (K.stage j'.succ) C)
    (hCT : TreeSequenceInitialSegment C T)
    (hfirst : (HierarchyFirstMissingPosition mu C eta).val =
      (HierarchyFirstMissingPosition phi C eta).val)
    (hfixed : ∀ r : Fin C.length, mu (C.edge r) = phi (C.edge r)) :
    HierarchySegmentColors K j' eta ⊆ HierarchySegmentColors H j eta := by
  classical
  have hcut : min (HierarchyFirstMissingPosition mu C eta).val
      (K.stage j'.succ).length =
      min (HierarchyFirstMissingPosition phi T eta).val (K.stage j'.succ).length := by
    rw [hfirst]
    exact HierarchyFirstMissingPositionPrefixCutoff phi C T hCT eta _ hUC.1
  intro c hc
  simp only [HierarchySegmentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  obtain ⟨r, hlo, hhi, hcol⟩ := hc
  refine ⟨Fin.castLE hUW.1 r, ?_, ?_, ?_⟩
  · simpa only [hstar, Fin.val_castLE] using hlo
  · have hr : r.val < (HierarchyFirstMissingPosition phi T eta).val := by
      rw [hcut] at hhi
      exact lt_of_lt_of_le hhi (Nat.min_le_left _ _)
    exact lt_min hr (Fin.castLE hUW.1 r).isLt
  · rw [hUW.2.2 r]
    have hf := hfixed (Fin.castLE hUC.1 r)
    rw [hUC.2.2 r] at hf
    exact hf.symm.trans hcol

private theorem treeSequenceVertexCast {V E : Type*} {G : LooplessMultigraph V E}
    {e0 : E} {S U : TreeSequence G e0} (h : S = U) (i : Fin (S.length + 1)) :
    U.vertex (Fin.cast (congrArg (fun R : TreeSequence G e0 => R.length + 1) h) i) =
      S.vertex i := by
  cases h
  rfl

private abbrev helperBranch366Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
   [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
   (input : PartialEdgeColoring E k) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k)
   (ett : ExtendedTashkinovTree G k e0 input T phi),
   (0 : ℕ) < ett.rounds →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (_ : GoodHierarchy H) (_ : ℕ)
     (alpha beta : Fin k),
     alpha ≠ beta →
      ∀ (b₂ : V) (gamma : Fin k) (sigma : PartialEdgeColoring E k)
       (i₁ i₂ : Fin (T.length + (1 : ℕ))) (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ))
       (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ)) (hsT : (↑i₂ : ℕ) ≤ T.length),
       let Bminus : TreeSequence G e0 :=
        TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos
         (Decidable.byContradiction fun (a : ¬(↑i₂ : ℕ) - (1 : ℕ) ≤ T.length) ↦ by omega);
       let C : TreeSequence G e0 :=
        TreeSequencePrefix T (↑i₂ : ℕ)
         (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑i₂ : ℕ)) ↦ by omega) hsT;
       TreeSequenceInitialSegment C T →
        Bminus.length < C.length →
         let mu : PartialEdgeColoring E k := TwoColorComponentSwap G sigma gamma beta (Sum.inl b₂);
         (∀ (f : E), TreeIncidentEdge Bminus f → mu f = phi f) →
          (∀ v ∈ TreeSequenceVertexSet Bminus, MissingColors G mu v = MissingColors G phi v) →
           (∀ (S : TreeSequence G e0), TreeSequenceInitialSegment S S) →
            (∀ {S U W : TreeSequence G e0},
              TreeSequenceInitialSegment S U →
               TreeSequenceInitialSegment U W → TreeSequenceInitialSegment S W) →
             let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
             TreeSequenceInitialSegment base.core Bminus →
              TreeSequenceInitialSegment Tn Bminus →
               C.length = Bminus.length + (1 : ℕ) →
                TreeSequenceInitialSegment Bminus C →
                 (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                   TreeSequenceInitialSegment (H.stage j.castSucc) Bminus) →
                  (∀ (j : Fin (H.dividerCount + (1 : ℕ))),
                    TreeSequenceInitialSegment (HierarchyStarredStage H j) Bminus) →
                   (∀ (S : TreeSequence G e0) (i : Fin (S.length + (1 : ℕ))),
                     S.vertex i ∈ TreeSequenceVertexSet S) →
                    (∀ (j : Fin C.length), mu (C.edge j) = phi (C.edge j)) →
                     (∀ (S : TreeSequence G e0),
                       TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet Bminus →
                        TreeMissingColors mu S = TreeMissingColors phi S) →
                      (∀ {r : ℕ} {inp : PartialEdgeColoring E k} (s : TashkinovSeries G k r e0 inp)
                        (q : Fin r),
                        s.data.kind q.succ = some TashkinovExtensionKind.PE →
                         ∃ (v : V) (u : V) (f : E),
                          s.data.chosenVertex q.succ = some v ∧
                           s.data.connectingEdges q.succ = { f } ∧
                            v ∈ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
                             u ∉ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
                              G.ends f = s(v, u)) →
                       ∀ (newInput : PartialEdgeColoring E k)
                        (newSeries : TashkinovSeries G k ett.rounds e0 newInput)
                        (hgen : mu = newSeries.data.coloring (Fin.last ett.rounds))
                        (htrees :
                         ∀ (i : Fin ett.rounds),
                          newSeries.data.tree i.succ.castSucc =
                           ett.series.data.tree i.succ.castSucc)
                        (hstored :
                         ∀ (i : Fin (ett.rounds + (1 : ℕ))),
                          newSeries.data.stored i = ett.series.data.stored i)
                        (hedges :
                         ∀ (i : Fin (ett.rounds + (1 : ℕ))),
                          newSeries.data.connectingEdges i = ett.series.data.connectingEdges i)
                        (hkinds :
                         ∀ (i : Fin (ett.rounds + (1 : ℕ))),
                          newSeries.data.kind i = ett.series.data.kind i)
                        (hproper :
                         ∀ (i : Fin (ett.rounds + (1 : ℕ))),
                          IsProperEdgeColoring G (newSeries.data.coloring i))
                        (hone :
                         ∀ (i : Fin (ett.rounds + (1 : ℕ))),
                          IsOneEdgeUncolored (newSeries.data.coloring i) e0)
                        (hstableSeries :
                         ∀ (i : Fin ett.rounds),
                          StableColoring (ett.series.data.tree i.succ.castSucc)
                           (TashkinovStoredColors ett.series.data i.succ)
                           (ett.series.data.coloring i.succ) (newSeries.data.coloring i.succ))
                        (r : ℕ) (rp : (1 : ℕ) ≤ r) (series : TashkinovSeries G k r e0 newInput)
                        (above :
                         TreeSequenceInitialSegment
                          (series.data.tree (⟨r, by omega⟩ : Fin (r + (2 : ℕ)))) C)
                        (strict :
                         (series.data.tree (⟨r, by omega⟩ : Fin (r + (2 : ℕ)))).length < C.length)
                        (below :
                         TreeSequenceInitialSegment C (series.data.tree (Fin.last (r + (1 : ℕ)))))
                        (gen : mu = series.data.coloring (Fin.last r))
                        (hr :
                         { rounds := r, roundsPositive := rp, series := series,
                            abovePenultimate := above, strictAbovePenultimate := strict,
                            belowFinal := below, generatingColoring := gen :
                            ExtendedTashkinovTree G k e0 newInput C mu }.rounds =
                          ett.rounds)
                        (hs :
                         { rounds := r, roundsPositive := rp, series := series,
                            abovePenultimate := above, strictAbovePenultimate := strict,
                            belowFinal := below, generatingColoring := gen :
                            ExtendedTashkinovTree G k e0 newInput C mu }.series ≍
                          newSeries),
                        MaximumProperty
                          { replacementInput := newInput, replacementSeries := newSeries,
                            replacementETT :=
                             {
                              rounds := r, roundsPositive := rp, series := series,
                              abovePenultimate := above, strictAbovePenultimate := strict,
                              belowFinal := below, generatingColoring := gen :
                              ExtendedTashkinovTree G k e0 newInput C mu },
                            rungAgreement := hr, seriesPresentation := hs,
                            finalGeneratingColoring := hgen, ladderTreesAgree := htrees,
                            storedColorsAgree := hstored, connectingEdgesAgree := hedges,
                            extensionKindsAgree := hkinds, replacementProper := hproper,
                            replacementOneUncolored := hone, replacementStable := hstableSeries :
                            CorrespondingExtendedTashkinovTree G k e0 ett mu C }.replacementETT →
                         ∃ (baseC :
                          HierarchyBase
                           { replacementInput := newInput, replacementSeries := newSeries,
                             replacementETT :=
                              {
                               rounds := r, roundsPositive := rp, series := series,
                               abovePenultimate := above, strictAbovePenultimate := strict,
                               belowFinal := below, generatingColoring := gen :
                               ExtendedTashkinovTree G k e0 newInput C mu },
                             rungAgreement := hr, seriesPresentation := hs,
                             finalGeneratingColoring := hgen, ladderTreesAgree := htrees,
                             storedColorsAgree := hstored, connectingEdgesAgree := hedges,
                             extensionKindsAgree := hkinds, replacementProper := hproper,
                             replacementOneUncolored := hone, replacementStable := hstableSeries :
                             CorrespondingExtendedTashkinovTree G k e0 ett mu C }.replacementETT
                           mu)
                          (KC :
                          TashkinovHierarchy
                           { replacementInput := newInput, replacementSeries := newSeries,
                             replacementETT :=
                              {
                               rounds := r, roundsPositive := rp, series := series,
                               abovePenultimate := above, strictAbovePenultimate := strict,
                               belowFinal := below, generatingColoring := gen :
                               ExtendedTashkinovTree G k e0 newInput C mu },
                             rungAgreement := hr, seriesPresentation := hs,
                             finalGeneratingColoring := hgen, ladderTreesAgree := htrees,
                             storedColorsAgree := hstored, connectingEdgesAgree := hedges,
                             extensionKindsAgree := hkinds, replacementProper := hproper,
                             replacementOneUncolored := hone, replacementStable := hstableSeries :
                             CorrespondingExtendedTashkinovTree G k e0 ett mu C }.replacementETT
                           baseC)
                          (_goodC : GoodHierarchy KC),
                          MaximumProperty
                            { replacementInput := newInput, replacementSeries := newSeries,
                              replacementETT :=
                               {
                                rounds := r, roundsPositive := rp, series := series,
                                abovePenultimate := above, strictAbovePenultimate := strict,
                                belowFinal := below, generatingColoring := gen :
                                ExtendedTashkinovTree G k e0 newInput C mu },
                              rungAgreement := hr, seriesPresentation := hs,
                              finalGeneratingColoring := hgen, ladderTreesAgree := htrees,
                              storedColorsAgree := hstored, connectingEdgesAgree := hedges,
                              extensionKindsAgree := hkinds, replacementProper := hproper,
                              replacementOneUncolored := hone, replacementStable := hstableSeries :
                              CorrespondingExtendedTashkinovTree G k e0 ett mu C }.replacementETT ∧
                           KC.dividerCount = H.dividerCount

private theorem helper_branch_366.{u_1, u_2} :
    helperBranch366Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive base H good q alpha beta hne b₂ gamma sigma
      i₁ i₂ hiorder hspos hsT Bminus C hCT hBCstrict mu hfixed hmissingFixed segRefl segTrans Tn
      coreToB TnToB hlenC hBtoC stageToB starredToB vertexMem fixedC missingEq peSupport newInput
      newSeries hgen htrees hstored hedges hkinds hproper hone hstableSeries r rp series above
      strict below gen hr hs hMPC
  cases hr
  cases (show series = newSeries from eq_of_heq hs)
  let rep : ExtendedTashkinovTree G k e0 newInput C mu :=
    ⟨ett.rounds, rp, newSeries, above, strict, below, gen⟩
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hq : q.succ = Fin.last ett.rounds := Fin.ext (by simp [q]; omega)
  have htree : newSeries.data.tree (Fin.last ett.rounds).castSucc = Tn := by
    simpa only [hq, Tn] using htrees q
  have hkind := hkinds (Fin.last ett.rounds)
  have chosenAgree :=
    helper_chosenAgree_381 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hpositive) (@i₁) (@i₂)
        (@hiorder) (@hspos) (@hsT) (@peSupport) (@newInput) (@newSeries) (@hedges) (@hq) (@htree)
        (@hkind)
  have closureVertices :=
    helper_closureVertices_400 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@i₁) (@i₂)
        (@hiorder) (@hspos) (@coreToB)
  -- The closure need not be an ordered prefix of the core.
  have closureMu :=
    helper_closureMu_658 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@beta) (@b₂)
        (@gamma) (@sigma) (@i₁) (@i₂) (@hiorder) (@hspos) (@hfixed) (@hmissingFixed) (@vertexMem)
        (@closureVertices)
  let pos : Fin ((newSeries.data.tree (Fin.last ett.rounds).castSucc).length + 1) :=
    Fin.cast (congrArg (fun S : TreeSequence G e0 => S.length + 1) htree.symm)
      base.supportPosition
  let baseC : HierarchyBase rep mu :=
    { core := base.core
      closure := base.closure
      supportPosition := pos
      supportPositive := by simpa [pos] using base.supportPositive
      terminalMissingColors := rfl
      parallel := by
        dsimp only [rep]
        intro hp
        have hpOld := hkind.symm.trans hp
        obtain ⟨hv, hc, hu⟩ := base.parallel hpOld
        refine ⟨?_, ?_, ?_⟩
        · rw [chosenAgree hpOld]
          rw [treeSequenceVertexCast htree.symm base.supportPosition]
          exact hv
        · simpa [pos, htree] using closureMu hpOld
        · simpa [htree] using hu
      nonparallel := by
        dsimp only [rep]
        intro hp
        exact (base.nonparallel (fun h => hp (hkind.trans h))).trans htree.symm }
  refine ⟨baseC, ?_⟩
  let stageC : Fin (H.dividerCount + 2) → TreeSequence G e0 :=
    fun j => if j.val = H.dividerCount + 1 then C else H.stage j
  have stageOld (j : Fin (H.dividerCount + 2)) (hj : j.val ≤ H.dividerCount) :
      stageC j = H.stage j := by
    exact ite_eq_right (show j.val ≠ H.dividerCount + 1 by omega)
  have stageLast : stageC (Fin.last (H.dividerCount + 1)) = C := by
    simp only [stageC, Fin.val_last, ite_true]
  have divBound :=
    helper_divBound_489 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hpositive) (@base) (@H)
        (@beta) (@b₂) (@gamma) (@sigma) (@i₁) (@i₂) (@hiorder) (@hspos) (@hsT) (@hBtoC)
        (@stageToB) (@newInput) (@newSeries) (@rp) (@above) (@strict) (@below) (@gen) (@hs)
  let KC : TashkinovHierarchy rep baseC :=
    { dividerCount := H.dividerCount
      stage := stageC
      baseStage := by
        rw [stageOld 0 (by simp), H.baseStage]
        exact htree.symm
      terminalStage := stageLast
      nested := by
        exact helper_nested_879 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hpositive) (@base)
            (@H) (@i₁) (@i₂) (@hiorder) (@hspos) (@hsT) (@segTrans) (@hBtoC) (@stageToB)
            (@newInput) (@newSeries) (@stageOld) (@stageLast)
      strict := by
        exact helper_strict_833 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hpositive) (@base)
            (@H) (@i₁) (@i₂) (@hiorder) (@hspos) (@hsT) (@hBCstrict) (@stageToB) (@newInput)
            (@newSeries) (@strict) (@stageOld) (@stageLast)
      dividerPosition := fun i => ⟨(H.dividerPosition i).val, Nat.lt_succ_of_le (divBound i)⟩
      dividerPositive := H.dividerPositive
      dividerIncreasing := H.dividerIncreasing
      dividerStage := by
        exact helper_dividerStage_937 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hpositive)
            (@base) (@H) (@i₁) (@i₂) (@hiorder) (@hspos) (@hsT) (@newInput) (@newSeries)
            (@stageOld) (@divBound)
      coreInsideFirst := by
        by_cases hd : H.dividerCount = 0
        · have he : (⟨1, by omega⟩ : Fin (H.dividerCount + 2)) =
              Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
          rw [he, stageLast]
          exact segTrans coreToB hBtoC
        · rw [stageOld ⟨1, by omega⟩ (by change 1 ≤ H.dividerCount; omega)]
          exact H.coreInsideFirst }
  have ordinaryEq (j : Fin (H.dividerCount + 1)) :
      KC.stage j.castSucc = H.stage j.castSucc :=
    stageOld j.castSucc (Nat.le_of_lt_succ j.isLt)
  have starredEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStarredStage KC j = HierarchyStarredStage H j := by
    refine Fin.cases rfl (fun i => ordinaryEq i.succ) j
  have terminalMissing : TreeMissingColors mu Tn = TreeMissingColors phi Tn :=
    missingEq Tn (TreeSequenceInitialSegmentVertexSetSubset TnToB)
  have storedEq : TashkinovStoredColors newSeries.data (Fin.last ett.rounds) =
      TashkinovStoredColors ett.series.data (Fin.last ett.rounds) := by
    unfold TashkinovStoredColors
    simp only [hstored, ← hgen, ← ett.generatingColoring, htree, terminalMissing]
    rfl
  have indexedStoredEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStoredColorsAt KC j = HierarchyStoredColorsAt H j := by
    change TashkinovStoredColors newSeries.data (Fin.last ett.rounds) \
        TreeMissingColors mu (HierarchyStarredStage KC j) =
      TashkinovStoredColors ett.series.data (Fin.last ett.rounds) \
        TreeMissingColors phi (HierarchyStarredStage H j)
    rw [storedEq, starredEq, missingEq _
      (TreeSequenceInitialSegmentVertexSetSubset (starredToB j))]
  have stageMissingEq (j : Fin (H.dividerCount + 1)) :
      HierarchyStageMissingColors KC j = HierarchyStageMissingColors H j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · change TreeMissingColors mu (newSeries.data.tree (Fin.last ett.rounds).castSucc) =
        TreeMissingColors phi Tn
      rw [htree, terminalMissing]
    · change TreeMissingColors mu (KC.stage i.succ.castSucc) =
        TreeMissingColors phi (H.stage i.succ.castSucc)
      rw [ordinaryEq]
      exact missingEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageToB i.succ))
  refine ⟨KC, ?_⟩
  have nextPrefix (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (KC.stage j.succ) (H.stage j.succ) ∧
        TreeSequenceInitialSegment (KC.stage j.succ) C := by
    change TreeSequenceInitialSegment (stageC j.succ) (H.stage j.succ) ∧
      TreeSequenceInitialSegment (stageC j.succ) C
    by_cases hj : j.val = H.dividerCount
    · have he : j.succ = Fin.last (H.dividerCount + 1) := Fin.ext (by simp; omega)
      rw [he, stageLast, H.terminalStage]
      exact ⟨hCT, segRefl C⟩
    · rw [stageOld j.succ (by simp; have := j.isLt; omega)]
      exact ⟨segRefl _, segTrans (stageToB ⟨j.val + 1, by omega⟩) hBtoC⟩
  have segmentSubset (j : Fin (H.dividerCount + 1)) (eta : Fin k) :
      HierarchySegmentColors KC j eta ⊆ HierarchySegmentColors H j eta := by
    exact hierarchySegmentColorsMono H KC j j eta (starredEq j)
      (nextPrefix j).1 (nextPrefix j).2 hCT
      (congrArg Fin.val
        (C.firstMissingPosition_eq_of_prefix_agreement hBtoC hlenC.le hmissingFixed eta)) fixedC
  have boundaryFixed :=
    helper_boundaryFixed_658 (@G) (@k) (@e0) (@T) (@phi) (@beta) (@b₂) (@gamma) (@sigma) (@i₁)
        (@i₂) (@hiorder) (@hspos) (@hfixed)
  have minusEq :=
    helper_minusEq_668 (@G) (@k) (@e0) (@T) (@phi) (@beta) (@b₂) (@gamma) (@sigma) (@i₁) (@i₂)
        (@hiorder) (@hspos) (@missingEq) (@boundaryFixed)
  have refreshEq (i : Fin H.dividerCount) :
      ((TreeSequenceVertexSet (KC.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage KC i.castSucc)).biUnion
          fun v => MissingColors G mu v) =
      ((TreeSequenceVertexSet (H.stage i.succ.castSucc) \
        TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc)).biUnion
          fun v => MissingColors G phi v) := by
    rw [ordinaryEq, starredEq]
    apply Finset.biUnion_congr rfl
    intro v hv
    exact hmissingFixed v (TreeSequenceInitialSegmentVertexSetSubset
      (stageToB i.succ) (Finset.mem_sdiff.mp hv).1)
  let goodC : GoodHierarchy KC :=
    { gamma := good.gamma
      twoColors := by
        intro j eta he
        exact good.twoColors j eta (indexedStoredEq j ▸ he)
      avoidance := by
        intro j eta he c hc
        have hav := good.avoidance j eta (indexedStoredEq j ▸ he) hc
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · rw [stageMissingEq]; exact (Finset.mem_sdiff.mp hav).1
        · intro hs
          exact (Finset.mem_sdiff.mp hav).2 (segmentSubset j eta hs)
      disjointPairs := by
        intro j eta theta he ht hne
        exact good.disjointPairs j eta theta (indexedStoredEq j ▸ he)
          (indexedStoredEq j ▸ ht) hne
      uniqueRefresh := by
        intro i
        simpa only [indexedStoredEq, refreshEq] using good.uniqueRefresh i
      parallelBase := by
        dsimp only
        intro hp
        have hpOld := hkind.symm.trans hp
        have hold := good.parallelBase hpOld
        change ¬TreeColorSetMinusClosed G mu base.core
            ((HierarchyStoredColorsAt KC 0).biUnion (good.gamma 0)) ∧
          4 ≤ ((TreeMissingColors mu (newSeries.data.tree (Fin.last ett.rounds).castSucc) ∩
            TreeMissingColors mu base.closure) \
              (HierarchyStoredColorsAt KC 0).biUnion (good.gamma 0)).card
        rw [indexedStoredEq, minusEq _ (TreeSequenceInitialSegmentVertexSetSubset coreToB),
          htree, terminalMissing, missingEq _ (closureVertices hpOld)]
        exact hold
      minusClosed := by
        intro i
        rw [ordinaryEq, indexedStoredEq,
          minusEq _ (TreeSequenceInitialSegmentVertexSetSubset (stageToB i.succ))]
        exact good.minusClosed i }
  exact ⟨goodC, hMPC, rfl⟩

private theorem helper_rebuild_367.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi),
    MaximumProperty ett →
    (0 : ℕ) < ett.rounds →
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base)
      (_ : GoodHierarchy H) (_ : ℕ) (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (b₂ : V),
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    ∀ (gamma : Fin k) (sigma : PartialEdgeColoring E k) (i₁ i₂ : Fin (T.length + (1 : ℕ)))
      (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ)) (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ))
      (hsT : (↑i₂ : ℕ) ≤ T.length),
    let Bminus : TreeSequence G e0 :=
      TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos
        (Decidable.byContradiction fun (a : ¬(↑i₂ : ℕ) - (1 : ℕ) ≤ T.length) ↦ by omega);
    let C : TreeSequence G e0 :=
      TreeSequencePrefix T (↑i₂ : ℕ)
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ (↑i₂ : ℕ)) ↦ by omega) hsT;
    TreeSequenceInitialSegment A Bminus →
    TreeSequenceInitialSegment C T →
    Bminus.length < C.length →
    (∃ (g : E), TreeSequenceAdjoinEdge Bminus g C) →
    let mu : PartialEdgeColoring E k :=
      TwoColorComponentSwap G sigma gamma beta (Sum.inl b₂);
    IsProperEdgeColoring G mu →
    IsOneEdgeUncolored mu e0 →
    (∀ (f : E), TreeIncidentEdge Bminus f → mu f = phi f) →
    (∀ v ∈ TreeSequenceVertexSet Bminus, MissingColors G mu v = MissingColors G phi v) →
    ∃ (corrC : CorrespondingExtendedTashkinovTree G k e0 ett mu C) (baseC :
      HierarchyBase corrC.replacementETT mu) (KC :
      TashkinovHierarchy corrC.replacementETT baseC) (_goodC : GoodHierarchy KC),
    MaximumProperty corrC.replacementETT ∧
    KC.dividerCount = H.dividerCount := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hMP hpositive hproper hone hlower base H good q alpha
      beta hne b₂ A gamma sigma i₁ i₂ hiorder hspos hsT Bminus C hAB hCT hBCstrict hBCadjoin mu
      hproperMu honeMu hfixed hmissingFixed
  classical
  have segRefl (S : TreeSequence G e0) : TreeSequenceInitialSegment S S :=
    ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have segTrans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) :
      TreeSequenceInitialSegment S W := by
    exact hSU.trans hUW
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
  have lastZero (h : H.dividerCount = 0) : A = base.core := by
    simp [A, HierarchyStarredStage, h, Fin.last]
  have coreToA : TreeSequenceInitialSegment base.core A := by
    exact H.coreInitialSegmentOfStarredStage (Fin.last H.dividerCount)
  have TnToCore : TreeSequenceInitialSegment Tn base.core := by
    exact base.lastRoundInitialSegmentCore
  have coreToB := segTrans coreToA hAB
  have TnToB := segTrans TnToCore coreToB
  obtain ⟨g, hattach⟩ := hBCadjoin
  obtain ⟨hlenC, hBtoC, hg⟩ := hattach
  have TnToC := segTrans TnToB hBtoC
  have TnStrictC : Tn.length < C.length := lt_of_le_of_lt TnToB.1 hBCstrict
  have stageToB (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (H.stage j.castSucc) Bminus := by
    exact (H.stageInitialSegmentOfStarredStage j (Fin.last H.dividerCount) (Fin.le_last _)).trans
      hAB
  have starredToB (j : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H j) Bminus := by
    exact (H.starredStageInitialSegmentOfLE j (Fin.last H.dividerCount) (Fin.le_last _)).trans
      hAB
  have vertexMem (S : TreeSequence G e0) (i : Fin (S.length + 1)) :
      S.vertex i ∈ TreeSequenceVertexSet S := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  have fixedC (j : Fin C.length) : mu (C.edge j) = phi (C.edge j) := by
    obtain ⟨i, hi⟩ := C.attaches j
    let ib : Fin (Bminus.length + 1) := ⟨i.val, by have := i.isLt; have := j.isLt; omega⟩
    have hv : C.vertex (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt))) = Bminus.vertex ib := by
      exact hBtoC.2.1 ib
    apply hfixed
    refine ⟨Bminus.vertex ib, vertexMem _ _, ?_⟩
    change Bminus.vertex ib ∈ G.ends (C.edge j)
    rw [hi, hv]
    exact Sym2.mem_mk_right _ _
  have missingEq (S : TreeSequence G e0)
      (hS : TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet Bminus) :
      TreeMissingColors mu S = TreeMissingColors phi S := by
    unfold TreeMissingColors
    apply Finset.biUnion_congr rfl
    intro v hv
    exact hmissingFixed v (hS hv)
  have hstable : StableColoring Tn
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi mu := by
    constructor
    · intro f ⟨v, hv, hvf⟩ _
      exact hfixed f ⟨v, TreeSequenceInitialSegmentVertexSetSubset TnToB hv, hvf⟩
    · intro v hv
      exact hmissingFixed v (TreeSequenceInitialSegmentVertexSetSubset TnToB hv)
  have hmod : ModColoring ett mu :=
    Td G k e0 input T phi ett hMP hpositive hlower mu hproperMu honeMu
      (by simpa [ett.generatingColoring] using hstable)
  have terminalRoute := ett.series.terminalRouteColoringTransport hpositive phi
    ett.generatingColoring C TnToC TnStrictC (segTrans hCT ett.belowFinal)
    mu Bminus hBtoC hlenC (fun t _ => fixedC t) hmissingFixed
  obtain ⟨corrC⟩ := hmod.2.2 C TnToC TnStrictC terminalRoute
  have hMPC := MaximumPropertyTransport G k e0 ett mu hmod C corrC hMP
  refine ⟨corrC, ?_⟩
  have peSupport {r : ℕ} {inp : PartialEdgeColoring E k}
      (s : TashkinovSeries G k r e0 inp) (q : Fin r)
      (hp : s.data.kind q.succ = some TashkinovExtensionKind.PE) :
      ∃ v u f, s.data.chosenVertex q.succ = some v ∧
        s.data.connectingEdges q.succ = {f} ∧
        v ∈ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
        u ∉ TreeSequenceVertexSet (s.data.tree q.succ.castSucc) ∧
        G.ends f = s(v, u) := by
    have step := s.certified q.succ
    generalize hi : q.succ = i at step
    cases step with
    | initial _ _ _ _ _ kind =>
      rw [hi, kind] at hp; cases hp
    | SE j _ _ _ _ _ choice _ coloring stored edges kind =>
      rw [hi, kind] at hp; cases hp
    | RE j _ _ _ _ available coloring stored edges kind =>
      rw [hi, kind] at hp; cases hp
    | PE j _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper one stored
        edges kind vertex outside delta gammaEq closure ordered strict =>
      simpa only [hi] using
        (show ∃ v u f, s.data.chosenVertex j.succ = some v ∧
          s.data.connectingEdges j.succ = {f} ∧
          v ∈ TreeSequenceVertexSet (s.data.tree j.succ.castSucc) ∧
          u ∉ TreeSequenceVertexSet (s.data.tree j.succ.castSucc) ∧
          G.ends f = s(v, u) from
          ⟨choice.vertex, choice.otherEndpoint, choice.edge, vertex, edges,
            choice.vertexDefective.1, choice.otherOutside, choice.edgeEnds⟩)
  rcases corrC with ⟨newInput, newSeries, newETT, hr, hs, hgen, htrees, hstored,
    hedges, hkinds, hproper, hone, hstableSeries⟩
  cases newETT with
  | mk r rp series above strict below gen =>
      exact @helper_branch_366 V E inferInstance inferInstance inferInstance inferInstance G k e0
          input T phi ett hpositive base H good q alpha beta hne b₂ gamma sigma i₁ i₂ hiorder
          hspos hsT hCT hBCstrict hfixed hmissingFixed segRefl segTrans coreToB TnToB hlenC hBtoC
          stageToB starredToB vertexMem fixedC missingEq peSupport newInput newSeries hgen htrees
          hstored hedges hkinds hproper hone hstableSeries r rp series above strict below gen hr
          hs hMPC
private theorem helper_continuation_1138.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi),
    MaximumProperty ett →
    (0 : ℕ) < ett.rounds →
    IsProperEdgeColoring G phi →
    IsOneEdgeUncolored phi e0 →
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base)
      (_ : GoodHierarchy H) (q : ℕ),
    H.dividerCount < q →
    (∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k}
        (other : ExtendedTashkinovTree G k e0 input' T' generating'),
        other.rounds = ett.rounds →
          MaximumProperty other →
            ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base')
              (_ : GoodHierarchy K),
              K.dividerCount < q →
                ColoredVertexSetElementary G generating' (TreeSequenceVertexSet T')) →
    ∀ (alpha beta : Fin k),
    alpha ≠ beta →
    ∀ (a₂ b₂ : V),
    b₂ ∉ TreeSequenceVertexSet (HierarchyStarredStage H (Fin.last H.dividerCount)) →
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    beta ∈ TreeMissingColors phi A →
    ∀ (gamma : Fin k),
    gamma ≠ beta →
    ∀ (sigma : PartialEdgeColoring E k)
      (Q₂ : (TwoColorIncidenceGraph G sigma gamma beta).Walk (Sum.inl a₂) (Sum.inl b₂)),
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    (∀ (f : E), TreeIncidentEdge T f → sigma f = phi f) →
    TreeExitPath T sigma gamma beta a₂ b₂ Q₂ →
    gamma ∈ MissingColors G sigma b₂ →
    ∀ (i₁ i₂ : Fin (T.length + (1 : ℕ))) (hiorder : (↑i₁ : ℕ) < (↑i₂ : ℕ))
      (hspos : (1 : ℕ) ≤ (↑i₂ : ℕ) - (1 : ℕ)) (hsT : (↑i₂ : ℕ) ≤ T.length),
    let Bminus : TreeSequence G e0 :=
      TreeSequencePrefix T ((↑i₂ : ℕ) - (1 : ℕ)) hspos
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega);
    let C : TreeSequence G e0 :=
      TreeSequencePrefix T (↑i₂ : ℕ)
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          omega)
        hsT;
    TreeSequenceInitialSegment A Bminus →
    TreeSequenceInitialSegment Bminus C →
    TreeSequenceInitialSegment C T →
    TreeSequenceInitialSegment Bminus T →
    Bminus.length < C.length →
    C.vertex (Fin.last C.length) = b₂ →
    b₂ ∉ TreeSequenceVertexSet Bminus →
    (∃ (g : E), TreeSequenceAdjoinEdge Bminus g C) →
    False := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hMP hpositive hproper hone hlower base H good q
      hdivider hfewer alpha beta hne a₂ b₂ houtside A betaA gamma hgb sigma Q₂ hsproper hsone
      sigma_fixed hQ₂ hgSigma i₁ i₂ hiorder hspos hsT Bminus C hAB hBC hCT hBT hBCstrict hbC
      hbNotB hBCadjoin
  let K₂ := TwoColorComponent G sigma gamma beta (Sum.inl b₂)
  have hKtree : ∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ K₂ ↔ v = b₂ :=
    TreeExitComponentMeetsTreeOnlyAtExit T sigma gamma beta b₂ hsproper hgSigma
      ⟨a₂, Q₂, hQ₂⟩
  let mu := TwoColorComponentSwap G sigma gamma beta (Sum.inl b₂)
  have hproperMu : IsProperEdgeColoring G mu :=
    TwoColorComponentSwapProper G sigma gamma beta hgb hsproper _
  have honeMu : IsOneEdgeUncolored mu e0 := by
    constructor
    · simp [mu, TwoColorComponentSwap, hsone.1]
    · intro f hfe
      obtain ⟨c, hc⟩ := hsone.2 f hfe
      by_cases hf : Sum.inr f ∈ K₂
      · by_cases ha : sigma f = some gamma
        · exact ⟨beta, by simp [mu, TwoColorComponentSwap, K₂, hf, ha]⟩
        · by_cases hb : sigma f = some beta
          · exact ⟨gamma, by simp [mu, TwoColorComponentSwap, K₂, hf, hb, hgb.symm]⟩
          · refine ⟨c, ?_⟩
            change (if Sum.inr f ∈ K₂ then
              if sigma f = some gamma then some beta
              else if sigma f = some beta then some gamma else sigma f
              else sigma f) = some c
            rw [ite_eq_left hf, ite_eq_right ha, ite_eq_right hb]
            exact hc
      · exact ⟨c, by simp [mu, TwoColorComponentSwap, K₂, hf, hc]⟩
  have hfixed : ∀ f, TreeIncidentEdge Bminus f → mu f = phi f := by
    intro f hf
    obtain ⟨v, hv, hvf⟩ := hf
    have hvT := TreeSequenceInitialSegmentVertexSetSubset hBT hv
    have hvK : Sum.inl v ∉ K₂ := by
      intro h
      exact hbNotB ((hKtree v hvT).mp h ▸ hv)
    have unchanged : mu f = sigma f := by
      by_cases heK : Sum.inr f ∈ K₂
      · have noColor : ¬ (sigma f = some gamma ∨ sigma f = some beta) := by
          intro hc
          have ha : (TwoColorIncidenceGraph G sigma gamma beta).Adj
              (Sum.inl v) (Sum.inr f) := ⟨hvf, hc⟩
          exact hvK ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj ha).trans heK)
        push Not at noColor
        simp [mu, TwoColorComponentSwap, K₂, heK, noColor.1, noColor.2]
      · simp [mu, TwoColorComponentSwap, K₂, heK]
    exact unchanged.trans (sigma_fixed f ⟨v, hvT, hvf⟩)
  have hmissingFixed : ∀ v ∈ TreeSequenceVertexSet Bminus,
      MissingColors G mu v = MissingColors G phi v := by
    intro v hv
    ext c
    simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
      PresentColors, Finset.mem_filter]
    have same : (∃ f, Incident G v f ∧ mu f = some c) ↔
        (∃ f, Incident G v f ∧ phi f = some c) := by
      constructor <;> rintro ⟨f, hf, hc⟩
      · exact ⟨f, hf, (hfixed f ⟨v, hv, hf⟩).symm.trans hc⟩
      · exact ⟨f, hf, (hfixed f ⟨v, hv, hf⟩).trans hc⟩
    exact not_congr same
  have hbMissing : beta ∈ MissingColors G mu b₂ :=
    (TwoColorComponentSwapMissingBehavior G sigma gamma beta hgb hsproper
      (Sum.inl b₂)).2.1 b₂ (show Sum.inl b₂ ∈ K₂ from rfl) hgSigma
  have rebuild :=
    @helper_rebuild_367 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T phi ett hMP hpositive hproper hone hlower base H good q alpha beta hne b₂ gamma
        sigma i₁ i₂ hiorder hspos hsT hAB hCT hBCstrict hBCadjoin hproperMu honeMu hfixed
        hmissingFixed
  obtain ⟨corrC, baseC, KC, goodC, hMPC, hdiv⟩ := rebuild
  have elementaryC : ColoredVertexSetElementary G mu (TreeSequenceVertexSet C) :=
    hfewer corrC.replacementETT corrC.rungAgreement hMPC baseC KC goodC
      (by rw [hdiv]; exact hdivider)
  obtain ⟨v, hvA, hbv⟩ := Finset.mem_biUnion.mp betaA
  have hvB := TreeSequenceInitialSegmentVertexSetSubset hAB hvA
  have hvC := TreeSequenceInitialSegmentVertexSetSubset hBC hvB
  have hbCmem : b₂ ∈ TreeSequenceVertexSet C := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last C.length, hbC⟩
  have hvb : v ≠ b₂ := by intro h; exact houtside (h ▸ hvA)
  have hbvMu : beta ∈ MissingColors G mu v := by
    rw [hmissingFixed v hvB]
    exact hbv
  exact (Finset.disjoint_left.mp (elementaryC hvC hbCmem hvb)) hbvMu hbMissing

lemma Step1CaseOneOutsideStar {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (q : ℕ) (hdivider : H.dividerCount < q)
    (hfewer : ∀ {input' : PartialEdgeColoring E k}
      {T' : TreeSequence G e0}
      {generating' : PartialEdgeColoring E k}
      (other : ExtendedTashkinovTree G k e0 input' T' generating'),
      other.rounds = ett.rounds → MaximumProperty other →
      ∀ (base' : HierarchyBase other generating')
        (K : TashkinovHierarchy other base'),
        GoodHierarchy K → K.dividerCount < q →
        ColoredVertexSetElementary G generating'
          (TreeSequenceVertexSet T'))
    (_ : 2 * ett.rounds + 11 ≤
      (TreeMissingColors phi
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)).card)
    (hterminal : TreeColorSetMinusClosed G phi T
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (hElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (alpha beta : Fin k) (_ : alpha ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {alpha})
    (hne : alpha ≠ beta) (hbeta : beta ∈ TreeMissingColors phi T)
    (a₁ b₁ a₂ b₂ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (_ : TreeExitPath T phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath T phi alpha beta a₂ b₂ P₂)
    (_ : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (_ : a₁ ≠ a₂) (_ : b₁ ≠ b₂)
    (horder : TreeVertexOrder T b₁ b₂)
    (f₁ f₂ : E)
    (_ : f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₂ : f₂ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (_ : Incident G b₁ f₁) (hif₂ : Incident G b₂ f₂)
    (_ : Sum.inr f₁ ∈ P₁.support)
    (_ : Sum.inr f₂ ∈ P₂.support)
    (houtside : b₂ ∉ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount))) : False := by
  classical
  have segment_trans {S U W : TreeSequence G e0}
      (hSU : TreeSequenceInitialSegment S U)
      (hUW : TreeSequenceInitialSegment U W) : TreeSequenceInitialSegment S W := by
    exact hSU.trans hUW
  have stage_segment : ∀ (a d : ℕ) (hbound : a + d ≤ H.dividerCount + 1),
      TreeSequenceInitialSegment (H.stage ⟨a, by omega⟩)
        (H.stage ⟨a + d, by omega⟩) := by
    intro a d bound
    exact H.stageInitialSegmentOfLE _ _ (by change a ≤ a + d; exact Nat.le_add_right _ _)
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  have hAT : TreeSequenceInitialSegment A T := by
    by_cases hz : H.dividerCount = 0
    · have hl : Fin.last H.dividerCount = (0 : Fin (H.dividerCount + 1)) :=
        Fin.ext (by simp [hz])
      have ht : (1 : Fin (H.dividerCount + 2)) =
          Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
      simpa [A, hl, HierarchyStarredStage, ht, H.terminalStage] using H.coreInsideFirst
    · have hs : A = H.stage ⟨H.dividerCount, by omega⟩ := by
        unfold A HierarchyStarredStage
        obtain hz' | ⟨i, hi⟩ := Fin.eq_zero_or_eq_succ (Fin.last H.dividerCount)
        · exact False.elim (hz (by simpa using congrArg Fin.val hz'))
        · rw [hi, Fin.cases_succ]
          congr 1
          apply Fin.ext
          simpa using (congrArg Fin.val hi).symm
      have hh := stage_segment H.dividerCount 1 (by omega)
      have ht : (⟨H.dividerCount + 1, by omega⟩ : Fin (H.dividerCount + 2)) =
          Fin.last (H.dividerCount + 1) := Fin.ext rfl
      simpa only [← hs, ht, H.terminalStage] using hh
  have hbT : b₂ ∈ TreeSequenceVertexSet T := hP₂.2.2.2.1
  have betaReserved : beta ∈ (HierarchyTerminalStoredColors H).biUnion
      (good.gamma (Fin.last H.dividerCount)) := by
    by_contra hn
    have hempty := hterminal beta (Finset.mem_sdiff.mpr ⟨hbeta, hn⟩)
    rw [hempty] at hf₂
    exact Finset.notMem_empty _ hf₂
  have betaA : beta ∈ TreeMissingColors phi A := by
    obtain ⟨eta, he, hbe⟩ := Finset.mem_biUnion.mp betaReserved
    exact (GoodHierarchyReservedDisjoint good (Fin.last H.dividerCount)).1 eta
      ((HierarchyTerminalStoredColorsSubsetLast H).1 he) hbe
  have hdegree : MaximumDegree G + 1 ≤ k := by
    have hinit := ett.series.certified 0
    cases hinit with
    | initial triple => exact triple.2.2.1
  obtain ⟨gamma, hgamma⟩ := MissingColorsNonemptyOfMaximumDegree G phi hdegree b₂
  have hgb : gamma ≠ beta := by
    intro h
    have hn : gamma ∉ PresentColors G phi b₂ := by simpa [MissingColors] using hgamma
    apply hn
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨f₂, hif₂, h.symm ▸ (Finset.mem_filter.mp hf₂).2⟩
  have hgReserved : gamma ∉ (HierarchyStoredColorsAt H
      (Fin.last H.dividerCount)).biUnion (good.gamma (Fin.last H.dividerCount)) := by
    intro hg
    obtain ⟨eta, heta, hge⟩ := Finset.mem_biUnion.mp hg
    have hgm := (GoodHierarchyReservedDisjoint good (Fin.last H.dividerCount)).1
      eta heta hge
    obtain ⟨v, hvA, hgv⟩ := Finset.mem_biUnion.mp hgm
    have hvT := TreeSequenceInitialSegmentVertexSetSubset hAT hvA
    have hvb : v ≠ b₂ := by intro h; exact houtside (h ▸ hvA)
    exact (Finset.disjoint_left.mp (hElementary hvT hbT hvb)) hgv hgamma
  have hgTerminal : gamma ∉ (HierarchyTerminalStoredColors H).biUnion
      (good.gamma (Fin.last H.dividerCount)) := by
    intro hg
    obtain ⟨eta, heta, hge⟩ := Finset.mem_biUnion.mp hg
    exact hgReserved (Finset.mem_biUnion.mpr ⟨eta,
      (HierarchyTerminalStoredColorsSubsetLast H).1 heta, hge⟩)
  have hgClosed : TreeColorSetClosed G phi T {gamma} := by
    intro c hc
    have he : c = gamma := Finset.mem_singleton.mp hc
    subst c
    apply hterminal gamma
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨b₂, hbT, hgamma⟩, hgTerminal⟩
  have first : ∃ (sigma : PartialEdgeColoring E k)
      (Q₂ : (TwoColorIncidenceGraph G sigma gamma beta).Walk (Sum.inl a₂) (Sum.inl b₂)),
      IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
      (∀ f, TreeIncidentEdge T f → sigma f = phi f) ∧
      (∀ v ∈ TreeSequenceVertexSet T, MissingColors G sigma v = MissingColors G phi v) ∧
      TreeExitPath T sigma gamma beta a₂ b₂ Q₂ := by
    by_cases hag : alpha = gamma
    · subst gamma
      exact ⟨phi, P₂, hproper, hone, fun _ _ => rfl, fun _ _ => rfl, hP₂⟩
    · obtain ⟨sigma, hrec, hsproper, hsone, hsub, hout, hcopy⟩ :=
        P2716_T1_OutsideExitTransport G T phi alpha gamma beta hag hne hgb
          hproper hone hclosed hgClosed
      obtain ⟨Q₂, hQ₂, _, _⟩ := hcopy T (fun _ h => h) a₂ b₂ P₂ hP₂ hbT
      obtain ⟨_, _, hs, _, fixed⟩ := OutsideKempeRecoloringStable G e0 T ∅
        phi sigma alpha gamma hproper hone hrec
      exact ⟨sigma, Q₂, hsproper, hsone, fixed, hs.2, hQ₂⟩
  obtain ⟨sigma, Q₂, hsproper, hsone, sigma_fixed, sigma_missing, hQ₂⟩ := first
  have hgSigma : gamma ∈ MissingColors G sigma b₂ := by
    rw [sigma_missing b₂ hbT]
    exact hgamma
  obtain ⟨i₁, i₂, hi₁, hi₂, hiorder⟩ := horder
  have hAs : A.length < i₂.val := by
    by_contra h
    have hiA : i₂.val ≤ A.length := by omega
    let r : Fin (A.length + 1) := ⟨i₂.val, by omega⟩
    have hr : Fin.castLE (Nat.succ_le_succ hAT.1) r = i₂ := Fin.ext rfl
    have hv : A.vertex r = b₂ :=
      (hAT.2.1 r).symm.trans (by simpa only [hr] using hi₂)
    apply houtside
    change b₂ ∈ TreeSequenceVertexSet A
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨r, hv⟩
  have hspos : 1 ≤ i₂.val - 1 := by have := A.positive; omega
  have hsT : i₂.val ≤ T.length := Nat.le_of_lt_succ i₂.isLt
  let Bminus := TreeSequencePrefix T (i₂.val - 1) hspos (by omega)
  let C := TreeSequencePrefix T i₂.val (by omega) hsT
  have hAB : TreeSequenceInitialSegment A Bminus := by
    refine ⟨by simpa [Bminus, TreeSequencePrefix] using (show A.length ≤ i₂.val - 1 by omega),
      ?_, ?_⟩
    · intro i
      change T.vertex (Fin.castLE _ (Fin.castLE _ i)) = A.vertex i
      exact hAT.2.1 i
    · intro i
      change T.edge (Fin.castLE _ (Fin.castLE _ i)) = A.edge i
      exact hAT.2.2 i
  have hBC : TreeSequenceInitialSegment Bminus C := by
    refine ⟨by simp [Bminus, C, TreeSequencePrefix], ?_, ?_⟩
    · intro i; rfl
    · intro i; rfl
  have hCT : TreeSequenceInitialSegment C T := ⟨hsT, fun _ => rfl, fun _ => rfl⟩
  have hBT := segment_trans hBC hCT
  have hBCstrict : Bminus.length < C.length := by
    simp only [Bminus, C, TreeSequencePrefix]
    omega
  have hbC : C.vertex (Fin.last C.length) = b₂ := by
    change T.vertex ⟨i₂.val, _⟩ = b₂
    exact hi₂
  have hbNotB : b₂ ∉ TreeSequenceVertexSet Bminus := by
    intro hb
    obtain ⟨r, hr⟩ := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hb
    have heq := T.vertex_injective ((hBT.2.1 r).trans (hr.trans hi₂.symm))
    have hv := congrArg Fin.val heq
    have hrl := r.isLt
    change r.val < i₂.val - 1 + 1 at hrl
    simp only [Fin.val_castLE] at hv
    omega
  have hBCadjoin : ∃ g, TreeSequenceAdjoinEdge Bminus g C := by
    have hlen : C.length = Bminus.length + 1 := by
      simp only [Bminus, C, TreeSequencePrefix]
      omega
    exact ⟨C.edge (Fin.cast hlen.symm (Fin.last Bminus.length)), hlen, hBC, rfl⟩
  exact helper_continuation_1138 (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hMP) (@hpositive)
      (@hproper) (@hone) (@hlower) (@base) (@H) (@good) (@q) (@hdivider) (@hfewer) (@alpha)
      (@beta) (@hne) (@a₂) (@b₂) (@houtside) (@betaA) (@gamma) (@hgb) (@sigma) (@Q₂) (@hsproper)
      (@hsone) (@sigma_fixed) (@hQ₂) (@hgSigma) (@i₁) (@i₂) (@hiorder) (@hspos) (@hsT) (@hAB)
      (@hBC) (@hCT) (@hBT) (@hBCstrict) (@hbC) (@hbNotB) (@hBCadjoin)
end GoldbergSeymour

end
