/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HkuParallelBoundaryStructure

public import LeanPool.GoldbergSeymour.TreeColorSetClosed

/-!
# Parallel Common Missing Closed

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_branch_238.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
          PartialEdgeColoring E k)
      (T : TreeSequence G e0) (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
      (base : HierarchyBase ett phi),
      phi = ett.series.data.coloring (Fin.last ett.rounds) →
        let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
        let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
        let q : Fin ett.rounds :=
          (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) <
              ett.rounds) => by omega⟩ :
            Fin ett.rounds);
        ∀ (gamma : Fin k)
          (choice :
            MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
              (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring
                  q.castSucc)),
          BoundaryColorEdges G (ett.series.data.coloring q.succ)
                  (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) gamma =
                {choice.edge} ∧
              (∀
                  g ∈
                    BoundaryColorEdges G (ett.series.data.coloring q.succ)
                      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color,
                  ∃ (w : V), TreeVertexOrder (ett.series.data.tree q.succ.castSucc) w
                      choice.vertex ∧ Incident G w g) ∧
                (ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
                    (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
                  ∀ alpha ∈ TreeMissingColors (ett.series.data.coloring q.succ)
                      (ett.series.data.tree q.succ.castSucc),
                    alpha ≠ choice.color →
                      BoundaryColorEdges G (ett.series.data.coloring q.succ)
                          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) alpha =
                        ∅) →
            Tn = ett.series.data.tree q.succ.castSucc →
              choice.vertex = Tn.vertex base.supportPosition →
                q.succ = Fin.last ett.rounds →
                  ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
                      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
                    TreeSequenceVertexSet base.core = TreeSequenceVertexSet Tn ∪
                        TreeSequenceVertexSet base.closure →
                      TreeSequenceVertexSet Tn ⊆ TreeSequenceVertexSet base.core →
                        TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet base.core →
                          (∀ {w : V},
                              TreeVertexOrder Tn w (Tn.vertex base.supportPosition) →
                                w ∈ TreeSequenceVertexSet base.closure) →
                            ∀
                              alpha ∈
                                TreeMissingColors phi (ett.series.data.tree (Fin.last
                                    ett.rounds).castSucc) ∩
                                  TreeMissingColors phi base.closure,
                              alpha ∈ TreeMissingColors phi (ett.series.data.tree (Fin.last
                                  ett.rounds).castSucc) →
                                alpha ∈ TreeMissingColors phi base.closure →
                                  ∀ (y : V),
                                    alpha ∈ MissingColors G phi y →
                                      ∀ g ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet
                                          base.core) alpha,
                                        phi g = some alpha →
                                          ∀ p ∈ TreeSequenceVertexSet base.core,
                                            ∀ r ∉ TreeSequenceVertexSet base.core,
                                              G.ends g = s(p, r) → p ∉ TreeSequenceVertexSet
                                                  base.closure → False := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett hpositive base hphi n Tn q gamma choice
      hboundary hTn hchoice hindex helem coreVertices hX hY hpreVertex alpha halpha halphaX
      halphaY y hymiss g hg hcolor p hp r hr hends hpY
  have hpX : p ∈ TreeSequenceVertexSet Tn := by
    have : p ∈ TreeSequenceVertexSet Tn ∪
        TreeSequenceVertexSet base.closure := by
      rw [← coreVertices]
      exact hp
    exact Finset.mem_union.mp this |>.resolve_right hpY
  have hrX : r ∉ TreeSequenceVertexSet Tn := by
    intro hrX
    apply hr
    exact hX hrX
  have hbX : g ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) := by
      simpa [BoundaryEdges] using
        (show ∃ u ∈ TreeSequenceVertexSet Tn, ∃ v ∉
            TreeSequenceVertexSet Tn, G.ends g = s(u, v) from
          ⟨p, hpX, r, hrX, hends⟩)
  have hcgX : g ∈ BoundaryColorEdges G phi
      (TreeSequenceVertexSet Tn) alpha := by
    simp [BoundaryColorEdges, hbX, hcolor]
  have hcgX' := hcgX
  rw [hphi, ← hindex, hTn] at hcgX'
  have hworderT : ∀ {w : V},
      TreeVertexOrder (ett.series.data.tree q.succ.castSucc) w choice.vertex →
      TreeVertexOrder Tn w (Tn.vertex base.supportPosition) := by
    intro w hw
    simpa [hTn, hchoice] using hw
  by_cases halphaDelta : alpha = choice.color
  · subst alpha
    obtain ⟨w, hworder, hincident⟩ := hboundary.2.1 g hcgX'
    have hwX : w ∈ TreeSequenceVertexSet Tn := by
      have hworder' := hworderT hworder
      unfold TreeVertexOrder at hworder'
      obtain ⟨i, j, hi, hj, hij⟩ := hworder'
      unfold TreeSequenceVertexSet
      simp only [Finset.mem_image]
      exact ⟨i, Finset.mem_univ _, hi⟩
    have hwY : w ∈ TreeSequenceVertexSet base.closure := by
      apply hpreVertex
      exact hworderT hworder
    have hwends : w = p ∨ w = r := by
      change w ∈ G.ends g at hincident
      rw [hends] at hincident
      simpa using hincident
    cases hwends with
    | inl hwp => exact hpY (hwp ▸ hwY)
    | inr hwr => exact hr (hY (hwr ▸ hwY))
  · have halphaX' := halphaX
    rw [hphi, ← hindex] at halphaX'
    have hempty := hboundary.2.2 helem alpha halphaX' halphaDelta
    rw [hempty] at hcgX'
    simp at hcgX'

private theorem helper_continuation_360.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
          PartialEdgeColoring E k)
      (T : TreeSequence G e0) (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
      (base : HierarchyBase ett phi),
      phi = ett.series.data.coloring (Fin.last ett.rounds) →
        let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
        let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
        let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
        ∀ (gamma : Fin k)
          (choice :
            MaximumDefectiveChoice G e0 (ett.series.data.tree q.succ.castSucc)
              (TashkinovStoredColors ett.series.data q.castSucc) (ett.series.data.coloring
                  q.castSucc)),
          BoundaryColorEdges G (ett.series.data.coloring q.succ)
                  (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) gamma =
                ({choice.edge} : Finset E) ∧
              (∀
                  g ∈
                    BoundaryColorEdges G (ett.series.data.coloring q.succ)
                      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) choice.color,
                  ∃ (w : V), TreeVertexOrder (ett.series.data.tree q.succ.castSucc) w
                      choice.vertex ∧ Incident G w g) ∧
                (ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
                    (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
                  ∀ alpha ∈ TreeMissingColors (ett.series.data.coloring q.succ)
                      (ett.series.data.tree q.succ.castSucc),
                    alpha ≠ choice.color →
                      BoundaryColorEdges G (ett.series.data.coloring q.succ)
                          (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) alpha =
                        ∅) →
            Tn = ett.series.data.tree q.succ.castSucc →
              choice.vertex = Tn.vertex base.supportPosition →
                q.succ = Fin.last ett.rounds →
                  ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
                      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) →
                    TreeSequenceVertexSet base.core = TreeSequenceVertexSet Tn ∪
                        TreeSequenceVertexSet base.closure →
                      ColoredVertexSetClosed G phi (TreeSequenceVertexSet base.closure) →
                        TreeSequenceVertexSet Tn ⊆ TreeSequenceVertexSet base.core →
                          TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet base.core →
                            (∀ {w : V},
                                TreeVertexOrder Tn w (Tn.vertex base.supportPosition) →
                                  w ∈ TreeSequenceVertexSet base.closure) →
                              ∀
                                alpha ∈
                                  (TreeMissingColors phi (ett.series.data.tree (Fin.last
                                      ett.rounds).castSucc) ∩
                                      TreeMissingColors phi base.closure :
                                    Finset (Fin k)),
                                BoundaryColorEdges G phi (TreeSequenceVertexSet base.core) alpha
                                    = ∅ := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett hpositive base hphi n Tn q gamma choice
      hboundary hTn hchoice hindex helem coreVertices hclosed hX hY hpreVertex alpha halpha
  obtain ⟨halphaX, halphaY⟩ := Finset.mem_inter.mp halpha
  have alphaMissing : ∃ y : V, y ∈ TreeSequenceVertexSet base.closure ∧
      alpha ∈ MissingColors G phi y := by
    unfold TreeMissingColors at halphaY
    exact Finset.mem_biUnion.mp halphaY
  obtain ⟨y, hy, hymiss⟩ := alphaMissing
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have hg' : g ∈ BoundaryEdges G (TreeSequenceVertexSet base.core) ∧
      phi g = some alpha := by
    simpa [BoundaryColorEdges] using hg
  obtain ⟨hb, hcolor⟩ := hg'
  have hb' : ∃ u ∈ TreeSequenceVertexSet base.core, ∃ v ∉
      TreeSequenceVertexSet base.core, G.ends g = s(u, v) := by
    simpa [BoundaryEdges] using hb
  obtain ⟨p, hp, r, hr, hends⟩ := hb'
  by_cases hpY : p ∈ TreeSequenceVertexSet base.closure
  · have hrY : r ∉ TreeSequenceVertexSet base.closure := by
      intro hrY
      apply hr
      exact hY hrY
    have hbY : g ∈ BoundaryEdges G (TreeSequenceVertexSet base.closure) := by
        simpa [BoundaryEdges] using
          (show ∃ u ∈ TreeSequenceVertexSet base.closure, ∃ v ∉
              TreeSequenceVertexSet base.closure, G.ends g = s(u, v) from
            ⟨p, hpY, r, hrY, hends⟩)
    have hcgY : g ∈ BoundaryColorEdges G phi
        (TreeSequenceVertexSet base.closure) alpha := by
      simp [BoundaryColorEdges, hbY, hcolor]
    have hnot := hclosed hbY hy hcolor
    exact (hnot (by simpa [MissingColors] using hymiss)).elim
  · exact @helper_branch_238 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T generating phi ett hpositive base hphi gamma choice hboundary hTn hchoice hindex
      helem coreVertices hX hY hpreVertex alpha halpha halphaX halphaY y hymiss g hg hcolor p hp
      r hr hends hpY

private theorem helper_branch_69.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input :
          PartialEdgeColoring E k)
      (T : TreeSequence G e0) (generating phi : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds)
      (base : HierarchyBase ett phi),
      phi = ett.series.data.coloring (Fin.last ett.rounds) →
        ett.series.data.kind (Fin.last ett.rounds) = some TashkinovExtensionKind.PE →
          (let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
            ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
              (TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc))) →
            let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
            let _ : TreeSequence G e0 := ett.series.data.tree n.castSucc;
            let q : Fin ett.rounds :=
              (⟨ett.rounds - (1 : ℕ), Decidable.byContradiction fun (a : ¬ett.rounds - (1 : ℕ) <
                  ett.rounds) => by omega⟩ :
                Fin ett.rounds);
            q.succ = n →
              ∀ (ci : Fin ett.rounds),
                IsProperEdgeColoring G (ett.series.data.coloring ci.castSucc) →
                  IsOneEdgeUncolored (ett.series.data.coloring ci.castSucc) e0 →
                    ColoredVertexSetClosed G (ett.series.data.coloring ci.castSucc)
                        (TreeSequenceVertexSet (ett.series.data.tree ci.succ.castSucc)) →
                      ¬ColoredVertexSetStronglyClosed G (ett.series.data.coloring ci.castSucc)
                            (TreeSequenceVertexSet (ett.series.data.tree ci.succ.castSucc)) →
                        ¬Nonempty (RevisitingExtensionCertificate ett.series.data ci.castSucc) →
                          ∀
                            (choice :
                              MaximumDefectiveChoice G e0 (ett.series.data.tree ci.succ.castSucc)
                                (TashkinovStoredColors ett.series.data ci.castSucc)
                                    (ett.series.data.coloring ci.castSucc)),
                            (∃ (rho : PartialEdgeColoring E k),
                                IsProperEdgeColoring G rho ∧
                                  IsOneEdgeUncolored rho e0 ∧
                                    StableColoring (ett.series.data.tree ci.succ.castSucc)
                                        (insert choice.color (TashkinovStoredColors
                                            ett.series.data ci.castSucc))
                                        choice.selected rho ∧
                                      ¬Disjoint (MissingColors G rho choice.otherEndpoint)
                                          (TreeMissingColors rho (ett.series.data.tree
                                              ci.succ.castSucc))) →
                              ∀ (gamma : Fin k),
                                ParallelExtensionColor ett.series.data ci.castSucc
                                    choice.selected choice.vertex gamma →
                                  ∀ (secondStable : PartialEdgeColoring E k),
                                    StableColoring (ett.series.data.tree ci.succ.castSucc)
                                        (insert choice.color (TashkinovStoredColors
                                            ett.series.data ci.castSucc))
                                        choice.selected secondStable →
                                      TreeExit (ett.series.data.tree ci.succ.castSucc)
                                          secondStable gamma choice.color
                                          choice.vertex →
                                        ett.series.data.coloring ci.succ =
                                            TwoColorComponentSwap G secondStable gamma choice.color
                                              (Sum.inl choice.vertex) →
                                          IsProperEdgeColoring G (ett.series.data.coloring
                                              ci.succ) →
                                            IsOneEdgeUncolored (ett.series.data.coloring ci.succ)
                                                e0 →
                                              ett.series.data.stored ci.succ = {choice.color,
                                                  gamma} →
                                                ett.series.data.connectingEdges ci.succ =
                                                    {choice.edge} →
                                                  ett.series.data.kind ci.succ = some
                                                      TashkinovExtensionKind.PE →
                                                    ett.series.data.chosenVertex ci.succ = some
                                                        choice.vertex →
                                                      ett.series.data.outsideVertex ci.succ =
                                                          some choice.otherEndpoint →
                                                        ett.series.data.delta ci.succ = some
                                                            choice.color →
                                                          ett.series.data.gamma ci.succ = some
                                                              gamma →
                                                            TashkinovClosure
                                                                (ett.series.data.coloring ci.succ)
                                                                (ett.series.data.tree
                                                                    ci.succ.castSucc)
                                                                (ett.series.data.tree
                                                                    ci.succ.succ) →
                                                              TreeSequenceInitialSegment
                                                                  (ett.series.data.tree
                                                                      ci.succ.castSucc)
                                                                  (ett.series.data.tree
                                                                      ci.succ.succ) →
                                                                (ett.series.data.tree
                                                                    ci.succ.castSucc).length <
                                                                    (ett.series.data.tree
                                                                        ci.succ.succ).length →
                                                                  q.succ = ci.succ →
                                                                    let Tn : TreeSequence G e0 :=
                                                                      ett.series.data.tree
                                                                          (Fin.last
                                                                          ett.rounds).castSucc;
                                                                    TreeColorSetClosed G phi
                                                                        base.core
                                                                      (TreeMissingColors phi Tn ∩
                                                                        TreeMissingColors phi
                                                                            base.closure) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating phi ett hpositive base hphi hPE hlowerElementary n
      Tn q hsucc ci previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable
      secondStableRelation exitWitness currentColoring currentProper currentOneUncolored
      currentStored currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension target_eq
  have hci : ci = q := by
    apply Fin.ext
    have hv := congrArg Fin.val target_eq
    simp at hv
    omega
  subst ci
  have hboundary := HkuParallelBoundaryStructure G k ett.rounds e0 input ett.series q
    choice.edge choice.color gamma choice.vertex
    (by simpa using currentKind) (by simpa using currentEdges)
    (by simpa using currentDelta) (by simpa using currentGamma)
    (by simpa using currentVertex)
  have hTn : Tn = ett.series.data.tree q.succ.castSucc := by
    simpa [Tn] using congrArg
      (fun z : Fin (ett.rounds + 1) => ett.series.data.tree z.castSucc) hsucc.symm
  have hchoice : choice.vertex = Tn.vertex base.supportPosition := by
    have hp := (base.parallel hPE).1
    change ett.series.data.chosenVertex n =
      some (Tn.vertex base.supportPosition) at hp
    rw [← hsucc] at hp
    have hc : ett.series.data.chosenVertex q.succ = some choice.vertex := currentVertex
    exact Option.some.inj (hc.symm.trans hp)
  have hindex : q.succ = Fin.last ett.rounds := by
    simpa [n] using hsucc
  have helem : ColoredVertexSetElementary G
      (ett.series.data.coloring q.castSucc)
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) := by
    unfold ColoredVertexSetElementary at hlowerElementary ⊢
    have hqsucc : q.succ = Fin.last ett.rounds := by
      apply Fin.ext
      simp [q]
      omega
    rw [hqsucc]
    intro u hu v hv huv
    exact hlowerElementary hu hv huv
  have initialVertices : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hab x hx
    unfold TreeSequenceVertexSet at hx ⊢
    simp only [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨hlen, hvertices, hedges⟩ := hab
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, ?_⟩
    exact hvertices i
  have prefixClosure : TashkinovClosure phi
      (TreeSequencePrefix Tn base.supportPosition.val base.supportPositive
        (Nat.le_of_lt_succ base.supportPosition.isLt)) base.closure := by
    exact (base.parallel hPE).2.1
  have vertexReach : ∀ {A B : TreeSequence G e0},
      TashkinovAugmentationSequence phi A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hab
    unfold TashkinovAugmentationSequence at hab
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => exact Finset.Subset.rfl
    | @head A B hstep htail ih =>
      intro x hx
      obtain ⟨hlen, hvertices, hedges⟩ := hstep.2.1
      apply ih
      apply initialVertices hstep.2.1
      exact hx
  have prefixInClosure : TreeSequenceVertexSet
      (TreeSequencePrefix Tn base.supportPosition.val base.supportPositive
        (Nat.le_of_lt_succ base.supportPosition.isLt)) ⊆
      TreeSequenceVertexSet base.closure := vertexReach prefixClosure.1
  obtain ⟨orderedUnion⟩ := (base.parallel hPE).2.2
  have coreVertices : TreeSequenceVertexSet base.core =
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet base.closure := by
    rw [← orderedUnion.vertexSet]
  have hclosed : ColoredVertexSetClosed G phi
      (TreeSequenceVertexSet base.closure) := prefixClosure.2
  have hX : TreeSequenceVertexSet Tn ⊆
      TreeSequenceVertexSet base.core := by
    rw [coreVertices]
    exact Finset.subset_union_left
  have hY : TreeSequenceVertexSet base.closure ⊆
      TreeSequenceVertexSet base.core := by
    rw [coreVertices]
    exact Finset.subset_union_right
  have hpreVertex : ∀ {w : V}, TreeVertexOrder Tn w
      (Tn.vertex base.supportPosition) → w ∈ TreeSequenceVertexSet base.closure := by
    intro w hw
    obtain ⟨i, j, hi, hj, hij⟩ := hw
    have hj' : j = base.supportPosition := Tn.vertex_injective hj
    subst j
    have hi' : i.val < base.supportPosition.val := hij
    apply prefixInClosure
    unfold TreeSequenceVertexSet
    simp only [Finset.mem_image]
    let i' : Fin (base.supportPosition.val + 1) := ⟨i.val, by omega⟩
    refine ⟨i', Finset.mem_univ _, ?_⟩
    simpa [TreeSequencePrefix, i'] using hi
  unfold TreeColorSetClosed
  dsimp
  exact @helper_continuation_360 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@phi) (@ett) (@hpositive)
      (@base) (@hphi) (@gamma) (@choice) (@hboundary) (@hTn) (@hchoice) (@hindex) (@helem)
      (@coreVertices) (@hclosed) (@hX) (@hY) (@hpreVertex)
theorem ParallelCommonMissingClosed {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hpositive : 0 < ett.rounds)
    (base : HierarchyBase ett phi)
    (hphi : phi = ett.series.data.coloring (Fin.last ett.rounds))
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hlowerElementary :
      let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
      ColoredVertexSetElementary G
        (ett.series.data.coloring q.castSucc)
        (TreeSequenceVertexSet
          (ett.series.data.tree (Fin.last ett.rounds).castSucc))) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    TreeColorSetClosed G phi base.core
      (TreeMissingColors phi Tn ∩ TreeMissingColors phi base.closure) := by
  classical
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  have hq : 0 < ett.rounds := hpositive
  let q : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hsucc : q.succ = n := by
    apply Fin.ext
    simp only [Fin.succ_mk, Fin.last, q, n]
    omega
  generalize target_eq : q.succ = target
  cases ett.series.certified target with
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
          exact @helper_branch_69 V E inferInstance inferInstance inferInstance inferInstance G k
              e0 input T generating phi ett hpositive base hphi hPE hlowerElementary hsucc ci
              previousProper previousOneUncolored previousClosed previousNotStronglyClosed
              noRevisiting choice seriesAlternativeFails gamma gammaRule secondStable
              secondStableRelation exitWitness currentColoring currentProper currentOneUncolored
              currentStored currentEdges currentKind currentVertex currentOutside currentDelta
              currentGamma closedExtension orderedExtension strictExtension target_eq
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero q target_eq).elim
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hv := congrArg Fin.val target_eq
    simp at hv
    have hci : ci = q := by ext; omega
    subst ci
    change ett.series.data.kind n = some TashkinovExtensionKind.PE at hPE
    rw [← hsucc] at hPE
    rw [currentKind] at hPE
    simp at hPE
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hv := congrArg Fin.val target_eq
    simp at hv
    have hci : ci = q := by ext; omega
    subst ci
    change ett.series.data.kind n = some TashkinovExtensionKind.PE at hPE
    rw [← hsucc] at hPE
    rw [currentKind] at hPE
    simp at hPE

end GoldbergSeymour

end
