/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBase
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.TechnicalInductionContext

/-!
# Parallel Terminal PEPreprocessing

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation991Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi), TechnicalInductionContext G k e0 ett.rounds → MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.PE →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 →
    ∀ (base : HierarchyBase ett sigma), StableColoring (ett.series.data.tree (Fin.last ett.rounds
        : Fin (ett.rounds + (1 : ℕ))).castSucc) (TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds : Fin (ett.rounds + (1 : ℕ)))) (ett.series.data.coloring (Fin.last ett.rounds :
        Fin (ett.rounds + (1 : ℕ)))) sigma →
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (secondStableProper :
        IsProperEdgeColoring G secondStable) (secondStableOneUncolored : IsOneEdgeUncolored
        secondStable e0) (previousProper : IsProperEdgeColoring G (ett.series.data.coloring
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc)) (previousOneUncolored : IsOneEdgeUncolored
        (ett.series.data.coloring ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) e0), ColoredVertexSetClosed G
        (ett.series.data.coloring ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ.castSucc)) →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ.castSucc) (TashkinovStoredColors ett.series.data
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) (ett.series.data.coloring ((⟨ett.rounds - (1 :
        ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc)), ett.series.data.coloring ((⟨ett.rounds - (1
        : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = TwoColorComponentSwap G secondStable gamma
        choice.color (Sum.inl choice.vertex) → IsProperEdgeColoring G (ett.series.data.coloring
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ) → IsOneEdgeUncolored (ett.series.data.coloring
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ) e0 → ett.series.data.connectingEdges ((⟨ett.rounds
        - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = { choice.edge } → ett.series.data.kind
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = some choice.vertex → ett.series.data.delta
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = some choice.color → ett.series.data.gamma
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = some gamma → (Fin.last ett.rounds : Fin
        (ett.rounds + (1 : ℕ))) = ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ → Fin.last ett.rounds = ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ → ett.series.data.tree (Fin.last ett.rounds : Fin
        (ett.rounds + (1 : ℕ))).castSucc = ett.series.data.tree ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ.castSucc → choice.vertex ∈ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc) → gamma
        ∈ MissingColors G secondStable choice.vertex → secondStable choice.edge = some
        choice.color → gamma ≠ choice.color → choice.edge ∈ BoundaryEdges G (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc)) → (
    ∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc)) → TreeIncidentEdge
        (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc) f) →
        ColoredVertexSetElementary G (ett.series.data.coloring ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc)) → StableColoring
        (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc)
        (TashkinovStoredColors ett.series.data ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) (ett.series.data.coloring ((⟨ett.rounds - (1 :
        ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) choice.selected → StableColoring
        (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc) (insert
        choice.color (TashkinovStoredColors ett.series.data ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc)) choice.selected secondStable →
    let previousSubtype : { psi : PartialEdgeColoring E k // IsProperEdgeColoring G psi ∧
        IsOneEdgeUncolored psi e0 } := (⟨ett.series.data.coloring ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc, (⟨previousProper, previousOneUncolored⟩ :
        IsProperEdgeColoring G (ett.series.data.coloring ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) ∧ IsOneEdgeUncolored (ett.series.data.coloring
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) e0)⟩ : { psi : PartialEdgeColoring E k //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0 });
    let selectedSubtype : { psi : PartialEdgeColoring E k // IsProperEdgeColoring G psi ∧
        IsOneEdgeUncolored psi e0 } := (⟨choice.selected, (⟨choice.selectedProper,
        choice.selectedOneUncolored⟩ : IsProperEdgeColoring G choice.selected ∧ IsOneEdgeUncolored
        choice.selected e0)⟩ : { psi : PartialEdgeColoring E k // IsProperEdgeColoring G psi ∧
        IsOneEdgeUncolored psi e0 });
    let secondSubtype : { psi : PartialEdgeColoring E k // IsProperEdgeColoring G psi ∧
        IsOneEdgeUncolored psi e0 } := (⟨secondStable, (⟨secondStableProper,
        secondStableOneUncolored⟩ : IsProperEdgeColoring G secondStable ∧ IsOneEdgeUncolored
        secondStable e0)⟩ : { psi : PartialEdgeColoring E k // IsProperEdgeColoring G psi ∧
        IsOneEdgeUncolored psi e0 }); StableColoring (ett.series.data.tree (Fin.last ett.rounds :
        Fin (ett.rounds + (1 : ℕ))).castSucc) (TashkinovStoredColors ett.series.data ((⟨ett.rounds
        - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) (↑selectedSubtype : PartialEdgeColoring E k)
        (↑previousSubtype : PartialEdgeColoring E k) → StableColoring (ett.series.data.tree
        (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc)) (↑secondSubtype : PartialEdgeColoring E k)
        (↑selectedSubtype : PartialEdgeColoring E k) →
    ∃ (support : V) (common : V) (gamma : Fin k) (delta : Fin k), ett.series.data.chosenVertex
        (Fin.last ett.rounds) = some support ∧ ett.series.data.gamma (Fin.last ett.rounds) = some
        gamma ∧ ett.series.data.delta (Fin.last ett.rounds) = some delta ∧ support ∈
        TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∧ support ∈
        TreeSequenceVertexSet base.closure ∧ common ∈ TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) ∧ common ∈ TreeSequenceVertexSet base.closure ∧ common ≠
        support ∧ delta ∈ MissingColors G sigma support ∧ gamma ∉ TreeMissingColors sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∧ (MissingColors G sigma
        common).Nonempty ∧ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc))

private theorem helper_hPreviousElementary_238.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi),
    TechnicalInductionContext G k e0 ett.rounds →
    MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ColoredVertexSetElementary G (ett.series.data.coloring previous.castSucc)
      (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx hMP hpositive terminal previous
  by_cases hOne : ett.rounds = 1
  · have hbase : ColoredVertexSetElementary G
        (ett.series.data.coloring 0)
        (TreeSequenceVertexSet
          (ett.series.data.tree (⟨1, by omega⟩ :
            Fin (ett.rounds + 2)))) :=
      (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
    have hTerminalOne : terminal.castSucc =
        (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simp [terminal, hOne]
    have hPreviousZero : previous.castSucc =
        (0 : Fin (ett.rounds + 1)) := by
      apply Fin.ext
      simp [previous, hOne]
    simpa only [hTerminalOne, hPreviousZero] using hbase
  · have hrPositive : 1 ≤ ett.rounds - 1 := by omega
    have hrBefore : ett.rounds - 1 < ett.rounds := by omega
    obtain ⟨restricted, hRounds, hRestrictedMP, hRestrictedTrees,
        hRestrictedData⟩ :=
      CertifiedETTRestriction G k e0 input T phi ett hMP
        (ett.rounds - 1) hrPositive hrBefore
    have hLower : ColoredVertexSetElementary G
        (ett.series.data.coloring
          (⟨ett.rounds - 1, by omega⟩ : Fin (ett.rounds + 1)))
        (TreeSequenceVertexSet
          (ett.series.data.tree
            (⟨(ett.rounds - 1) + 1, by omega⟩ :
              Fin (ett.rounds + 2)))) :=
      ctx.lowerOne restricted (by omega) (by omega) hRestrictedMP
    have hLowerTree :
        (ett.series.data.tree
          (⟨(ett.rounds - 1) + 1, by omega⟩ :
            Fin (ett.rounds + 2))) =
          ett.series.data.tree terminal.castSucc := by
      congr 1
      apply Fin.ext
      simp [terminal]
      omega
    have hLowerColor :
        (ett.series.data.coloring
          (⟨ett.rounds - 1, by omega⟩ :
            Fin (ett.rounds + 1))) =
          ett.series.data.coloring previous.castSucc := by
      congr 1
    simpa only [hLowerTree, hLowerColor] using hLower

private theorem helper_hSecondClosed_343.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (secondStable : PartialEdgeColoring E k) (secondStableProper : IsProperEdgeColoring G
        secondStable) (secondStableOneUncolored : IsOneEdgeUncolored secondStable e0)
        (previousProper : IsProperEdgeColoring G (ett.series.data.coloring previous.castSucc))
        (previousOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring previous.castSucc)
        e0), ColoredVertexSetClosed G (ett.series.data.coloring previous.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree previous.succ.castSucc)) →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree previous.succ.castSucc)
        (TashkinovStoredColors ett.series.data previous.castSucc) (ett.series.data.coloring
        previous.castSucc)), ett.series.data.tree terminal.castSucc = ett.series.data.tree
        previous.succ.castSucc → (
    ∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet (ett.series.data.tree
        terminal.castSucc)) → TreeIncidentEdge (ett.series.data.tree terminal.castSucc) f) →
        StableColoring (ett.series.data.tree terminal.castSucc) (TashkinovStoredColors
        ett.series.data previous.castSucc) (ett.series.data.coloring previous.castSucc)
        choice.selected → StableColoring (ett.series.data.tree terminal.castSucc) (insert
        choice.color (TashkinovStoredColors ett.series.data previous.castSucc)) choice.selected
        secondStable →
    let previousSubtype : { psi : PartialEdgeColoring E k // IsProperEdgeColoring G psi ∧
        IsOneEdgeUncolored psi e0 } := (⟨ett.series.data.coloring previous.castSucc,
        (⟨previousProper, previousOneUncolored⟩ : IsProperEdgeColoring G (ett.series.data.coloring
        previous.castSucc) ∧ IsOneEdgeUncolored (ett.series.data.coloring previous.castSucc) e0)⟩
        : { psi : PartialEdgeColoring E k // IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi
        e0 });
    let selectedSubtype : { psi : PartialEdgeColoring E k // IsProperEdgeColoring G psi ∧
        IsOneEdgeUncolored psi e0 } := (⟨choice.selected, (⟨choice.selectedProper,
        choice.selectedOneUncolored⟩ : IsProperEdgeColoring G choice.selected ∧ IsOneEdgeUncolored
        choice.selected e0)⟩ : { psi : PartialEdgeColoring E k // IsProperEdgeColoring G psi ∧
        IsOneEdgeUncolored psi e0 });
    let secondSubtype : { psi : PartialEdgeColoring E k // IsProperEdgeColoring G psi ∧
        IsOneEdgeUncolored psi e0 } := (⟨secondStable, (⟨secondStableProper,
        secondStableOneUncolored⟩ : IsProperEdgeColoring G secondStable ∧ IsOneEdgeUncolored
        secondStable e0)⟩ : { psi : PartialEdgeColoring E k // IsProperEdgeColoring G psi ∧
        IsOneEdgeUncolored psi e0 }); StableColoring (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data previous.castSucc) (↑selectedSubtype :
        PartialEdgeColoring E k) (↑previousSubtype : PartialEdgeColoring E k) → StableColoring
        (ett.series.data.tree terminal.castSucc) (insert choice.color (TashkinovStoredColors
        ett.series.data previous.castSucc)) (↑secondSubtype : PartialEdgeColoring E k)
        (↑selectedSubtype : PartialEdgeColoring E k) → ColoredVertexSetClosed G secondStable
        (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive terminal previous secondStable
      secondStableProper secondStableOneUncolored previousProper previousOneUncolored
      previousClosed choice hTreeEq boundaryIncident hSelectedStable hSecondStable
      previousSubtype selectedSubtype secondSubtype hSelectedReverseSubtype hSecondReverseSubtype
      f c v hfBoundary hv hfColor hcMissing
  have hfIncident := boundaryIncident hfBoundary
  have hTreeMissingSecond : c ∈ TreeMissingColors secondStable
      (ett.series.data.tree terminal.castSucc) := by
    rw [TreeMissingColors]
    exact Finset.mem_biUnion.mpr ⟨v, hv, hcMissing⟩
  have hSelectedColor : choice.selected f = some c := by
    have hfix := hSecondReverseSubtype.1 f hfIncident
      ⟨c, Finset.mem_union_left _ hTreeMissingSecond, hfColor⟩
    exact hfix.trans hfColor
  have hSelectedMissing : c ∈ MissingColors G choice.selected v := by
    rw [← hSecondStable.2 v hv]
    exact hcMissing
  have hTreeMissingSelected : c ∈ TreeMissingColors choice.selected
      (ett.series.data.tree terminal.castSucc) := by
    rw [TreeMissingColors]
    exact Finset.mem_biUnion.mpr ⟨v, hv, hSelectedMissing⟩
  have hPreviousColor :
      ett.series.data.coloring previous.castSucc f = some c := by
    have hfix := hSelectedReverseSubtype.1 f hfIncident
      ⟨c, Finset.mem_union_left _ hTreeMissingSelected,
        hSelectedColor⟩
    exact hfix.trans hSelectedColor
  have hPreviousMissing : c ∈ MissingColors G
      (ett.series.data.coloring previous.castSucc) v := by
    rw [← hSelectedStable.2 v hv]
    exact hSelectedMissing
  have hclosed := previousClosed (f := f) (c := c) (v := v)
    (by simpa only [hTreeEq] using hfBoundary)
    (by simpa only [hTreeEq] using hv) hPreviousColor
  exact hclosed hPreviousMissing

private theorem helper_hPairColors_420.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree previous.succ.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc)), ett.series.data.coloring
        previous.succ = TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl
        choice.vertex) → terminal = previous.succ → gamma ≠ choice.color →
    ∀ (f : E), ett.series.data.coloring terminal f = some gamma ∨ ett.series.data.coloring
        terminal f = some choice.color ↔ secondStable f = some gamma ∨ secondStable f = some
        choice.color := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive terminal previous gamma secondStable choice
      currentColoring hTerminalEq hGammaDelta f
  rw [hTerminalEq, currentColoring]
  by_cases hf : Sum.inr f ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex)
  · by_cases hfg : secondStable f = some gamma
    · constructor
      · intro h
        exact Or.inl hfg
      · intro h
        right
        simp [TwoColorComponentSwap, hf, hfg]
    · by_cases hfd : secondStable f = some choice.color
      · constructor
        · intro h
          exact Or.inr hfd
        · intro h
          left
          simp [TwoColorComponentSwap, hf, hfd,
            hGammaDelta.symm]
      · simp [TwoColorComponentSwap, hf, hfg, hfd]
  · simp [TwoColorComponentSwap, hf]

private theorem helper_hOnlyIncidentComponent_489.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree previous.succ.castSucc)
        (TashkinovStoredColors ett.series.data previous.castSucc) (ett.series.data.coloring
        previous.castSucc)), gamma ∈ MissingColors G secondStable choice.vertex → secondStable
        choice.edge = some choice.color → (
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), Sum.inl x ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) ↔ x =
        choice.vertex) → (
    ∀ (f : E), Sum.inr f ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl
        choice.vertex) → secondStable f = some gamma ∨ secondStable f = some choice.color) →
    ∀ (f : E), TreeIncidentEdge (ett.series.data.tree terminal.castSucc) f → Sum.inr f ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → f =
        choice.edge := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive terminal previous gamma secondStable
      secondStableProper choice hGammaSecond hChoiceSecond hComponentSecond hComponentEdgeColor f
      hfIncident hfComponent
  rcases hfIncident with ⟨x, hx, hxf⟩
  rcases hComponentEdgeColor f hfComponent with hfg | hfd
  · have hpresent : gamma ∈ PresentColors G secondStable x := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨f, hxf, hfg⟩
    have hxComponent : Sum.inl x ∈
        TwoColorComponent G secondStable gamma choice.color
          (Sum.inl choice.vertex) := by
      change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
          (Sum.inl x) =
        (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
          (Sum.inl choice.vertex)
      exact
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (by simp [TwoColorIncidenceGraph, hxf, hfg])).trans hfComponent
    have hxEq := (hComponentSecond x hx).mp hxComponent
    subst x
    have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
      simpa [MissingColors] using hGammaSecond
    exact (hnot hpresent).elim
  · have hxComponent : Sum.inl x ∈
        TwoColorComponent G secondStable gamma choice.color
          (Sum.inl choice.vertex) := by
      change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
          (Sum.inl x) =
        (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
          (Sum.inl choice.vertex)
      exact
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (by simp [TwoColorIncidenceGraph, hxf, hfd])).trans hfComponent
    have hxEq := (hComponentSecond x hx).mp hxComponent
    subst x
    by_contra hne
    exact secondStableProper hne
      ⟨choice.vertex, hxf, choice.edgeIncident⟩ hfd hChoiceSecond

private theorem helper_hDeltaCurrentMissing_531.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G
        secondStable →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree previous.succ.castSucc)
        (TashkinovStoredColors ett.series.data previous.castSucc) (ett.series.data.coloring
        previous.castSucc)), ett.series.data.coloring previous.succ = TwoColorComponentSwap G
        secondStable gamma choice.color (Sum.inl choice.vertex) → terminal = previous.succ → gamma
        ∈ MissingColors G secondStable choice.vertex → secondStable choice.edge = some
        choice.color → gamma ≠ choice.color → Sum.inr choice.edge ∈ TwoColorComponent G
        secondStable gamma choice.color (Sum.inl choice.vertex) → choice.color ∈ MissingColors G
        (ett.series.data.coloring terminal) choice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive terminal previous gamma secondStable
      secondStableProper choice currentColoring hTerminalEq hGammaSecond hChoiceSecond
      hGammaDelta hChoiceComponent
  rw [MissingColors]
  simp only [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hpresent
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hpresent
  rcases hpresent with ⟨f, hfIncident, hfCurrent⟩
  rw [hTerminalEq, currentColoring] at hfCurrent
  by_cases hfComponent : Sum.inr f ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex)
  · by_cases hfg : secondStable f = some gamma
    · have hp : gamma ∈ PresentColors G secondStable choice.vertex := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨f, hfIncident, hfg⟩
      have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
        simpa [MissingColors] using hGammaSecond
      exact hnot hp
    · by_cases hfd : secondStable f = some choice.color
      · have heq : choice.color = gamma := by
          simpa [TwoColorComponentSwap, hfComponent, hfg, hfd,
            hGammaDelta] using hfCurrent
        exact hGammaDelta heq.symm
      · simp [TwoColorComponentSwap, hfComponent, hfg, hfd] at hfCurrent
  · have hfd : secondStable f = some choice.color := by
      simpa [TwoColorComponentSwap, hfComponent] using hfCurrent
    by_cases hfeq : f = choice.edge
    · subst f
      exact hfComponent hChoiceComponent
    · exact (secondStableProper hfeq
        ⟨choice.vertex, hfIncident, choice.edgeIncident⟩
        hfd hChoiceSecond).elim

private theorem helper_hFixAway_566.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree previous.succ.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc)), ett.series.data.coloring
        previous.succ = TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl
        choice.vertex) → terminal = previous.succ → secondStable choice.edge = some choice.color →
        (
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), Sum.inl x ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) ↔ x =
        choice.vertex) → Sum.inr choice.edge ∈ TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) → (
    ∀ (f : E), TreeIncidentEdge (ett.series.data.tree terminal.castSucc) f → Sum.inr f ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → f =
        choice.edge) →
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), x ≠ choice.vertex →
    ∀ (f : E), Incident G x f → ett.series.data.coloring terminal f = secondStable f := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive terminal previous gamma secondStable choice
      currentColoring hTerminalEq hChoiceSecond hComponentSecond hChoiceComponent
      hOnlyIncidentComponent x hx hxne f hxf
  rw [hTerminalEq, currentColoring]
  by_cases hfComponent : Sum.inr f ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex)
  · have htreeIncident : TreeIncidentEdge
        (ett.series.data.tree terminal.castSucc) f := ⟨x, hx, hxf⟩
    have hfeq := hOnlyIncidentComponent f htreeIncident hfComponent
    subst f
    have hxComponent : Sum.inl x ∈
        TwoColorComponent G secondStable gamma choice.color
          (Sum.inl choice.vertex) := by
      change (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
          (Sum.inl x) =
        (TwoColorIncidenceGraph G secondStable gamma choice.color).connectedComponentMk
          (Sum.inl choice.vertex)
      exact
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (by simp [TwoColorIncidenceGraph, hxf, hChoiceSecond])).trans
          hChoiceComponent
    exact (hxne ((hComponentSecond x hx).mp hxComponent)).elim
  · simp [TwoColorComponentSwap, hfComponent]

private theorem helper_hMissingSupportOfNeDelta_612.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree previous.succ.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc)), ett.series.data.coloring
        previous.succ = TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl
        choice.vertex) → terminal = previous.succ → choice.vertex ∈ TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc) → secondStable choice.edge = some choice.color →
        (
    ∀ (f : E), TreeIncidentEdge (ett.series.data.tree terminal.castSucc) f → Sum.inr f ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → f =
        choice.edge) →
    ∀ c ∈ MissingColors G (ett.series.data.coloring terminal) choice.vertex, c ≠ choice.color → c
        ∈ MissingColors G secondStable choice.vertex := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive terminal previous gamma secondStable choice
      currentColoring hTerminalEq hSupportTree hChoiceSecond hOnlyIncidentComponent c hcCurrent
      hcDelta
  by_contra hcSecond
  have hcPresent : c ∈ PresentColors G secondStable choice.vertex := by
    simpa [MissingColors] using hcSecond
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hcPresent
  rcases hcPresent with ⟨f, hxf, hfc⟩
  by_cases hfComponent : Sum.inr f ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex)
  · have hfeq := hOnlyIncidentComponent f
      ⟨choice.vertex, hSupportTree, hxf⟩ hfComponent
    subst f
    exact hcDelta (Option.some.inj (hfc.symm.trans hChoiceSecond))
  · have hCurrentColor : ett.series.data.coloring terminal f = some c := by
      rw [hTerminalEq, currentColoring]
      simpa [TwoColorComponentSwap, hfComponent] using hfc
    have hcNotPresent : c ∉ PresentColors G
        (ett.series.data.coloring terminal) choice.vertex := by
      simpa [MissingColors] using hcCurrent
    exact hcNotPresent (by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨f, hxf, hCurrentColor⟩)

private theorem helper_hCurrentElementary_640.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree previous.succ.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc)), choice.vertex ∈
        TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc) →
        ColoredVertexSetElementary G secondStable (TreeSequenceVertexSet (ett.series.data.tree
        terminal.castSucc)) → choice.color ∉ TreeMissingColors secondStable (ett.series.data.tree
        terminal.castSucc) → (
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), x ≠ choice.vertex →
        MissingColors G (ett.series.data.coloring terminal) x = MissingColors G secondStable x) →
        (
    ∀ c ∈ MissingColors G (ett.series.data.coloring terminal) choice.vertex, c ≠ choice.color → c
        ∈ MissingColors G secondStable choice.vertex) → ColoredVertexSetElementary G
        (ett.series.data.coloring terminal) (TreeSequenceVertexSet (ett.series.data.tree
        terminal.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive terminal previous secondStable choice
      hSupportTree hSecondElementary hDeltaNotTreeSecond hMissingAway hMissingSupportOfNeDelta u
      hu v hv huv
  apply Finset.disjoint_left.mpr
  intro c hcu hcv
  by_cases huSupport : u = choice.vertex
  · subst u
    have hvSupport : v ≠ choice.vertex := by
      intro heq
      exact huv heq.symm
    have hcvSecond : c ∈ MissingColors G secondStable v := by
      rw [← hMissingAway v hv hvSupport]
      exact hcv
    by_cases hcDelta : c = choice.color
    · subst c
      apply hDeltaNotTreeSecond
      rw [TreeMissingColors]
      exact Finset.mem_biUnion.mpr ⟨v, hv, hcvSecond⟩
    · have hcuSecond := hMissingSupportOfNeDelta c hcu hcDelta
      exact (Finset.disjoint_left.mp
        (hSecondElementary hSupportTree hv huv)) hcuSecond hcvSecond
  · by_cases hvSupport : v = choice.vertex
    · subst v
      have hcuSecond : c ∈ MissingColors G secondStable u := by
        rw [← hMissingAway u hu huSupport]
        exact hcu
      by_cases hcDelta : c = choice.color
      · subst c
        apply hDeltaNotTreeSecond
        rw [TreeMissingColors]
        exact Finset.mem_biUnion.mpr ⟨u, hu, hcuSecond⟩
      · have hcvSecond := hMissingSupportOfNeDelta c hcv hcDelta
        exact (Finset.disjoint_left.mp
          (hSecondElementary hu hSupportTree huv)) hcuSecond hcvSecond
    · have hcuSecond : c ∈ MissingColors G secondStable u := by
        rw [← hMissingAway u hu huSupport]
        exact hcu
      have hcvSecond : c ∈ MissingColors G secondStable v := by
        rw [← hMissingAway v hv hvSupport]
        exact hcv
      exact (Finset.disjoint_left.mp (hSecondElementary hu hv huv))
        hcuSecond hcvSecond

private theorem helper_hCommonPrefix_849.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (base :
        HierarchyBase ett sigma),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree previous.succ.castSucc)
        (TashkinovStoredColors ett.series.data previous.castSucc) (ett.series.data.coloring
        previous.castSucc)) (common : V), TreeVertexOrder (ett.series.data.tree terminal.castSucc)
        common choice.vertex → choice.vertex = (ett.series.data.tree terminal.castSucc).vertex
        base.supportPosition →
    let supportPrefix : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree
        terminal.castSucc) (↑base.supportPosition : ℕ) base.supportPositive (Nat.le_of_lt_succ
        base.supportPosition.isLt); common ∈ TreeSequenceVertexSet supportPrefix := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive sigma base terminal previous choice common
      hCommonOrderTerminal hSupportPosition supportPrefix
  rcases hCommonOrderTerminal with ⟨i, j, hi, hj, hij⟩
  have hjSupport : j = base.supportPosition := by
    apply (ett.series.data.tree terminal.castSucc).vertex_injective
    exact hj.trans hSupportPosition
  rw [hjSupport] at hij
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  let i' : Fin (base.supportPosition.val + 1) := ⟨i.val, by omega⟩
  refine ⟨i', ?_⟩
  change (ett.series.data.tree terminal.castSucc).vertex
      (Fin.castLE
        (Nat.succ_le_succ
          (Nat.le_of_lt_succ base.supportPosition.isLt)) i') = common
  have hiEq : Fin.castLE
      (Nat.succ_le_succ
        (Nat.le_of_lt_succ base.supportPosition.isLt)) i' = i := by
    apply Fin.ext
    rfl
  rw [hiEq]
  exact hi

private theorem helper_hComponentCurrent_860.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi), TechnicalInductionContext G k e0 ett.rounds → MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)), IsProperEdgeColoring G
        (ett.series.data.coloring previous.succ) → IsOneEdgeUncolored (ett.series.data.coloring
        previous.succ) e0 → ett.series.data.kind previous.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex previous.succ = some choice.vertex → ett.series.data.delta
        previous.succ = some choice.color → ett.series.data.gamma previous.succ = some gamma →
        terminal = previous.succ → Fin.last ett.rounds = previous.succ → StableColoring
        (ett.series.data.tree terminal.castSucc) (TashkinovStoredColors ett.series.data terminal)
        (ett.series.data.coloring terminal) (ett.series.data.coloring terminal) →
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), Sum.inl x ∈
        TwoColorComponent G (ett.series.data.coloring terminal) gamma choice.color (Sum.inl
        choice.vertex) ↔ x = choice.vertex := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx hMP hpositive terminal previous gamma choice
      currentProper currentOneUncolored currentKind currentVertex currentDelta currentGamma
      hTerminalEq hTerminalLast hCurrentStable
  have hbase := ExtensionBase G k e0 input T phi ett hMP hpositive
    (fun lower hlowerPositive hlowerRounds hlowerMP =>
      ⟨ctx.lowerOne lower hlowerPositive hlowerRounds hlowerMP,
        ctx.lowerTwo lower hlowerPositive hlowerRounds hlowerMP,
        ctx.lowerThree lower hlowerPositive hlowerRounds hlowerMP,
        ctx.lowerFour lower hlowerPositive hlowerRounds hlowerMP,
        ctx.lowerFive lower hlowerPositive hlowerRounds hlowerMP,
        ctx.lowerSix lower hlowerPositive hlowerRounds hlowerMP⟩)
    choice.vertex gamma choice.color
    (by simpa only [hTerminalLast] using currentKind)
    (by simpa only [hTerminalLast] using currentVertex)
    (by simpa only [hTerminalLast] using currentGamma)
    (by simpa only [hTerminalLast] using currentDelta)
    (ett.series.data.coloring terminal)
    (by simpa only [hTerminalEq] using currentProper)
    (by simpa only [hTerminalEq] using currentOneUncolored)
    hCurrentStable
  simpa only [terminal] using hbase

private theorem helper_hComponentEdgeColor_910.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds),
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree previous.succ.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc)) (f : E), Sum.inr f ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → secondStable
        f = some gamma ∨ secondStable f = some choice.color := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive previous gamma secondStable choice f hf
  have hs : Sum.inr f ∈
      (TwoColorIncidenceGraph G secondStable gamma choice.color).support := by
    apply SimpleGraph.mem_support_of_reachable
      (G := TwoColorIncidenceGraph G secondStable gamma choice.color)
      (u := Sum.inr f) (v := Sum.inl choice.vertex) (by simp)
    exact SimpleGraph.ConnectedComponent.eq.mp hf
  obtain ⟨r, hr⟩ :=
    (TwoColorIncidenceGraph G secondStable gamma choice.color).mem_support.mp hs
  cases r with
  | inl x => exact hr.2
  | inr x => simp [TwoColorIncidenceGraph] at hr

private theorem helper_hMissingAway_947.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree previous.succ.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc)), (
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), x ≠ choice.vertex →
    ∀ (f : E), Incident G x f → ett.series.data.coloring terminal f = secondStable f) →
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), x ≠ choice.vertex →
        MissingColors G (ett.series.data.coloring terminal) x = MissingColors G secondStable x := by
  classical
  intro V E _ _ _ G k e0 input T phi ett hpositive terminal previous secondStable choice hFixAway
      x hx hxne
  have hPresent : PresentColors G
      (ett.series.data.coloring terminal) x =
      PresentColors G secondStable x := by
    ext c
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨f, hxf, hfc⟩
      exact ⟨f, hxf, by rw [← hFixAway x hx hxne f hxf]; exact hfc⟩
    · rintro ⟨f, hxf, hfc⟩
      exact ⟨f, hxf, by rw [hFixAway x hx hxne f hxf]; exact hfc⟩
  simp only [MissingColors, hPresent]

private theorem helper_hSupportPrefix_1126.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E k) (base :
        HierarchyBase ett sigma),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree previous.succ.castSucc)
        (TashkinovStoredColors ett.series.data previous.castSucc) (ett.series.data.coloring
        previous.castSucc)), choice.vertex = (ett.series.data.tree terminal.castSucc).vertex
        base.supportPosition →
    let supportPrefix : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree
        terminal.castSucc) (↑base.supportPosition : ℕ) base.supportPositive (Nat.le_of_lt_succ
        base.supportPosition.isLt); choice.vertex ∈ TreeSequenceVertexSet supportPrefix := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive sigma base terminal previous choice
      hSupportPosition supportPrefix
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  let i : Fin (base.supportPosition.val + 1) :=
    ⟨base.supportPosition.val, Nat.lt_succ_self _⟩
  refine ⟨i, ?_⟩
  change (ett.series.data.tree terminal.castSucc).vertex
      (Fin.castLE
        (Nat.succ_le_succ
          (Nat.le_of_lt_succ base.supportPosition.isLt)) i) =
    choice.vertex
  rw [hSupportPosition]
  apply congrArg (ett.series.data.tree terminal.castSucc).vertex
  apply Fin.ext
  rfl

private theorem helper_continuation_963.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds), ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.PE →
    ∀ (sigma : PartialEdgeColoring E k) (base : HierarchyBase ett sigma),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (gamma : Fin k) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        previous.succ.castSucc) (TashkinovStoredColors ett.series.data previous.castSucc)
        (ett.series.data.coloring previous.castSucc)), ett.series.data.chosenVertex previous.succ
        = some choice.vertex → ett.series.data.delta previous.succ = some choice.color →
        ett.series.data.gamma previous.succ = some gamma → terminal = previous.succ → Fin.last
        ett.rounds = previous.succ → ett.series.data.tree terminal.castSucc = ett.series.data.tree
        previous.succ.castSucc → choice.vertex ∈ TreeSequenceVertexSet (ett.series.data.tree
        terminal.castSucc) → ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc)) → choice.color ∈ MissingColors G sigma
        choice.vertex → BoundaryColorEdges G (ett.series.data.coloring previous.succ)
        (TreeSequenceVertexSet (ett.series.data.tree previous.succ.castSucc)) gamma =
        { choice.edge } ∧ (
    ∀ g ∈ BoundaryColorEdges G (ett.series.data.coloring previous.succ) (TreeSequenceVertexSet
        (ett.series.data.tree previous.succ.castSucc)) choice.color,
    ∃ (w : V), TreeVertexOrder (ett.series.data.tree previous.succ.castSucc) w choice.vertex ∧
        Incident G w g) ∧ (ColoredVertexSetElementary G (ett.series.data.coloring
        previous.castSucc) (TreeSequenceVertexSet (ett.series.data.tree previous.succ.castSucc)) →
    ∀ alpha ∈ TreeMissingColors (ett.series.data.coloring previous.succ) (ett.series.data.tree
        previous.succ.castSucc), alpha ≠ choice.color → BoundaryColorEdges G
        (ett.series.data.coloring previous.succ) (TreeSequenceVertexSet (ett.series.data.tree
        previous.succ.castSucc)) alpha = ∅) → gamma ∉ TreeMissingColors sigma
        (ett.series.data.tree terminal.castSucc) →
    ∀ g ∈ BoundaryColorEdges G (ett.series.data.coloring terminal) (TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc)) choice.color,
    ∃ (support : V) (common : V) (gamma : Fin k) (delta : Fin k), ett.series.data.chosenVertex
        (Fin.last ett.rounds) = some support ∧ ett.series.data.gamma (Fin.last ett.rounds) = some
        gamma ∧ ett.series.data.delta (Fin.last ett.rounds) = some delta ∧ support ∈
        TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∧ support ∈
        TreeSequenceVertexSet base.closure ∧ common ∈ TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) ∧ common ∈ TreeSequenceVertexSet base.closure ∧ common ≠
        support ∧ delta ∈ MissingColors G sigma support ∧ gamma ∉ TreeMissingColors sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∧ (MissingColors G sigma
        common).Nonempty ∧ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive hPE sigma base terminal previous gamma
      choice currentVertex currentDelta currentGamma hTerminalEq hTerminalLast hTreeEq
      hSupportTree hSigmaElementary hDeltaSigma hBoundaryFacts hGammaNotSigma g hgBoundaryCurrent
  obtain ⟨common, hCommonOrder, hCommonIncident⟩ :=
    hBoundaryFacts.2.1 g (by
      simpa only [hTerminalEq] using hgBoundaryCurrent)
  have hCommonOrderTerminal : TreeVertexOrder
      (ett.series.data.tree terminal.castSucc) common choice.vertex := by
    simpa only [hTreeEq] using hCommonOrder
  have hCommonTree : common ∈ TreeSequenceVertexSet
      (ett.series.data.tree terminal.castSucc) := by
    rcases hCommonOrderTerminal with ⟨i, j, hi, hj, hij⟩
    rw [← hi]
    simp [TreeSequenceVertexSet]
  have hCommonNe : common ≠ choice.vertex := by
    intro heq
    rcases hCommonOrderTerminal with ⟨i, j, hi, hj, hij⟩
    have hijEq : i = j := by
      apply (ett.series.data.tree terminal.castSucc).vertex_injective
      exact hi.trans (hj.trans heq.symm).symm
    omega
  have hBaseParallel := base.parallel hPE
  have hSupportPosition : choice.vertex =
      (ett.series.data.tree terminal.castSucc).vertex
        base.supportPosition := by
    apply Option.some.inj
    exact currentVertex.symm.trans (by
      simpa only [hTerminalLast, terminal] using hBaseParallel.1)
  let supportPrefix := TreeSequencePrefix
    (ett.series.data.tree terminal.castSucc)
    base.supportPosition.val base.supportPositive
    (Nat.le_of_lt_succ base.supportPosition.isLt)
  have hPrefixClosure : TashkinovClosure sigma supportPrefix base.closure := by
    simpa only [supportPrefix, terminal] using hBaseParallel.2.1
  have initialVertices : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hAB x hx
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and] at hx ⊢
    rcases hx with ⟨i, hi⟩
    rcases hAB with ⟨hlen, hvertices, hedges⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i,
      (hvertices i).trans hi⟩
  have vertexReach : ∀ {A B : TreeSequence G e0},
      TashkinovAugmentationSequence sigma A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hAB
    unfold TashkinovAugmentationSequence at hAB
    induction hAB using Relation.ReflTransGen.head_induction_on with
    | refl => exact Finset.Subset.rfl
    | @head A B hstep htail ih =>
      exact fun x hx => ih (initialVertices hstep.2.1 hx)
  have hPrefixSubset : TreeSequenceVertexSet supportPrefix ⊆
      TreeSequenceVertexSet base.closure := vertexReach hPrefixClosure.1
  have hSupportPrefix : choice.vertex ∈ TreeSequenceVertexSet supportPrefix := by
    exact @helper_hSupportPrefix_1126 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 input T phi ett hpositive sigma base choice hSupportPosition
  have hCommonPrefix : common ∈ TreeSequenceVertexSet supportPrefix := by
    exact @helper_hCommonPrefix_849 V E inferInstance inferInstance inferInstance inferInstance G
        k e0 input T phi ett hpositive sigma base choice common hCommonOrderTerminal
        hSupportPosition
  have hSupportClosure : choice.vertex ∈
      TreeSequenceVertexSet base.closure := hPrefixSubset hSupportPrefix
  have hCommonClosure : common ∈
      TreeSequenceVertexSet base.closure := hPrefixSubset hCommonPrefix
  have hDegree : MaximumDegree G + 1 ≤ k := by
    have hinitial := ett.series.certified (0 : Fin (ett.rounds + 1))
    cases hinitial with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure => exact triple.2.2.1
  have hCommonMissing : (MissingColors G sigma common).Nonempty :=
    MissingColorsNonemptyOfMaximumDegree G sigma hDegree common
  refine ⟨choice.vertex, common, gamma, choice.color, ?_, ?_, ?_,
    hSupportTree, hSupportClosure, hCommonTree, hCommonClosure, hCommonNe,
    hDeltaSigma, hGammaNotSigma, hCommonMissing, hSigmaElementary⟩
  · simpa only [hTerminalLast] using currentVertex
  · simpa only [hTerminalLast] using currentGamma
  · simpa only [hTerminalLast] using currentDelta

private theorem helper_continuation_1031.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds), ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.PE →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 →
    ∀ (base : HierarchyBase ett sigma), StableColoring (ett.series.data.tree (Fin.last ett.rounds
        : Fin (ett.rounds + (1 : ℕ))).castSucc) (TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds : Fin (ett.rounds + (1 : ℕ)))) (ett.series.data.coloring (Fin.last ett.rounds :
        Fin (ett.rounds + (1 : ℕ)))) sigma →
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ.castSucc) (TashkinovStoredColors ett.series.data
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) (ett.series.data.coloring ((⟨ett.rounds - (1 :
        ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc)), ett.series.data.coloring ((⟨ett.rounds - (1
        : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = TwoColorComponentSwap G secondStable gamma
        choice.color (Sum.inl choice.vertex) → ett.series.data.connectingEdges ((⟨ett.rounds - (1
        : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = { choice.edge } → ett.series.data.kind
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = some choice.vertex → ett.series.data.delta
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = some choice.color → ett.series.data.gamma
        ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ = some gamma → (Fin.last ett.rounds : Fin
        (ett.rounds + (1 : ℕ))) = ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ → Fin.last ett.rounds = ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ → ett.series.data.tree (Fin.last ett.rounds : Fin
        (ett.rounds + (1 : ℕ))).castSucc = ett.series.data.tree ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).succ.castSucc → choice.vertex ∈ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc) → gamma
        ≠ choice.color → (
    ∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet (ett.series.data.tree (Fin.last
        ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc)) → TreeIncidentEdge
        (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc) f) →
        ColoredVertexSetElementary G (ett.series.data.coloring ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc)) → StableColoring
        (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc) (insert
        choice.color (TashkinovStoredColors ett.series.data ((⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) : Fin ett.rounds).castSucc)) choice.selected secondStable →
        ColoredVertexSetElementary G secondStable (TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))).castSucc)) → choice.color ∉
        TreeMissingColors secondStable (ett.series.data.tree (Fin.last ett.rounds : Fin
        (ett.rounds + (1 : ℕ))).castSucc) → (
    ∀ (f : E), TreeIncidentEdge (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1
        : ℕ))).castSucc) f → Sum.inr f ∈ TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) → f = choice.edge) → choice.color ∈ MissingColors G
        (ett.series.data.coloring (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))))
        choice.vertex → (
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds : Fin (ett.rounds + (1
        : ℕ))).castSucc), x ≠ choice.vertex → MissingColors G (ett.series.data.coloring (Fin.last
        ett.rounds : Fin (ett.rounds + (1 : ℕ)))) x = MissingColors G secondStable x) → (
    ∀ c ∈ MissingColors G (ett.series.data.coloring (Fin.last ett.rounds : Fin (ett.rounds + (1 :
        ℕ)))) choice.vertex, c ≠ choice.color → c ∈ MissingColors G secondStable choice.vertex) →
    ∃ (support : V) (common : V) (gamma : Fin k) (delta : Fin k), ett.series.data.chosenVertex
        (Fin.last ett.rounds) = some support ∧ ett.series.data.gamma (Fin.last ett.rounds) = some
        gamma ∧ ett.series.data.delta (Fin.last ett.rounds) = some delta ∧ support ∈
        TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∧ support ∈
        TreeSequenceVertexSet base.closure ∧ common ∈ TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) ∧ common ∈ TreeSequenceVertexSet base.closure ∧ common ≠
        support ∧ delta ∈ MissingColors G sigma support ∧ gamma ∉ TreeMissingColors sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∧ (MissingColors G sigma
        common).Nonempty ∧ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive hPE sigma _ _ base
  set terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds
  set previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ :
                    Fin ett.rounds)
  intro hStableTerminal gamma secondStable choice currentColoring currentEdges currentKind
      currentVertex currentDelta currentGamma hTerminalEq hTerminalLast hTreeEq hSupportTree
      hGammaDelta boundaryIncident hPreviousElementary hSecondStable hSecondElementary
      hDeltaNotTreeSecond hOnlyIncidentComponent hDeltaCurrentMissing hMissingAway
      hMissingSupportOfNeDelta
  have hCurrentElementary : ColoredVertexSetElementary G
      (ett.series.data.coloring terminal)
      (TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc)) := by
    exact @helper_hCurrentElementary_640 V E inferInstance inferInstance
        inferInstance G k e0 input T phi ett hpositive secondStable choice hSupportTree
        hSecondElementary hDeltaNotTreeSecond hMissingAway hMissingSupportOfNeDelta
  have hSigmaElementary : ColoredVertexSetElementary G sigma
      (TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc)) := by
    intro u hu v hv huv
    rw [hStableTerminal.2 u hu, hStableTerminal.2 v hv]
    exact hCurrentElementary hu hv huv
  have hDeltaSigma : choice.color ∈ MissingColors G sigma
      choice.vertex := by
    rw [hStableTerminal.2 choice.vertex hSupportTree]
    exact hDeltaCurrentMissing
  have hBoundaryFacts := HkuParallelBoundaryStructure G k ett.rounds e0
    input ett.series previous choice.edge choice.color gamma choice.vertex
    currentKind currentEdges currentDelta currentGamma currentVertex
  have hPreviousElementaryBoundary : ColoredVertexSetElementary G
      (ett.series.data.coloring previous.castSucc)
      (TreeSequenceVertexSet
        (ett.series.data.tree previous.succ.castSucc)) := by
    intro u hu v hv huv
    apply hPreviousElementary
    · simpa only [hTreeEq] using hu
    · simpa only [hTreeEq] using hv
    · exact huv
  have hGammaNotCurrent : gamma ∉ TreeMissingColors
      (ett.series.data.coloring terminal)
        (ett.series.data.tree terminal.castSucc) := by
    intro hmissing
    have hempty := hBoundaryFacts.2.2 hPreviousElementaryBoundary gamma
      (by simpa only [hTerminalEq] using hmissing) hGammaDelta
    have hsingleton := hBoundaryFacts.1
    rw [hempty] at hsingleton
    simp at hsingleton
  have hGammaNotSigma : gamma ∉ TreeMissingColors sigma
      (ett.series.data.tree terminal.castSucc) := by
    intro hmissing
    rw [TreeMissingColors] at hmissing
    rcases Finset.mem_biUnion.mp hmissing with ⟨v, hv, hvmissing⟩
    apply hGammaNotCurrent
    rw [TreeMissingColors]
    refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
    rw [← hStableTerminal.2 v hv]
    exact hvmissing
  rcases choice.edgeDefective with
    ⟨edgeColor, hDefectiveColor, hChoiceBoundaryColor⟩
  have hEdgeColorEq : edgeColor = choice.color := by
    apply Option.some.inj
    exact (Finset.mem_filter.mp hChoiceBoundaryColor).2.symm.trans
      choice.edgeColor
  subst edgeColor
  have hBoundaryCard : 1 <
      (BoundaryColorEdges G choice.selected
        (TreeSequenceVertexSet
          (ett.series.data.tree terminal.castSucc)) choice.color).card := by
    have hcard : 2 ≤
        (BoundaryColorEdges G choice.selected
          (TreeSequenceVertexSet
            (ett.series.data.tree terminal.castSucc)) choice.color).card := by
      unfold DefectiveColor at hDefectiveColor
      simpa only [hTreeEq] using hDefectiveColor
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hBoundaryCard
  obtain ⟨g, hgBoundarySelected, hgNe⟩ :
      ∃ g, g ∈ BoundaryColorEdges G choice.selected
          (TreeSequenceVertexSet
            (ett.series.data.tree terminal.castSucc)) choice.color ∧
        g ≠ choice.edge := by
    by_cases hae : a = choice.edge
    · exact ⟨b, hb, by
        intro hbe
        exact hab (hae.trans hbe.symm)⟩
    · exact ⟨a, ha, hae⟩
  have hgBoundary : g ∈ BoundaryEdges G
      (TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc)) :=
    (Finset.mem_filter.mp hgBoundarySelected).1
  have hgSelected : choice.selected g = some choice.color :=
    (Finset.mem_filter.mp hgBoundarySelected).2
  have hgSecond : secondStable g = some choice.color := by
    have hfix := hSecondStable.1 g (boundaryIncident hgBoundary)
      ⟨choice.color, Finset.mem_union_right _
        (Finset.mem_insert_self _ _), hgSelected⟩
    exact hfix.trans hgSelected
  have hgOutside : Sum.inr g ∉
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) := by
    intro hgComponent
    have htree := boundaryIncident hgBoundary
    have hgeq := hOnlyIncidentComponent g htree hgComponent
    exact hgNe hgeq
  have hgCurrent : ett.series.data.coloring terminal g =
      some choice.color := by
    rw [hTerminalEq, currentColoring]
    simpa [TwoColorComponentSwap, hgOutside] using hgSecond
  have hgBoundaryCurrent : g ∈ BoundaryColorEdges G
      (ett.series.data.coloring terminal)
      (TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc)) choice.color := by
    simp only [BoundaryColorEdges, Finset.mem_filter]
    exact ⟨hgBoundary, hgCurrent⟩
  exact @helper_continuation_963 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett hpositive hPE sigma base gamma choice currentVertex currentDelta
      currentGamma hTerminalEq hTerminalLast hTreeEq hSupportTree hSigmaElementary hDeltaSigma
      hBoundaryFacts hGammaNotSigma g hgBoundaryCurrent
private theorem helper_continuation_1628.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (hpositive : (0 : ℕ) < ett.rounds), ett.series.data.kind (Fin.last
        ett.rounds) = some TashkinovExtensionKind.PE →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 →
    ∀ (base : HierarchyBase ett sigma),
    let terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); StableColoring (ett.series.data.tree terminal.castSucc)
        (TashkinovStoredColors ett.series.data terminal) (ett.series.data.coloring terminal) sigma
        →
    ∀ (gamma : Fin k) (secondStable : PartialEdgeColoring E k) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree previous.succ.castSucc) (TashkinovStoredColors ett.series.data
        previous.castSucc) (ett.series.data.coloring previous.castSucc)), ett.series.data.coloring
        previous.succ = TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl
        choice.vertex) → ett.series.data.connectingEdges previous.succ = ({ choice.edge } : Finset
        E) → ett.series.data.kind previous.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex previous.succ = some choice.vertex → ett.series.data.delta
        previous.succ = some choice.color → ett.series.data.gamma previous.succ = some gamma →
        terminal = previous.succ → Fin.last ett.rounds = previous.succ → ett.series.data.tree
        terminal.castSucc = ett.series.data.tree previous.succ.castSucc → choice.vertex ∈
        TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc) → secondStable choice.edge
        = some choice.color → gamma ≠ choice.color → (
    ∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet (ett.series.data.tree
        terminal.castSucc)) → TreeIncidentEdge (ett.series.data.tree terminal.castSucc) f) →
        ColoredVertexSetElementary G (ett.series.data.coloring previous.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc)) → StableColoring
        (ett.series.data.tree terminal.castSucc) (insert choice.color (TashkinovStoredColors
        ett.series.data previous.castSucc) : Finset (Fin k)) choice.selected secondStable →
        ColoredVertexSetElementary G secondStable (TreeSequenceVertexSet (ett.series.data.tree
        terminal.castSucc)) → choice.color ∉ TreeMissingColors secondStable (ett.series.data.tree
        terminal.castSucc) → (
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc), Sum.inl x ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) ↔ x =
        choice.vertex) → Sum.inr choice.edge ∈ TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) → (
    ∀ (f : E), TreeIncidentEdge (ett.series.data.tree terminal.castSucc) f → Sum.inr f ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → f =
        choice.edge) → choice.color ∈ MissingColors G (ett.series.data.coloring terminal)
        choice.vertex →
    ∃ (support : V) (common : V) (gamma : Fin k) (delta : Fin k), ett.series.data.chosenVertex
        (Fin.last ett.rounds) = some support ∧ ett.series.data.gamma (Fin.last ett.rounds) = some
        gamma ∧ ett.series.data.delta (Fin.last ett.rounds) = some delta ∧ support ∈
        TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∧ support ∈
        TreeSequenceVertexSet base.closure ∧ common ∈ TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) ∧ common ∈ TreeSequenceVertexSet base.closure ∧ common ≠
        support ∧ delta ∈ MissingColors G sigma support ∧ gamma ∉ TreeMissingColors sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∧ (MissingColors G sigma
        common).Nonempty ∧ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hpositive hPE sigma _ _ base terminal previous
      hStableTerminal gamma secondStable choice currentColoring currentEdges currentKind
      currentVertex currentDelta currentGamma hTerminalEq hTerminalLast hTreeEq hSupportTree
      hChoiceSecond hGammaDelta boundaryIncident hPreviousElementary hSecondStable
      hSecondElementary hDeltaNotTreeSecond hComponentSecond hChoiceComponent
      hOnlyIncidentComponent hDeltaCurrentMissing
  have hFixAway :
    ∀ (x : V), x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc) → x ≠
        choice.vertex →
    ∀ (f : E), Incident G x f → ett.series.data.coloring terminal f = secondStable f := by
    exact @helper_hFixAway_566 V E inferInstance inferInstance inferInstance G k e0 input T phi
        ett hpositive gamma secondStable choice currentColoring hTerminalEq hChoiceSecond
        hComponentSecond hChoiceComponent hOnlyIncidentComponent
  have hMissingAway :
    ∀ (x : V), x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc) → x ≠
        choice.vertex → MissingColors G (ett.series.data.coloring terminal) x = MissingColors G
        secondStable x := by
    exact @helper_hMissingAway_947 V E inferInstance inferInstance inferInstance G k e0 input T
        phi ett hpositive secondStable choice hFixAway
  have hMissingSupportOfNeDelta :
    ∀ (c : Fin k), c ∈ MissingColors G (ett.series.data.coloring terminal) choice.vertex → c ≠
        choice.color → c ∈ MissingColors G secondStable choice.vertex := by
    exact @helper_hMissingSupportOfNeDelta_612 V E inferInstance inferInstance inferInstance G k
        e0 input T phi ett hpositive gamma secondStable choice currentColoring hTerminalEq
        hSupportTree hChoiceSecond hOnlyIncidentComponent
  exact @helper_continuation_1031 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett hpositive hPE sigma (by assumption) (by assumption) base hStableTerminal
      gamma secondStable choice currentColoring currentEdges currentKind currentVertex
      currentDelta currentGamma hTerminalEq hTerminalLast hTreeEq hSupportTree hGammaDelta
      boundaryIncident hPreviousElementary hSecondStable hSecondElementary hDeltaNotTreeSecond
      hOnlyIncidentComponent hDeltaCurrentMissing hMissingAway hMissingSupportOfNeDelta

private theorem helper_continuation_991.{u_1, u_2} :
    helperContinuation991Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx hMP hpositive hPE sigma _ _ base
  set terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds
  set previous : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ :
                          Fin ett.rounds)
  intro hStableTerminal gamma secondStable secondStableProper secondStableOneUncolored
      previousProper previousOneUncolored previousClosed choice currentColoring currentProper
      currentOneUncolored currentEdges currentKind currentVertex currentDelta currentGamma
      hTerminalEq hTerminalLast hTreeEq hSupportTree hGammaSecond hChoiceSecond hGammaDelta
      hChoiceBoundary boundaryIncident hPreviousElementary hSelectedStable hSecondStable
      previousSubtype selectedSubtype secondSubtype hSelectedReverseSubtype hSecondReverseSubtype
  have hSecondElementary : ColoredVertexSetElementary G secondStable
      (TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc)) := by
    intro u hu v hv huv
    rw [hSecondStable.2 u hu, hSecondStable.2 v hv,
      hSelectedStable.2 u hu, hSelectedStable.2 v hv]
    exact hPreviousElementary hu hv huv
  have hSecondClosed : ColoredVertexSetClosed G secondStable
      (TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc)) := by
    exact @helper_hSecondClosed_343 V E inferInstance inferInstance inferInstance G k e0 input T
        phi ett hpositive secondStable secondStableProper secondStableOneUncolored previousProper
        previousOneUncolored previousClosed choice hTreeEq boundaryIncident hSelectedStable
        hSecondStable hSelectedReverseSubtype hSecondReverseSubtype
  have hDeltaNotTreeSecond : choice.color ∉
      TreeMissingColors secondStable
        (ett.series.data.tree terminal.castSucc) := by
    intro hmissing
    rw [TreeMissingColors] at hmissing
    rcases Finset.mem_biUnion.mp hmissing with ⟨v, hv, hvmissing⟩
    exact (hSecondClosed hChoiceBoundary hv hChoiceSecond) hvmissing
  have hCurrentStable : StableColoring
      (ett.series.data.tree terminal.castSucc)
      (TashkinovStoredColors ett.series.data terminal)
      (ett.series.data.coloring terminal)
      (ett.series.data.coloring terminal) := by
    let currentSubtype : {psi : PartialEdgeColoring E k //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨ett.series.data.coloring terminal,
        by simpa only [hTerminalEq] using currentProper,
        by simpa only [hTerminalEq] using currentOneUncolored⟩
    exact (sc2 G e0 (ett.series.data.tree terminal.castSucc)
      (TashkinovStoredColors ett.series.data terminal)).refl currentSubtype
  have hComponentCurrent :
    ∀ x, x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc) → (Sum.inl x ∈
        TwoColorComponent G (ett.series.data.coloring terminal) gamma choice.color (Sum.inl
        choice.vertex) ↔ x = choice.vertex) := by
    exact @helper_hComponentCurrent_860 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 input T phi ett ctx hMP hpositive gamma choice currentProper
        currentOneUncolored currentKind currentVertex currentDelta currentGamma hTerminalEq
        hTerminalLast hCurrentStable
  have hPairColors :
    ∀ f : E, (ett.series.data.coloring terminal f = some gamma ∨ ett.series.data.coloring terminal
        f = some choice.color) ↔ (secondStable f = some gamma ∨ secondStable f = some
        choice.color) := by
    exact @helper_hPairColors_420 V E inferInstance inferInstance inferInstance G k e0 input T
        phi ett hpositive gamma secondStable choice currentColoring hTerminalEq hGammaDelta
  have hGraph : TwoColorIncidenceGraph G
      (ett.series.data.coloring terminal) gamma choice.color =
      TwoColorIncidenceGraph G secondStable gamma choice.color := by
    ext x y
    cases x <;> cases y <;>
      simp [TwoColorIncidenceGraph, hPairColors]
  have hComponents (z : Sum V E) :
      TwoColorComponent G (ett.series.data.coloring terminal)
          gamma choice.color z =
        TwoColorComponent G secondStable gamma choice.color z := by
    unfold TwoColorComponent
    rw [hGraph]
  have hComponentSecond :
    ∀ x, x ∈ TreeSequenceVertexSet (ett.series.data.tree terminal.castSucc) → (Sum.inl x ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) ↔ x =
        choice.vertex) := by
    intro x hx
    rw [← hComponents]
    exact hComponentCurrent x hx
  have hComponentEdgeColor :
    ∀ f, Sum.inr f ∈ TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) →
        secondStable f = some gamma ∨ secondStable f = some choice.color := by
    exact @helper_hComponentEdgeColor_910 V E inferInstance inferInstance inferInstance G k e0
        input T phi ett hpositive gamma secondStable choice
  have hChoiceComponent : Sum.inr choice.edge ∈
      TwoColorComponent G secondStable gamma choice.color
        (Sum.inl choice.vertex) := by
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, choice.edgeIncident, hChoiceSecond]
  have hOnlyIncidentComponent :
    ∀ (f : E), TreeIncidentEdge (ett.series.data.tree terminal.castSucc) f → Sum.inr f ∈
        TwoColorComponent G secondStable gamma choice.color (Sum.inl choice.vertex) → f =
        choice.edge := by
    exact @helper_hOnlyIncidentComponent_489 V E inferInstance inferInstance inferInstance G k e0
        input T phi ett hpositive gamma secondStable secondStableProper choice hGammaSecond
        hChoiceSecond hComponentSecond hComponentEdgeColor
  have hDeltaCurrentMissing : choice.color ∈ MissingColors G
      (ett.series.data.coloring terminal) choice.vertex := by
    exact @helper_hDeltaCurrentMissing_531 V E inferInstance inferInstance inferInstance G k e0
        input T phi ett hpositive gamma secondStable secondStableProper choice currentColoring
        hTerminalEq hGammaSecond hChoiceSecond hGammaDelta hChoiceComponent
  exact @helper_continuation_1628 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hpositive) (@hPE) (@sigma) (by
      assumption) (by assumption) (@base) (@hStableTerminal) (@gamma) (@secondStable) (@choice)
      (@currentColoring) (@currentEdges) (@currentKind) (@currentVertex) (@currentDelta)
      (@currentGamma) (@hTerminalEq) (@hTerminalLast) (@hTreeEq) (@hSupportTree) (@hChoiceSecond)
      (@hGammaDelta) (@boundaryIncident) (@hPreviousElementary) (@hSecondStable)
      (@hSecondElementary) (@hDeltaNotTreeSecond) (@hComponentSecond) (@hChoiceComponent)
      (@hOnlyIncidentComponent) (@hDeltaCurrentMissing)
private theorem helper_branch_133.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi), TechnicalInductionContext G k e0 ett.rounds → MaximumProperty ett →
    ∀ (_ : (0 : ℕ) < ett.rounds), ett.series.data.kind (Fin.last ett.rounds) = some
        TashkinovExtensionKind.PE →
    ∀ (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G sigma → IsOneEdgeUncolored sigma
        e0 →
    ∀ (base : HierarchyBase ett sigma), StableColoring (ett.series.data.tree (Fin.last ett.rounds
        : Fin (ett.rounds + (1 : ℕ))).castSucc) (TashkinovStoredColors ett.series.data (Fin.last
        ett.rounds : Fin (ett.rounds + (1 : ℕ)))) (ett.series.data.coloring (Fin.last ett.rounds :
        Fin (ett.rounds + (1 : ℕ)))) sigma →
    ∀ (ci : Fin ett.rounds), IsProperEdgeColoring G (ett.series.data.coloring ci.castSucc) →
        IsOneEdgeUncolored (ett.series.data.coloring ci.castSucc) e0 → ColoredVertexSetClosed G
        (ett.series.data.coloring ci.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        ci.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G (ett.series.data.coloring
        ci.castSucc) (TreeSequenceVertexSet (ett.series.data.tree ci.succ.castSucc)) → ¬Nonempty
        (RevisitingExtensionCertificate ett.series.data ci.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree ci.succ.castSucc)
        (TashkinovStoredColors ett.series.data ci.castSucc) (ett.series.data.coloring
        ci.castSucc)), (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree ci.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data ci.castSucc)) choice.selected rho ∧ ¬Disjoint
        (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho (ett.series.data.tree
        ci.succ.castSucc))) →
    ∀ (gamma : Fin k), ParallelExtensionColor ett.series.data ci.castSucc choice.selected
        choice.vertex gamma →
    ∀ (secondStable : PartialEdgeColoring E k), IsProperEdgeColoring G secondStable →
        IsOneEdgeUncolored secondStable e0 → StableColoring (ett.series.data.tree
        ci.succ.castSucc) (insert choice.color (TashkinovStoredColors ett.series.data
        ci.castSucc)) choice.selected secondStable → TreeExit (ett.series.data.tree
        ci.succ.castSucc) secondStable gamma choice.color choice.vertex → ett.series.data.coloring
        ci.succ = TwoColorComponentSwap G secondStable gamma choice.color (Sum.inl choice.vertex)
        → IsProperEdgeColoring G (ett.series.data.coloring ci.succ) → IsOneEdgeUncolored
        (ett.series.data.coloring ci.succ) e0 → ett.series.data.stored ci.succ =
        { choice.color, gamma } → ett.series.data.connectingEdges ci.succ = { choice.edge } →
        ett.series.data.kind ci.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex ci.succ = some choice.vertex → ett.series.data.outsideVertex
        ci.succ = some choice.otherEndpoint → ett.series.data.delta ci.succ = some choice.color →
        ett.series.data.gamma ci.succ = some gamma → TashkinovClosure (ett.series.data.coloring
        ci.succ) (ett.series.data.tree ci.succ.castSucc) (ett.series.data.tree ci.succ.succ) →
        TreeSequenceInitialSegment (ett.series.data.tree ci.succ.castSucc) (ett.series.data.tree
        ci.succ.succ) → (ett.series.data.tree ci.succ.castSucc).length < (ett.series.data.tree
        ci.succ.succ).length → (Fin.last ett.rounds : Fin (ett.rounds + (1 : ℕ))) = ci.succ →
    ∃ (support : V) (common : V) (gamma : Fin k) (delta : Fin k), ett.series.data.chosenVertex
        (Fin.last ett.rounds) = some support ∧ ett.series.data.gamma (Fin.last ett.rounds) = some
        gamma ∧ ett.series.data.delta (Fin.last ett.rounds) = some delta ∧ support ∈
        TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∧ support ∈
        TreeSequenceVertexSet base.closure ∧ common ∈ TreeSequenceVertexSet (ett.series.data.tree
        (Fin.last ett.rounds).castSucc) ∧ common ∈ TreeSequenceVertexSet base.closure ∧ common ≠
        support ∧ delta ∈ MissingColors G sigma support ∧ gamma ∉ TreeMissingColors sigma
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∧ (MissingColors G sigma
        common).Nonempty ∧ ColoredVertexSetElementary G sigma (TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett ctx hMP hpositive hPE sigma _ _ base
  set terminal : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds
  let previous : Fin ett.rounds :=
    (⟨ett.rounds - (1 : ℕ), by omega⟩ :
    Fin ett.rounds)
  intro hStableTerminal ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma gammaRule
      secondStable secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges currentKind
      currentVertex currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension hslot
  have hci : ci = previous := by
    apply Fin.ext
    have hs := congrArg Fin.val hslot
    simp [terminal, previous] at hs ⊢
    omega
  subst ci
  have hTerminalEq : terminal = previous.succ := hslot
  have hTerminalLast : Fin.last ett.rounds = previous.succ := by
    simpa only [terminal] using hTerminalEq
  have hTreeEq : ett.series.data.tree terminal.castSucc =
      ett.series.data.tree previous.succ.castSucc := by
    rw [hTerminalEq]
  have hSupportTree : choice.vertex ∈ TreeSequenceVertexSet
      (ett.series.data.tree terminal.castSucc) := by
    simpa only [hTreeEq] using choice.vertexDefective.1
  have hGammaSecond : gamma ∈ MissingColors G secondStable
      choice.vertex := by
    rw [secondStableRelation.2 choice.vertex choice.vertexDefective.1]
    exact gammaRule.1
  have hChoiceSecond : secondStable choice.edge = some choice.color := by
    have hfix := secondStableRelation.1 choice.edge
      ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
      ⟨choice.color, Finset.mem_union_right _
        (Finset.mem_insert_self _ _), choice.edgeColor⟩
    exact hfix.trans choice.edgeColor
  have hGammaDelta : gamma ≠ choice.color := by
    intro heq
    have hpresent : gamma ∈ PresentColors G secondStable
        choice.vertex := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨choice.edge, choice.edgeIncident, heq ▸ hChoiceSecond⟩
    have hnot : gamma ∉ PresentColors G secondStable choice.vertex := by
      simpa [MissingColors] using hGammaSecond
    exact hnot hpresent
  have hChoiceBoundary : choice.edge ∈ BoundaryEdges G
      (TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc)) := by
    rcases choice.edgeDefective with ⟨c, hcDefective, hcEdge⟩
    have hcValue := (Finset.mem_filter.mp hcEdge).2
    have hcEq : c = choice.color :=
      Option.some.inj (hcValue.symm.trans choice.edgeColor)
    simpa only [hTreeEq] using (Finset.mem_filter.mp hcEdge).1
  have boundaryIncident :
    ∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet (ett.series.data.tree
        terminal.castSucc)) → TreeIncidentEdge (ett.series.data.tree terminal.castSucc) f := by
    intro f hf
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hf
    rcases hf with ⟨x, hx, y, hy, hxy⟩
    exact ⟨x, hx, by simp [Incident, hxy]⟩
  have hPreviousElementary : ColoredVertexSetElementary G
      (ett.series.data.coloring previous.castSucc)
      (TreeSequenceVertexSet
        (ett.series.data.tree terminal.castSucc)) := by
    exact @helper_hPreviousElementary_238 V E inferInstance inferInstance inferInstance
        inferInstance G k e0 input T phi ett ctx hMP hpositive
  have hSelectedStable : StableColoring
      (ett.series.data.tree terminal.castSucc)
      (TashkinovStoredColors ett.series.data previous.castSucc)
      (ett.series.data.coloring previous.castSucc) choice.selected := by
    simpa only [hTreeEq] using choice.selectedStable
  have hSecondStable : StableColoring
      (ett.series.data.tree terminal.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data previous.castSucc))
      choice.selected secondStable := by
    simpa only [hTreeEq] using secondStableRelation
  let previousSubtype : {psi : PartialEdgeColoring E k //
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
    ⟨ett.series.data.coloring previous.castSucc,
      previousProper, previousOneUncolored⟩
  let selectedSubtype : {psi : PartialEdgeColoring E k //
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
    ⟨choice.selected, choice.selectedProper, choice.selectedOneUncolored⟩
  let secondSubtype : {psi : PartialEdgeColoring E k //
      IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
    ⟨secondStable, secondStableProper, secondStableOneUncolored⟩
  have hSelectedForwardSubtype : StableColoring
      (ett.series.data.tree terminal.castSucc)
      (TashkinovStoredColors ett.series.data previous.castSucc)
      previousSubtype.1 selectedSubtype.1 := by
    simpa [previousSubtype, selectedSubtype] using hSelectedStable
  have hSelectedReverseSubtype : StableColoring
      (ett.series.data.tree terminal.castSucc)
      (TashkinovStoredColors ett.series.data previous.castSucc)
      selectedSubtype.1 previousSubtype.1 := by
    exact (sc2 G e0 (ett.series.data.tree terminal.castSucc)
      (TashkinovStoredColors ett.series.data previous.castSucc)).symm
      hSelectedForwardSubtype
  have hSecondForwardSubtype : StableColoring
      (ett.series.data.tree terminal.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data previous.castSucc))
      selectedSubtype.1 secondSubtype.1 := by
    simpa [selectedSubtype, secondSubtype] using hSecondStable
  have hSecondReverseSubtype : StableColoring
      (ett.series.data.tree terminal.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data previous.castSucc))
      secondSubtype.1 selectedSubtype.1 := by
    exact (sc2 G e0 (ett.series.data.tree terminal.castSucc)
      (insert choice.color
        (TashkinovStoredColors ett.series.data previous.castSucc))).symm
      hSecondForwardSubtype
  exact @helper_continuation_991 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T phi ett ctx hMP hpositive hPE sigma (by assumption) (by assumption) base
      hStableTerminal gamma secondStable secondStableProper secondStableOneUncolored
      previousProper previousOneUncolored previousClosed choice currentColoring currentProper
      currentOneUncolored currentEdges currentKind currentVertex currentDelta currentGamma
      hTerminalEq hTerminalLast hTreeEq hSupportTree hGammaSecond hChoiceSecond hGammaDelta
      hChoiceBoundary boundaryIncident hPreviousElementary hSelectedStable hSecondStable
      hSelectedReverseSubtype hSecondReverseSubtype
theorem ParallelTerminalPEPreprocessing {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (ctx : TechnicalInductionContext G k e0 ett.rounds)
    (hMP : MaximumProperty ett) (hpositive : 0 < ett.rounds)
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (sigma : PartialEdgeColoring E k)
    (_ : IsProperEdgeColoring G sigma)
    (_ : IsOneEdgeUncolored sigma e0)
    (hstable : StableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma)
    (base : HierarchyBase ett sigma) :
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc
    ∃ support common : V,
    ∃ gamma delta : Fin k,
    ett.series.data.chosenVertex n = some support ∧
      ett.series.data.gamma n = some gamma ∧
        ett.series.data.delta n = some delta ∧
          support ∈ TreeSequenceVertexSet Tn ∧
            support ∈ TreeSequenceVertexSet base.closure ∧
              common ∈ TreeSequenceVertexSet Tn ∧
                common ∈ TreeSequenceVertexSet base.closure ∧
                  common ≠ support ∧
                    delta ∈ MissingColors G sigma support ∧
                      gamma ∉ TreeMissingColors sigma Tn ∧
                        (MissingColors G sigma common).Nonempty ∧
                          ColoredVertexSetElementary G sigma (TreeSequenceVertexSet Tn) := by
  dsimp only
  let terminal : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let previous : Fin ett.rounds := ⟨ett.rounds - 1, by omega⟩
  have hPreviousSucc : previous.succ = terminal := by
    apply Fin.ext
    simp [previous, terminal]
    omega
  have hStableTerminal : StableColoring
      (ett.series.data.tree terminal.castSucc)
      (TashkinovStoredColors ett.series.data terminal)
      (ett.series.data.coloring terminal) sigma := by
    rw [← ett.generatingColoring]
    exact hstable
  have cert := ett.series.certified terminal
  generalize hslot : terminal = slot at cert
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have hz := congrArg Fin.val hslot
    simp [terminal] at hz
    omega
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hterm := hPE
    change ett.series.data.kind terminal =
      some TashkinovExtensionKind.PE at hterm
    rw [hslot, currentKind] at hterm
    simp at hterm
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hterm := hPE
    change ett.series.data.kind terminal =
      some TashkinovExtensionKind.PE at hterm
    rw [hslot, currentKind] at hterm
    simp at hterm
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_133 V E inferInstance inferInstance inferInstance inferInstance G
              k e0 input T phi ett ctx hMP hpositive hPE sigma (by assumption) (by assumption)
              base hStableTerminal ci previousProper previousOneUncolored previousClosed
              previousNotStronglyClosed noRevisiting choice seriesAlternativeFails gamma
              gammaRule secondStable secondStableProper secondStableOneUncolored
              secondStableRelation exitWitness currentColoring currentProper currentOneUncolored
              currentStored currentEdges currentKind currentVertex currentOutside currentDelta
              currentGamma closedExtension orderedExtension strictExtension hslot
end GoldbergSeymour

end
