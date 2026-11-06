/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceSuffix
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.ExtensionBaseRestorationTrace
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeVerticesBefore

/-!
# Shared facts for ExtensionBaseAuxiliary

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ExtensionBranches

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev branchStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
          e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
      let _ : DecidableEq V := Classical.decEq V;
      let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
      by omega
      ⟩ : Fin ett.rounds);
      ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
          (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
          : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
      let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
      by omega
      ⟩ : Fin ett.rounds);
      ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
          (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
          (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
      let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
          (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
      ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (_ : (
      ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
          TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
          B)) (_ : (ett.series.data.tree (0 : Fin (ett.rounds + (2 : ℕ)))).length = (1 : ℕ)) (_ :
          TashkinovClosure (ett.series.data.coloring (0 : Fin (ett.rounds + (1 : ℕ))))
          (ett.series.data.tree (0 : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (1 : Fin
          (ett.rounds + (2 : ℕ))))) (_ : jSlot.castSucc = (0 : Fin (ett.rounds + (1 : ℕ)))),
          TashkinovAugmentationSequence (ett.series.data.coloring (0 : Fin (ett.rounds + (1 : ℕ))))
          seed (ett.series.data.tree jSlot.succ.castSucc)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev equalPrefixesStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
          {A B D : TreeSequence G e0}, TreeSequenceInitialSegment A D → TreeSequenceInitialSegment B
          D → A.length = B.length → A = B

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev branch3050Statement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
          e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
      let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
      by omega
      ⟩ : Fin ett.rounds);
      ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
          (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
          : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
      let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
      by omega
      ⟩ : Fin ett.rounds);
      ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
          (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
          (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
      let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
          (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
      ∀ (_ : jSlot.castSucc.succ = jSlot.succ.castSucc) (_ : TreeSequenceInitialSegment seed
          (ett.series.data.tree jSlot.succ.castSucc)) (_ : (
      ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
          TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
          B)),
      let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
      ∀ (_ : (
      ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length)) (_ : (0 : ℕ) < (↑jSlot : ℕ))
          (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
          i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
          (ett.series.data.coloring i.castSucc)) (_ : ett.series.data.connectingEdges i.succ =
          { choice.edge }) (_ : ett.series.data.kind i.succ = some TashkinovExtensionKind.SE)
          (adjoined : TreeSequence G e0) (_ : TreeSequenceAdjoinEdge (ett.series.data.tree
          i.succ.castSucc) choice.edge adjoined) (_ : TashkinovClosure (ett.series.data.coloring
          i.succ) adjoined (ett.series.data.tree i.succ.succ)) (_ : jSlot.castSucc = i.succ),
          ett.series.data.kind i.succ = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence (ett.series.data.coloring i.succ) Tprevious seed ∨
          (ett.series.data.kind i.succ = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
          i.succ = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges i.succ = { f } ∧
          TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧ TashkinovAugmentationSequence
          (ett.series.data.coloring i.succ) adjoinSeed seed

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev branch3107Statement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
          e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
      let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
      by omega
      ⟩ : Fin ett.rounds);
      ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
          (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
          : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
      let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
      by omega
      ⟩ : Fin ett.rounds);
      ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
          (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
          (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
      let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
          (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
      ∀ (_ : jSlot.castSucc.succ = jSlot.succ.castSucc) (_ : TreeSequenceInitialSegment seed
          (ett.series.data.tree jSlot.succ.castSucc)),
      let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
      ∀ (_ : (
      ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), TreeSequenceInitialSegment Tprevious seed)) (_ : (0 : ℕ) <
          (↑jSlot : ℕ)) (i : Fin ett.rounds) (_ : ett.series.data.kind i.succ = some
          TashkinovExtensionKind.PE) (_ : TashkinovClosure (ett.series.data.coloring i.succ)
          (ett.series.data.tree i.succ.castSucc) (ett.series.data.tree i.succ.succ)) (_ :
          jSlot.castSucc = i.succ), ett.series.data.kind i.succ = some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence (ett.series.data.coloring i.succ) Tprevious seed ∨
          (ett.series.data.kind i.succ = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
          i.succ = some TashkinovExtensionKind.RE) ∧
      ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges i.succ = { f } ∧
          TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧ TashkinovAugmentationSequence
          (ett.series.data.coloring i.succ) adjoinSeed seed

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev branch3129Statement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
          e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
      let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
      by omega
      ⟩ : Fin ett.rounds);
      ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
          (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
          : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
      let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
      by omega
      ⟩ : Fin ett.rounds);
      ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
          (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
          (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
      let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
          (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
      ∀ (_ : jSlot.castSucc.succ = jSlot.succ.castSucc) (_ : TreeSequenceInitialSegment seed
          (ett.series.data.tree jSlot.succ.castSucc)) (_ : (
      ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
          TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
          B)),
      let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
      ∀ (_ : (
      ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length)) (_ : (0 : ℕ) < (↑jSlot : ℕ))
          (i : Fin ett.rounds) (available : RevisitingExtensionCertificate ett.series.data
          i.castSucc) (_ : ett.series.data.connectingEdges i.succ = { available.edge }) (_ :
          ett.series.data.kind i.succ = some TashkinovExtensionKind.RE) (adjoined : TreeSequence G
          e0) (_ : TreeSequenceAdjoinEdge (ett.series.data.tree i.succ.castSucc) available.edge
          adjoined) (_ : TashkinovClosure (ett.series.data.coloring i.succ) adjoined
          (ett.series.data.tree i.succ.succ)) (_ : jSlot.castSucc = i.succ), ett.series.data.kind
          i.succ = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
          (ett.series.data.coloring i.succ) Tprevious seed ∨ (ett.series.data.kind i.succ = some
          TashkinovExtensionKind.SE ∨ ett.series.data.kind i.succ = some TashkinovExtensionKind.RE)
          ∧
      ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges i.succ = { f } ∧
          TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧ TashkinovAugmentationSequence
          (ett.series.data.coloring i.succ) adjoinSeed seed

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev usegmentVertexBeforeStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
          e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
          (sigma : PartialEdgeColoring E k),
      let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
      by omega
      ⟩ : Fin ett.rounds);
      ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
          (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
          : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
      let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
      by omega
      ⟩ : Fin ett.rounds);
      ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ))
          → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
      let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
      ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
          (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
          (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
      let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
          (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
      ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (TjPrime :
          TreeSequence G e0),
      let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
      ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
          gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin ((ett.series.data.tree
          jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet
          TjPrime) (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
          (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (uPosition : Fin
          (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
          (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
      let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
          huPositionBound;
      ∀ (_ : TreeSequenceInitialSegment U TjPrime) (_ : (
      ∀ (i : Fin (TjPrime.length + (1 : ℕ))) (_ : (↑i : ℕ) < (↑uPosition : ℕ)), TjPrime.vertex i ∈
          TreeVerticesBefore TjPrime u0 huPrime0)) {A : TreeSequence G e0} (_ :
          TreeSequenceInitialSegment A U) (_ : A.length < U.length) {y : V} (_ : y ∈
          TreeSequenceVertexSet A), y ∈ TreeVerticesBefore TjPrime u0 huPrime0

/-- A common proof used by the branches of this transport or construction argument. -/
theorem branch.{u_1, u_2} : branchStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v this q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hseedTj commonPrefix seedLength initialClosure htarget
  have htargetZero : jSlot.val = 0 := by
    have := congrArg Fin.val htarget
    simpa using this
  have htreeOne : ett.series.data.tree 1 =
      ett.series.data.tree jSlot.succ.castSucc := by
    congr 1
    apply Fin.ext
    simp [htargetZero]
  have hinitialTj : TreeSequenceInitialSegment
      (ett.series.data.tree 0)
      (ett.series.data.tree jSlot.succ.castSucc) := by
    have h := TashkinovAugmentationSequenceInitialSegment _ _ _
      initialClosure.1
    rw [htreeOne] at h
    exact h
  have hbaseSeed : TreeSequenceInitialSegment
      (ett.series.data.tree 0) seed := by
    apply commonPrefix hinitialTj hseedTj
    rw [seedLength]
    exact seed.positive
  have hrouteOld : TashkinovAugmentationSequence
      (ett.series.data.coloring 0) (ett.series.data.tree 0)
      (ett.series.data.tree jSlot.succ.castSucc) := by
    rw [← htreeOne]
    exact initialClosure.1
  have hroute := TashkinovAugmentationSequenceSuffix
    (ett.series.data.coloring 0) (ett.series.data.tree 0) seed
    (ett.series.data.tree jSlot.succ.castSucc) hrouteOld hbaseSeed
    hseedTj
  simpa [htargetZero] using hroute

/-- A common proof used by the branches of this transport or construction argument. -/
theorem equalPrefixes.{u_1, u_2} : equalPrefixesStatement.{u_1, u_2} := by
  classical
  intro V E G e0 A B D hAD hBD hlen
  rcases hAD with ⟨hlenAD, hvertexAD, hedgeAD⟩
  rcases hBD with ⟨hlenBD, hvertexBD, hedgeBD⟩
  cases A with
  | mk alen apos avertex aedge avinj aeinf afirst aattach =>
    cases B with
    | mk blen bpos bvertex bedge bvinj beinj bfirst battach =>
      simp only at hlen
      subst blen
      rw [TreeSequence.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · apply heq_of_eq
        funext i
        calc
          avertex i = D.vertex
              (Fin.castLE (Nat.succ_le_succ hlenAD) i) :=
            (hvertexAD i).symm
          _ = D.vertex
              (Fin.castLE (Nat.succ_le_succ hlenBD) i) := by
            congr 1
          _ = bvertex i := hvertexBD i
      · apply heq_of_eq
        funext i
        calc
          aedge i = D.edge (Fin.castLE hlenAD i) :=
            (hedgeAD i).symm
          _ = D.edge (Fin.castLE hlenBD i) := by congr 1
          _ = bedge i := hedgeBD i

/-- A common proof used by the branches of this transport or construction argument. -/
theorem branch3050.{u_1, u_2} : branch3050Statement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hjTreeIndex hseedTj commonPrefix Tprevious hpreviousStrict hjPositive i choice currentEdges
      currentKind adjoined adjoinedExactly closedExtension htarget
  have hi : i.succ = jSlot.castSucc := htarget.symm
  have hroute : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) adjoined
      (ett.series.data.tree jSlot.succ.castSucc) := by
    have h := closedExtension.1
    rw [hi, hjTreeIndex] at h
    exact h
  have hadjoinedTj : TreeSequenceInitialSegment adjoined
      (ett.series.data.tree jSlot.succ.castSucc) :=
    TashkinovAugmentationSequenceInitialSegment _ _ _ hroute
  have hadjoinedLength : adjoined.length ≤ seed.length := by
    rcases adjoinedExactly with ⟨hlen, -, -⟩
    have hiCast : i.succ.castSucc =
        jSlot.castSucc.castSucc := by
      apply Fin.ext
      simpa using congrArg Fin.val hi
    have hprev : ett.series.data.tree i.succ.castSucc =
        Tprevious := by rw [hiCast]
    rw [hprev] at hlen
    rw [hlen]
    exact Nat.succ_le_of_lt (hpreviousStrict hjPositive)
  have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
    commonPrefix hadjoinedTj hseedTj hadjoinedLength
  right
  refine ⟨Or.inl (by simpa [htarget] using currentKind),
    choice.edge, adjoined, ?_, ?_, ?_⟩
  · simpa [htarget] using currentEdges
  · rcases adjoinedExactly with ⟨hlen, hsegment, hedge⟩
    have hiCast : i.castSucc.succ =
        jSlot.castSucc.castSucc := by
      apply Fin.ext
      simpa using congrArg Fin.val hi
    have hlenNew : adjoined.length = Tprevious.length + 1 := by
      simpa [Tprevious, hiCast] using hlen
    have hsegmentNew :
        TreeSequenceInitialSegment Tprevious adjoined := by
      simpa [Tprevious, hiCast] using hsegment
    refine ⟨hlenNew, hsegmentNew, ?_⟩
    have haddedIndex :
        Fin.cast hlenNew.symm (Fin.last Tprevious.length) =
          Fin.cast hlen.symm
            (Fin.last
              (ett.series.data.tree i.succ.castSucc).length) := by
      apply Fin.ext
      simp [Tprevious, hiCast]
    rw [haddedIndex]
    exact hedge
  · simpa [hi] using
      (TashkinovAugmentationSequenceRestrict
        (ett.series.data.coloring jSlot.castSucc) adjoined seed
        (ett.series.data.tree jSlot.succ.castSucc) hroute
        hadjoinedSeed hseedTj)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem branch3107.{u_1, u_2} : branch3107Statement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hjTreeIndex hseedTj Tprevious hpreviousSeed hjPositive i currentKind closedExtension htarget
  have hi : i.succ = jSlot.castSucc := htarget.symm
  have hroute : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) Tprevious
      (ett.series.data.tree jSlot.succ.castSucc) := by
    have h := closedExtension.1
    rw [hi, hjTreeIndex] at h
    simpa [Tprevious, hi] using h
  left
  refine ⟨by simpa [htarget] using currentKind, ?_⟩
  simpa [hi] using
    (TashkinovAugmentationSequenceRestrict
      (ett.series.data.coloring jSlot.castSucc) Tprevious seed
      (ett.series.data.tree jSlot.succ.castSucc) hroute
      (hpreviousSeed hjPositive) hseedTj)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem branch3129.{u_1, u_2} : branch3129Statement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hjTreeIndex hseedTj commonPrefix Tprevious hpreviousStrict hjPositive i available
      currentEdges currentKind adjoined adjoinedExactly closedExtension htarget
  have hi : i.succ = jSlot.castSucc := htarget.symm
  have hroute : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) adjoined
      (ett.series.data.tree jSlot.succ.castSucc) := by
    have h := closedExtension.1
    rw [hi, hjTreeIndex] at h
    exact h
  have hadjoinedTj : TreeSequenceInitialSegment adjoined
      (ett.series.data.tree jSlot.succ.castSucc) :=
    TashkinovAugmentationSequenceInitialSegment _ _ _ hroute
  have hadjoinedLength : adjoined.length ≤ seed.length := by
    rcases adjoinedExactly with ⟨hlen, -, -⟩
    have hiCast : i.succ.castSucc =
        jSlot.castSucc.castSucc := by
      apply Fin.ext
      simpa using congrArg Fin.val hi
    have hprev : ett.series.data.tree i.succ.castSucc =
        Tprevious := by rw [hiCast]
    rw [hprev] at hlen
    rw [hlen]
    exact Nat.succ_le_of_lt (hpreviousStrict hjPositive)
  have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
    commonPrefix hadjoinedTj hseedTj hadjoinedLength
  right
  refine ⟨Or.inr (by simpa [htarget] using currentKind),
    available.edge, adjoined, ?_, ?_, ?_⟩
  · simpa [htarget] using currentEdges
  · rcases adjoinedExactly with ⟨hlen, hsegment, hedge⟩
    have hiCast : i.castSucc.succ =
        jSlot.castSucc.castSucc := by
      apply Fin.ext
      simpa using congrArg Fin.val hi
    have hlenNew : adjoined.length = Tprevious.length + 1 := by
      simpa [Tprevious, hiCast] using hlen
    have hsegmentNew :
        TreeSequenceInitialSegment Tprevious adjoined := by
      simpa [Tprevious, hiCast] using hsegment
    refine ⟨hlenNew, hsegmentNew, ?_⟩
    have haddedIndex :
        Fin.cast hlenNew.symm (Fin.last Tprevious.length) =
          Fin.cast hlen.symm
            (Fin.last
              (ett.series.data.tree i.succ.castSucc).length) := by
      apply Fin.ext
      simp [Tprevious, hiCast]
    rw [haddedIndex]
    exact hedge
  · simpa [hi] using
      (TashkinovAugmentationSequenceRestrict
        (ett.series.data.coloring jSlot.castSucc) adjoined seed
        (ett.series.data.tree jSlot.succ.castSucc) hroute
        hadjoinedSeed hseedTj)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem usegmentVertexBefore.{u_1, u_2} : usegmentVertexBeforeStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H x
      componentPath u exitPath zPosition u0 huPrime0 exitPath0 zPosition0 uPosition
      huPositionPositive huPositionBound U hUPrime hprimeVertexBefore A hAU hAlen y hyA
  obtain ⟨hAULen, hAUVertices, -⟩ := hAU
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hyA
  obtain ⟨i, rfl⟩ := hyA
  let iU : Fin (U.length + 1) :=
    Fin.castLE (Nat.succ_le_succ hAULen) i
  let iPrime : Fin (TjPrime.length + 1) :=
    Fin.castLE (Nat.succ_le_succ hUPrime.1) iU
  have hiPrime : iPrime.val < uPosition.val := by
    change i.val < uPosition.val
    have hUlen : U.length = uPosition.val := by
      simp [U, TreeSequencePrefix]
    omega
  rw [← hAUVertices i, ← hUPrime.2.1 iU]
  exact hprimeVertexBefore iPrime hiPrime

end GoldbergSeymour.SharedFacts.ExtensionBranches

end
