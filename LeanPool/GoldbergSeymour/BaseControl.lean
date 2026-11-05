/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.HierarchyFullTailPrefix
public import LeanPool.GoldbergSeymour.ChangeLemmaBothInside
public import LeanPool.GoldbergSeymour.HierarchyMinimumCounterexampleContext
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloring
public import LeanPool.GoldbergSeymour.HierarchyOrderedExitReduction
public import LeanPool.GoldbergSeymour.HierarchyFullTailLength

/-!
# P2813_T1_Base Control

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperBaseStableProof1297Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (hprefixElementary :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := T.length - A.length;
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
        (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive) (Nat.min_le_right
        (A.length + (ell - (1 : ℕ))) T.length); ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet Ty)) (alpha beta : Fin k) (hne : alpha ≠ beta) (z : V ⊕ E) (sigma :
        PartialEdgeColoring E k) (hcase :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n; (0 : ℕ) < H.dividerCount ∧
        alpha ∈ TreeMissingColors phi Tnq ∨ H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        phi Tn ∨ alpha ∈ TreeMissingColors phi A ∧ alpha ∉ Dn ∧ beta ∉ Dn)) (hproper :
        IsProperEdgeColoring G phi) (hone : IsOneEdgeUncolored phi e0) (hlower :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
        LowerRoundProperties lower),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let a : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    ∀ (trans :
    ∀ {U W Z : TreeSequence G e0} (hUW : TreeSequenceInitialSegment U W) (hWZ :
        TreeSequenceInitialSegment W Z), TreeSequenceInitialSegment U Z) (starChain :
    ∀ (r s : Fin (H.dividerCount + (1 : ℕ))) (hrs : r ≤ s), TreeSequenceInitialSegment
        (HierarchyStarredStage H r) (HierarchyStarredStage H s)) (hAT : TreeSequenceInitialSegment
        A T) (haMissing : alpha ∈ MissingColors G phi a) (pathMissing :
    ∀ (c d : Fin k) (hcd : c ≠ d) (v : V) (hc : c ∈ MissingColors G phi v), TwoColorPathComponent
        G phi c d (Sum.inl v)) (interchangeableSwap :
    ∀ (B : TreeSequence G e0) (c d : Fin k) (hi : TreeInterchangeable G B phi c d),
        TreeInterchangeable G B phi d c) (hcombined : CombinedStableColoring Tn base.closure
        (TashkinovStoredColors ett.series.data n) phi phi) (nonPEMissingClosed :
    ∀ (hnonPE : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE) (c : Fin k) (hc : c ∈
        TreeMissingColors phi Tn), TreeColorSetClosed G phi Tn ({ c } : Finset (Fin k)))
        (coreChain : TreeSequenceInitialSegment Tn base.core) (TnA : TreeSequenceInitialSegment Tn
        A) (closureA :
    ∀ (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE), TreeSequenceVertexSet
        base.closure ⊆ TreeSequenceVertexSet A) (firstIn :
    ∀ (B : TreeSequence G e0) (hBT : TreeSequenceInitialSegment B T) (c : Fin k) (hc : c ∈
        TreeMissingColors phi B), T.vertex (HierarchyFirstMissingPosition phi T c) ∈
        TreeSequenceVertexSet B) (halphaA : alpha ∈ TreeMissingColors phi A) (haA : a ∈
        TreeSequenceVertexSet A) (haOutside : Sum.inl a ∉ TwoColorComponent G phi alpha beta z)
        (missingUnique :
    ∀ (c : Fin k) (hc : c ∈ TreeMissingColors phi A) (v : V) (hv : v ∈ TreeSequenceVertexSet A)
        (hvc : c ∈ MissingColors G phi v) (hcm : c ∈ MissingColors G phi (T.vertex
        (HierarchyFirstMissingPosition phi T c))), v = T.vertex (HierarchyFirstMissingPosition phi
        T c)) (outsideOfInter :
    ∀ (B : TreeSequence G e0) (v : V) (hv : v ∈ TreeSequenceVertexSet B) (hp :
        TwoColorPathComponent G phi alpha beta (Sum.inl v)) (hi : TreeInterchangeable G B phi
        alpha beta) (hout : Sum.inl v ∉ TwoColorComponent G phi alpha beta z),
        OutsideKempeRecoloring B phi sigma alpha beta) (outsideMono :
    ∀ (B S : TreeSequence G e0) (hBS : TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet S) (hout :
        OutsideKempeRecoloring S phi sigma alpha beta), OutsideKempeRecoloring B phi sigma alpha
        beta) (outsideStable :
    ∀ (B : TreeSequence G e0) (D : Finset (Fin k)) (hout : OutsideKempeRecoloring B phi sigma
        alpha beta), StableColoring B D phi sigma ∧
    ∀ (f : E), TreeIncidentEdge B f → sigma f = phi f) (closedOutside :
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))) (c : Fin k) (hc : c = alpha ∨ c = beta) (hm : c ∈
        TreeMissingColors phi (HierarchyStarredStage H r)) (hcl : TreeColorSetClosed G phi
        (HierarchyStarredStage H r) ({ c } : Finset (Fin k))), OutsideKempeRecoloring
        (HierarchyStarredStage H r) phi sigma alpha beta) (maxClosed :
    ∀ (c : Fin k) (hex :
    ∃ (r : Fin (H.dividerCount + (1 : ℕ))), TreeColorSetClosed G phi (HierarchyStarredStage H r)
        ({ c } : Finset (Fin k))),
    ∃ (r : Fin (H.dividerCount + (1 : ℕ))), TreeColorSetClosed G phi (HierarchyStarredStage H r)
        ({ c } : Finset (Fin k)) ∧
    ∀ (s : Fin (H.dividerCount + (1 : ℕ))), (↑r : ℕ) < (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) ({ c } : Finset (Fin k))) (missingAtMax :
    ∀ (c : Fin k) (hcA : c ∈ TreeMissingColors phi A) (r : Fin (H.dividerCount + (1 : ℕ))) (hmax :
    ∀ (s : Fin (H.dividerCount + (1 : ℕ))), (↑r : ℕ) < (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) ({ c } : Finset (Fin k))), c ∈ TreeMissingColors phi
        (HierarchyStarredStage H r)) (preStepElementary :
    let i : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    have this : (0 : ℕ) < ett.rounds := C.positive; Decidable.byContradiction fun (a : ¬ett.rounds
        - (1 : ℕ) < ett.rounds) ↦
    by omega
    ⟩ : Fin ett.rounds); ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet Tn)) (lastZero :
    ∀ (hq : H.dividerCount = (0 : ℕ)), A = base.core),
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let baseStable : Prop := if ett.series.data.kind n = some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn base.closure Dn phi sigma else StableColoring Tn Dn phi sigma;
    ∀ (stableNoAffected :
    ∀ (B : TreeSequence G e0) (D : Finset (Fin k)) (hBA : TreeSequenceVertexSet B ⊆
        TreeSequenceVertexSet A) (hna : alpha ∉ TreeMissingColors phi B ∪ D) (hnb : beta ∉
        TreeMissingColors phi B ∪ D), StableColoring B D phi sigma) (stableFromCore :
    ∀ (hout : OutsideKempeRecoloring base.core phi sigma alpha beta), baseStable), baseStable

private abbrev helperContinuation1245Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base)
        (hprefixElementary :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := T.length - A.length;
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
        (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive) (Nat.min_le_right
        (A.length + (ell - (1 : ℕ))) T.length); ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet Ty)) (alpha beta : Fin k) (hne : alpha ≠ beta) (hmissingPrefix :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := T.length - A.length;
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
        (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive) (Nat.min_le_right
        (A.length + (ell - (1 : ℕ))) T.length); alpha ∈ TreeMissingColors phi Ty ∧ beta ∈
        TreeMissingColors phi Ty) (z : V ⊕ E) (hpath : TwoColorPathComponent G phi alpha beta z)
        (sigma : PartialEdgeColoring E k) (hsigma : sigma = TwoColorComponentSwap G phi alpha beta
        z) (hcase :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n; (0 : ℕ) < H.dividerCount ∧
        alpha ∈ TreeMissingColors phi Tnq ∨ H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        phi Tn ∨ alpha ∈ TreeMissingColors phi A ∧ alpha ∉ Dn ∧ beta ∉ Dn)) (hdisjoint :
    let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha); Disjoint
        (TwoColorComponent G phi alpha beta z) (TwoColorComponent G phi alpha beta (Sum.inl va)))
        (hproper : IsProperEdgeColoring G phi) (hone : IsOneEdgeUncolored phi e0) (hlower :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
        LowerRoundProperties lower) (hfewer :
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (other : ExtendedTashkinovTree G k e0 input' T'
        generating'), other.rounds = ett.rounds → MaximumProperty other →
    ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base') (a :
        GoodHierarchy K), K.dividerCount < C.hierarchy.dividerCount → ColoredVertexSetElementary G
        generating' (TreeSequenceVertexSet T')) (hlarge :
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; (2 : ℕ) * ett.rounds + (11 : ℕ)
        ≤ (TreeMissingColors phi Tn).card),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let a : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    let b : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
    ∀ (trans :
    ∀ {U W Z : TreeSequence G e0} (hUW : TreeSequenceInitialSegment U W) (hWZ :
        TreeSequenceInitialSegment W Z), TreeSequenceInitialSegment U Z) (starChain :
    ∀ (r s : Fin (H.dividerCount + (1 : ℕ))) (hrs : r ≤ s), TreeSequenceInitialSegment
        (HierarchyStarredStage H r) (HierarchyStarredStage H s)) (hAT : TreeSequenceInitialSegment
        A T) (helemStar :
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H r))) (haMissing : alpha ∈ MissingColors G
        phi a) (hbMissing : beta ∈ MissingColors G phi b) (pathMissing :
    ∀ (c d : Fin k) (hcd : c ≠ d) (v : V) (hc : c ∈ MissingColors G phi v), TwoColorPathComponent
        G phi c d (Sum.inl v)) (graphSwap :
    ∀ (c d : Fin k), TwoColorIncidenceGraph G phi c d = TwoColorIncidenceGraph G phi d c)
        (componentSwap :
    ∀ (c d : Fin k) (z : V ⊕ E), TwoColorComponent G phi c d z = TwoColorComponent G phi d c z)
        (interchangeableSwap :
    ∀ (B : TreeSequence G e0) (c d : Fin k) (hi : TreeInterchangeable G B phi c d),
        TreeInterchangeable G B phi d c) (hcombined : CombinedStableColoring Tn base.closure
        (TashkinovStoredColors ett.series.data n) phi phi) (nonPEMissingClosed :
    ∀ (hnonPE : ett.series.data.kind n ≠ some TashkinovExtensionKind.PE) (c : Fin k) (hc : c ∈
        TreeMissingColors phi Tn), TreeColorSetClosed G phi Tn ({ c } : Finset (Fin k)))
        (coreChain : TreeSequenceInitialSegment Tn base.core) (TnA : TreeSequenceInitialSegment Tn
        A) (closureA :
    ∀ (hp : ett.series.data.kind n = some TashkinovExtensionKind.PE), TreeSequenceVertexSet
        base.closure ⊆ TreeSequenceVertexSet A) (firstIn :
    ∀ (B : TreeSequence G e0) (hBT : TreeSequenceInitialSegment B T) (c : Fin k) (hc : c ∈
        TreeMissingColors phi B), T.vertex (HierarchyFirstMissingPosition phi T c) ∈
        TreeSequenceVertexSet B) (halphaA : alpha ∈ TreeMissingColors phi A) (haA : a ∈
        TreeSequenceVertexSet A) (hsame :
    ∀ (hbA : beta ∈ TreeMissingColors phi A), TwoColorComponent G phi alpha beta (Sum.inl a) =
        TwoColorComponent G phi alpha beta (Sum.inl b)) (haOutside : Sum.inl a ∉ TwoColorComponent
        G phi alpha beta z) (hbOutside :
    ∀ (hbA : beta ∈ TreeMissingColors phi A), Sum.inl b ∉ TwoColorComponent G phi alpha beta z)
        (missingUnique :
    ∀ (c : Fin k) (hc : c ∈ TreeMissingColors phi A) (v : V) (hv : v ∈ TreeSequenceVertexSet A)
        (hvc : c ∈ MissingColors G phi v) (hcm : c ∈ MissingColors G phi (T.vertex
        (HierarchyFirstMissingPosition phi T c))), v = T.vertex (HierarchyFirstMissingPosition phi
        T c)) (edgeOfVertex :
    ∀ {v : V} {f : E} (hv : Sum.inl v ∈ TwoColorComponent G phi alpha beta z) (hinc : Incident G v
        f) (hc : phi f = some alpha ∨ phi f = some beta), Sum.inr f ∈ TwoColorComponent G phi
        alpha beta z),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount); (if
        ett.series.data.kind n = some TashkinovExtensionKind.PE then CombinedStableColoring Tn
        base.closure Dn phi sigma else StableColoring Tn Dn phi sigma) ∧ (
    ∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) ∧
        IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))) (c : Fin k), c = alpha ∨ c = beta → c ∈
        TreeMissingColors phi (HierarchyStarredStage H r) → TreeColorSetClosed G phi
        (HierarchyStarredStage H r) ({ c } : Finset (Fin k)) → OutsideKempeRecoloring
        (HierarchyStarredStage H r) phi sigma alpha beta

private theorem helper_trans_125.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W
        Z → TreeSequenceInitialSegment U Z := by
  classical
  intro V E G e0 U W Z hUW hWZ
  refine ⟨hUW.1.trans hWZ.1, ?_, ?_⟩
  · intro j
    exact (hWZ.2.1 (Fin.castLE (Nat.succ_le_succ hUW.1) j)).trans
      (hUW.2.1 j)
  · intro j
    exact (hWZ.2.2 (Fin.castLE hUW.1 j)).trans (hUW.2.2 j)

private theorem helper_stageChain_136.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy; (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W Z
        → TreeSequenceInitialSegment U Z) →
    ∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))), (↑i : ℕ) ≤
        j → TreeSequenceInitialSegment (H.stage i) (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 :
        ℕ)))) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H trans j
  induction j with
  | zero =>
      intro hj i hi
      have hi0 : i = 0 := Fin.ext (Nat.eq_zero_of_le_zero hi)
      subst i
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  | succ j ih =>
      intro hj i hi
      by_cases heq : i.val = j + 1
      · have heq' : i = ⟨j + 1, hj⟩ := Fin.ext heq
        subst i
        exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      · exact trans (ih (by omega) i (by omega))
          (H.nested ⟨j, by omega⟩)

private theorem helper_starChain_162.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy; (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W Z
        → TreeSequenceInitialSegment U Z) → (
    ∀ (j : ℕ) (hj : j < H.dividerCount + (2 : ℕ)) (i : Fin (H.dividerCount + (2 : ℕ))), (↑i : ℕ) ≤
        j → TreeSequenceInitialSegment (H.stage i) (H.stage (⟨j, hj⟩ : Fin (H.dividerCount + (2 :
        ℕ))))) → (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), TreeSequenceInitialSegment (HierarchyStarredStage H r)
        (H.stage r.succ)) →
    ∀ (r s : Fin (H.dividerCount + (1 : ℕ))), r ≤ s → TreeSequenceInitialSegment
        (HierarchyStarredStage H r) (HierarchyStarredStage H s) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H trans stageChain starStage r s hrs
  by_cases heq : r = s
  · subst s
    exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  · have hrlt : r.val < s.val := by
      have := Fin.le_iff_val_le_val.mp hrs
      have : r.val ≠ s.val := fun h => heq (Fin.ext h)
      omega
    have hs : s ≠ 0 := by intro hs; subst s; simp at hrlt
    have hstar : HierarchyStarredStage H s = H.stage s.castSucc := by
      rw [← Fin.succ_pred s hs]
      rfl
    rw [hstar]
    exact trans (starStage r)
      (stageChain s.val (by omega) r.succ (by simp; omega))

private theorem helper_hATy_184.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (T.length - A.length - (1
        : ℕ))) T.length) (
    have hA : (1 : ℕ) ≤ A.length := A.positive;
    have hT : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ min
        (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
    by omega
    ) (
    by
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive A
          omega
    ); TreeSequenceInitialSegment A T → TreeSequenceInitialSegment A Ty := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A Ty hAT
  have hlen : A.length ≤ Ty.length := by
    change A.length ≤ min (A.length + ((T.length - A.length) - 1)) T.length
    exact Nat.le_min.mpr ⟨Nat.le_add_right _ _, hAT.1⟩
  refine ⟨hlen, ?_, ?_⟩
  · intro j
    change T.vertex _ = A.vertex j
    exact hAT.2.1 j
  · intro j
    change T.edge _ = A.edge j
    exact hAT.2.2 j

private theorem helper_missingFirst_210.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0 input T phi)
      (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Ty : TreeSequence G e0 :=
      TreeSequencePrefix T (min (A.length + (T.length - A.length - (1 : ℕ))) T.length)
        (have hA : (1 : ℕ) ≤ A.length := A.positive;
        have hT : (1 : ℕ) ≤ T.length := T.positive;
        Decidable.byContradiction
          fun (a : ¬(1 : ℕ) ≤ min (A.length + (T.length - A.length - (1 : ℕ))) T.length) ↦
          by omega)
        (by
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive A
          omega);
    TreeSequenceInitialSegment Ty T →
    ∀ c ∈ TreeMissingColors phi Ty,
    c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A Ty hTyT c hc
  obtain ⟨v, hv, hcv⟩ := Finset.mem_biUnion.mp hc
  have hvT := TreeSequenceInitialSegmentVertexSetSubset hTyT hv
  obtain ⟨j, hj⟩ : ∃ j, T.vertex j = v := by
    simpa [TreeSequenceVertexSet] using hvT
  let candidates := Finset.univ.filter fun j : Fin (T.length + 1) =>
    c ∈ MissingColors G phi (T.vertex j)
  have hcandidates : candidates.Nonempty := by
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [hj] using hcv
  unfold HierarchyFirstMissingPosition
  rw [dite_eq_left hcandidates]
  exact (Finset.mem_filter.mp (Finset.min'_mem candidates hcandidates)).2

private theorem helper_pathMissing_230.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (phi : PartialEdgeColoring E k), IsProperEdgeColoring G phi →
    ∀ (c d : Fin k), c ≠ d →
    ∀ (v : V), c ∈ MissingColors G phi v → TwoColorPathComponent G phi c d (Sum.inl v) := by
  classical
  intro V E _ _ G k phi hproper c d hcd v hc
  let _ := Fintype.ofFinite V
  refine ⟨hcd, Sum.inl v, ?_, ?_⟩
  · change (TwoColorIncidenceGraph G phi c d).connectedComponentMk
        (Sum.inl v) =
      (TwoColorIncidenceGraph G phi c d).connectedComponentMk (Sum.inl v)
    rfl
  · let : Fintype
        ((TwoColorIncidenceGraph G phi c d).neighborSet (Sum.inl v)) :=
      Fintype.ofFinite _
    have hcard : Fintype.card
        ((TwoColorIncidenceGraph G phi c d).neighborSet (Sum.inl v)) ≤ 1 := by
      rw [SimpleGraph.card_neighborSet_eq_degree]
      exact MissingColorIncidenceEndpoint G phi c d hcd hproper v hc
    intro x hx y hy
    exact congrArg Subtype.val
      (Fintype.card_le_one_iff.mp hcard ⟨x, hx⟩ ⟨y, hy⟩)

private theorem helper_interchangeableSwap_258.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) (k : ℕ) (e0
        : E) (phi : PartialEdgeColoring E k) (_ : V ⊕ E), (
    ∀ (c d : Fin k), TwoColorIncidenceGraph G phi c d = TwoColorIncidenceGraph G phi d c) → (
    ∀ (c d : Fin k) (z : V ⊕ E), TwoColorComponent G phi c d z = TwoColorComponent G phi d c z) →
    ∀ (B : TreeSequence G e0) (c d : Fin k), TreeInterchangeable G B phi c d → TreeInterchangeable
        G B phi d c := by
  classical
  intro V E _ _ G k e0 phi z graphSwap componentSwap B c d hi
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  clear * - hi componentSwap graphSwap
  intro z w hz hw hzB hwB
  have pathSwap (z : Sum V E)
      (hz : TwoColorPathComponent G phi d c z) :
      TwoColorPathComponent G phi c d z := by
    refine ⟨hz.1.symm, ?_⟩
    simpa only [componentSwap c d, graphSwap c d] using hz.2
  rw [← componentSwap c d z, ← componentSwap c d w]
  apply hi z w (pathSwap z hz) (pathSwap w hw)
  · simpa only [componentSwap c d] using hzB
  · simpa only [componentSwap c d] using hwB

private theorem helper_hnonPEClosed_278.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (_ : HierarchyCounterexample base),
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W Z
        → TreeSequenceInitialSegment U Z) → ett.series.data.kind n ≠ some
        TashkinovExtensionKind.PE → ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone n Tn trans hnonPE
  have hp : 0 < ett.rounds := C.positive
  clear * - ett phi n Tn G hproper hone hnonPE hp
  have stableClosed (B : TreeSequence G e0) (D : Finset (Fin k))
      (psi : PartialEdgeColoring E k)
      (hppsi : IsProperEdgeColoring G psi)
      (hopsi : IsOneEdgeUncolored psi e0)
      (hcpsi : ColoredVertexSetClosed G psi (TreeSequenceVertexSet B))
      (hs : StableColoring B D psi phi) :
      ColoredVertexSetClosed G phi (TreeSequenceVertexSet B) := by
    clear * - G phi e0 hproper hone B D psi hppsi hopsi hcpsi hs
    intro f c x hf hx hfc hcm
    have hincident : TreeIncidentEdge B f := by
      obtain ⟨u, hu, v, hv, huv⟩ := by
        simpa [BoundaryEdges] using hf
      refine ⟨u, hu, ?_⟩
      change u ∈ G.ends f
      rw [huv]
      exact Sym2.mem_mk_left _ _
    have hcmPrev : c ∈ MissingColors G psi x := by
      rw [← hs.2 x hx]
      exact hcm
    have hcTree : c ∈ TreeMissingColors psi B :=
      Finset.mem_biUnion.mpr ⟨x, hx, hcmPrev⟩
    have hfixed : phi f = psi f :=
      (sc1 G e0 B D psi phi hppsi hopsi hproper hone).mp hs
        f hincident (Or.inr ⟨c, Finset.mem_union_left _ hcTree, hfc⟩)
    exact hcpsi hf hx (hfixed.symm.trans hfc) hcmPrev
  have hphi : phi = ett.series.data.coloring n := ett.generatingColoring
  have hstep := ett.series.certified n
  generalize targetEq : n = target at hstep
  cases hstep with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      have hn : n ≠ 0 := by
        intro hh
        have hv := congrArg Fin.val hh
        simp [n] at hv
        omega
      exact (hn targetEq).elim
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper secondStableOneUncolored
      secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
      exact (hnonPE (by rw [targetEq]; exact currentKind)).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
      have hi : i.succ = n := targetEq.symm
      have htree : ett.series.data.tree i.succ.castSucc = Tn := by
        simp [Tn, hi]
      have hselected : choice.selected = phi :=
        currentColoring.symm.trans
          ((congrArg ett.series.data.coloring hi).trans hphi.symm)
      have hs : StableColoring Tn
          (TashkinovStoredColors ett.series.data i.castSucc)
          (ett.series.data.coloring i.castSucc) phi := by
        simpa only [htree, hselected] using choice.selectedStable
      exact @stableClosed Tn _ _ previousProper previousOneUncolored
        (by rw [← htree]; exact previousClosed) hs
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
      have hi : i.succ = n := targetEq.symm
      have htree : ett.series.data.tree i.succ.castSucc = Tn := by
        simp [Tn, hi]
      have hcol : ett.series.data.coloring i.castSucc = phi :=
        currentColoring.symm.trans
          ((congrArg ett.series.data.coloring hi).trans hphi.symm)
      have hc : ColoredVertexSetClosed G (ett.series.data.coloring i.castSucc)
          (TreeSequenceVertexSet Tn) := by
        rw [← htree]
        exact previousClosed
      exact @Eq.mp _ _
        (congrArg (fun psi => ColoredVertexSetClosed G psi
          (TreeSequenceVertexSet Tn)) hcol) hc

private theorem helper_nonPEMissingClosed_364.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; (ett.series.data.kind n ≠ some
        TashkinovExtensionKind.PE → ColoredVertexSetClosed G phi (TreeSequenceVertexSet Tn)) →
        ett.series.data.kind n ≠ some TashkinovExtensionKind.PE →
    ∀ c ∈ TreeMissingColors phi Tn, TreeColorSetClosed G phi Tn ({ c } : Finset (Fin k)) := by
  classical
  intro V E _ _ _ G k e0 input T phi ett n Tn hnonPEClosed hnonPE c hc d hd
  have hdc : d = c := Finset.mem_singleton.mp hd
  subst d
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨x, hx, hcx⟩ := Finset.mem_biUnion.mp hc
  have hfd : f ∈ BoundaryEdges G (TreeSequenceVertexSet Tn) ∧
      phi f = some c := by simpa [BoundaryColorEdges] using hf
  exact hnonPEClosed hnonPE hfd.1 hx hfd.2 hcx

private theorem helper_closureA_384.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds; TreeSequenceInitialSegment
        base.core A → ett.series.data.kind n = some TashkinovExtensionKind.PE →
        TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A n coreA hp
  obtain ⟨u⟩ := (base.parallel hp).2.2
  intro v hv
  apply TreeSequenceInitialSegmentVertexSetSubset coreA
  rw [u.vertexSet]
  exact Finset.mem_union_right _ hv

private theorem helper_firstIn_391.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (T : TreeSequence G e0) (phi : PartialEdgeColoring E k), (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W Z
        → TreeSequenceInitialSegment U Z) →
    ∀ (B : TreeSequence G e0), TreeSequenceInitialSegment B T →
    ∀ c ∈ TreeMissingColors phi B, T.vertex (HierarchyFirstMissingPosition phi T c) ∈
        TreeSequenceVertexSet B := by
  classical
  intro V E _ _ G k e0 T phi trans B hBT c hc
  let _ := Fintype.ofFinite V
  clear * - B hBT c hc
  obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨i, hi⟩ : ∃ i, B.vertex i = v := by
    simpa [TreeSequenceVertexSet] using hv
  let iT := Fin.castLE (Nat.succ_le_succ hBT.1) i
  let S := Finset.univ.filter fun j : Fin (T.length + 1) =>
    c ∈ MissingColors G phi (T.vertex j)
  have hiS : iT ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [iT, hBT.2.1 i, hi] using hvc
  have hS : S.Nonempty := ⟨iT, hiS⟩
  have hpos : HierarchyFirstMissingPosition phi T c = S.min' hS := by
    simp only [HierarchyFirstMissingPosition, S, dite_eq_left hS]
  have hbound : (HierarchyFirstMissingPosition phi T c).val ≤ B.length := by
    have hh := Finset.min'_le S iT hiS
    rw [← hpos] at hh
    have := i.isLt
    change (HierarchyFirstMissingPosition phi T c).val ≤ i.val at hh
    omega
  let j : Fin (B.length + 1) := ⟨(HierarchyFirstMissingPosition phi T c).val, by omega⟩
  have hj : Fin.castLE (Nat.succ_le_succ hBT.1) j =
      HierarchyFirstMissingPosition phi T c := Fin.ext rfl
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨j, (hBT.2.1 j).symm.trans (congrArg T.vertex hj)⟩

private theorem helper_halphaA_419.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta
        : Fin k), (
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n; (0 : ℕ) < H.dividerCount ∧
        alpha ∈ TreeMissingColors phi Tnq ∨ H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        phi Tn ∨ alpha ∈ TreeMissingColors phi A ∧ alpha ∉ Dn ∧ beta ∉ Dn)) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; TreeSequenceInitialSegment Tn A
        → alpha ∈ TreeMissingColors phi A := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hcase H q A n Tn TnA
  rcases hcase with ⟨hq, ha⟩ | ⟨hq, ha | ha⟩
  · have hq0 : q ≠ 0 := by
      intro hz
      have hv := congrArg Fin.val hz
      change H.dividerCount = 0 at hv
      change 0 < H.dividerCount at hq
      omega
    have hstar : A = H.stage q.castSucc := by
      dsimp only [A]
      rw [← Fin.succ_pred q hq0]
      rfl
    have hstage : q.castSucc =
        (⟨H.dividerCount, by omega⟩ : Fin (H.dividerCount + 2)) := Fin.ext rfl
    simpa only [hstar, hstage] using ha
  · obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr
      ⟨v, TreeSequenceInitialSegmentVertexSetSubset TnA hv, hvm⟩
  · exact ha.1

private theorem helper_outsideOfInter_535.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) (k : ℕ) (e0
        : E) (phi : PartialEdgeColoring E k) (alpha beta : Fin k), alpha ≠ beta →
    ∀ (z : V ⊕ E), TwoColorPathComponent G phi alpha beta z →
    ∀ (sigma : PartialEdgeColoring E k), sigma = TwoColorComponentSwap G phi alpha beta z →
    ∀ (B : TreeSequence G e0),
    ∀ v ∈ TreeSequenceVertexSet B, TwoColorPathComponent G phi alpha beta (Sum.inl v) →
        TreeInterchangeable G B phi alpha beta → Sum.inl v ∉ TwoColorComponent G phi alpha beta z
        → OutsideKempeRecoloring B phi sigma alpha beta := by
  classical
  intro V E _ _ G k e0 phi alpha beta hne z hpath sigma hsigma B v hv hp hi hout
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  have avoid (w : V) (hw : w ∈ TreeSequenceVertexSet B) :
      Sum.inl w ∉ TwoColorComponent G phi alpha beta z := by
    intro hc
    have heq := hi z (Sum.inl v) hpath hp ⟨w, hw, hc⟩ ⟨v, hv, rfl⟩
    apply hout
    rw [heq]
    rfl
  refine ⟨hne, {z}, ?_, ?_⟩
  · intro w hw v hv hvB
    have hwz := Finset.mem_singleton.mp hw
    subst w
    exact avoid v hvB hv
  · intro f
    rw [hsigma]
    simp only [TwoColorComponentSwap, Finset.mem_singleton, exists_eq_left]

private theorem helper_sigmaOne_571.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi :
        PartialEdgeColoring E k) (alpha beta : Fin k) (z : V ⊕ E) (sigma : PartialEdgeColoring E
        k), sigma = TwoColorComponentSwap G phi alpha beta z → IsOneEdgeUncolored phi e0 →
        IsOneEdgeUncolored sigma e0 := by
  classical
  intro V E G k e0 phi alpha beta z sigma hsigma hone
  rw [hsigma]
  constructor
  · simp [TwoColorComponentSwap, hone.1]
  · intro f hfe
    obtain ⟨c, hc⟩ := hone.2 f hfe
    by_cases hf : Sum.inr f ∈ TwoColorComponent G phi alpha beta z
    · by_cases ha : phi f = some alpha
      · exact ⟨beta, by simp [TwoColorComponentSwap, hf, ha]⟩
      · by_cases hb : phi f = some beta
        · exact ⟨alpha, by simp [TwoColorComponentSwap, hf, hb]⟩
        · exact ⟨c, by
            simp only [TwoColorComponentSwap, ite_eq_left hf, ite_eq_right ha, ite_eq_right hb]
            exact hc⟩
    · exact ⟨c, by simp [TwoColorComponentSwap, hf, hc]⟩

private theorem helper_nonPEInter_586.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (_ : HierarchyCounterexample base),
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
        LowerRoundProperties lower) →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W Z
        → TreeSequenceInitialSegment U Z) → ett.series.data.kind n ≠ some
        TashkinovExtensionKind.PE →
    ∀ (c d : Fin k), c ∈ TreeMissingColors phi Tn → TreeInterchangeable G Tn phi c d := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower n Tn trans hp c d hc
  let j : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
  have hj : j.succ = n := Fin.ext (by simp [j, n]; have := C.positive; omega)
  have hprev : StableColoring Tn
      (TashkinovStoredColors ett.series.data j.castSucc)
      (ett.series.data.coloring j.castSucc) phi := by
    have step := ett.series.certified n
    generalize hi : n = i at step
    cases step with
    | initial =>
      have hv := congrArg Fin.val hi
      simp [n] at hv
      have := C.positive
      omega
    | SE ji _ _ _ _ _ choice _ coloring stored edges kind vertex outside
        delta gamma seed adjoin closure ordered strict =>
      have hji : ji = j := Fin.ext (by
        have hv := congrArg Fin.val hi
        simp [n, j] at hv ⊢
        omega)
      subst ji
      have hc : phi = choice.selected := by
        simpa only [← hj, coloring, n] using ett.generatingColoring
      simpa only [hj, Tn, hc] using choice.selectedStable
    | RE ji _ _ _ _ available coloring stored edges kind vertex outside
        delta gamma seed adjoin closure ordered strict =>
      have hji : ji = j := Fin.ext (by
        have hv := congrArg Fin.val hi
        simp [n, j] at hv ⊢
        omega)
      subst ji
      have hc : phi = ett.series.data.coloring j.castSucc := by
        simpa only [← hj, coloring, n] using ett.generatingColoring
      refine ⟨?_, ?_⟩
      · intro f _ _
        exact congrFun hc f
      · intro v _
        exact congrArg (fun psi => MissingColors G psi v) hc
    | PE ji _ _ _ _ _ choice _ gamma _ second _ _ _ exit coloring proper
        one stored edges kind vertex outside delta gammaEq closure ordered strict =>
      exact (hp (by simpa [← hi] using kind)).elim
  have hm : c ∈ TreeMissingColors phi Tn := hc
  by_cases hn : 1 < ett.rounds
  · obtain ⟨lower, hr, hmax, htrees, hdata⟩ :=
      CertifiedETTRestriction G k e0 input T phi ett C.maximum
        (ett.rounds - 1) (by omega) (by omega)
    let nl : Fin (lower.rounds + 1) := Fin.last lower.rounds
    have hcidx : Fin.castLE (by omega) nl = j.castSucc :=
      Fin.ext (by simp [nl, j, hr])
    have htidx : Fin.castLE (by omega) (Fin.last (lower.rounds + 1)) =
        n.castSucc := Fin.ext (by simp [n, hr]; omega)
    have ht : lower.series.data.tree (Fin.last (lower.rounds + 1)) = Tn :=
      (htrees _).trans (congrArg ett.series.data.tree htidx)
    obtain ⟨hc, _, _, _, _, _, _, _, hd, _⟩ := hdata nl
    rw [hcidx] at hc hd
    have hs : StableColoring
        (lower.series.data.tree (Fin.last (lower.rounds + 1)))
        (TashkinovStoredColors lower.series.data nl)
        (lower.series.data.coloring nl) phi := by
      rw [ht, hc, hd]
      exact hprev
    have hi := (hlower lower (by omega) (by omega) hmax).2.1
      phi hproper hone hs c d (Or.inl (by rw [ht]; exact hm))
    simpa only [ht] using hi
  · have hn1 : ett.rounds = 1 := by have := C.positive; omega
    have hj0 : j.castSucc = (0 : Fin (ett.rounds + 1)) :=
      Fin.ext (by simp [j, hn1])
    have ht1 : n.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) :=
      Fin.ext (by simp [n, hn1])
    have hs : StableColoring (ett.series.data.tree ⟨1, by omega⟩)
        (TashkinovStoredColors ett.series.data 0)
        (ett.series.data.coloring 0) phi := by
      simpa only [Tn, ht1, hj0] using hprev
    have hi := (TechnicalTheoremBase G k ett.rounds e0 input ett.series).2
      phi hproper hone hs c d
      (Or.inl (by simpa only [Tn, ht1] using hm))
    have hTn1 : Tn = ett.series.data.tree ⟨1, by omega⟩ :=
      congrArg ett.series.data.tree ht1
    change TreeInterchangeable G Tn phi c d
    rw [hTn1]
    exact hi

private theorem helper_closedStar_669.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
        IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
        LowerRoundProperties lower) → (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (other : ExtendedTashkinovTree G k e0 input' T'
        generating'), other.rounds = ett.rounds → MaximumProperty other →
    ∀ (base' : HierarchyBase other generating') (K : TashkinovHierarchy other base') (_ :
        GoodHierarchy K), K.dividerCount < C.hierarchy.dividerCount → ColoredVertexSetElementary G
        generating' (TreeSequenceVertexSet T')) → (
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; (2 : ℕ) * ett.rounds + (11 : ℕ)
        ≤ (TreeMissingColors phi Tn).card) →
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; CombinedStableColoring Tn
        base.closure (TashkinovStoredColors ett.series.data n) phi phi → (ett.series.data.kind n ≠
        some TashkinovExtensionKind.PE →
    ∀ (c d : Fin k), c ∈ TreeMissingColors phi Tn → TreeInterchangeable G Tn phi c d) →
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))) (c d : Fin k), c ≠ d → c ∈ TreeMissingColors phi
        (HierarchyStarredStage H r) → TreeColorSetClosed G phi (HierarchyStarredStage H r) ({ c }
        : Finset (Fin k)) → TreeInterchangeable G (HierarchyStarredStage H r) phi c d := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hproper hone hlower hfewer hlarge H n Tn
      hcombined nonPEInter r c d hcd hc hclosed
  cases r using Fin.cases with
  | zero =>
    change TreeInterchangeable G base.core phi c d
    change c ∈ TreeMissingColors phi base.core at hc
    change TreeColorSetClosed G phi base.core {c} at hclosed
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (interchange G k e0 input T phi phi ett C.maximum C.positive
        hlower hp base hproper hone hcombined c d).2.2.1 hc hclosed
    · rw [base.nonparallel hp] at hc ⊢
      exact nonPEInter hp c d hc
  | succ i =>
    exact step1 G k e0 input T phi ett C.maximum C.positive hproper hone
      hlower base H C.good hfewer hlarge i c d hc hcd hclosed

private theorem helper_closedOutside_690.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta
        : Fin k), alpha ≠ beta →
    ∀ (z : V ⊕ E) (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let a : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    let b : V := T.vertex (HierarchyFirstMissingPosition phi T beta); (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W Z
        → TreeSequenceInitialSegment U Z) → (
    ∀ (r s : Fin (H.dividerCount + (1 : ℕ))), r ≤ s → TreeSequenceInitialSegment
        (HierarchyStarredStage H r) (HierarchyStarredStage H s)) → TreeSequenceInitialSegment A T
        → alpha ∈ MissingColors G phi a → (
    ∀ (c d : Fin k), c ≠ d →
    ∀ (v : V), c ∈ MissingColors G phi v → TwoColorPathComponent G phi c d (Sum.inl v)) → (
    ∀ (B : TreeSequence G e0) (c d : Fin k), TreeInterchangeable G B phi c d → TreeInterchangeable
        G B phi d c) → (
    ∀ (B : TreeSequence G e0), TreeSequenceInitialSegment B T →
    ∀ c ∈ TreeMissingColors phi B, T.vertex (HierarchyFirstMissingPosition phi T c) ∈
        TreeSequenceVertexSet B) → Sum.inl a ∉ TwoColorComponent G phi alpha beta z → (beta ∈
        TreeMissingColors phi A → Sum.inl b ∉ TwoColorComponent G phi alpha beta z) → (
    ∀ (B : TreeSequence G e0),
    ∀ v ∈ TreeSequenceVertexSet B, TwoColorPathComponent G phi alpha beta (Sum.inl v) →
        TreeInterchangeable G B phi alpha beta → Sum.inl v ∉ TwoColorComponent G phi alpha beta z
        → OutsideKempeRecoloring B phi sigma alpha beta) → (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))) (c d : Fin k), c ≠ d → c ∈ TreeMissingColors phi
        (HierarchyStarredStage H r) → TreeColorSetClosed G phi (HierarchyStarredStage H r) ({ c }
        : Finset (Fin k)) → TreeInterchangeable G (HierarchyStarredStage H r) phi c d) →
        TwoColorPathComponent G phi alpha beta (Sum.inl b) →
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))) (c : Fin k), c = alpha ∨ c = beta → c ∈
        TreeMissingColors phi (HierarchyStarredStage H r) → TreeColorSetClosed G phi
        (HierarchyStarredStage H r) ({ c } : Finset (Fin k)) → OutsideKempeRecoloring
        (HierarchyStarredStage H r) phi sigma alpha beta := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne z sigma H q A a b trans
      starChain hAT haMissing pathMissing interchangeableSwap firstIn haOutside hbOutside
      outsideOfInter closedStar betaPath r c hc hm hcl
  have hrT := trans (starChain r q (Fin.le_last r)) hAT
  rcases hc with hc | hc
  · subst c
    exact outsideOfInter _ a (firstIn _ hrT alpha hm)
      (pathMissing alpha beta hne a haMissing)
      (closedStar r alpha beta hne hm hcl) haOutside
  · subst c
    have hbA : beta ∈ TreeMissingColors phi A := by
      obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hm
      exact Finset.mem_biUnion.mpr
        ⟨v, TreeSequenceInitialSegmentVertexSetSubset (starChain r q (Fin.le_last r)) hv, hvm⟩
    exact outsideOfInter _ b (firstIn _ hrT beta hm) betaPath
      (interchangeableSwap _ beta alpha (closedStar r beta alpha hne.symm hm hcl))
      (hbOutside hbA)

private theorem helper_maxClosed_714.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    ∀ (c : Fin k), (
    ∃ (r : Fin (H.dividerCount + (1 : ℕ))), TreeColorSetClosed G phi (HierarchyStarredStage H r)
        ({ c } : Finset (Fin k))) →
    ∃ (r : Fin (H.dividerCount + (1 : ℕ))), TreeColorSetClosed G phi (HierarchyStarredStage H r)
        ({ c } : Finset (Fin k)) ∧
    ∀ (s : Fin (H.dividerCount + (1 : ℕ))), (↑r : ℕ) < (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) ({ c } : Finset (Fin k)) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H c hex
  let S := Finset.univ.filter fun r : Fin (H.dividerCount + 1) =>
    TreeColorSetClosed G phi (HierarchyStarredStage H r) {c}
  have hS : S.Nonempty := by
    obtain ⟨r, hr⟩ := hex
    exact ⟨r, by simp [S, hr]⟩
  refine ⟨S.max' hS, (Finset.mem_filter.mp (Finset.max'_mem S hS)).2, ?_⟩
  intro s hs hcl
  have hmem : s ∈ S := by simp [S, hcl]
  have hle := Finset.le_max' S s hmem
  change s.val ≤ (S.max' hS).val at hle
  omega

private theorem helper_missingAtMax_731.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (
    ∀ (r s : Fin (H.dividerCount + (1 : ℕ))), r ≤ s → TreeSequenceInitialSegment
        (HierarchyStarredStage H r) (HierarchyStarredStage H s)) → (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H r))) → (
    ∀ {B S : TreeSequence G e0}, TreeSequenceInitialSegment B S → TreeMissingColors phi B ⊆
        TreeMissingColors phi S) →
    ∀ c ∈ TreeMissingColors phi A,
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), (
    ∀ (s : Fin (H.dividerCount + (1 : ℕ))), (↑r : ℕ) < (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) ({ c } : Finset (Fin k))) → c ∈ TreeMissingColors phi
        (HierarchyStarredStage H r) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C H q A starChain helemStar missingSubset c hcA r
      hmax
  let P (j : ℕ) := ∃ hj : j ≤ H.dividerCount,
    c ∈ TreeMissingColors phi (HierarchyStarredStage H ⟨j, by omega⟩)
  have hex : ∃ j, P j := ⟨H.dividerCount, le_rfl, hcA⟩
  let s := Nat.find hex
  obtain ⟨hs, hsm⟩ : P s := Nat.find_spec hex
  by_cases hsr : s ≤ r.val
  · exact missingSubset (starChain ⟨s, by omega⟩ r hsr) hsm
  · have hspos : 0 < s := by omega
    let i : Fin H.dividerCount := ⟨s - 1, by omega⟩
    have his : i.succ = (⟨s, by omega⟩ : Fin (H.dividerCount + 1)) :=
      Fin.ext (by simp [i]; omega)
    have hprev : c ∉ TreeMissingColors phi (HierarchyStarredStage H i.castSucc) := by
      intro hm
      have hh : P (s - 1) := ⟨by omega, hm⟩
      have hmin := Nat.find_min' hex hh
      change s ≤ s - 1 at hmin
      omega
    have hsm' : c ∈ TreeMissingColors phi (H.stage i.succ.castSucc) := by
      simpa only [← his, HierarchyStarredStage, Fin.cases_succ] using hsm
    obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hsm'
    have hvnew : v ∉ TreeSequenceVertexSet (HierarchyStarredStage H i.castSucc) := by
      intro hh
      exact hprev (Finset.mem_biUnion.mpr ⟨v, hh, hvm⟩)
    have hnew := GoodHierarchyNewMissingClosed C.good i (helemStar i.succ) c
      (Finset.mem_biUnion.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvnew⟩, hvm⟩)
    apply False.elim
    apply hmax i.succ (by simp [i]; omega)
    intro d hd
    have heq : d = c := Finset.mem_singleton.mp hd
    subst d
    exact hnew

private theorem helper_branch_773.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ {u : V}, ett.rounds = (1 : ℕ) → u ∈ TreeSequenceVertexSet Tn →
    ∀ {v : V}, v ∈ TreeSequenceVertexSet Tn → u ≠ v → Disjoint (MissingColors G
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    have this : (0 : ℕ) < ett.rounds := C.positive; Decidable.byContradiction fun (a : ¬ett.rounds
        - (1 : ℕ) < ett.rounds) ↦
    by
                  omega
    ⟩ : Fin ett.rounds).castSucc) u) (MissingColors G (ett.series.data.coloring (⟨ett.rounds - (1
        : ℕ),
    have this : (0 : ℕ) < ett.rounds := C.positive; Decidable.byContradiction fun (a : ¬ett.rounds
        - (1 : ℕ) < ett.rounds) ↦
    by
                  omega
    ⟩ : Fin ett.rounds).castSucc) v) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C n Tn _ hn
  have hcolor : (⟨ett.rounds - 1, by have := C.positive; omega⟩ : Fin ett.rounds).castSucc =
    0 :=
    Fin.ext (by simp [hn])
  have htree : n.castSucc = (⟨1, by omega⟩ : Fin (ett.rounds + 2)) :=
    Fin.ext (by simp [n, hn])
  dsimp only [Tn]
  rw [hcolor, htree]
  exact (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1

private theorem helper_branch_781.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base), (
    ∀ {input' : PartialEdgeColoring E k} {T' : TreeSequence G e0}
        {generating' : PartialEdgeColoring E k} (lower : ExtendedTashkinovTree G k e0 input' T'
        generating'), (0 : ℕ) < lower.rounds → lower.rounds < ett.rounds → MaximumProperty lower →
        LowerRoundProperties lower) →
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    ∀ {u : V}, ¬ett.rounds = (1 : ℕ) → u ∈ TreeSequenceVertexSet Tn →
    ∀ {v : V}, v ∈ TreeSequenceVertexSet Tn → u ≠ v → Disjoint (MissingColors G
        (ett.series.data.coloring (⟨ett.rounds - (1 : ℕ),
    have this : (0 : ℕ) < ett.rounds := C.positive; Decidable.byContradiction fun (a : ¬ett.rounds
        - (1 : ℕ) < ett.rounds) ↦
    by
                  omega
    ⟩ : Fin ett.rounds).castSucc) u) (MissingColors G (ett.series.data.coloring (⟨ett.rounds - (1
        : ℕ),
    have this : (0 : ℕ) < ett.rounds := C.positive; Decidable.byContradiction fun (a : ¬ett.rounds
        - (1 : ℕ) < ett.rounds) ↦
    by
                  omega
    ⟩ : Fin ett.rounds).castSucc) v) := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hlower n Tn _ hn
  have hmore : 1 < ett.rounds := by have := C.positive; omega
  obtain ⟨predecessor, hr, hmaximum, _, _⟩ :=
    CertifiedETTPredecessor G k e0 input T phi ett C.maximum hmore
  have htree : n.castSucc = (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + 2)) :=
    Fin.ext rfl
  dsimp only [Tn]
  rw [htree]
  exact (hlower predecessor (by omega) (by omega) hmaximum).1

private theorem helper_stableNoAffected_799.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta
        : Fin k) (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q; (
    ∀ {U W Z : TreeSequence G e0}, TreeSequenceInitialSegment U W → TreeSequenceInitialSegment W Z
        → TreeSequenceInitialSegment U Z) → (
    ∀ (f : E), phi f ≠ some alpha → phi f ≠ some beta → sigma f = phi f) → (
    ∀ v ∈ TreeSequenceVertexSet A, MissingColors G sigma v = MissingColors G phi v) →
    ∀ (B : TreeSequence G e0) (D : Finset (Fin k)), TreeSequenceVertexSet B ⊆
        TreeSequenceVertexSet A → alpha ∉ TreeMissingColors phi B ∪ D → beta ∉ TreeMissingColors
        phi B ∪ D → StableColoring B D phi sigma := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta sigma H q A trans fixedValue
      missingA B D hBA hna hnb
  refine ⟨?_, fun v hv => missingA v (hBA hv)⟩
  intro f hf hcol
  obtain ⟨c, hc, hfc⟩ := hcol
  apply fixedValue
  · intro ha
    have heq : c = alpha := Option.some.inj (hfc.symm.trans ha)
    subst c
    exact hna hc
  · intro hb
    have heq : c = beta := Option.some.inj (hfc.symm.trans hb)
    subst c
    exact hnb hc

private theorem helper_stableFromCore_816.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (alpha beta : Fin k) (sigma :
        PartialEdgeColoring E k),
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; TreeSequenceInitialSegment Tn
        base.core → (
    ∀ (B S : TreeSequence G e0), TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet S →
        OutsideKempeRecoloring S phi sigma alpha beta → OutsideKempeRecoloring B phi sigma alpha
        beta) → (
    ∀ (B : TreeSequence G e0) (D : Finset (Fin k)), OutsideKempeRecoloring B phi sigma alpha beta
        → StableColoring B D phi sigma ∧
    ∀ (f : E), TreeIncidentEdge B f → sigma f = phi f) →
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let baseStable : Prop := if ett.series.data.kind n = some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn base.closure Dn phi sigma else StableColoring Tn Dn phi sigma;
        OutsideKempeRecoloring base.core phi sigma alpha beta → baseStable := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base alpha beta sigma n Tn coreChain outsideMono
      outsideStable Dn baseStable hout
  have hn := (outsideStable Tn Dn (outsideMono Tn base.core
    (TreeSequenceInitialSegmentVertexSetSubset coreChain) hout)).1
  by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
  · simp only [baseStable, hp, ite_true]
    have hR : TreeSequenceVertexSet base.closure ⊆ TreeSequenceVertexSet base.core := by
      obtain ⟨u⟩ := (base.parallel hp).2.2
      rw [u.vertexSet]
      exact Finset.subset_union_right
    exact ⟨hn, (outsideStable base.closure ∅
      (outsideMono base.closure base.core hR hout)).1⟩
  · simpa only [baseStable, hp, ite_false] using hn

private theorem helper_branch_833.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta
        : Fin k) (sigma : PartialEdgeColoring E k),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc; (
    ∀ (r s : Fin (H.dividerCount + (1 : ℕ))), r ≤ s → TreeSequenceInitialSegment
        (HierarchyStarredStage H r) (HierarchyStarredStage H s)) → (
    ∀ (B S : TreeSequence G e0), TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet S →
        OutsideKempeRecoloring S phi sigma alpha beta → OutsideKempeRecoloring B phi sigma alpha
        beta) → (
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))) (c : Fin k), c = alpha ∨ c = beta → c ∈
        TreeMissingColors phi (HierarchyStarredStage H r) → TreeColorSetClosed G phi
        (HierarchyStarredStage H r) ({ c } : Finset (Fin k)) → OutsideKempeRecoloring
        (HierarchyStarredStage H r) phi sigma alpha beta) → (
    ∀ (c : Fin k), (
    ∃ (r : Fin (H.dividerCount + (1 : ℕ))), TreeColorSetClosed G phi (HierarchyStarredStage H r)
        ({ c } : Finset (Fin k))) →
    ∃ (r : Fin (H.dividerCount + (1 : ℕ))), TreeColorSetClosed G phi (HierarchyStarredStage H r)
        ({ c } : Finset (Fin k)) ∧
    ∀ (s : Fin (H.dividerCount + (1 : ℕ))), (↑r : ℕ) < (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) ({ c } : Finset (Fin k))) → (
    ∀ c ∈ TreeMissingColors phi A,
    ∀ (r : Fin (H.dividerCount + (1 : ℕ))), (
    ∀ (s : Fin (H.dividerCount + (1 : ℕ))), (↑r : ℕ) < (↑s : ℕ) → ¬TreeColorSetClosed G phi
        (HierarchyStarredStage H s) ({ c } : Finset (Fin k))) → c ∈ TreeMissingColors phi
        (HierarchyStarredStage H r)) →
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n;
    let baseStable : Prop := if ett.series.data.kind n = some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn base.closure Dn phi sigma else StableColoring Tn Dn phi sigma;
        (OutsideKempeRecoloring base.core phi sigma alpha beta → baseStable) → (
    ∃ (c : Fin k), (c = alpha ∨ c = beta) ∧ c ∈ TreeMissingColors phi A ∧
    ∃ (r : Fin (H.dividerCount + (1 : ℕ))), TreeColorSetClosed G phi (HierarchyStarredStage H r)
        ({ c } : Finset (Fin k))) → baseStable := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta sigma H q A n Tn starChain
      outsideMono closedOutside maxClosed missingAtMax Dn baseStable stableFromCore hex
  obtain ⟨c, hc, hm, hr⟩ := hex
  obtain ⟨r, hcl, hmax⟩ := maxClosed c hr
  have hmr := missingAtMax c hm r hmax
  have hout := closedOutside r c hc hmr hcl
  exact stableFromCore (outsideMono base.core _
    (TreeSequenceInitialSegmentVertexSetSubset (starChain 0 r (Fin.zero_le _))) hout)

private theorem helper_missingA_1163.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (C : HierarchyCounterexample base) (alpha beta
        : Fin k) (_ : alpha ≠ beta) (_ :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let ell : ℕ := T.length - A.length;
    let Ty : TreeSequence G e0 := TreeSequencePrefix T (min (A.length + (ell - (1 : ℕ))) T.length)
        (le_min (le_trans A.positive (Nat.le_add_right _ _)) T.positive) (Nat.min_le_right
        (A.length + (ell - (1 : ℕ))) T.length); alpha ∈ TreeMissingColors phi Ty ∧ beta ∈
        TreeMissingColors phi Ty) (z : V ⊕ E) (_ : TwoColorPathComponent G phi alpha beta z)
        (sigma : PartialEdgeColoring E k) (_ : sigma = TwoColorComponentSwap G phi alpha beta z)
        (_ :
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let n : Fin (ett.rounds + (1 : ℕ)) := Fin.last ett.rounds;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let Tnq : TreeSequence G e0 := H.stage (⟨H.dividerCount,
    by
                omega
    ⟩ : Fin (H.dividerCount + (2 : ℕ)));
    let Tn : TreeSequence G e0 := ett.series.data.tree n.castSucc;
    let Dn : Finset (Fin k) := TashkinovStoredColors ett.series.data n; (0 : ℕ) < H.dividerCount ∧
        alpha ∈ TreeMissingColors phi Tnq ∨ H.dividerCount = (0 : ℕ) ∧ (alpha ∈ TreeMissingColors
        phi Tn ∨ alpha ∈ TreeMissingColors phi A ∧ alpha ∉ Dn ∧ beta ∉ Dn)) (_ :
    let va : V := T.vertex (HierarchyFirstMissingPosition phi T alpha); Disjoint
        (TwoColorComponent G phi alpha beta z) (TwoColorComponent G phi alpha beta (Sum.inl va)))
        (_ : IsProperEdgeColoring G phi),
    let H : TashkinovHierarchy ett base := C.hierarchy;
    let q : Fin (H.dividerCount + (1 : ℕ)) := Fin.last H.dividerCount;
    let A : TreeSequence G e0 := HierarchyStarredStage H q;
    let a : V := T.vertex (HierarchyFirstMissingPosition phi T alpha);
    let b : V := T.vertex (HierarchyFirstMissingPosition phi T beta);
    ∀ (_ : alpha ∈ MissingColors G phi a) (_ : beta ∈ MissingColors G phi b) (_ : alpha ∈
        TreeMissingColors phi A) (_ : a ∈ TreeSequenceVertexSet A) (_ :
    ∀ (_ : beta ∈ TreeMissingColors phi A), TwoColorComponent G phi alpha beta (Sum.inl a) =
        TwoColorComponent G phi alpha beta (Sum.inl b)) (_ : Sum.inl a ∉ TwoColorComponent G phi
        alpha beta z) (_ :
    ∀ (_ : beta ∈ TreeMissingColors phi A), Sum.inl b ∉ TwoColorComponent G phi alpha beta z) (_ :
    ∀ (c : Fin k) (_ : c ∈ TreeMissingColors phi A) (v : V) (_ : v ∈ TreeSequenceVertexSet A) (_ :
        c ∈ MissingColors G phi v) (_ : c ∈ MissingColors G phi (T.vertex
        (HierarchyFirstMissingPosition phi T c))), v = T.vertex (HierarchyFirstMissingPosition phi
        T c)) (_ :
    ∀ {v : V} {f : E} (_ : Sum.inl v ∈ TwoColorComponent G phi alpha beta z) (_ : Incident G v f)
        (_ : phi f = some alpha ∨ phi f = some beta), Sum.inr f ∈ TwoColorComponent G phi alpha
        beta z) (_ :
    ∀ (f : E) (_ : phi f ≠ some alpha) (_ : phi f ≠ some beta), sigma f = phi f) (v : V) (_ : v ∈
        TreeSequenceVertexSet A), MissingColors G sigma v = MissingColors G phi v := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C alpha beta hne hmissingPrefix z hpath sigma
      hsigma hcase hdisjoint hproper H q A a b haMissing hbMissing halphaA haA hsame haOutside
      hbOutside missingUnique edgeOfVertex fixedValue v hv
  have behavior := TwoColorComponentSwapMissingBehavior G phi alpha beta hne hproper z
  rw [hsigma]
  by_cases hout : Sum.inl v ∉ TwoColorComponent G phi alpha beta z
  · exact behavior.1 v hout
  · have hin : Sum.inl v ∈ TwoColorComponent G phi alpha beta z := not_not.mp hout
    have hna : alpha ∉ MissingColors G phi v := by
      intro hm
      have heq := missingUnique alpha halphaA v hv hm haMissing
      subst v
      exact haOutside hin
    have hnb : beta ∉ MissingColors G phi v := by
      intro hm
      have hbA : beta ∈ TreeMissingColors phi A := Finset.mem_biUnion.mpr ⟨v, hv, hm⟩
      have heq := missingUnique beta hbA v hv hm hbMissing
      subst v
      exact hbOutside hbA hin
    have newPresent (c d : Fin k) (hcd : c = alpha ∧ d = beta ∨ c = beta ∧ d = alpha)
        (hd : d ∉ MissingColors G phi v) :
        c ∉ MissingColors G (TwoColorComponentSwap G phi alpha beta z) v := by
      have hp : d ∈ PresentColors G phi v := by simpa [MissingColors] using hd
      obtain ⟨f, hf, hcol⟩ : ∃ f, Incident G v f ∧ phi f = some d := by
        simpa [PresentColors] using hp
      have hfe : Sum.inr f ∈ TwoColorComponent G phi alpha beta z := by
        apply edgeOfVertex hin hf
        rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr hcol
        · exact Or.inl hcol
      have hnew : TwoColorComponentSwap G phi alpha beta z f = some c := by
        rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [TwoColorComponentSwap, hfe, hcol, hne.symm]
        · simp [TwoColorComponentSwap, hfe, hcol]
      have hpnew : c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨f, hf, hnew⟩
      simpa [MissingColors] using hpnew
    apply Finset.ext
    intro c
    by_cases hca : c = alpha
    · subst c
      simp only [hna, newPresent alpha beta (Or.inl ⟨rfl, rfl⟩) hnb]
    · by_cases hcb : c = beta
      · subst c
        simp only [hnb, newPresent beta alpha (Or.inr ⟨rfl, rfl⟩) hna]
      · exact behavior.2.2.2 v c hca hcb

private theorem helper_baseStableProof_1297.{u_1, u_2} :
    helperBaseStableProof1297Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hprefixElementary alpha beta hne z sigma hcase
      hproper hone hlower H q A n Tn a trans starChain hAT haMissing pathMissing
      interchangeableSwap hcombined nonPEMissingClosed coreChain TnA closureA firstIn halphaA haA
      haOutside missingUnique outsideOfInter outsideMono outsideStable closedOutside maxClosed
      missingAtMax preStepElementary lastZero Dn baseStable stableNoAffected stableFromCore
  by_cases hex : ∃ c : Fin k, (c = alpha ∨ c = beta) ∧
      c ∈ TreeMissingColors phi A ∧
      ∃ r, TreeColorSetClosed G phi (HierarchyStarredStage H r) {c}
  · exact @helper_branch_833 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@sigma)
      (@starChain) (@outsideMono) (@closedOutside) (@maxClosed) (@missingAtMax) (@stableFromCore)
      (@hex)
  · have noClosed (c : Fin k) (hc : c = alpha ∨ c = beta)
        (hm : c ∈ TreeMissingColors phi A) (r : Fin (H.dividerCount + 1)) :
        ¬ TreeColorSetClosed G phi (HierarchyStarredStage H r) {c} := by
      intro hr
      exact hex ⟨c, hc, hm, r, hr⟩
    have hpe : ett.series.data.kind n = some TashkinovExtensionKind.PE := by
      by_contra hp
      by_cases hq : 0 < H.dividerCount
      · have hh := (rutcor G k e0 input T phi ett base H C.good hq
          hprefixElementary preStepElementary alpha halphaA).2
          (noClosed alpha (Or.inl rfl) halphaA)
        exact hp hh.2.1
      · have hz : H.dividerCount = 0 := by omega
        have hm : alpha ∈ TreeMissingColors phi Tn := by
          simpa only [lastZero hz, base.nonparallel hp] using halphaA
        apply noClosed alpha (Or.inl rfl) halphaA 0
        change TreeColorSetClosed G phi base.core {alpha}
        rw [base.nonparallel hp]
        exact nonPEMissingClosed hp alpha hm
    have haCore : a ∈ TreeSequenceVertexSet base.core := by
      by_cases hq : 0 < H.dividerCount
      · have hh := (rutcor G k e0 input T phi ett base H C.good hq
          hprefixElementary preStepElementary alpha halphaA).2
          (noClosed alpha (Or.inl rfl) halphaA)
        exact TreeSequenceInitialSegmentVertexSetSubset coreChain
          (Finset.mem_sdiff.mp hh.2.2.1).1
      · simpa only [lastZero (by omega)] using haA
    have haNnotR : ¬ (a ∈ TreeSequenceVertexSet Tn ∧ a ∈ TreeSequenceVertexSet base.closure) := by
      intro hh
      have hmN : alpha ∈ TreeMissingColors phi Tn := Finset.mem_biUnion.mpr ⟨a, hh.1, haMissing⟩
      have hmR : alpha ∈ TreeMissingColors phi base.closure := Finset.mem_biUnion.mpr ⟨a, hh.2,
          haMissing⟩
      have hcl := ParallelCommonMissingClosed G k e0 input T phi phi ett
        C.positive base ett.generatingColoring hpe preStepElementary alpha
        (Finset.mem_inter.mpr ⟨hmN, hmR⟩)
      apply noClosed alpha (Or.inl rfl) halphaA 0
      intro c hc
      have heq : c = alpha := Finset.mem_singleton.mp hc
      subst c
      exact hcl
    have hRsub := closureA hpe
    have hi := interchange G k e0 input T phi phi ett C.maximum C.positive
      hlower hpe base hproper hone hcombined alpha beta
    have hj := interchange G k e0 input T phi phi ett C.maximum C.positive
      hlower hpe base hproper hone hcombined beta alpha
    by_cases haN : a ∈ TreeSequenceVertexSet Tn
    · have hmN : alpha ∈ TreeMissingColors phi Tn := Finset.mem_biUnion.mpr ⟨a, haN, haMissing⟩
      have houtN := outsideOfInter Tn a haN (pathMissing alpha beta hne a haMissing)
        (hi.2.1 hmN) haOutside
      by_cases hbR : beta ∈ TreeMissingColors phi base.closure
      · exact stableFromCore (outsideOfInter base.core a haCore
          (pathMissing alpha beta hne a haMissing) (hi.2.2.2 hmN hbR) haOutside)
      · have hnaR : alpha ∉ TreeMissingColors phi base.closure := by
          intro hm
          obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hm
          have heq := missingUnique alpha halphaA v (hRsub hv) hvm haMissing
          subst v
          exact haNnotR ⟨haN, hv⟩
        have hn := (outsideStable Tn Dn houtN).1
        have hr := stableNoAffected base.closure ∅ hRsub
          (by simpa only [Finset.union_empty] using hnaR)
          (by simpa only [Finset.union_empty] using hbR)
        simpa only [baseStable, hpe, ite_true, CombinedStableColoring] using And.intro hn hr
    · obtain ⟨u⟩ := (base.parallel hpe).2.2
      have haR : a ∈ TreeSequenceVertexSet base.closure := by
        have hh : a ∈ TreeSequenceVertexSet Tn ∨ a ∈ TreeSequenceVertexSet base.closure := by
          simpa only [u.vertexSet, Finset.mem_union] using haCore
        exact hh.resolve_left haN
      have hmR : alpha ∈ TreeMissingColors phi base.closure := Finset.mem_biUnion.mpr ⟨a, haR,
          haMissing⟩
      have houtR := outsideOfInter base.closure a haR (pathMissing alpha beta hne a haMissing)
        (hi.1 hmR) haOutside
      by_cases hbN : beta ∈ TreeMissingColors phi Tn
      · exact stableFromCore (outsideOfInter base.core a haCore
          (pathMissing alpha beta hne a haMissing)
          (interchangeableSwap base.core beta alpha (hj.2.2.2 hbN hmR)) haOutside)
      · have hnaN : alpha ∉ TreeMissingColors phi Tn := by
          intro hm
          have ha := firstIn Tn (trans TnA hAT) alpha hm
          exact haN ha
        have hzero : H.dividerCount = 0 := by
          by_contra hn
          have hq : 0 < H.dividerCount := by omega
          have hh := (rutcor G k e0 input T phi ett base H C.good hq
            hprefixElementary preStepElementary alpha halphaA).2
            (noClosed alpha (Or.inl rfl) halphaA)
          exact haN (Finset.mem_sdiff.mp hh.2.2.1).1
        have hDn : alpha ∉ Dn ∧ beta ∉ Dn := by
          rcases hcase with h | ⟨hq, h | h⟩
          · have hp : 0 < H.dividerCount := h.1
            omega
          · exact (hnaN h).elim
          · exact h.2
        have hn := stableNoAffected Tn Dn (TreeSequenceInitialSegmentVertexSetSubset TnA)
          (by simpa only [Finset.mem_union, not_or] using And.intro hnaN hDn.1)
          (by simpa only [Finset.mem_union, not_or] using And.intro hbN hDn.2)
        have hr := (outsideStable base.closure ∅ houtR).1
        simpa only [baseStable, hpe, ite_true, CombinedStableColoring] using And.intro hn hr

private theorem helper_continuation_1245.{u_1, u_2} :
    helperContinuation1245Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base C hprefixElementary alpha beta hne hmissingPrefix
      z hpath sigma hsigma hcase hdisjoint hproper hone hlower hfewer hlarge H q A n Tn a b trans
      starChain hAT helemStar haMissing hbMissing pathMissing graphSwap componentSwap
      interchangeableSwap hcombined nonPEMissingClosed coreChain TnA closureA firstIn halphaA haA
      hsame haOutside hbOutside missingUnique edgeOfVertex
  have fixedValue (f : E) (ha : phi f ≠ some alpha) (hb : phi f ≠ some beta) :
      sigma f = phi f := by
    rw [hsigma]
    simp only [TwoColorComponentSwap]
    split_ifs <;> simp_all
  have missingA := @helper_missingA_1163 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta) (@hne)
      (@hmissingPrefix) (@z) (@hpath) (@sigma) (@hsigma) (@hcase) (@hdisjoint) (@hproper)
      (@haMissing) (@hbMissing) (@halphaA) (@haA) (@hsame) (@haOutside) (@hbOutside)
      (@missingUnique) (@edgeOfVertex) (@fixedValue)
  have outsideOfInter := @helper_outsideOfInter_535 (@V) (@E) inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@alpha) (@beta) (@hne) (@z) (@hpath)
      (@sigma) (@hsigma)
  have outsideMono (B S : TreeSequence G e0)
      (hBS : TreeSequenceVertexSet B ⊆ TreeSequenceVertexSet S)
      (hout : OutsideKempeRecoloring S phi sigma alpha beta) :
      OutsideKempeRecoloring B phi sigma alpha beta := by
    rcases hout with ⟨hn, roots, ha, hb⟩
    exact ⟨hn, roots, fun z hz v hv hm => ha z hz v hv (hBS hm), hb⟩
  have outsideStable (B : TreeSequence G e0) (D : Finset (Fin k))
      (hout : OutsideKempeRecoloring B phi sigma alpha beta) :
      StableColoring B D phi sigma ∧
        (∀ f, TreeIncidentEdge B f → sigma f = phi f) := by
    have hh := OutsideKempeRecoloringStable G e0 B D phi sigma alpha beta hproper hone hout
    exact ⟨hh.2.2.1, hh.2.2.2.2⟩
  have sigmaProper : IsProperEdgeColoring G sigma := by
    rw [hsigma]
    exact TwoColorComponentSwapProper G phi alpha beta hne hproper z
  have sigmaOne := @helper_sigmaOne_571 (@V) (@E) (@G) (@k) (@e0) (@phi) (@alpha) (@beta) (@z)
      (@sigma) (@hsigma) (@hone)
  have nonPEInter := @helper_nonPEInter_586 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hlower) (@trans)
  have closedStar := @helper_closedStar_669 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@hlower) (@hfewer) (@hlarge) (@hcombined) (@nonPEInter)
  have betaPath : TwoColorPathComponent G phi alpha beta (Sum.inl b) := by
    have hp := pathMissing beta alpha hne.symm b hbMissing
    refine ⟨hne, ?_⟩
    simpa only [componentSwap alpha beta, graphSwap alpha beta] using hp.2
  have closedOutside := @helper_closedOutside_690 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha)
      (@beta) (@hne) (@z) (@sigma) (@trans) (@starChain) (@hAT) (@haMissing) (@pathMissing)
      (@interchangeableSwap) (@firstIn) (@haOutside) (@hbOutside) (@outsideOfInter) (@closedStar)
      (@betaPath)
  have missingSubset {B S : TreeSequence G e0} (hBS : TreeSequenceInitialSegment B S) :
      TreeMissingColors phi B ⊆ TreeMissingColors phi S := by
    intro c hc
    obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨v, TreeSequenceInitialSegmentVertexSetSubset hBS hv, hvm⟩
  have maxClosed := @helper_maxClosed_714 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
  have missingAtMax := @helper_missingAtMax_731 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@starChain)
      (@helemStar) (@missingSubset)
  have preStepElementary :
      let i : Fin ett.rounds := ⟨ett.rounds - 1, by have := C.positive; omega⟩
      ColoredVertexSetElementary G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet Tn) := by
    dsimp only
    by_cases hn : ett.rounds = 1
    · exact @helper_branch_773 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) _ (@hn)
    · exact @helper_branch_781 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hlower) _ (@hn)
  have lastZero (hq : H.dividerCount = 0) : A = base.core := by
    have hz : q = 0 := Fin.ext hq
    dsimp only [A]
    rw [hz]
    rfl
  let Dn := TashkinovStoredColors ett.series.data n
  let baseStable : Prop :=
    if ett.series.data.kind n = some TashkinovExtensionKind.PE then
      CombinedStableColoring Tn base.closure Dn phi sigma
    else StableColoring Tn Dn phi sigma
  have stableNoAffected := @helper_stableNoAffected_799 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha)
      (@beta) (@sigma) (@trans) (@fixedValue) (@missingA)
  have stableFromCore := @helper_stableFromCore_816 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@alpha)
      (@beta) (@sigma) (@coreChain) (@outsideMono) (@outsideStable)
  have baseStableProof := @helper_baseStableProof_1297 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C)
      (@hprefixElementary) (@alpha) (@beta) (@hne) (@z) (@sigma) (@hcase) (@hproper) (@hone)
      (@hlower) (@trans) (@starChain) (@hAT) (@haMissing) (@pathMissing) (@interchangeableSwap)
      (@hcombined) (@nonPEMissingClosed) (@coreChain) (@TnA) (@closureA) (@firstIn) (@halphaA)
      (@haA) (@haOutside) (@missingUnique) (@outsideOfInter) (@outsideMono) (@outsideStable)
      (@closedOutside) (@maxClosed) (@missingAtMax) (@preStepElementary) (@lastZero)
      (@stableNoAffected) (@stableFromCore)
  exact ⟨baseStableProof, missingA, sigmaProper, sigmaOne, closedOutside⟩

theorem P2813_T1_BaseControl {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (base : HierarchyBase ett phi)
    (C : HierarchyCounterexample base)
    (ctx : HierarchyMinimumCounterexampleContext G k e0 input T phi ett base C)
    (hprefixElementary :
      ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1))))
    (alpha beta : Fin k) (hne : alpha ≠ beta)
    (hmissingPrefix :
      alpha ∈ TreeMissingColors phi (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)) ∧
        beta ∈ TreeMissingColors phi (HierarchyFullTailPrefix C (HierarchyFullTailLength C - 1)))
    (z : Sum V E) (hpath : TwoColorPathComponent G phi alpha beta z)
    (sigma : PartialEdgeColoring E k)
    (hsigma : sigma = TwoColorComponentSwap G phi alpha beta z)
    (hcase :
      (0 < C.hierarchy.dividerCount ∧
        alpha ∈ TreeMissingColors phi
          (C.hierarchy.stage ⟨C.hierarchy.dividerCount, by omega⟩)) ∨
      (C.hierarchy.dividerCount = 0 ∧
        (alpha ∈ TreeMissingColors phi
            (ett.series.data.tree (Fin.last ett.rounds).castSucc) ∨
          (alpha ∈ TreeMissingColors phi
              (HierarchyStarredStage C.hierarchy (Fin.last C.hierarchy.dividerCount)) ∧
            alpha ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds) ∧
            beta ∉ TashkinovStoredColors ett.series.data (Fin.last ett.rounds)))))
    (hdisjoint :
      let va := T.vertex (HierarchyFirstMissingPosition phi T alpha)
      Disjoint (TwoColorComponent G phi alpha beta z)
        (TwoColorComponent G phi alpha beta (Sum.inl va))) :
    let H := C.hierarchy
    let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
    let Tn := ett.series.data.tree n.castSucc
    let Dn := TashkinovStoredColors ett.series.data n
    let A := HierarchyStarredStage H (Fin.last H.dividerCount)
    (if ett.series.data.kind n = some TashkinovExtensionKind.PE then
        CombinedStableColoring Tn base.closure Dn phi sigma
      else StableColoring Tn Dn phi sigma) ∧
      (∀ v ∈ TreeSequenceVertexSet A,
        MissingColors G sigma v = MissingColors G phi v) ∧
      IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 ∧
      (∀ (r : Fin (H.dividerCount + 1)) (c : Fin k),
        (c = alpha ∨ c = beta) →
        c ∈ TreeMissingColors phi (HierarchyStarredStage H r) →
        TreeColorSetClosed G phi (HierarchyStarredStage H r) {c} →
        OutsideKempeRecoloring (HierarchyStarredStage H r) phi sigma alpha beta) := by
  classical
  rcases ctx with ⟨hproper, hone, hlower, hfewer, hminimal, hlarge⟩
  let H := C.hierarchy
  let q : Fin (H.dividerCount + 1) := Fin.last H.dividerCount
  let A := HierarchyStarredStage H q
  let n : Fin (ett.rounds + 1) := Fin.last ett.rounds
  let Tn := ett.series.data.tree n.castSucc
  let a := T.vertex (HierarchyFirstMissingPosition phi T alpha)
  let b := T.vertex (HierarchyFirstMissingPosition phi T beta)
  let Ty := TreeSequencePrefix T
    (min (A.length + ((T.length - A.length) - 1)) T.length)
    (by have hA := A.positive; have hT := T.positive; omega)
    (Nat.min_le_right _ _)
  have trans := @helper_trans_125 (@V) (@E) (@G) (@e0)
  have stageChain := @helper_stageChain_136 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@trans)
  have starStage (r : Fin (H.dividerCount + 1)) :
      TreeSequenceInitialSegment (HierarchyStarredStage H r)
        (H.stage r.succ) := by
    clear * - H r
    refine Fin.cases ?_ (fun i => ?_) r
    · exact H.coreInsideFirst
    · exact H.nested i.succ
  have starChain := @helper_starChain_162 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@trans) (@stageChain)
      (@starStage)
  have hAT : TreeSequenceInitialSegment A T := by
    have hh := starStage q
    have hlast : q.succ = Fin.last (H.dividerCount + 1) := Fin.ext rfl
    simpa [hlast, H.terminalStage] using hh
  have hATy := @helper_hATy_184 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hAT)
  have hTyT : TreeSequenceInitialSegment Ty T :=
    ⟨Nat.min_le_right _ _, fun _ => rfl, fun _ => rfl⟩
  have helemA : ColoredVertexSetElementary G phi (TreeSequenceVertexSet A) := by
    intro u hu v hv hne'
    exact hprefixElementary
      (TreeSequenceInitialSegmentVertexSetSubset hATy hu)
      (TreeSequenceInitialSegmentVertexSetSubset hATy hv) hne'
  have helemStar (r : Fin (H.dividerCount + 1)) :
      ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet (HierarchyStarredStage H r)) := by
    have hsub := TreeSequenceInitialSegmentVertexSetSubset
      (starChain r q (Fin.le_last r))
    intro u hu v hv hne'
    exact helemA (hsub hu) (hsub hv) hne'
  have missingFirst := @helper_missingFirst_210 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hTyT)
  have haMissing : alpha ∈ MissingColors G phi a :=
    missingFirst alpha hmissingPrefix.1
  have hbMissing : beta ∈ MissingColors G phi b :=
    missingFirst beta hmissingPrefix.2
  have pathMissing := @helper_pathMissing_230 (@V) (@E) inferInstance inferInstance (@G) (@k) (@phi)
      (@hproper)
  have graphSwap (c d : Fin k) :
      TwoColorIncidenceGraph G phi c d = TwoColorIncidenceGraph G phi d c := by
    clear * - G phi c d
    ext x y
    cases x <;> cases y <;> simp [TwoColorIncidenceGraph, or_comm]
  have componentSwap (c d : Fin k) (z : Sum V E) :
      TwoColorComponent G phi c d z = TwoColorComponent G phi d c z := by
    unfold TwoColorComponent
    rw [graphSwap]
  have interchangeableSwap := @helper_interchangeableSwap_258 (@V) (@E) inferInstance inferInstance
      (@G) (@k) (@e0) (@phi) (@z) (@graphSwap) (@componentSwap)
  have stableRefl (B : TreeSequence G e0) (D : Finset (Fin k)) :
      StableColoring B D phi phi :=
    ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
  have hcombined : CombinedStableColoring Tn base.closure
      (TashkinovStoredColors ett.series.data n) phi phi :=
    ⟨stableRefl _ _, stableRefl _ _⟩
  have hnonPEClosed := @helper_hnonPEClosed_278 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hproper) (@hone)
      (@trans)
  have nonPEMissingClosed := @helper_nonPEMissingClosed_364 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hnonPEClosed)
  have coreChain : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind n = some TashkinovExtensionKind.PE
    · exact (base.parallel hp).2.2.some.leftSegment
    · rw [base.nonparallel hp]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have coreA : TreeSequenceInitialSegment base.core A := starChain 0 q (Fin.zero_le _)
  have TnA := trans coreChain coreA
  have closureA := @helper_closureA_384 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@coreA)
  have firstIn := @helper_firstIn_391 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@T)
      (@phi) (@trans)
  have halphaA := @helper_halphaA_419 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@alpha) (@beta)
      (@hcase) (@TnA)
  have haA : a ∈ TreeSequenceVertexSet A := firstIn A hAT alpha halphaA
  have hsame (hbA : beta ∈ TreeMissingColors phi A) :
      TwoColorComponent G phi alpha beta (Sum.inl a) =
        TwoColorComponent G phi alpha beta (Sum.inl b) := by
    have hh := ChangeLemmaBothInside G k e0 input T phi ett base C hproper hone
      hlower hfewer hminimal hprefixElementary hlarge alpha beta hne hmissingPrefix
      (fun h => (h.elim (fun hn => hn halphaA) (fun hn => hn hbA)).elim)
      ⟨haA, firstIn A hAT beta hbA⟩
    rcases hcase with ⟨hq, hm⟩ | ⟨hq, hm⟩
    · exact hh.1 ⟨hq, Or.inl hm⟩
    · apply hh.2.1
      refine ⟨hq, ?_⟩
      rcases hm with hm | hm
      · exact Or.inl hm
      · right
        apply Finset.disjoint_left.mpr
        intro c hc hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl
        · exact hm.2.1 hd
        · exact hm.2.2 hd
  have haOutside : Sum.inl a ∉ TwoColorComponent G phi alpha beta z := by
    intro ha
    exact Set.disjoint_left.mp hdisjoint ha (show Sum.inl a ∈
      TwoColorComponent G phi alpha beta (Sum.inl a) from rfl)
  have hbOutside (hbA : beta ∈ TreeMissingColors phi A) :
      Sum.inl b ∉ TwoColorComponent G phi alpha beta z := by
    intro hb
    apply Set.disjoint_left.mp hdisjoint hb
    rw [hsame hbA]
    rfl
  have missingUnique (c : Fin k) (hc : c ∈ TreeMissingColors phi A)
      (v : V) (hv : v ∈ TreeSequenceVertexSet A)
      (hvc : c ∈ MissingColors G phi v)
      (hcm : c ∈ MissingColors G phi (T.vertex (HierarchyFirstMissingPosition phi T c))) :
      v = T.vertex (HierarchyFirstMissingPosition phi T c) := by
    by_contra hn
    exact Finset.disjoint_left.mp
      (helemA hv (firstIn A hAT c hc) hn) hvc hcm
  have edgeOfVertex {v : V} {f : E}
      (hv : Sum.inl v ∈ TwoColorComponent G phi alpha beta z)
      (hinc : Incident G v f) (hc : phi f = some alpha ∨ phi f = some beta) :
      Sum.inr f ∈ TwoColorComponent G phi alpha beta z := by
    have hadj : (TwoColorIncidenceGraph G phi alpha beta).Adj
        (Sum.inr f) (Sum.inl v) := ⟨hinc, hc⟩
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hv
  exact @helper_continuation_1245 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@C) (@hprefixElementary)
      (@alpha) (@beta) (@hne) (@hmissingPrefix) (@z) (@hpath) (@sigma) (@hsigma) (@hcase)
      (@hdisjoint) (@hproper) (@hone) (@hlower) (@hfewer) (@hlarge) (@trans) (@starChain) (@hAT)
      (@helemStar) (@haMissing) (@hbMissing) (@pathMissing) (@graphSwap) (@componentSwap)
      (@interchangeableSwap) (@hcombined) (@nonPEMissingClosed) (@coreChain) (@TnA) (@closureA)
      (@firstIn) (@halphaA) (@haA) (@hsame) (@haOutside) (@hbOutside) (@missingUnique)
      (@edgeOfVertex)
end GoldbergSeymour

end
