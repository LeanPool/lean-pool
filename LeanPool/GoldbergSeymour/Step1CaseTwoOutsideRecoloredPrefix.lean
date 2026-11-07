/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.GoodHierarchy
public import LeanPool.GoldbergSeymour.GoodHierarchyReservedDisjoint
public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColors
public import LeanPool.GoldbergSeymour.OutsideKempeRecoloringStable
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.MissingColorsNonemptyOfMaximumDegree
public import LeanPool.GoldbergSeymour.HierarchyTerminalStoredColorsSubsetLast
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior

/-!
# Step1Case Two Outside Recolored Prefix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation386Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H) (alpha beta : Fin k), alpha ≠ beta →
    ∀ (a₁ b₁ a₂ b₂ a₃ b₃ : V) (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₁)
        (Sum.inl b₁)) (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₂) (Sum.inl
        b₂)) (P₃ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₃) (Sum.inl b₃)),
        TreeExitPath T phi alpha beta a₁ b₁ P₁ → TreeExitPath T phi alpha beta a₂ b₂ P₂ →
        TreeExitPath T phi alpha beta a₃ b₃ P₃ → (
    ∀ x ∈ P₁.support, x ∉ P₂.support) → (
    ∀ x ∈ P₁.support, x ∉ P₃.support) → (
    ∀ x ∈ P₂.support, x ∉ P₃.support) → TreeVertexOrder T b₁ b₂ → TreeVertexOrder T b₂ b₃ →
    ∀ (f₁ f₂ f₃ : E), f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta → f₂ ∈
        BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta → f₃ ∈ BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) beta → Incident G b₁ f₁ → Incident G b₂ f₂ → Incident G b₃ f₃ →
        Sum.inr f₁ ∈ P₁.support → Sum.inr f₂ ∈ P₂.support → Sum.inr f₃ ∈ P₃.support → b₃ ∉
        TreeSequenceVertexSet (HierarchyStarredStage H (Fin.last H.dividerCount)) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) →
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
        TreeSequenceInitialSegment Tn A → TreeSequenceInitialSegment A T →
    ∀ gamma ∈ MissingColors G phi b₃, b₃ ∈ TreeSequenceVertexSet T → gamma ≠ beta → gamma ∉
        (HierarchyStoredColorsAt H (Fin.last H.dividerCount)).biUnion (good.gamma (Fin.last
        H.dividerCount)) → (
    ∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet T) → phi f ≠ some alpha ∧ phi f ≠ some
        gamma) → (
    ∀ {z : Sym2 V} {x y : V}, x ∈ z → y ∈ z → x ≠ y → z = s(x, y)) → (
    ∀ {v : V} {f : E}, v ∉ TreeSequenceVertexSet T → Incident G v f → TreeIncidentEdge T f → f ∈
        BoundaryEdges G (TreeSequenceVertexSet T)) →
    let sigma : PartialEdgeColoring E k := OutsideTreeColorSwap T phi alpha gamma; (
    ∀ (f : E), TreeIncidentEdge T f → sigma f = phi f) → IsProperEdgeColoring G sigma ∧
        IsOneEdgeUncolored sigma e0 →
    ∃ (gamma : Fin k) (mu : PartialEdgeColoring E k) (Bminus : TreeSequence G e0) (C :
        TreeSequence G e0) (R₁ : (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a₁)
        (Sum.inl b₁)) (R₂ : (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a₂) (Sum.inl
        b₂)) (R₃ : (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a₃) (Sum.inl b₃)), gamma
        ≠ beta ∧ IsProperEdgeColoring G mu ∧ IsOneEdgeUncolored mu e0 ∧ StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (TashkinovStoredColors
        ett.series.data (Fin.last ett.rounds)) phi mu ∧ (
    ∀ (e : E), TreeIncidentEdge Bminus e → mu e = phi e) ∧ (
    ∀ v ∈ TreeSequenceVertexSet Bminus, MissingColors G mu v = MissingColors G phi v) ∧ gamma ∉
        (HierarchyStoredColorsAt H (Fin.last H.dividerCount)).biUnion (good.gamma (Fin.last
        H.dividerCount)) ∧ gamma ∈ MissingColors G phi b₃ ∧ beta ∈ MissingColors G mu b₃ ∧ mu f₃ =
        some gamma ∧ (
    ∀ v ∈ TreeSequenceVertexSet C,
    ∀ (eta : Fin k), eta ≠ gamma → eta ≠ beta → (eta ∈ MissingColors G mu v ↔ eta ∈ MissingColors
        G phi v)) ∧ TreeExitPath T mu gamma beta a₁ b₁ R₁ ∧ TreeExitPath T mu gamma beta a₂ b₂ R₂
        ∧ TreeExitPath T mu gamma beta a₃ b₃ R₃ ∧ (
    ∀ x ∈ R₁.support, x ∉ R₂.support) ∧ (
    ∀ x ∈ R₁.support, x ∉ R₃.support) ∧ (
    ∀ x ∈ R₂.support, x ∉ R₃.support) ∧ R₁.support = P₁.support ∧ R₂.support = P₂.support ∧
        R₃.support = P₃.support ∧ R₁.length = P₁.length ∧ R₂.length = P₂.length ∧ R₃.length =
        P₃.length ∧ TreeSequenceInitialSegment (HierarchyStarredStage H (Fin.last H.dividerCount))
        Bminus ∧ Bminus.length < C.length ∧ TreeSequenceInitialSegment C T ∧ C.vertex (Fin.last
        C.length) = b₃ ∧ (
    ∃ (g : E), TreeSequenceAdjoinEdge Bminus g C) ∧ f₁ ∈ BoundaryColorEdges G mu
        (TreeSequenceVertexSet C) beta ∧ f₂ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C)
        beta ∧ (
    ∀ (u₁ u₂ : V), Incident G u₁ f₁ → u₁ ∉ TreeSequenceVertexSet C → Incident G u₂ f₂ → u₂ ∉
        TreeSequenceVertexSet C → u₁ ≠ u₂) ∧ b₁ ∈ TreeSequenceVertexSet C ∧ b₂ ∈
        TreeSequenceVertexSet C ∧ b₃ ∈ TreeSequenceVertexSet C

private abbrev helperContinuation728Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H) (alpha beta : Fin k), alpha ≠ beta →
    ∀ (a₁ b₁ a₂ b₂ a₃ b₃ : V) (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₁)
        (Sum.inl b₁)) (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₂) (Sum.inl
        b₂)) (P₃ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₃) (Sum.inl b₃)),
        TreeExitPath T phi alpha beta a₁ b₁ P₁ → TreeExitPath T phi alpha beta a₂ b₂ P₂ → (
    ∀ x ∈ P₁.support, x ∉ P₂.support) → (
    ∀ x ∈ P₁.support, x ∉ P₃.support) → (
    ∀ x ∈ P₂.support, x ∉ P₃.support) →
    ∀ (f₁ f₂ f₃ : E), f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta → f₂ ∈
        BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta → f₃ ∈ BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) beta → Incident G b₁ f₁ → Incident G b₂ f₂ → Incident G b₃ f₃ →
        Sum.inr f₁ ∈ P₁.support → Sum.inr f₂ ∈ P₂.support → Sum.inr f₃ ∈ P₃.support →
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
    ∀ gamma ∈ MissingColors G phi b₃, b₃ ∈ TreeSequenceVertexSet T → gamma ≠ beta → gamma ∉
        (HierarchyStoredColorsAt H (Fin.last H.dividerCount)).biUnion (good.gamma (Fin.last
        H.dividerCount)) →
    let sigma : PartialEdgeColoring E k := OutsideTreeColorSwap T phi alpha gamma; (
    ∀ (f : E), TreeIncidentEdge T f → sigma f = phi f) → IsProperEdgeColoring G sigma ∧
        IsOneEdgeUncolored sigma e0 → (
    ∀ (W : TreeSequence G e0) (p q : PartialEdgeColoring E k), (
    ∀ (f : E), TreeIncidentEdge W f → q f = p f) →
    ∀ v ∈ TreeSequenceVertexSet W, MissingColors G q v = MissingColors G p v) → (
    ∀ v ∈ TreeSequenceVertexSet T, MissingColors G sigma v = MissingColors G phi v) → (
    ∀ {p : PartialEdgeColoring E k} {c d : Fin k} {u v : V}
        {walk : (TwoColorIncidenceGraph G p c d).Walk (Sum.inl u) (Sum.inl v)} {f : E} {x : V},
        walk.IsPath → Sum.inr f ∈ walk.support → Incident G x f → Sum.inl x ∈ walk.support) → (
    ∀ {p q : PartialEdgeColoring E k} {c d c' d' : Fin k} {u v : V} (walk :
        (TwoColorIncidenceGraph G p c d).Walk (Sum.inl u) (Sum.inl v)), TreeExitPath T p c d u v
        walk → (
    ∀ {w : V} {f : E}, Sum.inr f ∈ walk.support → Incident G w f → p f = some c ∨ p f = some d → q
        f = some c' ∨ q f = some d') → c' ∈ MissingColors G q u ∨ d' ∈ MissingColors G q u →
    ∃ (out : (TwoColorIncidenceGraph G q c' d').Walk (Sum.inl u) (Sum.inl v)), TreeExitPath T q c'
        d' u v out ∧ out.support = walk.support ∧ out.length = walk.length) →
    ∀ (Q₁ : (TwoColorIncidenceGraph G sigma gamma beta).Walk (Sum.inl a₁) (Sum.inl b₁)),
        TreeExitPath T sigma gamma beta a₁ b₁ Q₁ → Q₁.support = P₁.support → Q₁.length = P₁.length
        →
    ∀ (Q₂ : (TwoColorIncidenceGraph G sigma gamma beta).Walk (Sum.inl a₂) (Sum.inl b₂)),
        TreeExitPath T sigma gamma beta a₂ b₂ Q₂ → Q₂.support = P₂.support → Q₂.length = P₂.length
        →
    ∀ (Q₃ : (TwoColorIncidenceGraph G sigma gamma beta).Walk (Sum.inl a₃) (Sum.inl b₃)),
        TreeExitPath T sigma gamma beta a₃ b₃ Q₃ → Q₃.support = P₃.support → Q₃.length = P₃.length
        →
    ∀ (i₁ i₂ i₃ : Fin (T.length + (1 : ℕ))) (hAs : A.length < (↑i₃ : ℕ)) (hspos : (1 : ℕ) ≤ (↑i₃ :
        ℕ) - (1 : ℕ)) (hsT : (↑i₃ : ℕ) ≤ T.length),
    let Bminus : TreeSequence G e0 := TreeSequencePrefix T ((↑i₃ : ℕ) - (1 : ℕ)) hspos (
    by omega
    );
    let C : TreeSequence G e0 := TreeSequencePrefix T (↑i₃ : ℕ) (
    by omega
    ) hsT; TreeSequenceInitialSegment A Bminus → TreeSequenceInitialSegment C T →
        TreeSequenceInitialSegment Bminus T → TreeSequenceInitialSegment Tn Bminus → Bminus.length
        < C.length → C.vertex (Fin.last C.length) = b₃ → b₃ ∉ TreeSequenceVertexSet Bminus → b₁ ∈
        TreeSequenceVertexSet C → b₂ ∈ TreeSequenceVertexSet C → b₃ ∈ TreeSequenceVertexSet C → (
    ∃ (g : E), TreeSequenceAdjoinEdge Bminus g C) →
    let J : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G sigma gamma beta;
    let K : Set (V ⊕ E) := TwoColorComponent G sigma gamma beta (Sum.inl b₃); gamma ∈
        MissingColors G sigma b₃ → (
    ∀ x ∈ Q₃.support,
    ∀ (y : V ⊕ E), J.Adj x y → y ∈ Q₃.support) →
    ∃ (gamma : Fin k) (mu : PartialEdgeColoring E k) (Bminus : TreeSequence G e0) (C :
        TreeSequence G e0) (R₁ : (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a₁)
        (Sum.inl b₁)) (R₂ : (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a₂) (Sum.inl
        b₂)) (R₃ : (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a₃) (Sum.inl b₃)), gamma
        ≠ beta ∧ IsProperEdgeColoring G mu ∧ IsOneEdgeUncolored mu e0 ∧ StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (TashkinovStoredColors
        ett.series.data (Fin.last ett.rounds)) phi mu ∧ (
    ∀ (e : E), TreeIncidentEdge Bminus e → mu e = phi e) ∧ (
    ∀ v ∈ TreeSequenceVertexSet Bminus, MissingColors G mu v = MissingColors G phi v) ∧ gamma ∉
        (HierarchyStoredColorsAt H (Fin.last H.dividerCount)).biUnion (good.gamma (Fin.last
        H.dividerCount)) ∧ gamma ∈ MissingColors G phi b₃ ∧ beta ∈ MissingColors G mu b₃ ∧ mu f₃ =
        some gamma ∧ (
    ∀ v ∈ TreeSequenceVertexSet C,
    ∀ (eta : Fin k), eta ≠ gamma → eta ≠ beta → (eta ∈ MissingColors G mu v ↔ eta ∈ MissingColors
        G phi v)) ∧ TreeExitPath T mu gamma beta a₁ b₁ R₁ ∧ TreeExitPath T mu gamma beta a₂ b₂ R₂
        ∧ TreeExitPath T mu gamma beta a₃ b₃ R₃ ∧ (
    ∀ x ∈ R₁.support, x ∉ R₂.support) ∧ (
    ∀ x ∈ R₁.support, x ∉ R₃.support) ∧ (
    ∀ x ∈ R₂.support, x ∉ R₃.support) ∧ R₁.support = P₁.support ∧ R₂.support = P₂.support ∧
        R₃.support = P₃.support ∧ R₁.length = P₁.length ∧ R₂.length = P₂.length ∧ R₃.length =
        P₃.length ∧ TreeSequenceInitialSegment (HierarchyStarredStage H (Fin.last H.dividerCount))
        Bminus ∧ Bminus.length < C.length ∧ TreeSequenceInitialSegment C T ∧ C.vertex (Fin.last
        C.length) = b₃ ∧ (
    ∃ (g : E), TreeSequenceAdjoinEdge Bminus g C) ∧ f₁ ∈ BoundaryColorEdges G mu
        (TreeSequenceVertexSet C) beta ∧ f₂ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C)
        beta ∧ (
    ∀ (u₁ u₂ : V), Incident G u₁ f₁ → u₁ ∉ TreeSequenceVertexSet C → Incident G u₂ f₂ → u₂ ∉
        TreeSequenceVertexSet C → u₁ ≠ u₂) ∧ b₁ ∈ TreeSequenceVertexSet C ∧ b₂ ∈
        TreeSequenceVertexSet C ∧ b₃ ∈ TreeSequenceVertexSet C

private abbrev helperContinuation431Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi) (base : HierarchyBase ett phi) (H : TashkinovHierarchy ett base) (good :
        GoodHierarchy H) (alpha beta : Fin k), alpha ≠ beta →
    ∀ (a₁ b₁ a₂ b₂ a₃ b₃ : V) (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₁)
        (Sum.inl b₁)) (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₂) (Sum.inl
        b₂)) (P₃ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl a₃) (Sum.inl b₃)),
        TreeExitPath T phi alpha beta a₁ b₁ P₁ → TreeExitPath T phi alpha beta a₂ b₂ P₂ →
        TreeExitPath T phi alpha beta a₃ b₃ P₃ → (
    ∀ x ∈ P₁.support, x ∉ P₂.support) → (
    ∀ x ∈ P₁.support, x ∉ P₃.support) → (
    ∀ x ∈ P₂.support, x ∉ P₃.support) → TreeVertexOrder T b₁ b₂ → TreeVertexOrder T b₂ b₃ →
    ∀ (f₁ f₂ f₃ : E), f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta → f₂ ∈
        BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta → f₃ ∈ BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) beta → Incident G b₁ f₁ → Incident G b₂ f₂ → Incident G b₃ f₃ →
        Sum.inr f₁ ∈ P₁.support → Sum.inr f₂ ∈ P₂.support → Sum.inr f₃ ∈ P₃.support → b₃ ∉
        TreeSequenceVertexSet (HierarchyStarredStage H (Fin.last H.dividerCount)) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) →
    let A : TreeSequence G e0 := HierarchyStarredStage H (Fin.last H.dividerCount);
    let Tn : TreeSequence G e0 := ett.series.data.tree (Fin.last ett.rounds).castSucc;
        TreeSequenceInitialSegment Tn A → TreeSequenceInitialSegment A T →
    ∀ gamma ∈ MissingColors G phi b₃, b₃ ∈ TreeSequenceVertexSet T → gamma ≠ beta → gamma ∉
        (HierarchyStoredColorsAt H (Fin.last H.dividerCount)).biUnion (good.gamma (Fin.last
        H.dividerCount)) → (
    ∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet T) → phi f ≠ some alpha ∧ phi f ≠ some
        gamma) →
    let sigma : PartialEdgeColoring E k := OutsideTreeColorSwap T phi alpha gamma; (
    ∀ (f : E), TreeIncidentEdge T f → sigma f = phi f) → IsProperEdgeColoring G sigma ∧
        IsOneEdgeUncolored sigma e0 → (
    ∀ (W : TreeSequence G e0) (p q : PartialEdgeColoring E k), (
    ∀ (f : E), TreeIncidentEdge W f → q f = p f) →
    ∀ v ∈ TreeSequenceVertexSet W, MissingColors G q v = MissingColors G p v) → (
    ∀ v ∈ TreeSequenceVertexSet T, MissingColors G sigma v = MissingColors G phi v) → (
    ∀ (p : PartialEdgeColoring E k) (v : V) (c : Fin k), c ∈ MissingColors G p v ↔
    ∀ (f : E), Incident G v f → p f ≠ some c) → (
    ∀ {p : PartialEdgeColoring E k} {c d : Fin k} {u v : V}
        {walk : (TwoColorIncidenceGraph G p c d).Walk (Sum.inl u) (Sum.inl v)} {f : E} {x : V},
        walk.IsPath → Sum.inr f ∈ walk.support → Incident G x f → Sum.inl x ∈ walk.support) → (
    ∀ {u v : V} {walk : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)},
        TreeExitPath T phi alpha beta u v walk →
    ∀ {f : E}, Sum.inr f ∈ walk.support → TreeIncidentEdge T f → f ∈ BoundaryEdges G
        (TreeSequenceVertexSet T)) → (
    ∀ {p q : PartialEdgeColoring E k} {c d c' d' : Fin k} {u v : V} (walk :
        (TwoColorIncidenceGraph G p c d).Walk (Sum.inl u) (Sum.inl v)), TreeExitPath T p c d u v
        walk → (
    ∀ {w : V} {f : E}, Sum.inr f ∈ walk.support → Incident G w f → p f = some c ∨ p f = some d → q
        f = some c' ∨ q f = some d') → c' ∈ MissingColors G q u ∨ d' ∈ MissingColors G q u →
    ∃ (out : (TwoColorIncidenceGraph G q c' d').Walk (Sum.inl u) (Sum.inl v)), TreeExitPath T q c'
        d' u v out ∧ out.support = walk.support ∧ out.length = walk.length) → (
    ∀ u ∉ TreeSequenceVertexSet T, alpha ∈ MissingColors G phi u ∨ beta ∈ MissingColors G phi u →
        gamma ∈ MissingColors G sigma u ∨ beta ∈ MissingColors G sigma u) →
    ∃ (gamma : Fin k) (mu : PartialEdgeColoring E k) (Bminus : TreeSequence G e0) (C :
        TreeSequence G e0) (R₁ : (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a₁)
        (Sum.inl b₁)) (R₂ : (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a₂) (Sum.inl
        b₂)) (R₃ : (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl a₃) (Sum.inl b₃)), gamma
        ≠ beta ∧ IsProperEdgeColoring G mu ∧ IsOneEdgeUncolored mu e0 ∧ StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc) (TashkinovStoredColors
        ett.series.data (Fin.last ett.rounds)) phi mu ∧ (
    ∀ (e : E), TreeIncidentEdge Bminus e → mu e = phi e) ∧ (
    ∀ v ∈ TreeSequenceVertexSet Bminus, MissingColors G mu v = MissingColors G phi v) ∧ gamma ∉
        (HierarchyStoredColorsAt H (Fin.last H.dividerCount)).biUnion (good.gamma (Fin.last
        H.dividerCount)) ∧ gamma ∈ MissingColors G phi b₃ ∧ beta ∈ MissingColors G mu b₃ ∧ mu f₃ =
        some gamma ∧ (
    ∀ v ∈ TreeSequenceVertexSet C,
    ∀ (eta : Fin k), eta ≠ gamma → eta ≠ beta → (eta ∈ MissingColors G mu v ↔ eta ∈ MissingColors
        G phi v)) ∧ TreeExitPath T mu gamma beta a₁ b₁ R₁ ∧ TreeExitPath T mu gamma beta a₂ b₂ R₂
        ∧ TreeExitPath T mu gamma beta a₃ b₃ R₃ ∧ (
    ∀ x ∈ R₁.support, x ∉ R₂.support) ∧ (
    ∀ x ∈ R₁.support, x ∉ R₃.support) ∧ (
    ∀ x ∈ R₂.support, x ∉ R₃.support) ∧ R₁.support = P₁.support ∧ R₂.support = P₂.support ∧
        R₃.support = P₃.support ∧ R₁.length = P₁.length ∧ R₂.length = P₂.length ∧ R₃.length =
        P₃.length ∧ TreeSequenceInitialSegment (HierarchyStarredStage H (Fin.last H.dividerCount))
        Bminus ∧ Bminus.length < C.length ∧ TreeSequenceInitialSegment C T ∧ C.vertex (Fin.last
        C.length) = b₃ ∧ (
    ∃ (g : E), TreeSequenceAdjoinEdge Bminus g C) ∧ f₁ ∈ BoundaryColorEdges G mu
        (TreeSequenceVertexSet C) beta ∧ f₂ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C)
        beta ∧ (
    ∀ (u₁ u₂ : V), Incident G u₁ f₁ → u₁ ∉ TreeSequenceVertexSet C → Incident G u₂ f₂ → u₂ ∉
        TreeSequenceVertexSet C → u₁ ≠ u₂) ∧ b₁ ∈ TreeSequenceVertexSet C ∧ b₂ ∈
        TreeSequenceVertexSet C ∧ b₃ ∈ TreeSequenceVertexSet C

private theorem helper_continuation_728.{u_1, u_2} :
    helperContinuation728Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good alpha beta hne a₁ b₁ a₂ b₂ a₃ b₃ P₁ P₂ P₃
      hP₁ hP₂ hpaths₁₂ hpaths₁₃ hpaths₂₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ hif₁ hif₂ hif₃ hPf₁ hPf₂ hPf₃ A Tn
      gamma hgamma hbT hgb hgReserved sigma sigma_fixed sigma_properties missing_of_fixed
      sigma_missing incident_vertex_mem_support transfer_exit Q₁ hQ₁ hQs₁ hQl₁ Q₂ hQ₂ hQs₂ hQl₂
      Q₃ hQ₃ hQs₃ hQl₃ i₁ i₂ i₃ hAs hspos hsT Bminus C hAB hCT hBT hTnB hBClen hbC hbNotB hb₁C
      hb₂C hb₃C hadjoin J K hgSigma support_closed
  have hspan : ∀ x, x ∈ K ↔ x ∈ Q₃.support := by
    intro x
    constructor
    · intro hx
      have reach : J.Reachable (Sum.inl b₃) x := by
        change J.connectedComponentMk x = J.connectedComponentMk (Sum.inl b₃) at hx
        exact (SimpleGraph.ConnectedComponent.eq.mp hx).symm
      exact reach.mem_subgraphVerts
        (H := (⊤ : J.Subgraph).induce {z | z ∈ Q₃.support})
        (fun z hz y hzy => ⟨hz, support_closed z hz y hzy, hzy⟩)
        (by simp)
    · intro hx
      obtain ⟨i, hi, _⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
        (show x ∈ Q₃.reverse.support by simpa using hx)
      change J.connectedComponentMk x = J.connectedComponentMk (Sum.inl b₃)
      rw [← hi]
      exact (SimpleGraph.ConnectedComponent.sound (Q₃.reverse.take i).reachable).symm
  have hKtree : ∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ K ↔ v = b₃ := by
    intro v hv
    exact (hspan (Sum.inl v)).trans (hQ₃.2.2.2.2.2 v hv)
  have hKedge : ∀ f, TreeIncidentEdge Bminus f → Sum.inr f ∉ K := by
    intro f ⟨v, hv, hvf⟩ hf
    have hvs := incident_vertex_mem_support hQ₃.1 ((hspan _).mp hf) hvf
    have hvT := TreeSequenceInitialSegmentVertexSetSubset hBT hv
    have heq := (hQ₃.2.2.2.2.2 v hvT).mp hvs
    exact hbNotB (heq ▸ hv)
  let mu := TwoColorComponentSwap G sigma gamma beta (Sum.inl b₃)
  have mu_proper : IsProperEdgeColoring G mu :=
    TwoColorComponentSwapProper G sigma gamma beta hgb sigma_properties.1 _
  have mu_one : IsOneEdgeUncolored mu e0 := by
    constructor
    · simp [mu, TwoColorComponentSwap, sigma_properties.2.1]
    · intro f hfe
      obtain ⟨c, hc⟩ := sigma_properties.2.2 f hfe
      by_cases hf : Sum.inr f ∈ K
      · by_cases ha : sigma f = some gamma
        · exact ⟨beta, by simp [mu, TwoColorComponentSwap, K, hf, ha]⟩
        · by_cases hb : sigma f = some beta
          · exact ⟨gamma, by simp [mu, TwoColorComponentSwap, K, hf, hb, hgb.symm]⟩
          · refine ⟨c, ?_⟩
            change (if Sum.inr f ∈ K then
              if sigma f = some gamma then some beta
              else if sigma f = some beta then some gamma else sigma f
              else sigma f) = some c
            rw [ite_eq_left hf, ite_eq_right ha, ite_eq_right hb]
            exact hc
      · exact ⟨c, by simp [mu, TwoColorComponentSwap, K, hf, hc]⟩
  have mu_fixed : ∀ f, TreeIncidentEdge Bminus f → mu f = phi f := by
    intro f hf
    have hnot := hKedge f hf
    have hfT : TreeIncidentEdge T f := by
      obtain ⟨v, hv, hvf⟩ := hf
      exact ⟨v, TreeSequenceInitialSegmentVertexSetSubset hBT hv, hvf⟩
    simpa [mu, TwoColorComponentSwap, K, hnot] using sigma_fixed f hfT
  have mu_missing := missing_of_fixed Bminus phi mu mu_fixed
  have mu_stable : StableColoring Tn
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi mu := by
    constructor
    · intro f ⟨v, hv, hvf⟩ _
      exact mu_fixed f ⟨v, TreeSequenceInitialSegmentVertexSetSubset hTnB hv, hvf⟩
    · intro v hv
      exact mu_missing v (TreeSequenceInitialSegmentVertexSetSubset hTnB hv)
  have swap_missing := TwoColorComponentSwapMissingBehavior G sigma gamma beta hgb
    sigma_properties.1 (Sum.inl b₃)
  have hbMissing : beta ∈ MissingColors G mu b₃ :=
    swap_missing.2.1 b₃ (show Sum.inl b₃ ∈ K from rfl) hgSigma
  have hsf₃ : sigma f₃ = some beta :=
    (sigma_fixed f₃ ⟨b₃, hbT, hif₃⟩).trans (Finset.mem_filter.mp hf₃).2
  have hmf₃ : mu f₃ = some gamma := by
    have hfK : Sum.inr f₃ ∈ K := (hspan _).mpr (by simpa [hQs₃] using hPf₃)
    simp [mu, TwoColorComponentSwap, K, hfK, hsf₃, hgb.symm]
  have missing_other : ∀ v ∈ TreeSequenceVertexSet C, ∀ eta,
      eta ≠ gamma → eta ≠ beta →
      (eta ∈ MissingColors G mu v ↔ eta ∈ MissingColors G phi v) := by
    intro v hv eta heg heb
    have hother := swap_missing.2.2.2 v eta heg heb
    simpa only [sigma_missing v (TreeSequenceInitialSegmentVertexSetSubset hCT hv)] using hother
  have second_transfer :
    ∀ {u v : V} (walk : J.Walk (Sum.inl u) (Sum.inl v)), TreeExitPath T sigma gamma beta u v walk
        →
    ∃ out : (TwoColorIncidenceGraph G mu gamma beta).Walk (Sum.inl u) (Sum.inl v), TreeExitPath T
        mu gamma beta u v out ∧ out.support = walk.support ∧ out.length = walk.length := by
    intro u v walk hexit
    have hm : gamma ∈ MissingColors G mu u ∨ beta ∈ MissingColors G mu u := by
      by_cases hu : Sum.inl u ∈ K
      · rcases hexit.2.2.2.2.1 with hg | hb
        · exact Or.inr (swap_missing.2.1 u hu hg)
        · exact Or.inl (swap_missing.2.2.1 u hu hb)
      · have hmiss : MissingColors G mu u = MissingColors G sigma u := swap_missing.1 u hu
        rw [hmiss]
        exact hexit.2.2.2.2.1
    apply transfer_exit walk hexit _ hm
    intro w f _ _ hc
    by_cases hf : Sum.inr f ∈ K
    · rcases hc with hg | hb
      · exact Or.inr (by simp [mu, TwoColorComponentSwap, K, hf, hg])
      · exact Or.inl (by simp [mu, TwoColorComponentSwap, K, hf, hb, hgb.symm])
    · simpa [mu, TwoColorComponentSwap, K, hf] using hc
  obtain ⟨R₁, hR₁, hRs₁, hRl₁⟩ := second_transfer Q₁ hQ₁
  obtain ⟨R₂, hR₂, hRs₂, hRl₂⟩ := second_transfer Q₂ hQ₂
  obtain ⟨R₃, hR₃, hRs₃, hRl₃⟩ := second_transfer Q₃ hQ₃
  have sigma_beta : ∀ f, phi f = some beta → sigma f = some beta := by
    intro f hf
    by_cases ht : TreeIncidentEdge T f
    · exact (sigma_fixed f ht).trans hf
    · simp [sigma, OutsideTreeColorSwap, ht, hf, hne.symm, hgb.symm]
  have hf₁K : Sum.inr f₁ ∉ K := by
    intro hfK
    have hfP₃ : Sum.inr f₁ ∈ P₃.support := by
      simpa only [hQs₃] using (hspan _).mp hfK
    exact hpaths₁₃ _ hPf₁ hfP₃
  have hf₂K : Sum.inr f₂ ∉ K := by
    intro hfK
    have hfP₃ : Sum.inr f₂ ∈ P₃.support := by
      simpa only [hQs₃] using (hspan _).mp hfK
    exact hpaths₂₃ _ hPf₂ hfP₃
  have boundary_C : ∀ {f : E} {b : V},
      f ∈ BoundaryEdges G (TreeSequenceVertexSet T) → Incident G b f →
      b ∈ TreeSequenceVertexSet C → f ∈ BoundaryEdges G (TreeSequenceVertexSet C) := by
    intro f b hf hbf hb
    obtain ⟨x, hx, y, hy, he⟩ := by simpa [BoundaryEdges] using hf
    have hbx : b = x := by
      have hbxy : b = x ∨ b = y := by simpa [Incident, he] using hbf
      rcases hbxy with h | h
      · exact h
      · exact False.elim (hy (h ▸ TreeSequenceInitialSegmentVertexSetSubset hCT hb))
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨b, hb, y, fun hyC => hy (TreeSequenceInitialSegmentVertexSetSubset hCT hyC),
      by simpa only [hbx] using he⟩
  have hf₁C : f₁ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C) beta := by
    refine Finset.mem_filter.mpr ⟨boundary_C (Finset.mem_filter.mp hf₁).1 hif₁ hb₁C, ?_⟩
    have hc := sigma_beta f₁ (Finset.mem_filter.mp hf₁).2
    simpa [mu, TwoColorComponentSwap, K, hf₁K] using hc
  have hf₂C : f₂ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C) beta := by
    refine Finset.mem_filter.mpr ⟨boundary_C (Finset.mem_filter.mp hf₂).1 hif₂ hb₂C, ?_⟩
    have hc := sigma_beta f₂ (Finset.mem_filter.mp hf₂).2
    simpa [mu, TwoColorComponentSwap, K, hf₂K] using hc
  have hendpoints : ∀ u₁ u₂, Incident G u₁ f₁ → u₁ ∉ TreeSequenceVertexSet C →
      Incident G u₂ f₂ → u₂ ∉ TreeSequenceVertexSet C → u₁ ≠ u₂ := by
    intro u₁ u₂ hu₁ _ hu₂ _ heq
    have hs₁ := incident_vertex_mem_support hP₁.1 hPf₁ hu₁
    have hs₂ := incident_vertex_mem_support hP₂.1 hPf₂ hu₂
    exact hpaths₁₂ _ hs₁ (heq ▸ hs₂)
  refine ⟨gamma, mu, Bminus, C, R₁, R₂, R₃, hgb, mu_proper, mu_one,
    mu_stable, mu_fixed, mu_missing, hgReserved, hgamma, hbMissing, hmf₃,
    missing_other, hR₁, hR₂, hR₃, ?_, ?_, ?_,
    hRs₁.trans hQs₁, hRs₂.trans hQs₂, hRs₃.trans hQs₃,
    hRl₁.trans hQl₁, hRl₂.trans hQl₂, hRl₃.trans hQl₃,
    hAB, hBClen, hCT, hbC, hadjoin, hf₁C, hf₂C, hendpoints, hb₁C, hb₂C, hb₃C⟩
  · simpa only [hRs₁, hRs₂, hQs₁, hQs₂] using hpaths₁₂
  · simpa only [hRs₁, hRs₃, hQs₁, hQs₃] using hpaths₁₃
  · simpa only [hRs₂, hRs₃, hQs₂, hQs₃] using hpaths₂₃

private theorem helper_continuation_431.{u_1, u_2} :
    helperContinuation431Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good alpha beta hne a₁ b₁ a₂ b₂ a₃ b₃ P₁ P₂ P₃
      hP₁ hP₂ hP₃ hpaths₁₂ hpaths₁₃ hpaths₂₃ horder₁₂ horder₂₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ hif₁ hif₂
      hif₃ hPf₁ hPf₂ hPf₃ houtside segment_trans A Tn hTnA hAT gamma hgamma hbT hgb hgReserved
      no_boundary sigma sigma_fixed sigma_properties missing_of_fixed sigma_missing missing_iff
      incident_vertex_mem_support path_boundary transfer_exit sigma_remote_missing
  have first_transfer :
    ∀ {u v : V} (walk : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)),
        TreeExitPath T phi alpha beta u v walk →
    ∃ out : (TwoColorIncidenceGraph G sigma gamma beta).Walk (Sum.inl u) (Sum.inl v), TreeExitPath
        T sigma gamma beta u v out ∧ out.support = walk.support ∧ out.length = walk.length := by
    intro u v walk hexit
    apply transfer_exit walk hexit _
      (sigma_remote_missing u hexit.2.2.1 hexit.2.2.2.2.1)
    intro w f hf hwf hc
    rcases hc with ha | hb
    · have ht : ¬ TreeIncidentEdge T f := fun ht =>
        (no_boundary (path_boundary hexit hf ht)).1 ha
      exact Or.inl (by simp [sigma, OutsideTreeColorSwap, ht, ha])
    · by_cases ht : TreeIncidentEdge T f
      · exact Or.inr ((sigma_fixed f ht).trans hb)
      · exact Or.inr (by simp [sigma, OutsideTreeColorSwap, ht, hb, hne.symm, hgb.symm])
  obtain ⟨Q₁, hQ₁, hQs₁, hQl₁⟩ := first_transfer P₁ hP₁
  obtain ⟨Q₂, hQ₂, hQs₂, hQl₂⟩ := first_transfer P₂ hP₂
  obtain ⟨Q₃, hQ₃, hQs₃, hQl₃⟩ := first_transfer P₃ hP₃
  obtain ⟨i₁, i₂, hi₁, hi₂, hi₁₂⟩ := horder₁₂
  obtain ⟨j₂, i₃, hj₂, hi₃, hi₂₃⟩ := horder₂₃
  have hj : j₂ = i₂ := T.vertex_injective (hj₂.trans hi₂.symm)
  subst j₂
  have hAs : A.length < i₃.val := by
    by_contra h
    have hiA : i₃.val ≤ A.length := by omega
    let r : Fin (A.length + 1) := ⟨i₃.val, by omega⟩
    have hr : Fin.castLE (Nat.succ_le_succ hAT.1) r = i₃ := Fin.ext rfl
    have hv : A.vertex r = b₃ := by rw [← hAT.2.1 r, hr, hi₃]
    apply houtside
    change b₃ ∈ TreeSequenceVertexSet A
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨r, hv⟩
  have hspos : 1 ≤ i₃.val - 1 := by have := A.positive; omega
  have hsT : i₃.val ≤ T.length := Nat.le_of_lt_succ i₃.isLt
  let Bminus := TreeSequencePrefix T (i₃.val - 1) hspos (by omega)
  let C := TreeSequencePrefix T i₃.val (by omega) hsT
  have hAB : TreeSequenceInitialSegment A Bminus := by
    refine ⟨by simpa [Bminus, TreeSequencePrefix] using (show A.length ≤ i₃.val - 1 by omega),
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
  have hTnB := segment_trans hTnA hAB
  have hBClen : Bminus.length < C.length := by
    simp only [Bminus, C, TreeSequencePrefix]
    omega
  have hbC : C.vertex (Fin.last C.length) = b₃ := by
    change T.vertex ⟨i₃.val, _⟩ = b₃
    exact hi₃
  have hbNotB : b₃ ∉ TreeSequenceVertexSet Bminus := by
    intro hb
    obtain ⟨r, hr⟩ := by
      simpa only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] using hb
    have heq := T.vertex_injective ((hBT.2.1 r).trans (hr.trans hi₃.symm))
    have hv := congrArg Fin.val heq
    have hrl := r.isLt
    change r.val < i₃.val - 1 + 1 at hrl
    simp only [Fin.val_castLE] at hv
    omega
  have hb₁C : b₁ ∈ TreeSequenceVertexSet C := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i₁.val, by change i₁.val < i₃.val + 1; omega⟩, hi₁⟩
  have hb₂C : b₂ ∈ TreeSequenceVertexSet C := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨i₂.val, by change i₂.val < i₃.val + 1; omega⟩, hi₂⟩
  have hb₃C : b₃ ∈ TreeSequenceVertexSet C := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨Fin.last C.length, hbC⟩
  have hadjoin : ∃ g, TreeSequenceAdjoinEdge Bminus g C := by
    have hlen : C.length = Bminus.length + 1 := by
      simp only [Bminus, C, TreeSequencePrefix]
      omega
    exact ⟨C.edge (Fin.cast hlen.symm (Fin.last Bminus.length)), hlen, hBC, rfl⟩
  let J := TwoColorIncidenceGraph G sigma gamma beta
  let K := TwoColorComponent G sigma gamma beta (Sum.inl b₃)
  have hgSigma : gamma ∈ MissingColors G sigma b₃ := by
    rw [sigma_missing b₃ hbT]
    exact hgamma
  have leaf : ∀ v, gamma ∈ MissingColors G sigma v ∨ beta ∈ MissingColors G sigma v →
      (J.neighborSet (Sum.inl v)).Subsingleton := by
    intro v hm x hx y hy
    cases x with
    | inl w => exact False.elim hx
    | inr e =>
      cases y with
      | inl w => exact False.elim hy
      | inr f =>
        have he : Incident G v e ∧ (sigma e = some gamma ∨ sigma e = some beta) := hx
        have hf : Incident G v f ∧ (sigma f = some gamma ∨ sigma f = some beta) := hy
        have hsame : e = f := by
          by_contra hef
          rcases hm with hm | hm
          · have hec := he.2.resolve_left ((missing_iff sigma v gamma).mp hm e he.1)
            have hfc := hf.2.resolve_left ((missing_iff sigma v gamma).mp hm f hf.1)
            exact sigma_properties.1 hef ⟨v, he.1, hf.1⟩ hec hfc
          · have hec := he.2.resolve_right ((missing_iff sigma v beta).mp hm e he.1)
            have hfc := hf.2.resolve_right ((missing_iff sigma v beta).mp hm f hf.1)
            exact sigma_properties.1 hef ⟨v, he.1, hf.1⟩ hec hfc
        exact congrArg Sum.inr hsame
  have support_closed : ∀ x, x ∈ Q₃.support → ∀ y, J.Adj x y → y ∈ Q₃.support := by
    intro x hx y hxy
    obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    by_cases hn0 : n = 0
    · subst n
      have hx0 : x = Sum.inl a₃ := by simpa using hn.symm
      have ha : J.Adj (Sum.inl a₃) (Q₃.getVert 1) := by
        simpa using Q₃.adj_getVert_succ (i := 0) (by have := hQ₃.2.1; omega)
      have heq : y = Q₃.getVert 1 := (leaf a₃ hQ₃.2.2.2.2.1)
        (by simpa [hx0] using hxy) ha
      rw [heq]
      exact Q₃.getVert_mem_support _
    by_cases hlast : n = Q₃.length
    · have hx1 : x = Sum.inl b₃ := by
        rw [← hn, hQ₃.1.getVert_eq_end_iff hnle]
        exact hlast
      have ha : J.Adj (Sum.inl b₃) (Q₃.getVert (Q₃.length - 1)) := by
        simpa [show Q₃.length - 1 + 1 = Q₃.length by have := hQ₃.2.1; omega] using
          (Q₃.adj_getVert_succ (show Q₃.length - 1 < Q₃.length by
            have := hQ₃.2.1; omega)).symm
      have heq : y = Q₃.getVert (Q₃.length - 1) := (leaf b₃ (Or.inl hgSigma))
        (by simpa [hx1] using hxy) ha
      rw [heq]
      exact Q₃.getVert_mem_support _
    have hl : J.Adj (Q₃.getVert n) (Q₃.getVert (n - 1)) := by
      rw [← show n - 1 + 1 = n by omega]
      exact (Q₃.adj_getVert_succ (by omega)).symm
    have hr := Q₃.adj_getVert_succ (show n < Q₃.length by omega)
    by_contra hyout
    rw [← hn] at hxy
    have hnl : Q₃.getVert (n - 1) ≠ y := by
      intro h
      exact hyout (h ▸ Q₃.getVert_mem_support (n - 1))
    have hnr : Q₃.getVert (n + 1) ≠ y := by
      intro h
      exact hyout (h ▸ Q₃.getVert_mem_support (n + 1))
    have hnp : Q₃.getVert (n - 1) ≠ Q₃.getVert (n + 1) := by
      intro h
      have hi := hQ₃.1.getVert_injOn
        (show n - 1 ≤ Q₃.length by omega) (show n + 1 ≤ Q₃.length by omega) h
      omega
    let : Fintype (J.neighborSet (Q₃.getVert n)) := Fintype.ofFinite _
    have three : 3 ≤ J.degree (Q₃.getVert n) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let s : Finset _ := {y, Q₃.getVert (n - 1), Q₃.getVert (n + 1)}
      have hs : s ⊆ J.neighborFinset (Q₃.getVert n) := by
        intro t ht
        simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset] using hxy
        · simpa [SimpleGraph.mem_neighborFinset] using hl
        · simpa [SimpleGraph.mem_neighborFinset] using hr
      have hc : 3 ≤ s.card := by
        simp [s, hnp, hnl.symm, hnr.symm]
      exact hc.trans (Finset.card_le_card hs)
    have upper : J.degree (Q₃.getVert n) ≤ 2 :=
      TwoColorIncidenceDegreeAtMostTwo G sigma gamma beta sigma_properties.1 _
    omega
  exact @helper_continuation_728 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H) (@good) (@alpha)
      (@beta) (@hne) (@a₁) (@b₁) (@a₂) (@b₂) (@a₃) (@b₃) (@P₁) (@P₂) (@P₃) (@hP₁) (@hP₂)
      (@hpaths₁₂) (@hpaths₁₃) (@hpaths₂₃) (@f₁) (@f₂) (@f₃) (@hf₁) (@hf₂) (@hf₃) (@hif₁) (@hif₂)
      (@hif₃) (@hPf₁) (@hPf₂) (@hPf₃) (@gamma) (@hgamma) (@hbT) (@hgb) (@hgReserved)
      (@sigma_fixed) (@sigma_properties) (@missing_of_fixed) (@sigma_missing)
      (@incident_vertex_mem_support) (@transfer_exit) (@Q₁) (@hQ₁) (@hQs₁) (@hQl₁) (@Q₂) (@hQ₂)
      (@hQs₂) (@hQl₂) (@Q₃) (@hQ₃) (@hQs₃) (@hQl₃) (@i₁) (@i₂) (@i₃) (@hAs) (@hspos) (@hsT)
      (@hAB) (@hCT) (@hBT) (@hTnB) (@hBClen) (@hbC) (@hbNotB) (@hb₁C) (@hb₂C) (@hb₃C) (@hadjoin)
      (@hgSigma) (@support_closed)
private theorem helper_continuation_386.{u_1, u_2} :
    helperContinuation386Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett base H good alpha beta hne a₁ b₁ a₂ b₂ a₃ b₃ P₁ P₂ P₃
      hP₁ hP₂ hP₃ hpaths₁₂ hpaths₁₃ hpaths₂₃ horder₁₂ horder₂₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ hif₁ hif₂
      hif₃ hPf₁ hPf₂ hPf₃ houtside segment_trans A Tn hTnA hAT gamma hgamma hbT hgb hgReserved
      no_boundary ends_eq_of_mem boundary_of_outside sigma sigma_fixed sigma_properties
  have missing_of_fixed : ∀ (W : TreeSequence G e0)
      (p q : PartialEdgeColoring E k),
      (∀ f, TreeIncidentEdge W f → q f = p f) →
      ∀ v ∈ TreeSequenceVertexSet W, MissingColors G q v = MissingColors G p v := by
    intro W p q hfixed v hv
    unfold MissingColors PresentColors
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨f, hvf, hfc⟩
    · exact ⟨f, hvf, (hfixed f ⟨v, hv, hvf⟩).symm.trans hfc⟩
    · exact ⟨f, hvf, (hfixed f ⟨v, hv, hvf⟩).trans hfc⟩
  have sigma_missing := missing_of_fixed T phi sigma sigma_fixed
  have missing_iff : ∀ (p : PartialEdgeColoring E k) (v : V) (c : Fin k),
      c ∈ MissingColors G p v ↔ ∀ f, Incident G v f → p f ≠ some c := by
    intro p v c
    simp [MissingColors, PresentColors]
  have incident_vertex_mem_support :
      ∀ {p : PartialEdgeColoring E k} {c d : Fin k} {u v : V}
        {walk : (TwoColorIncidenceGraph G p c d).Walk (Sum.inl u) (Sum.inl v)}
        {f : E} {x : V}, walk.IsPath → Sum.inr f ∈ walk.support →
        Incident G x f → Sum.inl x ∈ walk.support := by
    intro p c d u v walk f x hp hf hxf
    obtain ⟨n, hn, hnle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
    have hnpos : 0 < n := by
      by_contra h
      have hnzero : n = 0 := by omega
      rw [hnzero] at hn
      simp at hn
    have hnlt : n < walk.length := by
      by_contra h
      have hneq : n = walk.length := by omega
      rw [hneq] at hn
      simp at hn
    have hprev := walk.adj_getVert_succ (i := n - 1) (by omega)
    have hnext := walk.adj_getVert_succ (i := n) hnlt
    rw [show n - 1 + 1 = n by omega, hn] at hprev
    rw [hn] at hnext
    cases hpreveq : walk.getVert (n - 1) with
    | inr g =>
      rw [hpreveq] at hprev
      simp [TwoColorIncidenceGraph] at hprev
    | inl y =>
      rw [hpreveq] at hprev
      cases hnexteq : walk.getVert (n + 1) with
      | inr g =>
        rw [hnexteq] at hnext
        simp [TwoColorIncidenceGraph] at hnext
      | inl z =>
        rw [hnexteq] at hnext
        have hyz : y ≠ z := by
          intro hyz
          have hverts : walk.getVert (n - 1) = walk.getVert (n + 1) := by
            rw [hpreveq, hnexteq, hyz]
          have hidx := hp.getVert_injOn
            (show n - 1 ≤ walk.length by omega)
            (show n + 1 ≤ walk.length by omega) hverts
          omega
        have hends : G.ends f = s(y, z) := ends_eq_of_mem hprev.1 hnext.1 hyz
        rw [Incident, hends] at hxf
        have hx : x = y ∨ x = z := by simpa using hxf
        rcases hx with rfl | rfl
        · rw [← hpreveq]
          exact walk.getVert_mem_support _
        · rw [← hnexteq]
          exact walk.getVert_mem_support _
  have path_boundary : ∀ {u v : V}
      {walk : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl u) (Sum.inl v)},
      TreeExitPath T phi alpha beta u v walk → ∀ {f : E},
      Sum.inr f ∈ walk.support → TreeIncidentEdge T f →
      f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
    intro u v walk hexit f hf ⟨x, hx, hxf⟩
    have unique : ∀ y, Incident G y f → y ∈ TreeSequenceVertexSet T → y = v := by
      intro y hyf hy
      exact (hexit.2.2.2.2.2 y hy).mp (incident_vertex_mem_support hexit.1 hf hyf)
    obtain ⟨y, z, he⟩ : ∃ y z, G.ends f = s(y, z) := by
      generalize G.ends f = s
      induction s using Sym2.inductionOn with
      | _ y z => exact ⟨y, z, rfl⟩
    have hyf : Incident G y f := by simp [Incident, he]
    have hzf : Incident G z f := by simp [Incident, he]
    have hyz : y ≠ z := by intro h; exact G.loopless f z (by simpa [h] using he)
    have hxends : x = y ∨ x = z := by simpa [Incident, he] using hxf
    rcases hxends with rfl | rfl
    · apply boundary_of_outside (v := z) (f := f) _ hzf ⟨x, hx, hyf⟩
      intro hz
      exact hyz ((unique x hyf hx).trans (unique z hzf hz).symm)
    · apply boundary_of_outside (v := y) (f := f) _ hyf ⟨x, hx, hzf⟩
      intro hy
      exact hyz ((unique y hyf hy).trans (unique x hzf hx).symm)
  have transfer_exit :
    ∀ {p q : PartialEdgeColoring E k} {c d c' d' : Fin k} {u v : V} (walk :
        (TwoColorIncidenceGraph G p c d).Walk (Sum.inl u) (Sum.inl v)), TreeExitPath T p c d u v
        walk → (
    ∀ {w : V} {f : E}, Sum.inr f ∈ walk.support → Incident G w f → (p f = some c ∨ p f = some d) →
        q f = some c' ∨ q f = some d') → (c' ∈ MissingColors G q u ∨ d' ∈ MissingColors G q u) →
    ∃ out : (TwoColorIncidenceGraph G q c' d').Walk (Sum.inl u) (Sum.inl v), TreeExitPath T q c'
        d' u v out ∧ out.support = walk.support ∧ out.length = walk.length := by
    intro p q c d c' d' u v walk hexit hcolor hmissing
    have hedges : ∀ z, z ∈ walk.edges → z ∈ (TwoColorIncidenceGraph G q c' d').edgeSet := by
      intro z hz
      induction z using Sym2.inductionOn with
      | _ x y =>
        have hadj := (SimpleGraph.mem_edgeSet _).mp (walk.edges_subset_edgeSet hz)
        have hx := walk.fst_mem_support_of_mem_edges hz
        have hy := walk.snd_mem_support_of_mem_edges hz
        apply (SimpleGraph.mem_edgeSet _).mpr
        cases x with
        | inl w =>
          cases y with
          | inl v => exact False.elim hadj
          | inr f => exact ⟨hadj.1, hcolor hy hadj.1 hadj.2⟩
        | inr f =>
          cases y with
          | inr g => exact False.elim hadj
          | inl w => exact ⟨hadj.1, hcolor hx hadj.1 hadj.2⟩
    let out := walk.transfer (TwoColorIncidenceGraph G q c' d') hedges
    refine ⟨out, ?_, by simp [out], by simp [out]⟩
    refine ⟨hexit.1.transfer hedges, by simpa [out] using hexit.2.1,
      hexit.2.2.1, hexit.2.2.2.1, hmissing, ?_⟩
    intro w hw
    simpa [out] using hexit.2.2.2.2.2 w hw
  have sigma_remote_missing : ∀ u, u ∉ TreeSequenceVertexSet T →
      (alpha ∈ MissingColors G phi u ∨ beta ∈ MissingColors G phi u) →
      gamma ∈ MissingColors G sigma u ∨ beta ∈ MissingColors G sigma u := by
    intro u hu hm
    rcases hm with hm | hm
    · left
      apply (missing_iff sigma u gamma).mpr
      intro f huf hsf
      by_cases ht : TreeIncidentEdge T f
      · exact (no_boundary (boundary_of_outside hu huf ht)).2
          ((sigma_fixed f ht).symm.trans hsf)
      · have hnot : phi f ≠ some alpha := (missing_iff phi u alpha).mp hm f huf
        by_cases hg : phi f = some gamma
        · have hag : alpha ≠ gamma := by intro h; exact hnot (by simpa [h] using hg)
          have hbad : alpha = gamma := by
            simpa [sigma, OutsideTreeColorSwap, ht, hnot, hg, hag.symm] using hsf
          exact hag hbad
        · have hbad : phi f = some gamma := by
            simp [sigma, OutsideTreeColorSwap, ht, hnot, hg] at hsf
          exact hg hbad
    · right
      apply (missing_iff sigma u beta).mpr
      intro f huf hsf
      have hnot := (missing_iff phi u beta).mp hm f huf
      by_cases ht : TreeIncidentEdge T f
      · exact hnot ((sigma_fixed f ht).symm.trans hsf)
      · by_cases ha : phi f = some alpha
        · exact hgb (by simpa [sigma, OutsideTreeColorSwap, ht, ha] using hsf)
        · by_cases hg : phi f = some gamma
          · have hag : gamma ≠ alpha := by intro h; exact ha (by simpa [h] using hg)
            exact hne (by simpa [sigma, OutsideTreeColorSwap, ht, ha, hg, hag] using hsf)
          · exact hnot (by simpa [sigma, OutsideTreeColorSwap, ht, ha, hg] using hsf)
  exact @helper_continuation_431 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H) (@good) (@alpha)
      (@beta) (@hne) (@a₁) (@b₁) (@a₂) (@b₂) (@a₃) (@b₃) (@P₁) (@P₂) (@P₃) (@hP₁) (@hP₂) (@hP₃)
      (@hpaths₁₂) (@hpaths₁₃) (@hpaths₂₃) (@horder₁₂) (@horder₂₃) (@f₁) (@f₂) (@f₃) (@hf₁) (@hf₂)
      (@hf₃) (@hif₁) (@hif₂) (@hif₃) (@hPf₁) (@hPf₂) (@hPf₃) (@houtside) (@segment_trans) (@hTnA)
      (@hAT) (@gamma) (@hgamma) (@hbT) (@hgb) (@hgReserved) (@no_boundary) (@sigma_fixed)
      (@sigma_properties) (@missing_of_fixed) (@sigma_missing) (@missing_iff)
      (@incident_vertex_mem_support) (@path_boundary) (@transfer_exit) (@sigma_remote_missing)
private theorem helper_sigma_properties_1696.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (phi : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k e0
        input T phi), IsProperEdgeColoring G phi → IsOneEdgeUncolored phi e0 →
    ∀ (base : HierarchyBase ett phi) (_ : TashkinovHierarchy ett base) (alpha gamma : Fin k), (
    ∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet T) → phi f ≠ some alpha ∧ phi f ≠ some
        gamma) → (
    ∀ {v : V} {f : E}, v ∉ TreeSequenceVertexSet T → Incident G v f → TreeIncidentEdge T f → f ∈
        BoundaryEdges G (TreeSequenceVertexSet T)) →
    let sigma : PartialEdgeColoring E k := OutsideTreeColorSwap T phi alpha gamma;
        IsProperEdgeColoring G sigma ∧ IsOneEdgeUncolored sigma e0 := by
  classical
  intro V E _ _ _ _ G k e0 input T phi ett hproper hone base H alpha gamma no_boundary
      boundary_of_outside sigma
  by_cases hag : alpha = gamma
  · have hs : sigma = phi := by
      funext f
      by_cases ht : TreeIncidentEdge T f
      · simp [sigma, OutsideTreeColorSwap, ht]
      · by_cases ha : phi f = some alpha <;>
          simp [sigma, OutsideTreeColorSwap, ht, ← hag, ha]
    simpa only [hs] using And.intro hproper hone
  · let J := TwoColorIncidenceGraph G phi alpha gamma
    let S : Set (Sum V E) := {z | match z with
      | Sum.inl v => v ∉ TreeSequenceVertexSet T
      | Sum.inr f => ¬ TreeIncidentEdge T f}
    have hstep : ∀ x, x ∈ S → ∀ y, J.Adj x y → y ∈ S := by
      intro x hx y hxy
      cases x with
      | inl v =>
        cases y with
        | inl w => exact False.elim hxy
        | inr f =>
          intro ht
          have hb := no_boundary (boundary_of_outside hx hxy.1 ht)
          exact hxy.2.elim hb.1 hb.2
      | inr f =>
        cases y with
        | inr g => exact False.elim hxy
        | inl v => exact fun hv => hx ⟨v, hv, hxy.1⟩
    let roots : Finset (Sum V E) := Finset.univ.filter fun z =>
      match z with
      | Sum.inl v => v ∉ TreeSequenceVertexSet T
      | Sum.inr _ => False
    have hout : ∀ z ∈ roots, ∀ v : V,
        Sum.inl v ∈ TwoColorComponent G phi alpha gamma z →
        v ∉ TreeSequenceVertexSet T := by
      intro z hz v hv
      have hzS : z ∈ S := by
        cases z with
        | inl w => simpa [roots, S] using hz
        | inr _ => simp [roots] at hz
      have hr : J.Reachable z (Sum.inl v) := by
        change J.connectedComponentMk (Sum.inl v) = J.connectedComponentMk z at hv
        exact (SimpleGraph.ConnectedComponent.eq.mp hv).symm
      exact hr.mem_subgraphVerts
        (H := (⊤ : J.Subgraph).induce S)
        (fun x hx y hxy => ⟨hx, hstep x hx y hxy, hxy⟩) hzS
    have selected : ∀ {f : E}, ¬ TreeIncidentEdge T f →
        (phi f = some alpha ∨ phi f = some gamma) →
        ∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha gamma z := by
      intro f ht hc
      obtain ⟨v, hv⟩ : ∃ v, Incident G v f := by
        change ∃ v, v ∈ G.ends f
        generalize G.ends f = z
        induction z using Sym2.inductionOn with
        | _ x y => exact ⟨x, by simp⟩
      have hvout : v ∉ TreeSequenceVertexSet T := fun h => ht ⟨v, h, hv⟩
      refine ⟨Sum.inl v, by simp [roots, hvout], ?_⟩
      have hadj : J.Adj (Sum.inl v) (Sum.inr f) := ⟨hv, hc⟩
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
    have selected_not_tree : ∀ {f : E},
        (∃ z ∈ roots, Sum.inr f ∈ TwoColorComponent G phi alpha gamma z) →
        (phi f = some alpha ∨ phi f = some gamma) → ¬ TreeIncidentEdge T f := by
      intro f ⟨z, hz, hzf⟩ hc ⟨v, hv, hvf⟩
      have hadj : J.Adj (Sum.inl v) (Sum.inr f) := ⟨hvf, hc⟩
      have hvc : Sum.inl v ∈ TwoColorComponent G phi alpha gamma z :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hzf
      exact hout z hz v hvc hv
    have hrec : OutsideKempeRecoloring T phi sigma alpha gamma := by
      refine ⟨hag, roots, hout, ?_⟩
      intro f
      by_cases ht : TreeIncidentEdge T f
      · by_cases hr : ∃ z ∈ roots,
            Sum.inr f ∈ TwoColorComponent G phi alpha gamma z
        · have ha : phi f ≠ some alpha := fun ha =>
            selected_not_tree hr (Or.inl ha) ht
          have hg : phi f ≠ some gamma := fun hg =>
            selected_not_tree hr (Or.inr hg) ht
          simp [sigma, OutsideTreeColorSwap, ht, hr, ha, hg]
        · simp [sigma, OutsideTreeColorSwap, ht, hr]
      · by_cases hr : ∃ z ∈ roots,
            Sum.inr f ∈ TwoColorComponent G phi alpha gamma z
        · simp [sigma, OutsideTreeColorSwap, ht, hr]
        · have ha : phi f ≠ some alpha := fun ha => hr (selected ht (Or.inl ha))
          have hg : phi f ≠ some gamma := fun hg => hr (selected ht (Or.inr hg))
          simp [sigma, OutsideTreeColorSwap, ht, hr, ha, hg]
    have hs := OutsideKempeRecoloringStable G e0 T ∅ phi sigma alpha gamma
      hproper hone hrec
    exact ⟨hs.1, hs.2.1⟩

lemma Step1CaseTwoOutsideRecoloredPrefix {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (phi : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T phi)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (base : HierarchyBase ett phi)
    (H : TashkinovHierarchy ett base) (good : GoodHierarchy H)
    (hterminal : TreeColorSetMinusClosed G phi T
      ((HierarchyTerminalStoredColors H).biUnion
        (good.gamma (Fin.last H.dividerCount))))
    (hElementary : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T))
    (alpha beta : Fin k) (_ : alpha ∈ TreeMissingColors phi T)
    (hclosed : TreeColorSetClosed G phi T {alpha})
    (hne : alpha ≠ beta) (hbeta : beta ∉ TreeMissingColors phi T)
    (a₁ b₁ a₂ b₂ a₃ b₃ : V)
    (P₁ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₁) (Sum.inl b₁))
    (P₂ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₂) (Sum.inl b₂))
    (P₃ : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl a₃) (Sum.inl b₃))
    (hP₁ : TreeExitPath T phi alpha beta a₁ b₁ P₁)
    (hP₂ : TreeExitPath T phi alpha beta a₂ b₂ P₂)
    (hP₃ : TreeExitPath T phi alpha beta a₃ b₃ P₃)
    (hpaths₁₂ : ∀ x, x ∈ P₁.support → x ∉ P₂.support)
    (hpaths₁₃ : ∀ x, x ∈ P₁.support → x ∉ P₃.support)
    (hpaths₂₃ : ∀ x, x ∈ P₂.support → x ∉ P₃.support)
    (_ : a₁ ≠ a₂) (_ : a₁ ≠ a₃) (_ : a₂ ≠ a₃)
    (_ : b₁ ≠ b₂) (_ : b₁ ≠ b₃) (_ : b₂ ≠ b₃)
    (horder₁₂ : TreeVertexOrder T b₁ b₂)
    (horder₂₃ : TreeVertexOrder T b₂ b₃)
    (f₁ f₂ f₃ : E)
    (hf₁ : f₁ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₂ : f₂ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hf₃ : f₃ ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) beta)
    (hif₁ : Incident G b₁ f₁) (hif₂ : Incident G b₂ f₂)
    (hif₃ : Incident G b₃ f₃)
    (hPf₁ : Sum.inr f₁ ∈ P₁.support)
    (hPf₂ : Sum.inr f₂ ∈ P₂.support)
    (hPf₃ : Sum.inr f₃ ∈ P₃.support)
    (houtside : b₃ ∉ TreeSequenceVertexSet
      (HierarchyStarredStage H (Fin.last H.dividerCount))) :
    ∃ (gamma : Fin k) (mu : PartialEdgeColoring E k)
      (Bminus C : TreeSequence G e0)
      (R₁ : (TwoColorIncidenceGraph G mu gamma beta).Walk
        (Sum.inl a₁) (Sum.inl b₁))
      (R₂ : (TwoColorIncidenceGraph G mu gamma beta).Walk
        (Sum.inl a₂) (Sum.inl b₂))
      (R₃ : (TwoColorIncidenceGraph G mu gamma beta).Walk
        (Sum.inl a₃) (Sum.inl b₃)),
      gamma ≠ beta ∧
      IsProperEdgeColoring G mu ∧ IsOneEdgeUncolored mu e0 ∧
      StableColoring
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)
        (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
        phi mu ∧
      (∀ e, TreeIncidentEdge Bminus e → mu e = phi e) ∧
      (∀ v, v ∈ TreeSequenceVertexSet Bminus →
        MissingColors G mu v = MissingColors G phi v) ∧
      gamma ∉ (HierarchyStoredColorsAt H
        (Fin.last H.dividerCount)).biUnion
          (good.gamma (Fin.last H.dividerCount)) ∧
      gamma ∈ MissingColors G phi b₃ ∧
      beta ∈ MissingColors G mu b₃ ∧
      mu f₃ = some gamma ∧
      (∀ v, v ∈ TreeSequenceVertexSet C → ∀ eta,
        eta ≠ gamma → eta ≠ beta →
        (eta ∈ MissingColors G mu v ↔ eta ∈ MissingColors G phi v)) ∧
      TreeExitPath T mu gamma beta a₁ b₁ R₁ ∧
      TreeExitPath T mu gamma beta a₂ b₂ R₂ ∧
      TreeExitPath T mu gamma beta a₃ b₃ R₃ ∧
      (∀ x, x ∈ R₁.support → x ∉ R₂.support) ∧
      (∀ x, x ∈ R₁.support → x ∉ R₃.support) ∧
      (∀ x, x ∈ R₂.support → x ∉ R₃.support) ∧
      R₁.support = P₁.support ∧ R₂.support = P₂.support ∧
      R₃.support = P₃.support ∧
      R₁.length = P₁.length ∧ R₂.length = P₂.length ∧
      R₃.length = P₃.length ∧
      TreeSequenceInitialSegment
        (HierarchyStarredStage H (Fin.last H.dividerCount)) Bminus ∧
      Bminus.length < C.length ∧ TreeSequenceInitialSegment C T ∧
      C.vertex (Fin.last C.length) = b₃ ∧
      (∃ g, TreeSequenceAdjoinEdge Bminus g C) ∧
      f₁ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C) beta ∧
      f₂ ∈ BoundaryColorEdges G mu (TreeSequenceVertexSet C) beta ∧
      (∀ u₁ u₂, Incident G u₁ f₁ →
        u₁ ∉ TreeSequenceVertexSet C → Incident G u₂ f₂ →
        u₂ ∉ TreeSequenceVertexSet C → u₁ ≠ u₂) ∧
      b₁ ∈ TreeSequenceVertexSet C ∧
      b₂ ∈ TreeSequenceVertexSet C ∧
      b₃ ∈ TreeSequenceVertexSet C := by
  classical
  have segment_trans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    refine ⟨hAB.1.trans hBC.1, ?_, ?_⟩
    · intro i
      exact (hBC.2.1 (Fin.castLE (Nat.succ_le_succ hAB.1) i)).trans
        (hAB.2.1 i)
    · intro i
      exact (hBC.2.2 (Fin.castLE hAB.1 i)).trans (hAB.2.2 i)
  have stage_segment : ∀ (i j : Fin (H.dividerCount + 2)), i ≤ j →
      TreeSequenceInitialSegment (H.stage i) (H.stage j) := by
    intro i j hij
    have aux : ∀ n (hn : n < H.dividerCount + 2), i.val ≤ n →
        TreeSequenceInitialSegment (H.stage i) (H.stage ⟨n, hn⟩) := by
      intro n
      induction n with
      | zero =>
          intro hn hi
          have heq : i = ⟨0, hn⟩ := by
            apply Fin.ext
            change i.val = 0
            omega
          rw [heq]
          exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
      | succ n ih =>
          intro hn hi
          by_cases heq : i.val = n + 1
          · have heq' : i = ⟨n + 1, hn⟩ := Fin.ext heq
            rw [heq']
            exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
          · exact segment_trans (ih (by omega) (by omega))
              (H.nested ⟨n, by omega⟩)
    exact aux j.val j.isLt hij
  let A := HierarchyStarredStage H (Fin.last H.dividerCount)
  let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
  have hTncore : TreeSequenceInitialSegment Tn base.core := by
    by_cases hp : ett.series.data.kind (Fin.last ett.rounds) =
        some TashkinovExtensionKind.PE
    · obtain ⟨_, _, ⟨u⟩⟩ := base.parallel hp
      exact u.leftSegment
    · rw [base.nonparallel hp]
      exact ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have hTnA : TreeSequenceInitialSegment Tn A := by
    by_cases hz : H.dividerCount = 0
    · have hl : Fin.last H.dividerCount = (0 : Fin (H.dividerCount + 1)) :=
        Fin.ext (by simp [hz])
      simpa [A, hl, HierarchyStarredStage] using hTncore
    · let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
      have hl : Fin.last H.dividerCount = i.succ := Fin.ext (by simp [i]; omega)
      have hs : A = H.stage i.succ.castSucc := by
        simp [A, hl, HierarchyStarredStage]
      have hh := stage_segment (0 : Fin (H.dividerCount + 2))
        i.succ.castSucc (by simp)
      simpa only [H.baseStage, ← hs] using hh
  have hAT : TreeSequenceInitialSegment A T := by
    by_cases hz : H.dividerCount = 0
    · have hl : Fin.last H.dividerCount = (0 : Fin (H.dividerCount + 1)) :=
        Fin.ext (by simp [hz])
      have ht : (1 : Fin (H.dividerCount + 2)) =
          Fin.last (H.dividerCount + 1) := Fin.ext (by simp [hz])
      simpa [A, hl, HierarchyStarredStage, ht, H.terminalStage] using H.coreInsideFirst
    · let i : Fin H.dividerCount := ⟨H.dividerCount - 1, by omega⟩
      have hl : Fin.last H.dividerCount = i.succ := Fin.ext (by simp [i]; omega)
      have hs : A = H.stage i.succ.castSucc := by
        simp [A, hl, HierarchyStarredStage]
      have hh := stage_segment i.succ.castSucc (Fin.last (H.dividerCount + 1))
        (by change i.val + 1 ≤ H.dividerCount + 1; omega)
      simpa only [H.terminalStage, ← hs] using hh
  have hdegree : MaximumDegree G + 1 ≤ k := by
    have hinit := ett.series.certified 0
    cases hinit with
    | initial triple => exact triple.2.2.1
  obtain ⟨gamma, hgamma⟩ := MissingColorsNonemptyOfMaximumDegree G phi hdegree b₃
  have hbT : b₃ ∈ TreeSequenceVertexSet T := hP₃.2.2.2.1
  have hgT : gamma ∈ TreeMissingColors phi T := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨b₃, hbT, hgamma⟩
  have hgb : gamma ≠ beta := by
    intro h
    exact hbeta (h ▸ hgT)
  have hgReserved : gamma ∉ (HierarchyStoredColorsAt H
      (Fin.last H.dividerCount)).biUnion (good.gamma (Fin.last H.dividerCount)) := by
    intro hg
    obtain ⟨eta, heta, hge⟩ := Finset.mem_biUnion.mp hg
    have hgm := (GoodHierarchyReservedDisjoint good (Fin.last H.dividerCount)).1
      eta heta hge
    obtain ⟨v, hvA, hgv⟩ := Finset.mem_biUnion.mp hgm
    have hvT := TreeSequenceInitialSegmentVertexSetSubset hAT hvA
    have hvb : v ≠ b₃ := by
      intro h
      exact houtside (h ▸ hvA)
    exact (Finset.disjoint_left.mp (hElementary hvT hbT hvb)) hgv hgamma
  have hgTerminal : gamma ∉ (HierarchyTerminalStoredColors H).biUnion
      (good.gamma (Fin.last H.dividerCount)) := by
    intro hg
    obtain ⟨eta, heta, hge⟩ := Finset.mem_biUnion.mp hg
    exact hgReserved (Finset.mem_biUnion.mpr ⟨eta,
      (HierarchyTerminalStoredColorsSubsetLast H).1 heta, hge⟩)
  have no_boundary : ∀ {f : E}, f ∈ BoundaryEdges G (TreeSequenceVertexSet T) →
      phi f ≠ some alpha ∧ phi f ≠ some gamma := by
    intro f hf
    constructor
    · intro hc
      have hm : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha :=
        Finset.mem_filter.mpr ⟨hf, hc⟩
      rw [hclosed alpha (by simp)] at hm
      exact Finset.notMem_empty _ hm
    · intro hc
      have hm : f ∈ BoundaryColorEdges G phi (TreeSequenceVertexSet T) gamma :=
        Finset.mem_filter.mpr ⟨hf, hc⟩
      rw [hterminal gamma (Finset.mem_sdiff.mpr ⟨hgT, hgTerminal⟩)] at hm
      exact Finset.notMem_empty _ hm
  have ends_eq_of_mem : ∀ {z : Sym2 V} {x y : V},
      x ∈ z → y ∈ z → x ≠ y → z = s(x, y) := by
    intro z x y hx hy hxy
    induction z using Sym2.inductionOn with
    | _ a b =>
      simp only [Sym2.mem_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        simp_all []
  have boundary_of_outside : ∀ {v : V} {f : E},
      v ∉ TreeSequenceVertexSet T → Incident G v f → TreeIncidentEdge T f →
      f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
    intro v f hv hvf ⟨w, hw, hwf⟩
    have hwv : w ≠ v := by intro h; exact hv (h ▸ hw)
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hw, v, hv, ends_eq_of_mem hwf hvf hwv⟩
  let sigma := OutsideTreeColorSwap T phi alpha gamma
  have sigma_fixed : ∀ f, TreeIncidentEdge T f → sigma f = phi f := by
    intro f hf
    simp [sigma, OutsideTreeColorSwap, hf]
  have sigma_properties := @helper_sigma_properties_1696 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@hproper) (@hone)
      (@base) (@H) (@alpha) (@gamma) (@no_boundary) (@boundary_of_outside)
  exact @helper_continuation_386 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@phi) (@ett) (@base) (@H) (@good) (@alpha)
      (@beta) (@hne) (@a₁) (@b₁) (@a₂) (@b₂) (@a₃) (@b₃) (@P₁) (@P₂) (@P₃) (@hP₁) (@hP₂) (@hP₃)
      (@hpaths₁₂) (@hpaths₁₃) (@hpaths₂₃) (@horder₁₂) (@horder₂₃) (@f₁) (@f₂) (@f₃) (@hf₁) (@hf₂)
      (@hf₃) (@hif₁) (@hif₂) (@hif₃) (@hPf₁) (@hPf₂) (@hPf₃) (@houtside) (@segment_trans) (@hTnA)
      (@hAT) (@gamma) (@hgamma) (@hbT) (@hgb) (@hgReserved) (@no_boundary) (@ends_eq_of_mem)
      (@boundary_of_outside) (@sigma_fixed) (@sigma_properties)
end GoldbergSeymour

end
