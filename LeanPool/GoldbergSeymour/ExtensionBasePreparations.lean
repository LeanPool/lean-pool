/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

import all LeanPool.GoldbergSeymour.ExtensionBaseAuxiliary

public import LeanPool.GoldbergSeymour.ExtensionBaseAuxiliary

/-!
# Preparatory lemmas for the extension base

Part of Wesley Pegden’s Trellis formalization of the Goldberg–Seymour theorem,
commit 88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. These lemmas establish the
base cases used by the extension construction.
-/

@[expose] public section

namespace GoldbergSeymour.ExtensionBaseProof

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch880Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal → (
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (0 : ℕ) < (↑i : ℕ) → TreeSequenceInitialSegment
        (ett.series.data.tree i.castSucc) (ett.series.data.tree i.succ)) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
        IsProperEdgeColoring G rho1 → IsOneEdgeUncolored rho1 e0 → StableColoringBeforeVertex T v
        hvFinal (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho1 →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = v →
    ∀ (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        jSlot.castSucc.succ = jSlot.succ.castSucc → TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) → (
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore T v hvFinal) → (
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho1 S seed) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ; (0 : ℕ) < (↑jSlot : ℕ) →
    ∃ (TjPrime : TreeSequence G e0), TashkinovClosure rho1 seed TjPrime ∧
        ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime) ∧
    let awayMissing : Finset (Fin k) := ((TreeSequenceVertexSet TjPrime).erase v).biUnion fun (x :
        V) ↦ MissingColors G rho1 x; (awayMissing ∩ supportColors : Finset (Fin k)).Nonempty ∨
        (awayMissing ∩ supportColors : Finset (Fin k)) = ∅

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch1756Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (sigma : PartialEdgeColoring E k),
    ∀ (computedIndex18 : Fin ett.rounds), computedIndex18 = (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) →
    ∀ (hqTerminal : (↑computedIndex18 : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈
        TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤
        (↑computedIndex18 : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett
        v hvFinal),
    ∀ (computedIndex23 : Fin ett.rounds), computedIndex23 = (⟨ETTFirstAppearanceIndex ett v
        hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds) → (↑computedIndex23 : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal
        → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree ((computedIndex23).succ).castSucc)) (p0 : ℕ)
        (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree ((computedIndex23).succ).castSucc).length +
        (1 : ℕ))) (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
        (hterminalPositionBound : (↑terminalPosition : ℕ) ≤ (ett.series.data.tree
        ((computedIndex23).succ).castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree
        ((computedIndex23).succ).castSucc) (↑terminalPosition : ℕ) hterminalPositionPositive
        hterminalPositionBound; ((computedIndex23).castSucc).succ =
        ((computedIndex23).succ).castSucc → TreeSequenceInitialSegment seed (ett.series.data.tree
        ((computedIndex23).succ).castSucc) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    ∀ (TjPrime : TreeSequence G e0), indices0 (Fin.last p0) = computedIndex18 →
    ∀ (u : V) (b : Fin (p0 + (1 : ℕ))) (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u p0
        indices0 b), u ∉ TreeSequenceVertexSet (ett.series.data.tree
        ((computedIndex23).succ).castSucc) →
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
        StableColoringBeforeVertex (ett.series.data.tree ((computedIndex23).succ).castSucc) v
        hterminalJ (TashkinovStoredColors ett.series.data (computedIndex23).castSucc)
        (ett.series.data.coloring (computedIndex23).castSucc) (traceB.coloring (Fin.last
        traceB.steps)) → IsProperEdgeColoring G rho2 → IsOneEdgeUncolored rho2 e0 →
    ∀ (_ : Fin (TjPrime.length + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree
        ((computedIndex23).castSucc).castSucc; ( (0 : ℕ) < (↑computedIndex23 : ℕ) →
        TreeSequenceInitialSegment Tprevious (ett.series.data.tree
        ((computedIndex23).succ).castSucc)) → ( (0 : ℕ) < (↑computedIndex23 : ℕ) →
        Tprevious.length < seed.length) → ( (0 : ℕ) < (↑computedIndex23 : ℕ) →
        TreeSequenceInitialSegment Tprevious seed) →
    let Tj0 : TreeSequence G e0 := ett.series.data.tree ((computedIndex23).succ).castSucc;
    ∀ (C : TreeSequence G e0), TashkinovAugmentationSequence rho2 seed C → ColoredVertexSetClosed
        G rho2 (TreeSequenceVertexSet C) → (
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore (ett.series.data.tree
        ((computedIndex23).succ).castSucc) v hterminalJ) → (
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        (computedIndex23).castSucc) S seed → TashkinovAugmentationSequence rho2 S seed) → u ∈
        TreeSequenceVertexSet C → TreeSequenceVertexSet Tj0 ⊂ TreeSequenceVertexSet C → (0 : ℕ) <
        (↑computedIndex23 : ℕ) → False

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperHclaim45Package6912Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds), v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal
        ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (indices0 : Fin
        (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
        IsProperEdgeColoring G rho1 → IsOneEdgeUncolored rho1 e0 → (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) → seed.vertex
        (Fin.last seed.length) = v → TreeSequenceInitialSegment (ett.series.data.tree
        jSlot.succ.castSucc) (ett.series.data.tree q.succ.castSucc) →
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0), TashkinovClosure rho1 seed TjPrime →
        ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime) →
        TreeSequenceInitialSegment seed TjPrime → StableColoringBeforeVertex (ett.series.data.tree
        jSlot.succ.castSucc) v hterminalJ (TashkinovStoredColors ett.series.data jSlot.castSucc)
        (ett.series.data.coloring jSlot.castSucc) rho1 → (
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, (MissingColors G rho1 x ∩ supportColors :
        Finset (Fin k)) = ∅) →
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ))); gamma ∈ supportColors → delta ∈
        supportColors → gamma ≠ delta → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → rho1
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) → delta ∉
        TreeMissingColors (ett.series.data.coloring jSlot.castSucc) (ett.series.data.tree
        jSlot.succ.castSucc) → v ∈ TreeSequenceVertexSet seed →
    ∀ (fN : E), delta ∈ MissingColors G rho1 v →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (a : V ⊕ E) (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)), componentPath.IsPath →
        {z : V ⊕ E | z ∈ componentPath.support} = C → x ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet TjPrime →
    ∀ (u : V) (exitPath : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl
        u)), exitPath.IsPath → (2 : ℕ) ≤ exitPath.length → (
    ∀ y ∈ exitPath.support, y ∈ componentPath.support) → (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet
        TjPrime, Sum.inl w ∈ exitPath.support ↔ w = u) → (
    ∃ g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)
        ∪ TreeSequenceVertexSet TjPrime) gamma, Incident G u g ∧ Sum.inr g ∈ exitPath.support) →
        ¬Incident G u fN → u ∈ TreeSequenceVertexSet TjPrime → u ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) → MaximumDegree G + (1 : ℕ) ≤ k →
    ∀ beta ∈ MissingColors G rho1 u, beta ∉ supportColors → TashkinovAugmentationSequence
        (ett.series.data.coloring jSlot.castSucc) seed (ett.series.data.tree jSlot.succ.castSucc)
        →
    ∀ (z : V) (hz : z ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
        (zPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition = z → seed.length ≤
        (↑zPosition : ℕ) → ((seed.length < (↑zPosition : ℕ) ∧ beta ∈ MissingColors G rho1 z ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → (↑r : ℕ) < (↑zPosition : ℕ) → beta ∉ MissingColors G rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).vertex r)) ∨ zPosition = Fin.last (ett.series.data.tree
        jSlot.succ.castSucc).length ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → beta ∉ MissingColors G rho1 ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) →
        (
    ∀ w ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z hz, beta ∉ MissingColors
        G rho1 w) → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → (↑a :
        ℕ) < (↑zPosition : ℕ) → rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) ≠ some
        beta) → ( (0 : ℕ) < p0 →
    ∃ (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (_ : u ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) (exitPath : (TwoColorIncidenceGraph G rho1 gamma
        delta).Walk (Sum.inl x) (Sum.inl u)), exitPath.IsPath ∧ (2 : ℕ) ≤ exitPath.length ∧ (
    ∀ y ∈ exitPath.support, y ∈ componentPath.support) ∧ (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet
        TjPrime, Sum.inl w ∈ exitPath.support ↔ w = u) ∧ (
    ∃ g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)
        ∪ TreeSequenceVertexSet TjPrime) gamma, Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
        ¬Incident G u fN ∧
    ∀ beta ∈ MissingColors G rho1 u,
    ∃ (z : V) (hz : z ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
        (zPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition = z ∧ seed.length ≤
        (↑zPosition : ℕ) ∧ ((seed.length < (↑zPosition : ℕ) ∧ beta ∈ MissingColors G rho1 z ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → (↑r : ℕ) < (↑zPosition : ℕ) → beta ∉ MissingColors G rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).vertex r)) ∨ zPosition = Fin.last (ett.series.data.tree
        jSlot.succ.castSucc).length ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → beta ∉ MissingColors G rho1 ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) ∧
        (
    ∀ w ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z hz, beta ∉ MissingColors
        G rho1 w) ∧ (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → (↑a :
        ℕ) < (↑zPosition : ℕ) → rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) ≠ some
        beta) ∧
    ∃ (rho3 : PartialEdgeColoring E k), IsProperEdgeColoring G rho3 ∧ IsOneEdgeUncolored rho3 e0 ∧
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho3 ∧ (
    ∀ v ∈ ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z hz ∪ ({ z } : Finset
        V) ∪ (TreeVerticesBefore TjPrime u huPrime ∪ ({ u } : Finset V))).erase u).erase z,
        MissingColors G rho3 v = MissingColors G rho1 v) ∧ (
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) ∧ (↑a :
        ℕ) < (↑zPosition : ℕ) ∧ (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → rho3 f = rho1 f) ∧ (
        beta ∈ MissingColors G rho1 z → delta ∈ MissingColors G rho3 z) ∧ ( z ∈ TreeVerticesBefore
        TjPrime u huPrime → MissingColors G rho3 z = MissingColors G rho1 z) ∧ gammaFirst ∈
        MissingColors G rho3 u) → ( p0 = (0 : ℕ) → gammaFirst = gamma) →
    ∃ (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime) (_ : u0 ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) (exitPath0 : (TwoColorIncidenceGraph G rho1 gamma
        delta).Walk (Sum.inl x) (Sum.inl u0)), exitPath0.IsPath ∧ (2 : ℕ) ≤ exitPath0.length ∧ (
    ∀ y ∈ exitPath0.support, y ∈ componentPath.support) ∧ (
    ∀ y ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet
        TjPrime, Sum.inl y ∈ exitPath0.support ↔ y = u0) ∧ (
    ∃ g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)
        ∪ TreeSequenceVertexSet TjPrime) gamma, Incident G u0 g ∧ Sum.inr g ∈ exitPath0.support) ∧
        ¬Incident G u0 fN ∧
    ∃ beta0 ∈ MissingColors G rho1 u0, beta0 ∉ supportColors ∧
    ∃ (z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
        (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition0 = z0 ∧ seed.length ≤
        (↑zPosition0 : ℕ) ∧ ((seed.length < (↑zPosition0 : ℕ) ∧ beta0 ∈ MissingColors G rho1 z0 ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → (↑r : ℕ) < (↑zPosition0 : ℕ) → beta0 ∉ MissingColors G rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).vertex r)) ∨ zPosition0 = Fin.last (ett.series.data.tree
        jSlot.succ.castSucc).length ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → beta0 ∉ MissingColors G rho1 ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) ∧
        (
    ∀ y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0, beta0 ∉
        MissingColors G rho1 y) ∧ (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → (↑a :
        ℕ) < (↑zPosition0 : ℕ) → rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) ≠ some
        beta0) ∧
    ∃ (rho3 : PartialEdgeColoring E k), IsProperEdgeColoring G rho3 ∧ IsOneEdgeUncolored rho3 e0 ∧
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho3 ∧ (
    ∀ y ∈ ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 ∪ ({ z0 } :
        Finset V) ∪ (TreeVerticesBefore TjPrime u0 huPrime0 ∪ ({ u0 } : Finset V))).erase
        u0).erase z0, MissingColors G rho3 y = MissingColors G rho1 y) ∧ (
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) ∧ (↑a :
        ℕ) < (↑zPosition0 : ℕ) ∧ (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u0 ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → rho3 f = rho1 f) ∧ (
        beta0 ∈ MissingColors G rho1 z0 → delta ∈ MissingColors G rho3 z0) ∧ ( z0 ∈
        TreeVerticesBefore TjPrime u0 huPrime0 → MissingColors G rho3 z0 = MissingColors G rho1
        z0) ∧ gammaFirst ∈ MissingColors G rho3 u0

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperCaseContinuation11664Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k) (sigma :
        PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by
     have := GoldbergSeymour.TreeSequence.positive T
     omega
    ⟩ : Fin ett.rounds); (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (indices0 : Fin
        (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (hseedTj : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)),
        seed.vertex (Fin.last seed.length) = v → TreeSequenceInitialSegment (ett.series.data.tree
        jSlot.succ.castSucc) (ett.series.data.tree q.succ.castSucc) → (
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore T v hvFinal) → (
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore T v hvFinal) → (
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho1 S seed) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    ∀ (TjPrime : TreeSequence G e0), delta ∈ MissingColors G rho1 v →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (a : V ⊕ E) (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (exitPath :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)) (zPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
    ∀ u0 ∉ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc),
    ∀ (exitPath0 : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
        (beta0 : Fin k) (z0 : V) (zPosition0 : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))), (ett.series.data.tree jSlot.succ.castSucc).vertex
        zPosition0 = z0 →
    ∀ (rho3 : PartialEdgeColoring E k), IsProperEdgeColoring G rho3 → IsOneEdgeUncolored rho3 e0 →
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho3 → ( beta0 ∈ MissingColors G rho1 z0 → delta ∈ MissingColors G rho3
        z0) →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ))),
    let terminalInTj : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)) :=
        Fin.castLE (
    by
     have := GoldbergSeymour.TreeSequence.positive T
     have := GoldbergSeymour.TreeSequence.positive seed
     have := Fin.isLt jSlot
     have := Fin.isLt terminalPosition
     have := GoldbergSeymour.TreeSequence.positive seed
     have :=
      GoldbergSeymour.TreeSequence.positive
       (ett.series.data.tree jSlot.succ.castSucc)
     have := hseedTj.1
     omega
    ) (Fin.last seed.length); (ett.series.data.tree jSlot.succ.castSucc).vertex terminalInTj = v →
        ¬z0 = v → zPosition0 = Fin.last (ett.series.data.tree jSlot.succ.castSucc).length ∨
        (↑zPosition0 : ℕ) < (↑(Fin.last (ett.series.data.tree jSlot.succ.castSucc).length) : ℕ) ∧
        beta0 ∈ MissingColors G rho1 z0 → (↑jSlot : ℕ) = (0 : ℕ) →
    ∀ (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤
        TjPrime.length) (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition0 : ℕ)) (hzPositionBound :
        (↑zPosition0 : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑zPosition0 : ℕ) hzPositionPositive hzPositionBound; TreeSequenceInitialSegment Z
        (ett.series.data.tree jSlot.succ.castSucc) → TreeSequenceInitialSegment seed Z →
        TashkinovAugmentationSequence rho3 seed U → MissingColors G rho3 v = MissingColors G rho1
        v →
    ∀ (M : TreeSequence G e0), OrderedTreeUnion U Z M → u0 ∈ TreeSequenceVertexSet U →
        TashkinovAugmentationSequence rho3 U M → False

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperCaseContinuation10866Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G
        sigma → IsOneEdgeUncolored sigma e0 →
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc), Sum.inl w ∈
        TwoColorComponent G sigma gamma delta (Sum.inl v) → ¬w = v →
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds), q.succ = Fin.last ett.rounds →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v → ett.series.data.gamma q.succ = some gamma →
        ett.series.data.delta q.succ = some delta → v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal
        ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal →
        StableColoring (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) → (
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (0 : ℕ) < (↑i : ℕ) → TreeSequenceInitialSegment
        (ett.series.data.tree i.castSucc) (ett.series.data.tree i.succ)) → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) → ((
    ∀ (s t : Fin ett.rounds) (vs vt : V), vs ∈ TreeSequenceVertexSet T → vt ∈
        TreeSequenceVertexSet T →
    ∀ (deltaT gammaS : Fin k), s ∈ ExtensionBaseActiveIndices ett v hvFinal → t ∈
        ExtensionBaseActiveIndices ett v hvFinal → (↑s : ℕ) ≤ (↑t : ℕ) →
        ett.series.data.chosenVertex s.succ = some vs → ett.series.data.chosenVertex t.succ = some
        vt → ett.series.data.delta t.succ = some deltaT → ett.series.data.gamma s.succ = some
        gammaS → deltaT ∉ TreeMissingColors (ett.series.data.coloring s.castSucc)
        (ett.series.data.tree s.succ.castSucc) ∧ deltaT ≠ gammaS) ∧
    ∀ (t : Fin ett.rounds),
    ∀ vt ∈ TreeSequenceVertexSet T,
    ∀ (deltaT : Fin k), t ∈ ExtensionBaseActiveIndices ett v hvFinal →
        ett.series.data.chosenVertex t.succ = some vt → ett.series.data.delta t.succ = some deltaT
        → deltaT ∉ TreeMissingColors (ett.series.data.coloring jSlot.castSucc)
        (ett.series.data.tree jSlot.succ.castSucc)) → (
    ∀ (t : Fin ett.rounds) (gammaT deltaT : Fin k), ett.series.data.kind t.succ = some
        TashkinovExtensionKind.PE → ett.series.data.gamma t.succ = some gammaT →
        ett.series.data.delta t.succ = some deltaT → ett.series.data.stored t.succ = (insert
        gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k))) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)), q ∈
        ExtensionBaseActiveIndices ett v hvFinal →
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 :
        ℕ)) → Fin k), (
    ∀ (a b : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
        → (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.gamma (indices0 a).succ = some (gamma0 a)) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a)) → (
    ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc) → Function.Injective (Fin.cons (gamma0 (0 :
        Fin (p0 + (1 : ℕ)))) delta0) →
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
        IsProperEdgeColoring G rho1 → IsOneEdgeUncolored rho1 e0 → (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) → (
    ∀ (f : E), rho1 f ≠ sigma f → f ∉ InternalEdges G (TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc)) ∧
    ∃ (c : Fin k) (d : Fin k), sigma f = some c ∧ rho1 f = some d ∧ (c ∈
        (ExtensionBaseRestorationIndices ett v hvFinal).biUnion fun (t : Fin ett.rounds) ↦
        ett.series.data.stored t.succ) ∧ d ∈ (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ) →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = v →
    ∀ (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        jSlot.castSucc.succ = jSlot.succ.castSucc → TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) → seed.vertex (Fin.last seed.length) = v →
        TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree q.succ.castSucc) → (
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore T v hvFinal) → (
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore T v hvFinal) → (
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho1 S seed) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0), TashkinovClosure rho1 seed TjPrime →
        ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime) →
        TreeSequenceInitialSegment seed TjPrime → v ∈ TreeSequenceVertexSet TjPrime → indices0
        (Fin.last p0) = q → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.chosenVertex (indices0 a).succ = some v) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.kind (indices0 a).succ = some
        TashkinovExtensionKind.PE) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.stored (indices0 a).succ = (insert (gamma0 a)
        ({delta0 a} : Finset (Fin k)) : Finset (Fin k))) → (MissingColors G rho1 v ∩ supportColors
        : Finset (Fin k)) = ({delta0 (Fin.last p0)} : Finset (Fin k)) → StableColoringBeforeVertex
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ (TashkinovStoredColors
        ett.series.data jSlot.castSucc) (ett.series.data.coloring jSlot.castSucc) rho1 → (
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, (MissingColors G rho1 x ∩ supportColors :
        Finset (Fin k)) = ∅) → (supportColors = (ExtensionBaseSupportClass ett v hvFinal
        v).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ) → q ∈
        ExtensionBaseSupportClass ett v hvFinal v → gamma0 (Fin.last p0) = gamma → delta0
        (Fin.last p0) = delta →
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ))); gamma ∈ supportColors → delta ∈
        supportColors → gammaFirst ∈ supportColors → gamma ≠ delta →
    let restorationColors : Finset (Fin k) := (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ; gamma ∉
        restorationColors ∧ delta ∉ restorationColors → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → gammaS ∈ supportColors ∧ deltaS ∈ supportColors) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → delta ≠ gammaS ∧ delta ≠ deltaS) → ( (0 : ℕ) < p0 →
    ∃ (preterminalSlot : Fin ett.rounds), (↑preterminalSlot : ℕ) < (↑q : ℕ) ∧ preterminalSlot ∈
        (ExtensionBaseSupportClass ett v hvFinal v).erase q ∧ ett.series.data.delta
        preterminalSlot.succ = some gamma) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → ETTStrongInterchangeable ett s v rho1 gammaS deltaS) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS →
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree s.succ.castSucc), x ≠ v →
    ∀ (y : V), Sum.inl y ∈ TwoColorComponent G rho1 gammaS deltaS (Sum.inl x) → y ∈
        TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) → MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho1 v ∪ ({ gammaFirst } :
        Finset (Fin k)) → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → rho1
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) → delta ∉
        TreeMissingColors (ett.series.data.coloring jSlot.castSucc) (ett.series.data.tree
        jSlot.succ.castSucc) → v ∈ TreeSequenceVertexSet seed → TreeSequenceInitialSegment seed
        (ett.series.data.tree q.succ.castSucc) →
    ∀ (fN : E), ett.series.data.connectingEdges q.succ = ({ fN } : Finset E) → Incident G v fN →
        IsProperEdgeColoring G (ett.series.data.coloring q.succ) → IsOneEdgeUncolored
        (ett.series.data.coloring q.succ) e0 → False

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation10517Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G
        sigma → IsOneEdgeUncolored sigma e0 →
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc), ¬w = v →
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds), q.succ = Fin.last ett.rounds →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v → ett.series.data.gamma q.succ = some gamma →
        ett.series.data.delta q.succ = some delta → v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal
        ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal →
        StableColoring (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) → (
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (0 : ℕ) < (↑i : ℕ) → TreeSequenceInitialSegment
        (ett.series.data.tree i.castSucc) (ett.series.data.tree i.succ)) → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) → ((
    ∀ (s t : Fin ett.rounds) (vs vt : V), vs ∈ TreeSequenceVertexSet T → vt ∈
        TreeSequenceVertexSet T →
    ∀ (deltaT gammaS : Fin k), s ∈ ExtensionBaseActiveIndices ett v hvFinal → t ∈
        ExtensionBaseActiveIndices ett v hvFinal → (↑s : ℕ) ≤ (↑t : ℕ) →
        ett.series.data.chosenVertex s.succ = some vs → ett.series.data.chosenVertex t.succ = some
        vt → ett.series.data.delta t.succ = some deltaT → ett.series.data.gamma s.succ = some
        gammaS → deltaT ∉ TreeMissingColors (ett.series.data.coloring s.castSucc)
        (ett.series.data.tree s.succ.castSucc) ∧ deltaT ≠ gammaS) ∧
    ∀ (t : Fin ett.rounds),
    ∀ vt ∈ TreeSequenceVertexSet T,
    ∀ (deltaT : Fin k), t ∈ ExtensionBaseActiveIndices ett v hvFinal →
        ett.series.data.chosenVertex t.succ = some vt → ett.series.data.delta t.succ = some deltaT
        → deltaT ∉ TreeMissingColors (ett.series.data.coloring jSlot.castSucc)
        (ett.series.data.tree jSlot.succ.castSucc)) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)), q ∈
        ExtensionBaseActiveIndices ett v hvFinal →
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 :
        ℕ)) → Fin k), (
    ∀ (a b : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
        → (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.gamma (indices0 a).succ = some (gamma0 a)) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a)) → (
    ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc) → Function.Injective (Fin.cons (gamma0 (0 :
        Fin (p0 + (1 : ℕ)))) delta0) →
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
        IsProperEdgeColoring G rho1 → IsOneEdgeUncolored rho1 e0 → (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) → (
    ∀ (f : E), rho1 f ≠ sigma f → f ∉ InternalEdges G (TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc)) ∧
    ∃ (c : Fin k) (d : Fin k), sigma f = some c ∧ rho1 f = some d ∧ (c ∈
        (ExtensionBaseRestorationIndices ett v hvFinal).biUnion fun (t : Fin ett.rounds) ↦
        ett.series.data.stored t.succ) ∧ d ∈ (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ) →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = v →
    ∀ (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        jSlot.castSucc.succ = jSlot.succ.castSucc → TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) → seed.vertex (Fin.last seed.length) = v →
        TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree q.succ.castSucc) → (
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore T v hvFinal) → (
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore T v hvFinal) → (
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho1 S seed) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0), TashkinovClosure rho1 seed TjPrime →
        ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime) →
        TreeSequenceInitialSegment seed TjPrime → v ∈ TreeSequenceVertexSet TjPrime → indices0
        (Fin.last p0) = q → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.chosenVertex (indices0 a).succ = some v) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.kind (indices0 a).succ = some
        TashkinovExtensionKind.PE) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.stored (indices0 a).succ = (insert (gamma0 a)
        ({delta0 a} : Finset (Fin k)) : Finset (Fin k))) → StableColoringBeforeVertex
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ (TashkinovStoredColors
        ett.series.data jSlot.castSucc) (ett.series.data.coloring jSlot.castSucc) rho1 → (
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, (MissingColors G rho1 x ∩ supportColors :
        Finset (Fin k)) = ∅) → (supportColors = (ExtensionBaseSupportClass ett v hvFinal
        v).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ) → q ∈
        ExtensionBaseSupportClass ett v hvFinal v → gamma0 (Fin.last p0) = gamma →
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ))); gamma ∈ supportColors → delta ∈
        supportColors → gammaFirst ∈ supportColors → gamma ≠ delta →
    let restorationColors : Finset (Fin k) := (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ; gamma ∉
        restorationColors ∧ delta ∉ restorationColors → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → gammaS ∈ supportColors ∧ deltaS ∈ supportColors) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → delta ≠ gammaS ∧ delta ≠ deltaS) → ( (0 : ℕ) < p0 →
    ∃ (preterminalSlot : Fin ett.rounds), (↑preterminalSlot : ℕ) < (↑q : ℕ) ∧ preterminalSlot ∈
        (ExtensionBaseSupportClass ett v hvFinal v).erase q ∧ ett.series.data.delta
        preterminalSlot.succ = some gamma) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → ETTStrongInterchangeable ett s v rho1 gammaS deltaS) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS →
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree s.succ.castSucc), x ≠ v →
    ∀ (y : V), Sum.inl y ∈ TwoColorComponent G rho1 gammaS deltaS (Sum.inl x) → y ∈
        TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) → MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho1 v ∪ ({ gammaFirst } :
        Finset (Fin k)) → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → rho1
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) → delta ∉
        TreeMissingColors (ett.series.data.coloring jSlot.castSucc) (ett.series.data.tree
        jSlot.succ.castSucc) → v ∈ TreeSequenceVertexSet seed → TreeSequenceInitialSegment seed
        (ett.series.data.tree q.succ.castSucc) →
    ∀ (fN : E), Incident G v fN → IsProperEdgeColoring G (ett.series.data.coloring q.succ) →
        IsOneEdgeUncolored (ett.series.data.coloring q.succ) e0 → BoundaryColorEdges G
        (ett.series.data.coloring q.succ) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) gamma = ({ fN } : Finset E) → (
    ∀ f ∈ BoundaryColorEdges G (ett.series.data.coloring q.succ) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) delta,
    ∃ y ∈ TreeSequenceVertexSet seed, Incident G y f) → delta ∈ MissingColors G rho1 v →
        (MissingColors G rho1 v ∩ supportColors : Finset (Fin k)) = ({ delta } : Finset (Fin k)) →
    let controlled : Finset (Fin k) := TreeMissingColors (ett.series.data.coloring q.succ)
        (ett.series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors ett.series.data q.succ;
        gamma ∈ controlled → delta ∈ controlled → StableColoring (ett.series.data.tree
        q.succ.castSucc) controlled (ett.series.data.coloring q.succ) sigma → BoundaryColorEdges G
        rho1 (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) gamma = ({ fN } :
        Finset E) → BoundaryColorEdges G rho1 (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc) ∪ TreeSequenceVertexSet TjPrime) delta = ∅ → TwoColorIncidenceGraph G
        sigma gamma delta = TwoColorIncidenceGraph G rho1 gamma delta → Sum.inl w ∈
        TwoColorComponent G rho1 gamma delta (Sum.inl v) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (a b : V ⊕ E) (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)), componentPath.IsPath
        → {z : V ⊕ E | z ∈ componentPath.support} = C → ¬componentPath.Nil → (0 : ℕ) <
        componentPath.length → Sum.inl x ∈ C → (
    ∀ (z : V ⊕ E), H.Adj (Sum.inl x) z → z = componentPath.getVert (componentPath.length - (1 :
        ℕ))) → False

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation11325Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G
        sigma → IsOneEdgeUncolored sigma e0 →
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds), ett.series.data.gamma q.succ = some gamma →
        ett.series.data.delta q.succ = some delta → v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal
        ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (indices0 : Fin
        (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k), (
    ∀ (a b : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
        → (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.gamma (indices0 a).succ = some (gamma0 a)) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a)) → (
    ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc) → Function.Injective (Fin.cons (gamma0 (0 :
        Fin (p0 + (1 : ℕ)))) delta0) →
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
        IsProperEdgeColoring G rho1 → IsOneEdgeUncolored rho1 e0 → (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) → (
    ∀ (f : E), rho1 f ≠ sigma f → f ∉ InternalEdges G (TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc)) ∧
    ∃ (c : Fin k) (d : Fin k), sigma f = some c ∧ rho1 f = some d ∧ (c ∈
        (ExtensionBaseRestorationIndices ett v hvFinal).biUnion fun (t : Fin ett.rounds) ↦
        ett.series.data.stored t.succ) ∧ d ∈ (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ) →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        jSlot.castSucc.succ = jSlot.succ.castSucc → TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) → seed.vertex (Fin.last seed.length) = v →
        TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree q.succ.castSucc) → (
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore T v hvFinal) → (
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore T v hvFinal) → (
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho1 S seed) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0), TashkinovClosure rho1 seed TjPrime →
        ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime) →
        TreeSequenceInitialSegment seed TjPrime → v ∈ TreeSequenceVertexSet TjPrime → indices0
        (Fin.last p0) = q → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.chosenVertex (indices0 a).succ = some v) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.kind (indices0 a).succ = some
        TashkinovExtensionKind.PE) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.stored (indices0 a).succ = (insert (gamma0 a)
        ({delta0 a} : Finset (Fin k)) : Finset (Fin k))) → StableColoringBeforeVertex
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ (TashkinovStoredColors
        ett.series.data jSlot.castSucc) (ett.series.data.coloring jSlot.castSucc) rho1 → (
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, (MissingColors G rho1 x ∩ supportColors :
        Finset (Fin k)) = ∅) → (supportColors = (ExtensionBaseSupportClass ett v hvFinal
        v).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ) → q ∈
        ExtensionBaseSupportClass ett v hvFinal v → gamma0 (Fin.last p0) = gamma →
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ))); gamma ∈ supportColors → delta ∈
        supportColors → gammaFirst ∈ supportColors → gamma ≠ delta →
    let restorationColors : Finset (Fin k) := (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ; gamma ∉
        restorationColors ∧ delta ∉ restorationColors → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → gammaS ∈ supportColors ∧ deltaS ∈ supportColors) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → delta ≠ gammaS ∧ delta ≠ deltaS) → ( (0 : ℕ) < p0 →
    ∃ (preterminalSlot : Fin ett.rounds), (↑preterminalSlot : ℕ) < (↑q : ℕ) ∧ preterminalSlot ∈
        (ExtensionBaseSupportClass ett v hvFinal v).erase q ∧ ett.series.data.delta
        preterminalSlot.succ = some gamma) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → ETTStrongInterchangeable ett s v rho1 gammaS deltaS) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS →
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree s.succ.castSucc), x ≠ v →
    ∀ (y : V), Sum.inl y ∈ TwoColorComponent G rho1 gammaS deltaS (Sum.inl x) → y ∈
        TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) → MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho1 v ∪ ({ gammaFirst } :
        Finset (Fin k)) → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → rho1
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) → delta ∉
        TreeMissingColors (ett.series.data.coloring jSlot.castSucc) (ett.series.data.tree
        jSlot.succ.castSucc) → v ∈ TreeSequenceVertexSet seed → TreeSequenceInitialSegment seed
        (ett.series.data.tree q.succ.castSucc) →
    ∀ (fN : E), Incident G v fN → IsProperEdgeColoring G (ett.series.data.coloring q.succ) →
        IsOneEdgeUncolored (ett.series.data.coloring q.succ) e0 → BoundaryColorEdges G
        (ett.series.data.coloring q.succ) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) gamma = ({ fN } : Finset E) → (
    ∀ f ∈ BoundaryColorEdges G (ett.series.data.coloring q.succ) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) delta,
    ∃ y ∈ TreeSequenceVertexSet seed, Incident G y f) → delta ∈ MissingColors G rho1 v →
        (MissingColors G rho1 v ∩ supportColors : Finset (Fin k)) = ({ delta } : Finset (Fin k)) →
    let controlled : Finset (Fin k) := TreeMissingColors (ett.series.data.coloring q.succ)
        (ett.series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors ett.series.data q.succ;
        gamma ∈ controlled → delta ∈ controlled → StableColoring (ett.series.data.tree
        q.succ.castSucc) controlled (ett.series.data.coloring q.succ) sigma →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (a b : V ⊕ E) (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)), componentPath.IsPath
        → {z : V ⊕ E | z ∈ componentPath.support} = C → x ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet TjPrime → (
    ∃ y ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), y ≠ v ∧ Sum.inl y ∈
        componentPath.support) →
    ∀ (u : V) (exitPath : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl
        u)), exitPath.IsPath → (2 : ℕ) ≤ exitPath.length → (
    ∀ y ∈ exitPath.support, y ∈ componentPath.support) → (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet
        TjPrime, Sum.inl w ∈ exitPath.support ↔ w = u) → (
    ∃ g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)
        ∪ TreeSequenceVertexSet TjPrime) gamma, Incident G u g ∧ Sum.inr g ∈ exitPath.support) →
        ¬Incident G u fN → u ∈ TreeSequenceVertexSet TjPrime → u ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) → MaximumDegree G + (1 : ℕ) ≤ k →
    ∀ beta ∈ MissingColors G rho1 u, u ∈ (TreeSequenceVertexSet TjPrime).erase v → beta ∉
        supportColors →
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ( (0 : ℕ) <
        (↑jSlot : ℕ) → TreeSequenceInitialSegment Tprevious (ett.series.data.tree
        jSlot.succ.castSucc)) → ( (0 : ℕ) < (↑jSlot : ℕ) → Tprevious.length < seed.length) → ( (0
        : ℕ) < (↑jSlot : ℕ) → TreeSequenceInitialSegment Tprevious seed) →
        TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) seed
        (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (z : V) (hz : z ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
        (zPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition = z → seed.length ≤
        (↑zPosition : ℕ) → ((seed.length < (↑zPosition : ℕ) ∧ beta ∈ MissingColors G rho1 z ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → (↑r : ℕ) < (↑zPosition : ℕ) → beta ∉ MissingColors G rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).vertex r)) ∨ zPosition = Fin.last (ett.series.data.tree
        jSlot.succ.castSucc).length ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → beta ∉ MissingColors G rho1 ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) →
        (
    ∀ w ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z hz, beta ∉ MissingColors
        G rho1 w) → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → (↑a :
        ℕ) < (↑zPosition : ℕ) → rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) ≠ some
        beta) → False

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperCaseContinuation13733Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G
        sigma → IsOneEdgeUncolored sigma e0 →
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc), Sum.inl w ∈
        TwoColorComponent G sigma gamma delta (Sum.inl v) → ¬w = v →
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds), q.succ = Fin.last ett.rounds →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v → ett.series.data.gamma q.succ = some gamma →
        ett.series.data.delta q.succ = some delta → v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) → q.succ.castSucc = (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal
        ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal → (↑jSlot
        : ℕ) ≤ (↑q : ℕ) → StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T v hvFinal (TashkinovStoredColors ett.series.data
        jSlot.castSucc) (ett.series.data.coloring jSlot.castSucc) sigma → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) → (
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (0 : ℕ) < (↑i : ℕ) → TreeSequenceInitialSegment
        (ett.series.data.tree i.castSucc) (ett.series.data.tree i.succ)) → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) → ((
    ∀ (s t : Fin ett.rounds) (vs vt : V), vs ∈ TreeSequenceVertexSet T → vt ∈
        TreeSequenceVertexSet T → s ∈ ExtensionBaseActiveIndices ett v hvFinal → t ∈
        ExtensionBaseActiveIndices ett v hvFinal → (↑s : ℕ) < (↑t : ℕ) →
        ett.series.data.chosenVertex s.succ = some vs → ett.series.data.chosenVertex t.succ = some
        vt → vt = vs ∨ TreeVertexOrder T vt vs) ∧ (
    ∀ (s : Fin ett.rounds) (vs : V) (hvsFinal : vs ∈ TreeSequenceVertexSet T), s ∈
        ExtensionBaseActiveIndices ett v hvFinal → ett.series.data.chosenVertex s.succ = some vs →
        ETTFirstAppearanceIndex ett vs hvsFinal = ETTFirstAppearanceIndex ett v hvFinal ∧ (v = vs
        ∨ TreeVertexOrder T v vs)) ∧
    ∀ (s t : Fin ett.rounds) (vs vt : V), vs ∈ TreeSequenceVertexSet T → vt ∈
        TreeSequenceVertexSet T → s ∈ ExtensionBaseActiveIndices ett v hvFinal → t ∈
        ExtensionBaseActiveIndices ett v hvFinal → ett.series.data.chosenVertex s.succ = some vs →
        ett.series.data.chosenVertex t.succ = some vt → vs ≠ vt → TreeVertexOrder T vs vt → (↑t :
        ℕ) < (↑s : ℕ)) → ((
    ∀ (s t : Fin ett.rounds) (vs vt : V), vs ∈ TreeSequenceVertexSet T → vt ∈
        TreeSequenceVertexSet T →
    ∀ (deltaT gammaS : Fin k), s ∈ ExtensionBaseActiveIndices ett v hvFinal → t ∈
        ExtensionBaseActiveIndices ett v hvFinal → (↑s : ℕ) ≤ (↑t : ℕ) →
        ett.series.data.chosenVertex s.succ = some vs → ett.series.data.chosenVertex t.succ = some
        vt → ett.series.data.delta t.succ = some deltaT → ett.series.data.gamma s.succ = some
        gammaS → deltaT ∉ TreeMissingColors (ett.series.data.coloring s.castSucc)
        (ett.series.data.tree s.succ.castSucc) ∧ deltaT ≠ gammaS) ∧
    ∀ (t : Fin ett.rounds),
    ∀ vt ∈ TreeSequenceVertexSet T,
    ∀ (deltaT : Fin k), t ∈ ExtensionBaseActiveIndices ett v hvFinal →
        ett.series.data.chosenVertex t.succ = some vt → ett.series.data.delta t.succ = some deltaT
        → deltaT ∉ TreeMissingColors (ett.series.data.coloring jSlot.castSucc)
        (ett.series.data.tree jSlot.succ.castSucc)) → (
    ∀ (s t : Fin ett.rounds) (vs vt : V), vs ∈ TreeSequenceVertexSet T → vt ∈
        TreeSequenceVertexSet T →
    ∀ (gammaS deltaS gammaT deltaT : Fin k), s ∈ ExtensionBaseActiveIndices ett v hvFinal → t ∈
        ExtensionBaseActiveIndices ett v hvFinal → (↑s : ℕ) < (↑t : ℕ) →
        ett.series.data.chosenVertex s.succ = some vs → ett.series.data.chosenVertex t.succ = some
        vt → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ = some
        deltaS → ett.series.data.gamma t.succ = some gammaT → ett.series.data.delta t.succ = some
        deltaT → ((ett.series.data.stored s.succ ∩ ett.series.data.stored t.succ : Finset (Fin
        k)).Nonempty ↔ vs = vt ∧ ¬
    ∃ r ∈ ExtensionBaseActiveIndices ett v hvFinal, (↑s : ℕ) < (↑r : ℕ) ∧ (↑r : ℕ) < (↑t : ℕ) ∧
        ett.series.data.chosenVertex r.succ = some vs) ∧ ( (ett.series.data.stored s.succ ∩
        ett.series.data.stored t.succ : Finset (Fin k)).Nonempty → (ett.series.data.stored s.succ
        ∩ ett.series.data.stored t.succ : Finset (Fin k)) = ({ gammaT } : Finset (Fin k)) ∧
        (ett.series.data.stored s.succ ∩ ett.series.data.stored t.succ : Finset (Fin k)) =
        ({ deltaS } : Finset (Fin k)))) → False

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation13931Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k), IsProperEdgeColoring G
        sigma → IsOneEdgeUncolored sigma e0 →
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc), Sum.inl w ∈
        TwoColorComponent G sigma gamma delta (Sum.inl v) → ¬w = v →
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds), q.succ = Fin.last ett.rounds →
        ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v → ett.series.data.gamma q.succ = some gamma →
        ett.series.data.delta q.succ = some delta → v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) → q.succ.castSucc = (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal
        ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal → (↑jSlot
        : ℕ) ≤ (↑q : ℕ) → StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma →
        StableColoringBeforeVertex T v hvFinal (TashkinovStoredColors ett.series.data
        jSlot.castSucc) (ett.series.data.coloring jSlot.castSucc) sigma → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) → (
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (0 : ℕ) < (↑i : ℕ) → TreeSequenceInitialSegment
        (ett.series.data.tree i.castSucc) (ett.series.data.tree i.succ)) → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) → ((
    ∀ (s t : Fin ett.rounds) (vs vt : V), vs ∈ TreeSequenceVertexSet T → vt ∈
        TreeSequenceVertexSet T →
    ∀ (deltaT gammaS : Fin k), s ∈ ExtensionBaseActiveIndices ett v hvFinal → t ∈
        ExtensionBaseActiveIndices ett v hvFinal → (↑s : ℕ) ≤ (↑t : ℕ) →
        ett.series.data.chosenVertex s.succ = some vs → ett.series.data.chosenVertex t.succ = some
        vt → ett.series.data.delta t.succ = some deltaT → ett.series.data.gamma s.succ = some
        gammaS → deltaT ∉ TreeMissingColors (ett.series.data.coloring s.castSucc)
        (ett.series.data.tree s.succ.castSucc) ∧ deltaT ≠ gammaS) ∧
    ∀ (t : Fin ett.rounds),
    ∀ vt ∈ TreeSequenceVertexSet T,
    ∀ (deltaT : Fin k), t ∈ ExtensionBaseActiveIndices ett v hvFinal →
        ett.series.data.chosenVertex t.succ = some vt → ett.series.data.delta t.succ = some deltaT
        → deltaT ∉ TreeMissingColors (ett.series.data.coloring jSlot.castSucc)
        (ett.series.data.tree jSlot.succ.castSucc)) → (
    ∀ (t : Fin ett.rounds), ett.series.data.kind t.succ = some TashkinovExtensionKind.PE →
    ∃ (vt : V) (gammaT : Fin k) (deltaT : Fin k), ett.series.data.chosenVertex t.succ = some vt ∧
        ett.series.data.gamma t.succ = some gammaT ∧ ett.series.data.delta t.succ = some deltaT) →
        (
    ∀ (t : Fin ett.rounds) (gammaT deltaT : Fin k), ett.series.data.kind t.succ = some
        TashkinovExtensionKind.PE → ett.series.data.gamma t.succ = some gammaT →
        ett.series.data.delta t.succ = some deltaT → ett.series.data.stored t.succ = (insert
        gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k))) → (
    ∀ (u : V), (ExtensionBaseSupportClass ett v hvFinal u).Nonempty →
    ∃ (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (gammaClass : Fin (p + (1 : ℕ)) → Fin
        k) (deltaClass : Fin (p + (1 : ℕ)) → Fin k), (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices a) : ℕ) < (↑(indices b) : ℕ)) ∧
        (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal u ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = r) ∧ (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gammaClass a)) ∧ (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (deltaClass a)) ∧ (
    ∀ (a : Fin p), gammaClass a.succ = deltaClass a.castSucc) ∧ Function.Injective (Fin.cons
        (gammaClass (0 : Fin (p + (1 : ℕ)))) deltaClass) ∧ (
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc), (
    ∀ r ∈ ExtensionBaseActiveIndices ett v hvFinal, ett.series.data.chosenVertex r.succ ≠ some x)
        → MissingColors G sigma x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
    let storedPairs : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p + (1 : ℕ))) ↦
        ett.series.data.stored (indices a).succ; (MissingColors G sigma u ∩ storedPairs : Finset
        (Fin k)) = ({deltaClass (Fin.last p)} : Finset (Fin k)) ∧ MissingColors G
        (ett.series.data.coloring jSlot.castSucc) u = MissingColors G sigma u \
        ({deltaClass (Fin.last p)} : Finset (Fin k)) ∪ ({gammaClass (0 : Fin (p + (1 : ℕ)))} :
        Finset (Fin k))) → (
    ∀ (t : Fin ett.rounds) (vt : V), t ∈ ExtensionBaseRestorationIndices ett v hvFinal →
        ett.series.data.chosenVertex t.succ = some vt → TreeVertexOrder T v vt) → (
    ∀ t ∈ ExtensionBaseRestorationIndices ett v hvFinal, TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc) (ett.series.data.tree t.succ.castSucc)) → (
    ∀ t ∈ ExtensionBaseRestorationIndices ett v hvFinal,
    ∃ (vt : V) (gammaT : Fin k) (deltaT : Fin k), ett.series.data.chosenVertex t.succ = some vt ∧
        ett.series.data.gamma t.succ = some gammaT ∧ ett.series.data.delta t.succ = some deltaT) →
        (
    ∀ (t : Fin ett.rounds) (vt : V) (gammaT deltaT : Fin k), t ∈ ExtensionBaseActiveIndices ett v
        hvFinal → t ≠ q → ett.series.data.chosenVertex t.succ = some vt → ett.series.data.gamma
        t.succ = some gammaT → ett.series.data.delta t.succ = some deltaT →
        ETTStrongInterchangeable ett t vt sigma gammaT deltaT) → (
    ∀ (u : V) (t : Fin ett.rounds) (deltaT : Fin k), ExtensionBaseSupportClass ett v hvFinal u ⊆
        ExtensionBaseRestorationIndices ett v hvFinal → t ∈ ExtensionBaseSupportClass ett v
        hvFinal u → (
    ∀ s ∈ ExtensionBaseSupportClass ett v hvFinal u, (↑s : ℕ) ≤ (↑t : ℕ)) → ett.series.data.delta
        t.succ = some deltaT → (MissingColors G sigma u ∩ (ExtensionBaseSupportClass ett v hvFinal
        u).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ : Finset (Fin k)) =
        ({ deltaT } : Finset (Fin k))) → (
    ∀ (s t : Fin ett.rounds) (vs vt : V) (gammaS deltaS gammaT deltaT : Fin k), s ∈
        ExtensionBaseActiveIndices ett v hvFinal → t ∈ ExtensionBaseActiveIndices ett v hvFinal →
        (↑s : ℕ) < (↑t : ℕ) → ett.series.data.chosenVertex s.succ = some vs →
        ett.series.data.chosenVertex t.succ = some vt → ett.series.data.gamma s.succ = some gammaS
        → ett.series.data.delta s.succ = some deltaS → ett.series.data.gamma t.succ = some gammaT
        → ett.series.data.delta t.succ = some deltaT → (((insert gammaS ({ deltaS } : Finset (Fin
        k)) : Finset (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k)) :
        Finset (Fin k)).Nonempty ↔ vs = vt ∧ ¬
    ∃ r ∈ ExtensionBaseSupportClass ett v hvFinal vs, (↑s : ℕ) < (↑r : ℕ) ∧ (↑r : ℕ) < (↑t : ℕ) ∧
        ett.series.data.chosenVertex r.succ = some vs) ∧ ( ((insert gammaS ({ deltaS } : Finset
        (Fin k)) : Finset (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin
        k)) : Finset (Fin k)).Nonempty → ((insert gammaS ({ deltaS } : Finset (Fin k)) : Finset
        (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k)) : Finset (Fin
        k)) = ({ gammaT } : Finset (Fin k)) ∧ ((insert gammaS ({ deltaS } : Finset (Fin k)) :
        Finset (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k)) : Finset
        (Fin k)) = ({ deltaS } : Finset (Fin k)))) → False

end GoldbergSeymour.ExtensionBaseProof

end
