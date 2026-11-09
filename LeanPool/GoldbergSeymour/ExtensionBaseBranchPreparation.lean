/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceTransport


public import LeanPool.GoldbergSeymour.IncidencePathFacts
public import LeanPool.GoldbergSeymour.SharedFacts.ExtensionBranchPreparation

public import LeanPool.GoldbergSeymour.SharedFacts.ExtensionBaseStepLemmas

import all LeanPool.GoldbergSeymour.ExtensionBaseAuxiliary

public import LeanPool.GoldbergSeymour.ExtensionBaseStepLemmas
public import LeanPool.GoldbergSeymour.TashkinovAugmentationBeforeVertex
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap

/-!
# Preparatory lemmas for the extension base

Part of Wesley Pegden’s Trellis formalization of the Goldberg–Seymour theorem,
commit 88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. These lemmas establish the
base cases used by the extension construction.
-/

@[expose] public section

namespace GoldbergSeymour.ExtensionBaseProof

private abbrev helperHmissingX6300Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let this : DecidableEq V := Classical.decEq V;
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
    ∀ (hseedTj : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc))
        (TjPrime : TreeSequence G e0) (a : V ⊕ E) (u0 z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)) (zPosition0 : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (hzPosition0 : (ett.series.data.tree
        jSlot.succ.castSucc).vertex zPosition0 = z0) (rho3 : PartialEdgeColoring E k) (uPosition :
        Fin (TjPrime.length + (1 : ℕ))),
    let terminalInTj : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)) :=
        Fin.castLE (
    by
         first
         | omega
         | (
           have := GoldbergSeymour.TreeSequence.positive T
           have := Fin.isLt terminalPosition
           have := hseedTj.1
           have :=
            GoldbergSeymour.TreeSequence.positive
             (TreeSequencePrefix
              (ett.series.data.tree
               (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by omega⟩ :
                 Fin ett.rounds).succ.castSucc)
              (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound)
           have :=
            GoldbergSeymour.TreeSequence.positive
             (ett.series.data.tree
              (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by omega⟩ :
                Fin ett.rounds).succ.castSucc)
           all_goals omega)
    ) (Fin.last seed.length);
    ∀ (hterminalInTjVal : (↑terminalInTj : ℕ) = seed.length) (huPositionPositive : (1 : ℕ) ≤
        (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length)
        (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition0 : ℕ)) (hzPositionBound : (↑zPosition0 : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑zPosition0 : ℕ) hzPositionPositive hzPositionBound;
    ∀ (hZTj : TreeSequenceInitialSegment Z (ett.series.data.tree jSlot.succ.castSucc)) (hseedU :
        TreeSequenceInitialSegment seed U) (hterminalInclusionRho3 : MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho3 v ∪ MissingColors G
        rho3 u0) (hbeforeZMissing :
    ∀ y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0, y ≠ v →
        MissingColors G rho3 y = MissingColors G (ett.series.data.coloring jSlot.castSucc) y) (M :
        TreeSequence G e0) (huU : u0 ∈ TreeSequenceVertexSet U) (heveryNewRightEntry :
    ∀ (i : Fin Z.length), Z.vertex i.succ ∉ TreeSequenceVertexSet U →
    ∃ (j : Fin M.length), U.length ≤ (↑j : ℕ) ∧ M.edge j = Z.edge i ∧ M.vertex j.succ = Z.vertex
        i.succ) (hrightOrder :
    ∀ (i j : Fin Z.length), Z.vertex i.succ ∉ TreeSequenceVertexSet U → Z.vertex j.succ ∉
        TreeSequenceVertexSet U → (↑i : ℕ) < (↑j : ℕ) →
    ∀ (p q : Fin M.length), M.vertex p.succ = Z.vertex i.succ → M.vertex q.succ = Z.vertex j.succ
        → (↑p : ℕ) < (↑q : ℕ)) (hseedZSegment : TreeSequenceInitialSegment seed Z) (n : ℕ) (hnU :
        U.length ≤ n) (hnM : n + (1 : ℕ) ≤ M.length) (hnM' : n ≤ M.length),
    let X : TreeSequence G e0 := TreeSequencePrefix M n (Nat.le_trans U.positive hnU) hnM';
    let j : Fin M.length := (⟨n,
    by omega
    ⟩ : Fin M.length);
    ∀ (i : Fin Z.length) (hvertexMZ : M.vertex j.succ = Z.vertex i.succ) (hrightOutside : Z.vertex
        i.succ ∉ TreeSequenceVertexSet U) (hiSeed : seed.length ≤ (↑i : ℕ)) (hiZ : (↑i : ℕ) <
        Z.length),
    let ZX : TreeSequence G e0 := TreeSequencePrefix Z (↑i : ℕ) (Nat.le_trans seed.positive
        hiSeed) (Nat.le_of_lt hiZ);
    ∀ (hZXZ : TreeSequenceInitialSegment ZX Z) (hZXlen : ZX.length = (↑i : ℕ)) (A : TreeSequence G
        e0) (hlenA : A.length = ZX.length + (1 : ℕ)) (c : Fin k) (hmissingZX : c ∈
        TreeMissingColors (ett.series.data.coloring jSlot.castSucc) ZX) (hleftX :
    ∀ {y : V} (hyU : y ∈ TreeSequenceVertexSet U), y ∈ TreeSequenceVertexSet X), c ∈
        TreeMissingColors rho3 X

private abbrev helperContinuation8265Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hMP : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds)
        (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvStage : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hjSlot : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (segmentTrans :
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) (vertexTransfer :
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma)
        (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 :
        ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) →
        Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (hrho1Proper : IsProperEdgeColoring G rho1) (hrho1One : IsOneEdgeUncolored rho1 e0)
        (hb2Missing : (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v) (hb2TreeEdges :
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) (terminalPosition :
        Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (hjTreeIndex : jSlot.castSucc.succ = jSlot.succ.castSucc) (hseedTj :
        TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (hseedTerminal
        : seed.vertex (Fin.last seed.length) = v) (hTjQ : TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc) (ett.series.data.tree q.succ.castSucc))
        (hseedVertexBefore :
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore T v hvFinal) (segmentVertexBefore :
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore T v hvFinal)
        (transportSeedRoute :
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho1 S seed) (commonPrefix :
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B),
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0) (hclosure : TashkinovClosure rho1 seed TjPrime)
        (hprimeElementary : ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime))
        (hseedPrime : TreeSequenceInitialSegment seed TjPrime) (hterminalPrime : v ∈
        TreeSequenceVertexSet TjPrime) (hqLast : indices0 (Fin.last p0) = q) (hb1Tj :
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho1) (hcaseTwoPointwise :
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, (MissingColors G rho1 x ∩ supportColors :
        Finset (Fin k)) = ∅),
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ)));
    ∀ (hgammaSupport : gamma ∈ supportColors) (hdeltaSupport : delta ∈ supportColors) (hgammaDelta
        : gamma ≠ delta) (hterminalInclusion : MissingColors G (ett.series.data.coloring
        jSlot.castSucc) v ⊆ MissingColors G rho1 v ∪ ({ gammaFirst } : Finset (Fin k)))
        (hb2EdgesFromSeed :
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → rho1
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) (hdeltaPhiJ : delta ∉
        TreeMissingColors (ett.series.data.coloring jSlot.castSucc) (ett.series.data.tree
        jSlot.succ.castSucc)) (hterminalSeed : v ∈ TreeSequenceVertexSet seed) (hseedN :
        TreeSequenceInitialSegment seed (ett.series.data.tree q.succ.castSucc)) (fN : E)
        (hdeltaMissing : delta ∈ MissingColors G rho1 v),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (a b : V ⊕ E) (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (hcomponentPath :
        componentPath.IsPath) (hcomponentSupport : {z : V ⊕ E | z ∈ componentPath.support} = C)
        (hxOutside : x ∉ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪
        TreeSequenceVertexSet TjPrime) (u : V) (exitPath : (TwoColorIncidenceGraph G rho1 gamma
        delta).Walk (Sum.inl x) (Sum.inl u)) (hexitPath : exitPath.IsPath) (hexitLength : (2 : ℕ)
        ≤ exitPath.length) (hexitSupport :
    ∀ y ∈ exitPath.support, y ∈ componentPath.support) (hexitIntersection :
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet
        TjPrime, Sum.inl w ∈ exitPath.support ↔ w = u) (hexitBoundary :
    ∃ g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)
        ∪ TreeSequenceVertexSet TjPrime) gamma, Incident G u g ∧ Sum.inr g ∈ exitPath.support)
        (huNotFN : ¬Incident G u fN) (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (huOutside : u
        ∉ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) (hdegree : MaximumDegree G
        + (1 : ℕ) ≤ k) (beta : Fin k) (hbeta : beta ∈ MissingColors G rho1 u) (hbetaSupport : beta
        ∉ supportColors),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (hpreviousTj : (0 : ℕ) < (↑jSlot : ℕ) → TreeSequenceInitialSegment Tprevious
        (ett.series.data.tree jSlot.succ.castSucc)) (hpreviousStrict : (0 : ℕ) < (↑jSlot : ℕ) →
        Tprevious.length < seed.length) (hpreviousSeed : (0 : ℕ) < (↑jSlot : ℕ) →
        TreeSequenceInitialSegment Tprevious seed) (haugmentation : TashkinovAugmentationSequence
        (ett.series.data.coloring jSlot.castSucc) seed (ett.series.data.tree jSlot.succ.castSucc))
        (z : V) (hz : z ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
        (zPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hzPosition : (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition = z) (hzAfter :
        seed.length ≤ (↑zPosition : ℕ)) (hzChoice : (seed.length < (↑zPosition : ℕ) ∧ beta ∈
        MissingColors G rho1 z ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → (↑r : ℕ) < (↑zPosition : ℕ) → beta ∉ MissingColors G rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).vertex r)) ∨ zPosition = Fin.last (ett.series.data.tree
        jSlot.succ.castSucc).length ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → beta ∉ MissingColors G rho1 ((ett.series.data.tree jSlot.succ.castSucc).vertex r))
        (hzBefore :
    ∀ w ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z hz, beta ∉ MissingColors
        G rho1 w) (hzEdges :
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → (↑a :
        ℕ) < (↑zPosition : ℕ) → rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) ≠ some
        beta) (hpositiveClaim45 :
    ∀ (hp0 : (0 : ℕ) < p0),
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
        uPosition = u ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → rho3 f = rho1 f) ∧
        (beta ∈ MissingColors G rho1 z → delta ∈ MissingColors G rho3 z) ∧ (z ∈ TreeVerticesBefore
        TjPrime u huPrime → MissingColors G rho3 z = MissingColors G rho1 z) ∧ gammaFirst ∈
        MissingColors G rho3 u) (hgammaFirstZero :
    ∀ (hp0 : p0 = (0 : ℕ)), gammaFirst = gamma), False

private abbrev helperContinuation7187Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hMP : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds)
        (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k) (hsigmaProper : IsProperEdgeColoring G sigma) (hsigmaOne
        : IsOneEdgeUncolored sigma e0),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hqGamma : ett.series.data.gamma q.succ =
        some gamma) (hqDelta : ett.series.data.delta q.succ = some delta) (hvStage : v ∈
        TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) (hvFinal : v ∈
        TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) +
        (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hjSlot : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (segmentTrans :
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) (stageToStage :
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) (vertexTransfer :
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma)
        (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 :
        ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) →
        Fin k) (hincreasing0 :
    ∀ (a b : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
        (hclass0 :
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) (hgamma0 :
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.gamma (indices0 a).succ = some (gamma0 a))
        (hdelta0 :
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a))
        (hchain0 :
    ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc) (hinjective0 : Function.Injective (Fin.cons
        (gamma0 (0 : Fin (p0 + (1 : ℕ)))) delta0)),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (hrho1Proper : IsProperEdgeColoring G rho1) (hrho1One : IsOneEdgeUncolored rho1 e0)
        (hb2Missing : (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v) (hb2TreeEdges :
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) (hb3EdgeEffects :
    ∀ (f : E), rho1 f ≠ sigma f → f ∉ InternalEdges G (TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc)) ∧
    ∃ (c : Fin k) (d : Fin k), sigma f = some c ∧ rho1 f = some d ∧ (c ∈
        (ExtensionBaseRestorationIndices ett v hvFinal).biUnion fun (t : Fin ett.rounds) ↦
        ett.series.data.stored t.succ) ∧ d ∈ (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ)
        (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (hjTreeIndex : jSlot.castSucc.succ = jSlot.succ.castSucc) (hseedTj :
        TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (hseedTerminal
        : seed.vertex (Fin.last seed.length) = v) (hTjQ : TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc) (ett.series.data.tree q.succ.castSucc))
        (hseedVertexBefore :
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore T v hvFinal) (segmentVertexBefore :
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore T v hvFinal)
        (transportSeedRoute :
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho1 S seed) (commonPrefix :
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B),
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0) (hclosure : TashkinovClosure rho1 seed TjPrime)
        (hprimeElementary : ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime))
        (hseedPrime : TreeSequenceInitialSegment seed TjPrime) (hterminalPrime : v ∈
        TreeSequenceVertexSet TjPrime) (hqLast : indices0 (Fin.last p0) = q) (hsupport0 :
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.chosenVertex (indices0 a).succ = some v) (hkind0 :
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.kind (indices0 a).succ = some
        TashkinovExtensionKind.PE) (hstored0 :
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.stored (indices0 a).succ = (insert (gamma0 a)
        ({delta0 a} : Finset (Fin k)) : Finset (Fin k))) (hb1Tj : StableColoringBeforeVertex
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ (TashkinovStoredColors
        ett.series.data jSlot.castSucc) (ett.series.data.coloring jSlot.castSucc) rho1)
        (hcaseTwoPointwise :
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, (MissingColors G rho1 x ∩ supportColors :
        Finset (Fin k)) = ∅) (hsupportSet : supportColors = (ExtensionBaseSupportClass ett v
        hvFinal v).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ)
        (hterminalClass : q ∈ ExtensionBaseSupportClass ett v hvFinal v) (hgammaLast : gamma0
        (Fin.last p0) = gamma),
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ)));
    ∀ (hgammaSupport : gamma ∈ supportColors) (hdeltaSupport : delta ∈ supportColors)
        (hgammaFirstSupport : gammaFirst ∈ supportColors) (hgammaDelta : gamma ≠ delta),
    let restorationColors : Finset (Fin k) := (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ;
    ∀ (hterminalColorsNotRestored : gamma ∉ restorationColors ∧ delta ∉ restorationColors)
        (hsupportColors :
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → gammaS ∈ supportColors ∧ deltaS ∈ supportColors) (hdeltaEarlier :
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → delta ≠ gammaS ∧ delta ≠ deltaS) (hpreterminalPackage : (0 : ℕ) < p0 →
    ∃ (preterminalSlot : Fin ett.rounds), (↑preterminalSlot : ℕ) < (↑q : ℕ) ∧ preterminalSlot ∈
        (ExtensionBaseSupportClass ett v hvFinal v).erase q ∧ ett.series.data.delta
        preterminalSlot.succ = some gamma) (hb4Earlier :
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → ETTStrongInterchangeable ett s v rho1 gammaS deltaS) (hsupportComponentOrder
        :
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS →
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree s.succ.castSucc), x ≠ v →
    ∀ (y : V), Sum.inl y ∈ TwoColorComponent G rho1 gammaS deltaS (Sum.inl x) → y ∈
        TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) (hterminalInclusion :
        MissingColors G (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho1 v ∪
        ({ gammaFirst } : Finset (Fin k))) (hb2EdgesFromSeed :
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → rho1
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) (hdeltaPhiJ : delta ∉
        TreeMissingColors (ett.series.data.coloring jSlot.castSucc) (ett.series.data.tree
        jSlot.succ.castSucc)) (hterminalSeed : v ∈ TreeSequenceVertexSet seed) (hseedN :
        TreeSequenceInitialSegment seed (ett.series.data.tree q.succ.castSucc)) (fN : E)
        (hfNterminal : Incident G v fN) (hphiNProper : IsProperEdgeColoring G
        (ett.series.data.coloring q.succ)) (hphiNOne : IsOneEdgeUncolored
        (ett.series.data.coloring q.succ) e0) (hgammaBoundary : BoundaryColorEdges G
        (ett.series.data.coloring q.succ) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) gamma = ({ fN } : Finset E)) (hdeltaLocation :
    ∀ f ∈ BoundaryColorEdges G (ett.series.data.coloring q.succ) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) delta,
    ∃ y ∈ TreeSequenceVertexSet seed, Incident G y f) (hdeltaMissing : delta ∈ MissingColors G
        rho1 v) (hterminalIntersection' : (MissingColors G rho1 v ∩ supportColors : Finset (Fin
        k)) = ({ delta } : Finset (Fin k))),
    let controlled : Finset (Fin k) := TreeMissingColors (ett.series.data.coloring q.succ)
        (ett.series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors ett.series.data q.succ;
    ∀ (hgammaControlled : gamma ∈ controlled) (hdeltaControlled : delta ∈ controlled)
        (hsigmaControlled : StableColoring (ett.series.data.tree q.succ.castSucc) controlled
        (ett.series.data.coloring q.succ) sigma),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (a b : V ⊕ E) (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (hcomponentPath :
        componentPath.IsPath) (hcomponentSupport : {z : V ⊕ E | z ∈ componentPath.support} = C)
        (hxOutside : x ∉ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪
        TreeSequenceVertexSet TjPrime) (htwoN :
    ∃ y ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), y ≠ v ∧ Sum.inl y ∈
        componentPath.support) (u : V) (exitPath : (TwoColorIncidenceGraph G rho1 gamma
        delta).Walk (Sum.inl x) (Sum.inl u)) (hexitPath : exitPath.IsPath) (hexitLength : (2 : ℕ)
        ≤ exitPath.length) (hexitSupport :
    ∀ y ∈ exitPath.support, y ∈ componentPath.support) (hexitIntersection :
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet
        TjPrime, Sum.inl w ∈ exitPath.support ↔ w = u) (hexitBoundary :
    ∃ g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)
        ∪ TreeSequenceVertexSet TjPrime) gamma, Incident G u g ∧ Sum.inr g ∈ exitPath.support)
        (huNotFN : ¬Incident G u fN) (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (huOutside : u
        ∉ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) (hdegree : MaximumDegree G
        + (1 : ℕ) ≤ k) (beta : Fin k) (hbeta : beta ∈ MissingColors G rho1 u) (huErase : u ∈
        (TreeSequenceVertexSet TjPrime).erase v) (hbetaSupport : beta ∉ supportColors)
        (hbetaGammaFirst : beta ≠ gammaFirst) (hbetaTerminal : beta ∉ MissingColors G rho1 v)
        (huSeed : u ∉ TreeSequenceVertexSet seed),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (hpreviousTj :
    ∀ (hjPositive : (0 : ℕ) < (↑jSlot : ℕ)), TreeSequenceInitialSegment Tprevious
        (ett.series.data.tree jSlot.succ.castSucc)) (hpreviousStrict :
    ∀ (hjPositive : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length), False

private abbrev helperContinuation7819Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hMP : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds)
        (hlower : LowerRoundInductionHypothesis G k e0 ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k) (hsigmaProper : IsProperEdgeColoring G sigma) (hsigmaOne
        : IsOneEdgeUncolored sigma e0) (w : V) (hw : w ∈ TreeSequenceVertexSet
        (ett.series.data.tree (Fin.last ett.rounds).castSucc)) (hwComponent : Sum.inl w ∈
        TwoColorComponent G sigma gamma delta (Sum.inl v)) (hwNe : ¬w = v),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hqSucc : q.succ = Fin.last ett.rounds)
        (hqKind : ett.series.data.kind q.succ = some TashkinovExtensionKind.PE) (hqVertex :
        ett.series.data.chosenVertex q.succ = some v) (hqGamma : ett.series.data.gamma q.succ =
        some gamma) (hqDelta : ett.series.data.delta q.succ = some delta) (hvStage : v ∈
        TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) (hvFinal : v ∈
        TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) +
        (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hjSlot : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (hsigmaTerminal :
        StableColoring (ett.series.data.tree q.succ.castSucc) (TashkinovStoredColors
        ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma) (segmentTrans :
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) (stepSegment :
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (0 : ℕ) < (↑i : ℕ) → TreeSequenceInitialSegment
        (ett.series.data.tree i.castSucc) (ett.series.data.tree i.succ)) (stageToStage :
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) (vertexTransfer :
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) (hdeltaExclusion : (
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
        (ett.series.data.tree jSlot.succ.castSucc)) (hPEStored :
    ∀ (t : Fin ett.rounds) (gammaT deltaT : Fin k), ett.series.data.kind t.succ = some
        TashkinovExtensionKind.PE → ett.series.data.gamma t.succ = some gammaT →
        ett.series.data.delta t.succ = some deltaT → ett.series.data.stored t.succ = (insert
        gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k))) (trace :
        ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)) (hqActive : q ∈ ExtensionBaseActiveIndices ett
        v hvFinal) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin
        (p0 + (1 : ℕ)) → Fin k) (hincreasing0 :
    ∀ (a b : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
        (hclass0 :
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) (hgamma0 :
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.gamma (indices0 a).succ = some (gamma0 a))
        (hdelta0 :
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a))
        (hchain0 :
    ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc) (hinjective0 : Function.Injective (Fin.cons
        (gamma0 (0 : Fin (p0 + (1 : ℕ)))) delta0)),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (hrho1Proper : IsProperEdgeColoring G rho1) (hrho1One : IsOneEdgeUncolored rho1 e0)
        (hb2Missing : (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v) (hb2TreeEdges :
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) (hb3EdgeEffects :
    ∀ (f : E), rho1 f ≠ sigma f → f ∉ InternalEdges G (TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc)) ∧
    ∃ (c : Fin k) (d : Fin k), sigma f = some c ∧ rho1 f = some d ∧ (c ∈
        (ExtensionBaseRestorationIndices ett v hvFinal).biUnion fun (t : Fin ett.rounds) ↦
        ett.series.data.stored t.succ) ∧ d ∈ (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ)
        (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalAt : (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = v)
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (hjTreeIndex : jSlot.castSucc.succ = jSlot.succ.castSucc) (hseedTj :
        TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (hseedTerminal
        : seed.vertex (Fin.last seed.length) = v) (hTjQ : TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc) (ett.series.data.tree q.succ.castSucc))
        (hseedVertexBefore :
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore T v hvFinal) (segmentVertexBefore :
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore T v hvFinal)
        (transportSeedRoute :
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho1 S seed) (commonPrefix :
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B),
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0) (hclosure : TashkinovClosure rho1 seed TjPrime)
        (hprimeElementary : ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime))
        (hseedPrime : TreeSequenceInitialSegment seed TjPrime) (hterminalPrime : v ∈
        TreeSequenceVertexSet TjPrime) (hqLast : indices0 (Fin.last p0) = q) (hsupport0 :
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.chosenVertex (indices0 a).succ = some v) (hkind0 :
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.kind (indices0 a).succ = some
        TashkinovExtensionKind.PE) (hstored0 :
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.stored (indices0 a).succ = (insert (gamma0 a)
        ({delta0 a} : Finset (Fin k)) : Finset (Fin k))) (hterminalIntersection : (MissingColors G
        rho1 v ∩ supportColors : Finset (Fin k)) = ({delta0 (Fin.last p0)} : Finset (Fin k)))
        (hb1Tj : StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v
        hterminalJ (TashkinovStoredColors ett.series.data jSlot.castSucc)
        (ett.series.data.coloring jSlot.castSucc) rho1) (hcaseTwoPointwise :
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, (MissingColors G rho1 x ∩ supportColors :
        Finset (Fin k)) = ∅) (hsupportSet : supportColors = (ExtensionBaseSupportClass ett v
        hvFinal v).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ)
        (hterminalClass : q ∈ ExtensionBaseSupportClass ett v hvFinal v) (hgammaLast : gamma0
        (Fin.last p0) = gamma) (hdeltaLast : delta0 (Fin.last p0) = delta),
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ)));
    ∀ (hgammaSupport : gamma ∈ supportColors) (hdeltaSupport : delta ∈ supportColors)
        (hgammaFirstSupport : gammaFirst ∈ supportColors) (hgammaDelta : gamma ≠ delta),
    let restorationColors : Finset (Fin k) := (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ;
    ∀ (hterminalColorsNotRestored : gamma ∉ restorationColors ∧ delta ∉ restorationColors)
        (hsupportColors :
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → gammaS ∈ supportColors ∧ deltaS ∈ supportColors) (hdeltaEarlier :
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → delta ≠ gammaS ∧ delta ≠ deltaS) (hpreterminalPackage : (0 : ℕ) < p0 →
    ∃ (preterminalSlot : Fin ett.rounds), (↑preterminalSlot : ℕ) < (↑q : ℕ) ∧ preterminalSlot ∈
        (ExtensionBaseSupportClass ett v hvFinal v).erase q ∧ ett.series.data.delta
        preterminalSlot.succ = some gamma) (hb4Earlier :
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → ETTStrongInterchangeable ett s v rho1 gammaS deltaS) (hsupportComponentOrder
        :
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS →
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree s.succ.castSucc), x ≠ v →
    ∀ (y : V), Sum.inl y ∈ TwoColorComponent G rho1 gammaS deltaS (Sum.inl x) → y ∈
        TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) (hterminalInclusion :
        MissingColors G (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho1 v ∪
        ({ gammaFirst } : Finset (Fin k))) (hb2EdgesFromSeed :
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → rho1
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) (hdeltaPhiJ : delta ∉
        TreeMissingColors (ett.series.data.coloring jSlot.castSucc) (ett.series.data.tree
        jSlot.succ.castSucc)) (hterminalSeed : v ∈ TreeSequenceVertexSet seed), False

private abbrev helperCaseContinuation8566Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (_ :
        LowerRoundInductionHypothesis G k e0 ett.rounds) (v : V) (sigma : PartialEdgeColoring E
        k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (_ :
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) (_ :
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma)
        (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 :
        ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (_ : (
    ∀ v_1 ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.castSucc.succ)).erase v,
        MissingColors G (trace.coloring (Fin.last trace.steps)) v_1 = MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v_1) ∧ MissingColors G (trace.coloring (Fin.last
        trace.steps)) v = MissingColors G sigma v),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v) (_ :
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) (terminalPosition :
        Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : jSlot.castSucc.succ = jSlot.succ.castSucc) (_ : TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc)) (_ : seed.vertex (Fin.last seed.length) = v)
        (_ :
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) (TjPrime : TreeSequence G e0) (_ :
        indices0 (Fin.last p0) = q) (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (b : Fin
        (p0 + (1 : ℕ))) (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b) (_ : u
        ∉ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
    ∀ (_ : StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) (traceB.coloring (Fin.last traceB.steps))) (_ : (
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∪ TreeVerticesBefore
        TjPrime u huPrime, MissingColors G (traceB.coloring (Fin.last traceB.steps)) x =
        MissingColors G rho1 x) ∧
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), (ett.series.data.tree
        jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex z = u ∧ (↑a :
        ℕ) < (↑z : ℕ) ∧ TjPrime.edge a = f) → traceB.coloring (Fin.last traceB.steps) f = rho1 f)
        (_ : IsProperEdgeColoring G rho2) (_ : IsOneEdgeUncolored rho2 e0) (uPosition : Fin
        (TjPrime.length + (1 : ℕ))) (_ : TjPrime.vertex uPosition = u) (huPositionPositive : (1 :
        ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed U) (_ : TashkinovAugmentationSequence rho2 seed U) (_ :
        MissingColors G (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho2 v ∪
        MissingColors G rho2 u),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ :
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), TreeSequenceInitialSegment Tprevious (ett.series.data.tree
        jSlot.succ.castSucc)) (_ :
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length) (_ :
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), TreeSequenceInitialSegment Tprevious seed) (_ :
        TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) seed
        (ett.series.data.tree jSlot.succ.castSucc)), False

theorem helper_branch_3512.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k)
        (hvFinal : v ∈ TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v
        hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (a b : V ⊕ E) (spanningPath : (TwoColorIncidenceGraph G rho1 gamma delta).Walk a b),
        spanningPath.IsPath → {x : V ⊕ E | x ∈ spanningPath.support} = TwoColorComponent G rho1
        gamma delta (Sum.inl v) → Sum.inl v ∈ spanningPath.support → Sum.inl v = b →
    ∃ (endpoint : V ⊕ E) (componentPath : H.Walk (Sum.inl v) endpoint), componentPath.IsPath ∧
        {z : V ⊕ E | z ∈ componentPath.support} = C := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v gamma delta sigma hvFinal trace rho1 H C a b
      spanningPath hspanningPath hspanningSupport hvSpanning hvb
  subst b
  refine ⟨a, spanningPath.reverse, hspanningPath.reverse, ?_⟩
  ext z
  rw [SimpleGraph.Walk.support_reverse]
  simpa using Set.ext_iff.mp hspanningSupport z

theorem helper_hfNComponent_3517.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (fN : E),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    H.Adj (Sum.inl v) (Sum.inr fN) →
    Sum.inr fN ∈ C := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v gamma delta sigma hvFinal trace rho1 fN H C hfNAdj
  change H.connectedComponentMk (Sum.inr fN) =
    H.connectedComponentMk (Sum.inl v)
  exact
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hfNAdj).symm

theorem helper_hcomponentNonempty_3523.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k)
        (hvFinal : v ∈ TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v
        hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (fN : E),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (endpoint : V ⊕ E) (componentPath : H.Walk (Sum.inl v) endpoint), componentPath.IsPath →
        {z : V ⊕ E | z ∈ componentPath.support} = C → Sum.inr fN ∈ C → ¬componentPath.Nil := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v gamma delta sigma hvFinal trace rho1 fN H C
      endpoint componentPath hcomponentPath hcomponentSupport hfNComponent hnil
  have hfNSupport : Sum.inr fN ∈ componentPath.support := by
    change Sum.inr fN ∈ {z | z ∈ componentPath.support}
    rw [hcomponentSupport]
    exact hfNComponent
  cases hnil
  simp at hfNSupport

theorem helper_hxNe_3545.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k)
        (hvFinal : v ∈ TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v
        hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)), componentPath.IsPath →
        {z : V ⊕ E | z ∈ componentPath.support} = C → ¬componentPath.Nil → (0 : ℕ) <
        componentPath.length → Sum.inl x ∈ C → (
    ∀ (z : V ⊕ E), H.Adj (Sum.inl x) z → z = componentPath.getVert (componentPath.length - (1 :
        ℕ))) → x ≠ v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v gamma delta sigma hvFinal trace rho1 H C x
      componentPath hcomponentPath hcomponentSupport hcomponentNonempty hcomponentPositive
      hendpointC hendpointNeighbor hxv
  subst x
  have hnil : componentPath.Nil :=
    hcomponentPath.nil_iff_eq.mpr rfl
  exact hcomponentNonempty hnil

theorem helper_hbetaSupport_3628.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (sigma : PartialEdgeColoring E k),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v hvFinal
        sigma) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0), (
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, (MissingColors G rho1 x ∩ supportColors :
        Finset (Fin k)) = ∅) →
    ∀ (u : V),
    ∀ beta ∈ MissingColors G rho1 u, u ∈ (TreeSequenceVertexSet TjPrime).erase v → beta ∉
        supportColors := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v sigma this hvFinal trace p0 indices0 rho1
      supportColors TjPrime hcaseTwoPointwise u beta hbeta huErase hbetaIn
  have hmember : beta ∈ MissingColors G rho1 u ∩ supportColors :=
    Finset.mem_inter.mpr ⟨hbeta, hbetaIn⟩
  rw [hcaseTwoPointwise u huErase] at hmember
  simp at hmember

theorem helper_hcaseTwoObservationPackage_3695.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0) (fN : E),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (exitPath :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)), exitPath.IsPath
        → (2 : ℕ) ≤ exitPath.length → (
    ∀ y ∈ exitPath.support, y ∈ componentPath.support) → (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet
        TjPrime, Sum.inl w ∈ exitPath.support ↔ w = u) → (
    ∃ g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)
        ∪ TreeSequenceVertexSet TjPrime) gamma, Incident G u g ∧ Sum.inr g ∈ exitPath.support) →
        ¬Incident G u fN → u ∈ TreeSequenceVertexSet TjPrime → u ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) →
    ∀ beta ∈ MissingColors G rho1 u, beta ∉ supportColors →
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
        beta) → (u ∈ TreeSequenceVertexSet TjPrime ∧ u ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) ∧ (exitPath.IsPath ∧ (2 : ℕ) ≤ exitPath.length ∧ (
    ∀ y ∈ exitPath.support, y ∈ componentPath.support) ∧ (
    ∀ y ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet
        TjPrime, Sum.inl y ∈ exitPath.support ↔ y = u) ∧ (
    ∃ g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)
        ∪ TreeSequenceVertexSet TjPrime) gamma, Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
        ¬Incident G u fN) ∧ (beta ∈ MissingColors G rho1 u ∧ beta ∉ supportColors) ∧ z ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∧ (ett.series.data.tree
        jSlot.succ.castSucc).vertex zPosition = z ∧ seed.length ≤ (↑zPosition : ℕ) ∧ ((seed.length
        < (↑zPosition : ℕ) ∧ beta ∈ MissingColors G rho1 z ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → (↑r : ℕ) < (↑zPosition : ℕ) → beta ∉ MissingColors G rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).vertex r)) ∨ zPosition = Fin.last (ett.series.data.tree
        jSlot.succ.castSucc).length ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → beta ∉ MissingColors G rho1 ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) ∧
        (
    ∀ y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z hz, beta ∉ MissingColors
        G rho1 y) ∧
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → (↑a :
        ℕ) < (↑zPosition : ℕ) → rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) ≠ some
        beta := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 rho1 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed supportColors TjPrime fN H x
      componentPath u exitPath hexitPath hexitLength hexitSupport hexitIntersection hexitBoundary
      huNotFN huPrime huOutside beta hbeta hbetaSupport z hz zPosition hzPosition hzAfter
      hzChoice hzBefore hzEdges
  exact ⟨⟨huPrime, huOutside⟩,
    ⟨hexitPath, hexitLength, hexitSupport, hexitIntersection,
      hexitBoundary, huNotFN⟩,
    ⟨hbeta, hbetaSupport⟩,
    ⟨hz, hzPosition, hzAfter, hzChoice, hzBefore, hzEdges⟩⟩

theorem helper_hgammaFirstZero_3790.{u_1, u_2} :
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
        → Fin ett.rounds) (gamma0 _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), (1 :
        ℕ) ≤ (↑terminalPosition : ℕ) → (↑terminalPosition : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length → gamma0 (Fin.last p0) = gamma →
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ)));
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))), p0 = (0 : ℕ) → gammaFirst = gamma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound hgammaLast gammaFirst H x
      componentPath u exitPath zPosition hp0
  have hindex : (0 : Fin (p0 + 1)) = Fin.last p0 := by
    apply Fin.ext
    exact hp0.symm
  exact (congrArg gamma0 hindex).trans hgammaLast

theorem helper_hvBeforePrime_3939.{u_1, u_2} :
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
    ⟩ : Fin ett.rounds); (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound; seed.vertex
        (Fin.last seed.length) = v →
    ∀ (TjPrime : TreeSequence G e0), TreeSequenceInitialSegment seed TjPrime → v ∈
        TreeSequenceVertexSet seed →
    ∀ (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime) (uPosition : Fin (TjPrime.length +
        (1 : ℕ))), TjPrime.vertex uPosition = u0 → seed.length < (↑uPosition : ℕ) → v ∈
        TreeVerticesBefore TjPrime u0 huPrime0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot vertexTransfer terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedTerminal TjPrime hseedPrime hterminalSeed u0 huPrime0
      uPosition huPosition hseedBeforeU
  unfold TreeVerticesBefore
  apply Finset.mem_filter.mpr
  let vPosition : Fin (TjPrime.length + 1) :=
    Fin.castLE (Nat.succ_le_succ hseedPrime.1)
      (Fin.last seed.length)
  refine ⟨vertexTransfer hseedPrime hterminalSeed,
    vPosition, uPosition, ?_, huPosition, ?_⟩
  · exact (hseedPrime.2.1 (Fin.last seed.length)).trans
      hseedTerminal
  · change seed.length < uPosition.val
    exact hseedBeforeU

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_hUPrime_3958.{u_1, u_2} :
    SharedFacts.ExtensionBaseStepLemmas.uPrimeStatement.{u_1, u_2} :=
  SharedFacts.ExtensionBaseStepLemmas.uPrime.{u_1, u_2}




/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_huU_4024.{u_1, u_2} :
    SharedFacts.ExtensionBranchPreparation.huUStatement.{u_1, u_2} :=
  SharedFacts.ExtensionBranchPreparation.huU.{u_1, u_2}

theorem helper_segmentVertexBefore_4061.{u_1, u_2} :
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
    ∀ (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
        (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound; (
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ) →
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {y : V}, y ∈ TreeSequenceVertexSet A → y ∈ TreeVerticesBefore (ett.series.data.tree
        jSlot.succ.castSucc) v hterminalJ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hterminalJ terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedVertexBefore A hAseed hAlen y hyA
  obtain ⟨hAseedLen, hAseedVertices, -⟩ := hAseed
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hyA
  obtain ⟨i, rfl⟩ := hyA
  have hi : (Fin.castLE (Nat.succ_le_succ hAseedLen) i).val <
      seed.length := by
    change i.val < seed.length
    exact lt_of_le_of_lt (Nat.lt_succ_iff.mp i.isLt) hAlen
  rw [← hAseedVertices i]
  exact hseedVertexBefore _ hi

theorem helper_transportSeedRoute_4083.{u_1, u_2} :
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
    ∀ (rho3 : PartialEdgeColoring E k), (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentation (ett.series.data.coloring jSlot.castSucc) A
        B → TreeSequenceInitialSegment B seed → TashkinovAugmentation rho3 A B) →
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho3 S seed := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      rho3 transportSeedStep S hroute
  exact TashkinovAugmentationSequence.transport transportSeedStep hroute

theorem helper_hzChoiceForContradiction_4107.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma :
        PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (beta0 : Fin k) (z0 : V) (zPosition0 : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))), ((seed.length < (↑zPosition0 : ℕ) ∧ beta0 ∈
        MissingColors G rho1 z0 ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → (↑r : ℕ) < (↑zPosition0 : ℕ) → beta0 ∉ MissingColors G rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).vertex r)) ∨ zPosition0 = Fin.last (ett.series.data.tree
        jSlot.succ.castSucc).length ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → beta0 ∉ MissingColors G rho1 ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) →
        zPosition0 = Fin.last (ett.series.data.tree jSlot.succ.castSucc).length ∨ (↑zPosition0 :
        ℕ) < (↑(Fin.last (ett.series.data.tree jSlot.succ.castSucc).length) : ℕ) ∧ beta0 ∈
        MissingColors G rho1 z0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace rho1 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed beta0 z0 zPosition0 hzChoice0
  rcases hzChoice0 with hfirst | hlast
  · by_cases heq : zPosition0 = Fin.last
        (ett.series.data.tree jSlot.succ.castSucc).length
    · exact Or.inl heq
    · right
      refine ⟨?_, hfirst.2.1⟩
      exact lt_of_le_of_ne
        (Fin.le_iff_val_le_val.mp (Fin.le_last zPosition0))
        (fun hval => heq (Fin.ext hval))
  · exact Or.inl hlast.1

/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_hUPrime_4274.{u_1, u_2} :
    SharedFacts.ExtensionBaseStepLemmas.uPrimeStatement.{u_1, u_2} :=
  SharedFacts.ExtensionBaseStepLemmas.uPrime.{u_1, u_2}

theorem helper_hZTj_4280.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition0 : ℕ))
      (hzPositionBound :
        (↑zPosition0 : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let Z : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑zPosition0 : ℕ)
        hzPositionPositive hzPositionBound;
    TreeSequenceInitialSegment Z (ett.series.data.tree jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot zPosition0 hzPositionPositive hzPositionBound Z
  refine ⟨hzPositionBound, ?_, ?_⟩
  · intro i
    simp [Z, TreeSequencePrefix]
  · intro i
    simp [Z, TreeSequencePrefix]



theorem helper_hterminalMissingEq_4347.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma :
        PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (TjPrime : TreeSequence G e0) (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime) (z0 :
        V) (hz0 : z0 ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (rho3 :
        PartialEdgeColoring E k), (
    ∀ y ∈ ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 ∪ ({ z0 } :
        Finset V) ∪ (TreeVerticesBefore TjPrime u0 huPrime0 ∪ ({ u0 } : Finset V))).erase
        u0).erase z0, MissingColors G rho3 y = MissingColors G rho1 y) → ¬z0 = v → v ∈
        TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 → v ≠ u0 →
        MissingColors G rho3 v = MissingColors G rho1 v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace rho1 TjPrime u0 huPrime0 z0 hz0 rho3 hd2Missing hzv
      hterminalBeforeZ hterminalNeU
  apply hd2Missing v
  apply Finset.mem_erase.mpr
  refine ⟨(fun hvz => hzv hvz.symm),
    Finset.mem_erase.mpr ⟨hterminalNeU, ?_⟩⟩
  exact Finset.mem_union_left _
    (Finset.mem_union_left _ hterminalBeforeZ)

theorem helper_hterminalInclusionRho3_4355.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (gamma0 : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ)));
    MissingColors G (ett.series.data.coloring jSlot.castSucc) v ⊆
        MissingColors G rho1 v ∪ ({ gammaFirst } : Finset (Fin k)) →
    ∀ (u0 : V) (rho3 : PartialEdgeColoring E k),
    gammaFirst ∈ MissingColors G rho3 u0 →
    MissingColors G rho3 v = MissingColors G rho1 v →
    MissingColors G (ett.series.data.coloring jSlot.castSucc) v ⊆
      MissingColors G rho3 v ∪ MissingColors G rho3 u0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace p0 gamma0 rho1 gammaFirst hterminalInclusion u0 rho3
      hd3 hterminalMissingEq c hc
  rcases Finset.mem_union.mp (hterminalInclusion hc) with
    hcTerminal | hcGamma
  · exact Finset.mem_union_left _ (hterminalMissingEq.symm ▸ hcTerminal)
  · apply Finset.mem_union_right
    have hcgamma : c = gammaFirst := Finset.mem_singleton.mp hcGamma
    simpa [hcgamma] using hd3


/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_huU_4386.{u_1, u_2} :
    SharedFacts.ExtensionBranchPreparation.huUStatement.{u_1, u_2} :=
  SharedFacts.ExtensionBranchPreparation.huU.{u_1, u_2}


/-- Existing proof-module entry point for the shared interface or construction. -/
theorem helper_prefixSelf_4429.{u_1, u_2} :
    SharedFacts.ExtensionBaseStepLemmas.prefixSelfStatement.{u_1, u_2} :=
  SharedFacts.ExtensionBaseStepLemmas.prefixSelf.{u_1, u_2}

theorem helper_branch_4837.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k),
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree (Fin.last ett.rounds).castSucc), w = v →
        Sum.inl w ∈ TwoColorComponent G sigma gamma delta (Sum.inl v) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v gamma delta sigma w hw hwv
  subst w
  change Sum.inl v ∈
    (TwoColorIncidenceGraph G sigma gamma delta).connectedComponentMk
      (Sum.inl v)
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl

theorem helper_hXY_5375.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma :
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
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds), (
    ∀ v_1 ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.castSucc.succ)).erase v,
        MissingColors G (trace.coloring (Fin.last trace.steps)) v_1 = MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v_1) ∧ MissingColors G (trace.coloring (Fin.last
        trace.steps)) v = MissingColors G sigma v →
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps); (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (_ :
        (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (_ : (↑terminalPosition : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length) (TjPrime : TreeSequence G e0) (u : V) (huPrime : u ∈
        TreeSequenceVertexSet TjPrime) (b : Fin (p0 + (1 : ℕ))) (traceB :
        ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps); ((
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∪ TreeVerticesBefore
        TjPrime u huPrime, MissingColors G (traceB.coloring (Fin.last traceB.steps)) x =
        MissingColors G rho1 x) ∧
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), (ett.series.data.tree
        jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex z = u ∧ (↑a :
        ℕ) < (↑z : ℕ) ∧ TjPrime.edge a = f) → traceB.coloring (Fin.last traceB.steps) f = rho1 f)
        →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition :
        ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (M : TreeSequence G e0), (
    ∀ (A : TreeSequence G e0) (r : ℕ) (hr : (1 : ℕ) ≤ r) (hrA : r + (1 : ℕ) ≤ A.length),
        TreeSequenceInitialSegment (TreeSequencePrefix A r hr (Nat.le_trans (Nat.le_succ r) hrA))
        (TreeSequencePrefix A (r + (1 : ℕ)) (
    by omega
    ) hrA)) →
    ∀ (n : ℕ) (hnU : U.length ≤ n) (hnM hnSuccM : n + (1 : ℕ) ≤ M.length) (hnM' : n ≤ M.length),
    let X : TreeSequence G e0 := TreeSequencePrefix M n (Nat.le_trans U.positive hnU) hnM';
    let Y : TreeSequence G e0 := TreeSequencePrefix M (n + (1 : ℕ)) (
    by omega
    ) hnSuccM;
    let mIndex : Fin M.length := (⟨n,
    by
          have := GoldbergSeymour.TreeSequence.positive M
          omega
    ⟩ : Fin M.length);
    ∀ (i : Fin Tj0.length), M.edge mIndex = Tj0.edge i →
    ∀ (c : Fin k), ett.series.data.coloring jSlot.castSucc (Tj0.edge i) = some c → c ∈
        TreeMissingColors rho2 X → TashkinovAugmentation rho2 X Y := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace p0 indices0 hb2 rho1 hb2TreeEdges terminalPosition
      hterminalPositionPositive hterminalPositionBound TjPrime u huPrime b traceB rho2 c2
      uPosition huPositionPositive huPositionBound U Tj0 M prefixPrefix n hnU hnM hnSuccM hnM' X
      Y mIndex i hedgeMTj c hcolorTj hmissingX
  have hlenXY : Y.length = X.length + 1 := by
    change n + 1 = n + 1
    rfl
  refine ⟨hlenXY, ?_, c, ?_, hmissingX⟩
  · simpa [X, Y] using prefixPrefix M n
      (Nat.le_trans U.positive hnU) hnSuccM
  · have hfixedTj : rho2 (Tj0.edge i) =
        ett.series.data.coloring jSlot.castSucc
          (Tj0.edge i) := by
      have hc2 : rho2 (Tj0.edge i) = rho1 (Tj0.edge i) := by
        apply c2.2
        apply Or.inl
        exact ⟨i, by simp [Tj0]⟩
      have hb2 := hb2TreeEdges
        (Fin.cast (by simp [Tj0]) i)
      simpa [Tj0] using hc2.trans (hb2.1.trans hb2.2)
    have hcolorM : rho2 (M.edge mIndex) = some c := by
      rw [hedgeMTj]
      exact hfixedTj.trans hcolorTj
    change rho2 (M.edge _) = some c
    convert hcolorM using 1
    apply congrArg rho2
    apply congrArg M.edge
    apply Fin.ext
    rfl

theorem helper_hXY_6689.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
        TreeSequence G e0), (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → rho1
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V) (_ : (TwoColorIncidenceGraph G rho1 gamma
        delta).Walk (Sum.inl x) (Sum.inl u0)) (zPosition0 : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (rho3 : PartialEdgeColoring E k), (
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) ∧ (↑a :
        ℕ) < (↑zPosition0 : ℕ) ∧ (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u0 ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → rho3 f = rho1 f) →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition :
        ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length) (hzPositionPositive : (1 : ℕ) ≤
        (↑zPosition0 : ℕ)) (hzPositionBound : (↑zPosition0 : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑zPosition0 : ℕ) hzPositionPositive hzPositionBound; TreeSequenceInitialSegment Z
        (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (M : TreeSequence G e0), (
    ∀ (A : TreeSequence G e0) (q0 : ℕ) (hq0 : (1 : ℕ) ≤ q0) (hqA : q0 + (1 : ℕ) ≤ A.length),
        TreeSequenceInitialSegment (TreeSequencePrefix A q0 hq0 (Nat.le_trans (Nat.le_succ q0)
        hqA)) (TreeSequencePrefix A (q0 + (1 : ℕ)) (
    by omega
    ) hqA)) →
    ∀ (n : ℕ) (hnU : U.length ≤ n) (hnM hnSuccM : n + (1 : ℕ) ≤ M.length) (hnM' : n ≤ M.length),
    let X : TreeSequence G e0 := TreeSequencePrefix M n (Nat.le_trans U.positive hnU) hnM';
    let Y : TreeSequence G e0 := TreeSequencePrefix M (n + (1 : ℕ)) (
    by omega
    ) hnSuccM;
    let j : Fin M.length := (⟨n,
    by
          have := GoldbergSeymour.TreeSequence.positive M
          omega
    ⟩ : Fin M.length);
    ∀ (i : Fin Z.length), M.edge j = Z.edge i → seed.length ≤ (↑i : ℕ) →
    ∀ (c : Fin k), ett.series.data.coloring jSlot.castSucc (Z.edge i) = some c → c ∈
        TreeMissingColors rho3 X → TashkinovAugmentation rho3 X Y := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime
      hb2EdgesFromSeed H x componentPath u exitPath zPosition u0 exitPath0 zPosition0 rho3
      hd2Edges uPosition huPositionPositive huPositionBound hzPositionPositive hzPositionBound U
      Z hZTj M prefixPrefix n hnU hnM hnSuccM hnM' X Y j i hedgeMZ hiSeed c hcolorZ hmissingX
  have hlenXY : Y.length = X.length + 1 := by rfl
  refine ⟨hlenXY, ?_, c, ?_, hmissingX⟩
  · simpa [X, Y] using prefixPrefix M n
      (Nat.le_trans U.positive hnU) hnSuccM
  · let iTj : Fin
        (ett.series.data.tree jSlot.succ.castSucc).length :=
      Fin.castLE hZTj.1 i
    have hiTj : iTj.val < zPosition0.val := by
      change i.val < zPosition0.val
      have hiLt := i.isLt
      simp only [Fin.castSucc_succ, TreeSequencePrefix, Nat.succ_eq_add_one, Z] at hiLt
      exact hiLt
    have hiSeedTj : seed.length ≤ iTj.val := by
      exact hiSeed
    have hedgeTj :
        (ett.series.data.tree jSlot.succ.castSucc).edge iTj =
          Z.edge i := hZTj.2.2 i
    have hfixedZ : rho3 (Z.edge i) =
        ett.series.data.coloring jSlot.castSucc (Z.edge i) := by
      calc
        rho3 (Z.edge i) = rho1 (Z.edge i) :=
          hd2Edges (Z.edge i)
            (Or.inl ⟨iTj, hiSeedTj, hiTj, hedgeTj⟩)
        _ = ett.series.data.coloring
            jSlot.castSucc (Z.edge i) := by
          rw [← hedgeTj]
          exact hb2EdgesFromSeed iTj hiSeedTj
    have hcolorM : rho3 (M.edge j) = some c := by
      rw [hedgeMZ]
      exact hfixedZ.trans hcolorZ
    change rho3 (M.edge _) = some c
    convert hcolorM using 1
    apply congrArg rho3
    apply congrArg M.edge
    apply Fin.ext
    rfl

theorem helper_hdeltaAvoids_5315.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds); ((
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
    ∀ (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds), (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices a) : ℕ) < (↑(indices b) : ℕ)) →
        (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal u ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = r) →
    ∀ (gammaClass deltaClass : Fin (p + (1 : ℕ)) → Fin k), (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gammaClass a)) → (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (deltaClass a)) → u ∈
        TreeSequenceVertexSet T →
    ∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) ≤ (↑b : ℕ) → deltaClass b ≠ gammaClass a := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hdeltaExclusion u p indices hincreasing hclass gammaClass deltaClass
      hgammaClass hdeltaClass huFinal
  exact @helper_hdeltaAvoids_958 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
      (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hdeltaExclusion) (@u) (@p) (@indices)
      (@hincreasing) (@hclass) (@gammaClass) (@deltaClass) (@hgammaClass) (@hdeltaClass)
      (@huFinal)

theorem helper_hseedVertexBefore_5540.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound; seed.vertex
        (Fin.last seed.length) = v → TreeSequenceInitialSegment seed T →
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore T v hvFinal := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot vertexTransfer terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedTerminal hseedFinal i hi
  exact @helper_hseedVertexBefore_2479 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
      (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@vertexTransfer) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTerminal) (@hseedFinal)
      (@i) (@hi)

theorem helper_segmentVertexBefore_5548.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound; (
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore T v hvFinal) →
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore T v hvFinal := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hseedVertexBefore A hAseed hAlen x hxA
  exact @helper_segmentVertexBefore_2493 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
      (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedVertexBefore) (@A)
      (@hAseed) (@hAlen) (@x) (@hxA)

theorem helper_branch_5591.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (sigma : PartialEdgeColoring E k),
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
        (awayMissing ∩ supportColors : Finset (Fin k)) = ∅ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower v sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot hjSlot stepSegment trace p0 indices0 rho1 hrho1Proper
      hrho1One hb1Rho terminalPosition hterminalAt hterminalPositionPositive hterminalPositionBound
      seed hjTreeIndex hseedTj segmentVertexBefore transportSeedRoute commonPrefix supportColors
      hjPositive
  exact @helper_branch_880 (@V) (@E) inferInstance inferInstance inferInstance
    inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
    (@hlower) (@v) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
    (@hjSlot) (@stepSegment) (@trace) (@p0) (@indices0) (@hrho1Proper) (@hrho1One)
    (@hb1Rho) (@terminalPosition) (@hterminalAt) (@hterminalPositionPositive)
    (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@segmentVertexBefore)
    (@transportSeedRoute) (@commonPrefix) (@hjPositive)

theorem helper_hseedBeforeU_5770.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds);
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive
        : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0), TreeSequenceInitialSegment seed TjPrime →
    ∀ (u : V) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex uPosition = u → u ∉
        TreeSequenceVertexSet seed → seed.length < (↑uPosition : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed TjPrime hseedPrime u uPosition huPosition huNotSeed
  exact @helper_hseedBeforeU_2115 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
      (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime) (@hseedPrime) (@u)
      (@uPosition) (@huPosition) (@huNotSeed)

theorem helper_hterminalInclusion_5831.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma :
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
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k), (
    let storedPairs : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ; (MissingColors G sigma v ∩ storedPairs : Finset
        (Fin k)) = ({delta0 (Fin.last p0)} : Finset (Fin k)) ∧ MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v = MissingColors G sigma v \
        ({delta0 (Fin.last p0)} : Finset (Fin k)) ∪ ({gamma0 (0 : Fin (p0 + (1 : ℕ)))} : Finset
        (Fin k))) →
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps); (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v →
    ∀ (u : V) (b : Fin (p0 + (1 : ℕ))) (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u p0
        indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps); gamma0 (0 : Fin
        (p0 + (1 : ℕ))) ∈ MissingColors G (traceB.coloring (Fin.last traceB.steps)) u →
        MissingColors G rho2 v = MissingColors G rho1 v → MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho2 v ∪ MissingColors G
        rho2 u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 hmissing0 rho1 hb2Missing
      u b traceB rho2 c3 hterminalMissingEq
  exact @helper_hterminalInclusion_2787 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0)
      (@gamma0) (@delta0) (@hmissing0) (@hb2Missing) (@u) (@b) (@traceB) (@c3)
      (@hterminalMissingEq)

theorem helper_hvNotPrevious_5841.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal →
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), (1 : ℕ) ≤
        (↑terminalPosition : ℕ) → (↑terminalPosition : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length →
    ∀ (TjPrime : TreeSequence G e0), indices0 (Fin.last p0) = q →
    ∀ (_ : Fin (TjPrime.length + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; (0 : ℕ) <
        (↑jSlot : ℕ) → v ∉ TreeSequenceVertexSet Tprevious := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hjSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound TjPrime hqLast uPosition Tprevious hjPositive
  exact @helper_hvNotPrevious_2347 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
      (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@p0) (@indices0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime)
      (@hqLast) (@uPosition) (@hjPositive)

theorem helper_hpreviousStrict_5854.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds);
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), (ett.series.data.tree
        jSlot.succ.castSucc).vertex terminalPosition = v →
    ∀ (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0) (_ : Fin (TjPrime.length + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ((0 : ℕ) <
        (↑jSlot : ℕ) → v ∉ TreeSequenceVertexSet Tprevious) → ((0 : ℕ) < (↑jSlot : ℕ) →
        TreeSequenceInitialSegment Tprevious (ett.series.data.tree jSlot.succ.castSucc)) → (0 : ℕ)
        < (↑jSlot : ℕ) → Tprevious.length < seed.length := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalAt hterminalPositionPositive
      hterminalPositionBound seed TjPrime uPosition Tprevious hvNotPrevious hpreviousTj hjPositive
  exact @helper_hpreviousStrict_2394 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
      (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0) (@terminalPosition)
      (@hterminalAt) (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime)
      (@uPosition) (@hvNotPrevious) (@hpreviousTj) (@hjPositive)

theorem helper_branch_5870.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) → (ett.series.data.tree (0 : Fin
        (ett.rounds + (2 : ℕ)))).length = (1 : ℕ) → TashkinovClosure (ett.series.data.coloring (0
        : Fin (ett.rounds + (1 : ℕ)))) (ett.series.data.tree (0 : Fin (ett.rounds + (2 : ℕ))))
        (ett.series.data.tree (1 : Fin (ett.rounds + (2 : ℕ)))) → jSlot.castSucc = (0 : Fin
        (ett.rounds + (1 : ℕ))) → TashkinovAugmentationSequence (ett.series.data.coloring (0 : Fin
        (ett.rounds + (1 : ℕ)))) seed (ett.series.data.tree jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hseedTj commonPrefix seedLength initialClosure htarget
  exact @helper_branch_2422 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj)
      (@commonPrefix) (@seedLength) (@initialClosure) (@htarget)

theorem helper_branch_5878.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds);
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive
        : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        jSlot.castSucc.succ = jSlot.succ.castSucc → TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    ∀ (TjPrime : TreeSequence G e0) (_ : Fin (TjPrime.length + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ((0 : ℕ) <
        (↑jSlot : ℕ) → Tprevious.length < seed.length) →
    ∀ (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)) (adjoined : TreeSequence G e0),
        TreeSequenceAdjoinEdge (ett.series.data.tree i.succ.castSucc) choice.edge adjoined →
        TashkinovClosure (ett.series.data.coloring i.succ) adjoined (ett.series.data.tree
        i.succ.succ) → jSlot.castSucc = i.succ → TashkinovAugmentationSequence
        (ett.series.data.coloring i.succ) seed (ett.series.data.tree jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hjTreeIndex hseedTj commonPrefix TjPrime uPosition Tprevious
      hpreviousStrict i choice adjoined adjoinedExactly closedExtension htarget
  exact @helper_branch_2455 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
      (@hjTreeIndex) (@hseedTj) (@commonPrefix) (@TjPrime) (@uPosition)
      (@hpreviousStrict) (@i) (@choice) (@adjoined) (@adjoinedExactly)
      (@closedExtension) (@htarget)

theorem helper_branch_5890.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds);
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive
        : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        jSlot.castSucc.succ = jSlot.succ.castSucc → TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (TjPrime : TreeSequence G e0) (_ : Fin (TjPrime.length + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ((0 : ℕ) <
        (↑jSlot : ℕ) → TreeSequenceInitialSegment Tprevious seed) →
    ∀ (i : Fin ett.rounds), TashkinovClosure (ett.series.data.coloring i.succ)
        (ett.series.data.tree i.succ.castSucc) (ett.series.data.tree i.succ.succ) → jSlot.castSucc
        = i.succ → TashkinovAugmentationSequence (ett.series.data.coloring i.succ) seed
        (ett.series.data.tree jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hjTreeIndex hseedTj TjPrime uPosition Tprevious hpreviousSeed i
      closedExtension htarget
  exact @helper_branch_2490 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
      (@hjTreeIndex) (@hseedTj) (@TjPrime) (@uPosition) (@hpreviousSeed) (@i)
      (@closedExtension) (@htarget)

theorem helper_branch_5903.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds);
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive
        : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        jSlot.castSucc.succ = jSlot.succ.castSucc → TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    ∀ (TjPrime : TreeSequence G e0) (_ : Fin (TjPrime.length + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ((0 : ℕ) <
        (↑jSlot : ℕ) → Tprevious.length < seed.length) →
    ∀ (i : Fin ett.rounds) (available : RevisitingExtensionCertificate ett.series.data i.castSucc)
        (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (ett.series.data.tree
        i.succ.castSucc) available.edge adjoined → TashkinovClosure (ett.series.data.coloring
        i.succ) adjoined (ett.series.data.tree i.succ.succ) → jSlot.castSucc = i.succ →
        TashkinovAugmentationSequence (ett.series.data.coloring i.succ) seed (ett.series.data.tree
        jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hjTreeIndex hseedTj commonPrefix TjPrime uPosition Tprevious
      hpreviousStrict i available adjoined adjoinedExactly closedExtension htarget
  exact @helper_branch_2512 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
      (@hjTreeIndex) (@hseedTj) (@commonPrefix) (@TjPrime) (@uPosition)
      (@hpreviousStrict) (@i) (@available) (@adjoined) (@adjoinedExactly)
      (@closedExtension) (@htarget)

theorem helper_hrightOutside_6001.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds);
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (_ : (1 : ℕ) ≤
        (↑terminalPosition : ℕ)) (_ : (↑terminalPosition : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length) (TjPrime : TreeSequence G e0) (uPosition : Fin
        (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
        (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (M : TreeSequence G e0), TreeSequenceInitialSegment U M →
    ∀ (n : ℕ), U.length ≤ n →
    ∀ (hnM : n + (1 : ℕ) ≤ M.length),
    let mIndex : Fin M.length := (⟨n,
    by
          have := GoldbergSeymour.TreeSequence.positive M
          omega
    ⟩ : Fin M.length);
    ∀ (i : Fin Tj0.length), M.vertex mIndex.succ = Tj0.vertex i.succ → Tj0.vertex i.succ ∉
        TreeSequenceVertexSet U := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound TjPrime uPosition huPositionPositive huPositionBound U Tj0 M
      hleftSegment n hnU hnM mIndex i hvertexMTj
  rw [← hvertexMTj]
  exact hleftSegment.vertex_not_mem_after (Nat.lt_succ_of_le hnU)

theorem helper_hiSeed_6009.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds);
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive
        : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0) (uPosition : Fin (TjPrime.length + (1 : ℕ)))
        (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤
        TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound; TreeSequenceInitialSegment seed U →
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (_ : TreeSequence G e0), TreeSequenceInitialSegment seed Tj0 →
    ∀ (_ : ℕ) (i : Fin Tj0.length), Tj0.vertex i.succ ∉ TreeSequenceVertexSet U → seed.length ≤
        (↑i : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed TjPrime uPosition huPositionPositive huPositionBound U hseedU
      Tj0 M hseedTjSegment n i hrightOutside
  exact @helper_hiSeed_2699 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
      (@TjPrime) (@uPosition) (@huPositionPositive) (@huPositionBound) (@hseedU)
      (@M) (@hseedTjSegment) (@n) (@i) (@hrightOutside)

theorem helper_hXY_6159.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma :
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
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds), (
    ∀ v_1 ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.castSucc.succ)).erase v,
        MissingColors G (trace.coloring (Fin.last trace.steps)) v_1 = MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v_1) ∧ MissingColors G (trace.coloring (Fin.last
        trace.steps)) v = MissingColors G sigma v →
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps); (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (_ :
        (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (_ : (↑terminalPosition : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length) (TjPrime : TreeSequence G e0) (u : V) (huPrime : u ∈
        TreeSequenceVertexSet TjPrime) (b : Fin (p0 + (1 : ℕ))) (traceB :
        ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps); ((
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∪ TreeVerticesBefore
        TjPrime u huPrime, MissingColors G (traceB.coloring (Fin.last traceB.steps)) x =
        MissingColors G rho1 x) ∧
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), (ett.series.data.tree
        jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex z = u ∧ (↑a :
        ℕ) < (↑z : ℕ) ∧ TjPrime.edge a = f) → traceB.coloring (Fin.last traceB.steps) f = rho1 f)
        →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition :
        ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (M : TreeSequence G e0), (
    ∀ (A : TreeSequence G e0) (r : ℕ) (hr : (1 : ℕ) ≤ r) (hrA : r + (1 : ℕ) ≤ A.length),
        TreeSequenceInitialSegment (TreeSequencePrefix A r hr (Nat.le_trans (Nat.le_succ r) hrA))
        (TreeSequencePrefix A (r + (1 : ℕ)) (
    by omega
    ) hrA)) →
    ∀ (n : ℕ) (hnU : U.length ≤ n) (hnM hnSuccM : n + (1 : ℕ) ≤ M.length) (hnM' : n ≤ M.length),
    let X : TreeSequence G e0 := TreeSequencePrefix M n (Nat.le_trans U.positive hnU) hnM';
    let Y : TreeSequence G e0 := TreeSequencePrefix M (n + (1 : ℕ)) (
    by omega
    ) hnSuccM;
    let mIndex : Fin M.length := (⟨n,
    by
          have := GoldbergSeymour.TreeSequence.positive M
          omega
    ⟩ : Fin M.length);
    ∀ (i : Fin Tj0.length), M.edge mIndex = Tj0.edge i →
    ∀ (c : Fin k), ett.series.data.coloring jSlot.castSucc (Tj0.edge i) = some c → c ∈
        TreeMissingColors rho2 X → TashkinovAugmentation rho2 X Y := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace p0 indices0 hb2 rho1 hb2TreeEdges terminalPosition
      hterminalPositionPositive hterminalPositionBound TjPrime u huPrime b traceB rho2 c2
      uPosition huPositionPositive huPositionBound U Tj0 M prefixPrefix n hnU hnM hnSuccM hnM' X
      Y mIndex i hedgeMTj c hcolorTj hmissingX
  exact @helper_hXY_5375 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
      (@indices0) (@hb2) (@hb2TreeEdges) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime) (@u)
      (@huPrime) (@b) (@traceB) (@c2) (@uPosition) (@huPositionPositive)
      (@huPositionBound) (@M) (@prefixPrefix) (@n) (@hnU) (@hnM) (@hnSuccM) (@hnM')
      (@i) (@hedgeMTj) (@c) (@hcolorTj) (@hmissingX)

theorem helper_hseedVertexBeforeJ_6180.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
        (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) → seed.vertex
        (Fin.last seed.length) = v →
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot vertexTransfer hterminalJ terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedTj hseedTerminal i hi
  exact @helper_hseedVertexBeforeJ_2905 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
      (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@vertexTransfer) (@hterminalJ)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj)
      (@hseedTerminal) (@i) (@hi)

theorem helper_segmentVertexBeforeJ_6189.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds);
    ∀ (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ)
        (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive : (1 : ℕ) ≤
        (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0) (_ : Fin (TjPrime.length + (1 : ℕ))), (
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ) →
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore (ett.series.data.tree
        jSlot.succ.castSucc) v hterminalJ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hterminalJ p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed TjPrime uPosition hseedVertexBeforeJ A hAseed hAlen x hxA
  exact @helper_segmentVertexBeforeJ_3151 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hterminalJ) (@p0)
      (@indices0) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@TjPrime) (@uPosition) (@hseedVertexBeforeJ) (@A)
      (@hAseed) (@hAlen) (@x) (@hxA)

theorem helper_transportSeedStep2_6201.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma :
        PartialEdgeColoring E k),
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
        → TreeSequenceInitialSegment A C) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (indices0 : Fin
        (p0 + (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0) (u : V) (b : Fin (p0 + (1 : ℕ))) (traceB :
        ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) (traceB.coloring (Fin.last traceB.steps)) →
    ∀ (_ : Fin (TjPrime.length + (1 : ℕ))), (
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore (ett.series.data.tree
        jSlot.succ.castSucc) v hterminalJ) →
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentation (ett.series.data.coloring jSlot.castSucc) A
        B → TreeSequenceInitialSegment B seed → TashkinovAugmentation rho2 A B := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot segmentTrans trace hterminalJ p0 indices0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed TjPrime u b traceB
      rho2 c1 uPosition segmentVertexBeforeJ A B hstep hBseed
  exact TashkinovAugmentation.transportBeforeVertex
    (ett.series.data.tree jSlot.succ.castSucc) seed
    (ett.series.data.coloring jSlot.castSucc) rho2
    (TashkinovStoredColors ett.series.data jSlot.castSucc) v hterminalJ c1
    segmentVertexBeforeJ hstep hBseed

theorem helper_transportSeedRoute2_6212.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma :
        PartialEdgeColoring E k),
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
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (u : V) (b : Fin (p0 + (1 : ℕ))) (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u p0
        indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps); (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentation (ett.series.data.coloring jSlot.castSucc) A
        B → TreeSequenceInitialSegment B seed → TashkinovAugmentation rho2 A B) →
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho2 S seed := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace p0 indices0 rho1 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed u b traceB rho2 transportSeedStep2 S
      hroute
  exact TashkinovAugmentationSequence.transport transportSeedStep2 hroute

theorem helper_branch_6243.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma : PartialEdgeColoring E k),
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
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound; (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    ∀ (TjPrime : TreeSequence G e0) (u : V) (b : Fin (p0 + (1 : ℕ))) (traceB :
        ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
        IsProperEdgeColoring G rho2 → IsOneEdgeUncolored rho2 e0 →
    ∀ (_ : Fin (TjPrime.length + (1 : ℕ))),
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
        TreeSequenceInitialSegment seed Tj0 →
    ∀ (C : TreeSequence G e0), TashkinovAugmentationSequence rho2 seed C → (
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho2 S seed) →
        TreeSequenceVertexSet Tj0 ⊂ TreeSequenceVertexSet C → ¬(0 : ℕ) < (↑jSlot : ℕ) → False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot hjSlot trace p0 indices0 rho1 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed commonPrefix TjPrime u b traceB rho2
      hrho2Proper hrho2One uPosition Tj0 hseedTj0 C hrouteSeedC transportSeedRoute2 hTj0StrictC
      hjPositive
  exact @helper_branch_3377 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
    (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@v) (@sigma)
    (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@trace) (@p0)
    (@indices0) (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
    (@commonPrefix) (@TjPrime) (@u) (@b) (@traceB) (@hrho2Proper) (@hrho2One) (@uPosition)
    (@hseedTj0) (@C) (@hrouteSeedC) (@transportSeedRoute2) (@hTj0StrictC) (@hjPositive)

theorem helper_hterminalColorsNotRestored_6300.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds), ett.series.data.chosenVertex q.succ = some v
        → ett.series.data.gamma q.succ = some gamma → ett.series.data.delta q.succ = some delta →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal
        ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); (
    ∀ (t : Fin ett.rounds), ett.series.data.kind t.succ = some TashkinovExtensionKind.PE →
    ∃ (vt : V) (gammaT : Fin k) (deltaT : Fin k), ett.series.data.chosenVertex t.succ = some vt ∧
        ett.series.data.gamma t.succ = some gammaT ∧ ett.series.data.delta t.succ = some deltaT) →
        (
    ∀ (t : Fin ett.rounds) (gammaT deltaT : Fin k), ett.series.data.kind t.succ = some
        TashkinovExtensionKind.PE → ett.series.data.gamma t.succ = some gammaT →
        ett.series.data.delta t.succ = some deltaT → ett.series.data.stored t.succ = (insert
        gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k))) → (
    ∀ (s t : Fin ett.rounds) (vs vt : V) (gammaS deltaS gammaT deltaT : Fin k), s ∈
        ExtensionBaseActiveIndices ett v hvFinal → t ∈ ExtensionBaseActiveIndices ett v hvFinal →
        (↑s : ℕ) < (↑t : ℕ) → ett.series.data.chosenVertex s.succ = some vs →
        ett.series.data.chosenVertex t.succ = some vt → ett.series.data.gamma s.succ = some gammaS
        → ett.series.data.delta s.succ = some deltaS → ett.series.data.gamma t.succ = some gammaT
        → ett.series.data.delta t.succ = some deltaT → (((insert gammaS ({ deltaS } : Finset (Fin
        k)) : Finset (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k)) :
        Finset (Fin k)).Nonempty ↔ vs = vt ∧ ¬
    ∃ r ∈ ExtensionBaseSupportClass ett v hvFinal vs, (↑s : ℕ) < (↑r : ℕ) ∧ (↑r : ℕ) < (↑t : ℕ) ∧
        ett.series.data.chosenVertex r.succ = some vs) ∧ (((insert gammaS ({ deltaS } : Finset
        (Fin k)) : Finset (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin
        k)) : Finset (Fin k)).Nonempty → ((insert gammaS ({ deltaS } : Finset (Fin k)) : Finset
        (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k)) : Finset (Fin
        k)) = ({ gammaT } : Finset (Fin k)) ∧ ((insert gammaS ({ deltaS } : Finset (Fin k)) :
        Finset (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k)) : Finset
        (Fin k)) = ({ deltaS } : Finset (Fin k)))) → q ∈ ExtensionBaseActiveIndices ett v hvFinal
        → q ∈ ExtensionBaseSupportClass ett v hvFinal v →
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k)
        (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), indices0
        (Fin.last p0) = q →
    let restorationColors : Finset (Fin k) := (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ; gamma ∉
        restorationColors ∧ delta ∉ restorationColors := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta q hqTerminal hqVertex
      hqGamma hqDelta hvFinal hfirstUpper hfirstPositive jSlot hPESlotData hPEStored
      hpairOverlapColors hqActive hqClass p0 indices0 gamma0 delta0 terminalPosition hqLast
      restorationColors
  exact @helper_hterminalColorsNotRestored_1977 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@gamma) (@delta) (@hqTerminal) (@hqVertex) (@hqGamma) (@hqDelta) (@hvFinal)
      (@hfirstUpper) (@hfirstPositive) (@hPESlotData) (@hPEStored) (@hpairOverlapColors)
      (@hqActive) (@hqClass) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
      (@hqLast)

theorem helper_hdeltaEarlier_6317.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (delta : Fin k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds), ett.series.data.chosenVertex q.succ = some v
        → ett.series.data.delta q.succ = some delta →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal
        ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); ((
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
        (ett.series.data.tree jSlot.succ.castSucc)) → q ∈ ExtensionBaseActiveIndices ett v hvFinal
        →
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 :
        ℕ)) → Fin k), (
    ∀ (a b : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
        → (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a)) →
        Function.Injective (Fin.cons (gamma0 (0 : Fin (p0 + (1 : ℕ)))) delta0) → indices0
        (Fin.last p0) = q → delta0 (Fin.last p0) = delta →
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → delta ≠ gammaS ∧ delta ≠ deltaS := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v delta q hqTerminal hqVertex hqDelta
      hvFinal hfirstUpper hfirstPositive jSlot hdeltaExclusion hqActive p0 indices0 gamma0 delta0
      hincreasing0 hclass0 hdelta0 hinjective0 hqLast hdeltaLast
  exact @helper_hdeltaEarlier_3576 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@delta)
      (@hqTerminal) (@hqVertex) (@hqDelta) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@hdeltaExclusion) (@hqActive) (@p0) (@indices0) (@gamma0) (@delta0) (@hincreasing0)
      (@hclass0) (@hdelta0) (@hinjective0) (@hqLast) (@hdeltaLast)

theorem helper_hpreterminalPackage_6328.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma _ : Fin k),
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
    ⟩ : Fin ett.rounds);
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 :
        ℕ)) → Fin k), (
    ∀ (a b : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
        → (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a)) → (
    ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc) →
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), indices0 (Fin.last
        p0) = q → gamma0 (Fin.last p0) = gamma → (0 : ℕ) < p0 →
    ∃ (preterminalSlot : Fin ett.rounds), (↑preterminalSlot : ℕ) < (↑q : ℕ) ∧ preterminalSlot ∈
        (ExtensionBaseSupportClass ett v hvFinal v).erase q ∧ ett.series.data.delta
        preterminalSlot.succ = some gamma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot p0 indices0 gamma0 delta0 hincreasing0 hclass0 hdelta0
      hchain0 terminalPosition hqLast hgammaLast
  exact @helper_hpreterminalPackage_3617 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@gamma) (@delta) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0)
      (@indices0) (@gamma0) (@delta0) (@hincreasing0) (@hclass0) (@hdelta0) (@hchain0)
      (@terminalPosition) (@hqLast) (@hgammaLast)

theorem helper_hsupportComponentOrder_6348.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (_ _ : Fin k) (sigma :
        PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds), ett.series.data.kind q.succ = some
        TashkinovExtensionKind.PE →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal
        ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), indices0 (Fin.last
        p0) = q → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → ETTStrongInterchangeable ett s v rho1 gammaS deltaS) →
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS →
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree s.succ.castSucc), x ≠ v →
    ∀ (y : V), Sum.inl y ∈ TwoColorComponent G rho1 gammaS deltaS (Sum.inl x) → y ∈
        TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal hqKind
      hvFinal hfirstUpper hfirstPositive jSlot stageToStage vertexTransfer trace p0 indices0
      gamma0 delta0 rho1 terminalPosition hqLast hb4Earlier
  exact @helper_hsupportComponentOrder_3667 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@gamma) (@delta) (@sigma) (@hqTerminal) (@hqKind) (@hvFinal) (@hfirstUpper)
      (@hfirstPositive) (@stageToStage) (@vertexTransfer) (@trace) (@p0) (@indices0)
      (@gamma0) (@delta0) (@terminalPosition) (@hqLast) (@hb4Earlier)

theorem helper_branch_6417.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); ett.series.data.chosenVertex q.succ = some v →
    ∀ (i : Fin ett.rounds), IsProperEdgeColoring G (ett.series.data.coloring i.castSucc) →
        IsOneEdgeUncolored (ett.series.data.coloring i.castSucc) e0 → ColoredVertexSetClosed G
        (ett.series.data.coloring i.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        i.succ.castSucc)) → ¬ColoredVertexSetStronglyClosed G (ett.series.data.coloring
        i.castSucc) (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc)) → ¬Nonempty
        (RevisitingExtensionCertificate ett.series.data i.castSucc) →
    ∀ (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors ett.series.data i.castSucc) (ett.series.data.coloring i.castSucc)),
        (
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree i.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data i.castSucc) : Finset (Fin k)) choice.selected rho ∧
        ¬Disjoint (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho
        (ett.series.data.tree i.succ.castSucc))) →
    ∀ (actualGamma : Fin k), ParallelExtensionColor ett.series.data i.castSucc choice.selected
        choice.vertex actualGamma →
    ∀ (secondStable : PartialEdgeColoring E k), StableColoring (ett.series.data.tree
        i.succ.castSucc) (insert choice.color (TashkinovStoredColors ett.series.data i.castSucc) :
        Finset (Fin k)) choice.selected secondStable → TreeExit (ett.series.data.tree
        i.succ.castSucc) secondStable actualGamma choice.color choice.vertex →
        ett.series.data.coloring i.succ = TwoColorComponentSwap G secondStable actualGamma
        choice.color (Sum.inl choice.vertex) → IsProperEdgeColoring G (ett.series.data.coloring
        i.succ) → IsOneEdgeUncolored (ett.series.data.coloring i.succ) e0 → ett.series.data.stored
        i.succ = (insert choice.color ({ actualGamma } : Finset (Fin k)) : Finset (Fin k)) →
        ett.series.data.connectingEdges i.succ = ({ choice.edge } : Finset E) →
        ett.series.data.kind i.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex i.succ = some choice.vertex → ett.series.data.outsideVertex
        i.succ = some choice.otherEndpoint → ett.series.data.delta i.succ = some choice.color →
        ett.series.data.gamma i.succ = some actualGamma → TashkinovClosure
        (ett.series.data.coloring i.succ) (ett.series.data.tree i.succ.castSucc)
        (ett.series.data.tree i.succ.succ) → TreeSequenceInitialSegment (ett.series.data.tree
        i.succ.castSucc) (ett.series.data.tree i.succ.succ) → (ett.series.data.tree
        i.succ.castSucc).length < (ett.series.data.tree i.succ.succ).length → q.succ = i.succ →
    ∃ (fN : E), ett.series.data.connectingEdges i.succ = ({ fN } : Finset E) ∧ Incident G v fN ∧
        IsProperEdgeColoring G (ett.series.data.coloring i.succ) ∧ IsOneEdgeUncolored
        (ett.series.data.coloring i.succ) e0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqVertex i previousProper
      previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
      seriesAlternativeFails actualGamma gammaRule secondStable secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges currentKind
      currentVertex currentOutside currentDelta currentGamma closedExtension orderedExtension
      strictExtension htarget
  exact @helper_branch_2800 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@hqVertex) (@i) (@previousProper) (@previousOneUncolored) (@previousClosed)
      (@previousNotStronglyClosed) (@noRevisiting) (@choice)
      (@seriesAlternativeFails) (@actualGamma) (@gammaRule) (@secondStable)
      (@secondStableRelation) (@exitWitness) (@currentColoring) (@currentProper)
      (@currentOneUncolored) (@currentStored) (@currentEdges) (@currentKind)
      (@currentVertex) (@currentOutside) (@currentDelta) (@currentGamma)
      (@closedExtension) (@orderedExtension) (@strictExtension) (@htarget)

theorem helper_hdeltaLocation_6440.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k),
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
    ⟩ : Fin ett.rounds);
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k)
        (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound; seed.vertex
        (Fin.last seed.length) = v → TreeSequenceInitialSegment seed (ett.series.data.tree
        q.succ.castSucc) →
    ∀ (fN : E), BoundaryColorEdges G (ett.series.data.coloring q.succ) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) gamma = ({ fN } : Finset E) ∧ (
    ∀ g ∈ BoundaryColorEdges G (ett.series.data.coloring q.succ) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) delta,
    ∃ (w : V), TreeVertexOrder (ett.series.data.tree q.succ.castSucc) w v ∧ Incident G w g) ∧
        (ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) →
    ∀ alpha ∈ TreeMissingColors (ett.series.data.coloring q.succ) (ett.series.data.tree
        q.succ.castSucc), alpha ≠ delta → BoundaryColorEdges G (ett.series.data.coloring q.succ)
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) alpha = ∅) →
    ∀ f ∈ BoundaryColorEdges G (ett.series.data.coloring q.succ) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) delta,
    ∃ y ∈ TreeSequenceVertexSet seed, Incident G y f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot p0 indices0 gamma0 delta0 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed hseedTerminal hseedN fN
      hboundaryStructure
  exact @helper_hdeltaLocation_3782 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0)
      (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@hseedTerminal) (@hseedN) (@fN) (@hboundaryStructure)

theorem helper_hendpointNeighbor_6578.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
        IsProperEdgeColoring G rho1 →
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v); (H.neighborSet
        (Sum.inl v)).Subsingleton →
    ∀ (endpoint : V ⊕ E) (componentPath : H.Walk (Sum.inl v) endpoint), componentPath.IsPath →
        {z : V ⊕ E | z ∈ componentPath.support} = C → ¬componentPath.Nil → (0 : ℕ) <
        componentPath.length → endpoint ∈ C →
    ∀ (z : V ⊕ E), H.Adj endpoint z → z = componentPath.getVert (componentPath.length - (1 : ℕ))
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1 hrho1Proper
      terminalPosition H C hvSub endpoint componentPath hcomponentPath hcomponentSupport
      hcomponentNonempty hcomponentPositive hendpointC
  exact degreeTwoComponentPathEndNeighbor componentPath hcomponentPath
    (TwoColorIncidenceDegreeAtMostTwo G rho1 gamma delta hrho1Proper)
    hvSub hcomponentSupport

theorem helper_hendpointVertex_6586.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (endpoint : V ⊕ E) (componentPath : H.Walk (Sum.inl v) endpoint), (0 : ℕ) <
        componentPath.length → (
    ∀ (z : V ⊕ E), H.Adj endpoint z → z = componentPath.getVert (componentPath.length - (1 : ℕ)))
        →
    ∃ (x : V), endpoint = Sum.inl x := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition H endpoint componentPath hcomponentPositive hendpointNeighbor
  exact incidenceLeafEndVertex componentPath hcomponentPositive (by
    intro x hx y hy
    simp only [SimpleGraph.mem_neighborSet] at hx hy
    exact (hendpointNeighbor x hx).trans (hendpointNeighbor y hy).symm)

theorem helper_hTnElementary_6609.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k),
    let _ : DecidableEq V := Classical.decEq V;
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
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), indices0 (Fin.last
        p0) = q →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)), ColoredVertexSetElementary G
        (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma this q
      hqTerminal hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hqLast H x componentPath
  exact @helper_hTnElementary_4214 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper)
      (@hfirstPositive) (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
      (@hqLast) (@x) (@componentPath)

theorem helper_hterminalPresentSigma_6628.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds); ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex q.succ = some v → ett.series.data.gamma q.succ = some gamma →
        ett.series.data.delta q.succ = some delta → v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) → StableColoring (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring
        q.succ) sigma → gamma ≠ delta → (
    ∀ (phi : PartialEdgeColoring E k) (alpha beta : Fin k), alpha ≠ beta →
    ∀ (root : V ⊕ E) (y : V), alpha ∈ PresentColors G phi y → beta ∈ PresentColors G phi y → alpha
        ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta root) y ∧ beta ∈ PresentColors G
        (TwoColorComponentSwap G phi alpha beta root) y) → ColoredVertexSetElementary G
        (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) → gamma ∈ MissingColors G (ett.series.data.coloring q.castSucc) v →
        delta ∉ TreeMissingColors (ett.series.data.coloring q.castSucc) (ett.series.data.tree
        q.succ.castSucc) →
    ∀ y ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), y ≠ v → gamma ∈
        PresentColors G sigma y ∧ delta ∈ PresentColors G sigma y := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqKind hqVertex
      hqGamma hqDelta hvStage hsigmaTerminal hgammaDelta swapBothPresent hTnElementary
      hgammaMissingPre hdeltaNotMissingPre
  exact @helper_hterminalPresentSigma_4287 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@gamma) (@delta) (@sigma) (@hqKind) (@hqVertex) (@hqGamma) (@hqDelta) (@hvStage)
      (@hsigmaTerminal) (@hgammaDelta) (@swapBothPresent) (@hTnElementary)
      (@hgammaMissingPre) (@hdeltaNotMissingPre)

theorem helper_hxOutsidePrime_6645.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k),
    let _ : DecidableEq V := Classical.decEq V;
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v hvFinal
        sigma) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0), (
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, (MissingColors G rho1 x ∩ supportColors :
        Finset (Fin k)) = ∅) → gamma ∈ supportColors → delta ∈ supportColors → gamma ≠ delta →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)), (
    ∀ (z : V ⊕ E), H.Adj (Sum.inl x) z → z = componentPath.getVert (componentPath.length - (1 :
        ℕ))) → x ≠ v → x ∉ TreeSequenceVertexSet TjPrime := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v gamma delta sigma this hvFinal trace p0
      indices0 rho1 supportColors TjPrime hcaseTwoPointwise hgammaSupport hdeltaSupport
      hgammaDelta H x componentPath hendpointNeighbor hxNe
  exact @helper_hxOutsidePrime_4415 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@v) (@gamma) (@delta) (@sigma)
      (@hvFinal) (@trace) (@p0) (@indices0) (@TjPrime) (@hcaseTwoPointwise)
      (@hgammaSupport) (@hdeltaSupport) (@hgammaDelta) (@x) (@componentPath)
      (@hendpointNeighbor) (@hxNe)

theorem helper_hvNotPrevious_6710.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), indices0 (Fin.last
        p0) = q →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; (0 : ℕ) <
        (↑jSlot : ℕ) → v ∉ TreeSequenceVertexSet Tprevious := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot hjSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hqLast H x componentPath u exitPath Tprevious hjPositive
  exact @helper_hvNotPrevious_4521 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
      (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@trace)
      (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hqLast) (@x)
      (@componentPath) (@u) (@exitPath) (@hjPositive)

theorem helper_hpreviousStrict_6723.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = v →
    ∀ (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ((0 : ℕ) <
        (↑jSlot : ℕ) → v ∉ TreeSequenceVertexSet Tprevious) → ((0 : ℕ) < (↑jSlot : ℕ) →
        TreeSequenceInitialSegment Tprevious (ett.series.data.tree jSlot.succ.castSucc)) → (0 : ℕ)
        < (↑jSlot : ℕ) → Tprevious.length < seed.length := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalAt hterminalPositionPositive hterminalPositionBound seed H x
      componentPath u exitPath Tprevious hvNotPrevious hpreviousTj hjPositive
  exact @helper_hpreviousStrict_4568 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace)
      (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalAt)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@x) (@componentPath) (@u)
      (@exitPath) (@hvNotPrevious) (@hpreviousTj) (@hjPositive)

theorem helper_branch_6740.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
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
    ⟩ : Fin ett.rounds);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) → (ett.series.data.tree (0 : Fin
        (ett.rounds + (2 : ℕ)))).length = (1 : ℕ) → TashkinovClosure (ett.series.data.coloring (0
        : Fin (ett.rounds + (1 : ℕ)))) (ett.series.data.tree (0 : Fin (ett.rounds + (2 : ℕ))))
        (ett.series.data.tree (1 : Fin (ett.rounds + (2 : ℕ)))) → jSlot.castSucc = (0 : Fin
        (ett.rounds + (1 : ℕ))) → TashkinovAugmentationSequence (ett.series.data.coloring (0 : Fin
        (ett.rounds + (1 : ℕ)))) seed (ett.series.data.tree jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hseedTj commonPrefix seedLength initialClosure htarget
  exact @helper_branch_4596 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj)
      (@commonPrefix) (@seedLength) (@initialClosure) (@htarget)

theorem helper_branch_6748.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        jSlot.castSucc.succ = jSlot.succ.castSucc → TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ((0 : ℕ) <
        (↑jSlot : ℕ) → Tprevious.length < seed.length) →
    ∀ (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0 (ett.series.data.tree
        i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)) (adjoined : TreeSequence G e0),
        TreeSequenceAdjoinEdge (ett.series.data.tree i.succ.castSucc) choice.edge adjoined →
        TashkinovClosure (ett.series.data.coloring i.succ) adjoined (ett.series.data.tree
        i.succ.succ) → jSlot.castSucc = i.succ → TashkinovAugmentationSequence
        (ett.series.data.coloring i.succ) seed (ett.series.data.tree jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj
      commonPrefix H x componentPath u exitPath Tprevious hpreviousStrict i choice adjoined
      adjoinedExactly closedExtension htarget
  exact @helper_branch_4629 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex)
      (@hseedTj) (@commonPrefix) (@x) (@componentPath) (@u) (@exitPath)
      (@hpreviousStrict) (@i) (@choice) (@adjoined) (@adjoinedExactly)
      (@closedExtension) (@htarget)

theorem helper_branch_6761.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        jSlot.castSucc.succ = jSlot.succ.castSucc → TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ((0 : ℕ) <
        (↑jSlot : ℕ) → TreeSequenceInitialSegment Tprevious seed) →
    ∀ (i : Fin ett.rounds), TashkinovClosure (ett.series.data.coloring i.succ)
        (ett.series.data.tree i.succ.castSucc) (ett.series.data.tree i.succ.succ) → jSlot.castSucc
        = i.succ → TashkinovAugmentationSequence (ett.series.data.coloring i.succ) seed
        (ett.series.data.tree jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj
      H x componentPath u exitPath Tprevious hpreviousSeed i closedExtension htarget
  exact @helper_branch_4664 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex)
      (@hseedTj) (@x) (@componentPath) (@u) (@exitPath) (@hpreviousSeed) (@i)
      (@closedExtension) (@htarget)

theorem helper_branch_6775.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        jSlot.castSucc.succ = jSlot.succ.castSucc → TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ((0 : ℕ) <
        (↑jSlot : ℕ) → Tprevious.length < seed.length) →
    ∀ (i : Fin ett.rounds) (available : RevisitingExtensionCertificate ett.series.data i.castSucc)
        (adjoined : TreeSequence G e0), TreeSequenceAdjoinEdge (ett.series.data.tree
        i.succ.castSucc) available.edge adjoined → TashkinovClosure (ett.series.data.coloring
        i.succ) adjoined (ett.series.data.tree i.succ.succ) → jSlot.castSucc = i.succ →
        TashkinovAugmentationSequence (ett.series.data.coloring i.succ) seed (ett.series.data.tree
        jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj
      commonPrefix H x componentPath u exitPath Tprevious hpreviousStrict i available adjoined
      adjoinedExactly closedExtension htarget
  exact @helper_branch_4686 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex)
      (@hseedTj) (@commonPrefix) (@x) (@componentPath) (@u) (@exitPath)
      (@hpreviousStrict) (@i) (@available) (@adjoined) (@adjoinedExactly)
      (@closedExtension) (@htarget)

theorem helper_hcaseTwoObservationPackage_6796.{u_1, u_2} :
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
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0) (fN : E),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (exitPath :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)), exitPath.IsPath
        → (2 : ℕ) ≤ exitPath.length → (
    ∀ y ∈ exitPath.support, y ∈ componentPath.support) → (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet
        TjPrime, Sum.inl w ∈ exitPath.support ↔ w = u) → (
    ∃ g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)
        ∪ TreeSequenceVertexSet TjPrime) gamma, Incident G u g ∧ Sum.inr g ∈ exitPath.support) →
        ¬Incident G u fN → u ∈ TreeSequenceVertexSet TjPrime → u ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) →
    ∀ beta ∈ MissingColors G rho1 u, beta ∉ supportColors →
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
        beta) → (u ∈ TreeSequenceVertexSet TjPrime ∧ u ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) ∧ (exitPath.IsPath ∧ (2 : ℕ) ≤ exitPath.length ∧ (
    ∀ y ∈ exitPath.support, y ∈ componentPath.support) ∧ (
    ∀ y ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet
        TjPrime, Sum.inl y ∈ exitPath.support ↔ y = u) ∧ (
    ∃ g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)
        ∪ TreeSequenceVertexSet TjPrime) gamma, Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
        ¬Incident G u fN) ∧ (beta ∈ MissingColors G rho1 u ∧ beta ∉ supportColors) ∧ z ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∧ (ett.series.data.tree
        jSlot.succ.castSucc).vertex zPosition = z ∧ seed.length ≤ (↑zPosition : ℕ) ∧ ((seed.length
        < (↑zPosition : ℕ) ∧ beta ∈ MissingColors G rho1 z ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → (↑r : ℕ) < (↑zPosition : ℕ) → beta ∉ MissingColors G rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).vertex r)) ∨ zPosition = Fin.last (ett.series.data.tree
        jSlot.succ.castSucc).length ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → beta ∉ MissingColors G rho1 ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) ∧
        (
    ∀ y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z hz, beta ∉ MissingColors
        G rho1 y) ∧
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → (↑a :
        ℕ) < (↑zPosition : ℕ) → rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) ≠ some
        beta := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 rho1 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed supportColors TjPrime fN H x
      componentPath u exitPath hexitPath hexitLength hexitSupport hexitIntersection hexitBoundary
      huNotFN huPrime huOutside beta hbeta hbetaSupport z hz zPosition hzPosition hzAfter
      hzChoice hzBefore hzEdges
  exact @helper_hcaseTwoObservationPackage_3695 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@trace) (@p0) (@indices0) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@TjPrime) (@fN) (@x) (@componentPath) (@u) (@exitPath)
      (@hexitPath) (@hexitLength) (@hexitSupport) (@hexitIntersection) (@hexitBoundary)
      (@huNotFN) (@huPrime) (@huOutside) (@beta) (@hbeta) (@hbetaSupport) (@z) (@hz)
      (@zPosition) (@hzPosition) (@hzAfter) (@hzChoice) (@hzBefore) (@hzEdges)

theorem helper_hpreterminalGammaPresent_6848.{u_1, u_2} :
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
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k), (
    ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc) → Function.Injective (Fin.cons (gamma0 (0 :
        Fin (p0 + (1 : ℕ)))) delta0) →
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), (1 :
        ℕ) ≤ (↑terminalPosition : ℕ) → (↑terminalPosition : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length →
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0), (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.stored (indices0 a).succ = (insert (gamma0 a)
        ({delta0 a} : Finset (Fin k)) : Finset (Fin k))) → (
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, (MissingColors G rho1 x ∩ supportColors :
        Finset (Fin k)) = ∅) → gamma0 (Fin.last p0) = gamma →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (_ : V ⊕ E) (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)), u ∈
        (TreeSequenceVertexSet TjPrime).erase v →
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (u : V) (beta : Fin
        k), u ∈ TreeSequenceVertexSet TjPrime → u ∉ TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc) → beta ∈ MissingColors G rho1 u →
    ∀ (a : Fin p0), gamma0 a.castSucc ∈ PresentColors G (TwoColorComponentSwap G
        (OutsideTreeColorSwap TjPrime rho1 beta delta) gamma beta (Sum.inl u)) u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvStage hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 hchain0
      hinjective0 rho1 terminalPosition hterminalPositionPositive hterminalPositionBound
      supportColors TjPrime hstored0 hcaseTwoPointwise hgammaLast H a x componentPath u exitPath
      huErase zPosition
  exact @helper_hpreterminalGammaPresent_4778 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvStage) (@hvFinal) (@hfirstUpper)
      (@hfirstPositive) (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@hchain0)
      (@hinjective0) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@TjPrime) (@hstored0) (@hcaseTwoPointwise) (@hgammaLast)
      (@a) (@x) (@componentPath) (@u) (@exitPath) (@huErase) (@zPosition)

theorem helper_hTjInitialEarlier_6865.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by
                    have := GoldbergSeymour.TreeSequence.positive T
                    omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), (1 :
        ℕ) ≤ (↑terminalPosition : ℕ) → (↑terminalPosition : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length → indices0 (Fin.last p0) = q →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))),
    ∀ s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q, TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc) (ett.series.data.tree s.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot hjSlot stageToStage trace p0 indices0 gamma0
      delta0 rho1 terminalPosition hterminalPositionPositive hterminalPositionBound hqLast H x
      componentPath u exitPath zPosition
  exact @helper_hTjInitialEarlier_3214 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot)
      (@stageToStage) (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hqLast) (@x)
      (@componentPath) (@u) (@exitPath) (@zPosition)

theorem helper_hgammaFirstZero_6905.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds) (gamma0 _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), (1 :
        ℕ) ≤ (↑terminalPosition : ℕ) → (↑terminalPosition : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length → gamma0 (Fin.last p0) = gamma →
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ)));
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))), p0 = (0 : ℕ) → gammaFirst = gamma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound hgammaLast gammaFirst H x
      componentPath u exitPath zPosition hp0
  have hindex : (0 : Fin (p0 + 1)) = Fin.last p0 := by
    apply Fin.ext
    exact hp0.symm
  exact (congrArg gamma0 hindex).trans hgammaLast

theorem helper_hclaim45Package_6912.{u_1, u_2} :
    helperHclaim45Package6912Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvStage hvFinal hfirstUpper hfirstPositive jSlot trace hterminalJ p0 indices0 gamma0 rho1
      hrho1Proper hrho1One hb2Missing terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedTj hseedTerminal hTjQ supportColors TjPrime hclosure
      hprimeElementary hseedPrime hb1Tj hcaseTwoPointwise gammaFirst hgammaSupport hdeltaSupport
      hgammaDelta hb2EdgesFromSeed hdeltaPhiJ hterminalSeed fN hdeltaMissing H C a x
      componentPath hcomponentPath hcomponentSupport hxOutside u exitPath hexitPath hexitLength
      hexitSupport hexitIntersection hexitBoundary huNotFN huPrime huOutside hdegree beta hbeta
      hbetaSupport haugmentation z hz zPosition hzPosition hzAfter hzChoice hzBefore hzEdges
      hpositiveClaim45 hgammaFirstZero
  exact @helper_hclaim45Package_4916 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@sigma) (@hqTerminal) (@hvStage) (@hvFinal) (@hfirstUpper)
      (@hfirstPositive) (@trace) (@hterminalJ) (@p0) (@indices0) (@gamma0) (@hrho1Proper)
      (@hrho1One) (@hb2Missing) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@hseedTj) (@hseedTerminal) (@hTjQ) (@TjPrime) (@hclosure)
      (@hprimeElementary) (@hseedPrime) (@hb1Tj) (@hcaseTwoPointwise) (@hgammaSupport)
      (@hdeltaSupport) (@hgammaDelta) (@hb2EdgesFromSeed) (@hdeltaPhiJ) (@hterminalSeed)
      (@fN) (@hdeltaMissing) (@a) (@x) (@componentPath) (@hcomponentPath)
      (@hcomponentSupport) (@hxOutside) (@u) (@exitPath) (@hexitPath) (@hexitLength)
      (@hexitSupport) (@hexitIntersection) (@hexitBoundary) (@huNotFN) (@huPrime)
      (@huOutside) (@hdegree) (@beta) (@hbeta) (@hbetaSupport) (@haugmentation) (@z) (@hz)
      (@zPosition) (@hzPosition) (@hzAfter) (@hzChoice) (@hzBefore) (@hzEdges)
      (@hpositiveClaim45) (@hgammaFirstZero)

end GoldbergSeymour.ExtensionBaseProof

end
