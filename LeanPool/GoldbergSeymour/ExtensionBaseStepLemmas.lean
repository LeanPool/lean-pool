/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

import all LeanPool.GoldbergSeymour.ExtensionBaseAuxiliary

public import LeanPool.GoldbergSeymour.ExtensionBasePreparations
public import LeanPool.GoldbergSeymour.ExtensionBaseClosure
public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmBInvariant
public import LeanPool.GoldbergSeymour.ParallelStepRootComponentSetup

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
abbrev helperContinuation14264Conditions.{u_1, u_2} : Prop :=
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
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal → (↑jSlot
        : ℕ) ≤ (↑q : ℕ) → StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma → (
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
        (Fin k)) = ({ deltaS } : Finset (Fin k)))) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma), v ∈ TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc) → q ∈ ExtensionBaseActiveIndices ett v hvFinal
        → q ∈ ExtensionBaseSupportClass ett v hvFinal v →
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 :
        ℕ)) → Fin k), (
    ∀ (a b : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
        → (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.gamma (indices0 a).succ = some (gamma0 a)) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a)) → (
    ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc) → Function.Injective (Fin.cons (gamma0 (0 :
        Fin (p0 + (1 : ℕ)))) delta0) → (
    let storedPairs : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ; (MissingColors G sigma v ∩ storedPairs : Finset
        (Fin k)) = ({delta0 (Fin.last p0)} : Finset (Fin k)) ∧ MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v = MissingColors G sigma v \
        ({delta0 (Fin.last p0)} : Finset (Fin k)) ∪ ({gamma0 (0 : Fin (p0 + (1 : ℕ)))} : Finset
        (Fin k))) → (
    ∀ v_1 ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.castSucc.succ)).erase v,
        MissingColors G (trace.coloring (Fin.last trace.steps)) v_1 = MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v_1) ∧ MissingColors G (trace.coloring (Fin.last
        trace.steps)) v = MissingColors G sigma v →
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
        IsProperEdgeColoring G rho1 → IsOneEdgeUncolored rho1 e0 → StableColoringBeforeVertex T v
        hvFinal (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho1 → (
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
        hvFinal).biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ ExtensionBaseSupportClass ett v hvFinal v
        → s ≠ q → ett.series.data.chosenVertex s.succ = some v → ett.series.data.gamma s.succ =
        some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett s
        v rho1 gammaS deltaS) →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = v →
    ∀ (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        jSlot.castSucc.succ = jSlot.succ.castSucc → TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) → seed.vertex (Fin.last seed.length) = v →
        TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree q.succ.castSucc) → TreeSequenceInitialSegment (ett.series.data.tree
        q.succ.castSucc) T → (
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore T v hvFinal) → (
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore T v hvFinal) → (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentation (ett.series.data.coloring jSlot.castSucc) A
        B → TreeSequenceInitialSegment B seed → TashkinovAugmentation rho1 A B) → False

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch13441Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k) (sigma :
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
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal → (
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
        jSlot.castSucc.succ = jSlot.succ.castSucc →
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
    ∀ (TjPrime : TreeSequence G e0), TashkinovClosure rho1 seed TjPrime →
        TreeSequenceInitialSegment seed TjPrime → indices0 (Fin.last p0) = q → v ∈
        TreeSequenceVertexSet seed →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (a : V ⊕ E) (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (exitPath :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ( (0 : ℕ) <
        (↑jSlot : ℕ) → Tprevious.length < seed.length) → ( (0 : ℕ) < (↑jSlot : ℕ) →
        TreeSequenceInitialSegment Tprevious seed) →
    ∀ (zPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V)
        (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime), u0 ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) →
    ∀ (exitPath0 : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
        (beta0 : Fin k) (z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc)) (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length
        + (1 : ℕ))), ((seed.length < (↑zPosition0 : ℕ) ∧ beta0 ∈ MissingColors G rho1 z0 ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → (↑r : ℕ) < (↑zPosition0 : ℕ) → beta0 ∉ MissingColors G rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).vertex r)) ∨ zPosition0 = Fin.last (ett.series.data.tree
        jSlot.succ.castSucc).length ∧
    ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), seed.length < (↑r :
        ℕ) → beta0 ∉ MissingColors G rho1 ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) →
    ∀ (rho3 : PartialEdgeColoring E k), IsProperEdgeColoring G rho3 → IsOneEdgeUncolored rho3 e0 →
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho3 → (
    ∀ y ∈ ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 ∪ ({ z0 } :
        Finset V) ∪ (TreeVerticesBefore TjPrime u0 huPrime0 ∪ ({ u0 } : Finset V))).erase
        u0).erase z0, MissingColors G rho3 y = MissingColors G rho1 y) → (
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) ∧ (↑a :
        ℕ) < (↑zPosition0 : ℕ) ∧ (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u0 ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → rho3 f = rho1 f) → (
        z0 ∈ TreeVerticesBefore TjPrime u0 huPrime0 → MissingColors G rho3 z0 = MissingColors G
        rho1 z0) → beta0 ∉ MissingColors G rho1 v →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex uPosition = u0 → seed.length <
        (↑uPosition : ℕ) →
    let terminalInTj : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)) :=
        Fin.castLE (Nat.succ_le_succ hseedTj.1) (Fin.last seed.length); (ett.series.data.tree
        jSlot.succ.castSucc).vertex terminalInTj = v → (↑terminalInTj : ℕ) = seed.length → (z0 = v
        ↔ zPosition0 = terminalInTj) → z0 = v → False

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch13578Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k),
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
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (indices0 : Fin
        (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps); (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
        jSlot.castSucc.succ = jSlot.succ.castSucc →
    ∀ (hseedTj : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)),
        seed.vertex (Fin.last seed.length) = v → TreeSequenceInitialSegment (ett.series.data.tree
        jSlot.succ.castSucc) (ett.series.data.tree q.succ.castSucc) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    ∀ (TjPrime : TreeSequence G e0), TashkinovClosure rho1 seed TjPrime →
        ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime) →
        TreeSequenceInitialSegment seed TjPrime → indices0 (Fin.last p0) = q →
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ))); MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho1 v ∪ ({ gammaFirst } :
        Finset (Fin k)) → delta ∈ MissingColors G rho1 v →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (a b : V ⊕ E) (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (exitPath :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ( (0 : ℕ) <
        (↑jSlot : ℕ) → TreeSequenceInitialSegment Tprevious (ett.series.data.tree
        jSlot.succ.castSucc)) → ( (0 : ℕ) < (↑jSlot : ℕ) → Tprevious.length < seed.length) → ( (0
        : ℕ) < (↑jSlot : ℕ) → TreeSequenceInitialSegment Tprevious seed) →
        TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) seed
        (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (zPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V)
        (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime), u0 ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) →
    ∀ (exitPath0 : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0)),
    ∀ beta0 ∈ MissingColors G rho1 u0,
    ∀ (z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
        (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition0 = z0 → seed.length ≤
        (↑zPosition0 : ℕ) →
    ∀ (rho3 : PartialEdgeColoring E k), IsProperEdgeColoring G rho3 → IsOneEdgeUncolored rho3 e0 →
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho3 → (
    ∀ y ∈ ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 ∪ ({ z0 } :
        Finset V) ∪ (TreeVerticesBefore TjPrime u0 huPrime0 ∪ ({ u0 } : Finset V))).erase
        u0).erase z0, MissingColors G rho3 y = MissingColors G rho1 y) → (
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) ∧ (↑a :
        ℕ) < (↑zPosition0 : ℕ) ∧ (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u0 ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → rho3 f = rho1 f) → (
        beta0 ∈ MissingColors G rho1 z0 → delta ∈ MissingColors G rho3 z0) → ( z0 ∈
        TreeVerticesBefore TjPrime u0 huPrime0 → MissingColors G rho3 z0 = MissingColors G rho1
        z0) → gammaFirst ∈ MissingColors G rho3 u0 →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex uPosition = u0 → seed.length <
        (↑uPosition : ℕ) →
    let terminalInTj : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)) :=
        Fin.castLE (Nat.succ_le_succ hseedTj.1) (Fin.last seed.length); (ett.series.data.tree
        jSlot.succ.castSucc).vertex terminalInTj = v → (↑terminalInTj : ℕ) = seed.length → v ∈
        TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 → zPosition0 =
        Fin.last (ett.series.data.tree jSlot.succ.castSucc).length ∨ (↑zPosition0 : ℕ) <
        (↑(Fin.last (ett.series.data.tree jSlot.succ.castSucc).length) : ℕ) ∧ beta0 ∈
        MissingColors G rho1 z0 → (0 : ℕ) < (↑jSlot : ℕ) → False

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch15456Conditions.{u_1, u_2} : Prop :=
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
    ⟩ : Fin ett.rounds); (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds), (
    ∀ v_1 ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.castSucc.succ)).erase v,
        MissingColors G (trace.coloring (Fin.last trace.steps)) v_1 = MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v_1) ∧ MissingColors G (trace.coloring (Fin.last
        trace.steps)) v = MissingColors G sigma v →
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps); (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0) (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (b : Fin
        (p0 + (1 : ℕ))) (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
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
        huPositionBound; TreeSequenceInitialSegment seed U → MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho2 v ∪ MissingColors G
        rho2 u →
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
        TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) seed Tj0 →
    ∀ (M : TreeSequence G e0), u ∈ TreeSequenceVertexSet U → TreeSequenceInitialSegment U M → (
    ∀ (j : Fin M.length), U.length ≤ (↑j : ℕ) →
    ∃ (i : Fin Tj0.length), M.edge j = Tj0.edge i ∧ M.vertex j.succ = Tj0.vertex i.succ) → (
    ∀ (i : Fin Tj0.length), Tj0.vertex i.succ ∉ TreeSequenceVertexSet U →
    ∃ (j : Fin M.length), U.length ≤ (↑j : ℕ) ∧ M.edge j = Tj0.edge i ∧ M.vertex j.succ =
        Tj0.vertex i.succ) → (
    ∀ (i j : Fin Tj0.length), Tj0.vertex i.succ ∉ TreeSequenceVertexSet U → Tj0.vertex j.succ ∉
        TreeSequenceVertexSet U → (↑i : ℕ) < (↑j : ℕ) →
    ∀ (p q : Fin M.length), M.vertex p.succ = Tj0.vertex i.succ → M.vertex q.succ = Tj0.vertex
        j.succ → (↑p : ℕ) < (↑q : ℕ)) → (
    ∀ (A : TreeSequence G e0) (r : ℕ) (hr : (1 : ℕ) ≤ r) (hrA : r ≤ A.length),
        TreeSequenceInitialSegment (TreeSequencePrefix A r hr hrA) A) → (
    ∀ (A : TreeSequence G e0) (r : ℕ) (hr : (1 : ℕ) ≤ r) (hrA : r + (1 : ℕ) ≤ A.length),
        TreeSequenceInitialSegment (TreeSequencePrefix A r hr (Nat.le_trans (Nat.le_succ r) hrA))
        (TreeSequencePrefix A (r + (1 : ℕ)) (
    by omega
    ) hrA)) → TreeSequenceInitialSegment seed Tj0 → (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) A B → A.length < B.length →
    ∃ (C : TreeSequence G e0), TashkinovAugmentation (ett.series.data.coloring jSlot.castSucc) A C
        ∧ TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) C B) →
    ∀ (n : ℕ) (hnU : U.length ≤ n), (
    ∀ (hnM : n ≤ M.length), TashkinovAugmentationSequence rho2 U (TreeSequencePrefix M n
        (Nat.le_trans U.positive hnU) hnM)) →
    ∀ (hnM : n + (1 : ℕ) ≤ M.length), TashkinovAugmentationSequence rho2 U (TreeSequencePrefix M
        (n + (1 : ℕ)) (Nat.le_trans U.positive (Nat.le_succ_of_le hnU)) hnM)

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch15626Conditions.{u_1, u_2} : Prop :=
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
        ett.series.data.chosenVertex r.succ = some vs) ∧ ( ((insert gammaS ({ deltaS } : Finset
        (Fin k)) : Finset (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin
        k)) : Finset (Fin k)).Nonempty → ((insert gammaS ({ deltaS } : Finset (Fin k)) : Finset
        (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k)) : Finset (Fin
        k)) = ({ gammaT } : Finset (Fin k)) ∧ ((insert gammaS ({ deltaS } : Finset (Fin k)) :
        Finset (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k)) : Finset
        (Fin k)) = ({ deltaS } : Finset (Fin k)))) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)), q ∈
        ExtensionBaseActiveIndices ett v hvFinal → q ∈ ExtensionBaseSupportClass ett v hvFinal v →
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 :
        ℕ)) → Fin k), (
    ∀ (a b : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
        → (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.gamma (indices0 a).succ = some (gamma0 a)) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a)) → (
    ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc) → Function.Injective (Fin.cons (gamma0 (0 :
        Fin (p0 + (1 : ℕ)))) delta0) → (
    let storedPairs : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ; (MissingColors G sigma v ∩ storedPairs : Finset
        (Fin k)) = ({delta0 (Fin.last p0)} : Finset (Fin k)) ∧ MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v = MissingColors G sigma v \
        ({delta0 (Fin.last p0)} : Finset (Fin k)) ∪ ({gamma0 (0 : Fin (p0 + (1 : ℕ)))} : Finset
        (Fin k))) →
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
        hvFinal).biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ ExtensionBaseSupportClass ett v hvFinal v
        → s ≠ q → ett.series.data.chosenVertex s.succ = some v → ett.series.data.gamma s.succ =
        some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett s
        v rho1 gammaS deltaS) →
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
        : Finset (Fin k)) = ({delta0 (Fin.last p0)} : Finset (Fin k)) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), delta0 a ∉ TreeMissingColors (ett.series.data.coloring
        jSlot.castSucc) (ett.series.data.tree jSlot.succ.castSucc)) → StableColoringBeforeVertex
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ (TashkinovStoredColors
        ett.series.data jSlot.castSucc) (ett.series.data.coloring jSlot.castSucc) rho1 →
        ((((TreeSequenceVertexSet TjPrime).erase v).biUnion fun (x : V) ↦ MissingColors G rho1 x)
        ∩ supportColors : Finset (Fin k)) = ∅ → False

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation14753Conditions.{u_1, u_2} : Prop :=
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
        ett.series.data.chosenVertex r.succ = some vs) ∧ ( ((insert gammaS ({ deltaS } : Finset
        (Fin k)) : Finset (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin
        k)) : Finset (Fin k)).Nonempty → ((insert gammaS ({ deltaS } : Finset (Fin k)) : Finset
        (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k)) : Finset (Fin
        k)) = ({ gammaT } : Finset (Fin k)) ∧ ((insert gammaS ({ deltaS } : Finset (Fin k)) :
        Finset (Fin k)) ∩ (insert gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k)) : Finset
        (Fin k)) = ({ deltaS } : Finset (Fin k)))) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)), q ∈
        ExtensionBaseActiveIndices ett v hvFinal → q ∈ ExtensionBaseSupportClass ett v hvFinal v →
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 :
        ℕ)) → Fin k), (
    ∀ (a b : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
        → (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.gamma (indices0 a).succ = some (gamma0 a)) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a)) → (
    ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc) → Function.Injective (Fin.cons (gamma0 (0 :
        Fin (p0 + (1 : ℕ)))) delta0) → (
    let storedPairs : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ; (MissingColors G sigma v ∩ storedPairs : Finset
        (Fin k)) = ({delta0 (Fin.last p0)} : Finset (Fin k)) ∧ MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v = MissingColors G sigma v \
        ({delta0 (Fin.last p0)} : Finset (Fin k)) ∪ ({gamma0 (0 : Fin (p0 + (1 : ℕ)))} : Finset
        (Fin k))) → (
    ∀ v_1 ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.castSucc.succ)).erase v,
        MissingColors G (trace.coloring (Fin.last trace.steps)) v_1 = MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v_1) ∧ MissingColors G (trace.coloring (Fin.last
        trace.steps)) v = MissingColors G sigma v →
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
        hvFinal).biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ ExtensionBaseSupportClass ett v hvFinal v
        → s ≠ q → ett.series.data.chosenVertex s.succ = some v → ett.series.data.gamma s.succ =
        some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett s
        v rho1 gammaS deltaS) →
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
        ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime) → (
    let awayMissing : Finset (Fin k) := ((TreeSequenceVertexSet TjPrime).erase v).biUnion fun (x :
        V) ↦ MissingColors G rho1 x; (awayMissing ∩ supportColors : Finset (Fin k)).Nonempty ∨
        (awayMissing ∩ supportColors : Finset (Fin k)) = ∅) → TreeSequenceInitialSegment seed
        TjPrime → v ∈ TreeSequenceVertexSet TjPrime → indices0 (Fin.last p0) = q → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.chosenVertex (indices0 a).succ = some v) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.kind (indices0 a).succ = some
        TashkinovExtensionKind.PE) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.stored (indices0 a).succ = (insert (gamma0 a)
        ({delta0 a} : Finset (Fin k)) : Finset (Fin k))) → (MissingColors G rho1 v ∩ supportColors
        : Finset (Fin k)) = ({delta0 (Fin.last p0)} : Finset (Fin k)) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), delta0 a ∉ TreeMissingColors (ett.series.data.coloring
        jSlot.castSucc) (ett.series.data.tree jSlot.succ.castSucc)) → StableColoringBeforeVertex
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ (TashkinovStoredColors
        ett.series.data jSlot.castSucc) (ett.series.data.coloring jSlot.castSucc) rho1 → (
        ((((TreeSequenceVertexSet TjPrime).erase v).biUnion fun (x : V) ↦ MissingColors G rho1 x)
        ∩ supportColors : Finset (Fin k)).Nonempty →
    ∃ (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (b : Fin (p0 + (1 : ℕ))) (traceB :
        ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b), u ∉ TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc) ∧ ExtensionBaseAlgorithmBInvariant ett v jSlot
        rho1 u p0 indices0 b traceB ∧
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho2 ∧ ((
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∪ TreeVerticesBefore
        TjPrime u huPrime, MissingColors G rho2 x = MissingColors G rho1 x) ∧
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), (ett.series.data.tree
        jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex z = u ∧ (↑a :
        ℕ) < (↑z : ℕ) ∧ TjPrime.edge a = f) → rho2 f = rho1 f) ∧ gamma0 (0 : Fin (p0 + (1 : ℕ))) ∈
        MissingColors G rho2 u) → False

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch15674Conditions.{u_1, u_2} : Prop :=
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
        (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (hseedTj : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc))
        (TjPrime : TreeSequence G e0), (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → rho1
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (a b : V ⊕ E) (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (exitPath :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)) (zPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V) (exitPath0 :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0)) (z0 : V) (hz0 :
        z0 ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (zPosition0 : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), (ett.series.data.tree
        jSlot.succ.castSucc).vertex zPosition0 = z0 →
    ∀ (rho3 : PartialEdgeColoring E k), (
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) ∧ (↑a :
        ℕ) < (↑zPosition0 : ℕ) ∧ (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u0 ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → rho3 f = rho1 f) →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ))),
    let terminalInTj : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)) :=
        Fin.castLE (Nat.succ_le_succ hseedTj.1) (Fin.last seed.length); (↑terminalInTj : ℕ) =
        seed.length →
    ∀ (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤
        TjPrime.length) (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition0 : ℕ)) (hzPositionBound :
        (↑zPosition0 : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑zPosition0 : ℕ) hzPositionPositive hzPositionBound; TreeSequenceInitialSegment Z
        (ett.series.data.tree jSlot.succ.castSucc) → TreeSequenceInitialSegment seed U →
        MissingColors G (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho3 v ∪
        MissingColors G rho3 u0 → (
    ∀ y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0, y ≠ v →
        MissingColors G rho3 y = MissingColors G (ett.series.data.coloring jSlot.castSucc) y) →
    ∀ (M : TreeSequence G e0), u0 ∈ TreeSequenceVertexSet U → TashkinovAugmentationSequence
        (ett.series.data.coloring jSlot.castSucc) seed Z → TreeSequenceInitialSegment U M → (
    ∀ (j : Fin M.length), U.length ≤ (↑j : ℕ) →
    ∃ (i : Fin Z.length), M.edge j = Z.edge i ∧ M.vertex j.succ = Z.vertex i.succ) → (
    ∀ (i : Fin Z.length), Z.vertex i.succ ∉ TreeSequenceVertexSet U →
    ∃ (j : Fin M.length), U.length ≤ (↑j : ℕ) ∧ M.edge j = Z.edge i ∧ M.vertex j.succ = Z.vertex
        i.succ) → (
    ∀ (i j : Fin Z.length), Z.vertex i.succ ∉ TreeSequenceVertexSet U → Z.vertex j.succ ∉
        TreeSequenceVertexSet U → (↑i : ℕ) < (↑j : ℕ) →
    ∀ (p q : Fin M.length), M.vertex p.succ = Z.vertex i.succ → M.vertex q.succ = Z.vertex j.succ
        → (↑p : ℕ) < (↑q : ℕ)) → (
    ∀ (A : TreeSequence G e0) (q0 : ℕ) (hq0 : (1 : ℕ) ≤ q0) (hqA : q0 ≤ A.length),
        TreeSequenceInitialSegment (TreeSequencePrefix A q0 hq0 hqA) A) → (
    ∀ (A : TreeSequence G e0) (q0 : ℕ) (hq0 : (1 : ℕ) ≤ q0) (hqA : q0 + (1 : ℕ) ≤ A.length),
        TreeSequenceInitialSegment (TreeSequencePrefix A q0 hq0 (Nat.le_trans (Nat.le_succ q0)
        hqA)) (TreeSequencePrefix A (q0 + (1 : ℕ)) (
    by omega
    ) hqA)) → TreeSequenceInitialSegment seed Z → (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) A B → A.length < B.length →
    ∃ (C : TreeSequence G e0), TashkinovAugmentation (ett.series.data.coloring jSlot.castSucc) A C
        ∧ TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) C B) →
    ∀ (n : ℕ) (hnU : U.length ≤ n), (
    ∀ (hnM : n ≤ M.length), TashkinovAugmentationSequence rho3 U (TreeSequencePrefix M n
        (Nat.le_trans U.positive hnU) hnM)) →
    ∀ (hnM : n + (1 : ℕ) ≤ M.length), TashkinovAugmentationSequence rho3 U (TreeSequencePrefix M
        (n + (1 : ℕ)) (Nat.le_trans U.positive (Nat.le_succ_of_le hnU)) hnM)

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch15847Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k) (sigma :
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
    ⟩ : Fin ett.rounds); (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (indices0 : Fin
        (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps); (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v →
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
    ∀ (TjPrime : TreeSequence G e0), TashkinovClosure rho1 seed TjPrime →
        TreeSequenceInitialSegment seed TjPrime →
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ))); MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho1 v ∪ ({ gammaFirst } :
        Finset (Fin k)) → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → rho1
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) → delta ∈
        MissingColors G rho1 v →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (a b : V ⊕ E) (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (exitPath :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)),
        TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) seed
        (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (zPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V)
        (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime), u0 ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) →
    ∀ (exitPath0 : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
        (beta0 : Fin k) (z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc)) (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length
        + (1 : ℕ))), (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition0 = z0 →
        seed.length ≤ (↑zPosition0 : ℕ) →
    ∀ (rho3 : PartialEdgeColoring E k), IsProperEdgeColoring G rho3 → IsOneEdgeUncolored rho3 e0 →
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho3 → (
    ∀ y ∈ ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 ∪ ({ z0 } :
        Finset V) ∪ (TreeVerticesBefore TjPrime u0 huPrime0 ∪ ({ u0 } : Finset V))).erase
        u0).erase z0, MissingColors G rho3 y = MissingColors G rho1 y) → (
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) ∧ (↑a :
        ℕ) < (↑zPosition0 : ℕ) ∧ (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u0 ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → rho3 f = rho1 f) → (
        beta0 ∈ MissingColors G rho1 z0 → delta ∈ MissingColors G rho3 z0) → ( z0 ∈
        TreeVerticesBefore TjPrime u0 huPrime0 → MissingColors G rho3 z0 = MissingColors G rho1
        z0) → gammaFirst ∈ MissingColors G rho3 u0 → u0 ≠ v →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex uPosition = u0 → seed.length <
        (↑uPosition : ℕ) →
    let terminalInTj : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)) :=
        Fin.castLE (Nat.succ_le_succ hseedTj.1) (Fin.last seed.length); (ett.series.data.tree
        jSlot.succ.castSucc).vertex terminalInTj = v → (↑terminalInTj : ℕ) = seed.length → ¬z0 = v
        → v ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 → zPosition0 =
        Fin.last (ett.series.data.tree jSlot.succ.castSucc).length ∨ (↑zPosition0 : ℕ) <
        (↑(Fin.last (ett.series.data.tree jSlot.succ.castSucc).length) : ℕ) ∧ beta0 ∈
        MissingColors G rho1 z0 → ¬(0 : ℕ) < (↑jSlot : ℕ) → False

/-- Dependent contract shared by the extension base proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation12157Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds), v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal
        ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B C
        → TreeSequenceInitialSegment A C) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (indices0 : Fin
        (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps); (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), rho1 ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) →
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
        (Fin.last p0) = q →
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ))); MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho1 v ∪ ({ gammaFirst } :
        Finset (Fin k)) → (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) → rho1
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a)) → v ∈
        TreeSequenceVertexSet seed → TreeSequenceInitialSegment seed (ett.series.data.tree
        q.succ.castSucc) →
    ∀ (fN : E), delta ∈ MissingColors G rho1 v →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (a b : V ⊕ E) (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (exitPath :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ( (0 : ℕ) <
        (↑jSlot : ℕ) → TreeSequenceInitialSegment Tprevious (ett.series.data.tree
        jSlot.succ.castSucc)) → ( (0 : ℕ) < (↑jSlot : ℕ) → Tprevious.length < seed.length) → ( (0
        : ℕ) < (↑jSlot : ℕ) → TreeSequenceInitialSegment Tprevious seed) →
        TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) seed
        (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (zPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), (
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
        z0) ∧ gammaFirst ∈ MissingColors G rho3 u0) → False

theorem helper_hLowerPartV_179.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T) (_ :
        ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (_ : (0 : ℕ) <
        ETTFirstAppearanceIndex ett v hvFinal), (
    ∀ (i : Fin (ett.rounds + (1 : ℕ))), (0 : ℕ) < (↑i : ℕ) → TreeSequenceInitialSegment
        (ett.series.data.tree i.castSucc) (ett.series.data.tree i.succ)) → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B →
    ∀ (x y : V), x ∈ TreeSequenceVertexSet A → y ∈ TreeSequenceVertexSet A → TreeVertexOrder B x y
        → TreeVertexOrder A x y) →
    ∀ (r a : Fin ett.rounds), (↑a : ℕ) < (↑r : ℕ) →
    ∀ (sigmaR : PartialEdgeColoring E k), IsProperEdgeColoring G sigmaR → IsOneEdgeUncolored
        sigmaR e0 → StableColoring (ett.series.data.tree r.succ.castSucc) (TashkinovStoredColors
        ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc) sigmaR →
    ∀ (deltaR : Fin k), DefectiveColor G sigmaR (TreeSequenceVertexSet (ett.series.data.tree
        r.succ.castSucc)) deltaR →
    ∀ (x : V), BoundaryColorVertex G sigmaR (TreeSequenceVertexSet (ett.series.data.tree
        r.succ.castSucc)) deltaR x → (
    ∃ (y : V), BoundaryColorVertex G sigmaR (TreeSequenceVertexSet (ett.series.data.tree
        r.succ.castSucc)) deltaR y ∧ TreeVertexOrder (ett.series.data.tree r.succ.castSucc) y x) →
    ∀ (hxFinal : x ∈ TreeSequenceVertexSet T), ETTFirstAppearanceIndex ett x hxFinal ≤ (↑a : ℕ) +
        (1 : ℕ) →
    ∀ (xa : V), ett.series.data.kind a.succ = some TashkinovExtensionKind.PE ∨
        ett.series.data.kind a.succ = some TashkinovExtensionKind.SE →
        ett.series.data.chosenVertex a.succ = some xa → x = xa ∨ TreeVertexOrder
        (ett.series.data.tree r.succ.castSucc) x xa := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower v q hqTerminal hvFinal
      hfirstUpper hfirstPositive stepSegment stageToStage vertexTransfer orderRestrict r a har
      sigmaR hproperR honeR hstableR deltaR hdefectiveR x hboundaryR hearlierR hxFinal hfirstR xa
      hkindA hvertexA
  obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
    CertifiedETTRestriction G k e0 input T generating ett hMP r.val
      (by omega) (by omega)
  let nLower : Fin (lower.rounds + 1) := Fin.last lower.rounds
  let aLower : Fin lower.rounds := ⟨a.val, by omega⟩
  have hnMap : Fin.castLE (by omega) nLower = r.castSucc := by
    apply Fin.ext
    simp [nLower, hround]
  have hnTreeMap : Fin.castLE (by omega) nLower.castSucc =
      r.castSucc.castSucc := by
    apply Fin.ext
    simp [nLower, hround]
  have haMap : Fin.castLE (by omega) aLower.succ = a.succ := by
    apply Fin.ext
    rfl
  let P : TreeSequence G e0 := ett.series.data.tree r.castSucc.castSucc
  let Tnext : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc
  have hPNext : TreeSequenceInitialSegment P Tnext := by
    have hs := stepSegment r.castSucc (by simpa using (show 0 < r.val by omega))
    simpa [P, Tnext] using hs
  have hxP : x ∈ TreeSequenceVertexSet P := by
    exact @helper_hxP_352 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@stageToStage) (@vertexTransfer) (@r) (@a) (@har) (@x)
        (@hxFinal) (@hfirstR) (@lower) (@hround)
  obtain ⟨y, hyBoundary, hyx⟩ := hearlierR
  have hyP : y ∈ TreeSequenceVertexSet P := by
    exact @helper_hyP_393 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@r) (@a) (@har) (@x) (@hxFinal) (@lower) (@hround)
        (@hPNext) (@hxP) (@y) (@hyx)
  have hyxP : TreeVertexOrder P y x :=
    orderRestrict hPNext y x hyP hxP hyx
  have hyne : y ≠ x := by
    intro hyxEq
    subst y
    rcases hyxP with ⟨iy, ix, hiy, hix, hlt⟩
    have : iy = ix := P.vertex_injective (hiy.trans hix.symm)
    omega
  have boundaryRestrict :
    ∀ z : V, z ∈ TreeSequenceVertexSet P →
    ∀ f : E, f ∈ BoundaryColorEdges G sigmaR (TreeSequenceVertexSet Tnext) deltaR → Incident G z f
        → f ∈ BoundaryColorEdges G sigmaR (TreeSequenceVertexSet P) deltaR := by
    exact @helper_boundaryRestrict_424 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@vertexTransfer) (@r) (@sigmaR) (@deltaR)
        (@hPNext)
  obtain ⟨fx, hfxBoundary, hfxIncident⟩ := hboundaryR.2
  obtain ⟨fy, hfyBoundary, hfyIncident⟩ := hyBoundary.2
  have hfxP := boundaryRestrict x hxP fx hfxBoundary hfxIncident
  have hfyP := boundaryRestrict y hyP fy hfyBoundary hfyIncident
  have hfxy : fx ≠ fy := by
    exact @helper_hfxy_453 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@vertexTransfer) (@r) (@sigmaR) (@deltaR) (@x)
        (@hPNext) (@hxP) (@y) (@hyP) (@hyne) (@fx) (@hfxBoundary) (@hfxIncident) (@fy)
        (@hfyBoundary) (@hfyIncident) (@hfyP)
  have hdefectiveP : DefectiveColor G sigmaR
      (TreeSequenceVertexSet P) deltaR := by
    unfold DefectiveColor
    exact Finset.one_lt_card.mpr ⟨fx, hfxP, fy, hfyP, hfxy⟩
  have htreeLower : lower.series.data.tree nLower.castSucc =
      P := by
    rw [htrees nLower.castSucc, hnTreeMap]
  have hcolorLower : lower.series.data.coloring nLower =
      ett.series.data.coloring r.castSucc := by
    rw [(hdata nLower).1, hnMap]
  have hstoredLower : TashkinovStoredColors lower.series.data nLower =
      TashkinovStoredColors ett.series.data r.castSucc := by
    rw [(hdata nLower).2.2.2.2.2.2.2.2.1, hnMap]
  have hstableLower : StableColoring
      (lower.series.data.tree nLower.castSucc)
      (TashkinovStoredColors lower.series.data nLower)
      (lower.series.data.coloring nLower) sigmaR := by
    exact @helper_hstableLower_484 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@vertexTransfer) (@r) (@a) (@sigmaR) (@hstableR) (@x)
        (@hxFinal) (@lower) (@hPNext) (@htreeLower) (@hcolorLower) (@hstoredLower)
  have hdefectiveLower : DefectiveColor G sigmaR
      (TreeSequenceVertexSet
        (lower.series.data.tree nLower.castSucc)) deltaR := by
    simpa [htreeLower] using hdefectiveP
  have hboundaryLower : BoundaryColorVertex G sigmaR
      (TreeSequenceVertexSet
        (lower.series.data.tree nLower.castSucc)) deltaR x := by
    rw [htreeLower]
    exact ⟨hxP, fx, hfxP, hfxIncident⟩
  have hearlierLower : ∃ y : V, BoundaryColorVertex G sigmaR
      (TreeSequenceVertexSet
      (lower.series.data.tree nLower.castSucc)) deltaR y ∧
      TreeVertexOrder (lower.series.data.tree nLower.castSucc) y x := by
    rw [htreeLower]
    exact ⟨y, ⟨hyP, fy, hfyP, hfyIncident⟩, hyxP⟩
  have hxLower : x ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨r.val + 1, by omega⟩) := by
    have hx := hboundaryR.1
    convert hx using 1; congr 2
  have hkindLower : lower.series.data.kind aLower.succ =
      some TashkinovExtensionKind.PE ∨
      lower.series.data.kind aLower.succ =
        some TashkinovExtensionKind.SE := by
    rcases hkindA with hkindA | hkindA
    · left
      rw [(hdata aLower.succ).2.2.2.1, haMap]
      exact hkindA
    · right
      rw [(hdata aLower.succ).2.2.2.1, haMap]
      exact hkindA
  have hvertexLower : lower.series.data.chosenVertex aLower.succ =
      some xa := by
    rw [(hdata aLower.succ).2.2.2.2.1, haMap]
    exact hvertexA
  have hfirstLower : ETTFirstAppearanceIndex lower x hxLower ≤
      aLower.val + 1 := by
    exact @helper_hfirstLower_539 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@r) (@a) (@har) (@x) (@hxFinal) (@hfirstR) (@lower)
        (@hround) (@htrees) (@hxLower)
  have hpack := hlower lower (by omega) (by omega) hlowerMP
  have hresult := hpack.2.2.2.2.1 sigmaR hproperR honeR hstableLower
    deltaR hdefectiveLower x hboundaryLower hearlierLower hxLower aLower xa
    hkindLower hvertexLower hfirstLower
  exact hresult

theorem helper_hLowerInterchange_328.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (↑q : ℕ) + (1 : ℕ) = ett.rounds →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T), ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) +
        (1 : ℕ) → (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (t : Fin ett.rounds) (vt : V) (gammaT deltaT : Fin k), t ∈ ExtensionBaseActiveIndices ett v
        hvFinal → (↑t : ℕ) < (↑q : ℕ) → ett.series.data.chosenVertex t.succ = some vt →
        ett.series.data.gamma t.succ = some gammaT → ett.series.data.delta t.succ = some deltaT →
        TreeInterchangeable G (ett.series.data.tree t.succ.succ) (ett.series.data.coloring t.succ)
        gammaT deltaT := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower v q hqTerminal hvFinal
      hfirstUpper hfirstPositive vertexTransfer t vt gammaT deltaT htActive htq htVertex htGamma
      htDelta
  have htKind : ett.series.data.kind t.succ =
      some TashkinovExtensionKind.PE := by
    have htData := htActive
    simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] at htData
    exact htData.2.1
  have htCurrent : IsOneEdgeUncolored
        (ett.series.data.coloring t.succ) e0 ∧
      deltaT ∈ MissingColors G
        (ett.series.data.coloring t.succ) vt := by
    generalize htarget : t.succ = target
    cases ett.series.certified target with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
      exact (Fin.succ_ne_zero t htarget).elim
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
      have hbad : some TashkinovExtensionKind.SE =
          some TashkinovExtensionKind.PE :=
        currentKind.symm.trans (by simpa [htarget] using htKind)
      cases hbad
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
      have hbad : some TashkinovExtensionKind.RE =
          some TashkinovExtensionKind.PE :=
        currentKind.symm.trans (by simpa [htarget] using htKind)
      cases hbad
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        actualGamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
            exact @helper_branch_664 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                (@k) (@e0) (@input) (@T) (@generating) (@ett) (@t) (@vt) (@gammaT) (@deltaT)
                (@htVertex) (@htGamma) (@htDelta) (@i) (@previousProper) (@previousOneUncolored)
                (@previousClosed) (@previousNotStronglyClosed) (@noRevisiting) (@choice)
                (@seriesAlternativeFails) (@actualGamma) (@gammaRule) (@secondStable)
                (@secondStableRelation) (@exitWitness) (@currentColoring) (@currentProper)
                (@currentOneUncolored) (@currentStored) (@currentEdges) (@currentKind)
                (@currentVertex) (@currentOutside) (@currentDelta) (@currentGamma)
                (@closedExtension) (@orderedExtension) (@strictExtension) (@htarget)
  obtain ⟨hcolorNe, htProper, htSegment, hvtStage, hrootPath,
      hrootOnly, hnonisolated⟩ :=
    ParallelStepRootComponentSetup ett.series t vt gammaT deltaT
      htKind htVertex htGamma htDelta
  have hdeltaTree : deltaT ∈ TreeMissingColors
      (ett.series.data.coloring t.succ)
      (ett.series.data.tree t.succ.succ) := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨vt, vertexTransfer htSegment hvtStage, htCurrent.2⟩
  let s := t.val + 1
  obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
    CertifiedETTRestriction G k e0 input T generating ett hMP s
      (by simp [s]) (by dsimp [s]; omega)
  let nLower : Fin (lower.rounds + 1) := Fin.last lower.rounds
  let nextLower : Fin (lower.rounds + 2) := Fin.last (lower.rounds + 1)
  have hnMap : Fin.castLE (by omega) nLower = t.succ := by
    apply Fin.ext
    simp [nLower, hround, s]
  have hnextMap : Fin.castLE (by omega) nextLower = t.succ.succ := by
    apply Fin.ext
    simp [nextLower, hround, s]
  have htreeLower : lower.series.data.tree nextLower =
      ett.series.data.tree t.succ.succ := by
    rw [htrees nextLower, hnextMap]
  have htreeFinal : lower.series.data.tree
      (Fin.last (lower.rounds + 1)) =
      ett.series.data.tree t.succ.succ := by
    simpa [nextLower] using htreeLower
  have hcolorLower : lower.series.data.coloring nLower =
      ett.series.data.coloring t.succ := by
    rw [(hdata nLower).1, hnMap]
  have hstoredLower : TashkinovStoredColors lower.series.data nLower =
      TashkinovStoredColors ett.series.data t.succ := by
    rw [(hdata nLower).2.2.2.2.2.2.2.2.1, hnMap]
  have hstableSelf : StableColoring
      (ett.series.data.tree t.succ.succ)
      (TashkinovStoredColors ett.series.data t.succ)
      (ett.series.data.coloring t.succ)
      (ett.series.data.coloring t.succ) := by
    exact ⟨(by intros; rfl), (by intros; rfl)⟩
  have hstableLower : StableColoring
      (lower.series.data.tree nextLower)
      (TashkinovStoredColors lower.series.data nLower)
      (lower.series.data.coloring nLower)
      (ett.series.data.coloring t.succ) := by
    simpa [htreeLower, hstoredLower, hcolorLower] using hstableSelf
  have hpack := hlower lower (by omega) (by omega) hlowerMP
  have hdeltaLower : deltaT ∈ TreeMissingColors
      (ett.series.data.coloring t.succ)
      (lower.series.data.tree (Fin.last (lower.rounds + 1))) := by
    rw [htreeFinal]
    exact hdeltaTree
  have hinterchange := hpack.2.1 (ett.series.data.coloring t.succ)
    htProper htCurrent.1 hstableLower gammaT deltaT (Or.inr hdeltaLower)
  rw [htreeFinal] at hinterchange
  exact hinterchange

theorem helper_hpairOverlapColors_581.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T), (
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
        ({ deltaS } : Finset (Fin k)))) → (
    ∀ (t : Fin ett.rounds) (gammaT deltaT : Fin k), ett.series.data.kind t.succ = some
        TashkinovExtensionKind.PE → ett.series.data.gamma t.succ = some gammaT →
        ett.series.data.delta t.succ = some deltaT → ett.series.data.stored t.succ = (insert
        gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k))) →
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
        (Fin k)) = ({ deltaS } : Finset (Fin k))) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal hpairOverlap hPEStored s t vs vt gammaS
      deltaS gammaT deltaT hs ht hst hsVertex htVertex hsGamma hsDelta htGamma htDelta
  have hsData := hs
  have htData := ht
  simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
    Finset.mem_univ, true_and] at hsData htData
  obtain ⟨hsFirst, hsKind, vs0, hvsFinal, hvsChosen, hvsFirst⟩ := hsData
  obtain ⟨htFirst, htKind, vt0, hvtFinal, hvtChosen, hvtFirst⟩ := htData
  have hvsEq : vs0 = vs :=
    Option.some.inj (hvsChosen.symm.trans hsVertex)
  have hvtEq : vt0 = vt :=
    Option.some.inj (hvtChosen.symm.trans htVertex)
  subst vs0
  subst vt0
  have hsStored := hPEStored s gammaS deltaS hsKind hsGamma hsDelta
  have htStored := hPEStored t gammaT deltaT htKind htGamma htDelta
  have hoverlap :=
    hpairOverlap s t vs vt hvsFinal hvtFinal gammaS deltaS gammaT deltaT
      hs ht hst hsVertex htVertex hsGamma hsDelta htGamma htDelta
  rw [hsStored, htStored] at hoverlap
  refine ⟨?_, hoverlap.2⟩
  constructor
  · intro hnonempty
    obtain ⟨hvs, hbetween⟩ := hoverlap.1.mp hnonempty
    refine ⟨hvs, ?_⟩
    rintro ⟨r, hrClass, hsr, hrt, hrVertex⟩
    have hrData :
        r ∈ ExtensionBaseActiveIndices ett v hvFinal ∧
          ett.series.data.chosenVertex r.succ = some vs := by
      simpa [ExtensionBaseSupportClass] using hrClass
    exact hbetween ⟨r, hrData.1, hsr, hrt, hrVertex⟩
  · rintro ⟨hvs, hbetween⟩
    apply hoverlap.1.mpr
    refine ⟨hvs, ?_⟩
    rintro ⟨r, hrActive, hsr, hrt, hrVertex⟩
    apply hbetween
    refine ⟨r, ?_, hsr, hrt, hrVertex⟩
    simp [ExtensionBaseSupportClass, hrActive, hrVertex]

theorem helper_hseedBuild_496.{u_1, u_2} :
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
        jSlot.castSucc.succ = jSlot.succ.castSucc → TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc) → (
    ∀ {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B C
        → A.length ≤ B.length → TreeSequenceInitialSegment A B) → (0 : ℕ) < (↑jSlot : ℕ) →
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
        Tprevious.length < seed.length → TreeSequenceInitialSegment Tprevious seed →
        ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) Tprevious seed ∨
        (ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges jSlot.castSucc =
        ({ f } : Finset E) ∧ TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
        TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) adjoinSeed seed
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hjTreeIndex hseedTj commonPrefix hjPositive Tprevious hpreviousStrict hpreviousSeed
  generalize htarget : jSlot.castSucc = target
  cases ett.series.certified target with
  | initial =>
      have hzero := congrArg Fin.val htarget
      simp at hzero
      omega
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
          exact @helper_branch_1655 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
              (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalPositionPositive)
              (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@commonPrefix)
              (@hpreviousStrict) (@i) (@choice) (@currentEdges) (@currentKind) (@adjoined)
              (@adjoinedExactly) (@closedExtension) (@htarget)
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      chosenGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_1709 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
              (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalPositionPositive)
              (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@hpreviousSeed) (@i)
              (@currentKind) (@closedExtension) (@htarget)
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
          exact @helper_branch_1730 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
              (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalPositionPositive)
              (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@commonPrefix)
              (@hpreviousStrict) (@i) (@available) (@currentEdges) (@currentKind) (@adjoined)
              (@adjoinedExactly) (@closedExtension) (@htarget)

theorem helper_branch_880.{u_1, u_2} :
    helperBranch880Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot hjSlot stepSegment trace p0 indices0 rho1
      hrho1Proper hrho1One hb1Rho terminalPosition hterminalAt hterminalPositionPositive
      hterminalPositionBound seed hjTreeIndex hseedTj segmentVertexBefore transportSeedRoute
      commonPrefix supportColors hjPositive
  let Tprevious : TreeSequence G e0 :=
    ett.series.data.tree jSlot.castSucc.castSucc
  have hpreviousTj : TreeSequenceInitialSegment Tprevious
      (ett.series.data.tree jSlot.succ.castSucc) := by
    have hstep := stepSegment jSlot.castSucc (by simpa using hjPositive)
    rw [hjTreeIndex] at hstep
    exact hstep
  have hvNotPrevious : v ∉ TreeSequenceVertexSet Tprevious := by
    exact @helper_hvNotPrevious_1574 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@terminalPosition) (@hjPositive)
  have hpreviousStrict : Tprevious.length < seed.length := by
    exact @helper_hpreviousStrict_1615 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalAt)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@hpreviousTj) (@hvNotPrevious)
  have hpreviousSeed : TreeSequenceInitialSegment Tprevious seed :=
    commonPrefix hpreviousTj hseedTj (Nat.le_of_lt hpreviousStrict)
  have hseedBuild :
      (ett.series.data.kind jSlot.castSucc =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence
          (ett.series.data.coloring jSlot.castSucc) Tprevious seed) ∨
      ((ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
            TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
            TashkinovAugmentationSequence
              (ett.series.data.coloring jSlot.castSucc)
              adjoinSeed seed) := by
    exact @helper_hseedBuild_496 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@commonPrefix) (@hjPositive)
        (@hpreviousStrict) (@hpreviousSeed)
  have hseedBuildRho :
      (ett.series.data.kind jSlot.castSucc =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho1 Tprevious seed) ∨
      ((ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
            TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
            TashkinovAugmentationSequence rho1 adjoinSeed seed) := by
    rcases hseedBuild with hparallel | hserial
    · exact Or.inl ⟨hparallel.1,
        transportSeedRoute Tprevious hparallel.2⟩
    · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
          hadjoin, hroute⟩
      exact Or.inr ⟨hkind, f, adjoinSeed, hconnecting, hadjoin,
        transportSeedRoute adjoinSeed hroute⟩
  obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
    CertifiedETTRestriction G k e0 input T generating ett hMP
      jSlot.val hjPositive jSlot.isLt
  let nLower : Fin (lower.rounds + 1) := Fin.last lower.rounds
  have hnMap : Fin.castLE (by omega) nLower = jSlot.castSucc := by
    apply Fin.ext
    simp [nLower, hround]
  have hnTreeMap : Fin.castLE (by omega) nLower.castSucc =
      jSlot.castSucc.castSucc := by
    apply Fin.ext
    simp [nLower, hround]
  have htreeLower : lower.series.data.tree nLower.castSucc =
      Tprevious := by
    rw [htrees nLower.castSucc, hnTreeMap]
  have hcolorLower : lower.series.data.coloring nLower =
      ett.series.data.coloring jSlot.castSucc := by
    rw [(hdata nLower).1, hnMap]
  have hstoredLower : TashkinovStoredColors lower.series.data nLower =
      TashkinovStoredColors ett.series.data jSlot.castSucc := by
    rw [(hdata nLower).2.2.2.2.2.2.2.2.1, hnMap]
  have hkindLower : lower.series.data.kind nLower =
      ett.series.data.kind jSlot.castSucc := by
    rw [(hdata nLower).2.2.2.1, hnMap]
  have hconnectingLower : lower.series.data.connectingEdges nLower =
      ett.series.data.connectingEdges jSlot.castSucc := by
    rw [(hdata nLower).2.2.1, hnMap]
  have hstablePrevious : StableColoring Tprevious
      (TashkinovStoredColors ett.series.data jSlot.castSucc)
      (ett.series.data.coloring jSlot.castSucc) rho1 := by
    exact @helper_hstablePrevious_1829 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@hb1Rho) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (by assumption) (@hpreviousStrict)
        (@hpreviousSeed)
  have hstableLower : StableColoring
      (lower.series.data.tree nLower.castSucc)
      (TashkinovStoredColors lower.series.data nLower)
      (lower.series.data.coloring nLower) rho1 := by
    simpa [htreeLower, hstoredLower, hcolorLower] using hstablePrevious
  have hlowerPack := hlower lower (by omega) (by omega) hlowerMP
  have hmod : ModColoring lower rho1 :=
    hlowerPack.2.2.2.2.2 rho1 hrho1Proper hrho1One hstableLower
  have heligibleLower :
      (lower.series.data.kind nLower =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho1
          (lower.series.data.tree nLower.castSucc) seed) ∨
      ((lower.series.data.kind nLower =
            some TashkinovExtensionKind.SE ∨
          lower.series.data.kind nLower =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          lower.series.data.connectingEdges nLower = {f} ∧
            TreeSequenceAdjoinEdge
              (lower.series.data.tree nLower.castSucc) f adjoinSeed ∧
            TashkinovAugmentationSequence rho1 adjoinSeed seed) := by
    rcases hseedBuildRho with hparallel | hserial
    · left
      simpa [hkindLower, htreeLower] using hparallel
    · right
      rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
          hadjoin, hroute⟩
      refine ⟨?_, f, adjoinSeed, ?_, ?_, hroute⟩
      · simpa [hkindLower] using hkind
      · simpa [hconnectingLower] using hconnecting
      · simpa [htreeLower] using hadjoin
  obtain ⟨TjPrime, corr, hclosure, hcorrMP, hprimeElementary,
      hcaseSplit⟩ :=
    ExtensionBaseClosure lower rho1 seed v supportColors
      (by
        change TreeSequenceInitialSegment
          (lower.series.data.tree nLower.castSucc) seed
        rw [htreeLower]
        exact hpreviousSeed)
      (by
        change (lower.series.data.tree nLower.castSucc).length <
          seed.length
        rw [htreeLower]
        exact hpreviousStrict)
      (by exact heligibleLower) hmod hlowerMP
      (fun Tstar corr hcorrMP => by
        have hcorrRounds : corr.replacementETT.rounds = jSlot.val :=
          corr.rungAgreement.trans hround
        have hpackCorr := hlower corr.replacementETT
          corr.replacementETT.roundsPositive (by omega) hcorrMP
        unfold ColoredVertexSetElementary
        intro x hx y hy hxy
        exact hpackCorr.1 hx hy hxy)
  exact ⟨TjPrime, hclosure, hprimeElementary, hcaseSplit⟩

theorem helper_continuation_1011.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds), LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (sigma : PartialEdgeColoring E k),
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
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0), indices0 (Fin.last p0) = q →
    ∀ (u : V) (b : Fin (p0 + (1 : ℕ))) (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u p0
        indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
        IsProperEdgeColoring G rho2 → IsOneEdgeUncolored rho2 e0 →
    ∀ (_ : Fin (TjPrime.length + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (C : TreeSequence G e0), TashkinovAugmentationSequence rho2 seed C → ColoredVertexSetClosed
        G rho2 (TreeSequenceVertexSet C) → TreeSequenceVertexSet Tj0 ⊂ TreeSequenceVertexSet C →
        (0 : ℕ) < (↑jSlot : ℕ) → (ett.series.data.kind jSlot.castSucc = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence rho2 Tprevious seed ∨
        (ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges jSlot.castSucc =
        ({ f } : Finset E) ∧ TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
        TashkinovAugmentationSequence rho2 adjoinSeed seed) →
    ∀ (lower : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (⟨(↑jSlot : ℕ) + (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨(↑jSlot : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))), lower.rounds = (↑jSlot : ℕ) → MaximumProperty lower →
    let nLower : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds; lower.series.data.tree
        nLower.castSucc = Tprevious → lower.series.data.kind nLower = ett.series.data.kind
        jSlot.castSucc → lower.series.data.connectingEdges nLower =
        ett.series.data.connectingEdges jSlot.castSucc → StableColoring Tprevious
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho2 → ModColoring lower rho2 → TreeSequenceInitialSegment Tprevious C →
        Tprevious.length < C.length → False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot hjSlot trace p0 indices0 rho1 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed TjPrime hqLast u b traceB rho2
      hrho2Proper hrho2One uPosition Tprevious Tj0 C hrouteSeedC hclosedC hTj0StrictC hjPositive
      hseedBuildRho2 lower hround hLowerMP nLower hLowerTree hLowerKind hLowerConnecting
      hstablePrevious hmod hPreviousC hPreviousStrictC
  have hLowerEligible :
      (lower.series.data.kind nLower =
            some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence rho2 Tprevious C) ∨
        ((lower.series.data.kind nLower =
              some TashkinovExtensionKind.SE ∨
            lower.series.data.kind nLower =
              some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (adjoinSeed : TreeSequence G e0),
            lower.series.data.connectingEdges nLower = {f} ∧
              TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
              TashkinovAugmentationSequence rho2 adjoinSeed C) := by
    rcases hseedBuildRho2 with hparallel | hserial
    · exact Or.inl ⟨hLowerKind.trans hparallel.1,
        Relation.ReflTransGen.trans hparallel.2 hrouteSeedC⟩
    · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
          hadjoin, hroute⟩
      exact Or.inr
        ⟨Or.imp (hLowerKind.trans) (hLowerKind.trans) hkind,
          f, adjoinSeed, hLowerConnecting.trans hconnecting, hadjoin,
          Relation.ReflTransGen.trans hroute hrouteSeedC⟩
  have hcorrNonempty : Nonempty
      (CorrespondingExtendedTashkinovTree G k e0 lower rho2 C) := by
    exact @helper_hcorrNonempty_3307 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0) (@u) (@b)
        (@traceB) (@C) (@lower) (@hLowerTree) (@hmod) (@hPreviousC) (@hPreviousStrictC)
        (@hLowerEligible)
  obtain ⟨corr⟩ := hcorrNonempty
  have hreplacementMP : MaximumProperty corr.replacementETT :=
    MaximumPropertyTransport G k e0 lower rho2 hmod C corr hLowerMP
  have hcorrRounds : corr.replacementETT.rounds = jSlot.val :=
    corr.rungAgreement.trans hround
  have hCElementary :
      ColoredVertexSetElementary G rho2 (TreeSequenceVertexSet C) :=
    (hlower corr.replacementETT corr.replacementETT.roundsPositive
      (by omega) hreplacementMP).1
  have hbound : (TreeSequenceVertexSet C).card ≤
      (TreeSequenceVertexSet Tj0).card := by
    exact @helper_hbound_3342 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@trace) (@p0) (@indices0)
        (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime)
        (@hqLast) (@u) (@b) (@traceB) (@hrho2Proper) (@hrho2One) (@uPosition) (@C) (@hrouteSeedC)
        (@hclosedC) (@hjPositive) (@hseedBuildRho2) (@lower) (@hround) (@hstablePrevious) (@corr)
        (@hcorrRounds)
  have hstrictCard := Finset.card_lt_card hTj0StrictC
  exact (Nat.not_lt_of_ge hbound) hstrictCard

theorem helper_branch_1756.{u_1, u_2} :
    helperBranch1756Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v sigma q qSpecification
  subst q
  set q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds)
  intro hqTerminal hvFinal hfirstUpper hfirstPositive jSlot jSlotSpecification
  subst jSlot
  set jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by omega⟩ :
      Fin ett.rounds)
  intro hjSlot segmentTrans vertexTransfer trace hterminalJ p0 indices0 rho1 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj commonPrefix
      TjPrime hqLast u b traceB huOutside rho2 c1 hrho2Proper hrho2One uPosition Tprevious
      hpreviousTj hpreviousStrict hpreviousSeed Tj0 C hrouteSeedC hclosedC segmentVertexBeforeJ
      transportSeedRoute2 huC hTj0StrictC hjPositive
  have hseedBuildPhi :
      (ett.series.data.kind jSlot.castSucc =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence
          (ett.series.data.coloring jSlot.castSucc) Tprevious seed) ∨
      ((ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
            TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
            TashkinovAugmentationSequence
              (ett.series.data.coloring jSlot.castSucc)
              adjoinSeed seed) := by as_aux_lemma =>
    generalize htarget : jSlot.castSucc = target
    cases ett.series.certified target with
    | initial =>
        have hzero := congrArg Fin.val htarget
        simp at hzero
        omega
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
            exact @helper_branch_3050 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
                (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@terminalPosition)
                (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj)
                (@commonPrefix) (@hpreviousStrict) (@hjPositive) (@i) (@choice) (@currentEdges)
                (@currentKind) (@adjoined) (@adjoinedExactly) (@closedExtension) (@htarget)
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice
        seriesAlternativeFails chosenGamma gammaRule secondStable
        secondStableProper secondStableOneUncolored secondStableRelation
        exitWitness currentColoring currentProper currentOneUncolored
        currentStored currentEdges currentKind currentVertex currentOutside
        currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
            exact @helper_branch_3107 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
                (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@terminalPosition)
                (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj)
                (@hpreviousSeed) (@hjPositive) (@i) (@currentKind) (@closedExtension) (@htarget)
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
            exact @helper_branch_3129 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
                (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@terminalPosition)
                (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj)
                (@commonPrefix) (@hpreviousStrict) (@hjPositive) (@i) (@available)
                (@currentEdges) (@currentKind) (@adjoined) (@adjoinedExactly) (@closedExtension)
                (@htarget)
  have hseedBuildRho2 :
      (ett.series.data.kind jSlot.castSucc =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho2 Tprevious seed) ∨
      ((ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
            TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
            TashkinovAugmentationSequence rho2 adjoinSeed seed) := by
    as_aux_lemma =>
    rcases hseedBuildPhi with hparallel | hserial
    · exact Or.inl ⟨hparallel.1,
        transportSeedRoute2 Tprevious hparallel.2⟩
    · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
          hadjoin, hroute⟩
      exact Or.inr ⟨hkind, f, adjoinSeed, hconnecting, hadjoin,
        transportSeedRoute2 adjoinSeed hroute⟩
  obtain ⟨lower, hround, hLowerMP, htrees, hdata⟩ :=
    CertifiedETTRestriction G k e0 input T generating ett hMP
      jSlot.val hjPositive jSlot.isLt
  let nLower : Fin (lower.rounds + 1) := Fin.last lower.rounds
  have hnMap : Fin.castLE (by omega) nLower = jSlot.castSucc := by
    apply Fin.ext
    simp [nLower, hround]
  have hnTreeMap : Fin.castLE (by omega) nLower.castSucc =
      jSlot.castSucc.castSucc := by
    apply Fin.ext
    simp [nLower, hround]
  have hLowerTree : lower.series.data.tree nLower.castSucc =
      Tprevious := by
    rw [htrees nLower.castSucc, hnTreeMap]
  have hLowerColor : lower.series.data.coloring nLower =
      ett.series.data.coloring jSlot.castSucc := by
    rw [(hdata nLower).1, hnMap]
  have hLowerStored : TashkinovStoredColors lower.series.data nLower =
      TashkinovStoredColors ett.series.data jSlot.castSucc := by
    rw [(hdata nLower).2.2.2.2.2.2.2.2.1, hnMap]
  have hLowerKind : lower.series.data.kind nLower =
      ett.series.data.kind jSlot.castSucc := by
    rw [(hdata nLower).2.2.2.1, hnMap]
  have hLowerConnecting : lower.series.data.connectingEdges nLower =
      ett.series.data.connectingEdges jSlot.castSucc := by
    rw [(hdata nLower).2.2.1, hnMap]
  have hstablePrevious : StableColoring Tprevious
      (TashkinovStoredColors ett.series.data jSlot.castSucc)
      (ett.series.data.coloring jSlot.castSucc) rho2 := by
    exact @helper_hstablePrevious_3232 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@hterminalJ) (@p0) (@indices0)
        (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@u) (@b)
        (@traceB) (@c1) (@hpreviousStrict) (@hpreviousSeed) (@segmentVertexBeforeJ) (@hjPositive)
  have hstableLower : StableColoring
      (lower.series.data.tree nLower.castSucc)
      (TashkinovStoredColors lower.series.data nLower)
      (lower.series.data.coloring nLower) rho2 := by
    simpa [hLowerTree, hLowerStored, hLowerColor] using hstablePrevious
  have hLowerPack := hlower lower (by omega) (by omega) hLowerMP
  have hmod : ModColoring lower rho2 :=
    hLowerPack.2.2.2.2.2 rho2 hrho2Proper hrho2One hstableLower
  have hPreviousC : TreeSequenceInitialSegment Tprevious C := by
    rcases hseedBuildRho2 with hparallel | hserial
    · exact TashkinovAugmentationSequenceInitialSegment rho2 Tprevious C
        (Relation.ReflTransGen.trans hparallel.2 hrouteSeedC)
    · rcases hserial with ⟨-, f, adjoinSeed, -, hadjoin, hroute⟩
      exact segmentTrans hadjoin.2.1
        (TashkinovAugmentationSequenceInitialSegment rho2 adjoinSeed C
          (Relation.ReflTransGen.trans hroute hrouteSeedC))
  have huNotPrevious : u ∉ TreeSequenceVertexSet Tprevious := by
    intro huPrevious
    exact huOutside (vertexTransfer (hpreviousTj hjPositive) huPrevious)
  have hPreviousStrictC : Tprevious.length < C.length := by
    have hsubset : TreeSequenceVertexSet Tprevious ⊆
        TreeSequenceVertexSet C := vertexTransfer hPreviousC
    have hstrict : TreeSequenceVertexSet Tprevious <
        TreeSequenceVertexSet C :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, by
        intro heq
        exact huNotPrevious (heq.symm.subset huC)⟩
    have hcard := Finset.card_lt_card hstrict
    simpa [TreeSequenceVertexSet, Finset.card_image_of_injective,
      Tprevious.vertex_injective, C.vertex_injective] using hcard
  exact @helper_continuation_1011 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot)
      (@trace) (@p0) (@indices0) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@TjPrime) (@hqLast) (@u) (@b) (@traceB) (@hrho2Proper)
      (@hrho2One) (@uPosition) (@C) (@hrouteSeedC) (@hclosedC) (@hTj0StrictC) (@hjPositive)
      (@hseedBuildRho2) (@lower) (@hround) (@hLowerMP) (@hLowerTree) (@hLowerKind)
      (@hLowerConnecting) (@hstablePrevious) (@hmod) (@hPreviousC) (@hPreviousStrictC)
theorem helper_hterminalColorsNotRestored_1977.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds), ett.series.data.chosenVertex q.succ = some v
        → ett.series.data.gamma q.succ = some gamma → ett.series.data.delta q.succ = some delta →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal
        ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
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
        ett.series.data.chosenVertex r.succ = some vs) ∧ ( ((insert gammaS ({ deltaS } : Finset
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
  have hseparate : ∀ c : Fin k, c ∈ ({gamma, delta} : Finset (Fin k)) →
      c ∉ restorationColors := by
    intro c hcTerminal hcRestored
    obtain ⟨s, hsRestored, hcStored⟩ :=
      Finset.mem_biUnion.mp hcRestored
    have hsData := hsRestored
    simp only [ExtensionBaseRestorationIndices, Finset.mem_sdiff] at hsData
    have hsActiveData := hsData.1
    simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] at hsActiveData
    obtain ⟨hsFirst, hsKind, vs, hvsFinal, hsVertex, hsAppearance⟩ :=
      hsActiveData
    obtain ⟨vs', gammaS, deltaS, hsVertex', hsGamma, hsDelta⟩ :=
      hPESlotData s hsKind
    have hvsEq : vs' = vs :=
      Option.some.inj (hsVertex'.symm.trans hsVertex)
    subst vs'
    have hsStored : ett.series.data.stored s.succ =
        {gammaS, deltaS} :=
      hPEStored s gammaS deltaS hsKind hsGamma hsDelta
    have hsNeQ : s ≠ q := by
      intro hsq
      apply hsData.2
      simpa [hsq] using hqClass
    have hsq : s.val < q.val := by
      have hsle : s.val ≤ q.val := by omega
      exact lt_of_le_of_ne hsle (fun heq => hsNeQ (Fin.ext heq))
    have hoverlap := hpairOverlapColors s q vs v gammaS deltaS gamma delta
      hsData.1 hqActive hsq hsVertex hqVertex hsGamma hsDelta hqGamma
      hqDelta
    have hnonempty :
        (({gammaS, deltaS} : Finset (Fin k)) ∩ {gamma, delta}).Nonempty := by
      refine ⟨c, ?_⟩
      rw [← hsStored]
      exact Finset.mem_inter.mpr ⟨hcStored, hcTerminal⟩
    have hsameSupport : vs = v := (hoverlap.1.mp hnonempty).1
    apply hsData.2
    simp only [ExtensionBaseSupportClass, Finset.mem_filter]
    refine ⟨hsData.1, ?_⟩
    simpa [hsameSupport] using hsVertex
  exact ⟨hseparate gamma (by simp), hseparate delta (by simp)⟩

theorem helper_branch_2914.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating), MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k) (sigma :
        PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (indices0 : Fin
        (p0 + (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
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
    ∀ (TjPrime : TreeSequence G e0), indices0 (Fin.last p0) = q →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ( (0 : ℕ) <
        (↑jSlot : ℕ) → Tprevious.length < seed.length) → ( (0 : ℕ) < (↑jSlot : ℕ) →
        TreeSequenceInitialSegment Tprevious seed) →
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V) (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0)) (_ : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (rho3 : PartialEdgeColoring
        E k), IsProperEdgeColoring G rho3 → IsOneEdgeUncolored rho3 e0 →
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho3 →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition :
        ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    ∀ (C : TreeSequence G e0), TashkinovClosure rho3 U C → TashkinovAugmentationSequence rho3 seed
        C → TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ⊂
        TreeSequenceVertexSet C → (
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {y : V}, y ∈ TreeSequenceVertexSet A → y ∈ TreeVerticesBefore (ett.series.data.tree
        jSlot.succ.castSucc) v hterminalJ) → (
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho3 S seed) → (0 : ℕ) < (↑jSlot :
        ℕ) → False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot hjSlot trace hterminalJ p0 indices0 gamma0 delta0
      rho1 terminalPosition hterminalPositionPositive hterminalPositionBound seed hjTreeIndex
      hseedTj _ _ commonPrefix TjPrime hqLast H x componentPath u exitPath Tprevious
      hpreviousStrict hpreviousSeed zPosition u0 exitPath0 zPosition0 rho3 hrho3Proper hrho3One
      hd1 uPosition huPositionPositive huPositionBound U C hclosureUC hrouteSeedC hTjStrictC
      segmentVertexBefore transportSeedRoute hjPositive
  have hstablePrevious : StableColoring Tprevious
      (TashkinovStoredColors ett.series.data jSlot.castSucc)
      (ett.series.data.coloring jSlot.castSucc) rho3 := by
    constructor
    · exact @helper_branch_5420 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@hterminalJ) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (by assumption) (@hpreviousStrict)
        (@hpreviousSeed) (@rho3) (@hd1) (by assumption) (@hjPositive)
    · intro y hy
      exact hd1.2 y (segmentVertexBefore (hpreviousSeed hjPositive)
        (hpreviousStrict hjPositive) hy)
  have hseedBuildRho :
      (ett.series.data.kind jSlot.castSucc =
          some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho3 Tprevious seed) ∨
      ((ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.SE ∨
          ett.series.data.kind jSlot.castSucc =
            some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          ett.series.data.connectingEdges jSlot.castSucc = {f} ∧
            TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
            TashkinovAugmentationSequence rho3 adjoinSeed seed) := by
    generalize htarget : jSlot.castSucc = target
    cases ett.series.certified target with
    | initial =>
        have hzero := congrArg Fin.val htarget
        simp at hzero
        omega
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice
        seriesAlternativeFails chosenGamma gammaRule secondStable
        secondStableProper secondStableOneUncolored secondStableRelation
        exitWitness currentColoring currentProper currentOneUncolored
        currentStored currentEdges currentKind currentVertex currentOutside
        currentDelta currentGamma closedExtension orderedExtension
        strictExtension =>
        have hi : i.succ = jSlot.castSucc := htarget.symm
        have hroute : TashkinovAugmentationSequence
            (ett.series.data.coloring jSlot.castSucc) Tprevious seed := by
          have hfull := closedExtension.1
          rw [hi, hjTreeIndex] at hfull
          have hbase : TreeSequenceInitialSegment Tprevious seed :=
            hpreviousSeed hjPositive
          exact TashkinovAugmentationSequenceRestrict _ Tprevious seed _
            (by simpa [Tprevious, hi] using hfull) hbase hseedTj
        exact Or.inl ⟨by simpa [htarget] using currentKind,
          transportSeedRoute Tprevious hroute⟩
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind
        currentVertex currentOutside currentDelta currentGamma adjoined
        adjoinedExactly closedExtension orderedExtension strictExtension =>
          exact @helper_branch_5475 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
              (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@terminalPosition)
              (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj)
              (by assumption) (@commonPrefix) (@hpreviousStrict) (@rho3) (by assumption)
              (@hjPositive) (@i) (@choice) (@currentEdges) (@currentKind) (@adjoined)
              (@adjoinedExactly) (@closedExtension) (@htarget)
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension
        orderedExtension strictExtension =>
          exact @helper_branch_5528 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
              (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@terminalPosition)
              (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj)
              (by assumption) (@commonPrefix) (@hpreviousStrict) (@rho3) (by assumption)
              (@hjPositive) (@i) (@available) (@currentEdges) (@currentKind) (@adjoined)
              (@adjoinedExactly) (@closedExtension) (@htarget)
  have hbound : (TreeSequenceVertexSet C).card ≤
      (TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)).card := by
    exact @helper_hbound_5582 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@v) (@gamma) (@delta) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@trace) (@p0)
        (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@hqLast) (@x) (@componentPath) (@u)
        (@exitPath) (@zPosition) (@u0) (@exitPath0) (@zPosition0) (@rho3) (@hrho3Proper)
        (@hrho3One) (@uPosition) (@huPositionPositive) (@huPositionBound) (@C) (@hclosureUC)
        (@hrouteSeedC) (@hjPositive) (@hstablePrevious) (@hseedBuildRho)
  exact (Nat.not_lt_of_ge hbound) (Finset.card_lt_card hTjStrictC)

theorem helper_hterminalPositionPositive_1612.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds), ett.series.data.kind q.succ = some
        TashkinovExtensionKind.PE → ett.series.data.chosenVertex q.succ = some v →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal
        ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = v → (1 : ℕ) ≤
        (↑terminalPosition : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hqKind hqVertex hvFinal
      hfirstUpper hfirstPositive jSlot hjSlot stageToStage terminalPosition hterminalAt
  generalize htarget : q.succ = target
  cases hcert : ett.series.certified target with
  | initial => exact (Fin.succ_ne_zero q htarget).elim
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have hbad : some TashkinovExtensionKind.SE =
        some TashkinovExtensionKind.PE :=
      currentKind.symm.trans (by simpa [htarget] using hqKind)
    cases hbad
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have hbad : some TashkinovExtensionKind.RE =
        some TashkinovExtensionKind.PE :=
      currentKind.symm.trans (by simpa [htarget] using hqKind)
    cases hbad
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      chosenGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
          exact @helper_branch_1321 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
              (@hqVertex) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@stageToStage)
              (@terminalPosition) (@hterminalAt) (@i) (@previousProper) (@previousOneUncolored)
              (@previousClosed) (@previousNotStronglyClosed) (@noRevisiting) (@choice)
              (@seriesAlternativeFails) (@chosenGamma) (@gammaRule) (@secondStable)
              (@secondStableProper) (@secondStableOneUncolored) (@secondStableRelation)
              (@exitWitness) (@currentColoring) (@currentProper) (@currentOneUncolored)
              (@currentStored) (@currentEdges) (@currentKind) (@currentVertex) (@currentOutside)
              (@currentDelta) (@currentGamma) (@closedExtension) (@orderedExtension)
              (@strictExtension) (@htarget) (@hcert)

theorem helper_hseedBuild_3505.{u_1, u_2} :
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
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
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
    ∀ (TjPrime : TreeSequence G e0), indices0 (Fin.last p0) = q →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc; ( (0 : ℕ) <
        (↑jSlot : ℕ) → Tprevious.length < seed.length) → ( (0 : ℕ) < (↑jSlot : ℕ) →
        TreeSequenceInitialSegment Tprevious seed) →
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V) (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0)) (_ : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (_ : Fin (TjPrime.length +
        (1 : ℕ))), (0 : ℕ) < (↑jSlot : ℕ) →
    ∀ (lower : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (⟨(↑jSlot : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨(↑jSlot : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))), lower.rounds = (↑jSlot : ℕ) → ett.series.data.kind
        jSlot.castSucc = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        (ett.series.data.coloring jSlot.castSucc) Tprevious seed ∨ (ett.series.data.kind
        jSlot.castSucc = some TashkinovExtensionKind.SE ∨ ett.series.data.kind jSlot.castSucc =
        some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges jSlot.castSucc =
        ({ f } : Finset E) ∧ TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
        TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) adjoinSeed seed
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot hjSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj
      commonPrefix TjPrime hqLast H x componentPath u exitPath Tprevious hpreviousStrict
      hpreviousSeed zPosition u0 exitPath0 zPosition0 uPosition hjPositive lower hround
  generalize htarget : jSlot.castSucc = target
  cases ett.series.certified target with
  | initial =>
      have hzero := congrArg Fin.val htarget
      simp at hzero
      omega
  | SE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind
      currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
          exact @helper_branch_5782 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
              (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalPositionPositive)
              (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@commonPrefix)
              (@hpreviousStrict) (@hjPositive) (@i) (@choice) (@currentEdges) (@currentKind)
              (@adjoined) (@adjoinedExactly) (@closedExtension) (@htarget)
  | PE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice
      seriesAlternativeFails chosenGamma gammaRule secondStable
      secondStableProper secondStableOneUncolored secondStableRelation
      exitWitness currentColoring currentProper currentOneUncolored
      currentStored currentEdges currentKind currentVertex currentOutside
      currentDelta currentGamma closedExtension orderedExtension
      strictExtension =>
          exact @helper_branch_5839 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
              (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalPositionPositive)
              (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@hpreviousSeed) (@hjPositive)
              (@i) (@currentKind) (@closedExtension) (@htarget)
  | RE i previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension =>
          exact @helper_branch_5861 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
              (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalPositionPositive)
              (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@commonPrefix)
              (@hpreviousStrict) (@hjPositive) (@i) (@available) (@currentEdges) (@currentKind)
              (@adjoined) (@adjoinedExactly) (@closedExtension) (@htarget)

theorem helper_orderRestrict_1438.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B →
    ∀ (x y : V), x ∈ TreeSequenceVertexSet A → y ∈ TreeSequenceVertexSet A → TreeVertexOrder B x y
        → TreeVertexOrder A x y := by
  classical
  intro V E G e0 A B hAB x y hxA hyA hxy
  rcases hAB with ⟨hlen, hvertices, hedges⟩
  rcases Finset.mem_image.mp hxA with ⟨ix, _, hix⟩
  rcases Finset.mem_image.mp hyA with ⟨iy, _, hiy⟩
  rcases hxy with ⟨jx, jy, hjx, hjy, hjlt⟩
  have hjxEq : jx = Fin.castLE (Nat.succ_le_succ hlen) ix := by
    apply B.vertex_injective
    exact hjx.trans ((hvertices ix).trans hix).symm
  have hjyEq : jy = Fin.castLE (Nat.succ_le_succ hlen) iy := by
    apply B.vertex_injective
    exact hjy.trans ((hvertices iy).trans hiy).symm
  refine ⟨ix, iy, hix, hiy, ?_⟩
  rw [hjxEq, hjyEq] at hjlt
  simpa using hjlt

theorem helper_hjInitial_1603.{u_1, u_2} :
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
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) →
    ∀ t ∈ ExtensionBaseRestorationIndices ett v hvFinal, TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc) (ett.series.data.tree t.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hjSlot stageToStage t htRest
  have htData := htRest
  simp only [ExtensionBaseRestorationIndices, Finset.mem_sdiff] at htData
  have htActiveData := htData.1
  simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
    Finset.mem_univ, true_and] at htActiveData
  have hjt : jSlot.val + 1 ≤ t.val + 1 := by
    rw [hjSlot]
    exact htActiveData.1
  have hseg := stageToStage (jSlot.val + 1) (t.val + 1)
    (by omega) hjt (by omega)
  convert hseg using 1 <;> congr 1

theorem helper_hclassPrepared_1698.{u_1, u_2} :
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
    ⟩ : Fin ett.rounds); (
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
        Finset (Fin k))) →
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc), x ≠ v → (
    ∃ t ∈ ExtensionBaseRestorationIndices ett v hvFinal, ett.series.data.chosenVertex t.succ =
        some x) →
    ∃ (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (gammaClass : Fin (p + (1 : ℕ)) → Fin
        k) (deltaClass : Fin (p + (1 : ℕ)) → Fin k), (
    ∀ (a b : Fin (p + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices a) : ℕ) < (↑(indices b) : ℕ)) ∧
        (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal x ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = r) ∧ (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gammaClass a)) ∧ (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (deltaClass a)) ∧ (
    ∀ (a : Fin p), gammaClass a.succ = deltaClass a.castSucc) ∧ Function.Injective (Fin.cons
        (gammaClass (0 : Fin (p + (1 : ℕ)))) deltaClass) ∧ MissingColors G
        (ett.series.data.coloring jSlot.castSucc) x = MissingColors G sigma x \
        ({deltaClass (Fin.last p)} : Finset (Fin k)) ∪ ({gammaClass (0 : Fin (p + (1 : ℕ)))} :
        Finset (Fin k)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot hclassPackage x hxJ hxNe
  rintro ⟨t, htRest, htVertex⟩
  have htData := htRest
  simp only [ExtensionBaseRestorationIndices, Finset.mem_sdiff] at htData
  have htClass : t ∈ ExtensionBaseSupportClass ett v hvFinal x := by
    simp [ExtensionBaseSupportClass, htData.1, htVertex]
  obtain ⟨p, indices, gammaClass, deltaClass, hincreasing, hclass,
      hgammaClass, hdeltaClass, hchain, hinjective,
      hunsupportedClass, hmissing⟩ := hclassPackage x ⟨t, htClass⟩
  dsimp at hmissing
  exact ⟨p, indices, gammaClass, deltaClass, hincreasing, hclass,
    hgammaClass, hdeltaClass, hchain, hinjective, hmissing.2⟩

theorem helper_hb1Tj_1978.{u_1, u_2} :
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
  ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma)
    (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)),
  let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
  StableColoringBeforeVertex T v hvFinal
      (TashkinovStoredColors ett.series.data jSlot.castSucc)
      (ett.series.data.coloring jSlot.castSucc) rho1 →
  TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ ⊆
      TreeVerticesBefore T v hvFinal →
  StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
    (TashkinovStoredColors ett.series.data jSlot.castSucc)
    (ett.series.data.coloring jSlot.castSucc) rho1 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace hterminalJ rho1 hb1Rho hbeforeTjFinal
  constructor
  · intro f hfIncident hfControlled
    obtain ⟨x, hxBefore, hxf⟩ := hfIncident
    apply hb1Rho.1 f ⟨x, hbeforeTjFinal hxBefore, hxf⟩
    obtain ⟨c, hcControlled, hfc⟩ := hfControlled
    refine ⟨c, ?_, hfc⟩
    rcases Finset.mem_union.mp hcControlled with hcMissing | hcStored
    · apply Finset.mem_union_left
      obtain ⟨z, hzBefore, hcz⟩ := Finset.mem_biUnion.mp hcMissing
      exact Finset.mem_biUnion.mpr
        ⟨z, hbeforeTjFinal hzBefore, hcz⟩
    · exact Finset.mem_union_right _ hcStored
  · intro x hxBefore
    exact hb1Rho.2 x (hbeforeTjFinal hxBefore)

theorem helper_hinitialB_2039.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma :
        PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v hvFinal
        sigma) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0
        + (1 : ℕ)) → Fin k), (
    ∀ (a b : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
        → (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.gamma (indices0 a).succ = some (gamma0 a)) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a)) →
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps); (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ ExtensionBaseSupportClass ett v hvFinal v
        → s ≠ q → ett.series.data.chosenVertex s.succ = some v → ett.series.data.gamma s.succ =
        some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett s
        v rho1 gammaS deltaS) → indices0 (Fin.last p0) = q → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.chosenVertex (indices0 a).succ = some v) →
    ∀ (b a : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → ETTStrongInterchangeable ett (indices0 a)
        v rho1 (gamma0 a) (delta0 a) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hvFinal trace p0 indices0
      gamma0 delta0 hincreasing0 hclass0 hgamma0 hdelta0 rho1 hb4Interchange hqLast hsupport0 b a
      hab
  apply hb4Interchange (indices0 a) (gamma0 a) (delta0 a)
  · exact (hclass0 (indices0 a)).2 ⟨a, rfl⟩
  · intro heq
    have haLast : a.val < (Fin.last p0).val :=
      lt_of_lt_of_le hab (Fin.le_last b)
    have hindexLt := hincreasing0 a (Fin.last p0) haLast
    rw [hqLast, heq] at hindexLt
    exact (Nat.lt_irrefl _ hindexLt)
  · exact hsupport0 a
  · exact hgamma0 a
  · exact hdelta0 a

theorem helper_hTjInitialB_2054.{u_1, u_2} :
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
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))))) →
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds), (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) →
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), indices0 (Fin.last
        p0) = q →
    ∀ (b a : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc) (ett.series.data.tree (indices0
        a).succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hjSlot stageToStage p0 indices0 hclass0 terminalPosition hqLast b a hab
  have haClass := (hclass0 (indices0 a)).2 ⟨a, rfl⟩
  have haData := haClass
  simp only [ExtensionBaseSupportClass, Finset.mem_filter] at haData
  have haActive := haData.1
  have haActiveData := haActive
  simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
    Finset.mem_univ, true_and] at haActiveData
  have hjIndexLe : jSlot.val + 1 ≤ (indices0 a).val + 1 := by
    rw [hjSlot]
    exact haActiveData.1
  have hseg := stageToStage (jSlot.val + 1)
    ((indices0 a).val + 1) (by omega) hjIndexLe (by omega)
  convert hseg using 1 <;> congr 1

theorem helper_hseedBeforeU_2115.{u_1, u_2} :
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
  by_contra hnot
  have huBound : uPosition.val ≤ seed.length := Nat.le_of_not_gt hnot
  let i : Fin (seed.length + 1) := ⟨uPosition.val, by omega⟩
  have hcast : Fin.castLE (Nat.succ_le_succ hseedPrime.1) i =
      uPosition := by
    apply Fin.ext
    rfl
  apply huNotSeed
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  refine ⟨i, ?_⟩
  exact (hseedPrime.2.1 i).symm.trans (hcast ▸ huPosition)

theorem helper_hrightOutside_2349.{u_1, u_2} :
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
    by omega
    ⟩ : Fin M.length);
    ∀ (i : Fin Tj0.length), M.vertex mIndex.succ = Tj0.vertex i.succ → Tj0.vertex i.succ ∉
        TreeSequenceVertexSet U := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound TjPrime uPosition huPositionPositive huPositionBound U Tj0 M
      hleftSegment n hnU hnM mIndex i hvertexMTj hmem
  simp only [TreeSequenceVertexSet, Finset.mem_image,
    Finset.mem_univ, true_and] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hmvertex : M.vertex
        (Fin.castLE (Nat.succ_le_succ hleftSegment.1) a) =
      U.vertex a := hleftSegment.2.1 a
  have heq : M.vertex mIndex.succ =
      M.vertex
        (Fin.castLE (Nat.succ_le_succ hleftSegment.1) a) :=
    hvertexMTj.trans (ha.symm.trans hmvertex.symm)
  have hindex := congrArg Fin.val (M.vertex_injective heq)
  simp [mIndex] at hindex
  omega

theorem helper_hsupportColors_2684.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T), (
    ∀ (t : Fin ett.rounds) (gammaT deltaT : Fin k), ett.series.data.kind t.succ = some
        TashkinovExtensionKind.PE → ett.series.data.gamma t.succ = some gammaT →
        ett.series.data.delta t.succ = some deltaT → ett.series.data.stored t.succ = (insert
        gammaT ({ deltaT } : Finset (Fin k)) : Finset (Fin k))) →
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds),
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ; (supportColors = (ExtensionBaseSupportClass ett
        v hvFinal v).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ) →
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → gammaS ∈ supportColors ∧ deltaS ∈ supportColors := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hvFinal hPEStored p0 indices0
      supportColors hsupportSet s gammaS deltaS hs hsGamma hsDelta
  have hsClass := (Finset.mem_erase.mp hs).2
  have hsClassData := hsClass
  simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hsClassData
  have hsActiveData := hsClassData.1
  simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
    Finset.mem_univ, true_and] at hsActiveData
  have hsStored := hPEStored s gammaS deltaS hsActiveData.2.1
    hsGamma hsDelta
  rw [hsupportSet]
  constructor <;> apply Finset.mem_biUnion.mpr <;>
    refine ⟨s, hsClass, ?_⟩ <;> rw [hsStored] <;> simp

theorem helper_branch_2800.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
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
  have hi : i = q := by
    apply Fin.ext
    simpa using (congrArg Fin.val htarget).symm
  subst i
  have hvChoice : choice.vertex = v :=
    Option.some.inj
      (currentVertex.symm.trans (by simpa [htarget] using hqVertex))
  refine ⟨choice.edge, ?_, ?_, ?_, ?_⟩
  · simpa [htarget] using currentEdges
  · simpa [hvChoice] using choice.edgeIncident
  · simpa [htarget] using currentProper
  · simpa [htarget] using currentOneUncolored

theorem helper_hterminalColorControlled_2850.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (gamma delta : Fin k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    let controlled : Finset (Fin k) := TreeMissingColors (ett.series.data.coloring q.succ)
        (ett.series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors ett.series.data q.succ;
        ett.series.data.stored q.succ = (insert gamma ({ delta } : Finset (Fin k)) : Finset (Fin
        k)) →
    ∀ c ∈ (insert gamma ({ delta } : Finset (Fin k)) : Finset (Fin k)), c ∈ controlled := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive gamma delta q controlled
      hterminalRawStored c hc
  by_cases hcMissing : c ∈ TreeMissingColors
      (ett.series.data.coloring q.succ)
      (ett.series.data.tree q.succ.castSucc)
  · exact Finset.mem_union_left _ hcMissing
  · apply Finset.mem_union_right
    unfold TashkinovStoredColors
    have hqSuccNe : q.succ.val ≠ 0 := Nat.succ_ne_zero q.val
    rw [ite_eq_right hqSuccNe]
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hcMissing⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨q.succ, Finset.mem_univ _, ?_⟩
    rw [ite_eq_left le_rfl, hterminalRawStored]
    exact hc

theorem helper_hsigmaControlled_2871.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (sigma : PartialEdgeColoring E
        k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); StableColoring (ett.series.data.tree q.succ.castSucc)
        (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring q.succ) sigma →
    let controlled : Finset (Fin k) := TreeMissingColors (ett.series.data.coloring q.succ)
        (ett.series.data.tree q.succ.castSucc) ∪ TashkinovStoredColors ett.series.data q.succ;
        StableColoring (ett.series.data.tree q.succ.castSucc) controlled (ett.series.data.coloring
        q.succ) sigma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive sigma q hsigmaTerminal controlled
  constructor
  · intro f hfIncident hfControl
    apply hsigmaTerminal.1 f hfIncident
    obtain ⟨c, hc, hfc⟩ := hfControl
    refine ⟨c, ?_, hfc⟩
    rcases Finset.mem_union.mp hc with hcMissing | hcControlled
    · exact Finset.mem_union_left _ hcMissing
    · change c ∈ TreeMissingColors
          (ett.series.data.coloring q.succ)
          (ett.series.data.tree q.succ.castSucc) ∪
        TashkinovStoredColors ett.series.data q.succ at hcControlled
      exact hcControlled
  · exact hsigmaTerminal.2

theorem helper_hTjInitialEarlier_3214.{u_1, u_2} :
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
    ⟩ : Fin ett.rounds); (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal → (
    ∀ (a b : ℕ), (1 : ℕ) ≤ a →
    ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds), TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
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
      componentPath u exitPath zPosition s hs
  have hsClass := (Finset.mem_erase.mp hs).2
  have hsData := hsClass
  simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hsData
  have hsActive := hsData.1
  simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
    Finset.mem_univ, true_and] at hsActive
  have hjIndexLe : jSlot.val + 1 ≤ s.val + 1 := by
    rw [hjSlot]
    exact hsActive.1
  have hseg := stageToStage (jSlot.val + 1) (s.val + 1)
    (by omega) hjIndexLe (by omega)
  convert hseg using 1 <;> congr 1

theorem helper_hseedBeforeU_3367.{u_1, u_2} :
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
    ∀ (TjPrime : TreeSequence G e0), TreeSequenceInitialSegment seed TjPrime →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V) (_ : (TwoColorIncidenceGraph G rho1 gamma
        delta).Walk (Sum.inl x) (Sum.inl u0)) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (uPosition : Fin (TjPrime.length + (1 : ℕ))),
        TjPrime.vertex uPosition = u0 → u0 ∉ TreeSequenceVertexSet seed → seed.length <
        (↑uPosition : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed TjPrime hseedPrime H
      x componentPath u exitPath zPosition u0 exitPath0 zPosition0 uPosition huPosition huNotSeed
  by_contra hnot
  have huBound : uPosition.val ≤ seed.length := Nat.le_of_not_gt hnot
  let i : Fin (seed.length + 1) := ⟨uPosition.val, by omega⟩
  have hcast : Fin.castLE (Nat.succ_le_succ hseedPrime.1) i =
      uPosition := by
    apply Fin.ext
    rfl
  apply huNotSeed
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  refine ⟨i, ?_⟩
  exact (hseedPrime.2.1 i).symm.trans (hcast ▸ huPosition)

theorem helper_hbeforeZMissing_3860.{u_1, u_2} :
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
    ⟩ : Fin ett.rounds); (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps); (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v → TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc) (ett.series.data.tree q.succ.castSucc) →
    ∀ (TjPrime : TreeSequence G e0) (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime), u0 ∉
        TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) →
    ∀ (z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (rho3
        : PartialEdgeColoring E k), (
    ∀ y ∈ ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 ∪ ({ z0 } :
        Finset V) ∪ (TreeVerticesBefore TjPrime u0 huPrime0 ∪ ({ u0 } : Finset V))).erase
        u0).erase z0, MissingColors G rho3 y = MissingColors G rho1 y) → (
    ∀ {y : V}, y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 → y ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∧ y ≠ z0) →
    ∀ y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0, y ≠ v →
        MissingColors G rho3 y = MissingColors G (ett.series.data.coloring jSlot.castSucc) y := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot vertexTransfer trace rho1 hb2Missing hTjQ TjPrime u0
      huPrime0 huOutside0 z0 hz0 rho3 hd2Missing hbeforeZData y hy hyTerminal
  have hyData := hbeforeZData hy
  have hyU : y ≠ u0 := by
    intro hyu
    subst y
    exact huOutside0 (vertexTransfer hTjQ hyData.1)
  have hRhoThreeOne : MissingColors G rho3 y =
      MissingColors G rho1 y := by
    apply hd2Missing y
    apply Finset.mem_erase.mpr
    refine ⟨hyData.2, Finset.mem_erase.mpr ⟨hyU, ?_⟩⟩
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hy)
  exact hRhoThreeOne.trans
    (hb2Missing.1 y (Finset.mem_erase.mpr ⟨hyTerminal, hyData.1⟩))

theorem helper_hrightOutside_3985.{u_1, u_2} :
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
    ∀ (_ : V ⊕ E) (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V) (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0)) (zPosition0 :
        Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (uPosition : Fin
        (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
        (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length) (hzPositionPositive : (1 : ℕ) ≤
        (↑zPosition0 : ℕ)) (hzPositionBound : (↑zPosition0 : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    let Z : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑zPosition0 : ℕ) hzPositionPositive hzPositionBound;
    ∀ (M : TreeSequence G e0), TreeSequenceInitialSegment U M →
    ∀ (n : ℕ), U.length ≤ n →
    ∀ (hnM : n + (1 : ℕ) ≤ M.length),
    let j : Fin M.length := (⟨n,
    by omega
    ⟩ : Fin M.length);
    ∀ (i : Fin Z.length), M.vertex j.succ = Z.vertex i.succ → Z.vertex i.succ ∉
        TreeSequenceVertexSet U := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H a
      x componentPath u exitPath zPosition u0 exitPath0 zPosition0 uPosition huPositionPositive
      huPositionBound hzPositionPositive hzPositionBound U Z M hleftSegment n hnU hnM j i
      hvertexMZ hmem
  simp only [TreeSequenceVertexSet, Finset.mem_image,
    Finset.mem_univ, true_and] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hmvertex : M.vertex
        (Fin.castLE (Nat.succ_le_succ hleftSegment.1) a) =
      U.vertex a := hleftSegment.2.1 a
  have heq : M.vertex j.succ = M.vertex
      (Fin.castLE (Nat.succ_le_succ hleftSegment.1) a) :=
    hvertexMZ.trans (ha.symm.trans hmvertex.symm)
  have hindex := congrArg Fin.val (M.vertex_injective heq)
  simp [j] at hindex
  omega

theorem helper_hvFinal_2051.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (generating : PartialEdgeColoring E k)
  (ett : ExtendedTashkinovTree G k e0 input T generating)
  (hpositive : (0 : ℕ) < ett.rounds) (v : V),
  let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
  v ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) →
  q.succ.castSucc = (⟨ett.rounds, by omega⟩ : Fin (ett.rounds + (2 : ℕ))) →
  v ∈ TreeSequenceVertexSet T := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hvStage hqTreeIndex
  have hvPenultimate : v ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨ett.rounds, by omega⟩) := by
    simpa [hqTreeIndex] using hvStage
  rcases ett.abovePenultimate with ⟨hlen, hvertices, hedges⟩
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hvPenultimate ⊢
  obtain ⟨i, hi⟩ := hvPenultimate
  refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, ?_⟩
  exact (hvertices i).trans hi

theorem helper_segmentTrans_2087.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B
        C → TreeSequenceInitialSegment A C := by
  classical
  intro V E G e0 A B C hAB hBC
  rcases hAB with ⟨hab, hvab, heab⟩
  rcases hBC with ⟨hbc, hvbc, hebc⟩
  refine ⟨hab.trans hbc, ?_, ?_⟩
  · intro i
    simpa using
      (hvbc (Fin.castLE (Nat.succ_le_succ hab) i)).trans (hvab i)
  · intro i
    simpa using (hebc (Fin.castLE hab i)).trans (heab i)

theorem helper_stepSegment_2099.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (i : Fin (ett.rounds + (1 : ℕ))), (0 : ℕ) < (↑i : ℕ) →
        TreeSequenceInitialSegment (ett.series.data.tree i.castSucc) (ett.series.data.tree i.succ)
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett i hi
  cases ett.series.certified i with
  | initial => simp at hi
  | SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
  | PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption
  | RE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => assumption

theorem helper_vertexTransfer_2114.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
  {A B : TreeSequence G e0},
  TreeSequenceInitialSegment A B →
  TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
  classical
  intro V E G e0 A B hAB x hx
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hx ⊢
  obtain ⟨i, rfl⟩ := hx
  rcases hAB with ⟨hlen, hvertices, hedges⟩
  exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, hvertices i⟩

theorem helper_qStageToFinal_2202.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (↑q : ℕ) + (1 : ℕ) = ett.rounds → q.succ.castSucc = (⟨ett.rounds,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ))) →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T), ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) +
        (1 : ℕ) → (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal → (
    ∀ {A B : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B) →
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), x ∈ TreeSequenceVertexSet
        T := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hqTreeIndex hvFinal
      hfirstUpper hfirstPositive vertexTransfer x hx
  have hxPenultimate : x ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨ett.rounds, by omega⟩) := by
    simpa [hqTreeIndex] using hx
  exact vertexTransfer ett.abovePenultimate hxPenultimate

theorem helper_hslot_2247.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (
    ∀ (t : Fin ett.rounds), ett.series.data.kind t.succ = some TashkinovExtensionKind.PE →
    ∃ (vt : V) (gammaT : Fin k) (deltaT : Fin k), ett.series.data.chosenVertex t.succ = some vt ∧
        ett.series.data.gamma t.succ = some gammaT ∧ ett.series.data.delta t.succ = some deltaT) →
    ∀ (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds), (
    ∀ (r : Fin ett.rounds), (↑r : ℕ) ≤ (↑q : ℕ) ∧ ett.series.data.kind r.succ = some
        TashkinovExtensionKind.PE ∧ ett.series.data.chosenVertex r.succ = some u ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = r) →
    ∀ (a : Fin (p + (1 : ℕ))),
    ∃ (gammaA : Fin k) (deltaA : Fin k), ett.series.data.gamma (indices a).succ = some gammaA ∧
        ett.series.data.delta (indices a).succ = some deltaA := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive q hPESlotData u p indices henumerates a
  have henum := (henumerates (indices a)).2 ⟨a, rfl⟩
  obtain ⟨uA, gammaA, deltaA, huA, hgammaA, hdeltaA⟩ :=
    hPESlotData (indices a) henum.2.1
  have huEq : uA = u := Option.some.inj (huA.symm.trans henum.2.2)
  exact ⟨gammaA, deltaA, hgammaA, hdeltaA⟩

theorem helper_hslotData_2282.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T), (
    ∀ (t : Fin ett.rounds), ett.series.data.kind t.succ = some TashkinovExtensionKind.PE →
    ∃ (vt : V) (gammaT : Fin k) (deltaT : Fin k), ett.series.data.chosenVertex t.succ = some vt ∧
        ett.series.data.gamma t.succ = some gammaT ∧ ett.series.data.delta t.succ = some deltaT) →
    ∀ t ∈ ExtensionBaseRestorationIndices ett v hvFinal,
    ∃ (vt : V) (gammaT : Fin k) (deltaT : Fin k), ett.series.data.chosenVertex t.succ = some vt ∧
        ett.series.data.gamma t.succ = some gammaT ∧ ett.series.data.delta t.succ = some deltaT
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal hPESlotData t htRest
  have htData := htRest
  simp only [ExtensionBaseRestorationIndices, Finset.mem_sdiff] at htData
  have htActiveData := htData.1
  simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
    Finset.mem_univ, true_and] at htActiveData
  exact hPESlotData t htActiveData.2.1

theorem helper_hinitialSI_2295.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma :
        PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); (↑q : ℕ) + (1 : ℕ) = ett.rounds →
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T), ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) +
        (1 : ℕ) → (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal → (
    ∀ (t : Fin ett.rounds) (vt : V) (gamma delta : Fin k), t ∈ ExtensionBaseActiveIndices ett v
        hvFinal → (↑t : ℕ) < (↑q : ℕ) → ett.series.data.chosenVertex t.succ = some vt →
        ett.series.data.gamma t.succ = some gamma → ett.series.data.delta t.succ = some delta →
        ETTStrongInterchangeable ett t vt sigma gamma delta) →
    ∀ (t : Fin ett.rounds) (vt : V) (gammaT deltaT : Fin k), t ∈ ExtensionBaseActiveIndices ett v
        hvFinal → t ≠ q → ett.series.data.chosenVertex t.succ = some vt → ett.series.data.gamma
        t.succ = some gammaT → ett.series.data.delta t.succ = some deltaT →
        ETTStrongInterchangeable ett t vt sigma gammaT deltaT := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive hstrongInterchange t vt gammaT deltaT htActive htNe htVertex
      htGamma htDelta
  have htq : t.val < q.val := by
    have htBound : t.val ≤ q.val := by omega
    exact lt_of_le_of_ne htBound fun h => htNe (Fin.ext h)
  exact hstrongInterchange t vt gammaT deltaT htActive htq htVertex
    htGamma htDelta

theorem helper_hseedTj_2451.{u_1, u_2} :
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
  ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
    (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
    (hterminalPositionBound :
      (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
  let seed : TreeSequence G e0 :=
    TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
      hterminalPositionPositive hterminalPositionBound;
  jSlot.castSucc.succ = jSlot.succ.castSucc →
  TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hjTreeIndex
  refine ⟨?_, ?_, ?_⟩
  · change terminalPosition.val ≤
      (ett.series.data.tree jSlot.castSucc.succ).length
    rw [hjTreeIndex]
    exact hterminalPositionBound
  · intro i
    rfl
  · intro i
    rfl

theorem helper_hseedTerminal_2462.{u_1, u_2} :
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
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
        (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = v →
    ∀ (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound; seed.vertex
        (Fin.last seed.length) = v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalAt hterminalPositionPositive
      hterminalPositionBound seed
  have hlast : Fin.castLE (Nat.succ_le_succ hterminalPositionBound)
      (Fin.last terminalPosition.val) = terminalPosition := by
    apply Fin.ext
    simp
  simpa [seed, TreeSequencePrefix, hlast] using hterminalAt

theorem helper_hseedVertexBefore_2479.{u_1, u_2} :
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
        (Fin.last seed.length) = v → TreeSequenceInitialSegment seed T →
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore T v hvFinal := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot vertexTransfer terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedTerminal hseedFinal i hi
  unfold TreeVerticesBefore
  apply Finset.mem_filter.mpr
  constructor
  · exact vertexTransfer hseedFinal (by simp [TreeSequenceVertexSet])
  · let p : Fin (T.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hseedFinal.1) i
    let z : Fin (T.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hseedFinal.1) (Fin.last seed.length)
    refine ⟨p, z, hseedFinal.2.1 i,
      (hseedFinal.2.1 (Fin.last seed.length)).trans hseedTerminal, ?_⟩
    simpa [p, z] using hi

theorem helper_segmentVertexBefore_2493.{u_1, u_2} :
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
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound; (
    ∀ (i : Fin (seed.length + (1 : ℕ))), (↑i : ℕ) < seed.length → seed.vertex i ∈
        TreeVerticesBefore T v hvFinal) →
    ∀ {A : TreeSequence G e0}, TreeSequenceInitialSegment A seed → A.length < seed.length →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet A → x ∈ TreeVerticesBefore T v hvFinal := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hseedVertexBefore A hAseed hAlen x hxA
  obtain ⟨hAseedLen, hAseedVertices, -⟩ := hAseed
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hxA
  obtain ⟨i, rfl⟩ := hxA
  have hi : (Fin.castLE (Nat.succ_le_succ hAseedLen) i).val <
      seed.length := by
    change i.val < seed.length
    omega
  rw [← hAseedVertices i]
  exact hseedVertexBefore _ hi

theorem helper_transportSeedRoute_2514.{u_1, u_2} :
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
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound; (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentation (ett.series.data.coloring jSlot.castSucc) A
        B → TreeSequenceInitialSegment B seed → TashkinovAugmentation rho1 A B) →
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed → TashkinovAugmentationSequence rho1 S seed := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace rho1 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed transportStep S hroute
  unfold TashkinovAugmentationSequence at hroute ⊢
  induction hroute using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head A B hAB hBseed ih =>
    have hBsegment : TreeSequenceInitialSegment B seed :=
      TashkinovAugmentationSequenceInitialSegment
        (ett.series.data.coloring jSlot.castSucc) B seed hBseed
    exact Relation.ReflTransGen.head (transportStep hAB hBsegment) ih

theorem helper_hqLast_2554.{u_1, u_2} :
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
    ⟩ : Fin ett.rounds); q ∈ ExtensionBaseSupportClass ett v hvFinal v →
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds), (
    ∀ (a b : Fin (p0 + (1 : ℕ))), (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
        → (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) →
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))), indices0 (Fin.last
        p0) = q := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hqClass p0 indices0 hincreasing0 hclass0 terminalPosition
  obtain ⟨a, ha⟩ := (hclass0 q).1 hqClass
  have haLast : a = Fin.last p0 := by
    by_contra hne
    have halt : a < Fin.last p0 := Fin.lt_last_iff_ne_last.mpr hne
    have hindexLt := hincreasing0 a (Fin.last p0) halt
    rw [ha] at hindexLt
    have hqMax : ∀ r : Fin ett.rounds, r.val ≤ q.val := by
      intro r
      omega
    exact (Nat.not_lt_of_ge (hqMax (indices0 (Fin.last p0)))) hindexLt
  rw [← haLast, ha]

theorem helper_hkind0_2572.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T) (p0 : ℕ) (indices0
        : Fin (p0 + (1 : ℕ)) → Fin ett.rounds), (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) →
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.kind (indices0 a).succ = some
        TashkinovExtensionKind.PE := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal p0 indices0 hclass0 a
  have ha := (hclass0 (indices0 a)).2 ⟨a, rfl⟩
  have haData := ha
  simp only [ExtensionBaseSupportClass, Finset.mem_filter] at haData
  have hactive := haData.1
  simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
    Finset.mem_univ, true_and] at hactive
  exact hactive.2.1

theorem helper_hdeltaAvoidsTj_2598.{u_1, u_2} :
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
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (delta0 : Fin (p0 + (1 : ℕ)) → Fin
        k), (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a)) → (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.chosenVertex (indices0 a).succ = some v) →
    ∀ (a : Fin (p0 + (1 : ℕ))), delta0 a ∉ TreeMissingColors (ett.series.data.coloring
        jSlot.castSucc) (ett.series.data.tree jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hdeltaExclusion p0 indices0 delta0 hclass0 hdelta0 hsupport0 a
  have haClass := (hclass0 (indices0 a)).2 ⟨a, rfl⟩
  have haData := haClass
  simp only [ExtensionBaseSupportClass, Finset.mem_filter] at haData
  exact hdeltaExclusion.2 (indices0 a) v hvFinal (delta0 a)
    haData.1 (hsupport0 a) (hdelta0 a)

theorem helper_hbeforeTjFinal_2616.{u_1, u_2} :
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
  (
  ∀ {A B : TreeSequence G e0},
  TreeSequenceInitialSegment A B →
  TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B) →
  ∀ (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)),
  TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc) T →
  TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ ⊆
    TreeVerticesBefore T v hvFinal := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot vertexTransfer hterminalJ hTjFinal x hx
  unfold TreeVerticesBefore at hx ⊢
  simp only [Finset.mem_filter] at hx ⊢
  refine ⟨vertexTransfer hTjFinal hx.1, ?_⟩
  rcases hx.2 with ⟨ix, iv, hix, hiv, hlt⟩
  refine ⟨Fin.castLE (Nat.succ_le_succ hTjFinal.1) ix,
    Fin.castLE (Nat.succ_le_succ hTjFinal.1) iv,
    (hTjFinal.2.1 ix).trans hix,
    (hTjFinal.2.1 iv).trans hiv, ?_⟩
  simpa using hlt

theorem helper_hprefixSubset_2691.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds),
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (b : Fin (p0 + (1 : ℕ))), ((ExtensionBaseCaseOneIndices ett p0 indices0 b).biUnion fun (t :
        Fin ett.rounds) ↦ ett.series.data.stored t.succ) ⊆ supportColors := by
  classical
  intro V E _ _ _ G k e0 input T generating ett p0 indices0 supportColors b c hc
  obtain ⟨t, ht, hct⟩ := Finset.mem_biUnion.mp hc
  unfold ExtensionBaseCaseOneIndices at ht
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
  exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hct⟩

theorem helper_hUPrime_2738.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) (TjPrime : TreeSequence
        G e0) (uPosition : Fin (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤
        (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound; TreeSequenceInitialSegment U TjPrime := by
  classical
  intro V E G e0 TjPrime uPosition huPositionPositive huPositionBound U
  refine ⟨huPositionBound, ?_, ?_⟩
  · intro i
    simp [U, TreeSequencePrefix]
  · intro i
    simp [U, TreeSequencePrefix]

theorem helper_hprimeVertexBefore_2750.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] (G : LooplessMultigraph V E) (e0 : E) (TjPrime :
        TreeSequence G e0) (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (uPosition : Fin
        (TjPrime.length + (1 : ℕ))), TjPrime.vertex uPosition = u →
    ∀ (i : Fin (TjPrime.length + (1 : ℕ))), (↑i : ℕ) < (↑uPosition : ℕ) → TjPrime.vertex i ∈
        TreeVerticesBefore TjPrime u huPrime := by
  classical
  intro V E _ G e0 TjPrime u huPrime uPosition huPosition i hi
  let _ := Fintype.ofFinite V
  unfold TreeVerticesBefore
  apply Finset.mem_filter.mpr
  constructor
  · simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨i, rfl⟩
  · exact ⟨i, uPosition, rfl, huPosition, hi⟩

theorem helper_transportURoute_2771.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (sigma : PartialEdgeColoring E k) (hvFinal : v ∈
        TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 :
        ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (TjPrime : TreeSequence G e0) (u : V) (b : Fin (p0 + (1 : ℕ))) (traceB :
        ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition :
        ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound; (
    ∀ {A B : TreeSequence G e0}, TashkinovAugmentation rho1 A B → TreeSequenceInitialSegment B U →
        TashkinovAugmentation rho2 A B) →
    ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence rho1 S U →
        TashkinovAugmentationSequence rho2 S U := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v sigma hvFinal trace p0 indices0 rho1 TjPrime u
      b traceB rho2 uPosition huPositionPositive huPositionBound U transportUStep S hroute
  unfold TashkinovAugmentationSequence at hroute ⊢
  induction hroute using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head A B hAB hBU ih =>
      have hBsegment : TreeSequenceInitialSegment B U :=
        TashkinovAugmentationSequenceInitialSegment rho1 B U hBU
      exact Relation.ReflTransGen.head
        (transportUStep hAB hBsegment) ih

theorem helper_hterminalInclusion_2787.{u_1, u_2} :
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
      u b traceB rho2 c3 hterminalMissingEq c hc
  rw [hmissing0.2] at hc
  rcases Finset.mem_union.mp hc with hcSigma | hcGamma
  · apply Finset.mem_union_left
    rw [hterminalMissingEq, hb2Missing.2]
    exact (Finset.mem_sdiff.mp hcSigma).1
  · apply Finset.mem_union_right
    have hcgamma : c = gamma0 0 := Finset.mem_singleton.mp hcGamma
    simpa [hcgamma] using c3

theorem helper_huU_2850.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) (TjPrime : TreeSequence
        G e0) (u : V) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex uPosition = u →
    ∀ (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤
        TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound; u ∈ TreeSequenceVertexSet U := by
  classical
  intro V E G e0 TjPrime u uPosition huPosition huPositionPositive huPositionBound U
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  refine ⟨Fin.last U.length, ?_⟩
  change TjPrime.vertex (Fin.castLE (Nat.succ_le_succ huPositionBound)
    (Fin.last uPosition.val)) = u
  have hindex : Fin.castLE (Nat.succ_le_succ huPositionBound)
      (Fin.last uPosition.val) = uPosition := by
    apply Fin.ext
    rfl
  rw [hindex]
  exact huPosition

theorem helper_prefixSegment_2868.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
  (A : TreeSequence G e0) (r : ℕ) (hr : (1 : ℕ) ≤ r) (hrA : r ≤ A.length),
  TreeSequenceInitialSegment (TreeSequencePrefix A r hr hrA) A := by
  classical
  intro V E G e0 A r hr hrA
  refine ⟨hrA, ?_, ?_⟩
  · intro i
    simp [TreeSequencePrefix]
  · intro i
    simp [TreeSequencePrefix]

theorem helper_prefixPrefix_2877.{u_1, u_2} :
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
  ∀ (p0 : ℕ) (_ :
  Fin (p0 + (1 : ℕ)) →
  Fin ett.rounds)
    (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
    (_ : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
    (_ : (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length)
    (TjPrime : TreeSequence G e0) (_ : Fin (TjPrime.length + (1 : ℕ)))
    (A : TreeSequence G e0) (r : ℕ) (hr : (1 : ℕ) ≤ r) (hrA : r + (1 : ℕ) ≤ A.length),
  TreeSequenceInitialSegment
    (TreeSequencePrefix A r hr (Nat.le_trans (Nat.le_succ r) hrA))
    (TreeSequencePrefix A (r + (1 : ℕ)) (by omega) hrA) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound TjPrime uPosition A r hr hrA
  refine ⟨Nat.le_succ r, ?_, ?_⟩
  · intro i
    change A.vertex _ = A.vertex _
    congr 1
  · intro i
    change A.edge _ = A.edge _
    congr 1

theorem helper_prefixSelf_2890.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
  (A : TreeSequence G e0),
  TreeSequencePrefix A A.length A.positive le_rfl = A := by
  classical
  intro V E G e0 A
  cases A with
  | mk len pos vertex edge vinj einj first attach =>
    rw [TreeSequence.mk.injEq]
    refine ⟨rfl, ?_, ?_⟩
    · apply heq_of_eq
      funext i
      rfl
    · apply heq_of_eq
      funext i
      rfl

theorem helper_hleftX_3005.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) (TjPrime : TreeSequence
        G e0) (uPosition : Fin (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤
        (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    ∀ (M : TreeSequence G e0), TreeSequenceInitialSegment U M →
    ∀ (n : ℕ) (hnU : U.length ≤ n) (hnM' : n ≤ M.length),
    let X : TreeSequence G e0 := TreeSequencePrefix M n (Nat.le_trans U.positive hnU) hnM';
    ∀ {x : V}, x ∈ TreeSequenceVertexSet U → x ∈ TreeSequenceVertexSet X := by
  classical
  intro V E G e0 TjPrime uPosition huPositionPositive huPositionBound U M hleftSegment n hnU hnM'
      X x hxU
  simp only [TreeSequenceVertexSet, Finset.mem_image,
    Finset.mem_univ, true_and] at hxU ⊢
  obtain ⟨a, ha⟩ := hxU
  refine ⟨Fin.castLE (Nat.succ_le_succ hnU) a, ?_⟩
  change M.vertex _ = x
  calc
    M.vertex _ = M.vertex
        (Fin.castLE (Nat.succ_le_succ hleftSegment.1) a) := by
      congr 1
    _ = U.vertex a := hleftSegment.2.1 a
    _ = x := ha

theorem helper_segmentVertexBeforeJ_3151.{u_1, u_2} :
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
  obtain ⟨hAseedLen, hAseedVertices, -⟩ := hAseed
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hxA
  obtain ⟨i, rfl⟩ := hxA
  have hi : (Fin.castLE (Nat.succ_le_succ hAseedLen) i).val <
      seed.length := by
    change i.val < seed.length
    omega
  rw [← hAseedVertices i]
  exact hseedVertexBeforeJ _ hi

theorem helper_transportSeedRoute2_3173.{u_1, u_2} :
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
  unfold TashkinovAugmentationSequence at hroute ⊢
  induction hroute using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head A B hAB hBseed ih =>
      have hBsegment : TreeSequenceInitialSegment B seed :=
        TashkinovAugmentationSequenceInitialSegment _ B seed hBseed
      exact Relation.ReflTransGen.head
        (transportSeedStep2 hAB hBsegment) ih

theorem helper_hsupportSet_3222.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T) (p0 : ℕ) (indices0
        : Fin (p0 + (1 : ℕ)) → Fin ett.rounds), (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r) →
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ; supportColors = (ExtensionBaseSupportClass ett v
        hvFinal v).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal p0 indices0 hclass0 supportColors
  ext c
  simp only [supportColors, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨a, hc⟩
    exact ⟨indices0 a, (hclass0 (indices0 a)).2 ⟨a, rfl⟩, hc⟩
  · rintro ⟨s, hs, hc⟩
    obtain ⟨a, rfl⟩ := (hclass0 s).1 hs
    exact ⟨a, hc⟩

theorem helper_hgammaSupport_3247.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (gamma : Fin k) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin
        ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k),
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ; (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.stored (indices0 a).succ = (insert (gamma0 a)
        ({delta0 a} : Finset (Fin k)) : Finset (Fin k))) → gamma0 (Fin.last p0) = gamma → gamma ∈
        supportColors := by
  classical
  intro V E _ _ _ G k e0 input T generating ett gamma p0 indices0 gamma0 delta0 supportColors
      hstored0 hgammaLast
  simp only [supportColors, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  refine ⟨Fin.last p0, ?_⟩
  rw [hstored0, hgammaLast]
  simp

theorem helper_hdeltaSupport_3253.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (delta : Fin k) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin
        ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k),
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ; (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.stored (indices0 a).succ = (insert (gamma0 a)
        ({delta0 a} : Finset (Fin k)) : Finset (Fin k))) → delta0 (Fin.last p0) = delta → delta ∈
        supportColors := by
  classical
  intro V E _ _ _ G k e0 input T generating ett delta p0 indices0 gamma0 delta0 supportColors
      hstored0 hdeltaLast
  simp only [supportColors, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  refine ⟨Fin.last p0, ?_⟩
  rw [hstored0, hdeltaLast]
  simp

theorem helper_hgammaFirstSupport_3259.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0
        delta0 : Fin (p0 + (1 : ℕ)) → Fin k),
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ; (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.stored (indices0 a).succ = (insert (gamma0 a)
        ({delta0 a} : Finset (Fin k)) : Finset (Fin k))) →
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ))); gammaFirst ∈ supportColors := by
  classical
  intro V E _ _ _ G k e0 input T generating ett p0 indices0 gamma0 delta0 supportColors hstored0
      gammaFirst
  simp only [supportColors, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  refine ⟨0, ?_⟩
  rw [hstored0]
  simp [gammaFirst]

theorem helper_hb4Earlier_3295.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma :
        PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v hvFinal
        sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps); (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ ExtensionBaseSupportClass ett v hvFinal v
        → s ≠ q → ett.series.data.chosenVertex s.succ = some v → ett.series.data.gamma s.succ =
        some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett s
        v rho1 gammaS deltaS) →
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett v hvFinal
        v).erase q → ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ =
        some deltaS → ETTStrongInterchangeable ett s v rho1 gammaS deltaS := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hvFinal trace rho1
      hb4Interchange s gammaS deltaS hs hsGamma hsDelta
  have hsNe := (Finset.mem_erase.mp hs).1
  have hsClass := (Finset.mem_erase.mp hs).2
  have hsClassData := hsClass
  simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hsClassData
  exact hb4Interchange s gammaS deltaS hsClass hsNe hsClassData.2
    hsGamma hsDelta

theorem helper_hterminalInclusion_3322.{u_1, u_2} :
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
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ))); MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v ⊆ MissingColors G rho1 v ∪ ({ gammaFirst } :
        Finset (Fin k)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 hmissing0 rho1 hb2Missing
      gammaFirst c hc
  rw [hmissing0.2] at hc
  rcases Finset.mem_union.mp hc with hcSigma | hcFirst
  · apply Finset.mem_union_left
    rw [hb2Missing.2]
    exact (Finset.mem_sdiff.mp hcSigma).1
  · apply Finset.mem_union_right
    simpa [gammaFirst] using hcFirst

theorem helper_branch_3361.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
    ∀ (i : Fin ett.rounds), ett.series.data.kind i.succ = some TashkinovExtensionKind.SE → q.succ
        = i.succ →
    ∃ (fN : E), ett.series.data.connectingEdges i.succ = ({ fN } : Finset E) ∧ Incident G v fN ∧
        IsProperEdgeColoring G (ett.series.data.coloring i.succ) ∧ IsOneEdgeUncolored
        (ett.series.data.coloring i.succ) e0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqKind i currentKind htarget
  have hbad : some TashkinovExtensionKind.SE =
      some TashkinovExtensionKind.PE :=
    currentKind.symm.trans (by simpa [htarget] using hqKind)
  cases hbad

theorem helper_branch_3370.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds); ett.series.data.kind q.succ = some TashkinovExtensionKind.PE →
    ∀ (i : Fin ett.rounds), ett.series.data.kind i.succ = some TashkinovExtensionKind.RE → q.succ
        = i.succ →
    ∃ (fN : E), ett.series.data.connectingEdges i.succ = ({ fN } : Finset E) ∧ Incident G v fN ∧
        IsProperEdgeColoring G (ett.series.data.coloring i.succ) ∧ IsOneEdgeUncolored
        (ett.series.data.coloring i.succ) e0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqKind i currentKind htarget
  have hbad : some TashkinovExtensionKind.RE =
      some TashkinovExtensionKind.PE :=
    currentKind.symm.trans (by simpa [htarget] using hqKind)
  cases hbad

theorem helper_hvDegree_3468.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k)
        (hvFinal : v ∈ TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v
        hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
        IsProperEdgeColoring G rho1 → gamma ≠ delta → delta ∈ MissingColors G rho1 v →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta; @SimpleGraph.degree
        (Sum V E) H (@Sum.inl V E v) (@Fintype.ofFinite (@Set.Elem (Sum V E)
        (@SimpleGraph.neighborSet (Sum V E) H (@Sum.inl V E v))) (@Subtype.finite (Sum V E)
        (@Finite.instSum V E (@Finite.of_fintype V inst) (@Finite.of_fintype E inst_1))
        (@Membership.mem (Sum V E) (Set (Sum V E)) (@Set.instMembership (Sum V E))
        (@SimpleGraph.neighborSet (Sum V E) H (@Sum.inl V E v))))) ≤ (1 : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v gamma delta sigma hvFinal trace rho1
      hrho1Proper hgammaDelta hdeltaMissing H
  have hdegree := MissingColorIncidenceEndpoint G rho1 delta gamma
    hgammaDelta.symm hrho1Proper v hdeltaMissing
  have hcolorOrder :
      TwoColorIncidenceGraph G rho1 delta gamma = H := by
    apply SimpleGraph.ext
    funext a b
    cases a <;> cases b <;>
      simp [H, TwoColorIncidenceGraph, or_comm]
  rw [hcolorOrder] at hdegree
  exact hdegree

theorem helper_hvSub_3480.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k)
        (hvFinal : v ∈ TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v
        hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta; @SimpleGraph.degree
        (Sum V E) H (@Sum.inl V E v) (@Fintype.ofFinite (@Set.Elem (Sum V E)
        (@SimpleGraph.neighborSet (Sum V E) H (@Sum.inl V E v))) (@Subtype.finite (Sum V E)
        (@Finite.instSum V E (@Finite.of_fintype V inst) (@Finite.of_fintype E inst_1))
        (@Membership.mem (Sum V E) (Set (Sum V E)) (@Set.instMembership (Sum V E))
        (@SimpleGraph.neighborSet (Sum V E) H (@Sum.inl V E v))))) ≤ (1 : ℕ) → (H.neighborSet
        (Sum.inl v)).Subsingleton := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v gamma delta sigma hvFinal trace rho1 H hvDegree
  let : Fintype (H.neighborSet (Sum.inl v)) := Fintype.ofFinite _
  have hcard : (H.neighborFinset (Sum.inl v)).card ≤ 1 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hvDegree
  intro a ha b hb
  exact (Finset.card_le_one.mp hcard) a
    (by simpa [SimpleGraph.mem_neighborFinset] using ha) b
    (by simpa [SimpleGraph.mem_neighborFinset] using hb)

end GoldbergSeymour.ExtensionBaseProof

end
