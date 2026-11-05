/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CertifiedETTRestriction
public import LeanPool.GoldbergSeymour.ExtensionBaseClaim45Singleton
public import LeanPool.GoldbergSeymour.LowerRoundInductionHypothesis
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceSuffix
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceRestrict
public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmBTrace
public import LeanPool.GoldbergSeymour.TechnicalTheoremBase
public import LeanPool.GoldbergSeymour.ExtensionBaseRestorationTrace
public import LeanPool.GoldbergSeymour.ETTStrongInterchangeable
public import LeanPool.GoldbergSeymour.InternalEdges

/-!
# Extension Base Auxiliary Lemmas

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperHclaim45Package4916Conditions.{u_1, u_2} : Prop :=
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
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (_ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (indices0 : Fin
        (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : IsProperEdgeColoring G rho1) (_ : IsOneEdgeUncolored rho1 e0) (_ : (
    ∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
        MissingColors G rho1 x = MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive
        : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (_ :
        seed.vertex (Fin.last seed.length) = v) (_ : TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc) (ett.series.data.tree q.succ.castSucc)),
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0) (_ : TashkinovClosure rho1 seed TjPrime) (_ :
        ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime)) (_ :
        TreeSequenceInitialSegment seed TjPrime) (_ : StableColoringBeforeVertex
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ (TashkinovStoredColors
        ett.series.data jSlot.castSucc) (ett.series.data.coloring jSlot.castSucc) rho1) (_ : (
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, MissingColors G rho1 x ∩ supportColors = ∅)),
    let gammaFirst : Fin k := gamma0 (0 : Fin (p0 + (1 : ℕ)));
    ∀ (_ : gamma ∈ supportColors) (_ : delta ∈ supportColors) (_ : gamma ≠ delta) (_ : (
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length) (_ : seed.length ≤ (↑a : ℕ)),
        rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) = ett.series.data.coloring
        jSlot.castSucc ((ett.series.data.tree jSlot.succ.castSucc).edge a))) (_ : delta ∉
        TreeMissingColors (ett.series.data.coloring jSlot.castSucc) (ett.series.data.tree
        jSlot.succ.castSucc)) (_ : v ∈ TreeSequenceVertexSet seed) (fN : E) (_ : delta ∈
        MissingColors G rho1 v),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (_ : V ⊕ E) (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (_ :
        componentPath.IsPath) (_ : {z : V ⊕ E | z ∈ componentPath.support} = C) (_ : x ∉
        TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet
        TjPrime) (u : V) (exitPath : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x)
        (Sum.inl u)) (_ : exitPath.IsPath) (_ : (2 : ℕ) ≤ exitPath.length) (_ : (
    ∀ y ∈ exitPath.support, y ∈ componentPath.support)) (_ : (
    ∀ w ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪ TreeSequenceVertexSet
        TjPrime, Sum.inl w ∈ exitPath.support ↔ w = u)) (_ : (
    ∃ g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)
        ∪ TreeSequenceVertexSet TjPrime) gamma, Incident G u g ∧ Sum.inr g ∈ exitPath.support)) (_
        : ¬Incident G u fN) (_ : u ∈ TreeSequenceVertexSet TjPrime) (_ : u ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) (_ : MaximumDegree G + (1 : ℕ) ≤ k),
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
        beta) → ((0 : ℕ) < p0 →
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
    ∀ v ∈ ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z hz ∪ { z } ∪
        (TreeVerticesBefore TjPrime u huPrime ∪ { u })).erase u).erase z, MissingColors G rho3 v =
        MissingColors G rho1 v) ∧ (
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) ∧ (↑a :
        ℕ) < (↑zPosition : ℕ) ∧ (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → rho3 f = rho1 f) ∧
        (beta ∈ MissingColors G rho1 z → delta ∈ MissingColors G rho3 z) ∧ (z ∈ TreeVerticesBefore
        TjPrime u huPrime → MissingColors G rho3 z = MissingColors G rho1 z) ∧ gammaFirst ∈
        MissingColors G rho3 u) → (p0 = (0 : ℕ) → gammaFirst = gamma) →
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
    ∀ y ∈ ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 ∪ { z0 } ∪
        (TreeVerticesBefore TjPrime u0 huPrime0 ∪ { u0 })).erase u0).erase z0, MissingColors G
        rho3 y = MissingColors G rho1 y) ∧ (
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) ∧ (↑a :
        ℕ) < (↑zPosition0 : ℕ) ∧ (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u0 ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → rho3 f = rho1 f) ∧
        (beta0 ∈ MissingColors G rho1 z0 → delta ∈ MissingColors G rho3 z0) ∧ (z0 ∈
        TreeVerticesBefore TjPrime u0 huPrime0 → MissingColors G rho3 z0 = MissingColors G rho1
        z0) ∧ gammaFirst ∈ MissingColors G rho3 u0

theorem ExtendedTashkinovTree.pe_chosenVertex_mem_previousTree
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (q : Fin ett.rounds) (v : V)
    (hqKind : ett.series.data.kind q.succ = some TashkinovExtensionKind.PE)
    (hqVertex : ett.series.data.chosenVertex q.succ = some v) :
    v ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) := by
  classical
  generalize htarget : q.succ = target
  cases ett.series.certified target with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    exact (Fin.succ_ne_zero q htarget).elim
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
    have hi : i = q := by
      apply Fin.ext
      simpa using (congrArg Fin.val htarget).symm
    subst i
    have hvChoice : choice.vertex = v :=
      Option.some.inj
        (currentVertex.symm.trans (by simpa [htarget] using hqVertex))
    simpa [hvChoice] using choice.vertexDefective.1

private theorem helper_stageToStage_226.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (_ : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (_ : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal)
      (_ : (∀ (A : TreeSequence G e0), TreeSequenceInitialSegment A A))
      (_ :
        (∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B)
          (_ : TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C))
      (_ :
        (∀ (i : Fin (ett.rounds + (1 : ℕ))) (_ : (0 : ℕ) < (↑i : ℕ)),
          TreeSequenceInitialSegment (ett.series.data.tree i.castSucc)
            (ett.series.data.tree i.succ)))
      (a b : ℕ) (_ : (1 : ℕ) ≤ a) (_hab : a ≤ b) (_hb : b ≤ ett.rounds),
    TreeSequenceInitialSegment
      (ett.series.data.tree (⟨a, by omega⟩ : Fin (ett.rounds + (2 : ℕ))))
      (ett.series.data.tree (⟨b, by omega⟩ : Fin (ett.rounds + (2 : ℕ)))) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive segmentRefl segmentTrans stepSegment a b ha hab hb
  have chain : ∀ (d : ℕ) (_hd : a + d ≤ b),
      TreeSequenceInitialSegment
        (ett.series.data.tree ⟨a, by omega⟩)
        (ett.series.data.tree ⟨a + d, by omega⟩) := by
    intro d hd
    induction d with
    | zero => simpa using segmentRefl (ett.series.data.tree ⟨a, by omega⟩)
    | succ d ih =>
        have hprev := ih (by omega)
        let idx : Fin (ett.rounds + 1) := ⟨a + d, by omega⟩
        have hone := stepSegment idx (by dsimp [idx]; omega)
        have hone' : TreeSequenceInitialSegment
            (ett.series.data.tree ⟨a + d, by omega⟩)
            (ett.series.data.tree ⟨a + (d + 1), by omega⟩) := by
          simpa [idx, Nat.add_assoc] using hone
        exact segmentTrans hprev hone'
  have hchain := chain (b - a) (by omega)
  convert hchain using 1; congr 1; apply Fin.ext; simp; omega

private theorem helper_hLowerElementary_277.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
       [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett)
      (hpositive : (0 : ℕ) < ett.rounds)
      (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (v : V),
    let _ : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (_ : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (_ : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (_ : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal) (r : Fin ett.rounds)
      (_ : (↑r : ℕ) < (↑q : ℕ)),
    ColoredVertexSetElementary G (ett.series.data.coloring r.castSucc)
      (TreeSequenceVertexSet (ett.series.data.tree r.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower v this q hqTerminal hvFinal
      hfirstUpper hfirstPositive r hrq
  by_cases hrZero : r.val = 0
  · have hbase : ColoredVertexSetElementary G
        (ett.series.data.coloring 0)
        (TreeSequenceVertexSet
          (ett.series.data.tree ⟨1, by omega⟩)) :=
      (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
    have hrColor : r.castSucc = (0 : Fin (ett.rounds + 1)) := by
      apply Fin.ext
      simpa using hrZero
    have hrTree : r.succ.castSucc =
        (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simpa using hrZero
    simpa [hrColor, hrTree] using hbase
  · obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
      CertifiedETTRestriction G k e0 input T generating ett hMP r.val
        (by omega) (by omega)
    have hpack := hlower lower (by omega) (by omega) hlowerMP
    exact hpack.1

private theorem helper_hxP_352.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let _ : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T) (_ :
        ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (_ : (0 : ℕ) <
        ETTFirstAppearanceIndex ett v hvFinal) (_ : (
    ∀ (a b : ℕ) (_ : (1 : ℕ) ≤ a) (_hab : a ≤ b) (_hb : b ≤ ett.rounds),
        TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))))) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (r a : Fin ett.rounds) (_ : (↑a : ℕ) < (↑r : ℕ)) (x : V)
        (hxFinal : x ∈ TreeSequenceVertexSet T) (_ : ETTFirstAppearanceIndex ett x hxFinal ≤ (↑a :
        ℕ) + (1 : ℕ)) (lower : ExtendedTashkinovTree G k e0 input (ett.series.data.tree (⟨(↑r : ℕ)
        + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨(↑r : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : lower.rounds = (↑r : ℕ)),
    let P : TreeSequence G e0 := ett.series.data.tree r.castSucc.castSucc; x ∈
        TreeSequenceVertexSet P := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v this q hqTerminal hvFinal hfirstUpper
      hfirstPositive stageToStage vertexTransfer r a har x hxFinal hfirstR lower hround P
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      x ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hnonempty : candidates.Nonempty := by
    refine ⟨Fin.last ett.rounds, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage ett (Fin.last ett.rounds) = T by
      simp [ExtendedTashkinovLadderStage, Fin.lastCases_last]]
    exact hxFinal
  let first := candidates.min' hnonempty
  have hfirstBound : first.val + 1 ≤ a.val + 1 := by
    have hfirstRaw := hfirstR
    unfold ETTFirstAppearanceIndex at hfirstRaw
    dsimp at hfirstRaw
    dsimp [first, candidates]
    convert hfirstRaw using 1
  have hfirstMem : first ∈ candidates :=
    Finset.min'_mem candidates hnonempty
  change first ∈ candidates at hfirstMem
  let firstBase : Fin ett.rounds := ⟨first.val, by omega⟩
  have hfirstEq : first = firstBase.castSucc := by
    apply Fin.ext
    rfl
  have hxFirst : x ∈ TreeSequenceVertexSet
      (ett.series.data.tree ⟨first.val + 1, by omega⟩) := by
    have hxLadder := (Finset.mem_filter.mp hfirstMem).2
    rw [hfirstEq] at hxLadder
    unfold ExtendedTashkinovLadderStage at hxLadder
    rw [Fin.lastCases_castSucc] at hxLadder
    convert hxLadder using 1; congr 2
  have hseg := stageToStage (first.val + 1) r.val (by omega)
    (by omega) (by omega)
  have hxStage := vertexTransfer hseg hxFirst
  have hPIndex : (⟨r.val, by omega⟩ : Fin (ett.rounds + 2)) =
      r.castSucc.castSucc := by
    apply Fin.ext
    rfl
  rw [hPIndex] at hxStage
  exact hxStage

private theorem helper_hyP_393.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T) (_ :
        ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (_ : (0 : ℕ) <
        ETTFirstAppearanceIndex ett v hvFinal) (r a : Fin ett.rounds) (_ : (↑a : ℕ) < (↑r : ℕ)) (x
        : V) (_ : x ∈ TreeSequenceVertexSet T) (lower : ExtendedTashkinovTree G k e0 input
        (ett.series.data.tree (⟨(↑r : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨(↑r : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : lower.rounds = (↑r : ℕ)),
    let P : TreeSequence G e0 := ett.series.data.tree r.castSucc.castSucc;
    let Tnext : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc;
    ∀ (_ : TreeSequenceInitialSegment P Tnext) (_ : x ∈ TreeSequenceVertexSet P) (y : V) (_ :
        TreeVertexOrder (ett.series.data.tree r.succ.castSucc) y x), y ∈ TreeSequenceVertexSet P
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive r a har x hxFinal lower hround P Tnext hPNext hxP y hyx
  rcases hPNext with ⟨hlen, hvertices, hedges⟩
  rcases Finset.mem_image.mp hxP with ⟨ix, _, hix⟩
  rcases hyx with ⟨jy, jx, hjy, hjx, hjlt⟩
  have hjxEq : jx = Fin.castLE (Nat.succ_le_succ hlen) ix := by
    apply Tnext.vertex_injective
    exact hjx.trans ((hvertices ix).trans hix).symm
  have hjyBound : jy.val < P.length + 1 := by
    have hjxVal := congrArg Fin.val hjxEq
    simp only [Fin.val_castLE] at hjxVal
    omega
  let iy : Fin (P.length + 1) := ⟨jy.val, hjyBound⟩
  apply Finset.mem_image.mpr
  refine ⟨iy, Finset.mem_univ _, ?_⟩
  have hcast : Fin.castLE (Nat.succ_le_succ hlen) iy = jy := by
    apply Fin.ext
    rfl
  have hnextIndex : r.castSucc.succ = r.succ.castSucc := by
    apply Fin.ext
    rfl
  have hjy' : Tnext.vertex jy = y := by
    simpa [Tnext, hnextIndex] using hjy
  exact (hvertices iy).symm.trans (by simpa [hcast] using hjy')

private theorem helper_boundaryRestrict_424.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (r : Fin ett.rounds) (sigmaR : PartialEdgeColoring E k) (deltaR
        : Fin k),
    let P : TreeSequence G e0 := ett.series.data.tree r.castSucc.castSucc;
    let Tnext : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc;
    ∀ (_ : TreeSequenceInitialSegment P Tnext),
    ∀ z ∈ TreeSequenceVertexSet P,
    ∀ f ∈ BoundaryColorEdges G sigmaR (TreeSequenceVertexSet Tnext) deltaR, Incident G z f → f ∈
        BoundaryColorEdges G sigmaR (TreeSequenceVertexSet P) deltaR := by
  classical
  intro V E _ _ _ G k e0 input T generating ett vertexTransfer r sigmaR deltaR P Tnext hPNext z
      hzP f hf hzf
  have hfBoundary := (Finset.mem_filter.mp hf).1
  have hfColor := (Finset.mem_filter.mp hf).2
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
    true_and] at hfBoundary
  obtain ⟨zin, hzin, zout, hzout, hends⟩ := hfBoundary
  have hzNext := vertexTransfer hPNext hzP
  have hzCases : z = zin ∨ z = zout := by
    simpa [Incident, hends] using hzf
  have hzEq : z = zin := hzCases.resolve_right fun hzEq =>
    hzout (hzEq ▸ hzNext)
  apply Finset.mem_filter.mpr
  refine ⟨?_, hfColor⟩
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
    true_and]
  refine ⟨z, hzP, zout, ?_, ?_⟩
  · intro hzoutP
    exact hzout (vertexTransfer hPNext hzoutP)
  · simpa [hzEq] using hends

private theorem helper_hfxy_453.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (r : Fin ett.rounds) (sigmaR : PartialEdgeColoring E k) (deltaR
        : Fin k) (x : V),
    let P : TreeSequence G e0 := ett.series.data.tree r.castSucc.castSucc;
    let Tnext : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc;
    ∀ (_ : TreeSequenceInitialSegment P Tnext) (_ : x ∈ TreeSequenceVertexSet P),
    ∀ y ∈ TreeSequenceVertexSet P, y ≠ x →
    ∀ fx ∈ BoundaryColorEdges G sigmaR (TreeSequenceVertexSet (ett.series.data.tree
        r.succ.castSucc)) deltaR, Incident G x fx →
    ∀ fy ∈ BoundaryColorEdges G sigmaR (TreeSequenceVertexSet (ett.series.data.tree
        r.succ.castSucc)) deltaR, Incident G y fy → fy ∈ BoundaryColorEdges G sigmaR
        (TreeSequenceVertexSet P) deltaR → fx ≠ fy := by
  classical
  intro V E _ _ _ G k e0 input T generating ett vertexTransfer r sigmaR deltaR x P Tnext hPNext
      hxP y hyP hyne fx hfxBoundary hfxIncident fy hfyBoundary hfyIncident hfyP hfeq
  subst fy
  have hfBoundary := (Finset.mem_filter.mp hfxBoundary).1
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
    true_and] at hfBoundary
  obtain ⟨zin, hzin, zout, hzout, hends⟩ := hfBoundary
  have hxCases : x = zin ∨ x = zout := by
    simpa [Incident, hends] using hfxIncident
  have hyCases : y = zin ∨ y = zout := by
    simpa [Incident, hends] using hfyIncident
  have hxNext := vertexTransfer hPNext hxP
  have hyNext := vertexTransfer hPNext hyP
  have hxEq : x = zin := hxCases.resolve_right fun hxEq =>
    hzout (hxEq ▸ hxNext)
  have hyEq : y = zin := hyCases.resolve_right fun hyEq =>
    hzout (hyEq ▸ hyNext)
  exact hyne (hyEq.trans hxEq.symm)

private theorem helper_hstableLower_484.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T) (_ :
        ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (_ : (0 : ℕ) <
        ETTFirstAppearanceIndex ett v hvFinal) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (r _ : Fin ett.rounds) (sigmaR : PartialEdgeColoring E k) (_ :
        StableColoring (ett.series.data.tree r.succ.castSucc) (TashkinovStoredColors
        ett.series.data r.castSucc) (ett.series.data.coloring r.castSucc) sigmaR) (x : V) (_ : x ∈
        TreeSequenceVertexSet T) (lower : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (⟨(↑r : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨(↑r : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))),
    let nLower : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
    let P : TreeSequence G e0 := ett.series.data.tree r.castSucc.castSucc;
    let Tnext : TreeSequence G e0 := ett.series.data.tree r.succ.castSucc;
    ∀ (_ : TreeSequenceInitialSegment P Tnext) (_ : lower.series.data.tree nLower.castSucc = P) (_
        : lower.series.data.coloring nLower = ett.series.data.coloring r.castSucc) (_ :
        TashkinovStoredColors lower.series.data nLower = TashkinovStoredColors ett.series.data
        r.castSucc), StableColoring (lower.series.data.tree nLower.castSucc)
        (TashkinovStoredColors lower.series.data nLower) (lower.series.data.coloring nLower)
        sigmaR := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive vertexTransfer r a sigmaR hstableR x hxFinal lower nLower P Tnext hPNext
      htreeLower hcolorLower hstoredLower
  rw [htreeLower, hstoredLower, hcolorLower]
  constructor
  · intro f hfP hcontrolled
    apply hstableR.1 f
    · rcases hfP with ⟨z, hz, hzf⟩
      exact ⟨z, vertexTransfer hPNext hz, hzf⟩
    · rcases hcontrolled with ⟨c, hc, hfc⟩
      refine ⟨c, ?_, hfc⟩
      rcases Finset.mem_union.mp hc with hc | hc
      · apply Finset.mem_union.mpr
        left
        simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
        rcases hc with ⟨z, hz, hcz⟩
        exact ⟨z, vertexTransfer hPNext hz, hcz⟩
      · exact Finset.mem_union.mpr (Or.inr hc)
  · intro z hz
    exact hstableR.2 z (vertexTransfer hPNext hz)

private theorem helper_hfirstLower_539.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let _ : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (_ : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (_ : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal) (r a : Fin ett.rounds)
      (har : (↑a : ℕ) < (↑r : ℕ)) (x : V) (hxFinal : x ∈ TreeSequenceVertexSet T)
      (_ : ETTFirstAppearanceIndex ett x hxFinal ≤ (↑a : ℕ) + (1 : ℕ))
      (lower :
        ExtendedTashkinovTree G k e0 input
          (ett.series.data.tree
            (⟨(↑r : ℕ) + (1 : ℕ), by omega⟩ : Fin (ett.rounds + (2 : ℕ))))
          (ett.series.data.coloring (⟨(↑r : ℕ), by omega⟩ : Fin (ett.rounds + (1 : ℕ)))))
      (hround : lower.rounds = (↑r : ℕ))
      (_ :
        (∀ (i : Fin (lower.rounds + (2 : ℕ))),
          lower.series.data.tree i = ett.series.data.tree (Fin.castLE (by omega) i))),
    let aLower : Fin lower.rounds := (⟨(↑a : ℕ), by omega⟩ : Fin lower.rounds);
    ∀
      (hxLower :
        x ∈
          TreeSequenceVertexSet
            (ett.series.data.tree
              (⟨(↑r : ℕ) + (1 : ℕ), by omega⟩ : Fin (ett.rounds + (2 : ℕ))))),
    ETTFirstAppearanceIndex lower x hxLower ≤ (↑aLower : ℕ) + (1 : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v this q hqTerminal hvFinal hfirstUpper
      hfirstPositive r a har x hxFinal hfirstR lower hround htrees aLower hxLower
  unfold ETTFirstAppearanceIndex
  dsimp
  let fullCandidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      x ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hfullNonempty : fullCandidates.Nonempty := by
    refine ⟨Fin.last ett.rounds, ?_⟩
    simp only [fullCandidates, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [show ExtendedTashkinovLadderStage ett (Fin.last ett.rounds) = T by
      simp [ExtendedTashkinovLadderStage, Fin.lastCases_last]]
    exact hxFinal
  let mf := fullCandidates.min' hfullNonempty
  have hmfBound : mf.val + 1 ≤ a.val + 1 := by
    have hfirstRaw := hfirstR
    unfold ETTFirstAppearanceIndex at hfirstRaw
    dsimp at hfirstRaw
    dsimp [mf, fullCandidates]
    convert hfirstRaw using 1
  let lowerCandidates : Finset (Fin (lower.rounds + 1)) :=
    Finset.univ.filter fun i =>
      x ∈ TreeSequenceVertexSet
        (ExtendedTashkinovLadderStage lower i)
  have hlowerNonempty : lowerCandidates.Nonempty := by
    refine ⟨Fin.last lower.rounds, ?_⟩
    simp only [lowerCandidates, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [show ExtendedTashkinovLadderStage lower
        (Fin.last lower.rounds) =
          ett.series.data.tree ⟨r.val + 1, by omega⟩ by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last]
    exact hxLower
  let mfLower : Fin (lower.rounds + 1) := ⟨mf.val, by omega⟩
  let mfBase : Fin lower.rounds := ⟨mf.val, by omega⟩
  let mfFull : Fin ett.rounds := ⟨mf.val, by omega⟩
  have hmfLower : mfLower = mfBase.castSucc := by
    apply Fin.ext
    rfl
  have hmfFull : mf = mfFull.castSucc := by
    apply Fin.ext
    rfl
  have hstageEq : ExtendedTashkinovLadderStage lower mfLower =
      ExtendedTashkinovLadderStage ett mf := by
    rw [hmfLower, hmfFull]
    unfold ExtendedTashkinovLadderStage
    rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc,
      htrees mfBase.succ.castSucc]
    congr 1
  have hmfMemFull := Finset.min'_mem fullCandidates hfullNonempty
  have hmfMemLower : mfLower ∈ lowerCandidates := by
    simp only [lowerCandidates, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [hstageEq]
    exact (Finset.mem_filter.mp hmfMemFull).2
  have hle := Finset.min'_le lowerCandidates mfLower hmfMemLower
  have hleVal := Fin.le_iff_val_le_val.mp hle
  have htarget :
      (lowerCandidates.min' hlowerNonempty).val + 1 ≤ a.val + 1 := by
    dsimp [mfLower] at hleVal
    omega
  convert htarget using 1

private theorem helper_branch_664.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (t : Fin ett.rounds) (vt : V) (gammaT deltaT : Fin k),
        ett.series.data.chosenVertex t.succ = some vt → ett.series.data.gamma t.succ = some gammaT
        → ett.series.data.delta t.succ = some deltaT →
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
        (TashkinovStoredColors ett.series.data i.castSucc)) choice.selected rho ∧ ¬Disjoint
        (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho (ett.series.data.tree
        i.succ.castSucc))) →
    ∀ (actualGamma : Fin k), ParallelExtensionColor ett.series.data i.castSucc choice.selected
        choice.vertex actualGamma →
    ∀ (secondStable : PartialEdgeColoring E k), StableColoring (ett.series.data.tree
        i.succ.castSucc) (insert choice.color (TashkinovStoredColors ett.series.data i.castSucc))
        choice.selected secondStable → TreeExit (ett.series.data.tree i.succ.castSucc)
        secondStable actualGamma choice.color choice.vertex → ett.series.data.coloring i.succ =
        TwoColorComponentSwap G secondStable actualGamma choice.color (Sum.inl choice.vertex) →
        IsProperEdgeColoring G (ett.series.data.coloring i.succ) → IsOneEdgeUncolored
        (ett.series.data.coloring i.succ) e0 → ett.series.data.stored i.succ =
        { choice.color, actualGamma } → ett.series.data.connectingEdges i.succ = { choice.edge } →
        ett.series.data.kind i.succ = some TashkinovExtensionKind.PE →
        ett.series.data.chosenVertex i.succ = some choice.vertex → ett.series.data.outsideVertex
        i.succ = some choice.otherEndpoint → ett.series.data.delta i.succ = some choice.color →
        ett.series.data.gamma i.succ = some actualGamma → TashkinovClosure
        (ett.series.data.coloring i.succ) (ett.series.data.tree i.succ.castSucc)
        (ett.series.data.tree i.succ.succ) → TreeSequenceInitialSegment (ett.series.data.tree
        i.succ.castSucc) (ett.series.data.tree i.succ.succ) → (ett.series.data.tree
        i.succ.castSucc).length < (ett.series.data.tree i.succ.succ).length → t.succ = i.succ →
        IsOneEdgeUncolored (ett.series.data.coloring i.succ) e0 ∧ deltaT ∈ MissingColors G
        (ett.series.data.coloring i.succ) vt := by
  classical
  intro V E _ _ _ G k e0 input T generating ett t vt gammaT deltaT htVertex htGamma htDelta i
      previousProper previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting
      choice seriesAlternativeFails actualGamma gammaRule secondStable secondStableRelation
      exitWitness currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension htarget
  have hi : i = t := by
    apply Fin.ext
    simpa using (congrArg Fin.val htarget).symm
  subst i
  have hvChoice : choice.vertex = vt :=
    Option.some.inj
      (currentVertex.symm.trans (by simpa [htarget] using htVertex))
  have hdeltaChoice : choice.color = deltaT :=
    Option.some.inj
      (currentDelta.symm.trans (by simpa [htarget] using htDelta))
  have hgammaChoice : actualGamma = gammaT :=
    Option.some.inj
      (currentGamma.symm.trans (by simpa [htarget] using htGamma))
  subst vt
  subst deltaT
  subst gammaT
  have hgammaMissing : actualGamma ∈
      MissingColors G secondStable choice.vertex := by
    exact (secondStableRelation.2 choice.vertex
      choice.vertexDefective.1).symm ▸ gammaRule.1
  have hedge : secondStable choice.edge = some choice.color := by
    exact (secondStableRelation.1 choice.edge
      ⟨choice.vertex, choice.vertexDefective.1, choice.edgeIncident⟩
      ⟨choice.color, by simp, choice.edgeColor⟩).trans choice.edgeColor
  have hgammaDelta : actualGamma ≠ choice.color := by
    intro heq
    have hpresent : actualGamma ∈
        PresentColors G secondStable choice.vertex := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨choice.edge, choice.edgeIncident, by simpa [heq] using hedge⟩
    exact (Finset.mem_sdiff.mp hgammaMissing).2 hpresent
  have componentEdge :
    ∀ e : E, Incident G choice.vertex e → secondStable e = some actualGamma ∨ secondStable e =
        some choice.color → Sum.inr e ∈ TwoColorComponent G secondStable actualGamma choice.color
        (Sum.inl choice.vertex) := by
    intro e he hcolor
    change (TwoColorIncidenceGraph G secondStable actualGamma
      choice.color).connectedComponentMk (Sum.inr e) = _
    apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    simp [TwoColorIncidenceGraph, he, hcolor]
  have hgammaNo : ∀ e : E, Incident G choice.vertex e →
      secondStable e ≠ some actualGamma := by
    intro e he hec
    apply (Finset.mem_sdiff.mp hgammaMissing).2
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨e, he, hec⟩
  have hdeltaMissing : choice.color ∈ MissingColors G
      (TwoColorComponentSwap G secondStable actualGamma choice.color
        (Sum.inl choice.vertex)) choice.vertex := by
    apply Finset.mem_sdiff.mpr
    refine ⟨by simp, ?_⟩
    intro hpresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hpresent
    obtain ⟨e, he, hec⟩ := hpresent
    rw [TwoColorComponentSwap] at hec
    by_cases hcomp : Sum.inr e ∈ TwoColorComponent G secondStable
        actualGamma choice.color (Sum.inl choice.vertex)
    · simp [hcomp] at hec
      by_cases heg : secondStable e = some actualGamma
      · exact (hgammaNo e he heg).elim
      · by_cases hed : secondStable e = some choice.color
        · simp [hed, hgammaDelta] at hec
          exact hgammaDelta hec.symm
        · simp [heg, hed] at hec
    · simp only [Fin.castSucc_succ, hcomp, ↓reduceIte] at hec
      exact hcomp (componentEdge e he (Or.inr hec))
  refine ⟨by simpa [htarget] using currentOneUncolored, ?_⟩
  rw [show ett.series.data.coloring t.succ =
      TwoColorComponentSwap G secondStable actualGamma choice.color
        (Sum.inl choice.vertex) by simpa [htarget] using currentColoring]
  exact hdeltaMissing

private theorem helper_hPESlotData_805.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (t : Fin ett.rounds), ett.series.data.kind t.succ = some
        TashkinovExtensionKind.PE →
    ∃ (vt : V) (gammaT : Fin k) (deltaT : Fin k), ett.series.data.chosenVertex t.succ = some vt ∧
        ett.series.data.gamma t.succ = some gammaT ∧ ett.series.data.delta t.succ = some deltaT
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett t htKind
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
    have hi : i = t := by
      apply Fin.ext
      simpa using (congrArg Fin.val htarget).symm
    subst i
    refine ⟨choice.vertex, actualGamma, choice.color, ?_, ?_, ?_⟩
    · simpa [htarget] using currentVertex
    · simpa [htarget] using currentGamma
    · simpa [htarget] using currentDelta

private theorem helper_hPEStored_851.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (t : Fin ett.rounds) (gammaT deltaT : Fin k), ett.series.data.kind
        t.succ = some TashkinovExtensionKind.PE → ett.series.data.gamma t.succ = some gammaT →
        ett.series.data.delta t.succ = some deltaT → ett.series.data.stored t.succ =
        { gammaT, deltaT } := by
  classical
  intro V E _ _ _ G k e0 input T generating ett t gammaT deltaT htKind htGamma htDelta
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
    have hi : i = t := by
      apply Fin.ext
      simpa using (congrArg Fin.val htarget).symm
    subst i
    have hgammaEq : actualGamma = gammaT :=
      Option.some.inj
        (currentGamma.symm.trans (by simpa [htarget] using htGamma))
    have hdeltaEq : choice.color = deltaT :=
      Option.some.inj
        (currentDelta.symm.trans (by simpa [htarget] using htDelta))
    rw [show ett.series.data.stored t.succ = {choice.color, actualGamma} by
      simpa [htarget] using currentStored, hgammaEq, hdeltaEq]
    ext c
    simp [or_comm]

private theorem helper_hdeltaAvoids_958.{u_1, u_2} :
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
    ∀ (_ : ((
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
        (ett.series.data.tree jSlot.succ.castSucc))) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ))
        → Fin ett.rounds) (_ : (
    ∀ (a b : Fin (p + (1 : ℕ))) (_ : (↑a : ℕ) < (↑b : ℕ)), (↑(indices a) : ℕ) < (↑(indices b) :
        ℕ))) (_ : (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal u ↔
    ∃ (a : Fin (p + (1 : ℕ))), indices a = r)) (gammaClass deltaClass : Fin (p + (1 : ℕ)) → Fin k)
        (_ : (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.gamma (indices a).succ = some (gammaClass a))) (_ :
        (
    ∀ (a : Fin (p + (1 : ℕ))), ett.series.data.delta (indices a).succ = some (deltaClass a))) (_ :
        u ∈ TreeSequenceVertexSet T) (a b : Fin (p + (1 : ℕ))) (_ : (↑a : ℕ) ≤ (↑b : ℕ)),
        deltaClass b ≠ gammaClass a := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hdeltaExclusion u p indices hincreasing hclass gammaClass deltaClass
      hgammaClass hdeltaClass huFinal a b hab
  have haClass := (hclass (indices a)).2 ⟨a, rfl⟩
  have hbClass := (hclass (indices b)).2 ⟨b, rfl⟩
  have haData := haClass
  have hbData := hbClass
  simp only [ExtensionBaseSupportClass, Finset.mem_filter] at haData hbData
  have haActive : indices a ∈ ExtensionBaseActiveIndices ett v hvFinal := by
    exact haData.1
  have hbActive : indices b ∈ ExtensionBaseActiveIndices ett v hvFinal := by
    exact hbData.1
  have habSlots : (indices a).val ≤ (indices b).val := by
    by_cases heq : a = b
    · subst b
      exact le_rfl
    · exact Nat.le_of_lt (hincreasing a b (by omega))
  exact (hdeltaExclusion.1 (indices a) (indices b) u u huFinal huFinal
    (deltaClass b) (gammaClass a) haActive hbActive habSlots
    haData.2 hbData.2 (hdeltaClass b) (hgammaClass a)).2

private theorem helper_hterminalBefore_988.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (hvFinal : v ∈ TreeSequenceVertexSet T), ((
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
        ℕ) < (↑s : ℕ)) →
    ∀ (t : Fin ett.rounds) (vt : V), t ∈ ExtensionBaseRestorationIndices ett v hvFinal →
        ett.series.data.chosenVertex t.succ = some vt → TreeVertexOrder T v vt := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v hvFinal hsupportOrder t vt htRest htVertex
  have htData := htRest
  simp only [ExtensionBaseRestorationIndices, Finset.mem_sdiff] at htData
  have htActive := htData.1
  have htActiveData := htActive
  simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
    Finset.mem_univ, true_and] at htActiveData
  obtain ⟨htFirst, htKind, vt0, hvt0Final, hvt0Vertex, hvt0First⟩ :=
    htActiveData
  have hvt0Eq : vt0 = vt :=
    Option.some.inj (hvt0Vertex.symm.trans htVertex)
  subst vt0
  have horder := (hsupportOrder.2.1 t vt hvt0Final htActive htVertex).2
  exact horder.resolve_left fun hEq => by
    apply htData.2
    simp only [ExtensionBaseSupportClass, Finset.mem_filter]
    exact ⟨htActive, by simpa [hEq] using htVertex⟩

private theorem helper_hclassMissing_1053.{u_1, u_2} :
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
    ∀ (_ : (
    ∀ (u : V) (_ : (ExtensionBaseSupportClass ett v hvFinal u).Nonempty),
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
        ett.series.data.stored (indices a).succ; MissingColors G sigma u ∩ storedPairs =
        {deltaClass (Fin.last p)} ∧ MissingColors G (ett.series.data.coloring jSlot.castSucc) u =
        MissingColors G sigma u \ {deltaClass (Fin.last p)} ∪
        {gammaClass (0 : Fin (p + (1 : ℕ)))})) (u : V) (t : Fin ett.rounds) (deltaT : Fin k) (_ :
        ExtensionBaseSupportClass ett v hvFinal u ⊆ ExtensionBaseRestorationIndices ett v hvFinal)
        (_ : t ∈ ExtensionBaseSupportClass ett v hvFinal u) (_ : (
    ∀ s ∈ ExtensionBaseSupportClass ett v hvFinal u, (↑s : ℕ) ≤ (↑t : ℕ))) (_ :
        ett.series.data.delta t.succ = some deltaT), (MissingColors G sigma u ∩
        (ExtensionBaseSupportClass ett v hvFinal u).biUnion fun (s : Fin ett.rounds) ↦
        ett.series.data.stored s.succ) = { deltaT } := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot hclassPackage u t deltaT hsubset htClass htMaximum htDelta
  obtain ⟨p, indices, gammaClass, deltaClass, hincreasing, hclass,
      hgammaClass, hdeltaClass, hchain, hinjective, hunsupportedClass,
      hmissing⟩ :=
    hclassPackage u ⟨t, htClass⟩
  dsimp at hmissing
  obtain ⟨aT, haT⟩ := (hclass t).1 htClass
  have haTLast : aT = Fin.last p := by
    by_contra hne
    have haLt : aT < Fin.last p :=
      Fin.lt_last_iff_ne_last.mpr hne
    have hindexLt := hincreasing aT (Fin.last p) haLt
    have hlastClass := (hclass (indices (Fin.last p))).2
      ⟨Fin.last p, rfl⟩
    have hlastLe := htMaximum (indices (Fin.last p)) hlastClass
    rw [haT] at hindexLt
    exact (not_lt_of_ge hlastLe) hindexLt
  have hindexLast : indices (Fin.last p) = t := by
    rw [← haT, haTLast]
  have hdeltaEq : deltaClass (Fin.last p) = deltaT := by
    apply Option.some.inj
    exact (hdeltaClass (Fin.last p)).symm.trans (by
      simpa [hindexLast] using htDelta)
  have hstoredEq :
      Finset.univ.biUnion (fun a : Fin (p + 1) =>
        ett.series.data.stored (indices a).succ) =
      (ExtensionBaseSupportClass ett v hvFinal u).biUnion
        (fun s => ett.series.data.stored s.succ) := by
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, hc⟩
      exact ⟨indices a, (hclass (indices a)).2 ⟨a, rfl⟩, hc⟩
    · rintro ⟨s, hs, hc⟩
      obtain ⟨a, rfl⟩ := (hclass s).1 hs
      exact ⟨a, hc⟩
  rw [← hstoredEq, ← hdeltaEq]
  exact hmissing.1

private theorem helper_hterminalJ_1166.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let _ : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal),
    v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v this q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hjSlot
  unfold ETTFirstAppearanceIndex at hjSlot
  dsimp at hjSlot
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hlast : Fin.last ett.rounds ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfinal : ExtendedTashkinovLadderStage ett
        (Fin.last ett.rounds) = T := by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last
    rw [hfinal]
    exact hvFinal
  have hfirstEq : jSlot.val + 1 =
      (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val + 1 := by
    simpa [candidates] using hjSlot
  have hminVal :
      (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val =
        jSlot.val := by
    omega
  have hminEq : candidates.min' ⟨Fin.last ett.rounds, hlast⟩ =
      jSlot.castSucc := by
    apply Fin.ext
    simpa using hminVal
  have hjMember : jSlot.castSucc ∈ candidates := by
    rw [← hminEq]
    exact Finset.min'_mem candidates ⟨Fin.last ett.rounds, hlast⟩
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    at hjMember
  simpa [ExtendedTashkinovLadderStage, Fin.lastCases_castSucc] using
    hjMember

private theorem helper_branch_1321.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let _ : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (_ : ett.series.data.chosenVertex q.succ =
        some v) (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett
        v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v
        hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (_ : (
    ∀ (a b : ℕ) (_ : (1 : ℕ) ≤ a) (_hab : a ≤ b) (_hb : b ≤ ett.rounds),
        TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))))) (terminalPosition : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (_ : (ett.series.data.tree
        jSlot.succ.castSucc).vertex terminalPosition = v) (i : Fin ett.rounds) (previousProper :
        IsProperEdgeColoring G (ett.series.data.coloring i.castSucc)) (previousOneUncolored :
        IsOneEdgeUncolored (ett.series.data.coloring i.castSucc) e0) (previousClosed :
        ColoredVertexSetClosed G (ett.series.data.coloring i.castSucc) (TreeSequenceVertexSet
        (ett.series.data.tree i.succ.castSucc))) (previousNotStronglyClosed :
        ¬ColoredVertexSetStronglyClosed G (ett.series.data.coloring i.castSucc)
        (TreeSequenceVertexSet (ett.series.data.tree i.succ.castSucc))) (noRevisiting : ¬Nonempty
        (RevisitingExtensionCertificate ett.series.data i.castSucc)) (choice :
        MaximumDefectiveChoice G e0 (ett.series.data.tree i.succ.castSucc) (TashkinovStoredColors
        ett.series.data i.castSucc) (ett.series.data.coloring i.castSucc)) (seriesAlternativeFails
        :
    ∃ (rho : PartialEdgeColoring E k), IsProperEdgeColoring G rho ∧ IsOneEdgeUncolored rho e0 ∧
        StableColoring (ett.series.data.tree i.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data i.castSucc)) choice.selected rho ∧ ¬Disjoint
        (MissingColors G rho choice.otherEndpoint) (TreeMissingColors rho (ett.series.data.tree
        i.succ.castSucc))) (chosenGamma : Fin k) (gammaRule : ParallelExtensionColor
        ett.series.data i.castSucc choice.selected choice.vertex chosenGamma) (secondStable :
        PartialEdgeColoring E k) (secondStableProper : IsProperEdgeColoring G secondStable)
        (secondStableOneUncolored : IsOneEdgeUncolored secondStable e0) (secondStableRelation :
        StableColoring (ett.series.data.tree i.succ.castSucc) (insert choice.color
        (TashkinovStoredColors ett.series.data i.castSucc)) choice.selected secondStable)
        (exitWitness : TreeExit (ett.series.data.tree i.succ.castSucc) secondStable chosenGamma
        choice.color choice.vertex) (currentColoring : ett.series.data.coloring i.succ =
        TwoColorComponentSwap G secondStable chosenGamma choice.color (Sum.inl choice.vertex))
        (currentProper : IsProperEdgeColoring G (ett.series.data.coloring i.succ))
        (currentOneUncolored : IsOneEdgeUncolored (ett.series.data.coloring i.succ) e0)
        (currentStored : ett.series.data.stored i.succ = { choice.color, chosenGamma })
        (currentEdges : ett.series.data.connectingEdges i.succ = { choice.edge }) (currentKind :
        ett.series.data.kind i.succ = some TashkinovExtensionKind.PE) (currentVertex :
        ett.series.data.chosenVertex i.succ = some choice.vertex) (currentOutside :
        ett.series.data.outsideVertex i.succ = some choice.otherEndpoint) (currentDelta :
        ett.series.data.delta i.succ = some choice.color) (currentGamma : ett.series.data.gamma
        i.succ = some chosenGamma) (closedExtension : TashkinovClosure (ett.series.data.coloring
        i.succ) (ett.series.data.tree i.succ.castSucc) (ett.series.data.tree i.succ.succ))
        (orderedExtension : TreeSequenceInitialSegment (ett.series.data.tree i.succ.castSucc)
        (ett.series.data.tree i.succ.succ)) (strictExtension : (ett.series.data.tree
        i.succ.castSucc).length < (ett.series.data.tree i.succ.succ).length) (_ : q.succ = i.succ)
        (_ : ett.series.certified i.succ = TashkinovSeriesStep.PE i previousProper
        previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting choice
        seriesAlternativeFails chosenGamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness currentColoring currentProper
        currentOneUncolored currentStored currentEdges currentKind currentVertex currentOutside
        currentDelta currentGamma closedExtension orderedExtension strictExtension), (1 : ℕ) ≤
        (↑terminalPosition : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v this q hqTerminal hqVertex hvFinal
      hfirstUpper hfirstPositive jSlot hjSlot stageToStage terminalPosition hterminalAt i
      previousProper previousOneUncolored previousClosed previousNotStronglyClosed noRevisiting
      choice seriesAlternativeFails chosenGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness currentColoring currentProper
      currentOneUncolored currentStored currentEdges currentKind currentVertex currentOutside
      currentDelta currentGamma closedExtension orderedExtension strictExtension htarget hcert
  have hi : i = q := by
    apply Fin.ext
    simpa using (congrArg Fin.val htarget).symm
  subst i
  have hvChoice : choice.vertex = v :=
    Option.some.inj
      (currentVertex.symm.trans (by simpa [htarget] using hqVertex))
  obtain ⟨defectiveColor, hdefective, hedgeBoundary⟩ :=
    choice.edgeDefective
  have hdefectiveColor : defectiveColor = choice.color := by
    have hedgeColor := (Finset.mem_filter.mp hedgeBoundary).2
    exact Option.some.inj (hedgeColor.symm.trans choice.edgeColor)
  let boundary := BoundaryColorEdges G choice.selected
    (TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc)) defectiveColor
  have hboundaryCard : 1 < boundary.card := by
    dsimp [boundary]
    exact Nat.lt_of_lt_of_le Nat.one_lt_two hdefective
  rcases Finset.exists_mem_ne hboundaryCard choice.edge with
    ⟨f, hfBoundary, hfNe⟩
  have hfBoundaryEdge : f ∈ BoundaryEdges G
      (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) :=
    (Finset.mem_filter.mp hfBoundary).1
  have hfColor : choice.selected f = some choice.color := by
    have hc := (Finset.mem_filter.mp hfBoundary).2
    simpa [hdefectiveColor] using hc
  simp only [BoundaryEdges, Fin.castSucc_succ, Finset.mem_filter, Finset.mem_univ,
    true_and] at hfBoundaryEdge
  obtain ⟨x, hxStage, xout, hends⟩ := hfBoundaryEdge
  rcases hends with ⟨hxout, hends⟩
  have hxf : Incident G x f := by
    change x ∈ G.ends f
    rw [hends]
    simp
  have hxDefective : DefectiveVertex G choice.selected
      (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) x := by
    refine ⟨hxStage, f, ⟨defectiveColor, hdefective, hfBoundary⟩, hxf⟩
  have hxOrderOr := choice.maximal choice.selected x
    choice.selectedProper choice.selectedOneUncolored
    choice.selectedStable hxDefective
  have hxNe : x ≠ choice.vertex := by
    intro hxv
    have hadjacent : AdjacentEdges G choice.edge f :=
      ⟨choice.vertex, choice.edgeIncident, hxv ▸ hxf⟩
    exact choice.selectedProper hfNe.symm hadjacent choice.edgeColor
      hfColor
  have hxOrder : TreeVertexOrder
      (ett.series.data.tree q.succ.castSucc) x v := by
    simpa [hvChoice] using hxOrderOr.resolve_left hxNe
  have hTjQ : TreeSequenceInitialSegment
      (ett.series.data.tree jSlot.succ.castSucc)
      (ett.series.data.tree q.succ.castSucc) := by
    have hseg := stageToStage (jSlot.val + 1) (q.val + 1)
      (by omega) (by omega) (by omega)
    convert hseg using 1 <;> congr 1
  let terminalQ : Fin
      ((ett.series.data.tree q.succ.castSucc).length + 1) :=
    Fin.castLE (Nat.succ_le_succ hTjQ.1) terminalPosition
  have hterminalQ :
      (ett.series.data.tree q.succ.castSucc).vertex terminalQ = v := by
    exact (hTjQ.2.1 terminalPosition).trans hterminalAt
  rcases hxOrder with ⟨ix, iv, hix, hiv, hlt⟩
  have hivEq : iv = terminalQ := by
    apply (ett.series.data.tree q.succ.castSucc).vertex_injective
    exact hiv.trans hterminalQ.symm
  rw [hivEq] at hlt
  change ix.val < terminalPosition.val at hlt
  omega

private theorem helper_transportStep_1463.{u_1, u_2} :
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
    ∀ (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (trace :
        ExtensionBaseRestorationTrace ett v hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : StableColoringBeforeVertex T v hvFinal (TashkinovStoredColors ett.series.data
        jSlot.castSucc) (ett.series.data.coloring jSlot.castSucc) rho1) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive
        : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A seed) (_ : A.length < seed.length)
        {x : V} (_ : x ∈ TreeSequenceVertexSet A), x ∈ TreeVerticesBefore T v hvFinal))
        {A B : TreeSequence G e0} (_ : TashkinovAugmentation (ett.series.data.coloring
        jSlot.castSucc) A B) (_ : TreeSequenceInitialSegment B seed), TashkinovAugmentation rho1 A
        B := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot segmentTrans trace rho1 hb1Rho terminalPosition
      hterminalPositionPositive hterminalPositionBound seed segmentVertexBefore A B hstep hBseed
  rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
  have hAseed : TreeSequenceInitialSegment A seed :=
    segmentTrans hAB hBseed
  have hAlen : A.length < seed.length :=
    lt_of_lt_of_le (by omega) hBseed.1
  have hcMissingRho : c ∈ TreeMissingColors rho1 A := by
    unfold TreeMissingColors at hcMissing ⊢
    obtain ⟨x, hxA, hcx⟩ := Finset.mem_biUnion.mp hcMissing
    refine Finset.mem_biUnion.mpr ⟨x, hxA, ?_⟩
    rw [hb1Rho.2 x (segmentVertexBefore hAseed hAlen hxA)]
    exact hcx
  let added : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
  obtain ⟨attach, hattach⟩ := B.attaches added
  let oldPosition : Fin (B.length + 1) :=
    Fin.castLT attach
      (Nat.lt_trans attach.isLt (Nat.succ_lt_succ added.isLt))
  have holdValue : oldPosition.val < A.length + 1 := by
    dsimp [oldPosition, added]
    omega
  let oldA : Fin (A.length + 1) := ⟨oldPosition.val, holdValue⟩
  have holdEq : B.vertex oldPosition = A.vertex oldA := by
    have hcast : Fin.castLE (Nat.succ_le_succ hAB.1) oldA =
        oldPosition := by
      apply Fin.ext
      rfl
    rw [← hcast]
    exact hAB.2.1 oldA
  have holdA : A.vertex oldA ∈ TreeSequenceVertexSet A := by
    simp [TreeSequenceVertexSet]
  have holdBefore : B.vertex oldPosition ∈
      TreeVerticesBefore T v hvFinal := by
    rw [holdEq]
    exact segmentVertexBefore hAseed hAlen holdA
  have holdIncident : Incident G (B.vertex oldPosition) (B.edge added) := by
    unfold Incident
    rw [hattach]
    simp [oldPosition]
  have haddedFixed : rho1 (B.edge added) =
      ett.series.data.coloring jSlot.castSucc (B.edge added) := by
    apply hb1Rho.1 (B.edge added)
      ⟨B.vertex oldPosition, holdBefore, holdIncident⟩
    refine ⟨c, ?_, hcolor⟩
    apply Finset.mem_union_left
    unfold TreeMissingColors at hcMissing
    obtain ⟨x, hxA, hcx⟩ := Finset.mem_biUnion.mp hcMissing
    exact Finset.mem_biUnion.mpr
      ⟨x, segmentVertexBefore hAseed hAlen hxA, hcx⟩
  refine ⟨hlen, hAB, c, ?_, hcMissingRho⟩
  change rho1 (B.edge added) = some c
  exact haddedFixed.trans hcolor

private theorem helper_commonPrefix_1530.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A C → TreeSequenceInitialSegment B
        C → A.length ≤ B.length → TreeSequenceInitialSegment A B := by
  classical
  intro V E G e0 A B C hAC hBC hlen
  rcases hAC with ⟨hACLen, hACVertices, hACEdges⟩
  rcases hBC with ⟨hBCLen, hBCVertices, hBCEdges⟩
  refine ⟨hlen, ?_, ?_⟩
  · intro i
    calc
      B.vertex (Fin.castLE (Nat.succ_le_succ hlen) i) =
          C.vertex (Fin.castLE (Nat.succ_le_succ hBCLen)
            (Fin.castLE (Nat.succ_le_succ hlen) i)) :=
        (hBCVertices _).symm
      _ = C.vertex (Fin.castLE (Nat.succ_le_succ hACLen) i) := by
        congr 1
      _ = A.vertex i := hACVertices i
  · intro i
    calc
      B.edge (Fin.castLE hlen i) =
          C.edge (Fin.castLE hBCLen (Fin.castLE hlen i)) :=
        (hBCEdges _).symm
      _ = C.edge (Fin.castLE hACLen i) := by congr 1
      _ = A.edge i := hACEdges i

private theorem helper_hvNotPrevious_1574.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let _ : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal)
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : (0 : ℕ) < (↑jSlot : ℕ)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    v ∉ TreeSequenceVertexSet Tprevious := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v this q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hjSlot terminalPosition hjPositive Tprevious hvPrevious
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hlast : Fin.last ett.rounds ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage ett
        (Fin.last ett.rounds) = T by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last]
    exact hvFinal
  have hfirst := hjSlot
  unfold ETTFirstAppearanceIndex at hfirst
  dsimp at hfirst
  have hminimumValue :
      (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val =
        jSlot.val := by
    change jSlot.val + 1 =
      (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val + 1 at hfirst
    omega
  let previousSlot : Fin ett.rounds :=
    ⟨jSlot.val - 1, by omega⟩
  have hpreviousIndex : previousSlot.succ = jSlot.castSucc := by
    apply Fin.ext
    simp [previousSlot]
    omega
  have hpreviousMember : previousSlot.castSucc ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage ett previousSlot.castSucc =
        Tprevious by
      unfold ExtendedTashkinovLadderStage
      rw [Fin.lastCases_castSucc, hpreviousIndex]
      ]
    exact hvPrevious
  have hminimum := Finset.min'_le candidates previousSlot.castSucc
    hpreviousMember
  have hminimumVal := Fin.le_iff_val_le_val.mp hminimum
  rw [hminimumValue] at hminimumVal
  dsimp [previousSlot] at hminimumVal
  omega

private theorem helper_hpreviousStrict_1615.{u_1, u_2} :
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
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (_ :
        (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = v)
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : TreeSequenceInitialSegment Tprevious (ett.series.data.tree jSlot.succ.castSucc)) (_ : v
        ∉ TreeSequenceVertexSet Tprevious), Tprevious.length < seed.length := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalAt hterminalPositionPositive
      hterminalPositionBound seed Tprevious hpreviousTj hvNotPrevious
  by_contra hnot
  have hpositionLe : terminalPosition.val ≤ Tprevious.length := by
    simpa [seed, TreeSequencePrefix] using Nat.le_of_not_gt hnot
  let previousPosition : Fin (Tprevious.length + 1) :=
    ⟨terminalPosition.val, by omega⟩
  have hcast : Fin.castLE (Nat.succ_le_succ hpreviousTj.1)
      previousPosition = terminalPosition := by
    apply Fin.ext
    rfl
  apply hvNotPrevious
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  refine ⟨previousPosition, ?_⟩
  have hvertex := hpreviousTj.2.1 previousPosition
  rw [hcast] at hvertex
  exact hvertex.symm.trans hterminalAt

private theorem helper_branch_1655.{u_1, u_2} :
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
    ∀ (_ : Tprevious.length < seed.length) (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G
        e0 (ett.series.data.tree i.succ.castSucc) (TashkinovStoredColors ett.series.data
        i.castSucc) (ett.series.data.coloring i.castSucc)) (_ : ett.series.data.connectingEdges
        i.succ = { choice.edge }) (_ : ett.series.data.kind i.succ = some
        TashkinovExtensionKind.SE) (adjoined : TreeSequence G e0) (_ : TreeSequenceAdjoinEdge
        (ett.series.data.tree i.succ.castSucc) choice.edge adjoined) (_ : TashkinovClosure
        (ett.series.data.coloring i.succ) adjoined (ett.series.data.tree i.succ.succ)) (_ :
        jSlot.castSucc = i.succ), ett.series.data.kind i.succ = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence (ett.series.data.coloring i.succ) Tprevious seed ∨
        (ett.series.data.kind i.succ = some TashkinovExtensionKind.SE ∨ ett.series.data.kind
        i.succ = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges i.succ = { f } ∧
        TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧ TashkinovAugmentationSequence
        (ett.series.data.coloring i.succ) adjoinSeed seed := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hjTreeIndex hseedTj commonPrefix Tprevious hpreviousStrict i choice currentEdges
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
    have hpreviousEq :
        ett.series.data.tree i.succ.castSucc = Tprevious := by
      rw [hi]
    rw [hpreviousEq] at hlen
    rw [hlen]
    omega
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
    have hsegmentNew : TreeSequenceInitialSegment Tprevious
        adjoined := by
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

private theorem helper_branch_1709.{u_1, u_2} :
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
    ∀ (_ : TreeSequenceInitialSegment Tprevious seed) (i : Fin ett.rounds) (_ :
        ett.series.data.kind i.succ = some TashkinovExtensionKind.PE) (_ : TashkinovClosure
        (ett.series.data.coloring i.succ) (ett.series.data.tree i.succ.castSucc)
        (ett.series.data.tree i.succ.succ)) (_ : jSlot.castSucc = i.succ), ett.series.data.kind
        i.succ = some TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence
        (ett.series.data.coloring i.succ) Tprevious seed ∨ (ett.series.data.kind i.succ = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind i.succ = some TashkinovExtensionKind.RE)
        ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges i.succ = { f } ∧
        TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧ TashkinovAugmentationSequence
        (ett.series.data.coloring i.succ) adjoinSeed seed := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hjTreeIndex hseedTj Tprevious hpreviousSeed i currentKind closedExtension htarget
  have hi : i.succ = jSlot.castSucc := htarget.symm
  have hroute : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) Tprevious
      (ett.series.data.tree jSlot.succ.castSucc) := by
    have h := closedExtension.1
    rw [hi, hjTreeIndex] at h
    exact h
  left
  refine ⟨by simpa [htarget] using currentKind, ?_⟩
  simpa [hi] using
    (TashkinovAugmentationSequenceRestrict
      (ett.series.data.coloring jSlot.castSucc) Tprevious seed
      (ett.series.data.tree jSlot.succ.castSucc) hroute
      hpreviousSeed hseedTj)

private theorem helper_branch_1730.{u_1, u_2} :
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
    ∀ (_ : Tprevious.length < seed.length) (i : Fin ett.rounds) (available :
        RevisitingExtensionCertificate ett.series.data i.castSucc) (_ :
        ett.series.data.connectingEdges i.succ = { available.edge }) (_ : ett.series.data.kind
        i.succ = some TashkinovExtensionKind.RE) (adjoined : TreeSequence G e0) (_ :
        TreeSequenceAdjoinEdge (ett.series.data.tree i.succ.castSucc) available.edge adjoined) (_
        : TashkinovClosure (ett.series.data.coloring i.succ) adjoined (ett.series.data.tree
        i.succ.succ)) (_ : jSlot.castSucc = i.succ), ett.series.data.kind i.succ = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence (ett.series.data.coloring
        i.succ) Tprevious seed ∨ (ett.series.data.kind i.succ = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind i.succ = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges i.succ = { f } ∧
        TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧ TashkinovAugmentationSequence
        (ett.series.data.coloring i.succ) adjoinSeed seed := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hjTreeIndex hseedTj commonPrefix Tprevious hpreviousStrict i available currentEdges
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
    have hpreviousEq :
        ett.series.data.tree i.succ.castSucc = Tprevious := by
      rw [hi]
    rw [hpreviousEq] at hlen
    rw [hlen]
    omega
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
    have hsegmentNew : TreeSequenceInitialSegment Tprevious
        adjoined := by
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

private theorem helper_hstablePrevious_1829.{u_1, u_2} :
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
    ∀ (_ : StableColoringBeforeVertex T v hvFinal (TashkinovStoredColors ett.series.data
        jSlot.castSucc) (ett.series.data.coloring jSlot.castSucc) rho1) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive
        : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A seed) (_ : A.length < seed.length)
        {x : V} (_ : x ∈ TreeSequenceVertexSet A), x ∈ TreeVerticesBefore T v hvFinal)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : Tprevious.length < seed.length) (_ : TreeSequenceInitialSegment Tprevious seed),
        StableColoring Tprevious (TashkinovStoredColors ett.series.data jSlot.castSucc)
        (ett.series.data.coloring jSlot.castSucc) rho1 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace rho1 hb1Rho terminalPosition
      hterminalPositionPositive hterminalPositionBound seed segmentVertexBefore Tprevious
      hpreviousStrict hpreviousSeed
  constructor
  · intro f hfIncident hfControlled
    obtain ⟨x, hxPrevious, hxf⟩ := hfIncident
    apply hb1Rho.1 f
      ⟨x, segmentVertexBefore hpreviousSeed hpreviousStrict hxPrevious,
        hxf⟩
    obtain ⟨c, hcControlled, hfc⟩ := hfControlled
    refine ⟨c, ?_, hfc⟩
    rcases Finset.mem_union.mp hcControlled with hcMissing | hcStored
    · apply Finset.mem_union_left
      unfold TreeMissingColors at hcMissing
      obtain ⟨z, hzPrevious, hcz⟩ :=
        Finset.mem_biUnion.mp hcMissing
      exact Finset.mem_biUnion.mpr
        ⟨z, segmentVertexBefore hpreviousSeed hpreviousStrict
          hzPrevious, hcz⟩
    · exact Finset.mem_union_right _ hcStored
  · intro x hxPrevious
    exact hb1Rho.2 x
      (segmentVertexBefore hpreviousSeed hpreviousStrict hxPrevious)

private theorem helper_branch_1907.{u_1, u_2} :
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
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (trace :
        ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : IsProperEdgeColoring G rho1) (_ : IsOneEdgeUncolored rho1 e0) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive
        : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (_ : (
    ∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed), TashkinovAugmentationSequence rho1 S seed)) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)),
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (_ : ¬(0 : ℕ) < (↑jSlot : ℕ)),
    ∃ (TjPrime : TreeSequence G e0), TashkinovClosure rho1 seed TjPrime ∧
        ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime) ∧
    let awayMissing : Finset (Fin k) := ((TreeSequenceVertexSet TjPrime).erase v).biUnion fun (x :
        V) ↦ MissingColors G rho1 x; (awayMissing ∩ supportColors).Nonempty ∨ awayMissing ∩
        supportColors = ∅ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot hjSlot trace p0 indices0 rho1 hrho1Proper hrho1One
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj
      transportSeedRoute commonPrefix supportColors hjPositive
  have hjZero : jSlot.val = 0 := by omega
  have hjIndex : jSlot.castSucc = (0 : Fin (ett.rounds + 1)) := by
    apply Fin.ext
    exact hjZero
  cases hcert : ett.series.certified (0 : Fin (ett.rounds + 1)) with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have htreeOne : ett.series.data.tree 1 =
        ett.series.data.tree jSlot.succ.castSucc := by
      congr 1
      apply Fin.ext
      simp [hjZero]
    have hinitialTj : TreeSequenceInitialSegment
        (ett.series.data.tree 0)
        (ett.series.data.tree jSlot.succ.castSucc) := by
      have h := TashkinovAugmentationSequenceInitialSegment _ _ _
        initialClosure.1
      rw [htreeOne] at h
      exact h
    have hinitialSeed : TreeSequenceInitialSegment
        (ett.series.data.tree 0) seed := by
      apply commonPrefix hinitialTj hseedTj
      rw [seedLength]
      simpa [seed, TreeSequencePrefix] using hterminalPositionPositive
    have hrouteOld : TashkinovAugmentationSequence
        (ett.series.data.coloring jSlot.castSucc)
        (ett.series.data.tree 0) seed := by
      have hrestricted := TashkinovAugmentationSequenceRestrict
        (ett.series.data.coloring 0) (ett.series.data.tree 0) seed
        (ett.series.data.tree jSlot.succ.castSucc)
        (by simpa [htreeOne] using initialClosure.1)
        hinitialSeed hseedTj
      simpa [hjIndex] using hrestricted
    have hrouteRho : TashkinovAugmentationSequence rho1
        (ett.series.data.tree 0) seed :=
      transportSeedRoute (ett.series.data.tree 0) hrouteOld
    obtain ⟨TjPrime, hclosure⟩ := TashkinovClosureExists rho1 seed
    have htripleRho : KTriple G k e0 rho1 :=
      ⟨triple.1, triple.2.1, triple.2.2.1, hrho1Proper, hrho1One⟩
    have hinitialTree : TashkinovTree G e0 rho1
        (ett.series.data.tree 0) := by
      intro a ha
      rw [seedLength] at a
      omega
    have hprimeTree : TashkinovTree G e0 rho1 TjPrime :=
      TashkinovAugmentationSequencePreservesTashkinovTree G e0 rho1
        (ett.series.data.tree 0) TjPrime hinitialTree
        (Relation.ReflTransGen.trans hrouteRho hclosure.1)
    have hprimeElementary : ColoredVertexSetElementary G rho1
        (TreeSequenceVertexSet TjPrime) := by
      unfold ColoredVertexSetElementary
      intro x hx y hy hxy
      exact (TashTree G k e0 rho1 TjPrime htripleRho hprimeTree)
        hx hy hxy
    refine ⟨TjPrime, hclosure, hprimeElementary, ?_⟩
    let awayMissing :=
      ((TreeSequenceVertexSet TjPrime).erase v).biUnion
        fun x => MissingColors G rho1 x
    by_cases hnonempty : (awayMissing ∩ supportColors).Nonempty
    · exact Or.inl hnonempty
    · exact Or.inr (Finset.not_nonempty_iff_eq_empty.mp hnonempty)

private theorem helper_hTjElementary_2030.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
       [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett)
      (hpositive : (0 : ℕ) < ett.rounds)
      (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (v : V),
    let _ : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (p0 : ℕ)
      (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : indices0 (Fin.last p0) = q),
    ColoredVertexSetElementary G (ett.series.data.coloring jSlot.castSucc)
      (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower v this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot hjSlot p0 indices0 terminalPosition hqLast
  by_cases hjPositive : 0 < jSlot.val
  · obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
      CertifiedETTRestriction G k e0 input T generating ett hMP
        jSlot.val hjPositive jSlot.isLt
    exact (hlower lower (by omega) (by omega) hlowerMP).1
  · have hjZero : jSlot.val = 0 := by omega
    have hbase : ColoredVertexSetElementary G
        (ett.series.data.coloring 0)
        (TreeSequenceVertexSet
          (ett.series.data.tree ⟨1, by omega⟩)) := by
      unfold ColoredVertexSetElementary
      intro x hx y hy hxy
      exact (TechnicalTheoremBase G k ett.rounds e0 input
        ett.series).1 hx hy hxy
    have hcolor : jSlot.castSucc = (0 : Fin (ett.rounds + 1)) := by
      apply Fin.ext
      exact hjZero
    have htree : jSlot.succ.castSucc =
        (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simp [hjZero]
    simpa [hcolor, htree] using hbase

private theorem helper_hprefixAvoids_2180.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (v : V) (sigma : PartialEdgeColoring E k) (hvFinal : v ∈
        TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 :
        ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (delta0 : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0) (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (b : Fin
        (p0 + (1 : ℕ))) (_ : ((TreeVerticesBefore TjPrime u huPrime).biUnion fun (v : V) ↦
        MissingColors G rho1 v) ∩ ((Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ) \ {delta0 (Fin.last p0)}) = ∅ ∧ (delta0
        (Fin.last p0) ∉ (ExtensionBaseCaseOneIndices ett p0 indices0 b).biUnion fun (t : Fin
        ett.rounds) ↦ ett.series.data.stored t.succ) ∧ (MissingColors G rho1 v ∩
        (ExtensionBaseCaseOneIndices ett p0 indices0 b).biUnion fun (t : Fin ett.rounds) ↦
        ett.series.data.stored t.succ) = ∅) (_ : ((ExtensionBaseCaseOneIndices ett p0 indices0
        b).biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ) ⊆ supportColors),
        (((TreeVerticesBefore TjPrime u huPrime).biUnion fun (x : V) ↦ MissingColors G rho1 x) ∩
        (ExtensionBaseCaseOneIndices ett p0 indices0 b).biUnion fun (t : Fin ett.rounds) ↦
        ett.series.data.stored t.succ) = ∅ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v sigma hvFinal trace p0 indices0 delta0 rho1
      supportColors TjPrime u huPrime b hprefixData hprefixSubset
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c hc
  obtain ⟨hcBefore, hcPrefix⟩ := Finset.mem_inter.mp hc
  have hcSupport := hprefixSubset hcPrefix
  have hcNe : c ≠ delta0 (Fin.last p0) := by
    intro hEq
    apply hprefixData.2.1
    rw [← hEq]
    exact hcPrefix
  have hcDifference : c ∈ supportColors \ {delta0 (Fin.last p0)} :=
    Finset.mem_sdiff.mpr ⟨hcSupport, by simpa using hcNe⟩
  have hcEmpty : c ∈ (∅ : Finset (Fin k)) := by
    rw [← hprefixData.1]
    exact Finset.mem_inter.mpr ⟨hcBefore, hcDifference⟩
  simp at hcEmpty

private theorem helper_hUsegmentVertexBefore_2265.{u_1, u_2} :
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
        jSlot.succ.castSucc).length) (TjPrime : TreeSequence G e0) (u : V) (huPrime : u ∈
        TreeSequenceVertexSet TjPrime) (uPosition : Fin (TjPrime.length + (1 : ℕ)))
        (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤
        TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    ∀ (_ : TreeSequenceInitialSegment U TjPrime) (_ : (
    ∀ (i : Fin (TjPrime.length + (1 : ℕ))) (_ : (↑i : ℕ) < (↑uPosition : ℕ)), TjPrime.vertex i ∈
        TreeVerticesBefore TjPrime u huPrime)) {A : TreeSequence G e0} (_ :
        TreeSequenceInitialSegment A U) (_ : A.length < U.length) {x : V} (_ : x ∈
        TreeSequenceVertexSet A), x ∈ TreeVerticesBefore TjPrime u huPrime := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound TjPrime u huPrime uPosition huPositionPositive huPositionBound U
      hUPrime hprimeVertexBefore A hAU hAlen x hxA
  obtain ⟨hAULen, hAUVertices, -⟩ := hAU
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hxA
  obtain ⟨i, rfl⟩ := hxA
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

private theorem helper_transportUStep_2285.{u_1, u_2} :
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
    ∀ (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (trace :
        ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (_ :
        (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (_ : (↑terminalPosition : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length) (TjPrime : TreeSequence G e0) (u : V) (huPrime : u ∈
        TreeSequenceVertexSet TjPrime) (b : Fin (p0 + (1 : ℕ))) (traceB :
        ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
    ∀ (_ : ((
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∪ TreeVerticesBefore
        TjPrime u huPrime, MissingColors G (traceB.coloring (Fin.last traceB.steps)) x =
        MissingColors G rho1 x) ∧
    ∀ (f : E), ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), (ett.series.data.tree
        jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex z = u ∧ (↑a :
        ℕ) < (↑z : ℕ) ∧ TjPrime.edge a = f) → traceB.coloring (Fin.last traceB.steps) f = rho1 f))
        (uPosition : Fin (TjPrime.length + (1 : ℕ))) (_ : TjPrime.vertex uPosition = u)
        (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤
        TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    ∀ (_ : TreeSequenceInitialSegment U TjPrime) (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A U) (_ : A.length < U.length)
        {x : V} (_ : x ∈ TreeSequenceVertexSet A), x ∈ TreeVerticesBefore TjPrime u huPrime))
        {A B : TreeSequence G e0} (_ : TashkinovAugmentation rho1 A B) (_ :
        TreeSequenceInitialSegment B U), TashkinovAugmentation rho2 A B := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot segmentTrans trace p0 indices0 rho1 terminalPosition
      hterminalPositionPositive hterminalPositionBound TjPrime u huPrime b traceB rho2 c2
      uPosition huPosition huPositionPositive huPositionBound U hUPrime hUsegmentVertexBefore A B
      hstep hBU
  rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
  have hAU : TreeSequenceInitialSegment A U := segmentTrans hAB hBU
  have hAlen : A.length < U.length :=
    lt_of_lt_of_le (by omega) hBU.1
  have hcMissingRho : c ∈ TreeMissingColors rho2 A := by
    unfold TreeMissingColors at hcMissing ⊢
    obtain ⟨x, hxA, hcx⟩ := Finset.mem_biUnion.mp hcMissing
    refine Finset.mem_biUnion.mpr ⟨x, hxA, ?_⟩
    rw [c2.1 x (Finset.mem_union_right _
      (hUsegmentVertexBefore hAU hAlen hxA))]
    exact hcx
  let added : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
  let addedU : Fin U.length := Fin.castLE hBU.1 added
  let addedPrime : Fin TjPrime.length := Fin.castLE hUPrime.1 addedU
  have haddedPosition : addedPrime.val < uPosition.val := by
    change A.length < uPosition.val
    have hUlen : U.length = uPosition.val := by
      simp [U, TreeSequencePrefix]
    omega
  have haddedIdentity : TjPrime.edge addedPrime = B.edge added :=
    (hUPrime.2.2 addedU).trans (hBU.2.2 added)
  have haddedFixed : rho2 (B.edge added) = rho1 (B.edge added) := by
    apply c2.2 (B.edge added)
    exact Or.inr ⟨addedPrime, uPosition, huPosition,
      haddedPosition, haddedIdentity⟩
  refine ⟨hlen, hAB, c, ?_, hcMissingRho⟩
  change rho2 (B.edge added) = some c
  exact haddedFixed.trans hcolor

private theorem helper_hvNotPrevious_2347.{u_1, u_2} :
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
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (p0 : ℕ) (indices0 :
        Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (_ : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (_ :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length) (TjPrime :
        TreeSequence G e0) (_ : indices0 (Fin.last p0) = q) (_ : Fin (TjPrime.length + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), v ∉ TreeSequenceVertexSet Tprevious := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v this q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hjSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound TjPrime hqLast uPosition Tprevious hjPositive hvPrevious
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hlast : Fin.last ett.rounds ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage ett
        (Fin.last ett.rounds) = T by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last]
    exact hvFinal
  have hfirst := hjSlot
  unfold ETTFirstAppearanceIndex at hfirst
  dsimp at hfirst
  have hminimumValue :
      (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val =
        jSlot.val := by
    change jSlot.val + 1 =
      (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val + 1 at hfirst
    omega
  let previousSlot : Fin ett.rounds :=
    ⟨jSlot.val - 1, by omega⟩
  have hpreviousIndex : previousSlot.succ = jSlot.castSucc := by
    apply Fin.ext
    simp [previousSlot]
    omega
  have hpreviousMember : previousSlot.castSucc ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage ett previousSlot.castSucc =
        Tprevious by
      unfold ExtendedTashkinovLadderStage
      rw [Fin.lastCases_castSucc, hpreviousIndex]]
    exact hvPrevious
  have hminimum := Finset.min'_le candidates previousSlot.castSucc
    hpreviousMember
  have hminimumVal := Fin.le_iff_val_le_val.mp hminimum
  rw [hminimumValue] at hminimumVal
  dsimp [previousSlot] at hminimumVal
  omega

private theorem helper_hpreviousStrict_2394.{u_1, u_2} :
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
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (_ : (ett.series.data.tree
        jSlot.succ.castSucc).vertex terminalPosition = v) (hterminalPositionPositive : (1 : ℕ) ≤
        (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0) (_ : Fin (TjPrime.length + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), v ∉ TreeSequenceVertexSet Tprevious)) (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), TreeSequenceInitialSegment Tprevious (ett.series.data.tree
        jSlot.succ.castSucc))) (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalAt hterminalPositionPositive
      hterminalPositionBound seed TjPrime uPosition Tprevious hvNotPrevious hpreviousTj hjPositive
  by_contra hnot
  have hpositionLe : terminalPosition.val ≤ Tprevious.length := by
    simpa [seed, TreeSequencePrefix] using Nat.le_of_not_gt hnot
  let previousPosition : Fin (Tprevious.length + 1) :=
    ⟨terminalPosition.val, by omega⟩
  have hcast : Fin.castLE
      (Nat.succ_le_succ (hpreviousTj hjPositive).1)
      previousPosition = terminalPosition := by
    apply Fin.ext
    rfl
  apply hvNotPrevious hjPositive
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  refine ⟨previousPosition, ?_⟩
  have hvertex := (hpreviousTj hjPositive).2.1 previousPosition
  rw [hcast] at hvertex
  exact hvertex.symm.trans hterminalAt

private theorem helper_branch_2422.{u_1, u_2} :
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
        seed (ett.series.data.tree jSlot.succ.castSucc) := by
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

private theorem helper_branch_2455.{u_1, u_2} :
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
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive
        : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : jSlot.castSucc.succ = jSlot.succ.castSucc) (_ : TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc)) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)) (TjPrime : TreeSequence G e0) (_ : Fin (TjPrime.length + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length)) (i : Fin ett.rounds) (choice
        : MaximumDefectiveChoice G e0 (ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors ett.series.data i.castSucc) (ett.series.data.coloring i.castSucc))
        (adjoined : TreeSequence G e0) (_ : TreeSequenceAdjoinEdge (ett.series.data.tree
        i.succ.castSucc) choice.edge adjoined) (_ : TashkinovClosure (ett.series.data.coloring
        i.succ) adjoined (ett.series.data.tree i.succ.succ)) (_ : jSlot.castSucc = i.succ),
        TashkinovAugmentationSequence (ett.series.data.coloring i.succ) seed (ett.series.data.tree
        jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v this q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hjTreeIndex hseedTj commonPrefix TjPrime uPosition Tprevious
      hpreviousStrict i choice adjoined adjoinedExactly closedExtension htarget
  have hi : i.succ = jSlot.castSucc := htarget.symm
  have hjPositive : 0 < jSlot.val := by
    have := congrArg Fin.val hi
    simp at this
    omega
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
    have hiCast : i.succ.castSucc = jSlot.castSucc.castSucc := by
      apply Fin.ext
      simpa using congrArg Fin.val hi
    have hprev : ett.series.data.tree i.succ.castSucc =
        Tprevious := by rw [hiCast]
    rw [hprev] at hlen
    rw [hlen]
    exact Nat.succ_le_of_lt (hpreviousStrict hjPositive)
  have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
    commonPrefix hadjoinedTj hseedTj hadjoinedLength
  simpa [hi] using
    (TashkinovAugmentationSequenceSuffix
      (ett.series.data.coloring jSlot.castSucc) adjoined seed _ hroute
        hadjoinedSeed hseedTj)

private theorem helper_branch_2490.{u_1, u_2} :
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
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive
        : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : jSlot.castSucc.succ = jSlot.succ.castSucc) (_ : TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc)) (TjPrime : TreeSequence G e0) (_ : Fin
        (TjPrime.length + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), TreeSequenceInitialSegment Tprevious seed)) (i : Fin
        ett.rounds) (_ : TashkinovClosure (ett.series.data.coloring i.succ) (ett.series.data.tree
        i.succ.castSucc) (ett.series.data.tree i.succ.succ)) (_ : jSlot.castSucc = i.succ),
        TashkinovAugmentationSequence (ett.series.data.coloring i.succ) seed (ett.series.data.tree
        jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v this q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hjTreeIndex hseedTj TjPrime uPosition Tprevious hpreviousSeed i
      closedExtension htarget
  have hi : i.succ = jSlot.castSucc := htarget.symm
  have hjPositive : 0 < jSlot.val := by
    have := congrArg Fin.val hi
    simp at this
    omega
  have hroute : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) Tprevious
      (ett.series.data.tree jSlot.succ.castSucc) := by
    have h := closedExtension.1
    rw [hi, hjTreeIndex] at h
    simpa [Tprevious, hi] using h
  simpa [hi] using
    (TashkinovAugmentationSequenceSuffix
      (ett.series.data.coloring jSlot.castSucc) Tprevious seed _ hroute
        (hpreviousSeed hjPositive) hseedTj)

private theorem helper_branch_2512.{u_1, u_2} :
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
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (terminalPosition : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive
        : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : jSlot.castSucc.succ = jSlot.succ.castSucc) (_ : TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc)) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)) (TjPrime : TreeSequence G e0) (_ : Fin (TjPrime.length + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length)) (i : Fin ett.rounds)
        (available : RevisitingExtensionCertificate ett.series.data i.castSucc) (adjoined :
        TreeSequence G e0) (_ : TreeSequenceAdjoinEdge (ett.series.data.tree i.succ.castSucc)
        available.edge adjoined) (_ : TashkinovClosure (ett.series.data.coloring i.succ) adjoined
        (ett.series.data.tree i.succ.succ)) (_ : jSlot.castSucc = i.succ),
        TashkinovAugmentationSequence (ett.series.data.coloring i.succ) seed (ett.series.data.tree
        jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v this q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hjTreeIndex hseedTj commonPrefix TjPrime uPosition Tprevious
      hpreviousStrict i available adjoined adjoinedExactly closedExtension htarget
  have hi : i.succ = jSlot.castSucc := htarget.symm
  have hjPositive : 0 < jSlot.val := by
    have := congrArg Fin.val hi
    simp at this
    omega
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
    have hiCast : i.succ.castSucc = jSlot.castSucc.castSucc := by
      apply Fin.ext
      simpa using congrArg Fin.val hi
    have hprev : ett.series.data.tree i.succ.castSucc =
        Tprevious := by rw [hiCast]
    rw [hprev] at hlen
    rw [hlen]
    exact Nat.succ_le_of_lt (hpreviousStrict hjPositive)
  have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
    commonPrefix hadjoinedTj hseedTj hadjoinedLength
  simpa [hi] using
    (TashkinovAugmentationSequenceSuffix
      (ett.series.data.coloring jSlot.castSucc) adjoined seed _ hroute
        hadjoinedSeed hseedTj)

private theorem helper_equalPrefixes_2607.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {A B D : TreeSequence G e0}, TreeSequenceInitialSegment A D → TreeSequenceInitialSegment B
        D → A.length = B.length → A = B := by
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

private theorem helper_hiSeed_2699.{u_1, u_2} :
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
    ∀ (TjPrime : TreeSequence G e0) (uPosition : Fin (TjPrime.length + (1 : ℕ)))
        (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤
        TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed U),
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (_ : TreeSequence G e0) (_ : TreeSequenceInitialSegment seed Tj0) (_ : ℕ) (i : Fin
        Tj0.length) (_ : Tj0.vertex i.succ ∉ TreeSequenceVertexSet U), seed.length ≤ (↑i : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed TjPrime uPosition huPositionPositive huPositionBound U hseedU
      Tj0 M hseedTjSegment n i hrightOutside
  by_contra hnot
  have hi : i.val < seed.length := Nat.lt_of_not_ge hnot
  let a : Fin (seed.length + 1) := ⟨i.val + 1, by omega⟩
  have hTjSeedA : Tj0.vertex
        (Fin.castLE (Nat.succ_le_succ hseedTjSegment.1) a) =
      seed.vertex a := hseedTjSegment.2.1 a
  apply hrightOutside
  simp only [TreeSequenceVertexSet, Finset.mem_image,
    Finset.mem_univ, true_and]
  refine ⟨Fin.castLE (Nat.succ_le_succ hseedU.1) a, ?_⟩
  have hia : Fin.castLE
        (Nat.succ_le_succ hseedTjSegment.1) a = i.succ := by
    apply Fin.ext
    simp [a]
  rw [hia] at hTjSeedA
  exact (hseedU.2.1 a).trans hTjSeedA.symm

private theorem helper_hseedVertexBeforeJ_2905.{u_1, u_2} :
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
    ∀ (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc)) (terminalPosition : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (hterminalPositionPositive : (1 : ℕ) ≤
        (↑terminalPosition : ℕ)) (hterminalPositionBound : (↑terminalPosition : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (_ :
        seed.vertex (Fin.last seed.length) = v) (i : Fin (seed.length + (1 : ℕ))) (_ : (↑i : ℕ) <
        seed.length), seed.vertex i ∈ TreeVerticesBefore (ett.series.data.tree
        jSlot.succ.castSucc) v hterminalJ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot vertexTransfer hterminalJ terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedTj hseedTerminal i hi
  unfold TreeVerticesBefore
  apply Finset.mem_filter.mpr
  constructor
  · exact vertexTransfer hseedTj
      (by simp [TreeSequenceVertexSet])
  · let p : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + 1) :=
      Fin.castLE (Nat.succ_le_succ hseedTj.1) i
    let z : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + 1) :=
      Fin.castLE (Nat.succ_le_succ hseedTj.1)
        (Fin.last seed.length)
    refine ⟨p, z, hseedTj.2.1 i,
      (hseedTj.2.1 (Fin.last seed.length)).trans hseedTerminal, ?_⟩
    simpa [p, z] using hi

private theorem helper_transportSeedStep2_2940.{u_1, u_2} :
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
    ∀ (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (trace :
        ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin
        ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0) (u : V) (b : Fin (p0 + (1 : ℕ))) (traceB :
        ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
    ∀ (_ : StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) (traceB.coloring (Fin.last traceB.steps))) (_ : Fin (TjPrime.length + (1 :
        ℕ))) (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A seed) (_ : A.length < seed.length)
        {x : V} (_ : x ∈ TreeSequenceVertexSet A), x ∈ TreeVerticesBefore (ett.series.data.tree
        jSlot.succ.castSucc) v hterminalJ)) {A B : TreeSequence G e0} (_ : TashkinovAugmentation
        (ett.series.data.coloring jSlot.castSucc) A B) (_ : TreeSequenceInitialSegment B seed),
        TashkinovAugmentation rho2 A B := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot segmentTrans trace hterminalJ p0 indices0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed TjPrime u b traceB
      rho2 c1 uPosition segmentVertexBeforeJ A B hstep hBseed
  rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
  have hAseed : TreeSequenceInitialSegment A seed :=
    segmentTrans hAB hBseed
  have hAlen : A.length < seed.length :=
    lt_of_lt_of_le (by omega) hBseed.1
  have hcMissingRho : c ∈ TreeMissingColors rho2 A := by
    unfold TreeMissingColors at hcMissing ⊢
    obtain ⟨x, hxA, hcx⟩ := Finset.mem_biUnion.mp hcMissing
    refine Finset.mem_biUnion.mpr ⟨x, hxA, ?_⟩
    rw [c1.2 x (segmentVertexBeforeJ hAseed hAlen hxA)]
    exact hcx
  let added : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
  obtain ⟨attach, hattach⟩ := B.attaches added
  let oldPosition : Fin (B.length + 1) :=
    Fin.castLT attach
      (Nat.lt_trans attach.isLt (Nat.succ_lt_succ added.isLt))
  have holdValue : oldPosition.val < A.length + 1 := by
    dsimp [oldPosition, added]
    omega
  let oldA : Fin (A.length + 1) := ⟨oldPosition.val, holdValue⟩
  have holdEq : B.vertex oldPosition = A.vertex oldA := by
    have hcast : Fin.castLE (Nat.succ_le_succ hAB.1) oldA =
        oldPosition := by
      apply Fin.ext
      rfl
    rw [← hcast]
    exact hAB.2.1 oldA
  have holdA : A.vertex oldA ∈ TreeSequenceVertexSet A := by
    simp [TreeSequenceVertexSet]
  have holdBefore : B.vertex oldPosition ∈ TreeVerticesBefore
      (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
    rw [holdEq]
    exact segmentVertexBeforeJ hAseed hAlen holdA
  have holdIncident : Incident G (B.vertex oldPosition)
      (B.edge added) := by
    unfold Incident
    rw [hattach]
    simp [oldPosition]
  have haddedFixed : rho2 (B.edge added) =
      ett.series.data.coloring jSlot.castSucc (B.edge added) := by
    apply c1.1 (B.edge added)
      ⟨B.vertex oldPosition, holdBefore, holdIncident⟩
    refine ⟨c, ?_, hcolor⟩
    apply Finset.mem_union_left
    unfold TreeMissingColors at hcMissing
    obtain ⟨x, hxA, hcx⟩ := Finset.mem_biUnion.mp hcMissing
    exact Finset.mem_biUnion.mpr
      ⟨x, segmentVertexBeforeJ hAseed hAlen hxA, hcx⟩
  refine ⟨hlen, hAB, c, ?_, hcMissingRho⟩
  change rho2 (B.edge added) = some c
  exact haddedFixed.trans hcolor

private theorem helper_branch_3050.{u_1, u_2} :
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
        (ett.series.data.coloring i.succ) adjoinSeed seed := by
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

private theorem helper_branch_3107.{u_1, u_2} :
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
        (ett.series.data.coloring i.succ) adjoinSeed seed := by
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

private theorem helper_branch_3129.{u_1, u_2} :
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
        (ett.series.data.coloring i.succ) adjoinSeed seed := by
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

private theorem helper_hstablePrevious_3232.{u_1, u_2} :
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
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈
        TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (indices0 : Fin
        (p0 + (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (u : V) (b : Fin (p0 + (1 : ℕ))) (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u p0
        indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
    ∀ (_ : StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) (traceB.coloring (Fin.last traceB.steps))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length)) (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), TreeSequenceInitialSegment Tprevious seed)) (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A seed) (_ : A.length < seed.length)
        {x : V} (_ : x ∈ TreeSequenceVertexSet A), x ∈ TreeVerticesBefore (ett.series.data.tree
        jSlot.succ.castSucc) v hterminalJ)) (_ : (0 : ℕ) < (↑jSlot : ℕ)), StableColoring Tprevious
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho2 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace hterminalJ p0 indices0 rho1 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed u b traceB rho2 c1 Tprevious
      hpreviousStrict hpreviousSeed segmentVertexBeforeJ hjPositive
  constructor
  · intro f hfIncident hfControlled
    obtain ⟨x, hxPrevious, hxf⟩ := hfIncident
    apply c1.1 f
      ⟨x, segmentVertexBeforeJ (hpreviousSeed hjPositive)
        (hpreviousStrict hjPositive) hxPrevious, hxf⟩
    obtain ⟨color, hcControlled, hfc⟩ := hfControlled
    refine ⟨color, ?_, hfc⟩
    rcases Finset.mem_union.mp hcControlled with hcMissing | hcStored
    · apply Finset.mem_union_left
      unfold TreeMissingColors at hcMissing
      obtain ⟨z, hzPrevious, hcz⟩ :=
        Finset.mem_biUnion.mp hcMissing
      exact Finset.mem_biUnion.mpr
        ⟨z, segmentVertexBeforeJ (hpreviousSeed hjPositive)
          (hpreviousStrict hjPositive) hzPrevious, hcz⟩
    · exact Finset.mem_union_right _ hcStored
  · intro x hxPrevious
    exact c1.2 x
      (segmentVertexBeforeJ (hpreviousSeed hjPositive)
        (hpreviousStrict hjPositive) hxPrevious)

private theorem helper_hcorrNonempty_3307.{u_1, u_2} :
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
    ∀ (u : V) (b : Fin (p0 + (1 : ℕ))) (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u p0
        indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (C : TreeSequence G e0) (lower : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (⟨(↑jSlot : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨(↑jSlot : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))),
    let nLower : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
    ∀ (_ : lower.series.data.tree nLower.castSucc = Tprevious) (_ : ModColoring lower rho2) (_ :
        TreeSequenceInitialSegment Tprevious C) (_ : Tprevious.length < C.length) (_ :
        (lower.series.data.kind nLower = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho2 Tprevious C ∨ (lower.series.data.kind nLower = some
        TashkinovExtensionKind.SE ∨ lower.series.data.kind nLower = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), lower.series.data.connectingEdges nLower = { f } ∧
        TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧ TashkinovAugmentationSequence rho2
        adjoinSeed C)), Nonempty (CorrespondingExtendedTashkinovTree G k e0 lower rho2 C) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace p0 indices0 rho1 u b traceB rho2 Tprevious C lower
      nLower hLowerTree hmod hPreviousC hPreviousStrictC hLowerEligible
  have hmod' := hmod
  unfold ModColoring at hmod'
  dsimp only at hmod'
  apply hmod'.2.2 C
  · rw [hLowerTree]
    exact hPreviousC
  · rw [hLowerTree]
    exact hPreviousStrictC
  · change
      (lower.series.data.kind nLower =
            some TashkinovExtensionKind.PE ∧
          TashkinovAugmentationSequence rho2
            (lower.series.data.tree nLower.castSucc) C) ∨
        ((lower.series.data.kind nLower =
              some TashkinovExtensionKind.SE ∨
            lower.series.data.kind nLower =
              some TashkinovExtensionKind.RE) ∧
          ∃ (f : E) (adjoinSeed : TreeSequence G e0),
            lower.series.data.connectingEdges nLower = {f} ∧
              TreeSequenceAdjoinEdge
                (lower.series.data.tree nLower.castSucc) f adjoinSeed ∧
              TashkinovAugmentationSequence rho2 adjoinSeed C)
    rw [hLowerTree]
    exact hLowerEligible

private theorem helper_hbound_3342.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (v :
        V) (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (trace :
        ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0) (_ : indices0 (Fin.last p0) = q) (u : V) (b : Fin (p0 + (1 :
        ℕ))) (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
    ∀ (_ : IsProperEdgeColoring G rho2) (_ : IsOneEdgeUncolored rho2 e0) (_ : Fin (TjPrime.length
        + (1 : ℕ))),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (C : TreeSequence G e0) (_ : TashkinovAugmentationSequence rho2 seed C) (_ :
        ColoredVertexSetClosed G rho2 (TreeSequenceVertexSet C)) (_ : (0 : ℕ) < (↑jSlot : ℕ)) (_ :
        (ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho2 Tprevious seed ∨ (ett.series.data.kind jSlot.castSucc =
        some TashkinovExtensionKind.SE ∨ ett.series.data.kind jSlot.castSucc = some
        TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges jSlot.castSucc =
        { f } ∧ TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧ TashkinovAugmentationSequence rho2
        adjoinSeed seed)) (lower : ExtendedTashkinovTree G k e0 input (ett.series.data.tree
        (⟨(↑jSlot : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.coloring (⟨(↑jSlot : ℕ),
    by omega
    ⟩ : Fin (ett.rounds + (1 : ℕ))))) (_ : lower.rounds = (↑jSlot : ℕ)) (_ : StableColoring
        Tprevious (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho2) (corr : CorrespondingExtendedTashkinovTree G k e0 lower rho2 C) (_ :
        corr.replacementETT.rounds = (↑jSlot : ℕ)), (TreeSequenceVertexSet C).card ≤
        (TreeSequenceVertexSet Tj0).card := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot hjSlot trace p0 indices0 rho1 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed TjPrime hqLast u b traceB rho2
      hrho2Proper hrho2One uPosition Tprevious Tj0 C hrouteSeedC hclosedC hjPositive
      hseedBuildRho2 lower hround hstablePrevious corr hcorrRounds
  have hMP' := hMP
  unfold MaximumProperty at hMP'
  have hstage := hMP'.2 jSlot.val hjPositive jSlot.isLt
  dsimp only at hstage
  have hidx : (⟨jSlot.val, by omega⟩ : Fin (ett.rounds + 1)) =
      jSlot.castSucc := by
    apply Fin.ext
    rfl
  have hnextIdx :
      (⟨jSlot.val + 1, by omega⟩ : Fin (ett.rounds + 2)) =
        jSlot.succ.castSucc := by
    apply Fin.ext
    rfl
  rw [hidx, hnextIdx] at hstage
  rcases hseedBuildRho2 with hparallel | hserial
  · have hclosurePreviousC : TashkinovClosure rho2 Tprevious C :=
      ⟨Relation.ReflTransGen.trans hparallel.2 hrouteSeedC,
        hclosedC⟩
    have hraw := hstage rho2 Tprevious C hrho2Proper hrho2One
      hstablePrevious
      (Or.inl ⟨hparallel.1, rfl⟩) hclosurePreviousC
    simpa [Tprevious, Tj0] using hraw
  · rcases hserial with ⟨hkind, f, adjoinSeed, hconnecting,
        hadjoin, hroute⟩
    have hclosureAdjoinC : TashkinovClosure rho2 adjoinSeed C :=
      ⟨Relation.ReflTransGen.trans hroute hrouteSeedC, hclosedC⟩
    have hraw := hstage rho2 adjoinSeed C hrho2Proper hrho2One
      hstablePrevious
      (Or.inr ⟨hkind, f, hconnecting, by
        simpa [Tprevious] using hadjoin⟩) hclosureAdjoinC
    simpa [Tj0] using hraw

private theorem helper_branch_3377.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (v :
        V) (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (trace :
        ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)) (TjPrime : TreeSequence G e0) (u : V) (b : Fin (p0 + (1 : ℕ))) (traceB :
        ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
    ∀ (_ : IsProperEdgeColoring G rho2) (_ : IsOneEdgeUncolored rho2 e0) (_ : Fin (TjPrime.length
        + (1 : ℕ))),
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (_ : TreeSequenceInitialSegment seed Tj0) (C : TreeSequence G e0) (_ :
        TashkinovAugmentationSequence rho2 seed C) (_ : (
    ∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed), TashkinovAugmentationSequence rho2 S seed)) (_ :
        TreeSequenceVertexSet Tj0 ⊂ TreeSequenceVertexSet C) (_ : ¬(0 : ℕ) < (↑jSlot : ℕ)), False
  := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot hjSlot trace p0 indices0 rho1 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed commonPrefix TjPrime u b traceB rho2
      hrho2Proper hrho2One uPosition Tj0 hseedTj0 C hrouteSeedC transportSeedRoute2 hTj0StrictC
      hjPositive
  have hjZero : jSlot.val = 0 := by omega
  have hjIndex : jSlot.castSucc =
      (0 : Fin (ett.rounds + 1)) := by
    apply Fin.ext
    exact hjZero
  cases hcert : ett.series.certified
      (0 : Fin (ett.rounds + 1)) with
  | initial triple seedLength initialColoring initialStored initialEdges
    initialKind initialVertex initialOutside initialDelta initialGamma
    initialClosure =>
    have htreeOne : ett.series.data.tree 1 = Tj0 := by
      unfold Tj0
      congr 1
      apply Fin.ext
      simp [hjZero]
    have hinitialTj : TreeSequenceInitialSegment
        (ett.series.data.tree 0) Tj0 := by
      have h := TashkinovAugmentationSequenceInitialSegment _ _ _
        initialClosure.1
      simpa [htreeOne] using h
    have hinitialSeed : TreeSequenceInitialSegment
        (ett.series.data.tree 0) seed := by
      apply commonPrefix hinitialTj
        (by simpa [Tj0] using hseedTj0)
      rw [seedLength]
      exact seed.positive
    have hroutePhiSeed : TashkinovAugmentationSequence
        (ett.series.data.coloring jSlot.castSucc)
        (ett.series.data.tree 0) seed := by
      have hrestricted := TashkinovAugmentationSequenceRestrict
        (ett.series.data.coloring 0) (ett.series.data.tree 0) seed
        Tj0 (by simpa [htreeOne] using initialClosure.1)
        hinitialSeed (by simpa [Tj0] using hseedTj0)
      simpa [hjIndex] using hrestricted
    have hrouteRhoTwoBase : TashkinovAugmentationSequence rho2
        (ett.series.data.tree 0) seed :=
      transportSeedRoute2 (ett.series.data.tree 0) hroutePhiSeed
    have hrouteBaseC : TashkinovAugmentationSequence rho2
        (ett.series.data.tree 0) C :=
      Relation.ReflTransGen.trans hrouteRhoTwoBase hrouteSeedC
    have htripleRho : KTriple G k e0 rho2 :=
      ⟨triple.1, triple.2.1, triple.2.2.1,
        hrho2Proper, hrho2One⟩
    have hinitialTree : TashkinovTree G e0 rho2
        (ett.series.data.tree 0) := by
      intro a ha
      rw [seedLength] at a
      omega
    have hCTree : TashkinovTree G e0 rho2 C :=
      TashkinovAugmentationSequencePreservesTashkinovTree G e0 rho2
        (ett.series.data.tree 0) C hinitialTree hrouteBaseC
    have hk : ChromaticIndex G - 1 = k := by
      have hchromatic := triple.2.1
      omega
    have hCOrder : (TreeSequenceVertexSet C).card ≤
        TashkinovOrder G := by
      unfold TashkinovOrder
      dsimp only
      apply Finset.le_max'
      apply Finset.mem_insert_of_mem
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact Nat.lt_succ_of_le (Finset.card_le_univ _)
      · rw [hk]
        exact ⟨e0, rho2, C, htripleRho, hCTree, rfl⟩
    have hTjOrder : (TreeSequenceVertexSet Tj0).card =
        TashkinovOrder G := by
      rw [← htreeOne]
      exact hMP.1
    have hbound : (TreeSequenceVertexSet C).card ≤
        (TreeSequenceVertexSet Tj0).card := by
      rw [hTjOrder]
      exact hCOrder
    exact (Nat.not_lt_of_ge hbound)
      (Finset.card_lt_card hTj0StrictC)

private theorem helper_hdeltaEarlier_3576.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (delta : Fin k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (_ : ett.series.data.chosenVertex q.succ =
        some v) (_ : ett.series.data.delta q.succ = some delta) (hvFinal : v ∈
        TreeSequenceVertexSet T) (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) +
        (1 : ℕ)) (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : ((
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
        (ett.series.data.tree jSlot.succ.castSucc))) (_ : q ∈ ExtensionBaseActiveIndices ett v
        hvFinal) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin
        (p0 + (1 : ℕ)) → Fin k) (_ : (
    ∀ (a b : Fin (p0 + (1 : ℕ))) (_ : (↑a : ℕ) < (↑b : ℕ)), (↑(indices0 a) : ℕ) < (↑(indices0 b) :
        ℕ))) (_ : (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r)) (_ : (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a))) (_ :
        Function.Injective (Fin.cons (gamma0 (0 : Fin (p0 + (1 : ℕ)))) delta0)) (_ : indices0
        (Fin.last p0) = q) (_ : delta0 (Fin.last p0) = delta) (s : Fin ett.rounds) (gammaS deltaS
        : Fin k) (_ : s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q) (_ :
        ett.series.data.gamma s.succ = some gammaS) (_ : ett.series.data.delta s.succ = some
        deltaS), delta ≠ gammaS ∧ delta ≠ deltaS := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v delta q hqTerminal hqVertex hqDelta
      hvFinal hfirstUpper hfirstPositive jSlot hdeltaExclusion hqActive p0 indices0 gamma0 delta0
      hincreasing0 hclass0 hdelta0 hinjective0 hqLast hdeltaLast s gammaS deltaS hs hsGamma hsDelta
  have hsNeQ := (Finset.mem_erase.mp hs).1
  have hsClass := (Finset.mem_erase.mp hs).2
  obtain ⟨a, ha⟩ := (hclass0 s).1 hsClass
  have haNeLast : a ≠ Fin.last p0 := by
    intro haLast
    apply hsNeQ
    rw [← ha, haLast, hqLast]
  have hsq : s.val < q.val := by
    have haLt : a.val < (Fin.last p0).val :=
      Fin.lt_last_iff_ne_last.mpr haNeLast
    have hlt := hincreasing0 a (Fin.last p0) haLt
    simpa [ha, hqLast] using hlt
  have hsClassData := hsClass
  simp only [ExtensionBaseSupportClass, Finset.mem_filter] at hsClassData
  have hsGammaNe : delta ≠ gammaS :=
    (hdeltaExclusion.1 s q v v hvFinal hvFinal delta gammaS
      hsClassData.1 hqActive (Nat.le_of_lt hsq) hsClassData.2 hqVertex
      hqDelta hsGamma).2
  have hdeltaAEq : delta0 a = deltaS := by
    apply Option.some.inj
    exact (hdelta0 a).symm.trans (by simpa [ha] using hsDelta)
  have hsDeltaNe : delta ≠ deltaS := by
    intro hEq
    have hvalues :
        (Fin.cons (gamma0 0) delta0 : Fin (p0 + 2) → Fin k) a.succ =
          (Fin.cons (gamma0 0) delta0 : Fin (p0 + 2) → Fin k)
            (Fin.last p0).succ := by
      simp [hdeltaAEq, hdeltaLast, hEq]
    have hindices := hinjective0 hvalues
    apply haNeLast
    apply Fin.ext
    have hvals := congrArg Fin.val hindices
    simpa using hvals
  exact ⟨hsGammaNe, hsDeltaNe⟩

private theorem helper_hpreterminalPackage_3617.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma _ : Fin k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 :
        ℕ)) → Fin k) (_ : (
    ∀ (a b : Fin (p0 + (1 : ℕ))) (_ : (↑a : ℕ) < (↑b : ℕ)), (↑(indices0 a) : ℕ) < (↑(indices0 b) :
        ℕ))) (_ : (
    ∀ (r : Fin ett.rounds), r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
    ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r)) (_ : (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.delta (indices0 a).succ = some (delta0 a))) (_ : (
    ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc)) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (_ : indices0 (Fin.last p0) = q) (_ : gamma0
        (Fin.last p0) = gamma) (_ : (0 : ℕ) < p0),
    ∃ (preterminalSlot : Fin ett.rounds), (↑preterminalSlot : ℕ) < (↑q : ℕ) ∧ preterminalSlot ∈
        (ExtensionBaseSupportClass ett v hvFinal v).erase q ∧ ett.series.data.delta
        preterminalSlot.succ = some gamma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot p0 indices0 gamma0 delta0 hincreasing0 hclass0 hdelta0
      hchain0 terminalPosition hqLast hgammaLast hp0
  let a : Fin p0 := ⟨p0 - 1, by omega⟩
  let a0 : Fin (p0 + 1) := ⟨p0 - 1, by omega⟩
  have haCast : a.castSucc = a0 := by
    apply Fin.ext
    rfl
  have haSucc : a.succ = Fin.last p0 := by
    apply Fin.ext
    simp [a]
    omega
  have haLast : a0.val < (Fin.last p0).val := by
    simp [a0]
    omega
  have hslotOrder : (indices0 a0).val < q.val := by
    have h := hincreasing0 a0 (Fin.last p0) haLast
    simpa [hqLast] using h
  have hslotClass : indices0 a0 ∈
      ExtensionBaseSupportClass ett v hvFinal v :=
    (hclass0 (indices0 a0)).2 ⟨a0, rfl⟩
  have hslotNe : indices0 a0 ≠ q := by
    intro heq
    rw [heq] at hslotOrder
    exact (Nat.lt_irrefl _ hslotOrder)
  have hdeltaGamma : ett.series.data.delta (indices0 a0).succ =
      some gamma := by
    rw [hdelta0 a0]
    have hchain := hchain0 a
    rw [haCast, haSucc] at hchain
    rw [← hchain, hgammaLast]
  exact ⟨indices0 a0, hslotOrder,
    Finset.mem_erase.mpr ⟨hslotNe, hslotClass⟩, hdeltaGamma⟩

private theorem helper_hsupportComponentOrder_3667.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (_ _ : Fin k) (sigma :
        PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (_ : ett.series.data.kind q.succ = some
        TashkinovExtensionKind.PE) (hvFinal : v ∈ TreeSequenceVertexSet T) (hfirstUpper :
        ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive : (0 : ℕ) <
        ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : (
    ∀ (a b : ℕ) (_ : (1 : ℕ) ≤ a) (_hab : a ≤ b) (_hb : b ≤ ett.rounds),
        TreeSequenceInitialSegment (ett.series.data.tree (⟨a,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))) (ett.series.data.tree (⟨b,
    by omega
    ⟩ : Fin (ett.rounds + (2 : ℕ)))))) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0
        : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (_ : indices0
        (Fin.last p0) = q) (_ : (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ (ExtensionBaseSupportClass ett v
        hvFinal v).erase q) (_ : ett.series.data.gamma s.succ = some gammaS) (_ :
        ett.series.data.delta s.succ = some deltaS), ETTStrongInterchangeable ett s v rho1 gammaS
        deltaS)) (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ (ExtensionBaseSupportClass
        ett v hvFinal v).erase q) (_ : ett.series.data.gamma s.succ = some gammaS) (_ :
        ett.series.data.delta s.succ = some deltaS),
    ∀ x ∈ TreeSequenceVertexSet (ett.series.data.tree s.succ.castSucc), x ≠ v →
    ∀ (y : V), Sum.inl y ∈ TwoColorComponent G rho1 gammaS deltaS (Sum.inl x) → y ∈
        TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal hqKind
      hvFinal hfirstUpper hfirstPositive jSlot stageToStage vertexTransfer trace p0 indices0
      gamma0 delta0 rho1 terminalPosition hqLast hb4Earlier s gammaS deltaS hs hsGamma hsDelta x
      hx hxNe y hy
  have hsNeQ := (Finset.mem_erase.mp hs).1
  have hsClass := (Finset.mem_erase.mp hs).2
  obtain ⟨hneColors, hsKind, hsVertex, epsilon, hsEpsilon,
      hepsilonKind, hbetween, hcycles⟩ :=
    hb4Earlier s gammaS deltaS hs hsGamma hsDelta
  have hsq : s.val < q.val := by
    have hle : s.val ≤ q.val := by omega
    exact lt_of_le_of_ne hle (fun heq => hsNeQ (Fin.ext heq))
  have hepsilonQ : epsilon.val ≤ q.val := by
    by_contra hnot
    have hqRE := hbetween q hsq (by omega)
    rw [hqKind] at hqRE
    simp at hqRE
  have hyEpsilon := (hcycles x hx hxNe).2.2 y hy
  have hsegment := stageToStage (epsilon.val + 1) (q.val + 1)
    (by omega) (by omega) (by omega)
  have hyQ := vertexTransfer hsegment hyEpsilon
  convert hyQ using 1; congr 1

private theorem helper_hdeltaLocation_3782.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k)
        (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : seed.vertex (Fin.last seed.length) = v) (_ : TreeSequenceInitialSegment seed
        (ett.series.data.tree q.succ.castSucc)) (fN : E) (_ : BoundaryColorEdges G
        (ett.series.data.coloring q.succ) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) gamma = { fN } ∧ (
    ∀ g ∈ BoundaryColorEdges G (ett.series.data.coloring q.succ) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) delta,
    ∃ (w : V), TreeVertexOrder (ett.series.data.tree q.succ.castSucc) w v ∧ Incident G w g) ∧
        (ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) →
    ∀ alpha ∈ TreeMissingColors (ett.series.data.coloring q.succ) (ett.series.data.tree
        q.succ.castSucc), alpha ≠ delta → BoundaryColorEdges G (ett.series.data.coloring q.succ)
        (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) alpha = ∅)),
    ∀ f ∈ BoundaryColorEdges G (ett.series.data.coloring q.succ) (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) delta,
    ∃ y ∈ TreeSequenceVertexSet seed, Incident G y f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot p0 indices0 gamma0 delta0 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed hseedTerminal hseedN fN
      hboundaryStructure f hf
  obtain ⟨y, hyOrder, hyf⟩ := hboundaryStructure.2.1 f hf
  rcases hyOrder with ⟨iy, iv, hiy, hiv, hlt⟩
  let terminalN : Fin
      ((ett.series.data.tree q.succ.castSucc).length + 1) :=
    Fin.castLE (Nat.succ_le_succ hseedN.1) (Fin.last seed.length)
  have hterminalN :
      (ett.series.data.tree q.succ.castSucc).vertex terminalN = v := by
    exact (hseedN.2.1 (Fin.last seed.length)).trans hseedTerminal
  have hivTerminal : iv = terminalN := by
    apply (ett.series.data.tree q.succ.castSucc).vertex_injective
    exact hiv.trans hterminalN.symm
  have hiyBound : iy.val < seed.length + 1 := by
    rw [hivTerminal] at hlt
    have hiyStrict : iy.val < seed.length := by
      simpa [terminalN] using hlt
    omega
  let iySeed : Fin (seed.length + 1) := ⟨iy.val, hiyBound⟩
  have hcast : Fin.castLE (Nat.succ_le_succ hseedN.1) iySeed = iy := by
    apply Fin.ext
    rfl
  have hySeed : seed.vertex iySeed = y := by
    have hvertex := hseedN.2.1 iySeed
    rw [hcast] at hvertex
    exact hvertex.symm.trans hiy
  refine ⟨y, ?_, hyf⟩
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact ⟨iySeed, hySeed⟩

private theorem helper_hterminalEdgeValues_3881.{u_1, u_2} :
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
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : (
    ∀ (f : E) (_ : rho1 f ≠ sigma f), f ∉ InternalEdges G (TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)) ∧
    ∃ (c : Fin k) (d : Fin k), sigma f = some c ∧ rho1 f = some d ∧ (c ∈
        (ExtensionBaseRestorationIndices ett v hvFinal).biUnion fun (t : Fin ett.rounds) ↦
        ett.series.data.stored t.succ) ∧ d ∈ (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ)),
    let restorationColors : Finset (Fin k) := (ExtensionBaseRestorationIndices ett v
        hvFinal).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ;
    ∀ (_ : gamma ∉ restorationColors ∧ delta ∉ restorationColors) (f : E), sigma f = some gamma ∨
        sigma f = some delta ↔ rho1 f = some gamma ∨ rho1 f = some delta := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace rho1 hb3EdgeEffects restorationColors
      hterminalColorsNotRestored f
  constructor
  · intro hf
    by_cases heq : rho1 f = sigma f
    · simpa [heq] using hf
    · obtain ⟨c, d, hsc, hrd, hcRestored, hdRestored⟩ :=
        (hb3EdgeEffects f heq).2
      rcases hf with hfgamma | hfdelta
      · have hc : c = gamma := Option.some.inj (hsc.symm.trans hfgamma)
        exact False.elim (hterminalColorsNotRestored.1 (hc ▸ hcRestored))
      · have hc : c = delta := Option.some.inj (hsc.symm.trans hfdelta)
        exact False.elim (hterminalColorsNotRestored.2 (hc ▸ hcRestored))
  · intro hf
    by_cases heq : rho1 f = sigma f
    · simpa [heq] using hf
    · obtain ⟨c, d, hsc, hrd, hcRestored, hdRestored⟩ :=
        (hb3EdgeEffects f heq).2
      rcases hf with hfgamma | hfdelta
      · have hd : d = gamma := Option.some.inj (hrd.symm.trans hfgamma)
        exact False.elim (hterminalColorsNotRestored.1 (hd ▸ hdRestored))
      · have hd : d = delta := Option.some.inj (hrd.symm.trans hfdelta)
        exact False.elim (hterminalColorsNotRestored.2 (hd ▸ hdRestored))

private theorem helper_hendpointNeighbor_4002.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let _ : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : IsProperEdgeColoring G rho1)
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let C : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (_ : (H.neighborSet (Sum.inl v)).Subsingleton) (endpoint : V ⊕ E)
      (componentPath : H.Walk (Sum.inl v) endpoint) (_ : componentPath.IsPath)
      (_ : {z : V ⊕ E | z ∈ componentPath.support} = C) (_ : ¬componentPath.Nil)
      (_ : (0 : ℕ) < componentPath.length) (_ : endpoint ∈ C) (z : V ⊕ E)
      (_ : H.Adj endpoint z),
    z = componentPath.getVert (componentPath.length - (1 : ℕ)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1 hrho1Proper
      terminalPosition H C hvSub endpoint componentPath hcomponentPath hcomponentSupport
      hcomponentNonempty hcomponentPositive hendpointC z hez
  have hzC : z ∈ C := by
    change H.connectedComponentMk z = H.connectedComponentMk (Sum.inl v)
    change H.connectedComponentMk endpoint =
      H.connectedComponentMk (Sum.inl v) at hendpointC
    exact
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        hez).symm.trans hendpointC
  have hzSupport : z ∈ componentPath.support := by
    change z ∈ {y | y ∈ componentPath.support}
    rw [hcomponentSupport]
    exact hzC
  obtain ⟨n, hn, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzSupport
  have hnlt : n < componentPath.length := by
    have hnne : n ≠ componentPath.length := by
      intro heq
      have hze : z = endpoint := by
        rw [← hn, heq, componentPath.getVert_length]
      exact hez.ne hze.symm
    omega
  by_cases hpen : n + 1 = componentPath.length
  · rw [← hn]
    congr 1
    omega
  by_cases hn0 : n = 0
  · have hnext : H.Adj (Sum.inl v) (componentPath.getVert 1) := by
      simpa [hn0, componentPath.getVert_zero] using
        componentPath.adj_getVert_succ hnlt
    have hendStart : H.Adj (Sum.inl v) endpoint := by
      rw [← hn, hn0, componentPath.getVert_zero] at hez
      exact hez.symm
    have hnextNe : componentPath.getVert 1 ≠ endpoint := by
      intro heq
      have hindices := hcomponentPath.getVert_injOn
        (show 1 ≤ componentPath.length by omega)
        (show componentPath.length ≤ componentPath.length by rfl)
        (heq.trans componentPath.getVert_length.symm)
      omega
    exact False.elim (hnextNe (hvSub hnext hendStart))
  · have hleft : H.Adj z (componentPath.getVert (n - 1)) := by
      rw [← hn]
      have hadj := componentPath.adj_getVert_succ (i := n - 1) (by omega)
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hadj.symm
    have hright : H.Adj z (componentPath.getVert (n + 1)) := by
      rw [← hn]
      exact componentPath.adj_getVert_succ hnlt
    have hendNeLeft : endpoint ≠ componentPath.getVert (n - 1) := by
      intro heq
      have hindices := hcomponentPath.getVert_injOn
        (show componentPath.length ≤ componentPath.length by rfl)
        (show n - 1 ≤ componentPath.length by omega)
        (componentPath.getVert_length.trans heq)
      omega
    have hendNeRight : endpoint ≠ componentPath.getVert (n + 1) := by
      intro heq
      have hindices := hcomponentPath.getVert_injOn
        (show componentPath.length ≤ componentPath.length by rfl)
        (show n + 1 ≤ componentPath.length by omega)
        (componentPath.getVert_length.trans heq)
      omega
    have hlrNe : componentPath.getVert (n - 1) ≠
        componentPath.getVert (n + 1) := by
      intro heq
      have hindices := hcomponentPath.getVert_injOn
        (show n - 1 ≤ componentPath.length by omega)
        (show n + 1 ≤ componentPath.length by omega) heq
      omega
    let : Fintype (H.neighborSet z) := Fintype.ofFinite _
    have hthree : 3 ≤ @SimpleGraph.degree _ H z (Fintype.ofFinite _) := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      let neighbors : Finset (Sum V E) :=
        {endpoint, componentPath.getVert (n - 1),
          componentPath.getVert (n + 1)}
      have hsubset : neighbors ⊆ H.neighborFinset z := by
        intro y hy
        simp only [neighbors, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · simpa [SimpleGraph.mem_neighborFinset] using hez.symm
        · simpa [SimpleGraph.mem_neighborFinset] using hleft
        · simpa [SimpleGraph.mem_neighborFinset] using hright
      have hcard : 3 ≤ neighbors.card := by
        simp [neighbors, hendNeLeft, hendNeRight, hlrNe]
      exact hcard.trans (Finset.card_le_card hsubset)
    have htwo : @SimpleGraph.degree _ H z (Fintype.ofFinite _) ≤ 2 := by
      change @SimpleGraph.degree _
        (TwoColorIncidenceGraph G rho1 gamma delta) z
          (Fintype.ofFinite _) ≤ 2
      exact TwoColorIncidenceDegreeAtMostTwo G rho1 gamma delta
        hrho1Proper z
    omega

private theorem helper_hendpointVertex_4095.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (endpoint : V ⊕ E) (componentPath : H.Walk (Sum.inl v) endpoint)
      (_ : (0 : ℕ) < componentPath.length)
      (_ :
        (∀ (z : V ⊕ E) (_ : H.Adj endpoint z),
          z = componentPath.getVert (componentPath.length - (1 : ℕ)))),
    ∃ (x : V),
    endpoint = Sum.inl x := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition H endpoint componentPath hcomponentPositive hendpointNeighbor
  cases hendpoint : endpoint with
  | inl x => exact ⟨x, rfl⟩
  | inr f =>
      have hlastAdj : H.Adj
          (componentPath.getVert (componentPath.length - 1)) endpoint := by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ componentPath.length),
          componentPath.getVert_length] using
          componentPath.adj_getVert_succ
            (i := componentPath.length - 1) (by omega)
      have hfColor : rho1 f = some gamma ∨ rho1 f = some delta := by
        cases hprevious : componentPath.getVert
            (componentPath.length - 1) with
        | inl y =>
            rw [hprevious, hendpoint] at hlastAdj
            simpa [H, TwoColorIncidenceGraph] using hlastAdj |>.2
        | inr g =>
            rw [hprevious, hendpoint] at hlastAdj
            simp [H, TwoColorIncidenceGraph] at hlastAdj
      induction hends : G.ends f using Sym2.inductionOn with
      | _ y z =>
          have hyz : y ≠ z := by
            intro hyz
            subst z
            exact G.loopless f y hends
          have hyAdj : H.Adj endpoint (Sum.inl y) := by
            rw [hendpoint]
            simpa [H, TwoColorIncidenceGraph, Incident, hends] using
              (show Incident G y f ∧
                  (rho1 f = some gamma ∨ rho1 f = some delta) from
                ⟨by simp [Incident, hends], hfColor⟩)
          have hzAdj : H.Adj endpoint (Sum.inl z) := by
            rw [hendpoint]
            simpa [H, TwoColorIncidenceGraph, Incident, hends] using
              (show Incident G z f ∧
                  (rho1 f = some gamma ∨ rho1 f = some delta) from
                ⟨by simp [Incident, hends], hfColor⟩)
          have heq := (hendpointNeighbor _ hyAdj).trans
            (hendpointNeighbor _ hzAdj).symm
          exact False.elim (hyz (Sum.inl.inj heq))

private theorem helper_swapBothPresent_4143.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (phi : PartialEdgeColoring E k) (alpha beta : Fin k), alpha ≠ beta →
    ∀ (root : V ⊕ E) (y : V), alpha ∈ PresentColors G phi y → beta ∈ PresentColors G phi y → alpha
        ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta root) y ∧ beta ∈ PresentColors G
        (TwoColorComponentSwap G phi alpha beta root) y := by
  classical
  intro V E _ _ G k phi alpha beta hne root y halpha hbeta
  let _ := Fintype.ofFinite V
  obtain ⟨eAlpha, heAlphaIncident, heAlphaColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] using halpha
  obtain ⟨eBeta, heBetaIncident, heBetaColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] using hbeta
  let K := TwoColorComponent G phi alpha beta root
  have hedgeSameComponent : Sum.inr eAlpha ∈ K ↔ Sum.inr eBeta ∈ K := by
    let J := TwoColorIncidenceGraph G phi alpha beta
    have hAlphaAdj : J.Adj (Sum.inl y) (Sum.inr eAlpha) := by
      simpa [J, TwoColorIncidenceGraph] using
        (show Incident G y eAlpha ∧
            (phi eAlpha = some alpha ∨ phi eAlpha = some beta) from
          ⟨heAlphaIncident, Or.inl heAlphaColor⟩)
    have hBetaAdj : J.Adj (Sum.inl y) (Sum.inr eBeta) := by
      simpa [J, TwoColorIncidenceGraph] using
        (show Incident G y eBeta ∧
            (phi eBeta = some alpha ∨ phi eBeta = some beta) from
          ⟨heBetaIncident, Or.inr heBetaColor⟩)
    constructor
    · intro hAlpha
      change J.connectedComponentMk (Sum.inr eBeta) =
        J.connectedComponentMk root
      change J.connectedComponentMk (Sum.inr eAlpha) =
        J.connectedComponentMk root at hAlpha
      exact
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hBetaAdj).symm.trans
        ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hAlphaAdj).trans hAlpha)
    · intro hBeta
      change J.connectedComponentMk (Sum.inr eAlpha) =
        J.connectedComponentMk root
      change J.connectedComponentMk (Sum.inr eBeta) =
        J.connectedComponentMk root at hBeta
      exact
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hAlphaAdj).symm.trans
        ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hBetaAdj).trans hBeta)
  by_cases hAlphaK : Sum.inr eAlpha ∈ K
  · have hBetaK : Sum.inr eBeta ∈ K := hedgeSameComponent.mp hAlphaK
    constructor
    · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      refine ⟨eBeta, heBetaIncident, ?_⟩
      simp [TwoColorComponentSwap, K, hBetaK, heBetaColor]
    · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      refine ⟨eAlpha, heAlphaIncident, ?_⟩
      simp [TwoColorComponentSwap, K, hAlphaK, heAlphaColor]
  · have hBetaK : Sum.inr eBeta ∉ K := by
      intro h
      exact hAlphaK (hedgeSameComponent.mpr h)
    constructor
    · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨eAlpha, heAlphaIncident, by
        simpa [TwoColorComponentSwap, K, hAlphaK] using heAlphaColor⟩
    · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨eBeta, heBetaIncident, by
        simpa [TwoColorComponentSwap, K, hBetaK] using heBetaColor⟩

private theorem helper_hTnElementary_4214.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
       [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating) (_ : MaximumProperty ett)
      (hpositive : (0 : ℕ) < ett.rounds)
      (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let _ : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : indices0 (Fin.last p0) = q),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)),
    ColoredVertexSetElementary G (ett.series.data.coloring q.castSucc)
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma this q
      hqTerminal hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hqLast H x componentPath
  by_cases hqPositive : 0 < q.val
  · obtain ⟨lower, hround, hlowerMP, htrees, hdata⟩ :=
      CertifiedETTRestriction G k e0 input T generating ett hMP
        q.val hqPositive q.isLt
    exact (hlower lower (by omega) (by omega) hlowerMP).1
  · have hqZero : q.val = 0 := by omega
    have hbase : ColoredVertexSetElementary G
        (ett.series.data.coloring 0)
        (TreeSequenceVertexSet
          (ett.series.data.tree ⟨1, by omega⟩)) :=
      (TechnicalTheoremBase G k ett.rounds e0 input ett.series).1
    have hcolor : q.castSucc = (0 : Fin (ett.rounds + 1)) := by
      apply Fin.ext
      exact hqZero
    have htree : q.succ.castSucc =
        (⟨1, by omega⟩ : Fin (ett.rounds + 2)) := by
      apply Fin.ext
      simp [hqZero]
    simpa [hcolor, htree] using hbase

private theorem helper_hgammaMissingPre_4237.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma : Fin k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (_ : ett.series.data.kind q.succ = some TashkinovExtensionKind.PE)
      (_ : ett.series.data.chosenVertex q.succ = some v)
      (_ : ett.series.data.gamma q.succ = some gamma),
    gamma ∈ MissingColors G (ett.series.data.coloring q.castSucc) v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma q hqKind hqVertex hqGamma
  generalize htarget : q.succ = target
  cases ett.series.certified target with
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
      actualGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hi : i = q := by
      apply Fin.ext
      simpa using (congrArg Fin.val htarget).symm
    subst i
    have hvChoice : choice.vertex = v :=
      Option.some.inj
        (currentVertex.symm.trans (by simpa [htarget] using hqVertex))
    have hgammaChoice : actualGamma = gamma :=
      Option.some.inj
        (currentGamma.symm.trans (by simpa [htarget] using hqGamma))
    have hmissingSelected : actualGamma ∈ MissingColors G
        choice.selected choice.vertex := gammaRule.1
    rw [choice.selectedStable.2 choice.vertex
      choice.vertexDefective.1] at hmissingSelected
    simpa only [hgammaChoice, hvChoice] using hmissingSelected

private theorem helper_hterminalPresentSigma_4287.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : ett.series.data.kind q.succ = some TashkinovExtensionKind.PE) (_ :
        ett.series.data.chosenVertex q.succ = some v) (_ : ett.series.data.gamma q.succ = some
        gamma) (_ : ett.series.data.delta q.succ = some delta) (_ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) (_ : StableColoring (ett.series.data.tree
        q.succ.castSucc) (TashkinovStoredColors ett.series.data q.succ) (ett.series.data.coloring
        q.succ) sigma) (_ : gamma ≠ delta) (_ : (
    ∀ (phi : PartialEdgeColoring E k) (alpha beta : Fin k) (_ : alpha ≠ beta) (root : V ⊕ E) (y :
        V) (_ : alpha ∈ PresentColors G phi y) (_ : beta ∈ PresentColors G phi y), alpha ∈
        PresentColors G (TwoColorComponentSwap G phi alpha beta root) y ∧ beta ∈ PresentColors G
        (TwoColorComponentSwap G phi alpha beta root) y)) (_ : ColoredVertexSetElementary G
        (ett.series.data.coloring q.castSucc) (TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc))) (_ : gamma ∈ MissingColors G (ett.series.data.coloring q.castSucc) v)
        (_ : delta ∉ TreeMissingColors (ett.series.data.coloring q.castSucc) (ett.series.data.tree
        q.succ.castSucc)),
    ∀ y ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), y ≠ v → gamma ∈
        PresentColors G sigma y ∧ delta ∈ PresentColors G sigma y := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqKind hqVertex
      hqGamma hqDelta hvStage hsigmaTerminal hgammaDelta swapBothPresent hTnElementary
      hgammaMissingPre hdeltaNotMissingPre y hy hyv
  have hgammaNotMissingPre : gamma ∉ MissingColors G
      (ett.series.data.coloring q.castSucc) y := by
    intro hgammaY
    have hdisjoint := hTnElementary hvStage hy hyv.symm
    exact (Finset.disjoint_left.mp hdisjoint) hgammaMissingPre hgammaY
  have hdeltaNotMissingPreY : delta ∉ MissingColors G
      (ett.series.data.coloring q.castSucc) y := by
    intro hdeltaY
    apply hdeltaNotMissingPre
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨y, hy, hdeltaY⟩
  generalize htarget : q.succ = target
  cases ett.series.certified target with
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
      actualGamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have hi : i = q := by
      apply Fin.ext
      simpa using (congrArg Fin.val htarget).symm
    subst i
    have hvChoice : choice.vertex = v :=
      Option.some.inj
        (currentVertex.symm.trans (by simpa [htarget] using hqVertex))
    have hgammaChoice : actualGamma = gamma :=
      Option.some.inj
        (currentGamma.symm.trans (by simpa [htarget] using hqGamma))
    have hdeltaChoice : choice.color = delta :=
      Option.some.inj
        (currentDelta.symm.trans (by simpa [htarget] using hqDelta))
    have hgammaSecondNot : actualGamma ∉
        MissingColors G secondStable y := by
      rw [secondStableRelation.2 y hy, choice.selectedStable.2 y hy]
      simpa only [hgammaChoice] using hgammaNotMissingPre
    have hdeltaSecondNot : choice.color ∉
        MissingColors G secondStable y := by
      rw [secondStableRelation.2 y hy, choice.selectedStable.2 y hy]
      simpa only [hdeltaChoice] using hdeltaNotMissingPreY
    have hgammaSecond : actualGamma ∈
        PresentColors G secondStable y := by
      simpa [MissingColors] using hgammaSecondNot
    have hdeltaSecond : choice.color ∈
        PresentColors G secondStable y := by
      simpa [MissingColors] using hdeltaSecondNot
    have hchoiceNe : actualGamma ≠ choice.color := by
      simpa only [hgammaChoice, hdeltaChoice] using hgammaDelta
    have hcurrentPresent := swapBothPresent secondStable actualGamma
      choice.color hchoiceNe (Sum.inl choice.vertex) y hgammaSecond
        hdeltaSecond
    have hgammaCurrent : actualGamma ∈ PresentColors G
        (ett.series.data.coloring q.succ) y := by
      rw [currentColoring]
      exact hcurrentPresent.1
    have hdeltaCurrent : choice.color ∈ PresentColors G
        (ett.series.data.coloring q.succ) y := by
      rw [currentColoring]
      exact hcurrentPresent.2
    have hgammaSigmaNot : actualGamma ∉ MissingColors G sigma y := by
      rw [hsigmaTerminal.2 y hy]
      simpa [MissingColors] using hgammaCurrent
    have hdeltaSigmaNot : choice.color ∉ MissingColors G sigma y := by
      rw [hsigmaTerminal.2 y hy]
      simpa [MissingColors] using hdeltaCurrent
    exact ⟨by
        simpa [hgammaChoice, MissingColors] using hgammaSigmaNot,
      by simpa [hdeltaChoice, MissingColors] using hdeltaSigmaNot⟩

private theorem helper_hxOutsideN_4382.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hvFinal : v ∈ TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v hvFinal
        sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : gamma ≠ delta) (_ : TwoColorIncidenceGraph G sigma gamma delta = TwoColorIncidenceGraph
        G rho1 gamma delta),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (_ : (
    ∀ (z : V ⊕ E) (_ : H.Adj (Sum.inl x) z), z = componentPath.getVert (componentPath.length - (1
        : ℕ)))) (_ : x ≠ v) (_ : (
    ∀ y ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc), y ≠ v → gamma ∈
        PresentColors G sigma y ∧ delta ∈ PresentColors G sigma y)), x ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hvFinal trace
      rho1 hgammaDelta hterminalGraph H x componentPath hendpointNeighbor hxNe
      hterminalPresentSigma hxN
  obtain ⟨hxGamma, hxDelta⟩ := hterminalPresentSigma x hxN hxNe
  obtain ⟨eGamma, heGammaIncident, heGammaColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] using hxGamma
  obtain ⟨eDelta, heDeltaIncident, heDeltaColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] using hxDelta
  have hedgeNe : eGamma ≠ eDelta := by
    intro heq
    subst eDelta
    exact hgammaDelta
      (Option.some.inj (heGammaColor.symm.trans heDeltaColor))
  have hgammaAdjSigma :
      (TwoColorIncidenceGraph G sigma gamma delta).Adj
        (Sum.inl x) (Sum.inr eGamma) := by
    simpa [TwoColorIncidenceGraph] using
      (show Incident G x eGamma ∧
          (sigma eGamma = some gamma ∨ sigma eGamma = some delta) from
        ⟨heGammaIncident, Or.inl heGammaColor⟩)
  have hdeltaAdjSigma :
      (TwoColorIncidenceGraph G sigma gamma delta).Adj
        (Sum.inl x) (Sum.inr eDelta) := by
    simpa [TwoColorIncidenceGraph] using
      (show Incident G x eDelta ∧
          (sigma eDelta = some gamma ∨ sigma eDelta = some delta) from
        ⟨heDeltaIncident, Or.inr heDeltaColor⟩)
  rw [hterminalGraph] at hgammaAdjSigma hdeltaAdjSigma
  have heq := (hendpointNeighbor _ hgammaAdjSigma).trans
    (hendpointNeighbor _ hdeltaAdjSigma).symm
  exact hedgeNe (Sum.inr.inj heq)

private theorem helper_hxOutsidePrime_4415.{u_1, u_2} :
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
    ∀ (TjPrime : TreeSequence G e0) (_ : (
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, MissingColors G rho1 x ∩ supportColors = ∅)) (_
        : gamma ∈ supportColors) (_ : delta ∈ supportColors) (_ : gamma ≠ delta),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (_ : (
    ∀ (z : V ⊕ E) (_ : H.Adj (Sum.inl x) z), z = componentPath.getVert (componentPath.length - (1
        : ℕ)))) (_ : x ≠ v), x ∉ TreeSequenceVertexSet TjPrime := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v gamma delta sigma this hvFinal trace p0
      indices0 rho1 supportColors TjPrime hcaseTwoPointwise hgammaSupport hdeltaSupport
      hgammaDelta H x componentPath hendpointNeighbor hxNe hxPrime
  have hxErase : x ∈ (TreeSequenceVertexSet TjPrime).erase v :=
    Finset.mem_erase.mpr ⟨hxNe, hxPrime⟩
  have hxEmpty := hcaseTwoPointwise x hxErase
  have hgammaNotMissing : gamma ∉ MissingColors G rho1 x := by
    intro hgammaMissing
    have hmember : gamma ∈ MissingColors G rho1 x ∩ supportColors :=
      Finset.mem_inter.mpr ⟨hgammaMissing, hgammaSupport⟩
    rw [hxEmpty] at hmember
    simp at hmember
  have hdeltaNotMissing : delta ∉ MissingColors G rho1 x := by
    intro hdeltaMissingX
    have hmember : delta ∈ MissingColors G rho1 x ∩ supportColors :=
      Finset.mem_inter.mpr ⟨hdeltaMissingX, hdeltaSupport⟩
    rw [hxEmpty] at hmember
    simp at hmember
  have hxGamma : gamma ∈ PresentColors G rho1 x := by
    simpa [MissingColors] using hgammaNotMissing
  have hxDelta : delta ∈ PresentColors G rho1 x := by
    simpa [MissingColors] using hdeltaNotMissing
  obtain ⟨eGamma, heGammaIncident, heGammaColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] using hxGamma
  obtain ⟨eDelta, heDeltaIncident, heDeltaColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] using hxDelta
  have hedgeNe : eGamma ≠ eDelta := by
    intro heq
    subst eDelta
    exact hgammaDelta
      (Option.some.inj (heGammaColor.symm.trans heDeltaColor))
  have hgammaAdj : H.Adj (Sum.inl x) (Sum.inr eGamma) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G x eGamma ∧
          (rho1 eGamma = some gamma ∨ rho1 eGamma = some delta) from
        ⟨heGammaIncident, Or.inl heGammaColor⟩)
  have hdeltaAdj : H.Adj (Sum.inl x) (Sum.inr eDelta) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G x eDelta ∧
          (rho1 eDelta = some gamma ∨ rho1 eDelta = some delta) from
        ⟨heDeltaIncident, Or.inr heDeltaColor⟩)
  have heq := (hendpointNeighbor _ hgammaAdj).trans
    (hendpointNeighbor _ hdeltaAdj).symm
  exact hedgeNe (Sum.inr.inj heq)

private theorem helper_hvNotPrevious_4521.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let _ : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by omega⟩ : Fin ett.rounds);
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal)
      (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : indices0 (Fin.last p0) = q),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)),
    v ∉ TreeSequenceVertexSet Tprevious := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot hjSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hqLast H x componentPath u exitPath Tprevious hjPositive hvPrevious
  let candidates : Finset (Fin (ett.rounds + 1)) :=
    Finset.univ.filter fun i =>
      v ∈ TreeSequenceVertexSet (ExtendedTashkinovLadderStage ett i)
  have hlast : Fin.last ett.rounds ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage ett
        (Fin.last ett.rounds) = T by
      unfold ExtendedTashkinovLadderStage
      exact Fin.lastCases_last]
    exact hvFinal
  have hfirst := hjSlot
  unfold ETTFirstAppearanceIndex at hfirst
  dsimp at hfirst
  have hminimumValue :
      (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val =
        jSlot.val := by
    change jSlot.val + 1 =
      (candidates.min' ⟨Fin.last ett.rounds, hlast⟩).val + 1 at hfirst
    omega
  let previousSlot : Fin ett.rounds :=
    ⟨jSlot.val - 1, by omega⟩
  have hpreviousIndex : previousSlot.succ = jSlot.castSucc := by
    apply Fin.ext
    simp [previousSlot]
    omega
  have hpreviousMember : previousSlot.castSucc ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show ExtendedTashkinovLadderStage ett previousSlot.castSucc =
        Tprevious by
      unfold ExtendedTashkinovLadderStage
      rw [Fin.lastCases_castSucc, hpreviousIndex]]
    exact hvPrevious
  have hminimum := Finset.min'_le candidates previousSlot.castSucc
    hpreviousMember
  have hminimumVal := Fin.le_iff_val_le_val.mp hminimum
  rw [hminimumValue] at hminimumVal
  dsimp [previousSlot] at hminimumVal
  omega

private theorem helper_hpreviousStrict_4568.{u_1, u_2} :
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
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (_ :
        (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = v)
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), v ∉ TreeSequenceVertexSet Tprevious)) (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), TreeSequenceInitialSegment Tprevious (ett.series.data.tree
        jSlot.succ.castSucc))) (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalAt hterminalPositionPositive hterminalPositionBound seed H x
      componentPath u exitPath Tprevious hvNotPrevious hpreviousTj hjPositive
  by_contra hnot
  have hpositionLe : terminalPosition.val ≤ Tprevious.length := by
    simpa [seed, TreeSequencePrefix] using Nat.le_of_not_gt hnot
  let previousPosition : Fin (Tprevious.length + 1) :=
    ⟨terminalPosition.val, by omega⟩
  have hcast : Fin.castLE
      (Nat.succ_le_succ (hpreviousTj hjPositive).1)
      previousPosition = terminalPosition := by
    apply Fin.ext
    rfl
  apply hvNotPrevious hjPositive
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  refine ⟨previousPosition, ?_⟩
  have hvertex := (hpreviousTj hjPositive).2.1 previousPosition
  rw [hcast] at hvertex
  exact hvertex.symm.trans hterminalAt

private theorem helper_branch_4596.{u_1, u_2} :
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
        seed (ett.series.data.tree jSlot.succ.castSucc) := by
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

private theorem helper_branch_4629.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
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
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length)) (i : Fin ett.rounds) (choice
        : MaximumDefectiveChoice G e0 (ett.series.data.tree i.succ.castSucc)
        (TashkinovStoredColors ett.series.data i.castSucc) (ett.series.data.coloring i.castSucc))
        (adjoined : TreeSequence G e0) (_ : TreeSequenceAdjoinEdge (ett.series.data.tree
        i.succ.castSucc) choice.edge adjoined) (_ : TashkinovClosure (ett.series.data.coloring
        i.succ) adjoined (ett.series.data.tree i.succ.succ)) (_ : jSlot.castSucc = i.succ),
        TashkinovAugmentationSequence (ett.series.data.coloring i.succ) seed (ett.series.data.tree
        jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj
      commonPrefix H x componentPath u exitPath Tprevious hpreviousStrict i choice adjoined
      adjoinedExactly closedExtension htarget
  have hi : i.succ = jSlot.castSucc := htarget.symm
  have hjPositive : 0 < jSlot.val := by
    have := congrArg Fin.val hi
    simp at this
    omega
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
    have hiCast : i.succ.castSucc = jSlot.castSucc.castSucc := by
      apply Fin.ext
      simpa using congrArg Fin.val hi
    have hprev : ett.series.data.tree i.succ.castSucc =
        Tprevious := by rw [hiCast]
    rw [hprev] at hlen
    rw [hlen]
    exact Nat.succ_le_of_lt (hpreviousStrict hjPositive)
  have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
    commonPrefix hadjoinedTj hseedTj hadjoinedLength
  simpa [hi] using
    (TashkinovAugmentationSequenceSuffix
      (ett.series.data.coloring jSlot.castSucc) adjoined seed _ hroute
        hadjoinedSeed hseedTj)

private theorem helper_branch_4664.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : jSlot.castSucc.succ = jSlot.succ.castSucc) (_ : TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc)),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), TreeSequenceInitialSegment Tprevious seed)) (i : Fin
        ett.rounds) (_ : TashkinovClosure (ett.series.data.coloring i.succ) (ett.series.data.tree
        i.succ.castSucc) (ett.series.data.tree i.succ.succ)) (_ : jSlot.castSucc = i.succ),
        TashkinovAugmentationSequence (ett.series.data.coloring i.succ) seed (ett.series.data.tree
        jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj
      H x componentPath u exitPath Tprevious hpreviousSeed i closedExtension htarget
  have hi : i.succ = jSlot.castSucc := htarget.symm
  have hjPositive : 0 < jSlot.val := by
    have := congrArg Fin.val hi
    simp at this
    omega
  have hroute : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) Tprevious
      (ett.series.data.tree jSlot.succ.castSucc) := by
    have h := closedExtension.1
    rw [hi, hjTreeIndex] at h
    simpa [Tprevious, hi] using h
  simpa [hi] using
    (TashkinovAugmentationSequenceSuffix
      (ett.series.data.coloring jSlot.castSucc) Tprevious seed _ hroute
        (hpreviousSeed hjPositive) hseedTj)

private theorem helper_branch_4686.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
        (sigma : PartialEdgeColoring E k),
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
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
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
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length)) (i : Fin ett.rounds)
        (available : RevisitingExtensionCertificate ett.series.data i.castSucc) (adjoined :
        TreeSequence G e0) (_ : TreeSequenceAdjoinEdge (ett.series.data.tree i.succ.castSucc)
        available.edge adjoined) (_ : TashkinovClosure (ett.series.data.coloring i.succ) adjoined
        (ett.series.data.tree i.succ.succ)) (_ : jSlot.castSucc = i.succ),
        TashkinovAugmentationSequence (ett.series.data.coloring i.succ) seed (ett.series.data.tree
        jSlot.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj
      commonPrefix H x componentPath u exitPath Tprevious hpreviousStrict i available adjoined
      adjoinedExactly closedExtension htarget
  have hi : i.succ = jSlot.castSucc := htarget.symm
  have hjPositive : 0 < jSlot.val := by
    have := congrArg Fin.val hi
    simp at this
    omega
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
    have hiCast : i.succ.castSucc = jSlot.castSucc.castSucc := by
      apply Fin.ext
      simpa using congrArg Fin.val hi
    have hprev : ett.series.data.tree i.succ.castSucc =
        Tprevious := by rw [hiCast]
    rw [hprev] at hlen
    rw [hlen]
    exact Nat.succ_le_of_lt (hpreviousStrict hjPositive)
  have hadjoinedSeed : TreeSequenceInitialSegment adjoined seed :=
    commonPrefix hadjoinedTj hseedTj hadjoinedLength
  simpa [hi] using
    (TashkinovAugmentationSequenceSuffix
      (ett.series.data.coloring jSlot.castSucc) adjoined seed _ hroute
        hadjoinedSeed hseedTj)

private theorem helper_hpreterminalGammaPresent_4778.{u_1, u_2} :
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
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (_ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 +
        (1 : ℕ)) → Fin ett.rounds) (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k) (_ : (
    ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc)) (_ : Function.Injective (Fin.cons (gamma0
        (0 : Fin (p0 + (1 : ℕ)))) delta0)),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (_ :
        (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (_ : (↑terminalPosition : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length),
    let supportColors : Finset (Fin k) := Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0) (_ : (
    ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.stored (indices0 a).succ = {gamma0 a, delta0 a}))
        (_ : (
    ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v, MissingColors G rho1 x ∩ supportColors = ∅)) (_
        : gamma0 (Fin.last p0) = gamma),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (_ : V ⊕ E) (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : u ∈
        (TreeSequenceVertexSet TjPrime).erase v) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (u : V) (beta : Fin k) (_ : u ∈
        TreeSequenceVertexSet TjPrime) (_ : u ∉ TreeSequenceVertexSet (ett.series.data.tree
        q.succ.castSucc)) (_ : beta ∈ MissingColors G rho1 u) (a : Fin p0), gamma0 a.castSucc ∈
        PresentColors G (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta delta)
        gamma beta (Sum.inl u)) u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvStage hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 hchain0
      hinjective0 rho1 terminalPosition hterminalPositionPositive hterminalPositionBound
      supportColors TjPrime hstored0 hcaseTwoPointwise hgammaLast H a x componentPath u exitPath
      huErase zPosition u' beta' huPrime' huOutside' hbeta' a
  let aSlot : Fin (p0 + 1) := a.castSucc
  have hgammaASupport : gamma0 aSlot ∈ supportColors := by
    simp only [supportColors, Finset.mem_biUnion, Finset.mem_univ,
      true_and]
    refine ⟨aSlot, ?_⟩
    rw [hstored0]
    simp
  have huNe : u' ≠ v := by
    intro huv
    apply huOutside'
    simpa [huv] using hvStage
  have huErase : u' ∈ (TreeSequenceVertexSet TjPrime).erase v :=
    Finset.mem_erase.mpr ⟨huNe, huPrime'⟩
  have hgammaANotMissing :
      gamma0 aSlot ∉ MissingColors G rho1 u' := by
    intro hmissing
    have hmember : gamma0 aSlot ∈
        MissingColors G rho1 u' ∩ supportColors :=
      Finset.mem_inter.mpr ⟨hmissing, hgammaASupport⟩
    rw [hcaseTwoPointwise u' huErase] at hmember
    simp at hmember
  have hgammaAPresent : gamma0 aSlot ∈ PresentColors G rho1 u' := by
    simpa [MissingColors] using hgammaANotMissing
  have hgammaANeBeta : gamma0 aSlot ≠ beta' := by
    intro heq
    have hbetaSupport' : beta' ∉ supportColors := by
      intro hbetaSupport'
      have hmember : beta' ∈ MissingColors G rho1 u' ∩ supportColors :=
        Finset.mem_inter.mpr ⟨hbeta', hbetaSupport'⟩
      rw [hcaseTwoPointwise u' huErase] at hmember
      simp at hmember
    exact hbetaSupport' (heq ▸ hgammaASupport)
  have hconsGamma (r : Fin (p0 + 1)) :
      (Fin.cons (gamma0 0) delta0 : Fin (p0 + 2) → Fin k)
          r.castSucc = gamma0 r := by
    refine Fin.cases ?_ (fun s => ?_) r
    · simp
    · rw [show (Fin.succ s).castSucc = s.castSucc.succ by
        apply Fin.ext
        rfl]
      rw [Fin.cons_succ]
      exact (hchain0 s).symm
  have hgammaANeGamma : gamma0 aSlot ≠ gamma := by
    intro heq
    have hvalues :
        (Fin.cons (gamma0 0) delta0 : Fin (p0 + 2) → Fin k)
            aSlot.castSucc =
          (Fin.cons (gamma0 0) delta0 : Fin (p0 + 2) → Fin k)
            (Fin.last p0).castSucc := by
      rw [hconsGamma, hconsGamma, hgammaLast]
      exact heq
    have hindices := hinjective0 hvalues
    have hvals := congrArg Fin.val hindices
    simp [aSlot] at hvals
    omega
  obtain ⟨f, huf, hcolor⟩ := by
    simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] using hgammaAPresent
  have htreeIncident : TreeIncidentEdge TjPrime f :=
    ⟨u', huPrime', huf⟩
  have houtsideColor :
      OutsideTreeColorSwap TjPrime rho1 beta' delta f =
        some (gamma0 aSlot) := by
    simp [OutsideTreeColorSwap, htreeIncident, hcolor]
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and]
  refine ⟨f, huf, ?_⟩
  by_cases hfComponent : Sum.inr f ∈
      TwoColorComponent G
        (OutsideTreeColorSwap TjPrime rho1 beta' delta)
        gamma beta' (Sum.inl u')
  · simp [TwoColorComponentSwap, hfComponent, houtsideColor,
      hgammaANeGamma, hgammaANeBeta, aSlot]
  · simp [TwoColorComponentSwap, hfComponent, houtsideColor, aSlot]

private theorem helper_hclaim45Package_4916.{u_1, u_2} :
    helperHclaim45Package4916Conditions.{u_1, u_2} := by
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
  by_cases hp0 : 0 < p0
  · obtain ⟨u0, huPrime0, huOutside0, exitPath0, hexitPath0,
        hexitLength0, hexitSupport0, hexitIntersection0,
        hexitBoundary0, huNotFN0, hforBeta0⟩ :=
      hpositiveClaim45 hp0
    obtain ⟨beta0, hbeta0⟩ :=
      MissingColorsNonemptyOfMaximumDegree G rho1 hdegree u0
    have huTerminal0 : u0 ≠ v := by
      intro huv
      apply huOutside0
      simpa [huv] using hvStage
    have huErase0 : u0 ∈ (TreeSequenceVertexSet TjPrime).erase v :=
      Finset.mem_erase.mpr ⟨huTerminal0, huPrime0⟩
    have hbetaSupport0 : beta0 ∉ supportColors := by
      intro hbetaIn
      have hmember : beta0 ∈
          MissingColors G rho1 u0 ∩ supportColors :=
        Finset.mem_inter.mpr ⟨hbeta0, hbetaIn⟩
      rw [hcaseTwoPointwise u0 huErase0] at hmember
      simp at hmember
    obtain ⟨z0, hz0, zPosition0, hzPosition0, hzAfter0, hzChoice0,
        hzBefore0, hzEdges0, rho3, hrho3Proper, hrho3One, hd1,
        hd2Missing, hd2Edges, hdeltaZ, hd2z, hd3⟩ :=
      hforBeta0 beta0 hbeta0
    exact ⟨u0, huPrime0, huOutside0, exitPath0, hexitPath0,
      hexitLength0, hexitSupport0, hexitIntersection0,
      hexitBoundary0, huNotFN0, beta0, hbeta0, hbetaSupport0,
      z0, hz0, zPosition0, hzPosition0, hzAfter0, hzChoice0,
      hzBefore0, hzEdges0, rho3, hrho3Proper, hrho3One, hd1,
      hd2Missing, hd2Edges, hdeltaZ, hd2z, hd3⟩
  · have hp0Zero : p0 = 0 := Nat.eq_zero_of_not_pos hp0
    let rho0 := OutsideTreeColorSwap TjPrime rho1 beta delta
    let rho3 := TwoColorComponentSwap G rho0 gamma beta (Sum.inl u)
    have hbetaDelta0 : beta ≠ delta := by
      intro heq
      exact hbetaSupport (heq ▸ hdeltaSupport)
    have hbetaGamma0 : beta ≠ gamma := by
      intro heq
      exact hbetaSupport (heq ▸ hgammaSupport)
    have hsingleton := ExtensionBaseClaim45Singleton
      (ett.series.data.tree q.succ.castSucc)
      (ett.series.data.tree jSlot.succ.castSucc) seed TjPrime
      (ett.series.data.coloring jSlot.castSucc) rho1
      (TashkinovStoredColors ett.series.data jSlot.castSucc)
      supportColors gammaFirst gamma delta beta v u x z
      componentPath exitPath zPosition (hgammaFirstZero hp0Zero)
      hrho1Proper hrho1One hTjQ hseedTj hseedPrime hseedTerminal
      hterminalJ hterminalSeed hclosure hprimeElementary hgammaDelta
      hbetaGamma0 hbetaDelta0 hbeta hdeltaMissing hcomponentPath
      (by simpa [C] using hcomponentSupport) hxOutside huPrime huOutside
      hexitPath hexitLength hexitSupport hexitIntersection hexitBoundary
      hb1Tj hb2Missing.1 haugmentation hb2EdgesFromSeed hdeltaPhiJ
      hz hzPosition hzAfter hzChoice hzBefore hzEdges
    change IsProperEdgeColoring G rho3 ∧
        IsOneEdgeUncolored rho3 e0 ∧
        StableColoringBeforeVertex
          (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
          (TashkinovStoredColors ett.series.data jSlot.castSucc)
          (ett.series.data.coloring jSlot.castSucc) rho3 ∧
        ((∀ y : V,
          y ∈ (((TreeVerticesBefore
              (ett.series.data.tree jSlot.succ.castSucc) z hz ∪ {z}) ∪
              (TreeVerticesBefore TjPrime u huPrime ∪
                {u})).erase u).erase z →
          MissingColors G rho3 y = MissingColors G rho1 y) ∧
          (∀ f : E,
            ((∃ a : Fin
                  (ett.series.data.tree jSlot.succ.castSucc).length,
                seed.length ≤ a.val ∧ a.val < zPosition.val ∧
                  (ett.series.data.tree jSlot.succ.castSucc).edge a =
                    f) ∨
              (∃ (a : Fin TjPrime.length)
                (uPosition : Fin (TjPrime.length + 1)),
                TjPrime.vertex uPosition = u ∧
                  a.val < uPosition.val ∧ TjPrime.edge a = f)) →
            rho3 f = rho1 f) ∧
          (beta ∈ MissingColors G rho1 z →
            delta ∈ MissingColors G rho3 z) ∧
          (z ∈ TreeVerticesBefore TjPrime u huPrime →
            MissingColors G rho3 z = MissingColors G rho1 z)) ∧
        gammaFirst ∈ MissingColors G rho3 u at hsingleton
    rcases hsingleton with
      ⟨hrho3Proper0, hrho3One0, hd10, hE20, hd30⟩
    rcases hE20 with
      ⟨hd2Missing0, hd2Edges0, hdeltaZ0, hd2z0⟩
    exact ⟨u, huPrime, huOutside, exitPath, hexitPath, hexitLength,
      hexitSupport, hexitIntersection, hexitBoundary, huNotFN,
      beta, hbeta, hbetaSupport, z, hz, zPosition, hzPosition,
      hzAfter, hzChoice, hzBefore, hzEdges, rho3, hrho3Proper0,
      hrho3One0, hd10, hd2Missing0, hd2Edges0, hdeltaZ0, hd2z0,
      hd30⟩

private theorem helper_hUsegmentVertexBefore_5198.{u_1, u_2} :
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
        TreeSequenceVertexSet A), y ∈ TreeVerticesBefore TjPrime u0 huPrime0 := by
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

private theorem helper_transportUStep_5236.{u_1, u_2} :
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
    ∀ (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (trace :
        ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin
        ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
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
        (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (rho3 :
        PartialEdgeColoring E k) (_ : (
    ∀ (f : E) (_ : ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) ∧ (↑a :
        ℕ) < (↑zPosition0 : ℕ) ∧ (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u0 ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f)), rho3 f = rho1 f))
        (uPosition : Fin (TjPrime.length + (1 : ℕ))) (_ : TjPrime.vertex uPosition = u0)
        (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤
        TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    ∀ (_ : TreeSequenceInitialSegment U TjPrime) (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A U) (_ : A.length < U.length)
        {y : V} (_ : y ∈ TreeSequenceVertexSet A), y ∈ TreeVerticesBefore TjPrime u0 huPrime0)) (_
        : (
    ∀ y ∈ TreeVerticesBefore TjPrime u0 huPrime0, MissingColors G rho3 y = MissingColors G rho1
        y)) {A B : TreeSequence G e0} (_ : TashkinovAugmentation rho1 A B) (_ :
        TreeSequenceInitialSegment B U), TashkinovAugmentation rho3 A B := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot segmentTrans trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H x
      componentPath u exitPath zPosition u0 huPrime0 exitPath0 zPosition0 rho3 hd2Edges uPosition
      huPosition huPositionPositive huPositionBound U hUPrime hUsegmentVertexBefore
      hbeforePrimeMissing A B hstep hBU
  rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
  have hAU : TreeSequenceInitialSegment A U := segmentTrans hAB hBU
  have hAlen : A.length < U.length :=
    lt_of_lt_of_le (by omega) hBU.1
  have hcMissingRho : c ∈ TreeMissingColors rho3 A := by
    unfold TreeMissingColors at hcMissing
    obtain ⟨y, hyA, hcy⟩ := Finset.mem_biUnion.mp hcMissing
    refine Finset.mem_biUnion.mpr ⟨y, hyA, ?_⟩
    rw [hbeforePrimeMissing y (hUsegmentVertexBefore hAU hAlen hyA)]
    exact hcy
  let added : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
  let addedU : Fin U.length := Fin.castLE hBU.1 added
  let addedPrime : Fin TjPrime.length := Fin.castLE hUPrime.1 addedU
  have haddedPosition : addedPrime.val < uPosition.val := by
    change A.length < uPosition.val
    have hUlen : U.length = uPosition.val := by
      simp [U, TreeSequencePrefix]
    omega
  have haddedIdentity : TjPrime.edge addedPrime = B.edge added :=
    (hUPrime.2.2 addedU).trans (hBU.2.2 added)
  have haddedFixed : rho3 (B.edge added) = rho1 (B.edge added) := by
    apply hd2Edges (B.edge added)
    exact Or.inr ⟨addedPrime, uPosition, huPosition,
      haddedPosition, haddedIdentity⟩
  refine ⟨hlen, hAB, c, haddedFixed.trans hcolor, hcMissingRho⟩

private theorem helper_hTjC_5298.{u_1, u_2} :
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
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (_ :
        seed.length = (ett.series.data.tree jSlot.succ.castSucc).length) (C : TreeSequence G e0)
        (_ : TreeSequenceInitialSegment seed C), TreeSequenceVertexSet (ett.series.data.tree
        jSlot.succ.castSucc) ⊆ TreeSequenceVertexSet C := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hseedTj hseedFull C hseedC y hy
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and] at hy ⊢
  obtain ⟨i, rfl⟩ := hy
  let iSeed : Fin (seed.length + 1) := ⟨i.val, by
    rw [hseedFull]
    exact i.isLt⟩
  refine ⟨Fin.castLE (Nat.succ_le_succ hseedC.1) iSeed, ?_⟩
  have hcast : Fin.castLE (Nat.succ_le_succ hseedTj.1) iSeed = i := by
    apply Fin.ext
    rfl
  exact (hseedC.2.1 iSeed).trans
    ((hseedTj.2.1 iSeed).symm.trans
      (congrArg
        (ett.series.data.tree jSlot.succ.castSucc).vertex hcast))

private theorem helper_transportSeedStep_5350.{u_1, u_2} :
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
    ∀ (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (trace :
        ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin
        ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A seed) (_ : A.length < seed.length)
        {x : V} (_ : x ∈ TreeSequenceVertexSet A), x ∈ TreeVerticesBefore T v hvFinal)) (TjPrime :
        TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V) (_ : (TwoColorIncidenceGraph G rho1 gamma
        delta).Walk (Sum.inl x) (Sum.inl u0)) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (rho3 : PartialEdgeColoring E k) (_ :
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho3) (_ : Fin (TjPrime.length + (1 : ℕ))) (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A seed) (_ : A.length < seed.length)
        {y : V} (_ : y ∈ TreeSequenceVertexSet A), y ∈ TreeVerticesBefore (ett.series.data.tree
        jSlot.succ.castSucc) v hterminalJ)) {A B : TreeSequence G e0} (_ : TashkinovAugmentation
        (ett.series.data.coloring jSlot.castSucc) A B) (_ : TreeSequenceInitialSegment B seed),
        TashkinovAugmentation rho3 A B := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot segmentTrans trace hterminalJ p0 indices0 gamma0
      delta0 rho1 terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj
      segmentVertexBefore TjPrime H x componentPath u exitPath zPosition u0 exitPath0 zPosition0
      rho3 hd1 uPosition segmentVertexBefore A B hstep hBseed
  rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
  have hAseed : TreeSequenceInitialSegment A seed :=
    segmentTrans hAB hBseed
  have hAlen : A.length < seed.length :=
    lt_of_lt_of_le (by omega) hBseed.1
  have hcMissingRho : c ∈ TreeMissingColors rho3 A := by
    unfold TreeMissingColors at hcMissing
    obtain ⟨y, hyA, hcy⟩ := Finset.mem_biUnion.mp hcMissing
    refine Finset.mem_biUnion.mpr ⟨y, hyA, ?_⟩
    rw [hd1.2 y (segmentVertexBefore hAseed hAlen hyA)]
    exact hcy
  let added : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
  obtain ⟨attach, hattach⟩ := B.attaches added
  let oldPosition : Fin (B.length + 1) :=
    Fin.castLT attach
      (Nat.lt_trans attach.isLt (Nat.succ_lt_succ added.isLt))
  have holdValue : oldPosition.val < A.length + 1 := by
    dsimp [oldPosition, added]
    omega
  let oldA : Fin (A.length + 1) := ⟨oldPosition.val, holdValue⟩
  have holdEq : B.vertex oldPosition = A.vertex oldA := by
    have hcast : Fin.castLE (Nat.succ_le_succ hAB.1) oldA =
        oldPosition := by
      apply Fin.ext
      rfl
    rw [← hcast]
    exact hAB.2.1 oldA
  have holdBefore : B.vertex oldPosition ∈ TreeVerticesBefore
      (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
    rw [holdEq]
    exact segmentVertexBefore hAseed hAlen
      (by simp [TreeSequenceVertexSet])
  have holdIncident : Incident G (B.vertex oldPosition)
      (B.edge added) := by
    unfold Incident
    rw [hattach]
    simp [oldPosition]
  have haddedFixed : rho3 (B.edge added) =
      ett.series.data.coloring jSlot.castSucc (B.edge added) := by
    apply hd1.1 (B.edge added)
      ⟨B.vertex oldPosition, holdBefore, holdIncident⟩
    refine ⟨c, ?_, hcolor⟩
    apply Finset.mem_union_left
    unfold TreeMissingColors at hcMissing
    obtain ⟨y, hyA, hcy⟩ := Finset.mem_biUnion.mp hcMissing
    exact Finset.mem_biUnion.mpr
      ⟨y, segmentVertexBefore hAseed hAlen hyA, hcy⟩
  exact ⟨hlen, hAB, c, haddedFixed.trans hcolor, hcMissingRho⟩

private theorem helper_branch_5420.{u_1, u_2} :
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
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A seed) (_ : A.length < seed.length)
        {x : V} (_ : x ∈ TreeSequenceVertexSet A), x ∈ TreeVerticesBefore T v hvFinal)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length)) (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), TreeSequenceInitialSegment Tprevious seed)) (rho3 :
        PartialEdgeColoring E k) (_ : StableColoringBeforeVertex (ett.series.data.tree
        jSlot.succ.castSucc) v hterminalJ (TashkinovStoredColors ett.series.data jSlot.castSucc)
        (ett.series.data.coloring jSlot.castSucc) rho3) (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A seed) (_ : A.length < seed.length)
        {y : V} (_ : y ∈ TreeSequenceVertexSet A), y ∈ TreeVerticesBefore (ett.series.data.tree
        jSlot.succ.castSucc) v hterminalJ)) (_ : (0 : ℕ) < (↑jSlot : ℕ)) (f : E) (_ :
        TreeIncidentEdge Tprevious f) (_ : (
    ∃ c ∈ TreeMissingColors (ett.series.data.coloring jSlot.castSucc) Tprevious ∪
        TashkinovStoredColors ett.series.data jSlot.castSucc, ett.series.data.coloring
        jSlot.castSucc f = some c)), rho3 f = ett.series.data.coloring jSlot.castSucc f := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hterminalJ terminalPosition hterminalPositionPositive
      hterminalPositionBound seed segmentVertexBefore Tprevious hpreviousStrict hpreviousSeed
      rho3 hd1 segmentVertexBefore hjPositive f hfIncident hfControlled
  obtain ⟨y, hyPrevious, hyf⟩ := hfIncident
  apply hd1.1 f
    ⟨y, segmentVertexBefore (hpreviousSeed hjPositive)
      (hpreviousStrict hjPositive) hyPrevious, hyf⟩
  obtain ⟨c, hcControlled, hfc⟩ := hfControlled
  refine ⟨c, ?_, hfc⟩
  rcases Finset.mem_union.mp hcControlled with hcMissing | hcStored
  · apply Finset.mem_union_left
    unfold TreeMissingColors at hcMissing
    obtain ⟨y, hy, hcy⟩ := Finset.mem_biUnion.mp hcMissing
    exact Finset.mem_biUnion.mpr
      ⟨y, segmentVertexBefore (hpreviousSeed hjPositive)
        (hpreviousStrict hjPositive) hy, hcy⟩
  · exact Finset.mem_union_right _ hcStored

private theorem helper_branch_5475.{u_1, u_2} :
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
    ∀ (_ : jSlot.castSucc.succ = jSlot.succ.castSucc) (_ : TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc)) (_ : (
    ∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed), TashkinovAugmentationSequence rho1 S seed)) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length)) (rho3 : PartialEdgeColoring E
        k) (_ : (
    ∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed), TashkinovAugmentationSequence rho3 S seed)) (_ : (0 : ℕ) <
        (↑jSlot : ℕ)) (i : Fin ett.rounds) (choice : MaximumDefectiveChoice G e0
        (ett.series.data.tree i.succ.castSucc) (TashkinovStoredColors ett.series.data i.castSucc)
        (ett.series.data.coloring i.castSucc)) (_ : ett.series.data.connectingEdges i.succ =
        { choice.edge }) (_ : ett.series.data.kind i.succ = some TashkinovExtensionKind.SE)
        (adjoined : TreeSequence G e0) (_ : TreeSequenceAdjoinEdge (ett.series.data.tree
        i.succ.castSucc) choice.edge adjoined) (_ : TashkinovClosure (ett.series.data.coloring
        i.succ) adjoined (ett.series.data.tree i.succ.succ)) (_ : jSlot.castSucc = i.succ),
        ett.series.data.kind i.succ = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho3 Tprevious seed ∨ (ett.series.data.kind i.succ = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind i.succ = some TashkinovExtensionKind.RE)
        ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges i.succ = { f } ∧
        TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧ TashkinovAugmentationSequence rho3
        adjoinSeed seed := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace rho1 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hjTreeIndex hseedTj transportSeedRoute commonPrefix Tprevious
      hpreviousStrict rho3 transportSeedRoute hjPositive i choice currentEdges currentKind
      adjoined adjoinedExactly closedExtension htarget
  have hi : i.succ = jSlot.castSucc := htarget.symm
  have hrouteFull : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) adjoined
      (ett.series.data.tree jSlot.succ.castSucc) := by
    have h := closedExtension.1
    rw [hi, hjTreeIndex] at h
    exact h
  have hadjoinedTj :=
    TashkinovAugmentationSequenceInitialSegment _ _ _ hrouteFull
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
  have hadjoinedSeed :=
    commonPrefix hadjoinedTj hseedTj hadjoinedLength
  have hroute := TashkinovAugmentationSequenceRestrict _
    adjoined seed _ hrouteFull hadjoinedSeed hseedTj
  right
  refine ⟨Or.inl (by simpa [htarget] using currentKind),
    choice.edge, adjoined, by simpa [htarget] using currentEdges,
    ?_, transportSeedRoute adjoined hroute⟩
  rcases adjoinedExactly with ⟨hlen, hsegment, hedge⟩
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

private theorem helper_branch_5528.{u_1, u_2} :
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
    ∀ (_ : jSlot.castSucc.succ = jSlot.succ.castSucc) (_ : TreeSequenceInitialSegment seed
        (ett.series.data.tree jSlot.succ.castSucc)) (_ : (
    ∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed), TashkinovAugmentationSequence rho1 S seed)) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ)), Tprevious.length < seed.length)) (rho3 : PartialEdgeColoring E
        k) (_ : (
    ∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed), TashkinovAugmentationSequence rho3 S seed)) (_ : (0 : ℕ) <
        (↑jSlot : ℕ)) (i : Fin ett.rounds) (available : RevisitingExtensionCertificate
        ett.series.data i.castSucc) (_ : ett.series.data.connectingEdges i.succ =
        { available.edge }) (_ : ett.series.data.kind i.succ = some TashkinovExtensionKind.RE)
        (adjoined : TreeSequence G e0) (_ : TreeSequenceAdjoinEdge (ett.series.data.tree
        i.succ.castSucc) available.edge adjoined) (_ : TashkinovClosure (ett.series.data.coloring
        i.succ) adjoined (ett.series.data.tree i.succ.succ)) (_ : jSlot.castSucc = i.succ),
        ett.series.data.kind i.succ = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence rho3 Tprevious seed ∨ (ett.series.data.kind i.succ = some
        TashkinovExtensionKind.SE ∨ ett.series.data.kind i.succ = some TashkinovExtensionKind.RE)
        ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges i.succ = { f } ∧
        TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧ TashkinovAugmentationSequence rho3
        adjoinSeed seed := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace rho1 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hjTreeIndex hseedTj transportSeedRoute commonPrefix Tprevious
      hpreviousStrict rho3 transportSeedRoute hjPositive i available currentEdges currentKind
      adjoined adjoinedExactly closedExtension htarget
  have hi : i.succ = jSlot.castSucc := htarget.symm
  have hrouteFull : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) adjoined
      (ett.series.data.tree jSlot.succ.castSucc) := by
    have h := closedExtension.1
    rw [hi, hjTreeIndex] at h
    exact h
  have hadjoinedTj :=
    TashkinovAugmentationSequenceInitialSegment _ _ _ hrouteFull
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
  have hadjoinedSeed :=
    commonPrefix hadjoinedTj hseedTj hadjoinedLength
  have hroute := TashkinovAugmentationSequenceRestrict _
    adjoined seed _ hrouteFull hadjoinedSeed hseedTj
  right
  refine ⟨Or.inr (by simpa [htarget] using currentKind),
    available.edge, adjoined,
    by simpa [htarget] using currentEdges, ?_,
    transportSeedRoute adjoined hroute⟩
  rcases adjoinedExactly with ⟨hlen, hsegment, hedge⟩
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

private theorem helper_hbound_5582.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (v :
        V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (trace :
        ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ))
        → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (TjPrime :
        TreeSequence G e0) (_ : indices0 (Fin.last p0) = q),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let _ : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V) (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0)) (_ : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (rho3 : PartialEdgeColoring
        E k) (_ : IsProperEdgeColoring G rho3) (_ : IsOneEdgeUncolored rho3 e0) (uPosition : Fin
        (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
        (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    ∀ (C : TreeSequence G e0) (_ : TashkinovClosure rho3 U C) (_ : TashkinovAugmentationSequence
        rho3 seed C) (_ : (0 : ℕ) < (↑jSlot : ℕ)) (_ : StableColoring Tprevious
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho3) (_ : (ett.series.data.kind jSlot.castSucc = some
        TashkinovExtensionKind.PE ∧ TashkinovAugmentationSequence rho3 Tprevious seed ∨
        (ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.SE ∨
        ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.RE) ∧
    ∃ (f : E) (adjoinSeed : TreeSequence G e0), ett.series.data.connectingEdges jSlot.castSucc =
        { f } ∧ TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧ TashkinovAugmentationSequence rho3
        adjoinSeed seed)), (TreeSequenceVertexSet C).card ≤ (TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)).card := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot hjSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime
      hqLast H C x componentPath u exitPath Tprevious zPosition u0 exitPath0 zPosition0 rho3
      hrho3Proper hrho3One uPosition huPositionPositive huPositionBound U C hclosureUC
      hrouteSeedC hjPositive hstablePrevious hseedBuildRho
  have hMP' := hMP
  unfold MaximumProperty at hMP'
  have hstage := hMP'.2 jSlot.val hjPositive jSlot.isLt
  dsimp only at hstage
  have hidx : (⟨jSlot.val, by omega⟩ : Fin (ett.rounds + 1)) =
      jSlot.castSucc := by apply Fin.ext; rfl
  have hnextIdx :
      (⟨jSlot.val + 1, by omega⟩ : Fin (ett.rounds + 2)) =
        jSlot.succ.castSucc := by apply Fin.ext; rfl
  rw [hidx, hnextIdx] at hstage
  rcases hseedBuildRho with hparallel | hserial
  · exact hstage rho3 Tprevious C hrho3Proper hrho3One
      hstablePrevious (Or.inl ⟨hparallel.1, rfl⟩)
      ⟨Relation.ReflTransGen.trans hparallel.2 hrouteSeedC,
        hclosureUC.2⟩
  · rcases hserial with
      ⟨hkind, f, adjoinSeed, hconnecting, hadjoin, hroute⟩
    exact hstage rho3 adjoinSeed C hrho3Proper hrho3One
      hstablePrevious
      (Or.inr ⟨hkind, f, hconnecting,
        by simpa [Tprevious] using hadjoin⟩)
      ⟨Relation.ReflTransGen.trans hroute hrouteSeedC,
        hclosureUC.2⟩

private theorem helper_branch_5609.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (v :
        V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k),
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
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (_ : (
    ∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed), TashkinovAugmentationSequence rho1 S seed)) (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A C) (_ :
        TreeSequenceInitialSegment B C) (_ : A.length ≤ B.length), TreeSequenceInitialSegment A
        B)) (TjPrime : TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let _ : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (_ : V ⊕ E) (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V) (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0)) (_ : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (rho3 : PartialEdgeColoring
        E k) (_ : IsProperEdgeColoring G rho3) (_ : IsOneEdgeUncolored rho3 e0) (_ : Fin
        (TjPrime.length + (1 : ℕ))) (C : TreeSequence G e0) (_ : TashkinovAugmentationSequence
        rho3 seed C) (_ : TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ⊂
        TreeSequenceVertexSet C) (_ : (
    ∀ (S : TreeSequence G e0) (_ : TashkinovAugmentationSequence (ett.series.data.coloring
        jSlot.castSucc) S seed), TashkinovAugmentationSequence rho3 S seed)) (_ : ¬(0 : ℕ) <
        (↑jSlot : ℕ)), False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj
      transportSeedRoute commonPrefix TjPrime H C a x componentPath u exitPath zPosition u0
      exitPath0 zPosition0 rho3 hrho3Proper hrho3One uPosition C hrouteSeedC hTjStrictC
      transportSeedRoute hjPositive
  have hjZero : jSlot.val = 0 := Nat.eq_zero_of_not_pos hjPositive
  have hjIndex : jSlot.castSucc =
      (0 : Fin (ett.rounds + 1)) := by
    apply Fin.ext
    exact hjZero
  cases hcert : ett.series.certified
      (0 : Fin (ett.rounds + 1)) with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
      have htreeOne : ett.series.data.tree 1 =
          ett.series.data.tree jSlot.succ.castSucc := by
        congr 1
        apply Fin.ext
        simp [hjZero]
      have hinitialTj : TreeSequenceInitialSegment
          (ett.series.data.tree 0)
          (ett.series.data.tree jSlot.succ.castSucc) := by
        have h := TashkinovAugmentationSequenceInitialSegment _ _ _
          initialClosure.1
        simpa [htreeOne] using h
      have hinitialSeed : TreeSequenceInitialSegment
          (ett.series.data.tree 0) seed := by
        apply commonPrefix hinitialTj hseedTj
        rw [seedLength]
        exact seed.positive
      have hroutePhiSeed : TashkinovAugmentationSequence
          (ett.series.data.coloring jSlot.castSucc)
          (ett.series.data.tree 0) seed := by
        have hrestricted := TashkinovAugmentationSequenceRestrict
          (ett.series.data.coloring 0) (ett.series.data.tree 0) seed
          (ett.series.data.tree jSlot.succ.castSucc)
          (by simpa [htreeOne] using initialClosure.1)
          hinitialSeed hseedTj
        simpa [hjIndex] using hrestricted
      have hrouteBaseC : TashkinovAugmentationSequence rho3
          (ett.series.data.tree 0) C :=
        Relation.ReflTransGen.trans
          (transportSeedRoute (ett.series.data.tree 0) hroutePhiSeed)
          hrouteSeedC
      have htripleRho : KTriple G k e0 rho3 :=
        ⟨triple.1, triple.2.1, triple.2.2.1,
          hrho3Proper, hrho3One⟩
      have hinitialTree : TashkinovTree G e0 rho3
          (ett.series.data.tree 0) := by
        intro a ha
        rw [seedLength] at a
        omega
      have hCTree : TashkinovTree G e0 rho3 C :=
        TashkinovAugmentationSequencePreservesTashkinovTree G e0 rho3
          (ett.series.data.tree 0) C hinitialTree hrouteBaseC
      have hk : ChromaticIndex G - 1 = k := by
        have hchromatic := triple.2.1
        omega
      have hCOrder : (TreeSequenceVertexSet C).card ≤
          TashkinovOrder G := by
        unfold TashkinovOrder
        dsimp only
        apply Finset.le_max'
        apply Finset.mem_insert_of_mem
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.lt_succ_of_le (Finset.card_le_univ _), ?_⟩
        rw [hk]
        exact ⟨e0, rho3, C, htripleRho, hCTree, rfl⟩
      have hTjOrder :
          (TreeSequenceVertexSet
            (ett.series.data.tree jSlot.succ.castSucc)).card =
            TashkinovOrder G := by
        rw [← htreeOne]
        exact hMP.1
      have hbound : (TreeSequenceVertexSet C).card ≤
          (TreeSequenceVertexSet
            (ett.series.data.tree jSlot.succ.castSucc)).card := by
        rw [hTjOrder]
        exact hCOrder
      exact (Nat.not_lt_of_ge hbound)
        (Finset.card_lt_card hTjStrictC)

private theorem helper_branch_5782.{u_1, u_2} :
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
        (ett.series.data.coloring i.succ) adjoinSeed seed := by
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

private theorem helper_branch_5839.{u_1, u_2} :
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
        (ett.series.data.coloring i.succ) adjoinSeed seed := by
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

private theorem helper_branch_5861.{u_1, u_2} :
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
        (ett.series.data.coloring i.succ) adjoinSeed seed := by
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

private theorem helper_hUsegmentVertexBefore_6032.{u_1, u_2} :
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
        TreeSequenceVertexSet A), y ∈ TreeVerticesBefore TjPrime u0 huPrime0 := by
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

private theorem helper_transportUStep_6071.{u_1, u_2} :
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
    ∀ (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (trace :
        ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin
        ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
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
        (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (rho3 :
        PartialEdgeColoring E k) (_ : (
    ∀ (f : E) (_ : ((
    ∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length), seed.length ≤ (↑a : ℕ) ∧ (↑a :
        ℕ) < (↑zPosition0 : ℕ) ∧ (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u0 ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f)), rho3 f = rho1 f))
        (uPosition : Fin (TjPrime.length + (1 : ℕ))) (_ : TjPrime.vertex uPosition = u0)
        (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ)) (huPositionBound : (↑uPosition : ℕ) ≤
        TjPrime.length),
    let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
        huPositionBound;
    ∀ (_ : TreeSequenceInitialSegment U TjPrime) (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A U) (_ : A.length < U.length)
        {y : V} (_ : y ∈ TreeSequenceVertexSet A), y ∈ TreeVerticesBefore TjPrime u0 huPrime0)) (_
        : (
    ∀ y ∈ TreeVerticesBefore TjPrime u0 huPrime0, MissingColors G rho3 y = MissingColors G rho1
        y)) {A B : TreeSequence G e0} (_ : TashkinovAugmentation rho1 A B) (_ :
        TreeSequenceInitialSegment B U), TashkinovAugmentation rho3 A B := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot segmentTrans trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H x
      componentPath u exitPath zPosition u0 huPrime0 exitPath0 zPosition0 rho3 hd2Edges uPosition
      huPosition huPositionPositive huPositionBound U hUPrime hUsegmentVertexBefore
      hbeforePrimeMissing A B hstep hBU
  rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
  have hAU : TreeSequenceInitialSegment A U := segmentTrans hAB hBU
  have hAlen : A.length < U.length :=
    lt_of_lt_of_le (by omega) hBU.1
  have hcMissingRho : c ∈ TreeMissingColors rho3 A := by
    unfold TreeMissingColors at hcMissing ⊢
    obtain ⟨y, hyA, hcy⟩ := Finset.mem_biUnion.mp hcMissing
    refine Finset.mem_biUnion.mpr ⟨y, hyA, ?_⟩
    rw [hbeforePrimeMissing y (hUsegmentVertexBefore hAU hAlen hyA)]
    exact hcy
  let added : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
  let addedU : Fin U.length := Fin.castLE hBU.1 added
  let addedPrime : Fin TjPrime.length := Fin.castLE hUPrime.1 addedU
  have haddedPosition : addedPrime.val < uPosition.val := by
    change A.length < uPosition.val
    have hUlen : U.length = uPosition.val := by
      simp [U, TreeSequencePrefix]
    omega
  have haddedIdentity : TjPrime.edge addedPrime = B.edge added :=
    (hUPrime.2.2 addedU).trans (hBU.2.2 added)
  have haddedFixed : rho3 (B.edge added) = rho1 (B.edge added) := by
    apply hd2Edges (B.edge added)
    exact Or.inr ⟨addedPrime, uPosition, huPosition,
      haddedPosition, haddedIdentity⟩
  exact ⟨hlen, hAB, c, haddedFixed.trans hcolor, hcMissingRho⟩

private theorem helper_equalPrefixes_6220.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        {A B D : TreeSequence G e0}, TreeSequenceInitialSegment A D → TreeSequenceInitialSegment B
        D → A.length = B.length → A = B := by
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

private theorem helper_transportSeedStep_6612.{u_1, u_2} :
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
    ∀ (_ : (
    ∀ {A B C : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B) (_ :
        TreeSequenceInitialSegment B C), TreeSequenceInitialSegment A C)) (trace :
        ExtensionBaseRestorationTrace ett v hvFinal sigma) (hterminalJ : v ∈ TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)) (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin
        ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A seed) (_ : A.length < seed.length)
        {x : V} (_ : x ∈ TreeSequenceVertexSet A), x ∈ TreeVerticesBefore T v hvFinal)) (TjPrime :
        TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V) (_ : (TwoColorIncidenceGraph G rho1 gamma
        delta).Walk (Sum.inl x) (Sum.inl u0)) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (rho3 : PartialEdgeColoring E k) (_ :
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc) (ett.series.data.coloring
        jSlot.castSucc) rho3) (_ : Fin (TjPrime.length + (1 : ℕ))) (_ : (
    ∀ {A : TreeSequence G e0} (_ : TreeSequenceInitialSegment A seed) (_ : A.length < seed.length)
        {y : V} (_ : y ∈ TreeSequenceVertexSet A), y ∈ TreeVerticesBefore (ett.series.data.tree
        jSlot.succ.castSucc) v hterminalJ)) {A B : TreeSequence G e0} (_ : TashkinovAugmentation
        (ett.series.data.coloring jSlot.castSucc) A B) (_ : TreeSequenceInitialSegment B seed),
        TashkinovAugmentation rho3 A B := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot segmentTrans trace hterminalJ p0 indices0 gamma0
      delta0 rho1 terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj
      segmentVertexBefore TjPrime H x componentPath u exitPath zPosition u0 exitPath0 zPosition0
      rho3 hd1 uPosition segmentVertexBefore A B hstep hBseed
  rcases hstep with ⟨hlen, hAB, c, hcolor, hcMissing⟩
  have hAseed := segmentTrans hAB hBseed
  have hAlen : A.length < seed.length :=
    lt_of_lt_of_le (by omega) hBseed.1
  have hcMissingRho : c ∈ TreeMissingColors rho3 A := by
    unfold TreeMissingColors at hcMissing ⊢
    obtain ⟨y, hyA, hcy⟩ := Finset.mem_biUnion.mp hcMissing
    refine Finset.mem_biUnion.mpr ⟨y, hyA, ?_⟩
    rw [hd1.2 y (segmentVertexBefore hAseed hAlen hyA)]
    exact hcy
  let added : Fin B.length :=
    Fin.cast hlen.symm (Fin.last A.length)
  obtain ⟨attach, hattach⟩ := B.attaches added
  let oldPosition : Fin (B.length + 1) :=
    Fin.castLT attach
      (Nat.lt_trans attach.isLt (Nat.succ_lt_succ added.isLt))
  have holdValue : oldPosition.val < A.length + 1 := by
    dsimp [oldPosition, added]
    omega
  let oldA : Fin (A.length + 1) :=
    ⟨oldPosition.val, holdValue⟩
  have holdEq : B.vertex oldPosition = A.vertex oldA := by
    have hcast : Fin.castLE (Nat.succ_le_succ hAB.1) oldA =
        oldPosition := by apply Fin.ext; rfl
    rw [← hcast]
    exact hAB.2.1 oldA
  have holdBefore : B.vertex oldPosition ∈ TreeVerticesBefore
      (ett.series.data.tree jSlot.succ.castSucc) v
      hterminalJ := by
    rw [holdEq]
    exact segmentVertexBefore hAseed hAlen
      (by simp [TreeSequenceVertexSet])
  have holdIncident : Incident G (B.vertex oldPosition)
      (B.edge added) := by
    unfold Incident
    rw [hattach]
    simp [oldPosition]
  have haddedFixed : rho3 (B.edge added) =
      ett.series.data.coloring jSlot.castSucc (B.edge added) := by
    apply hd1.1 (B.edge added)
      ⟨B.vertex oldPosition, holdBefore, holdIncident⟩
    refine ⟨c, Finset.mem_union_left _ ?_, hcolor⟩
    unfold TreeMissingColors at hcMissing
    obtain ⟨y, hyA, hcy⟩ := Finset.mem_biUnion.mp hcMissing
    exact Finset.mem_biUnion.mpr
      ⟨y, segmentVertexBefore hAseed hAlen hyA, hcy⟩
  exact ⟨hlen, hAB, c, haddedFixed.trans hcolor, hcMissingRho⟩

private theorem helper_branch_6698.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
        e0 input T generating) (_ : MaximumProperty ett) (hpositive : (0 : ℕ) < ett.rounds) (v :
        V) (gamma delta : Fin k) (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds := (⟨ett.rounds - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
        (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ)) (hfirstPositive
        : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds := (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
    by omega
    ⟩ : Fin ett.rounds);
    ∀ (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0
        : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds) (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)) (_ :
        TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree q.succ.castSucc)) (TjPrime : TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let _ : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
        gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))),
    ∀ u0 ∉ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc),
    ∀ (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0)) (zPosition0
        : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (rho3 :
        PartialEdgeColoring E k) (_ : Fin (TjPrime.length + (1 : ℕ))) (hzPositionPositive : (1 :
        ℕ) ≤ (↑zPosition0 : ℕ)) (hzPositionBound : (↑zPosition0 : ℕ) ≤ (ett.series.data.tree
        jSlot.succ.castSucc).length),
    let Z : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑zPosition0 : ℕ) hzPositionPositive hzPositionBound; TreeSequenceInitialSegment Z
        (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (C : TreeSequence G e0), u0 ∈ TreeSequenceVertexSet C → TreeSequenceVertexSet Z ⊆
        TreeSequenceVertexSet C → KTriple G k e0 input → ett.series.data.tree (1 : Fin (ett.rounds
        + (2 : ℕ))) = ett.series.data.tree jSlot.succ.castSucc → KTriple G k e0 rho3 →
        TashkinovTree G e0 rho3 C → zPosition0 = Fin.last (ett.series.data.tree
        jSlot.succ.castSucc).length → False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot vertexTransfer trace p0 indices0 gamma0 delta0
      rho1 terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj hTjQ
      TjPrime H C x componentPath u exitPath zPosition u0 huOutside0 exitPath0 zPosition0 rho3
      uPosition hzPositionPositive hzPositionBound Z hZTj C huC hZC triple htreeOne htripleRho
      hCTree hzLast
  have hZlen : Z.length =
      (ett.series.data.tree jSlot.succ.castSucc).length := by
    simp [Z, TreeSequencePrefix, hzLast]
  have hTjZ : TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc) ⊆
        TreeSequenceVertexSet Z := by
    intro y hy
    simp only [TreeSequenceVertexSet, Finset.mem_image,
      Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨i, rfl⟩ := hy
    let iZ : Fin (Z.length + 1) := ⟨i.val, by omega⟩
    refine ⟨iZ, ?_⟩
    have hcast : Fin.castLE (Nat.succ_le_succ hZTj.1) iZ =
        i := by apply Fin.ext; rfl
    rw [← hcast]
    exact hZTj.2.1 iZ
  have hTjC : TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc) ⊆
        TreeSequenceVertexSet C := fun _ hy => hZC (hTjZ hy)
  have hstrict : TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc) <
        TreeSequenceVertexSet C :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hTjC, by
      intro heq
      exact huOutside0
        (vertexTransfer hTjQ (heq.symm.subset huC))⟩
  have hk : ChromaticIndex G - 1 = k := by
    have hchromatic := triple.2.1
    omega
  have hCOrder : (TreeSequenceVertexSet C).card ≤
      TashkinovOrder G := by
    unfold TashkinovOrder
    dsimp only
    apply Finset.le_max'
    apply Finset.mem_insert_of_mem
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le (Finset.card_le_univ _), ?_⟩
    rw [hk]
    exact ⟨e0, rho3, C, htripleRho, hCTree, rfl⟩
  have hTjOrder : (TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc)).card =
        TashkinovOrder G := by
    rw [← htreeOne]
    exact hMP.1
  have hbound : (TreeSequenceVertexSet C).card ≤
      (TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)).card := by
    rw [hTjOrder]
    exact hCOrder
  exact (Nat.not_lt_of_ge hbound)
    (Finset.card_lt_card hstrict)

private theorem helper_branch_6749.{u_1, u_2} :
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
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
        (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ)) (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑terminalPosition : ℕ) hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : seed.vertex (Fin.last seed.length) = v) (_ : delta ∈ MissingColors G rho1 v),
    let _ : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (beta0 : Fin k) (z0 : V) (zPosition0 : Fin ((ett.series.data.tree
        jSlot.succ.castSucc).length + (1 : ℕ))) (_ : (ett.series.data.tree
        jSlot.succ.castSucc).vertex zPosition0 = z0) (rho3 : PartialEdgeColoring E k) (_ : (
    ∀ (_ : beta0 ∈ MissingColors G rho1 z0), delta ∈ MissingColors G rho3 z0)) (_ : ¬z0 = v)
        (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition0 : ℕ)) (hzPositionBound : (↑zPosition0 : ℕ) ≤
        (ett.series.data.tree jSlot.succ.castSucc).length),
    let Z : TreeSequence G e0 := TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
        (↑zPosition0 : ℕ) hzPositionPositive hzPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed Z) (_ : MissingColors G rho3 v = MissingColors G rho1
        v) (C : TreeSequence G e0) (_ : TreeSequenceVertexSet Z ⊆ TreeSequenceVertexSet C) (_ :
        ColoredVertexSetElementary G rho3 (TreeSequenceVertexSet C)) (_ : (↑zPosition0 : ℕ) <
        (↑(Fin.last (ett.series.data.tree jSlot.succ.castSucc).length) : ℕ) ∧ beta0 ∈
        MissingColors G rho1 z0), False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace rho1 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed hseedTerminal hdeltaMissing C beta0
      z0 zPosition0 hzPosition0 rho3 hdeltaZ hzv hzPositionPositive hzPositionBound Z hseedZ
      hterminalMissingEq C hZC hCElementary hzEarlier
  have hterminalC : v ∈ TreeSequenceVertexSet C := by
    apply hZC
    simp only [TreeSequenceVertexSet, Finset.mem_image,
      Finset.mem_univ, true_and]
    let vZ : Fin (Z.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hseedZ.1)
        (Fin.last seed.length)
    refine ⟨vZ, ?_⟩
    exact (hseedZ.2.1 (Fin.last seed.length)).trans
      hseedTerminal
  have hzZ : z0 ∈ TreeSequenceVertexSet Z := by
    simp only [TreeSequenceVertexSet, Finset.mem_image,
      Finset.mem_univ, true_and]
    refine ⟨Fin.last Z.length, ?_⟩
    change (ett.series.data.tree
      jSlot.succ.castSucc).vertex
        (Fin.castLE (Nat.succ_le_succ hzPositionBound)
          (Fin.last zPosition0.val)) = z0
    have hindex : Fin.castLE
        (Nat.succ_le_succ hzPositionBound)
          (Fin.last zPosition0.val) = zPosition0 := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hzPosition0
  have hzC : z0 ∈ TreeSequenceVertexSet C := hZC hzZ
  have hdeltaTerminal : delta ∈ MissingColors G rho3 v := by
    rw [hterminalMissingEq]
    exact hdeltaMissing
  have hdeltaAtZ : delta ∈ MissingColors G rho3 z0 :=
    hdeltaZ hzEarlier.2
  have hdisjoint := hCElementary hterminalC hzC
    (fun hvz => hzv hvz.symm)
  exact (Finset.disjoint_left.mp hdisjoint)
    hdeltaTerminal hdeltaAtZ

end GoldbergSeymour
