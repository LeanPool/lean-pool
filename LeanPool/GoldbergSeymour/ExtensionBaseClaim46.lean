/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DegreeTwoPaths

public import LeanPool.GoldbergSeymour.SharedFacts.ExtensionBaseClaim45Singleton

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.ETTStrongInterchangeable
public import LeanPool.GoldbergSeymour.ExtensionBaseCaseTwoObservation19
public import LeanPool.GoldbergSeymour.ExtensionBaseCaseTwoObservation20
public import LeanPool.GoldbergSeymour.ExtensionBaseCaseTwoObservation21
public import LeanPool.GoldbergSeymour.ExtensionBaseCaseTwoObservation23
public import LeanPool.GoldbergSeymour.ExtensionBaseSupportClass
public import LeanPool.GoldbergSeymour.InternalEdges
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwapStable
public import LeanPool.GoldbergSeymour.StableColoringBeforeVertex
public import LeanPool.GoldbergSeymour.OutsideSwapPrefixEffects
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo

/-!
# Extension Base Claim46

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperHE41070Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSlot : Fin ett.rounds)
        (terminalSupport : V) (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T) (Tn
        TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (supportColors : Finset (Fin
        k)) (gammaN deltaN : Fin k) (_ : (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).erase terminalSlot) (_ :
        ett.series.data.gamma s.succ = some gammaS) (_ : ett.series.data.delta s.succ = some
        deltaS), ETTStrongInterchangeable ett s terminalSupport rho1 gammaS deltaS)) (_ : (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).erase terminalSlot) (_ :
        ett.series.data.gamma s.succ = some gammaS) (_ : ett.series.data.delta s.succ = some
        deltaS), gammaS ∈ supportColors ∧ deltaS ∈ supportColors)) (_ : (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).erase terminalSlot) (_ :
        ett.series.data.gamma s.succ = some gammaS) (_ : ett.series.data.delta s.succ = some
        deltaS), deltaN ≠ gammaS ∧ deltaN ≠ deltaS)) (_ : (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).erase terminalSlot) (_ :
        ett.series.data.gamma s.succ = some gammaS) (_ : ett.series.data.delta s.succ = some
        deltaS),
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree s.succ.castSucc), v ≠ terminalSupport →
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G rho1 gammaS deltaS (Sum.inl v) → w ∈
        TreeSequenceVertexSet Tn)),
    ∀ u ∉ TreeSequenceVertexSet Tn,
    ∀ beta ∉ supportColors,
    ∀ (_ : V),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u); (
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, w ≠ u →
    ∀ (f : E), Incident G w f → Sum.inr f ∉ TwoColorComponent G rho0 gammaN beta (Sum.inl u)) → (
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, w ≠ u →
    ∀ (f : E), Incident G w f → mu0 f = rho0 f) → (
    ∀ (c : Fin k), c ≠ beta → c ≠ deltaN →
    ∀ (f : E), rho0 f = some c ↔ rho1 f = some c) →
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).erase terminalSlot →
        ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ = some deltaS →
        ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS

private abbrev helperContinuation1644Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSlot preterminalSlot : Fin
        ett.rounds) (_ : (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds) (_ : (↑preterminalSlot : ℕ) <
        (↑terminalSlot : ℕ)) (terminalSupport : V) (hterminalSupport : terminalSupport ∈
        TreeSequenceVertexSet T) (Tj Tn seed TjPrime : TreeSequence G e0) (phiJ rho1 :
        PartialEdgeColoring E k) (Dprev supportColors : Finset (Fin k)) (gammaN deltaN : Fin k) (x
        : V) (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
        (Sum.inl x)) (_ : TreeSequenceInitialSegment Tj Tn) (_ : TreeSequenceInitialSegment seed
        Tj) (_ : TreeSequenceInitialSegment seed TjPrime) (_ : seed.vertex (Fin.last seed.length)
        = terminalSupport) (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj) (_ :
        TashkinovClosure rho1 seed TjPrime) (_ : ColoredVertexSetElementary G rho1
        (TreeSequenceVertexSet TjPrime)) (_ : (
    ∀ v ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport, MissingColors G rho1 v ∩
        supportColors = ∅)) (_ : MissingColors G rho1 terminalSupport ∩ supportColors =
        { deltaN }) (_ : deltaN ∈ supportColors) (_ : gammaN ≠ deltaN) (_ : deltaN ∈ MissingColors
        G rho1 terminalSupport) (_ : p.IsPath) (_ : {y : V ⊕ E | y ∈ p.support} =
        TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport)) (_ : x ∉
        TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) (_ : StableColoringBeforeVertex
        Tj terminalSupport hterminalTj Dprev phiJ rho1) (_ : (
    ∀ v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport, MissingColors G rho1 v = MissingColors
        G phiJ v)) (_ : TashkinovAugmentationSequence phiJ seed Tj) (_ : (
    ∀ (a : Fin Tj.length) (_ : seed.length ≤ (↑a : ℕ)), rho1 (Tj.edge a) = phiJ (Tj.edge a))) (_ :
        deltaN ∉ TreeMissingColors phiJ Tj) (_ : (supportColors = (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).biUnion fun (s : Fin ett.rounds) ↦
        ett.series.data.stored s.succ)) (_ : terminalSlot ∈ ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport) (_ : preterminalSlot ∈
        (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
        terminalSlot) (_ : ett.series.data.delta preterminalSlot.succ = some gammaN) (_ :
        ett.series.data.gamma terminalSlot.succ = some gammaN) (_ : ett.series.data.delta
        terminalSlot.succ = some deltaN) (_ : (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).erase terminalSlot) (_ :
        ett.series.data.gamma s.succ = some gammaS) (_ : ett.series.data.delta s.succ = some
        deltaS), ETTStrongInterchangeable ett s terminalSupport rho1 gammaS deltaS)) (_ : (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).erase terminalSlot) (_ :
        ett.series.data.gamma s.succ = some gammaS) (_ : ett.series.data.delta s.succ = some
        deltaS), gammaS ∈ supportColors ∧ deltaS ∈ supportColors)) (_ : (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).erase terminalSlot) (_ :
        ett.series.data.gamma s.succ = some gammaS) (_ : ett.series.data.delta s.succ = some
        deltaS), deltaN ≠ gammaS ∧ deltaN ≠ deltaS)) (_ : (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k) (_ : s ∈ (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).erase terminalSlot) (_ :
        ett.series.data.gamma s.succ = some gammaS) (_ : ett.series.data.delta s.succ = some
        deltaS),
    ∀ v ∈ TreeSequenceVertexSet (ett.series.data.tree s.succ.castSucc), v ≠ terminalSupport →
    ∀ (w : V), Sum.inl w ∈ TwoColorComponent G rho1 gammaS deltaS (Sum.inl v) → w ∈
        TreeSequenceVertexSet Tn)) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (_ : terminalSupport ∈ TreeSequenceVertexSet TjPrime) (u : V)
        (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)) (_
        : exitPath.IsPath) (_ : (2 : ℕ) ≤ exitPath.length) (_ : (
    ∀ y ∈ exitPath.support, y ∈ p.support)) (_ : (
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, Sum.inl w ∈ exitPath.support ↔
        w = u)) (_ : (
    ∃ g ∈ BoundaryColorEdges G rho1 (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
        gammaN, Incident G u g ∧ Sum.inr g ∈ exitPath.support)) (huPrime : u ∈
        TreeSequenceVertexSet TjPrime) (_ : u ∉ TreeSequenceVertexSet Tn),
    ∀ beta ∈ MissingColors G rho1 u, u ≠ terminalSupport → u ∈ (TreeSequenceVertexSet
        TjPrime).erase terminalSupport → beta ∉ supportColors → beta ≠ deltaN → beta ≠ gammaN → u
        ∉ TreeSequenceVertexSet seed →
    ∀ (z : V) (hz : z ∈ TreeSequenceVertexSet Tj) (zPosition : Fin (Tj.length + (1 : ℕ))),
        Tj.vertex zPosition = z → seed.length ≤ (↑zPosition : ℕ) → (
    ∀ w ∈ TreeVerticesBefore Tj z hz, beta ∉ MissingColors G rho1 w) → (
    ∀ (a : Fin Tj.length), seed.length ≤ (↑a : ℕ) → (↑a : ℕ) < (↑zPosition : ℕ) → rho1 (Tj.edge a)
        ≠ some beta) → TreeMissingColors rho1 TjPrime ∩ supportColors = { deltaN } → (
    ∀ (a : Fin TjPrime.length), seed.length ≤ (↑a : ℕ) →
    ∀ c ∈ supportColors \ { deltaN }, rho1 (TjPrime.edge a) ≠ some c) →
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let _ : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
        IsProperEdgeColoring G rho0 → IsOneEdgeUncolored rho0 e0 → StableColoring TjPrime
        supportColors rho1 rho0 → (
    ∀ (f : E), TreeIncidentEdge TjPrime f → rho0 f = rho1 f) → gammaN ≠ beta →
        IsProperEdgeColoring G (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta
        deltaN) gammaN beta (Sum.inl u)) ∧ IsOneEdgeUncolored (TwoColorComponentSwap G
        (OutsideTreeColorSwap TjPrime rho1 beta deltaN) gammaN beta (Sum.inl u)) e0 ∧
        StableColoringBeforeVertex Tj terminalSupport hterminalTj Dprev phiJ
        (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN) gammaN beta
        (Sum.inl u)) ∧ ((
    ∀ v ∈ ((TreeVerticesBefore Tj z hz ∪ { z } ∪ (TreeVerticesBefore TjPrime u huPrime ∪
        { u })).erase u).erase z, MissingColors G (TwoColorComponentSwap G (OutsideTreeColorSwap
        TjPrime rho1 beta deltaN) gammaN beta (Sum.inl u)) v = MissingColors G rho1 v) ∧ (
    ∀ (f : E), ((
    ∃ (a : Fin Tj.length), seed.length ≤ (↑a : ℕ) ∧ (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → TwoColorComponentSwap
        G (OutsideTreeColorSwap TjPrime rho1 beta deltaN) gammaN beta (Sum.inl u) f = rho1 f) ∧
        (beta ∈ MissingColors G rho1 z → deltaN ∈ MissingColors G (TwoColorComponentSwap G
        (OutsideTreeColorSwap TjPrime rho1 beta deltaN) gammaN beta (Sum.inl u)) z) ∧ (z ∈
        TreeVerticesBefore TjPrime u huPrime → MissingColors G (TwoColorComponentSwap G
        (OutsideTreeColorSwap TjPrime rho1 beta deltaN) gammaN beta (Sum.inl u)) z = MissingColors
        G rho1 z)) ∧ (ett.series.data.delta preterminalSlot.succ = some gammaN ∧ gammaN ∈
        MissingColors G (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN)
        gammaN beta (Sum.inl u)) u ∧ beta ∉ MissingColors G (TwoColorComponentSwap G
        (OutsideTreeColorSwap TjPrime rho1 beta deltaN) gammaN beta (Sum.inl u)) u) ∧ (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).erase terminalSlot →
        ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ = some deltaS →
        ETTStrongInterchangeable ett s terminalSupport (TwoColorComponentSwap G
        (OutsideTreeColorSwap TjPrime rho1 beta deltaN) gammaN beta (Sum.inl u)) gammaS deltaS) ∧
        (((TreeSequenceVertexSet TjPrime).erase u).biUnion fun (v : V) ↦ MissingColors G
        (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta deltaN) gammaN beta
        (Sum.inl u)) v) ∩ supportColors = { deltaN } ∧ MissingColors G (TwoColorComponentSwap G
        (OutsideTreeColorSwap TjPrime rho1 beta deltaN) gammaN beta (Sum.inl u)) terminalSupport ∩
        supportColors = { deltaN } ∧
    ∀ (a : Fin TjPrime.length), seed.length ≤ (↑a : ℕ) →
    ∀ c ∈ supportColors \ { deltaN }, ¬TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1
        beta deltaN) gammaN beta (Sum.inl u) (TjPrime.edge a) = some c

private theorem helper_hgammaMu0_408.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN :
        Fin k) (u : V) (beta : Fin k) (_ : beta ≠ gammaN),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
    ∀ (_ : gammaN ≠ beta) (_ : beta ∈ MissingColors G rho0 u), gammaN ∈ MissingColors G mu0 u := by
  classical
  intro V E _ _ G k e0 TjPrime rho1 gammaN deltaN u beta hbetaGamma rho0 mu0 hgammaBeta hbetaRho0
  let _ := Fintype.ofFinite V
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hgPresent
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hgPresent
  obtain ⟨f, huf, hfMu0⟩ := hgPresent
  by_cases hfComponent : Sum.inr f ∈
      TwoColorComponent G rho0 gammaN beta (Sum.inl u)
  · by_cases hfGamma : rho0 f = some gammaN
    · have : (some beta : Option (Fin k)) = some gammaN := by
        simp [mu0, TwoColorComponentSwap, hfComponent, hfGamma, hbetaGamma] at hfMu0
      exact hbetaGamma (Option.some.inj this)
    · by_cases hfBeta : rho0 f = some beta
      · have hnotPresent : beta ∉ PresentColors G rho0 u := by
          simpa [MissingColors] using hbetaRho0
        exact hnotPresent (by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨f, huf, hfBeta⟩)
      · have : rho0 f = some gammaN := by
          simp [mu0, TwoColorComponentSwap, hfComponent, hfGamma, hfBeta] at hfMu0
        exact hfGamma this
  · have hfRho0 : rho0 f = some gammaN := by
      simpa [mu0, TwoColorComponentSwap, hfComponent] using hfMu0
    have hadj : (TwoColorIncidenceGraph G rho0 gammaN beta).Adj
        (Sum.inl u) (Sum.inr f) := ⟨huf, Or.inl hfRho0⟩
    apply hfComponent
    change (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
        (Sum.inr f) =
      (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
        (Sum.inl u)
    exact
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm

private theorem helper_path_edge_data_156.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSlot preterminalSlot : Fin
        ett.rounds) (_ : (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds) (_ : (↑preterminalSlot : ℕ) <
        (↑terminalSlot : ℕ)) (terminalSupport : V) (hterminalSupport : terminalSupport ∈
        TreeSequenceVertexSet T) (rho1 : PartialEdgeColoring E k) (supportColors : Finset (Fin k))
        (gammaN deltaN : Fin k) (x : V) (_ : (supportColors = (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).biUnion fun (s : Fin ett.rounds) ↦
        ett.series.data.stored s.succ)) (_ : terminalSlot ∈ ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport) (_ : preterminalSlot ∈
        (ExtensionBaseSupportClass ett terminalSupport hterminalSupport terminalSupport).erase
        terminalSlot) (_ : ett.series.data.gamma terminalSlot.succ = some gammaN) (_ :
        ett.series.data.delta terminalSlot.succ = some deltaN) (u : V) (_ :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)),
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN;
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)) (_ : q.IsPath) {e : E} (_ : Sum.inr e ∈
        q.support),
    ∃ (j : ℕ), (0 : ℕ) < j ∧ j < q.length ∧ q.getVert j = Sum.inr e ∧
    ∃ (v : V) (w : V), q.getVert (j - (1 : ℕ)) = Sum.inl v ∧ q.getVert (j + (1 : ℕ)) = Sum.inl w ∧
        v ≠ w ∧ G.ends e = s(v, w) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot preterminalSlot _ _ terminalSupport
      hterminalSupport rho1 supportColors gammaN deltaN x _ _ _ _ _ u exitPath H1 a b q hq e he
  obtain ⟨j, hj, hjle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp he
  have hjpos : 0 < j := by
    by_contra hn
    have hjzero : j = 0 := Nat.eq_zero_of_not_pos hn
    have : (Sum.inl a : Sum V E) = Sum.inr e := by
      simp [hjzero] at hj
    exact Sum.inl_ne_inr this
  have hjlt : j < q.length := by
    by_contra hn
    have hjend : j = q.length := by omega
    have : (Sum.inl b : Sum V E) = Sum.inr e := by
      simp [hjend] at hj
    exact Sum.inl_ne_inr this
  have hprev := q.adj_getVert_succ (i := j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega, hj] at hprev
  have hnext := q.adj_getVert_succ (i := j) hjlt
  rw [hj] at hnext
  obtain ⟨v, hv⟩ : ∃ v : V, q.getVert (j - 1) = Sum.inl v := by
    cases hc : q.getVert (j - 1) with
    | inl v => exact ⟨v, rfl⟩
    | inr f =>
        rw [hc] at hprev
        exact False.elim (by simp [H1, TwoColorIncidenceGraph] at hprev)
  obtain ⟨w, hw⟩ : ∃ w : V, q.getVert (j + 1) = Sum.inl w := by
    cases hc : q.getVert (j + 1) with
    | inl w => exact ⟨w, rfl⟩
    | inr f =>
        rw [hc] at hnext
        exact False.elim (by simp [H1, TwoColorIncidenceGraph] at hnext)
  have hve : Incident G v e := by
    rw [hv] at hprev
    change Incident G v e ∧
      (rho1 e = some gammaN ∨ rho1 e = some deltaN) at hprev
    exact hprev.1
  have hwe : Incident G w e := by
    rw [hw] at hnext
    change Incident G w e ∧
      (rho1 e = some gammaN ∨ rho1 e = some deltaN) at hnext
    exact hnext.1
  have hvw : v ≠ w := by
    intro hvw
    have hindex := hq.getVert_injOn
      (show j - 1 ≤ q.length by omega)
      (show j + 1 ≤ q.length by omega)
      (by rw [hv, hw, hvw])
    omega
  have hends : G.ends e = s(v, w) :=
    (Sym2.mem_and_mem_iff hvw).mp ⟨hve, hwe⟩
  exact ⟨j, hjpos, hjlt, hj, v, w, hv, hw, hvw, hends⟩

private theorem helper_exit_edge_color_254.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] [DecidableEq V]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn TjPrime : TreeSequence G e0) (rho1 :
        PartialEdgeColoring E k) (gammaN deltaN : Fin k) (x : V) (_ : gammaN ≠ deltaN) (u : V)
        (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)) (_
        : exitPath.IsPath) (_ : (
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, Sum.inl w ∈ exitPath.support ↔
        w = u)) (beta : Fin k) (_ : beta ≠ deltaN),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    ∀ (_ : (
    ∀ (f : E) (_ : TreeIncidentEdge TjPrime f), rho0 f = rho1 f)) (_ : gammaN ≠ beta) (g : E) (_ :
        rho1 g = some gammaN),
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN;
    ∀ (_ : (
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)) (_ : q.IsPath) {e : E} (_ : Sum.inr e ∈
        q.support) {w : V} (_ : Incident G w e), Sum.inl w ∈ q.support)) (_ : (
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)) (_ : q.IsPath) {e : E} (_ : Sum.inr e ∈
        q.support) (_ : Incident G b e), q.getVert (q.length - (1 : ℕ)) = Sum.inr e)) (_ :
        exitPath.getVert (exitPath.length - (1 : ℕ)) = Sum.inr g) (e : E) (_ : Sum.inr e ∈
        exitPath.support) (_ : rho1 e = some gammaN ∨ rho1 e = some deltaN), rho0 e = some gammaN
        ∨ rho0 e = some beta := by
  classical
  intro V E _ _ _ G k e0 Tn TjPrime rho1 gammaN deltaN x hgammaDelta u exitPath hexitPath
      hexitIntersection beta hbetaDelta rho0 hrho0Fixed hgammaBeta g hgRho1 H1
      path_incident_vertex_mem path_incident_end_last hgLast e he hcolor
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  rcases hcolor with hgamma | hdelta
  · left
    by_cases heIncident : TreeIncidentEdge TjPrime e
    · rw [hrho0Fixed e heIncident]
      exact hgamma
    · unfold rho0 OutsideTreeColorSwap
      rw [ite_eq_right heIncident]
      rw [ite_eq_right (by
        intro heb
        exact hgammaBeta (Option.some.inj (hgamma.symm.trans heb)))]
      rw [ite_eq_right (by
        intro hed
        exact hgammaDelta (Option.some.inj (hgamma.symm.trans hed)))]
      exact hgamma
  · have hnotIncident : ¬ TreeIncidentEdge TjPrime e := by
      intro heIncident
      obtain ⟨w, hwPrime, hwe⟩ := heIncident
      have hwExit : Sum.inl w ∈ exitPath.support :=
        path_incident_vertex_mem exitPath hexitPath he hwe
      have hwu : w = u :=
        (hexitIntersection w
          (Finset.mem_union.mpr (Or.inr hwPrime))).mp hwExit
      subst w
      have heLast := path_incident_end_last exitPath hexitPath he hwe
      have heg : e = g := Sum.inr.inj (heLast.symm.trans hgLast)
      subst e
      exact hgammaDelta (Option.some.inj (hgRho1.symm.trans hdelta))
    right
    unfold rho0 OutsideTreeColorSwap
    rw [ite_eq_right hnotIncident]
    rw [ite_eq_right (by
      intro heb
      exact hbetaDelta (Option.some.inj (heb.symm.trans hdelta)))]
    rw [ite_eq_left hdelta]

private theorem helper_exit_adj_rho0_292.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN :
        Fin k) (x u : V) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl
        x) (Sum.inl u)) (beta : Fin k),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN;
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho0 gammaN beta;
    ∀ (_ : (
    ∀ (e : E) (_ : Sum.inr e ∈ exitPath.support) (_ : rho1 e = some gammaN ∨ rho1 e = some
        deltaN), rho0 e = some gammaN ∨ rho0 e = some beta)),
    ∀ i < exitPath.length, H0.Adj (exitPath.getVert i) (exitPath.getVert (i + (1 : ℕ))) := by
  classical
  intro V E _ _ G k e0 TjPrime rho1 gammaN deltaN x u exitPath beta rho0 H1 H0 exit_edge_color i hi
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  have hadj := exitPath.adj_getVert_succ (i := i) hi
  cases hx : exitPath.getVert i with
  | inl v =>
      cases hy : exitPath.getVert (i + 1) with
      | inl w =>
          rw [hx, hy] at hadj
          exact False.elim (by simp [TwoColorIncidenceGraph] at hadj)
      | inr e =>
          rw [hx, hy] at hadj
          change Incident G v e ∧
              (rho1 e = some gammaN ∨ rho1 e = some deltaN) at hadj
          change Incident G v e ∧
              (rho0 e = some gammaN ∨ rho0 e = some beta)
          exact ⟨hadj.1, exit_edge_color e
            (by simpa [hy] using exitPath.getVert_mem_support (i + 1)) hadj.2⟩
  | inr e =>
      cases hy : exitPath.getVert (i + 1) with
      | inl v =>
          rw [hx, hy] at hadj
          change Incident G v e ∧
              (rho1 e = some gammaN ∨ rho1 e = some deltaN) at hadj
          change Incident G v e ∧
              (rho0 e = some gammaN ∨ rho0 e = some beta)
          exact ⟨hadj.1, exit_edge_color e
            (by simpa [hx] using exitPath.getVert_mem_support i) hadj.2⟩
      | inr f =>
          rw [hx, hy] at hadj
          exact False.elim (by simp [TwoColorIncidenceGraph] at hadj)

private theorem helper_new_x_adj_old_342.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (seed TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN
        deltaN : Fin k) (x : V) (_ : TashkinovClosure rho1 seed TjPrime) (_ : gammaN ≠ deltaN),
    ∀ u ∈ TreeSequenceVertexSet TjPrime,
    ∀ beta ∈ MissingColors G rho1 u, beta ≠ deltaN →
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN; (
    ∀ (f : E), TreeIncidentEdge TjPrime f → rho0 f = rho1 f) → x ∉ TreeSequenceVertexSet TjPrime →
    ∀ (e : E), Incident G x e → rho0 e = some gammaN ∨ rho0 e = some beta → rho1 e = some gammaN ∨
        rho1 e = some deltaN := by
  classical
  intro V E _ _ G k e0 seed TjPrime rho1 gammaN deltaN x hclosure hgammaDelta u huPrime beta
      hbeta hbetaDelta rho0 hrho0Fixed hxPrime e hxe hcolor
  by_cases heIncident : TreeIncidentEdge TjPrime e
  · have hfixed := hrho0Fixed e heIncident
    obtain ⟨w, hwPrime, hwe⟩ := heIncident
    have hwx : w ≠ x := by
      intro hwx
      apply hxPrime
      simpa [← hwx] using hwPrime
    have hends : G.ends e = s(w, x) :=
      (Sym2.mem_and_mem_iff hwx).mp ⟨hwe, hxe⟩
    have heBoundary : e ∈ BoundaryEdges G
        (TreeSequenceVertexSet TjPrime) := by
      unfold BoundaryEdges
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w, hwPrime, x, hxPrime, hends⟩
    rcases hcolor with hgamma | hbetaColor
    · exact Or.inl (hfixed.symm.trans hgamma)
    · have hbetaOld : rho1 e = some beta :=
        hfixed.symm.trans hbetaColor
      exact False.elim
        ((hclosure.2 heBoundary huPrime hbetaOld) hbeta)
  · unfold rho0 OutsideTreeColorSwap at hcolor
    rw [ite_eq_right heIncident] at hcolor
    by_cases hbetaOld : rho1 e = some beta
    · rw [ite_eq_left hbetaOld] at hcolor
      rcases hcolor with hdeltaGamma | hdeltaBeta
      · exact False.elim
          (hgammaDelta (Option.some.inj hdeltaGamma).symm)
      · exact False.elim
          (hbetaDelta (Option.some.inj hdeltaBeta).symm)
    · by_cases hdeltaOld : rho1 e = some deltaN
      · exact Or.inr hdeltaOld
      · rw [ite_eq_right hbetaOld, ite_eq_right hdeltaOld] at hcolor
        rcases hcolor with hgammaOld | hbetaOld'
        · exact Or.inl hgammaOld
        · exact False.elim (hbetaOld hbetaOld')

private theorem helper_first_p_last_384.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {k : ℕ} (terminalSupport : V)
        (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (x : V) (p :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport) (Sum.inl x))
        (_ : p.IsPath) (u : V) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl x) (Sum.inl u)) (_ : (
    ∀ y ∈ exitPath.support, y ∈ p.support)),
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN;
    ∀ (_ : (
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)) (_ : q.IsPath) {e : E} (_ : Sum.inr e ∈
        q.support) (_ : Incident G b e), q.getVert (q.length - (1 : ℕ)) = Sum.inr e)) (_ : H1.Adj
        (Sum.inl x) (exitPath.getVert (1 : ℕ))), p.getVert (p.length - (1 : ℕ)) = exitPath.getVert
        (1 : ℕ) := by
  classical
  intro V E G k terminalSupport rho1 gammaN deltaN x p hpath u exitPath hexitSupport H1
      path_incident_end_last first_old_adj
  cases hfirst : exitPath.getVert 1 with
  | inl v =>
      rw [hfirst] at first_old_adj
      exact False.elim
        (by simp [H1, TwoColorIncidenceGraph] at first_old_adj)
  | inr e =>
      have heExit : Sum.inr e ∈ exitPath.support := by
        simpa [hfirst] using exitPath.getVert_mem_support 1
      have heP : Sum.inr e ∈ p.support := hexitSupport _ heExit
      have hxe : Incident G x e := by
        rw [hfirst] at first_old_adj
        change Incident G x e ∧
          (rho1 e = some gammaN ∨ rho1 e = some deltaN) at first_old_adj
        exact first_old_adj.1
      exact path_incident_end_last p hpath heP hxe

private theorem helper_old_x_neighbor_unique_401.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (terminalSupport
        : V) (Tj : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (x
        : V) (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
        (Sum.inl x)) (_ : p.IsPath) (_ : {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G rho1
        gammaN deltaN (Sum.inl terminalSupport)) (u : V) (exitPath : (TwoColorIncidenceGraph G
        rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)),
    ∀ z ∈ TreeSequenceVertexSet Tj,
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN; (
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)), q.IsPath →
    ∀ {e : E}, Sum.inr e ∈ q.support → Incident G b e → q.getVert (q.length - (1 : ℕ)) = Sum.inr
        e) → p.getVert (p.length - (1 : ℕ)) = exitPath.getVert (1 : ℕ) →
    ∀ (z : V ⊕ E), H1.Adj (Sum.inl x) z → z = exitPath.getVert (1 : ℕ) := by
  classical
  intro V E G k e0 terminalSupport Tj rho1 gammaN deltaN x p hpath hcomponent u exitPath z hz H1
      path_incident_end_last first_p_last z hxz
  cases hz : z with
  | inl v =>
      rw [hz] at hxz
      exact False.elim (by simp [H1, TwoColorIncidenceGraph] at hxz)
  | inr e =>
      have hxzE : H1.Adj (Sum.inl x) (Sum.inr e) := by
        simpa [hz] using hxz
      have hxe : Incident G x e := by
        change Incident G x e ∧
          (rho1 e = some gammaN ∨ rho1 e = some deltaN) at hxzE
        exact hxzE.1
      have hxComponent : H1.connectedComponentMk (Sum.inl x) =
          H1.connectedComponentMk (Sum.inl terminalSupport) := by
        change Sum.inl x ∈
          TwoColorComponent G rho1 gammaN deltaN
            (Sum.inl terminalSupport)
        rw [← hcomponent]
        exact p.end_mem_support
      have heComponent : H1.connectedComponentMk (Sum.inr e) =
          H1.connectedComponentMk (Sum.inl terminalSupport) :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          hxzE).symm.trans hxComponent
      have heP : Sum.inr e ∈ p.support := by
        change Sum.inr e ∈ {q : Sum V E | q ∈ p.support}
        rw [hcomponent]
        exact heComponent
      have heLast := path_incident_end_last p hpath heP hxe
      exact heLast.symm.trans first_p_last

private theorem helper_x_neighbor_unique_432.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (Tj TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN
        : Fin k) (x u : V) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl
        x) (Sum.inl u)) (beta : Fin k),
    ∀ z ∈ TreeSequenceVertexSet Tj,
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN;
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho0 gammaN beta; (
    ∀ (e : E), Incident G x e → rho0 e = some gammaN ∨ rho0 e = some beta → rho1 e = some gammaN ∨
        rho1 e = some deltaN) → (
    ∀ (z : V ⊕ E), H1.Adj (Sum.inl x) z → z = exitPath.getVert (1 : ℕ)) →
    ∀ (z : V ⊕ E), H0.Adj (Sum.inl x) z → z = exitPath.getVert (1 : ℕ) := by
  classical
  intro V E _ _ G k e0 Tj TjPrime rho1 gammaN deltaN x u exitPath beta z hz rho0 H1 H0 new_x_adj_old
      old_x_neighbor_unique z hxz
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  apply old_x_neighbor_unique z
  cases hz : z with
  | inl v =>
      rw [hz] at hxz
      exact False.elim (by simp [H0, TwoColorIncidenceGraph] at hxz)
  | inr e =>
      have hxzE : H0.Adj (Sum.inl x) (Sum.inr e) := by
        simpa [hz] using hxz
      change Incident G x e ∧
        (rho0 e = some gammaN ∨ rho0 e = some beta) at hxzE
      change Incident G x e ∧
        (rho1 e = some gammaN ∨ rho1 e = some deltaN)
      exact ⟨hxzE.1, new_x_adj_old e hxzE.1 hxzE.2⟩

private theorem helper_u_neighbor_unique_448.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (Tj TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN
        : Fin k) (x u : V) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl
        x) (Sum.inl u)) (beta : Fin k),
    ∀ z ∈ TreeSequenceVertexSet Tj,
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
        IsProperEdgeColoring G rho0 → beta ∈ MissingColors G rho0 u →
    ∀ (g : E), Incident G u g → rho0 g = some gammaN →
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho0 gammaN beta; exitPath.getVert
        (exitPath.length - (1 : ℕ)) = Sum.inr g →
    ∀ (z : V ⊕ E), H0.Adj (Sum.inl u) z → z = exitPath.getVert (exitPath.length - (1 : ℕ)) := by
  classical
  intro V E _ _ G k e0 Tj TjPrime rho1 gammaN deltaN x u exitPath beta z hz rho0 hrho0Proper
      hbetaRho0 g hug hgRho0 H0 hgLast z huz
  let _ := Fintype.ofFinite V
  cases hz : z with
  | inl v =>
      rw [hz] at huz
      exact False.elim (by simp [H0, TwoColorIncidenceGraph] at huz)
  | inr e =>
      rw [hz] at huz
      change Incident G u e ∧
        (rho0 e = some gammaN ∨ rho0 e = some beta) at huz
      have heGamma : rho0 e = some gammaN := by
        rcases huz.2 with heGamma | heBeta
        · exact heGamma
        · have hnotPresent : beta ∉ PresentColors G rho0 u := by
            simpa [MissingColors] using hbetaRho0
          exact False.elim (hnotPresent (by
            simp only [PresentColors, Finset.mem_filter,
              Finset.mem_univ, true_and]
            exact ⟨e, huz.1, heBeta⟩))
      have heg : e = g := by
        by_contra hne
        exact (hrho0Proper hne ⟨u, huz.1, hug⟩ heGamma) hgRho0
      exact (congrArg Sum.inr heg).trans hgLast.symm

private theorem helper_branch_340.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ _ : Fin ett.rounds) (terminalSupport :
        V) (Tj Tn seed TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN
        deltaN : Fin k) (x : V) (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl
        terminalSupport) (Sum.inl x)) (_ : TashkinovClosure rho1 seed TjPrime) (_ : gammaN ≠
        deltaN) (_ : p.IsPath) (_ : {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G rho1 gammaN
        deltaN (Sum.inl terminalSupport)) (_ : x ∉ TreeSequenceVertexSet Tn ∪
        TreeSequenceVertexSet TjPrime) (u : V) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN
        deltaN).Walk (Sum.inl x) (Sum.inl u)) (_ : exitPath.IsPath) (_ : (2 : ℕ) ≤
        exitPath.length) (_ : (
    ∀ y ∈ exitPath.support, y ∈ p.support)) (_ : u ∈ TreeSequenceVertexSet TjPrime),
    ∀ beta ∈ MissingColors G rho1 u, beta ≠ deltaN →
    ∀ z ∈ TreeSequenceVertexSet Tj,
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
        IsProperEdgeColoring G rho0 → (
    ∀ (f : E), TreeIncidentEdge TjPrime f → rho0 f = rho1 f) → beta ∈ MissingColors G rho0 u →
    ∀ (g : E), Incident G u g → rho0 g = some gammaN →
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN;
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho0 gammaN beta; (
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)), q.IsPath →
    ∀ {e : E}, Sum.inr e ∈ q.support → Incident G b e → q.getVert (q.length - (1 : ℕ)) = Sum.inr
        e) → exitPath.getVert (exitPath.length - (1 : ℕ)) = Sum.inr g → (
    ∀ i < exitPath.length, H0.Adj (exitPath.getVert i) (exitPath.getVert (i + (1 : ℕ)))) →
        TwoColorComponent G rho0 gammaN beta (Sum.inl u) ⊆ {y : V ⊕ E | y ∈ exitPath.support} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSlot preterminalSlot terminalSupport Tj
      Tn seed TjPrime rho1 gammaN deltaN x p hclosure hgammaDelta hpath hcomponent hxOutside u
      exitPath hexitPath hexitLength hexitSupport huPrime beta hbeta hbetaDelta z hz rho0
      hrho0Proper hrho0Fixed hbetaRho0 g hug hgRho0 H1 H0 path_incident_end_last hgLast
      exit_adj_rho0 y hy
  have hxPrime : x ∉ TreeSequenceVertexSet TjPrime := by
    intro hx
    exact hxOutside (Finset.mem_union.mpr (Or.inr hx))
  have new_x_adj_old : ∀ e : E, Incident G x e →
      (rho0 e = some gammaN ∨ rho0 e = some beta) →
        rho1 e = some gammaN ∨ rho1 e = some deltaN := by
    exact @helper_new_x_adj_old_342 V E inferInstance inferInstance G k e0 seed TjPrime rho1
        gammaN deltaN x hclosure hgammaDelta u huPrime beta hbeta hbetaDelta hrho0Fixed hxPrime
  have first_old_adj : H1.Adj (Sum.inl x) (exitPath.getVert 1) := by
    simpa [H1] using exitPath.adj_getVert_succ
      (show 0 < exitPath.length by omega)
  have first_p_last :
      p.getVert (p.length - 1) = exitPath.getVert 1 := by
    exact @helper_first_p_last_384 V E G k terminalSupport rho1 gammaN deltaN x p hpath u
        exitPath hexitSupport path_incident_end_last first_old_adj
  have old_x_neighbor_unique : ∀ z : Sum V E,
      H1.Adj (Sum.inl x) z → z = exitPath.getVert 1 := by
    exact @helper_old_x_neighbor_unique_401 V E G k e0 terminalSupport Tj rho1 gammaN deltaN x p
        hpath hcomponent u exitPath z hz path_incident_end_last first_p_last
  have x_neighbor_unique : ∀ z : Sum V E,
      H0.Adj (Sum.inl x) z → z = exitPath.getVert 1 := by
    exact @helper_x_neighbor_unique_432 V E inferInstance inferInstance G k e0 Tj TjPrime rho1
        gammaN deltaN x u exitPath beta z hz new_x_adj_old old_x_neighbor_unique
  have u_neighbor_unique :
    ∀ z : Sum V E, H0.Adj (Sum.inl u) z → z = exitPath.getVert (exitPath.length - 1) := by
    exact @helper_u_neighbor_unique_448 V E inferInstance inferInstance G k e0 Tj TjPrime rho1
        gammaN deltaN x u exitPath beta z hz hrho0Proper hbetaRho0 g hug hgRho0 hgLast
  have support_closed : ∀ w : Sum V E, w ∈ exitPath.support →
      ∀ z : Sum V E, H0.Adj w z → z ∈ exitPath.support := by
    exact degreeTwoPathSupportClosed exitPath hexitPath
      (TwoColorIncidenceDegreeAtMostTwo G rho0 gammaN beta hrho0Proper)
      exit_adj_rho0 x_neighbor_unique u_neighbor_unique
  have reach : H0.Reachable (Sum.inl u) y := by
    change H0.connectedComponentMk y =
        H0.connectedComponentMk (Sum.inl u) at hy
    exact SimpleGraph.ConnectedComponent.eq.mp hy |>.symm
  apply reach.mem_subgraphVerts
    (H := (⊤ : H0.Subgraph).induce {w | w ∈ exitPath.support})
    (fun w hw z hadj => by
      exact ⟨by simpa using hw,
        support_closed w (by simpa using hw) z hadj, hadj⟩)
    (by simp)

private theorem helper_hcomponentExit_447.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSlot preterminalSlot : Fin
        ett.rounds) (_ : (↑terminalSlot : ℕ) + (1 : ℕ) = ett.rounds) (_ : (↑preterminalSlot : ℕ) <
        (↑terminalSlot : ℕ)) (terminalSupport : V) (hterminalSupport : terminalSupport ∈
        TreeSequenceVertexSet T) (Tj Tn seed TjPrime : TreeSequence G e0) (rho1 :
        PartialEdgeColoring E k) (supportColors : Finset (Fin k)) (gammaN deltaN : Fin k) (x : V)
        (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport) (Sum.inl
        x)) (_ : TashkinovClosure rho1 seed TjPrime) (_ : gammaN ≠ deltaN) (_ : p.IsPath) (_ :
        {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G rho1 gammaN deltaN (Sum.inl
        terminalSupport)) (_ : x ∉ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) (_ :
        (supportColors = (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
        terminalSupport).biUnion fun (s : Fin ett.rounds) ↦ ett.series.data.stored s.succ)) (_ :
        terminalSlot ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport
        terminalSupport) (_ : preterminalSlot ∈ (ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport terminalSupport).erase terminalSlot) (_ : ett.series.data.gamma
        terminalSlot.succ = some gammaN) (_ : ett.series.data.delta terminalSlot.succ = some
        deltaN) (u : V) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x)
        (Sum.inl u)) (_ : exitPath.IsPath) (_ : (2 : ℕ) ≤ exitPath.length) (_ : (
    ∀ y ∈ exitPath.support, y ∈ p.support)) (_ : (
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, Sum.inl w ∈ exitPath.support ↔
        w = u)) (_ : u ∈ TreeSequenceVertexSet TjPrime),
    ∀ beta ∈ MissingColors G rho1 u, beta ≠ deltaN →
    ∀ z ∈ TreeSequenceVertexSet Tj,
    ∀ (_ : Fin (Tj.length + (1 : ℕ))),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
        IsProperEdgeColoring G rho0 → (
    ∀ (f : E), TreeIncidentEdge TjPrime f → rho0 f = rho1 f) → gammaN ≠ beta → beta ∈
        MissingColors G rho0 u →
    ∀ (g : E), Incident G u g → Sum.inr g ∈ exitPath.support → rho1 g = some gammaN → rho0 g =
        some gammaN → {y : V ⊕ E | y ∈ exitPath.support} = TwoColorComponent G rho0 gammaN beta
        (Sum.inl u) := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSlot preterminalSlot _ _
      terminalSupport hterminalSupport Tj Tn seed TjPrime rho1 supportColors gammaN deltaN x p
      hclosure hgammaDelta hpath hcomponent hxOutside _ _ _ _ _ u exitPath hexitPath hexitLength
      hexitSupport hexitIntersection huPrime beta hbeta hbetaDelta z hz zPosition rho0
      hrho0Proper hrho0Fixed hgammaBeta hbetaRho0 g hug hgExit hgRho1 hgRho0
  let H1 := TwoColorIncidenceGraph G rho1 gammaN deltaN
  let H0 := TwoColorIncidenceGraph G rho0 gammaN beta
  have path_edge_data :
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)) (hq : q.IsPath) {e : E}, Sum.inr e ∈
        q.support →
    ∃ j : ℕ, 0 < j ∧ j < q.length ∧ q.getVert j = Sum.inr e ∧
    ∃ v w : V, q.getVert (j - 1) = Sum.inl v ∧ q.getVert (j + 1) = Sum.inl w ∧ v ≠ w ∧ G.ends e =
        s(v, w) := by
    exact @helper_path_edge_data_156 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett terminalSlot preterminalSlot (by assumption) (by assumption)
        terminalSupport hterminalSupport rho1 supportColors gammaN deltaN x (by assumption) (by
        assumption) (by assumption) (by assumption) (by assumption) u exitPath
  have path_incident_vertex_mem : ∀ {a b : V}
      (q : H1.Walk (Sum.inl a) (Sum.inl b)) (hq : q.IsPath)
      {e : E}, Sum.inr e ∈ q.support → ∀ {w : V}, Incident G w e →
        Sum.inl w ∈ q.support := by
    intro a b q hq e he w hwe
    obtain ⟨j, hjpos, hjlt, hj, v, t, hv, ht, hvt, hends⟩ :=
      path_edge_data q hq he
    have hwends : w ∈ s(v, t) := by
      rw [← hends]
      exact hwe
    simp only [Sym2.mem_iff] at hwends
    apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    rcases hwends with hwv | hwt
    · exact ⟨j - 1, by simpa [hwv] using hv, by omega⟩
    · exact ⟨j + 1, by simpa [hwt] using ht, by omega⟩
  have path_incident_end_last :
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)) (hq : q.IsPath) {e : E}, Sum.inr e ∈
        q.support → Incident G b e → q.getVert (q.length - 1) = Sum.inr e := by
    intro a b q hq e he hbe
    obtain ⟨j, hjpos, hjlt, hj, v, w, hv, hw, hvw, hends⟩ :=
      path_edge_data q hq he
    have hbends : b ∈ s(v, w) := by
      rw [← hends]
      exact hbe
    simp only [Sym2.mem_iff] at hbends
    rcases hbends with hbv | hbw
    · have hindex := hq.getVert_injOn
          (show j - 1 ≤ q.length by omega)
          (show q.length ≤ q.length by rfl)
          (by rw [hv, q.getVert_length, hbv])
      omega
    · have hindex := hq.getVert_injOn
          (show j + 1 ≤ q.length by omega)
          (show q.length ≤ q.length by rfl)
          (by rw [hw, q.getVert_length, hbw])
      have hjlast : j = q.length - 1 := by omega
      simpa [hjlast] using hj
  have hgLast : exitPath.getVert (exitPath.length - 1) = Sum.inr g :=
    path_incident_end_last exitPath hexitPath hgExit hug
  have exit_edge_color : ∀ e : E, Sum.inr e ∈ exitPath.support →
      (rho1 e = some gammaN ∨ rho1 e = some deltaN) →
        rho0 e = some gammaN ∨ rho0 e = some beta := by
    exact @helper_exit_edge_color_254 V E inferInstance inferInstance inferInstance G k e0 Tn
        TjPrime rho1 gammaN deltaN x hgammaDelta u exitPath hexitPath hexitIntersection beta
        hbetaDelta hrho0Fixed hgammaBeta g hgRho1 path_incident_vertex_mem path_incident_end_last
        hgLast
  have exit_adj_rho0 : ∀ i : ℕ, i < exitPath.length →
      H0.Adj (exitPath.getVert i) (exitPath.getVert (i + 1)) := by
    exact @helper_exit_adj_rho0_292 V E inferInstance inferInstance G k e0 TjPrime rho1 gammaN
        deltaN x u exitPath beta exit_edge_color
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨i, hi, hile⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
    have htoStart : ∀ j : ℕ, j ≤ exitPath.length →
        H0.connectedComponentMk (exitPath.getVert j) =
          H0.connectedComponentMk (exitPath.getVert 0) := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ih =>
          exact
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              (exit_adj_rho0 j (by omega))).symm.trans (ih (by omega))
    change H0.connectedComponentMk y = H0.connectedComponentMk (Sum.inl u)
    simpa only [hi, exitPath.getVert_length] using
      (htoStart i hile).trans (htoStart exitPath.length le_rfl).symm
  · exact @helper_branch_340 V E inferInstance inferInstance inferInstance inferInstance G k e0
      input T generating ett terminalSlot preterminalSlot terminalSupport Tj Tn seed TjPrime rho1
      gammaN deltaN x p hclosure hgammaDelta hpath hcomponent hxOutside u exitPath hexitPath
      hexitLength hexitSupport huPrime beta hbeta hbetaDelta z hz hrho0Proper hrho0Fixed
      hbetaRho0 g hug hgRho0 path_incident_end_last hgLast exit_adj_rho0
private theorem helper_htreeEdgeFixed_958.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ _ : Fin ett.rounds) (Tj _ TjPrime :
        TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k) (x u : V) (_ :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)) (beta : Fin k)
        (_ : Fin (Tj.length + (1 : ℕ))),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
    ∀ (_ : (
    ∀ w ∈ TreeSequenceVertexSet TjPrime, w ≠ u →
    ∀ (f : E), Incident G w f → mu0 f = rho1 f)) (a : Fin TjPrime.length), mu0 (TjPrime.edge a) =
        rho1 (TjPrime.edge a) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot preterminalSlot Tj seed TjPrime rho1
      gammaN deltaN x u exitPath beta zPosition rho0 mu0 hmuRho1PrimeFixed a
  obtain ⟨i, hi⟩ := TjPrime.attaches a
  let earlier : Fin (TjPrime.length + 1) :=
    Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ a.isLt))
  have hlaterSet : TjPrime.vertex a.succ ∈
      TreeSequenceVertexSet TjPrime := by
    simp [TreeSequenceVertexSet]
  have hearlierSet : TjPrime.vertex earlier ∈
      TreeSequenceVertexSet TjPrime := by
    simp [TreeSequenceVertexSet]
  have hlaterInc : Incident G (TjPrime.vertex a.succ)
      (TjPrime.edge a) := by
    change TjPrime.vertex a.succ ∈ G.ends (TjPrime.edge a)
    rw [hi]
    simp
  have hearlierInc : Incident G (TjPrime.vertex earlier)
      (TjPrime.edge a) := by
    change TjPrime.vertex earlier ∈ G.ends (TjPrime.edge a)
    rw [hi]
    simp [earlier]
  have hverticesNe : TjPrime.vertex a.succ ≠ TjPrime.vertex earlier := by
    apply TjPrime.vertex_injective.ne
    intro heq
    have hval := congrArg Fin.val heq
    simp [earlier] at hval
    omega
  by_cases hlu : TjPrime.vertex a.succ = u
  · exact hmuRho1PrimeFixed (TjPrime.vertex earlier) hearlierSet
      (by intro heu; exact hverticesNe (hlu.trans heu.symm))
      (TjPrime.edge a) hearlierInc
  · exact hmuRho1PrimeFixed (TjPrime.vertex a.succ) hlaterSet hlu
      (TjPrime.edge a) hlaterInc

private theorem helper_hE5_992.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] [DecidableEq V]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (terminalSupport : V) (seed TjPrime :
        TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (supportColors : Finset (Fin k))
        (gammaN deltaN : Fin k) (_ : (
    ∀ v ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport, MissingColors G rho1 v ∩
        supportColors = ∅)) (_ : MissingColors G rho1 terminalSupport ∩ supportColors =
        { deltaN }) (_ : deltaN ∈ supportColors) (_ : terminalSupport ∈ TreeSequenceVertexSet
        TjPrime) (u : V) (beta : Fin k) (_ : u ≠ terminalSupport) (_ : u ∈ (TreeSequenceVertexSet
        TjPrime).erase terminalSupport) (_ : TreeMissingColors rho1 TjPrime ∩ supportColors =
        { deltaN }) (_ : (
    ∀ (a : Fin TjPrime.length) (_ : seed.length ≤ (↑a : ℕ)),
    ∀ c ∈ supportColors \ { deltaN }, rho1 (TjPrime.edge a) ≠ some c)),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
    ∀ (_ : (
    ∀ w ∈ TreeSequenceVertexSet TjPrime, w ≠ u → MissingColors G mu0 w = MissingColors G rho1 w))
        (_ : (
    ∀ (a : Fin TjPrime.length), mu0 (TjPrime.edge a) = rho1 (TjPrime.edge a))),
        (((TreeSequenceVertexSet TjPrime).erase u).biUnion fun (v : V) ↦ MissingColors G mu0 v) ∩
        supportColors = { deltaN } ∧ MissingColors G mu0 terminalSupport ∩ supportColors =
        { deltaN } ∧
    ∀ (a : Fin TjPrime.length), seed.length ≤ (↑a : ℕ) →
    ∀ c ∈ supportColors \ { deltaN }, mu0 (TjPrime.edge a) ≠ some c := by
  classical
  intro V E _ _ _ G k e0 terminalSupport seed TjPrime rho1 supportColors gammaN deltaN hcaseTwo
      hterminalColors hdeltaSupport hterminalPrime u beta huTerminal huErase hprimeMissing
      hprimeEdges rho0 mu0 hmissingPrime htreeEdgeFixed
  let _ := Fintype.ofFinite V
  constructor
  · apply Finset.ext
    intro c
    constructor
    · intro hc
      obtain ⟨hcm, hcs⟩ := Finset.mem_inter.mp hc
      obtain ⟨v, hvErase, hcMu⟩ := Finset.mem_biUnion.mp hcm
      have hv := Finset.mem_of_mem_erase hvErase
      have hvu := (Finset.mem_erase.mp hvErase).1
      have hcRho : c ∈ MissingColors G rho1 v := by
        rw [← hmissingPrime v hv hvu]
        exact hcMu
      have hcTree : c ∈ TreeMissingColors rho1 TjPrime := by
        unfold TreeMissingColors
        exact Finset.mem_biUnion.mpr ⟨v, hv, hcRho⟩
      have hcSingle : c ∈ ({deltaN} : Finset (Fin k)) := by
        rw [← hprimeMissing]
        exact Finset.mem_inter.mpr ⟨hcTree, hcs⟩
      exact hcSingle
    · intro hc
      have hcd : c = deltaN := by simpa using hc
      subst c
      have hdBoth : deltaN ∈
          TreeMissingColors rho1 TjPrime ∩ supportColors := by
        rw [hprimeMissing]
        simp
      have hdTree := (Finset.mem_inter.mp hdBoth).1
      unfold TreeMissingColors at hdTree
      obtain ⟨v, hv, hdv⟩ := Finset.mem_biUnion.mp hdTree
      have hvu : v ≠ u := by
        intro hvu
        subst v
        have hboth : deltaN ∈ MissingColors G rho1 u ∩ supportColors :=
          Finset.mem_inter.mpr ⟨hdv, hdeltaSupport⟩
        rw [hcaseTwo u huErase] at hboth
        simp at hboth
      apply Finset.mem_inter.mpr
      refine ⟨Finset.mem_biUnion.mpr ⟨v,
        Finset.mem_erase.mpr ⟨hvu, hv⟩, ?_⟩, hdeltaSupport⟩
      rw [hmissingPrime v hv hvu]
      exact hdv
  · constructor
    · rw [hmissingPrime terminalSupport hterminalPrime (Ne.symm huTerminal)]
      exact hterminalColors
    · intro a ha c hc hbad
      apply hprimeEdges a ha c hc
      rw [← htreeEdgeFixed a]
      exact hbad

private theorem helper_hE4_1070.{u_1, u_2} :
    helperHE41070Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSlot terminalSupport hterminalSupport
      Tn TjPrime rho1 supportColors gammaN deltaN hb4 hsupportColors hdeltaEarlier hsupportOrder
      u huOutside beta hbetaSupport z rho0 mu0 component_edge_avoids hmuRho0Fixed rho0_unaffected
      s gammaS deltaS hs hgammaS hdeltaS
  obtain ⟨hgammaSSupport, hdeltaSSupport⟩ :=
    hsupportColors s gammaS deltaS hs hgammaS hdeltaS
  obtain ⟨hdeltaNGammaS, hdeltaNDeltaS⟩ :=
    hdeltaEarlier s gammaS deltaS hs hgammaS hdeltaS
  have hgammaSBeta : gammaS ≠ beta := by
    intro h
    exact hbetaSupport (h ▸ hgammaSSupport)
  have hdeltaSBeta : deltaS ≠ beta := by
    intro h
    exact hbetaSupport (h ▸ hdeltaSSupport)
  have hgammaSDeltaN : gammaS ≠ deltaN := Ne.symm hdeltaNGammaS
  have hdeltaSDeltaN : deltaS ≠ deltaN := Ne.symm hdeltaNDeltaS
  obtain ⟨hgammaSDeltaS, hkind, hchosen, epsilon, hsepsilon,
      hepsilonKind, hbetweenKinds, hstrong⟩ :=
    hb4 s gammaS deltaS hs hgammaS hdeltaS
  refine ⟨hgammaSDeltaS, hkind, hchosen, epsilon, hsepsilon,
    hepsilonKind, hbetweenKinds, ?_⟩
  intro v hvTree hvTerminal
  obtain ⟨hcycleRho1, hterminalAvoid, hepsilonContain⟩ :=
    hstrong v hvTree hvTerminal
  let H1 := TwoColorIncidenceGraph G rho1 gammaS deltaS
  let HM := TwoColorIncidenceGraph G mu0 gammaS deltaS
  let C1 := TwoColorComponent G rho1 gammaS deltaS (Sum.inl v)
  let CM := TwoColorComponent G mu0 gammaS deltaS (Sum.inl v)
  have hverticesTn : ∀ w : V, Sum.inl w ∈ C1 →
      w ∈ TreeSequenceVertexSet Tn := by
    intro w hw
    exact hsupportOrder s gammaS deltaS hs hgammaS hdeltaS
      v hvTree hvTerminal w hw
  have hedgeAvoidsK : ∀ e : E, Sum.inr e ∈ C1 →
      Sum.inr e ∉ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    intro e heC heK
    have heSupport : Sum.inr e ∈ H1.support := by
      apply SimpleGraph.mem_support_of_reachable
        (G := H1) (u := Sum.inr e) (v := Sum.inl v)
      · simp
      · exact SimpleGraph.ConnectedComponent.eq.mp heC
    obtain ⟨y, hy⟩ := H1.mem_support.mp heSupport
    cases y with
    | inl w =>
        have hwC : Sum.inl w ∈ C1 := by
          change H1.connectedComponentMk (Sum.inl w) =
            H1.connectedComponentMk (Sum.inl v)
          change H1.connectedComponentMk (Sum.inr e) =
            H1.connectedComponentMk (Sum.inl v) at heC
          exact
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hy).symm.trans heC
        have hwTn := hverticesTn w hwC
        exact component_edge_avoids w
          (Finset.mem_union.mpr (Or.inl hwTn))
          (by intro hwu; subst w; exact huOutside hwTn) e hy.1 heK
    | inr f => simp [H1, TwoColorIncidenceGraph] at hy
  have hadjIff : ∀ {a b : Sum V E}, a ∈ C1 →
      (HM.Adj a b ↔ H1.Adj a b) := by
    intro a b haC
    cases a with
    | inl w =>
        cases b with
        | inl z => simp [HM, H1, TwoColorIncidenceGraph]
        | inr e =>
            have hwTn := hverticesTn w haC
            simp only [HM, H1, TwoColorIncidenceGraph]
            constructor
            · rintro ⟨hwe, hec⟩
              have hfixed := hmuRho0Fixed w
                (Finset.mem_union.mpr (Or.inl hwTn))
                (by intro hwu; subst w; exact huOutside hwTn) e hwe
              rw [hfixed] at hec
              rcases hec with hec | hec
              · exact ⟨hwe, Or.inl
                  ((rho0_unaffected gammaS hgammaSBeta hgammaSDeltaN e).mp hec)⟩
              · exact ⟨hwe, Or.inr
                  ((rho0_unaffected deltaS hdeltaSBeta hdeltaSDeltaN e).mp hec)⟩
            · rintro ⟨hwe, hec⟩
              have hfixed := hmuRho0Fixed w
                (Finset.mem_union.mpr (Or.inl hwTn))
                (by intro hwu; subst w; exact huOutside hwTn) e hwe
              rw [hfixed]
              rcases hec with hec | hec
              · exact ⟨hwe, Or.inl
                  ((rho0_unaffected gammaS hgammaSBeta hgammaSDeltaN e).mpr hec)⟩
              · exact ⟨hwe, Or.inr
                  ((rho0_unaffected deltaS hdeltaSBeta hdeltaSDeltaN e).mpr hec)⟩
    | inr e =>
        cases b with
        | inl w =>
            have heK := hedgeAvoidsK e haC
            have hfixed : mu0 e = rho0 e := by
              simp [mu0, TwoColorComponentSwap, heK]
            simp only [HM, H1, TwoColorIncidenceGraph]
            constructor
            · rintro ⟨hwe, hec⟩
              rw [hfixed] at hec
              rcases hec with hec | hec
              · exact ⟨hwe, Or.inl
                  ((rho0_unaffected gammaS hgammaSBeta hgammaSDeltaN e).mp hec)⟩
              · exact ⟨hwe, Or.inr
                  ((rho0_unaffected deltaS hdeltaSBeta hdeltaSDeltaN e).mp hec)⟩
            · rintro ⟨hwe, hec⟩
              rw [hfixed]
              rcases hec with hec | hec
              · exact ⟨hwe, Or.inl
                  ((rho0_unaffected gammaS hgammaSBeta hgammaSDeltaN e).mpr hec)⟩
              · exact ⟨hwe, Or.inr
                  ((rho0_unaffected deltaS hdeltaSBeta hdeltaSDeltaN e).mpr hec)⟩
        | inr f => simp [HM, H1, TwoColorIncidenceGraph]
  have hcomponentEq : CM = C1 := by
    ext y
    constructor
    · intro hy
      have hreach : HM.Reachable (Sum.inl v) y := by
        apply SimpleGraph.ConnectedComponent.exact
        change HM.connectedComponentMk y = HM.connectedComponentMk (Sum.inl v)
          at hy
        exact hy.symm
      rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
      clear hy
      have hyC1 : y ∈ C1 := by
        induction hreach with
        | refl => rfl
        | tail hreach hlast ih =>
            have hlast1 : H1.Adj _ _ := (hadjIff ih).mp hlast
            change H1.connectedComponentMk _ =
              H1.connectedComponentMk (Sum.inl v)
            exact
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hlast1).symm.trans ih
      exact hyC1
    · intro hy
      have hreach : H1.Reachable (Sum.inl v) y := by
        apply SimpleGraph.ConnectedComponent.exact
        change H1.connectedComponentMk y = H1.connectedComponentMk (Sum.inl v)
          at hy
        exact hy.symm
      rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
      clear hy
      have hpair : y ∈ C1 ∧ y ∈ CM := by
        induction hreach with
        | refl => exact ⟨rfl, rfl⟩
        | tail hreach hlast ih =>
            have hnextC1 :=
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hlast).symm.trans ih.1
            have hlastM : HM.Adj _ _ := (hadjIff ih.1).mpr hlast
            have hnextCM :=
              (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                hlastM).symm.trans ih.2
            exact ⟨hnextC1, hnextCM⟩
      exact hpair.2
  unfold TwoColorComponentCycle at hcycleRho1 ⊢
  obtain ⟨cycle, hcycleSupport⟩ := hcycleRho1
  have hedgeTransfer : ∀ ed ∈ cycle.walk.edges, ed ∈ HM.edgeSet := by
    intro ed hed
    induction ed using Sym2.inductionOn with
    | _ a b =>
        have hab1 : H1.Adj a b := cycle.walk.adj_of_mem_edges hed
        have haSupport : a ∈ cycle.walk.support :=
          cycle.walk.fst_mem_support_of_mem_edges hed
        have haC : a ∈ C1 := (hcycleSupport a).mp haSupport
        exact (hadjIff haC).mpr hab1
  let walkM := cycle.walk.transfer HM hedgeTransfer
  let cycleM : TwoColorCycle G mu0 gammaS deltaS :=
    { base := cycle.base
      walk := walkM
      isCycle := cycle.isCycle.transfer hedgeTransfer }
  refine ⟨⟨cycleM, ?_⟩, ?_, ?_⟩
  · intro y
    change y ∈ walkM.support ↔ y ∈ CM
    rw [SimpleGraph.Walk.support_transfer, hcomponentEq]
    exact hcycleSupport y
  · intro hterminalM
    apply hterminalAvoid
    change Sum.inl terminalSupport ∈ C1
    rw [← hcomponentEq]
    exact hterminalM
  · intro w hwM
    apply hepsilonContain w
    change Sum.inl w ∈ C1
    rw [← hcomponentEq]
    exact hwM

private theorem helper_component_edge_avoids_1276.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] [DecidableEq V]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn TjPrime : TreeSequence G e0) (rho1 :
        PartialEdgeColoring E k) (gammaN deltaN : Fin k) (u : V) (beta : Fin k),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    ∀ (_ : (
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, Sum.inl w ∈ TwoColorComponent
        G rho0 gammaN beta (Sum.inl u) ↔ w = u)),
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, w ≠ u →
    ∀ (f : E), Incident G w f → Sum.inr f ∉ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
  classical
  intro V E _ _ _ G k e0 Tn TjPrime rho1 gammaN deltaN u beta rho0 hcomponentIntersection w hw hwu f
      hwf hf
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  let H := TwoColorIncidenceGraph G rho0 gammaN beta
  have hfSupport : Sum.inr f ∈ H.support := by
    apply SimpleGraph.mem_support_of_reachable
      (G := H) (u := Sum.inr f) (v := Sum.inl u)
    · simp
    · exact SimpleGraph.ConnectedComponent.eq.mp hf
  obtain ⟨y, hy⟩ := H.mem_support.mp hfSupport
  have hfColor : rho0 f = some gammaN ∨ rho0 f = some beta := by
    cases y with
    | inl y => exact hy.2
    | inr y => simp [H, TwoColorIncidenceGraph] at hy
  have hadj : H.Adj (Sum.inl w) (Sum.inr f) := by
    simpa [H, TwoColorIncidenceGraph] using And.intro hwf hfColor
  have hwComponent :
      Sum.inl w ∈ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    change H.connectedComponentMk (Sum.inl w) =
      H.connectedComponentMk (Sum.inl u)
    change H.connectedComponentMk (Sum.inr f) =
      H.connectedComponentMk (Sum.inl u) at hf
    exact
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hf
  exact hwu ((hcomponentIntersection w hw).mp hwComponent)

private theorem helper_before_seed_1330.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (_ _ : Fin ett.rounds) (terminalSupport :
        V) (Tj seed : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k)
        (x : V), TreeSequenceInitialSegment seed Tj → seed.vertex (Fin.last seed.length) =
        terminalSupport →
    ∀ (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj) (u : V) (_ :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin
        (Tj.length + (1 : ℕ))),
    ∀ w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj, w ∈ TreeSequenceVertexSet seed := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSlot preterminalSlot terminalSupport Tj
      seed rho1 gammaN deltaN x hseedJ hseedTerminal hterminalTj u exitPath zPosition w hw
  unfold TreeVerticesBefore at hw
  obtain ⟨hwJ, i, j, hiw, hjt, hij⟩ := Finset.mem_filter.mp hw
  obtain ⟨hlen, hvertices, hedges⟩ := hseedJ
  have hjLast : j = Fin.castLE (Nat.succ_le_succ hlen)
      (Fin.last seed.length) := by
    apply Tj.vertex_injective
    rw [hjt, hvertices, hseedTerminal]
  have hiBound : i.val < seed.length + 1 := by
    have hjVal : j.val = seed.length := by
      simpa using congrArg Fin.val hjLast
    rw [hjVal] at hij
    omega
  let iSeed : Fin (seed.length + 1) := ⟨i.val, hiBound⟩
  have hiCast : Fin.castLE (Nat.succ_le_succ hlen) iSeed = i := by
    apply Fin.ext
    rfl
  simp only [TreeSequenceVertexSet, Finset.mem_image]
  refine ⟨iSeed, Finset.mem_univ _, ?_⟩
  rw [← hvertices iSeed, hiCast]
  exact hiw

private theorem helper_initial_trans_1331.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {e0 : E}
        {A B C : TreeSequence G e0}, TreeSequenceInitialSegment A B → TreeSequenceInitialSegment B
        C → TreeSequenceInitialSegment A C := by
  classical
  intro V E G e0 A B C hAB hBC
  obtain ⟨hABlen, hABvertices, hABedges⟩ := hAB
  obtain ⟨hBClen, hBCvertices, hBCedges⟩ := hBC
  refine ⟨hABlen.trans hBClen, ?_, ?_⟩
  · intro i
    calc
      C.vertex (Fin.castLE (Nat.succ_le_succ (hABlen.trans hBClen)) i) =
          C.vertex (Fin.castLE (Nat.succ_le_succ hBClen)
            (Fin.castLE (Nat.succ_le_succ hABlen) i)) := by
              congr 1
      _ = B.vertex (Fin.castLE (Nat.succ_le_succ hABlen) i) :=
        hBCvertices _
      _ = A.vertex i := hABvertices i
  · intro i
    calc
      C.edge (Fin.castLE (hABlen.trans hBClen) i) =
          C.edge (Fin.castLE hBClen (Fin.castLE hABlen i)) := by
            congr 1
      _ = B.edge (Fin.castLE hABlen i) := hBCedges _
      _ = A.edge i := hABedges i

private theorem helper_hmu0One_1442.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN :
        Fin k) (u : V) (beta : Fin k) (_ : beta ≠ gammaN),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
    ∀ (_ : IsOneEdgeUncolored rho0 e0), IsOneEdgeUncolored mu0 e0 := by
  classical
  intro V E _ _ G k e0 TjPrime rho1 gammaN deltaN u beta hbetaGamma rho0 mu0 hrho0One
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  unfold IsOneEdgeUncolored at hrho0One ⊢
  constructor
  · simp [mu0, TwoColorComponentSwap, hrho0One.1]
  · intro f hfe
    obtain ⟨c, hc⟩ := hrho0One.2 f hfe
    have hne : mu0 f ≠ none := by
      by_cases hK : Sum.inr f ∈
          TwoColorComponent G rho0 gammaN beta (Sum.inl u)
      · by_cases hcg : c = gammaN
        · simp [mu0, TwoColorComponentSwap, hK, hc, hcg]
        · by_cases hcb : c = beta
          · simp [mu0, TwoColorComponentSwap, hK, hc, hcb,
              hbetaGamma]
          · simp [mu0, TwoColorComponentSwap, hK, hc, hcg, hcb]
      · simp [mu0, TwoColorComponentSwap, hK, hc]
    obtain ⟨d, hd⟩ := Option.ne_none_iff_exists.mp hne
    exact ⟨d, hd.symm⟩

private theorem helper_missing_eq_of_incident_eq_1524.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] {G : LooplessMultigraph V E}
      {k : ℕ} {e0 : E} (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k)
      (gammaN deltaN : Fin k) (u : V) (beta : Fin k),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let mu0 : PartialEdgeColoring E k :=
      TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
    ∀ (w : V) (_ : (∀ (f : E) (_ : Incident G w f), mu0 f = rho1 f)),
    MissingColors G mu0 w = MissingColors G rho1 w := by
  classical
  intro V E _ _ G k e0 TjPrime rho1 gammaN deltaN u beta rho0 mu0 w hfixed
  let _ := Fintype.ofFinite V
  apply Finset.ext
  intro c
  simp only [MissingColors, Finset.mem_sdiff, Finset.mem_univ, true_and,
    PresentColors, Finset.mem_filter]
  constructor
  · intro hnew hold
    obtain ⟨f, hwf, hfc⟩ := hold
    exact hnew ⟨f, hwf, (hfixed f hwf).trans hfc⟩
  · intro hold hnew
    obtain ⟨f, hwf, hfc⟩ := hnew
    exact hold ⟨f, hwf, (hfixed f hwf).symm.trans hfc⟩

private theorem helper_hE1_1548.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (terminalSupport : V) (Tj seed TjPrime : TreeSequence G e0) (phiJ rho1 :
        PartialEdgeColoring E k) (Dprev : Finset (Fin k)) (gammaN deltaN : Fin k) (hterminalTj :
        terminalSupport ∈ TreeSequenceVertexSet Tj) (_ : StableColoringBeforeVertex Tj
        terminalSupport hterminalTj Dprev phiJ rho1) (u : V) (beta : Fin k) (_ : u ∉
        TreeSequenceVertexSet seed),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let mu0 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
    ∀ (_ : (
    ∀ w ∈ TreeSequenceVertexSet TjPrime, w ≠ u →
    ∀ (f : E), Incident G w f → mu0 f = rho1 f)) (_ : (
    ∀ (w : V) (_ : (
    ∀ (f : E) (_ : Incident G w f), mu0 f = rho1 f)), MissingColors G mu0 w = MissingColors G rho1
        w)) (_ : (
    ∀ w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj, w ∈ TreeSequenceVertexSet seed)) (_ :
        (
    ∀ w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj, w ∈ TreeSequenceVertexSet TjPrime)),
        StableColoringBeforeVertex Tj terminalSupport hterminalTj Dprev phiJ mu0 := by
  classical
  intro V E _ _ G k e0 terminalSupport Tj seed TjPrime phiJ rho1 Dprev gammaN deltaN hterminalTj hb1
      u beta huSeed rho0 mu0 hmuRho1PrimeFixed missing_eq_of_incident_eq before_seed before_prime
  let _ := Fintype.ofFinite V
  unfold StableColoringBeforeVertex at hb1 ⊢
  have before_ne : ∀ w : V,
      w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj → w ≠ u := by
    intro w hw hwu
    subst w
    exact huSeed (before_seed u hw)
  constructor
  · intro f hf hcolor
    obtain ⟨w, hw, hwf⟩ := hf
    rw [hmuRho1PrimeFixed w (before_prime w hw) (before_ne w hw) f hwf]
    exact hb1.1 f ⟨w, hw, hwf⟩ hcolor
  · intro w hw
    exact (missing_eq_of_incident_eq w
      (hmuRho1PrimeFixed w (before_prime w hw) (before_ne w hw))).trans
        (hb1.2 w hw)

private theorem helper_continuation_1644.{u_1, u_2} :
    helperContinuation1644Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett terminalSlot preterminalSlot _ _
      terminalSupport hterminalSupport Tj Tn seed TjPrime phiJ rho1 Dprev supportColors gammaN
      deltaN x p hTjN hseedJ hseedPrime hseedTerminal hterminalTj hclosure hprimeElementary
      hcaseTwo hterminalColors hdeltaSupport hgammaDelta hdeltaMissing hpath hcomponent hxOutside
      hb1 hb2Missing haugmentation hb2Edges hdeltaPhiJ _ _ _ hgammaIdentity _ _ hb4
      hsupportColors hdeltaEarlier hsupportOrder initial_subset hterminalPrime u exitPath
      hexitPath hexitLength hexitSupport hexitIntersection hexitBoundary huPrime huOutside beta
      hbeta huTerminal huErase hbetaSupport hbetaDelta hbetaGamma huSeed z hz zPosition
      hzPosition hzAfter hzBefore hzEdges hprimeMissing hprimeEdges rho0 mu0 hrho0Proper hrho0One
      hrho0Stable hrho0Fixed hgammaBeta
  have hmu0Proper : IsProperEdgeColoring G mu0 :=
    TwoColorComponentSwapProper G rho0 gammaN beta hgammaBeta
      hrho0Proper (Sum.inl u)
  have hmu0One : IsOneEdgeUncolored mu0 e0 := by
    exact @helper_hmu0One_1442 V E inferInstance inferInstance G k e0 TjPrime rho1 gammaN deltaN
        u beta hbetaGamma hrho0One
  have hbetaRho0 : beta ∈ MissingColors G rho0 u := by
    rw [hrho0Stable.2 u huPrime]
    exact hbeta
  obtain ⟨g, hgBoundary, hug, hgExit⟩ := hexitBoundary
  have hgRho1 : rho1 g = some gammaN :=
    (Finset.mem_filter.mp hgBoundary).2
  have hgRho0 : rho0 g = some gammaN := by
    rw [hrho0Fixed g ⟨u, huPrime, hug⟩]
    exact hgRho1
  have hgComponent : Sum.inr g ∈
      TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    change (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
        (Sum.inr g) =
      (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
        (Sum.inl u)
    have hadj : (TwoColorIncidenceGraph G rho0 gammaN beta).Adj
        (Sum.inl u) (Sum.inr g) := ⟨hug, Or.inl hgRho0⟩
    exact
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
  have hgMu0 : mu0 g = some beta := by
    simp [mu0, TwoColorComponentSwap, hgComponent, hgRho0]
  have hbetaMu0 : beta ∉ MissingColors G mu0 u := by
    intro hb
    have hbPresent : beta ∉ PresentColors G mu0 u := by
      simpa [MissingColors] using hb
    apply hbPresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨g, hug, hgMu0⟩
  have hgammaMu0 : gammaN ∈ MissingColors G mu0 u := by
    exact @helper_hgammaMu0_408 V E inferInstance inferInstance G k e0 TjPrime rho1 gammaN deltaN
        u beta hbetaGamma hgammaBeta hbetaRho0
  have hE3 :
      ett.series.data.delta preterminalSlot.succ = some gammaN ∧
        gammaN ∈ MissingColors G mu0 u ∧
        beta ∉ MissingColors G mu0 u :=
    ⟨hgammaIdentity, hgammaMu0, hbetaMu0⟩
  have hcomponentExit :
      {y : Sum V E | y ∈ exitPath.support} =
        TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    exact @helper_hcomponentExit_447 V E inferInstance inferInstance inferInstance inferInstance
        G k e0 input T generating ett terminalSlot preterminalSlot (by assumption) (by
        assumption) terminalSupport hterminalSupport Tj Tn seed TjPrime rho1 supportColors gammaN
        deltaN x p hclosure hgammaDelta hpath hcomponent hxOutside (by assumption) (by
        assumption) (by assumption) (by assumption) (by assumption) u exitPath hexitPath
        hexitLength hexitSupport hexitIntersection huPrime beta hbeta hbetaDelta z hz zPosition
        hrho0Proper hrho0Fixed hgammaBeta hbetaRho0 g hug hgExit hgRho1 hgRho0
  have hcomponentIntersection :
    ∀ w : V, w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime → (Sum.inl w ∈
        TwoColorComponent G rho0 gammaN beta (Sum.inl u) ↔ w = u) := by
    intro w hw
    rw [← hcomponentExit]
    exact hexitIntersection w hw
  have component_edge_avoids :
    ∀ (w : V), w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime → w ≠ u →
    ∀ f : E, Incident G w f → Sum.inr f ∉ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    exact @helper_component_edge_avoids_1276 V E inferInstance inferInstance inferInstance G k e0
        Tn TjPrime rho1 gammaN deltaN u beta hcomponentIntersection
  have hmuRho0Fixed : ∀ (w : V),
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      w ≠ u → ∀ f : E, Incident G w f → mu0 f = rho0 f := by
    intro w hw hwu f hwf
    have hf := component_edge_avoids w hw hwu f hwf
    simp [mu0, TwoColorComponentSwap, hf]
  have hmuRho1PrimeFixed : ∀ (w : V),
      w ∈ TreeSequenceVertexSet TjPrime → w ≠ u →
      ∀ f : E, Incident G w f → mu0 f = rho1 f := by
    intro w hw hwu f hwf
    rw [hmuRho0Fixed w (Finset.mem_union.mpr (Or.inr hw)) hwu f hwf]
    exact hrho0Fixed f ⟨w, hw, hwf⟩
  have missing_eq_of_incident_eq : ∀ (w : V),
      (∀ f : E, Incident G w f → mu0 f = rho1 f) →
      MissingColors G mu0 w = MissingColors G rho1 w := by
    exact @helper_missing_eq_of_incident_eq_1524 V E inferInstance inferInstance G k e0 TjPrime
        rho1 gammaN deltaN u beta
  have before_seed : ∀ w : V,
      w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj →
      w ∈ TreeSequenceVertexSet seed := by
    exact @helper_before_seed_1330 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett terminalSlot preterminalSlot terminalSupport Tj seed rho1 gammaN deltaN x
        hseedJ hseedTerminal hterminalTj u exitPath zPosition
  have before_prime : ∀ w : V,
      w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj →
      w ∈ TreeSequenceVertexSet TjPrime := by
    intro w hw
    exact initial_subset hseedPrime (before_seed w hw)
  have hE1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ mu0 := by
    exact @helper_hE1_1548 V E inferInstance inferInstance G k e0 terminalSupport Tj seed TjPrime
        phiJ rho1 Dprev gammaN deltaN hterminalTj hb1 u beta huSeed hmuRho1PrimeFixed
        missing_eq_of_incident_eq before_seed before_prime
  have hmissingPrime : ∀ w : V,
      w ∈ TreeSequenceVertexSet TjPrime → w ≠ u →
      MissingColors G mu0 w = MissingColors G rho1 w := by
    intro w hw hwu
    exact missing_eq_of_incident_eq w (hmuRho1PrimeFixed w hw hwu)
  have htreeEdgeFixed : ∀ a : Fin TjPrime.length,
      mu0 (TjPrime.edge a) = rho1 (TjPrime.edge a) := by
    exact @helper_htreeEdgeFixed_958 V E inferInstance inferInstance inferInstance G k e0 input T
        generating ett terminalSlot preterminalSlot Tj seed TjPrime rho1 gammaN deltaN x u
        exitPath beta zPosition hmuRho1PrimeFixed
  have hE5 :
      ((TreeSequenceVertexSet TjPrime).erase u).biUnion
          (fun v => MissingColors G mu0 v) ∩ supportColors = {deltaN} ∧
        MissingColors G mu0 terminalSupport ∩ supportColors = {deltaN} ∧
        ∀ a : Fin TjPrime.length, seed.length ≤ a.val →
          ∀ c : Fin k, c ∈ supportColors \ {deltaN} →
            mu0 (TjPrime.edge a) ≠ some c := by
    exact @helper_hE5_992 V E inferInstance inferInstance inferInstance G k e0 terminalSupport
        seed TjPrime rho1 supportColors gammaN deltaN hcaseTwo hterminalColors hdeltaSupport
        hterminalPrime u beta huTerminal huErase hprimeMissing hprimeEdges hmissingPrime
        htreeEdgeFixed
  have rho0_unaffected : ∀ (c : Fin k), c ≠ beta → c ≠ deltaN →
      ∀ f : E, (rho0 f = some c ↔ rho1 f = some c) := by
    exact @SharedFacts.ExtensionBaseClaim45Singleton.rho0_unaffected V E inferInstance
        inferInstance G k e0 TjPrime rho1 deltaN
        beta
  have hE4 :
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ (ExtensionBaseSupportClass ett
        terminalSupport hterminalSupport terminalSupport).erase terminalSlot →
        ett.series.data.gamma s.succ = some gammaS → ett.series.data.delta s.succ = some deltaS →
        ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS := by
    exact @helper_hE4_1070 V E inferInstance inferInstance inferInstance inferInstance G k e0
        input T generating ett terminalSlot terminalSupport hterminalSupport Tn TjPrime rho1
        supportColors gammaN deltaN hb4 hsupportColors hdeltaEarlier hsupportOrder u huOutside
        beta hbetaSupport z component_edge_avoids hmuRho0Fixed rho0_unaffected
  have hE2 := P2966_T1_OutsideSwapPrefixEffects Tn Tj seed TjPrime
    phiJ rho1 rho0 mu0 deltaN beta terminalSupport u z zPosition
    hTjN hterminalPrime hclosure.2 hprimeElementary hbetaDelta hbeta
    hdeltaMissing hb2Missing haugmentation hb2Edges hdeltaPhiJ hz
    hzPosition hzAfter huPrime huOutside hzBefore hzEdges rfl hrho0Fixed hmuRho0Fixed
    hmissingPrime htreeEdgeFixed rho0_unaffected
  exact ⟨hmu0Proper, hmu0One, hE1, hE2, hE3, hE4, hE5⟩

theorem ExtensionBaseClaim46 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSlot preterminalSlot : Fin ett.rounds)
    (_ : terminalSlot.val + 1 = ett.rounds)
    (_ : preterminalSlot.val < terminalSlot.val)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (Tj Tn seed TjPrime : TreeSequence G e0)
    (phiJ phiN sigmaN rho1 : PartialEdgeColoring E k)
    (Dprev controlled restorationColors supportColors : Finset (Fin k))
    (gammaFirst gammaN deltaN : Fin k) (fN : E) (x : V)
    (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
      (Sum.inl terminalSupport) (Sum.inl x))
    (hphiNProper : IsProperEdgeColoring G phiN)
    (hphiNOne : IsOneEdgeUncolored phiN e0)
    (hsigmaProper : IsProperEdgeColoring G sigmaN)
    (hsigmaOne : IsOneEdgeUncolored sigmaN e0)
    (hrhoProper : IsProperEdgeColoring G rho1)
    (hrhoOne : IsOneEdgeUncolored rho1 e0)
    (hTjN : TreeSequenceInitialSegment Tj Tn)
    (hseedJ : TreeSequenceInitialSegment seed Tj)
    (hseedPrime : TreeSequenceInitialSegment seed TjPrime)
    (hseedTerminal : seed.vertex (Fin.last seed.length) = terminalSupport)
    (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet Tj)
    (hterminalSeed : terminalSupport ∈ TreeSequenceVertexSet seed)
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hprimeElementary : ColoredVertexSetElementary G rho1
      (TreeSequenceVertexSet TjPrime))
    (hcaseTwo : ∀ v : V,
      v ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport →
      MissingColors G rho1 v ∩ supportColors = ∅)
    (hterminalColors :
      MissingColors G rho1 terminalSupport ∩ supportColors = {deltaN})
    (hgammaSupport : gammaN ∈ supportColors)
    (hdeltaSupport : deltaN ∈ supportColors)
    (hgammaFirstSupport : gammaFirst ∈ supportColors)
    (hgammaDelta : gammaN ≠ deltaN)
    (hsigmaStable : StableColoring Tn controlled phiN sigmaN)
    (hgammaControlled : gammaN ∈ controlled)
    (hdeltaControlled : deltaN ∈ controlled)
    (hb3 : ∀ f : E, rho1 f ≠ sigmaN f →
      f ∉ InternalEdges G (TreeSequenceVertexSet Tj) ∧
        ∃ c d : Fin k, sigmaN f = some c ∧ rho1 f = some d ∧
          c ∈ restorationColors ∧ d ∈ restorationColors)
    (hgammaRestored : gammaN ∉ restorationColors)
    (hdeltaRestored : deltaN ∉ restorationColors)
    (hgammaBoundary :
      BoundaryColorEdges G phiN (TreeSequenceVertexSet Tn) gammaN = {fN})
    (hdeltaLocation : ∀ f ∈ BoundaryColorEdges G phiN
        (TreeSequenceVertexSet Tn) deltaN,
      ∃ w ∈ TreeSequenceVertexSet seed, Incident G w f)
    (hdeltaMissing : deltaN ∈ MissingColors G rho1 terminalSupport)
    (hpath : p.IsPath)
    (hcomponent : {y : Sum V E | y ∈ p.support} =
      TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport))
    (hxOutside : x ∉
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
    (htwoN : ∃ w ∈ TreeSequenceVertexSet Tn,
      w ≠ terminalSupport ∧ Sum.inl w ∈ p.support)
    (hfNterminal : Incident G terminalSupport fN)
    (hb1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ rho1)
    (hb2Missing : ∀ v : V,
      v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport →
      MissingColors G rho1 v = MissingColors G phiJ v)
    (hterminalInclusion : MissingColors G phiJ terminalSupport ⊆
      MissingColors G rho1 terminalSupport ∪ {gammaFirst})
    (haugmentation : TashkinovAugmentationSequence phiJ seed Tj)
    (hb2Edges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      rho1 (Tj.edge a) = phiJ (Tj.edge a))
    (hdeltaPhiJ : deltaN ∉ TreeMissingColors phiJ Tj)
    (_ : supportColors =
      (ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport terminalSupport).biUnion
          (fun s => ett.series.data.stored s.succ))
    (_ : terminalSlot ∈ ExtensionBaseSupportClass ett
      terminalSupport hterminalSupport terminalSupport)
    (_ : preterminalSlot ∈
      (ExtensionBaseSupportClass ett terminalSupport
        hterminalSupport terminalSupport).erase terminalSlot)
    (hgammaIdentity : ett.series.data.delta preterminalSlot.succ = some gammaN)
    (_ : ett.series.data.gamma terminalSlot.succ = some gammaN)
    (_ : ett.series.data.delta terminalSlot.succ = some deltaN)
    (hb4 : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s terminalSupport rho1 gammaS deltaS)
    (hsupportColors : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      gammaS ∈ supportColors ∧ deltaS ∈ supportColors)
    (hdeltaEarlier : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      deltaN ≠ gammaS ∧ deltaN ≠ deltaS)
    (hsupportOrder : ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett terminalSupport
          hterminalSupport terminalSupport).erase terminalSlot →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ∀ v : V,
        v ∈ TreeSequenceVertexSet
            (ett.series.data.tree s.succ.castSucc) →
        v ≠ terminalSupport →
        ∀ w : V, Sum.inl w ∈
          TwoColorComponent G rho1 gammaS deltaS (Sum.inl v) →
          w ∈ TreeSequenceVertexSet Tn) :
    ∃ (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (_ :
      u ∉ TreeSequenceVertexSet Tn) (exitPath :
      (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)),
    exitPath.IsPath ∧
    2 ≤ exitPath.length ∧
    (∀ y : Sum V E, y ∈ exitPath.support → y ∈ p.support) ∧
    (∀ w : V,
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
        (Sum.inl w ∈ exitPath.support ↔ w = u)) ∧
    (∃
      g ∈
        BoundaryColorEdges G rho1 (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
          gammaN,
      Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
    ¬Incident G u fN ∧
    ∀ beta : Fin k,
    beta ∈ MissingColors G rho1 u →
    ∃ (z : V) (hz : z ∈ TreeSequenceVertexSet Tj) (zPosition : Fin (Tj.length + 1)),
    Tj.vertex zPosition = z ∧
    seed.length ≤ zPosition.val ∧
    ((seed.length < zPosition.val ∧
        beta ∈ MissingColors G rho1 z ∧
          ∀ r : Fin (Tj.length + 1),
            seed.length < r.val →
              r.val < zPosition.val → beta ∉ MissingColors G rho1 (Tj.vertex r)) ∨
      (zPosition = Fin.last Tj.length ∧
        ∀ r : Fin (Tj.length + 1),
          seed.length < r.val → beta ∉ MissingColors G rho1 (Tj.vertex r))) ∧
    (∀ w ∈ TreeVerticesBefore Tj z hz, beta ∉ MissingColors G rho1 w) ∧
    (∀ a : Fin Tj.length,
      seed.length ≤ a.val → a.val < zPosition.val → rho1 (Tj.edge a) ≠ some beta) ∧
    let rho0 := OutsideTreeColorSwap TjPrime rho1 beta deltaN
    let mu0 := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
    IsProperEdgeColoring G mu0 ∧
    IsOneEdgeUncolored mu0 e0 ∧
    StableColoringBeforeVertex Tj terminalSupport hterminalTj Dprev phiJ mu0 ∧
    ((∀ v : V,
        v ∈
            (((TreeVerticesBefore Tj z hz ∪ { z }) ∪
                      (TreeVerticesBefore TjPrime u huPrime ∪ { u })).erase
                  u).erase
              z →
          MissingColors G mu0 v = MissingColors G rho1 v) ∧
      (∀ f : E,
          ((∃ a : Fin Tj.length,
                seed.length ≤ a.val ∧ a.val < zPosition.val ∧ Tj.edge a = f) ∨
              (∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + 1)),
                TjPrime.vertex uPosition = u ∧
                  a.val < uPosition.val ∧ TjPrime.edge a = f)) →
            mu0 f = rho1 f) ∧
        (beta ∈ MissingColors G rho1 z → deltaN ∈ MissingColors G mu0 z) ∧
          (z ∈ TreeVerticesBefore TjPrime u huPrime →
            MissingColors G mu0 z = MissingColors G rho1 z)) ∧
    (ett.series.data.delta preterminalSlot.succ = some gammaN ∧
      gammaN ∈ MissingColors G mu0 u ∧ beta ∉ MissingColors G mu0 u) ∧
    (∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈
          (ExtensionBaseSupportClass ett terminalSupport hterminalSupport
                terminalSupport).erase
            terminalSlot →
        ett.series.data.gamma s.succ = some gammaS →
          ett.series.data.delta s.succ = some deltaS →
            ETTStrongInterchangeable ett s terminalSupport mu0 gammaS deltaS) ∧
    ((TreeSequenceVertexSet TjPrime).erase u).biUnion (fun v => MissingColors G mu0 v) ∩
        supportColors =
      { deltaN } ∧
    MissingColors G mu0 terminalSupport ∩ supportColors = { deltaN } ∧
    ∀ a : Fin TjPrime.length,
    seed.length ≤ a.val →
    ∀ c : Fin k,
    c ∈ supportColors \ { deltaN } →
    mu0 (TjPrime.edge a) ≠ some c := by
  classical
  have initial_subset {A B : TreeSequence G e0}
      (h : TreeSequenceInitialSegment A B) :
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    obtain ⟨i, hi, hvi⟩ := hv
    obtain ⟨hlen, hvertices, hedges⟩ := h
    exact ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _,
      (hvertices i).trans hvi⟩
  have initial_trans {A B C : TreeSequence G e0}
      (hAB : TreeSequenceInitialSegment A B)
      (hBC : TreeSequenceInitialSegment B C) :
      TreeSequenceInitialSegment A C := by
    exact @helper_initial_trans_1331 V E G e0 A B C hAB hBC
  have hseedN : TreeSequenceInitialSegment seed Tn :=
    initial_trans hseedJ hTjN
  have hterminalN : terminalSupport ∈ TreeSequenceVertexSet Tn :=
    initial_subset hTjN hterminalTj
  have hterminalPrime : terminalSupport ∈ TreeSequenceVertexSet TjPrime :=
    initial_subset hseedPrime hterminalSeed
  have hboundaryFacts := ExtensionBaseCaseTwoObservation20
    Tn seed TjPrime phiN sigmaN rho1 controlled restorationColors
    gammaN deltaN fN terminalSupport hphiNProper hphiNOne
    hsigmaProper hsigmaOne hrhoProper hrhoOne hsigmaStable
    hgammaControlled hdeltaControlled
    (fun f hf => (hb3 f hf).2) hgammaRestored hdeltaRestored
    hgammaBoundary hdeltaLocation hseedN hseedTerminal hclosure
    hterminalSeed hdeltaMissing
  rcases hboundaryFacts with ⟨hgammaRho, hdeltaRho⟩
  obtain ⟨u, exitPath, huDiff, hexitPath, hexitLength,
      hexitSupport, hexitIntersection, hexitBoundary, huNotFN⟩ :=
    ExtensionBaseCaseTwoObservation21 Tn TjPrime rho1 gammaN deltaN
      fN terminalSupport x p hpath hcomponent hterminalN hterminalPrime
      hxOutside htwoN hgammaRho hdeltaRho hfNterminal
  have huPrime : u ∈ TreeSequenceVertexSet TjPrime :=
    (Finset.mem_sdiff.mp huDiff).1
  have huOutside : u ∉ TreeSequenceVertexSet Tn :=
    (Finset.mem_sdiff.mp huDiff).2
  refine ⟨u, huPrime, huOutside, exitPath, hexitPath, hexitLength,
    hexitSupport, hexitIntersection, hexitBoundary, huNotFN, ?_⟩
  intro beta hbeta
  have huTerminal : u ≠ terminalSupport := by
    intro hut
    apply huOutside
    simpa [hut] using hterminalN
  have huErase : u ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport :=
    Finset.mem_erase.mpr ⟨huTerminal, huPrime⟩
  have hbetaSupport : beta ∉ supportColors := by
    intro hbs
    have hbinter : beta ∈ MissingColors G rho1 u ∩ supportColors :=
      Finset.mem_inter.mpr ⟨hbeta, hbs⟩
    have hempty := hcaseTwo u huErase
    rw [hempty] at hbinter
    simp at hbinter
  have hbetaGammaFirst : beta ≠ gammaFirst := by
    intro h
    exact hbetaSupport (h ▸ hgammaFirstSupport)
  have hbetaDelta : beta ≠ deltaN := by
    intro h
    exact hbetaSupport (h ▸ hdeltaSupport)
  have hbetaGamma : beta ≠ gammaN := by
    intro h
    exact hbetaSupport (h ▸ hgammaSupport)
  have hbetaTerminal : beta ∉ MissingColors G rho1 terminalSupport := by
    intro hbt
    have hd := hprimeElementary huPrime hterminalPrime huTerminal
    exact (Finset.disjoint_left.mp hd) hbeta hbt
  have huSeed : u ∉ TreeSequenceVertexSet seed := by
    intro hus
    exact huOutside (initial_subset hseedN hus)
  obtain ⟨z, hz, zPosition, hzPosition, hzAfter,
      hzChoice, hzBefore, hzEdges⟩ :=
    ExtensionBaseCaseTwoObservation23 Tj seed TjPrime phiJ rho1
      terminalSupport u beta gammaFirst hseedJ hseedPrime hseedTerminal
      huPrime huSeed hprimeElementary hbeta hterminalSeed hb2Missing
      hbetaTerminal hterminalInclusion hbetaGammaFirst haugmentation hb2Edges
  obtain ⟨hprimeMissing, hprimeEdges⟩ :=
    ExtensionBaseCaseTwoObservation19 rho1 seed TjPrime terminalSupport
      supportColors deltaN hclosure hterminalPrime hcaseTwo hterminalColors
  refine ⟨z, hz, zPosition, hzPosition, hzAfter, hzChoice, hzBefore,
    hzEdges, ?_⟩
  dsimp
  let rho0 := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  let mu0 := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
  have hbetaTree : beta ∈ TreeMissingColors rho1 TjPrime := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨u, huPrime, hbeta⟩
  have hdeltaTree : deltaN ∈ TreeMissingColors rho1 TjPrime := by
    unfold TreeMissingColors
    exact Finset.mem_biUnion.mpr ⟨terminalSupport, hterminalPrime,
      hdeltaMissing⟩
  have houtside := OutsideTreeColorSwapStable TjPrime supportColors rho1
    beta deltaN hrhoProper hrhoOne hclosure.2 hbetaTree hdeltaTree
    hbetaDelta
  change IsProperEdgeColoring G rho0 ∧ IsOneEdgeUncolored rho0 e0 ∧
      StableColoring TjPrime supportColors rho1 rho0 ∧
      ∀ f : E, TreeIncidentEdge TjPrime f → rho0 f = rho1 f at houtside
  rcases houtside with ⟨hrho0Proper, hrho0One, hrho0Stable, hrho0Fixed⟩
  have hgammaBeta : gammaN ≠ beta := Ne.symm hbetaGamma
  exact @helper_continuation_1644 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 input T generating ett terminalSlot preterminalSlot (by assumption) (by assumption)
      terminalSupport hterminalSupport Tj Tn seed TjPrime phiJ rho1 Dprev supportColors gammaN
      deltaN x p hTjN hseedJ hseedPrime hseedTerminal hterminalTj hclosure hprimeElementary
      hcaseTwo hterminalColors hdeltaSupport hgammaDelta hdeltaMissing hpath hcomponent hxOutside
      hb1 hb2Missing haugmentation hb2Edges hdeltaPhiJ (by assumption) (by assumption) (by
      assumption) hgammaIdentity (by assumption) (by assumption) hb4 hsupportColors hdeltaEarlier
      hsupportOrder initial_subset hterminalPrime u exitPath hexitPath hexitLength hexitSupport
      hexitIntersection hexitBoundary huPrime huOutside beta hbeta huTerminal huErase
      hbetaSupport hbetaDelta hbetaGamma huSeed z hz zPosition hzPosition hzAfter hzBefore
      hzEdges hprimeMissing hprimeEdges hrho0Proper hrho0One hrho0Stable hrho0Fixed hgammaBeta
end GoldbergSeymour

end
