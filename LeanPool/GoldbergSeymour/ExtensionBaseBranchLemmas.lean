/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

import all LeanPool.GoldbergSeymour.ExtensionBaseBranchPreparation
import all LeanPool.GoldbergSeymour.ExtensionBaseAuxiliary
public import LeanPool.GoldbergSeymour.ExtensionBaseStepLemmas
public import LeanPool.GoldbergSeymour.ExtensionBaseClaim44
public import LeanPool.GoldbergSeymour.ExtensionBaseClaim43
public import LeanPool.GoldbergSeymour.ExtensionBaseCaseTwoContradiction
public import LeanPool.GoldbergSeymour.ExtensionBaseClaim45
public import LeanPool.GoldbergSeymour.ExtensionBaseCaseOneSelection
public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmB
public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmA
public import LeanPool.GoldbergSeymour.ExtensionBaseSupportClassEnumeration
public import LeanPool.GoldbergSeymour.ExtensionBaseSupportClassColors
public import LeanPool.GoldbergSeymour.ExtensionBaseClaimStrongInterchangeable
public import LeanPool.GoldbergSeymour.ExtensionBaseClaimMissingColors
public import LeanPool.GoldbergSeymour.HkuParallelBoundaryStructure

/-!
# Preparatory lemmas for the extension base

Part of Wesley Pegden’s Trellis formalization of the Goldberg–Seymour theorem,
commit 88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12. These lemmas establish the
base cases used by the extension construction.
-/

@[expose] public section

namespace GoldbergSeymour.ExtensionBaseProof

theorem helper_hseedBeforeU_7025.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0),
    TreeSequenceInitialSegment seed TjPrime →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (uPosition : Fin (TjPrime.length + (1 : ℕ))),
    TjPrime.vertex uPosition = u0 →
    u0 ∉ TreeSequenceVertexSet seed →
    seed.length < (↑uPosition : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed TjPrime hseedPrime H
      x componentPath u exitPath zPosition u0 exitPath0 zPosition0 uPosition huPosition huNotSeed
  exact @helper_hseedBeforeU_3367 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
      (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
      (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@TjPrime) (@hseedPrime) (@x) (@componentPath) (@u)
      (@exitPath) (@zPosition) (@u0) (@exitPath0) (@zPosition0) (@uPosition) (@huPosition)
      (@huNotSeed)

theorem helper_hvBeforePrime_7074.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    (∀ {A B : TreeSequence G e0},
        TreeSequenceInitialSegment A B →
          TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B) →
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    seed.vertex (Fin.last seed.length) = v →
    ∀ (TjPrime : TreeSequence G e0),
    TreeSequenceInitialSegment seed TjPrime →
    v ∈ TreeSequenceVertexSet seed →
    ∀ (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime)
      (uPosition : Fin (TjPrime.length + (1 : ℕ))),
    TjPrime.vertex uPosition = u0 →
    seed.length < (↑uPosition : ℕ) →
    v ∈ TreeVerticesBefore TjPrime u0 huPrime0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot vertexTransfer terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedTerminal TjPrime hseedPrime hterminalSeed u0 huPrime0
      uPosition huPosition hseedBeforeU
  exact @helper_hvBeforePrime_3939 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
      (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@vertexTransfer) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTerminal) (@TjPrime)
      (@hseedPrime) (@hterminalSeed) (@u0) (@huPrime0) (@uPosition) (@huPosition)
      (@hseedBeforeU)

theorem helper_hUsegmentVertexBefore_7104.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (TjPrime : TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (uPosition : Fin (TjPrime.length + (1 : ℕ)))
      (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
    TreeSequenceInitialSegment U TjPrime →
    (∀ (i : Fin (TjPrime.length + (1 : ℕ))),
        (↑i : ℕ) < (↑uPosition : ℕ) →
          TjPrime.vertex i ∈ TreeVerticesBefore TjPrime u0 huPrime0) →
    ∀ {A : TreeSequence G e0},
    TreeSequenceInitialSegment A U →
    A.length < U.length →
    ∀ {y : V},
    y ∈ TreeSequenceVertexSet A →
    y ∈ TreeVerticesBefore TjPrime u0 huPrime0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H x
      componentPath u exitPath zPosition u0 huPrime0 exitPath0 zPosition0 uPosition
      huPositionPositive huPositionBound U hUPrime hprimeVertexBefore A hAU hAlen y hyA
  exact @helper_hUsegmentVertexBefore_5198 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper)
      (@hfirstPositive) (@trace) (@p0) (@indices0) (@gamma0) (@delta0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
      (@hseedTj) (@TjPrime) (@x) (@componentPath) (@u) (@exitPath) (@zPosition) (@u0)
      (@huPrime0) (@exitPath0) (@zPosition0) (@uPosition) (@huPositionPositive)
      (@huPositionBound) (@hUPrime) (@hprimeVertexBefore) (@A) (@hAU) (@hAlen) (@y) (@hyA)

theorem helper_hbeforePrimeNeU_7117.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (TjPrime : TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : Fin (TjPrime.length + (1 : ℕ))) {y : V},
    y ∈ TreeVerticesBefore TjPrime u0 huPrime0 →
    y ≠ u0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H x
      componentPath u exitPath zPosition u0 huPrime0 exitPath0 zPosition0 uPosition y hy
  exact @helper_hbeforePrimeNeU_3983 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@x)
      (@componentPath) (@u) (@exitPath) (@zPosition) (@u0) (@huPrime0) (@exitPath0)
      (@zPosition0) (@uPosition) (@y) (@hy)

theorem helper_hbeforePrimeMissing_7126.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (TjPrime : TreeSequence G e0) (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime)
      (z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
      (rho3 : PartialEdgeColoring E k),
    (∀
        y ∈
          ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 ∪
                      ({ z0 } : Finset V) ∪
                    (TreeVerticesBefore TjPrime u0 huPrime0 ∪ ({ u0 } : Finset V))).erase
                u0).erase
            z0,
        MissingColors G rho3 y = MissingColors G rho1 y) →
    (z0 ∈ TreeVerticesBefore TjPrime u0 huPrime0 →
        MissingColors G rho3 z0 = MissingColors G rho1 z0) →
    (∀ {y : V}, y ∈ TreeVerticesBefore TjPrime u0 huPrime0 → y ≠ u0) →
    ∀ y ∈ TreeVerticesBefore TjPrime u0 huPrime0,
    MissingColors G rho3 y = MissingColors G rho1 y := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace rho1 TjPrime u0 huPrime0 z0 hz0 rho3 hd2Missing hd2z
      hbeforePrimeNeU y hy
  exact @helper_hbeforePrimeMissing_3991 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace)
      (@TjPrime) (@u0) (@huPrime0) (@z0) (@hz0) (@rho3) (@hd2Missing) (@hd2z)
      (@hbeforePrimeNeU) (@y) (@hy)

theorem helper_transportUStep_7134.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    (∀ {A B C : TreeSequence G e0},
        TreeSequenceInitialSegment A B →
          TreeSequenceInitialSegment B C → TreeSequenceInitialSegment A C) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (TjPrime : TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (rho3 : PartialEdgeColoring E k),
    (∀ (f : E),
        ((∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
              seed.length ≤ (↑a : ℕ) ∧
                (↑a : ℕ) < (↑zPosition0 : ℕ) ∧
                  (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
            ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))),
              TjPrime.vertex uPosition = u0 ∧
                (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) →
          rho3 f = rho1 f) →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ))),
    TjPrime.vertex uPosition = u0 →
    ∀ (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
    TreeSequenceInitialSegment U TjPrime →
    (∀ {A : TreeSequence G e0},
        TreeSequenceInitialSegment A U →
          A.length < U.length →
            ∀ {y : V},
              y ∈ TreeSequenceVertexSet A → y ∈ TreeVerticesBefore TjPrime u0 huPrime0) →
    (∀ y ∈ TreeVerticesBefore TjPrime u0 huPrime0,
        MissingColors G rho3 y = MissingColors G rho1 y) →
    ∀ {A B : TreeSequence G e0},
    TashkinovAugmentation rho1 A B →
    TreeSequenceInitialSegment B U →
    TashkinovAugmentation rho3 A B := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot segmentTrans trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H x
      componentPath u exitPath zPosition u0 huPrime0 exitPath0 zPosition0 rho3 hd2Edges uPosition
      huPosition huPositionPositive huPositionBound U hUPrime hUsegmentVertexBefore
      hbeforePrimeMissing A B hstep hBU
  exact @helper_transportUStep_5236 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@segmentTrans) (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@x)
      (@componentPath) (@u) (@exitPath) (@zPosition) (@u0) (@huPrime0) (@exitPath0)
      (@zPosition0) (@rho3) (@hd2Edges) (@uPosition) (@huPosition) (@huPositionPositive)
      (@huPositionBound) (@hUPrime) (@hUsegmentVertexBefore) (@hbeforePrimeMissing) (@A)
      (@B) (@hstep) (@hBU)

theorem helper_segmentVertexBefore_7192.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
      (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    (∀ (i : Fin (seed.length + (1 : ℕ))),
        (↑i : ℕ) < seed.length →
          seed.vertex i ∈
            TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ) →
    ∀ {A : TreeSequence G e0},
    TreeSequenceInitialSegment A seed →
    A.length < seed.length →
    ∀ {y : V},
    y ∈ TreeSequenceVertexSet A →
    y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hterminalJ terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedVertexBefore A hAseed hAlen y hyA
  exact @helper_segmentVertexBefore_4061 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hterminalJ)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
      (@hseedVertexBefore) (@A) (@hAseed) (@hAlen) (@y) (@hyA)

theorem helper_transportSeedRoute_7209.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (rho3 : PartialEdgeColoring E k),
    (∀ {A B : TreeSequence G e0},
        TashkinovAugmentation (ett.series.data.coloring jSlot.castSucc) A B →
          TreeSequenceInitialSegment B seed → TashkinovAugmentation rho3 A B) →
    ∀ (S : TreeSequence G e0),
    TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) S seed →
    TashkinovAugmentationSequence rho3 S seed := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      rho3 transportSeedStep S hroute
  exact @helper_transportSeedRoute_4083 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@rho3) (@transportSeedStep)
      (@S) (@hroute)

theorem helper_hzChoiceForContradiction_7230.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (beta0 : Fin k) (z0 : V)
      (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
    ((seed.length < (↑zPosition0 : ℕ) ∧
          beta0 ∈ MissingColors G rho1 z0 ∧
            ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
              seed.length < (↑r : ℕ) →
                (↑r : ℕ) < (↑zPosition0 : ℕ) →
                  beta0 ∉
                    MissingColors G rho1
                      ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) ∨
        zPosition0 = Fin.last (ett.series.data.tree jSlot.succ.castSucc).length ∧
          ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
            seed.length < (↑r : ℕ) →
              beta0 ∉
                MissingColors G rho1
                  ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) →
    zPosition0 = Fin.last (ett.series.data.tree jSlot.succ.castSucc).length ∨
      (↑zPosition0 : ℕ) <
          (↑(Fin.last (ett.series.data.tree jSlot.succ.castSucc).length) : ℕ) ∧
        beta0 ∈ MissingColors G rho1 z0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace rho1 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed beta0 z0 zPosition0 hzChoice0
  exact @helper_hzChoiceForContradiction_4107 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@beta0)
      (@z0) (@zPosition0) (@hzChoice0)

theorem helper_hUsegmentVertexBefore_7424.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (TjPrime : TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (uPosition : Fin (TjPrime.length + (1 : ℕ)))
      (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
    TreeSequenceInitialSegment U TjPrime →
    (∀ (i : Fin (TjPrime.length + (1 : ℕ))),
        (↑i : ℕ) < (↑uPosition : ℕ) →
          TjPrime.vertex i ∈ TreeVerticesBefore TjPrime u0 huPrime0) →
    ∀ {A : TreeSequence G e0},
    TreeSequenceInitialSegment A U →
    A.length < U.length →
    ∀ {y : V},
    y ∈ TreeSequenceVertexSet A →
    y ∈ TreeVerticesBefore TjPrime u0 huPrime0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H x
      componentPath u exitPath zPosition u0 huPrime0 exitPath0 zPosition0 uPosition
      huPositionPositive huPositionBound U hUPrime hprimeVertexBefore A hAU hAlen y hyA
  exact @helper_hUsegmentVertexBefore_6032 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@v) (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper)
      (@hfirstPositive) (@trace) (@p0) (@indices0) (@gamma0) (@delta0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
      (@hseedTj) (@TjPrime) (@x) (@componentPath) (@u) (@exitPath) (@zPosition) (@u0)
      (@huPrime0) (@exitPath0) (@zPosition0) (@uPosition) (@huPositionPositive)
      (@huPositionBound) (@hUPrime) (@hprimeVertexBefore) (@A) (@hAU) (@hAlen) (@y) (@hyA)

theorem helper_hbeforePrimeNeU_7437.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (TjPrime : TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : Fin (TjPrime.length + (1 : ℕ))) {y : V},
    y ∈ TreeVerticesBefore TjPrime u0 huPrime0 →
    y ≠ u0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H x
      componentPath u exitPath zPosition u0 huPrime0 exitPath0 zPosition0 uPosition y hy
  exact @helper_hbeforePrimeNeU_4309 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@v) (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper)
      (@hfirstPositive) (@trace) (@p0) (@indices0) (@gamma0) (@delta0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
      (@hseedTj) (@TjPrime) (@x) (@componentPath) (@u) (@exitPath) (@zPosition) (@u0)
      (@huPrime0) (@exitPath0) (@zPosition0) (@uPosition) (@y) (@hy)

theorem helper_hbeforePrimeMissing_7447.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (TjPrime : TreeSequence G e0) (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime)
      (z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
      (rho3 : PartialEdgeColoring E k),
    (∀
        y ∈
          ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 ∪
                      ({ z0 } : Finset V) ∪
                    (TreeVerticesBefore TjPrime u0 huPrime0 ∪ ({ u0 } : Finset V))).erase
                u0).erase
            z0,
        MissingColors G rho3 y = MissingColors G rho1 y) →
    (z0 ∈ TreeVerticesBefore TjPrime u0 huPrime0 →
        MissingColors G rho3 z0 = MissingColors G rho1 z0) →
    (∀ {y : V}, y ∈ TreeVerticesBefore TjPrime u0 huPrime0 → y ≠ u0) →
    ∀ y ∈ TreeVerticesBefore TjPrime u0 huPrime0,
    MissingColors G rho3 y = MissingColors G rho1 y := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace rho1 TjPrime u0 huPrime0 z0 hz0 rho3 hd2Missing hd2z
      hbeforePrimeNeU y hy
  exact @helper_hbeforePrimeMissing_4318 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@v) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace)
      (@TjPrime) (@u0) (@huPrime0) (@z0) (@hz0) (@rho3) (@hd2Missing) (@hd2z)
      (@hbeforePrimeNeU) (@y) (@hy)

theorem helper_transportUStep_7455.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    (∀ {A B C : TreeSequence G e0},
        TreeSequenceInitialSegment A B →
          TreeSequenceInitialSegment B C → TreeSequenceInitialSegment A C) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (TjPrime : TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (rho3 : PartialEdgeColoring E k),
    (∀ (f : E),
        ((∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
              seed.length ≤ (↑a : ℕ) ∧
                (↑a : ℕ) < (↑zPosition0 : ℕ) ∧
                  (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
            ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))),
              TjPrime.vertex uPosition = u0 ∧
                (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) →
          rho3 f = rho1 f) →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ))),
    TjPrime.vertex uPosition = u0 →
    ∀ (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
    TreeSequenceInitialSegment U TjPrime →
    (∀ {A : TreeSequence G e0},
        TreeSequenceInitialSegment A U →
          A.length < U.length →
            ∀ {y : V},
              y ∈ TreeSequenceVertexSet A → y ∈ TreeVerticesBefore TjPrime u0 huPrime0) →
    (∀ y ∈ TreeVerticesBefore TjPrime u0 huPrime0,
        MissingColors G rho3 y = MissingColors G rho1 y) →
    ∀ {A B : TreeSequence G e0},
    TashkinovAugmentation rho1 A B →
    TreeSequenceInitialSegment B U →
    TashkinovAugmentation rho3 A B := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot segmentTrans trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H x
      componentPath u exitPath zPosition u0 huPrime0 exitPath0 zPosition0 rho3 hd2Edges uPosition
      huPosition huPositionPositive huPositionBound U hUPrime hUsegmentVertexBefore
      hbeforePrimeMissing A B hstep hBU
  exact @helper_transportUStep_6071 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@segmentTrans) (@trace) (@p0) (@indices0) (@gamma0) (@delta0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
      (@hseedTj) (@TjPrime) (@x) (@componentPath) (@u) (@exitPath) (@zPosition) (@u0)
      (@huPrime0) (@exitPath0) (@zPosition0) (@rho3) (@hd2Edges) (@uPosition)
      (@huPosition) (@huPositionPositive) (@huPositionBound) (@hUPrime)
      (@hUsegmentVertexBefore) (@hbeforePrimeMissing) (@A) (@B) (@hstep) (@hBU)

theorem helper_hterminalMissingEq_7478.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (TjPrime : TreeSequence G e0) (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime)
      (z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
      (rho3 : PartialEdgeColoring E k),
    (∀
        y ∈
          ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 ∪
                      ({ z0 } : Finset V) ∪
                    (TreeVerticesBefore TjPrime u0 huPrime0 ∪ ({ u0 } : Finset V))).erase
                u0).erase
            z0,
        MissingColors G rho3 y = MissingColors G rho1 y) →
    ¬z0 = v →
    v ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 →
    v ≠ u0 →
    MissingColors G rho3 v = MissingColors G rho1 v := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace rho1 TjPrime u0 huPrime0 z0 hz0 rho3 hd2Missing hzv
      hterminalBeforeZ hterminalNeU
  exact @helper_hterminalMissingEq_4347 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@v) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace)
      (@TjPrime) (@u0) (@huPrime0) (@z0) (@hz0) (@rho3) (@hd2Missing) (@hzv)
      (@hterminalBeforeZ) (@hterminalNeU)

theorem helper_hbeforeZData_7492.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (TjPrime : TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : Fin (TjPrime.length + (1 : ℕ))) {y : V},
    y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 →
    y ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∧ y ≠ z0 := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H x
      componentPath u exitPath zPosition u0 exitPath0 z0 hz0 zPosition0 uPosition y hy
  exact @helper_hbeforeZData_4365 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@x)
      (@componentPath) (@u) (@exitPath) (@zPosition) (@u0) (@exitPath0) (@z0) (@hz0)
      (@zPosition0) (@uPosition) (@y) (@hy)

theorem helper_hbeforeZMissing_7504.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    (∀ {A B : TreeSequence G e0},
        TreeSequenceInitialSegment A B →
          TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    (∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
          MissingColors G rho1 x =
            MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
        MissingColors G rho1 v = MissingColors G sigma v →
    TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree q.succ.castSucc) →
    ∀ (TjPrime : TreeSequence G e0) (u0 : V)
      (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime),
    u0 ∉ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) →
    ∀ (z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
      (rho3 : PartialEdgeColoring E k),
    (∀
        y ∈
          ((TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 ∪
                      ({ z0 } : Finset V) ∪
                    (TreeVerticesBefore TjPrime u0 huPrime0 ∪ ({ u0 } : Finset V))).erase
                u0).erase
            z0,
        MissingColors G rho3 y = MissingColors G rho1 y) →
    (∀ {y : V},
        y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 →
          y ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∧ y ≠ z0) →
    ∀ y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0,
    y ≠ v →
    MissingColors G rho3 y = MissingColors G (ett.series.data.coloring jSlot.castSucc) y := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot vertexTransfer trace rho1 hb2Missing hTjQ TjPrime u0
      huPrime0 huOutside0 z0 hz0 rho3 hd2Missing hbeforeZData y hy hyTerminal
  exact @helper_hbeforeZMissing_3860 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
      (@v) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@vertexTransfer) (@trace) (@hb2Missing) (@hTjQ) (@TjPrime) (@u0) (@huPrime0)
      (@huOutside0) (@z0) (@hz0) (@rho3) (@hd2Missing) (@hbeforeZData) (@y) (@hy)
      (@hyTerminal)

theorem helper_prefixPrefix_7534.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc))
      (TjPrime : TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : Fin (TjPrime.length + (1 : ℕ))) (A : TreeSequence G e0) (q0 : ℕ)
      (hq0 : (1 : ℕ) ≤ q0) (hqA : q0 + (1 : ℕ) ≤ A.length),
    TreeSequenceInitialSegment
      (TreeSequencePrefix A q0 hq0 (Nat.le_trans (Nat.le_succ q0) hqA))
      (TreeSequencePrefix A (q0 + (1 : ℕ)) (by omega) hqA) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H x
      componentPath u exitPath zPosition u0 exitPath0 zPosition0 uPosition A q0 hq0 hqA
  exact @helper_prefixPrefix_4416 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj) (@TjPrime)
      (@x) (@componentPath) (@u) (@exitPath) (@zPosition) (@u0) (@exitPath0)
      (@zPosition0) (@uPosition) (@A) (@q0) (@hq0) (@hqA)

theorem helper_hrightOutside_7601.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc))
      (TjPrime : TreeSequence G e0),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (_ : V ⊕ E) (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (uPosition : Fin (TjPrime.length + (1 : ℕ)))
      (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length)
      (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition0 : ℕ))
      (hzPositionBound :
        (↑zPosition0 : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
    let Z : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑zPosition0 : ℕ)
        hzPositionPositive hzPositionBound;
    ∀ (M : TreeSequence G e0),
    TreeSequenceInitialSegment U M →
    ∀ (n : ℕ),
    U.length ≤ n →
    ∀ (hnM : n + (1 : ℕ) ≤ M.length),
    let j : Fin M.length :=
      (⟨n, by
          have := GoldbergSeymour.TreeSequence.positive M
          omega⟩ :
        Fin M.length);
    ∀ (i : Fin Z.length),
    M.vertex j.succ = Z.vertex i.succ →
    Z.vertex i.succ ∉ TreeSequenceVertexSet U := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H a
      x componentPath u exitPath zPosition u0 exitPath0 zPosition0 uPosition huPositionPositive
      huPositionBound hzPositionPositive hzPositionBound U Z M hleftSegment n hnU hnM j i hvertexMZ
  exact @helper_hrightOutside_3985 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett)
      (@hpositive) (@v) (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal)
      (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0) (@gamma0)
      (@delta0) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@a) (@x)
      (@componentPath) (@u) (@exitPath) (@zPosition) (@u0) (@exitPath0)
      (@zPosition0) (@uPosition) (@huPositionPositive) (@huPositionBound)
      (@hzPositionPositive) (@hzPositionBound) (@M) (@hleftSegment) (@n) (@hnU)
      (@hnM) (@i) (@hvertexMZ)

theorem helper_hXY_7786.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc))
      (TjPrime : TreeSequence G e0),
    (∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
        seed.length ≤ (↑a : ℕ) →
          rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
            ett.series.data.coloring jSlot.castSucc
              ((ett.series.data.tree jSlot.succ.castSucc).edge a)) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (rho3 : PartialEdgeColoring E k),
    (∀ (f : E),
        ((∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
              seed.length ≤ (↑a : ℕ) ∧
                (↑a : ℕ) < (↑zPosition0 : ℕ) ∧
                  (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
            ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))),
              TjPrime.vertex uPosition = u0 ∧
                (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) →
          rho3 f = rho1 f) →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ)))
      (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length)
      (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition0 : ℕ))
      (hzPositionBound :
        (↑zPosition0 : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
    let Z : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑zPosition0 : ℕ)
        hzPositionPositive hzPositionBound;
    TreeSequenceInitialSegment Z (ett.series.data.tree jSlot.succ.castSucc) →
    ∀ (M : TreeSequence G e0),
    (∀ (A : TreeSequence G e0) (q0 : ℕ) (hq0 : (1 : ℕ) ≤ q0)
        (hqA : q0 + (1 : ℕ) ≤ A.length),
        TreeSequenceInitialSegment
          (TreeSequencePrefix A q0 hq0 (Nat.le_trans (Nat.le_succ q0) hqA))
          (TreeSequencePrefix A (q0 + (1 : ℕ)) (by omega) hqA)) →
    ∀ (n : ℕ) (hnU : U.length ≤ n) (hnM hnSuccM : n + (1 : ℕ) ≤ M.length)
      (hnM' : n ≤ M.length),
    let X : TreeSequence G e0 := TreeSequencePrefix M n (Nat.le_trans U.positive hnU) hnM';
    let Y : TreeSequence G e0 := TreeSequencePrefix M (n + (1 : ℕ)) (by omega) hnSuccM;
    let j : Fin M.length :=
      (⟨n, by
          have := GoldbergSeymour.TreeSequence.positive M
          omega⟩ :
        Fin M.length);
    ∀ (i : Fin Z.length),
    M.edge j = Z.edge i →
    seed.length ≤ (↑i : ℕ) →
    ∀ (c : Fin k),
    ett.series.data.coloring jSlot.castSucc (Z.edge i) = some c →
    c ∈ TreeMissingColors rho3 X →
    TashkinovAugmentation rho3 X Y := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime
      hb2EdgesFromSeed H x componentPath u exitPath zPosition u0 exitPath0 zPosition0 rho3
      hd2Edges uPosition huPositionPositive huPositionBound hzPositionPositive hzPositionBound U
      Z hZTj M prefixPrefix n hnU hnM hnSuccM hnM' X Y j i hedgeMZ hiSeed c hcolorZ hmissingX
  exact @helper_hXY_6689 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper)
      (@hfirstPositive) (@trace) (@p0) (@indices0) (@gamma0) (@delta0)
      (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@hb2EdgesFromSeed) (@x)
      (@componentPath) (@u) (@exitPath) (@zPosition) (@u0) (@exitPath0)
      (@zPosition0) (@rho3) (@hd2Edges) (@uPosition) (@huPositionPositive)
      (@huPositionBound) (@hzPositionPositive) (@hzPositionBound) (@hZTj) (@M)
      (@prefixPrefix) (@n) (@hnU) (@hnM) (@hnSuccM) (@hnM') (@i) (@hedgeMZ)
      (@hiSeed) (@c) (@hcolorZ) (@hmissingX)

theorem helper_caseContinuation_10294.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
       [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating),
    MaximumProperty ett →
    ∀ (hpositive : (0 : ℕ) < ett.rounds),
    LowerRoundInductionHypothesis G k e0 ett.rounds →
    ∀ (v : V) (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ),
          by
          have := GoldbergSeymour.TreeSequence.positive T
          omega⟩ :
        Fin ett.rounds);
    (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal →
    (∀ {A B C : TreeSequence G e0},
        TreeSequenceInitialSegment A B →
          TreeSequenceInitialSegment B C → TreeSequenceInitialSegment A C) →
    (∀ {A B : TreeSequence G e0},
        TreeSequenceInitialSegment A B →
          TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B) →
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma)
      (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
      (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    jSlot.castSucc.succ = jSlot.succ.castSucc →
    TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) →
    seed.vertex (Fin.last seed.length) = v →
    (∀ {A B C : TreeSequence G e0},
        TreeSequenceInitialSegment A C →
          TreeSequenceInitialSegment B C →
            A.length ≤ B.length → TreeSequenceInitialSegment A B) →
    ∀ (TjPrime : TreeSequence G e0),
    indices0 (Fin.last p0) = q →
    ∀ (u : V) (b : Fin (p0 + (1 : ℕ)))
      (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    u ∉ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) →
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
    StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc)
        (ett.series.data.coloring jSlot.castSucc)
        (traceB.coloring (Fin.last traceB.steps)) →
    IsProperEdgeColoring G rho2 →
    IsOneEdgeUncolored rho2 e0 →
    ∀ (uPosition : Fin (TjPrime.length + (1 : ℕ)))
      (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
    TashkinovAugmentationSequence rho2 seed U →
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ((0 : ℕ) < (↑jSlot : ℕ) →
        TreeSequenceInitialSegment Tprevious (ett.series.data.tree jSlot.succ.castSucc)) →
    ((0 : ℕ) < (↑jSlot : ℕ) → Tprevious.length < seed.length) →
    ((0 : ℕ) < (↑jSlot : ℕ) → TreeSequenceInitialSegment Tprevious seed) →
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    TreeSequenceInitialSegment seed Tj0 →
    ∀ (M : TreeSequence G e0),
    OrderedTreeUnion U Tj0 M →
    u ∈ TreeSequenceVertexSet U →
    TashkinovAugmentationSequence rho2 U M →
    False := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive hlower v sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot hjSlot segmentTrans vertexTransfer trace hterminalJ
      p0 indices0 rho1 terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hjTreeIndex hseedTj hseedTerminal commonPrefix TjPrime hqLast u b traceB huOutside rho2 c1
      hrho2Proper hrho2One uPosition huPositionPositive huPositionBound U hrouteRhoTwoU Tprevious
      hpreviousTj hpreviousStrict hpreviousSeed Tj0 hseedTj0 M hunion huU hrouteUM
  obtain ⟨C, hclosureMC⟩ := TashkinovClosureExists rho2 M
  have hrouteUC : TashkinovAugmentationSequence rho2 U C :=
    Relation.ReflTransGen.trans hrouteUM hclosureMC.1
  have hrouteSeedC : TashkinovAugmentationSequence rho2 seed C :=
    Relation.ReflTransGen.trans hrouteRhoTwoU hrouteUC
  have hclosedC :
      ColoredVertexSetClosed G rho2 (TreeSequenceVertexSet C) :=
    hclosureMC.2
  have hseedVertexBeforeJ (i : Fin (seed.length + 1))
      (hi : i.val < seed.length) :
      seed.vertex i ∈ TreeVerticesBefore
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
    exact @helper_hseedVertexBeforeJ_6180 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@vertexTransfer) (@hterminalJ)
        (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj)
        (@hseedTerminal) (@i) (@hi)
  have segmentVertexBeforeJ {A : TreeSequence G e0}
      (hAseed : TreeSequenceInitialSegment A seed)
      (hAlen : A.length < seed.length) {x : V}
      (hxA : x ∈ TreeSequenceVertexSet A) :
      x ∈ TreeVerticesBefore
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
    exact @helper_segmentVertexBeforeJ_6189 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hterminalJ) (@p0) (@indices0)
        (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime)
        (@uPosition) (@hseedVertexBeforeJ) (@A) (@hAseed) (@hAlen) (@x) (@hxA)
  have transportSeedStep2 {A B : TreeSequence G e0}
      (hstep : TashkinovAugmentation
        (ett.series.data.coloring jSlot.castSucc) A B)
      (hBseed : TreeSequenceInitialSegment B seed) :
      TashkinovAugmentation rho2 A B := by
    exact @helper_transportSeedStep2_6201 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@segmentTrans) (@trace)
        (@hterminalJ) (@p0) (@indices0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@TjPrime) (@u) (@b) (@traceB) (@c1) (@uPosition)
        (@segmentVertexBeforeJ) (@A) (@B) (@hstep) (@hBseed)
  have transportSeedRoute2 (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence
        (ett.series.data.coloring jSlot.castSucc) S seed) :
      TashkinovAugmentationSequence rho2 S seed := by
    exact @helper_transportSeedRoute2_6212 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0)
        (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@u) (@b)
        (@traceB) (@transportSeedStep2) (@S) (@hroute)
  have huM : u ∈ TreeSequenceVertexSet M := by
    rw [hunion.vertexSet]
    exact Finset.mem_union_left _ huU
  have hMCsegment : TreeSequenceInitialSegment M C :=
    TashkinovAugmentationSequenceInitialSegment rho2 M C hclosureMC.1
  have huC : u ∈ TreeSequenceVertexSet C :=
    vertexTransfer hMCsegment huM
  have hTj0C : TreeSequenceVertexSet Tj0 ⊆
      TreeSequenceVertexSet C := by
    intro x hx
    apply vertexTransfer hMCsegment
    rw [hunion.vertexSet]
    exact Finset.mem_union_right _ hx
  have hTj0StrictC : TreeSequenceVertexSet Tj0 <
      TreeSequenceVertexSet C :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hTj0C, by
      intro heq
      apply huOutside
      have huTj0 : u ∈ TreeSequenceVertexSet Tj0 := heq.symm.subset huC
      simpa [Tj0] using huTj0⟩
  by_cases hjPositive : 0 < jSlot.val
  · exact @helper_branch_1756 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@hlower) (@v)
      (@sigma) _ (by rfl) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) _ (by rfl)
      (@hjSlot) (@segmentTrans) (@vertexTransfer) (@trace) (@hterminalJ) (@p0) (@indices0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex)
      (@hseedTj) (@commonPrefix) (@TjPrime) (@hqLast) (@u) (@b) (@traceB) (@huOutside) (@c1)
      (@hrho2Proper) (@hrho2One) (@uPosition) (@hpreviousTj) (@hpreviousStrict) (@hpreviousSeed)
      (@C) (@hrouteSeedC) (@hclosedC) (@segmentVertexBeforeJ) (@transportSeedRoute2) (@huC)
      (@hTj0StrictC) (@hjPositive)
  · exact @helper_branch_6243 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@v) (@sigma) (@hqTerminal)
      (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@trace) (@p0) (@indices0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@commonPrefix)
      (@TjPrime) (@u) (@b) (@traceB) (@hrho2Proper) (@hrho2One) (@uPosition) (@hseedTj0) (@C)
      (@hrouteSeedC) (@transportSeedRoute2) (@hTj0StrictC) (@hjPositive)

theorem helper_caseContinuation_11664.{u_1, u_2} :
    helperCaseContinuation11664Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive v gamma delta sigma this q
      hqTerminal hvFinal hfirstUpper hfirstPositive jSlot segmentTrans vertexTransfer trace
      hterminalJ p0 indices0 gamma0 delta0 rho1 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedTj hseedTerminal hTjQ hseedVertexBefore
      segmentVertexBefore transportSeedRoute commonPrefix TjPrime hdeltaMissing H C a x
      componentPath u exitPath zPosition u0 huOutside0 exitPath0 beta0 z0 zPosition0 hzPosition0
      rho3 hrho3Proper hrho3One hd1 hdeltaZ uPosition terminalInTj hterminalInTj hzv
      hzChoiceForContradiction hjZero huPositionPositive huPositionBound hzPositionPositive
      hzPositionBound U Z hZTj hseedZ hrouteRhoThreeU hterminalMissingEq M hunion huU hrouteUM
  obtain ⟨C, hclosureMC⟩ := TashkinovClosureExists rho3 M
  have hrouteUC : TashkinovAugmentationSequence rho3 U C :=
    Relation.ReflTransGen.trans hrouteUM hclosureMC.1
  have hrouteSeedC : TashkinovAugmentationSequence rho3 seed C :=
    Relation.ReflTransGen.trans hrouteRhoThreeU hrouteUC
  have hMCsegment : TreeSequenceInitialSegment M C :=
    TashkinovAugmentationSequenceInitialSegment rho3 M C hclosureMC.1
  have huC : u0 ∈ TreeSequenceVertexSet C := by
    apply vertexTransfer hMCsegment
    rw [hunion.vertexSet]
    exact Finset.mem_union_left _ huU
  have hZC : TreeSequenceVertexSet Z ⊆ TreeSequenceVertexSet C := by
    intro y hyZ
    apply vertexTransfer hMCsegment
    rw [hunion.vertexSet]
    exact Finset.mem_union_right _ hyZ
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
      have hseedVertexBefore (i : Fin (seed.length + 1))
          (hi : i.val < seed.length) : seed.vertex i ∈
            TreeVerticesBefore
              (ett.series.data.tree jSlot.succ.castSucc) v
              hterminalJ := by
        unfold TreeVerticesBefore
        apply Finset.mem_filter.mpr
        let iTj : Fin
            ((ett.series.data.tree
              jSlot.succ.castSucc).length + 1) :=
          Fin.castLE (Nat.succ_le_succ hseedTj.1) i
        exact ⟨vertexTransfer hseedTj (by simp [TreeSequenceVertexSet]),
          iTj, terminalInTj, hseedTj.2.1 i, hterminalInTj,
          by simpa [iTj, terminalInTj] using hi⟩
      have segmentVertexBefore {A : TreeSequence G e0}
          (hAseed : TreeSequenceInitialSegment A seed)
          (hAlen : A.length < seed.length) {y : V}
          (hyA : y ∈ TreeSequenceVertexSet A) : y ∈
            TreeVerticesBefore
              (ett.series.data.tree jSlot.succ.castSucc) v
              hterminalJ := by
        obtain ⟨hAseedLen, hAseedVertices, -⟩ := hAseed
        simp only [TreeSequenceVertexSet, Finset.mem_image,
          Finset.mem_univ, true_and] at hyA
        obtain ⟨i, rfl⟩ := hyA
        rw [← hAseedVertices i]
        apply hseedVertexBefore
        change i.val < seed.length
        exact lt_of_le_of_lt (Nat.lt_succ_iff.mp i.isLt) hAlen
      have transportSeedStep {A B : TreeSequence G e0}
          (hstep : TashkinovAugmentation
            (ett.series.data.coloring jSlot.castSucc) A B)
          (hBseed : TreeSequenceInitialSegment B seed) :
          TashkinovAugmentation rho3 A B := by
        exact @helper_transportSeedStep_6612 (@V) (@E) inferInstance inferInstance inferInstance
            (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
            (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
            (@segmentTrans) (@trace) (@hterminalJ) (@p0) (@indices0) (@gamma0) (@delta0)
            (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj)
            (by assumption) (@TjPrime) (@x) (@componentPath) (@u) (@exitPath) (@zPosition) (@u0)
            (@exitPath0) (@zPosition0) (@rho3) (@hd1) (@uPosition) (by assumption) (@A) (@B)
            (@hstep) (@hBseed)
      have transportSeedRoute (S : TreeSequence G e0)
          (hroute : TashkinovAugmentationSequence
            (ett.series.data.coloring jSlot.castSucc) S seed) :
          TashkinovAugmentationSequence rho3 S seed := by
        unfold TashkinovAugmentationSequence at hroute ⊢
        induction hroute using
            Relation.ReflTransGen.head_induction_on with
        | refl => exact Relation.ReflTransGen.refl
        | @head A B hAB hBseed ih =>
            have hBsegment : TreeSequenceInitialSegment B seed :=
              TashkinovAugmentationSequenceInitialSegment _ B seed
                hBseed
            exact Relation.ReflTransGen.head
              (transportSeedStep hAB hBsegment) ih
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
      have hCElementary : ColoredVertexSetElementary G rho3
          (TreeSequenceVertexSet C) :=
        TashTree G k e0 rho3 C htripleRho hCTree
      rcases hzChoiceForContradiction with hzLast | hzEarlier
      · exact @helper_branch_6698 (@V) (@E) inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@v)
          (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper)
          (@hfirstPositive) (@vertexTransfer) (@trace) (@p0) (@indices0) (@gamma0)
          (@delta0) (@terminalPosition) (@hterminalPositionPositive)
          (@hterminalPositionBound) (@hseedTj) (@hTjQ) (@TjPrime) (@x) (@componentPath)
          (@u) (@exitPath) (@zPosition) (@u0) (@huOutside0) (@exitPath0) (@zPosition0)
          (@rho3) (@uPosition) (@hzPositionPositive) (@hzPositionBound) (@hZTj) (@C)
          (@huC) (@hZC) (@triple) (@htreeOne) (@htripleRho) (@hCTree) (@hzLast)
      · exact @helper_branch_6749 (@V) (@E) inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
          (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
          (@trace) (@terminalPosition) (@hterminalPositionPositive)
          (@hterminalPositionBound) (@hseedTerminal) (@hdeltaMissing) (@beta0) (@z0)
          (@zPosition0) (@hzPosition0) (@rho3) (@hdeltaZ) (@hzv) (@hzPositionPositive)
          (@hzPositionBound) (@hseedZ) (@hterminalMissingEq) (@C) (@hZC) (@hCElementary)
          (@hzEarlier)

theorem helper_branch_13441.{u_1, u_2} :
    helperBranch13441Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive v gamma delta sigma this q
      hqTerminal hvFinal hfirstUpper hfirstPositive jSlot hjSlot segmentTrans vertexTransfer
      trace hterminalJ p0 indices0 gamma0 delta0 rho1 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hjTreeIndex hseedTj hseedTerminal hTjQ hseedVertexBefore
      segmentVertexBefore transportSeedRoute commonPrefix TjPrime hclosure hseedPrime hqLast
      hterminalSeed H C a x componentPath u exitPath Tprevious hpreviousStrict hpreviousSeed
      zPosition u0 huPrime0 huOutside0 exitPath0 beta0 z0 hz0 zPosition0 hzChoice0 rho3
      hrho3Proper hrho3One hd1 hd2Missing hd2Edges hd2z hbeta0Terminal uPosition huPosition
      hseedBeforeU terminalInTj hterminalInTj hterminalInTjVal hzTerminalIff hzv
  have hzLast : zPosition0 = Fin.last
      (ett.series.data.tree jSlot.succ.castSucc).length := by
    rcases hzChoice0 with hfirst | hlast
    · exact False.elim (hbeta0Terminal (by simpa [hzv] using hfirst.2.1))
    · exact hlast.1
  have hseedFull : seed.length =
      (ett.series.data.tree jSlot.succ.castSucc).length := by
    have hterminalEq := hzTerminalIff.mp hzv
    have hvals := congrArg Fin.val (hterminalEq.symm.trans hzLast)
    simpa [hterminalInTjVal] using hvals
  have hvBeforePrime : v ∈ TreeVerticesBefore TjPrime u0 huPrime0 := by
    exact @helper_hvBeforePrime_7074 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@vertexTransfer) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTerminal) (@TjPrime)
        (@hseedPrime) (@hterminalSeed) (@u0) (@huPrime0) (@uPosition) (@huPosition) (@hseedBeforeU)
  have huPositionPositive : 1 ≤ uPosition.val :=
    seed.positive.trans (Nat.le_of_lt hseedBeforeU)
  have huPositionBound : uPosition.val ≤ TjPrime.length :=
    Nat.lt_succ_iff.mp uPosition.isLt
  let U : TreeSequence G e0 :=
    TreeSequencePrefix TjPrime uPosition.val huPositionPositive
      huPositionBound
  have hUPrime : TreeSequenceInitialSegment U TjPrime := by
    exact @helper_hUPrime_3958 (@V) (@E) (@G) (@e0) (@TjPrime) (@uPosition)
        (@huPositionPositive) (@huPositionBound)
  have hseedU : TreeSequenceInitialSegment seed U := by
    apply commonPrefix hseedPrime hUPrime
    exact Nat.le_of_lt hseedBeforeU
  have hrouteRhoOneU : TashkinovAugmentationSequence rho1 seed U :=
    TashkinovAugmentationSequenceRestrict rho1 seed U TjPrime
      hclosure.1 hseedU hUPrime
  have hprimeVertexBefore (i : Fin (TjPrime.length + 1))
      (hi : i.val < uPosition.val) :
      TjPrime.vertex i ∈ TreeVerticesBefore TjPrime u0 huPrime0 := by
    unfold TreeVerticesBefore
    apply Finset.mem_filter.mpr
    refine ⟨by simp [TreeSequenceVertexSet], i, uPosition, rfl,
      huPosition, hi⟩
  have hUsegmentVertexBefore {A : TreeSequence G e0}
      (hAU : TreeSequenceInitialSegment A U)
      (hAlen : A.length < U.length) {y : V}
      (hyA : y ∈ TreeSequenceVertexSet A) :
      y ∈ TreeVerticesBefore TjPrime u0 huPrime0 := by
    exact @helper_hUsegmentVertexBefore_7104 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
        (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@x) (@componentPath) (@u) (@exitPath)
        (@zPosition) (@u0) (@huPrime0) (@exitPath0) (@zPosition0) (@uPosition)
        (@huPositionPositive) (@huPositionBound) (@hUPrime) (@hprimeVertexBefore) (@A) (@hAU)
        (@hAlen) (@y) (@hyA)
  have hbeforePrimeNeU {y : V}
      (hy : y ∈ TreeVerticesBefore TjPrime u0 huPrime0) : y ≠ u0 := by
    exact @helper_hbeforePrimeNeU_7117 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
        (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@x) (@componentPath) (@u) (@exitPath)
        (@zPosition) (@u0) (@huPrime0) (@exitPath0) (@zPosition0) (@uPosition) (@y) (@hy)
  have hbeforePrimeMissing (y : V)
      (hy : y ∈ TreeVerticesBefore TjPrime u0 huPrime0) :
      MissingColors G rho3 y = MissingColors G rho1 y := by
    exact @helper_hbeforePrimeMissing_7126 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@TjPrime) (@u0)
        (@huPrime0) (@z0) (@hz0) (@rho3) (@hd2Missing) (@hd2z) (@hbeforePrimeNeU) (@y) (@hy)
  have transportUStep {A B : TreeSequence G e0}
      (hstep : TashkinovAugmentation rho1 A B)
      (hBU : TreeSequenceInitialSegment B U) :
      TashkinovAugmentation rho3 A B := by
    exact @helper_transportUStep_7134 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@segmentTrans)
        (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@x)
        (@componentPath) (@u) (@exitPath) (@zPosition) (@u0) (@huPrime0) (@exitPath0)
        (@zPosition0) (@rho3) (@hd2Edges) (@uPosition) (@huPosition) (@huPositionPositive)
        (@huPositionBound) (@hUPrime) (@hUsegmentVertexBefore) (@hbeforePrimeMissing) (@A) (@B)
        (@hstep) (@hBU)
  have transportURoute (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence rho1 S U) :
      TashkinovAugmentationSequence rho3 S U := by
    exact @helper_transportURoute_4006 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@v) (@sigma) (@hvFinal)
        (@trace) (@TjPrime) (@rho3) (@uPosition) (@huPositionPositive) (@huPositionBound)
        (@transportUStep) (@S) (@hroute)
  have hrouteRhoThreeU : TashkinovAugmentationSequence rho3 seed U :=
    transportURoute seed hrouteRhoOneU
  obtain ⟨C, hclosureUC⟩ := TashkinovClosureExists rho3 U
  have hrouteSeedC : TashkinovAugmentationSequence rho3 seed C :=
    Relation.ReflTransGen.trans hrouteRhoThreeU hclosureUC.1
  have hseedC : TreeSequenceInitialSegment seed C :=
    TashkinovAugmentationSequenceInitialSegment rho3 seed C hrouteSeedC
  have huU : u0 ∈ TreeSequenceVertexSet U := by
    exact @helper_huU_4024 (@V) (@E) (@G) (@e0) (@TjPrime) (@u0) (@uPosition) (@huPosition)
        (@huPositionPositive) (@huPositionBound)
  have hUC : TreeSequenceInitialSegment U C :=
    TashkinovAugmentationSequenceInitialSegment rho3 U C hclosureUC.1
  have huC : u0 ∈ TreeSequenceVertexSet C := vertexTransfer hUC huU
  have hTjC : TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc) ⊆
        TreeSequenceVertexSet C := by
    exact @helper_hTjC_5298 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (@hseedFull) (@C) (@hseedC)
  have hTjStrictC : TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc) <
        TreeSequenceVertexSet C :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hTjC, by
      intro heq
      exact huOutside0 (vertexTransfer hTjQ (heq.symm.subset huC))⟩
  have hseedVertexBefore (i : Fin (seed.length + 1))
      (hi : i.val < seed.length) :
      seed.vertex i ∈ TreeVerticesBefore
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
    unfold TreeVerticesBefore
    apply Finset.mem_filter.mpr
    let iTj : Fin
        ((ett.series.data.tree jSlot.succ.castSucc).length + 1) :=
      Fin.castLE (Nat.succ_le_succ hseedTj.1) i
    refine ⟨vertexTransfer hseedTj (by simp [TreeSequenceVertexSet]),
      iTj, terminalInTj, hseedTj.2.1 i, hterminalInTj, ?_⟩
    simpa [iTj, terminalInTj] using hi
  have segmentVertexBefore {A : TreeSequence G e0}
      (hAseed : TreeSequenceInitialSegment A seed)
      (hAlen : A.length < seed.length) {y : V}
      (hyA : y ∈ TreeSequenceVertexSet A) :
      y ∈ TreeVerticesBefore
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
    exact @helper_segmentVertexBefore_7192 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hterminalJ) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedVertexBefore) (@A)
        (@hAseed) (@hAlen) (@y) (@hyA)
  have transportSeedStep {A B : TreeSequence G e0}
      (hstep : TashkinovAugmentation
        (ett.series.data.coloring jSlot.castSucc) A B)
      (hBseed : TreeSequenceInitialSegment B seed) :
      TashkinovAugmentation rho3 A B := by
    exact @helper_transportSeedStep_5350 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@segmentTrans)
        (@trace) (@hterminalJ) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj) (by assumption)
        (@TjPrime) (@x) (@componentPath) (@u) (@exitPath) (@zPosition) (@u0) (@exitPath0)
        (@zPosition0) (@rho3) (@hd1) (@uPosition) (by assumption) (@A) (@B) (@hstep) (@hBseed)
  have transportSeedRoute (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence
        (ett.series.data.coloring jSlot.castSucc) S seed) :
      TashkinovAugmentationSequence rho3 S seed := by
    exact @helper_transportSeedRoute_7209 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@rho3) (@transportSeedStep) (@S)
        (@hroute)
  by_cases hjPositive : 0 < jSlot.val
  · exact @helper_branch_2914 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@v) (@gamma) (@delta) (@sigma)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@trace) (@hterminalJ)
      (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (by assumption) (by assumption)
      (@commonPrefix) (@TjPrime) (@hqLast) (@x) (@componentPath) (@u) (@exitPath)
      (@hpreviousStrict) (@hpreviousSeed) (@zPosition) (@u0) (@exitPath0) (@zPosition0) (@rho3)
      (@hrho3Proper) (@hrho3One) (@hd1) (@uPosition) (@huPositionPositive) (@huPositionBound)
      (@C) (@hclosureUC) (@hrouteSeedC) (@hTjStrictC) (@segmentVertexBefore)
      (@transportSeedRoute) (@hjPositive)
  · exact @helper_branch_5609 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@v) (@gamma) (@delta) (@sigma)
      (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0)
      (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@hseedTj) (by assumption) (@commonPrefix) (@TjPrime) (@a) (@x)
      (@componentPath) (@u) (@exitPath) (@zPosition) (@u0) (@exitPath0) (@zPosition0) (@rho3)
      (@hrho3Proper) (@hrho3One) (@uPosition) (@C) (@hrouteSeedC) (@hTjStrictC) (by assumption)
      (@hjPositive)

private theorem helper_hTpreviousBefore_6081.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀
      (_ :
        ∀ {A B : TreeSequence G e0},
          TreeSequenceInitialSegment A B →
            TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B)
      (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
      (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀
      (hseedTj :
        TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀
      (_ :
        (0 : ℕ) < (↑jSlot : ℕ) →
          TreeSequenceInitialSegment Tprevious (ett.series.data.tree jSlot.succ.castSucc))
      (_ : (0 : ℕ) < (↑jSlot : ℕ) → Tprevious.length < seed.length)
      (_ : (0 : ℕ) < (↑jSlot : ℕ) → TreeSequenceInitialSegment Tprevious seed),
    let terminalInTj : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)) :=
      Fin.castLE
        (by
          first
          | omega
          | ( have := GoldbergSeymour.TreeSequence.positive T
              have := Fin.isLt terminalPosition
              have := hseedTj.1
              have :=
                GoldbergSeymour.TreeSequence.positive
                  (TreeSequencePrefix
                    (ett.series.data.tree
                      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
                            omega⟩ :
                          Fin ett.rounds).succ.castSucc)
                    (↑terminalPosition : ℕ) hterminalPositionPositive
                    hterminalPositionBound)
              have :=
                GoldbergSeymour.TreeSequence.positive
                  (ett.series.data.tree
                    (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
                          omega⟩ :
                        Fin ett.rounds).succ.castSucc)
              all_goals omega))
        (Fin.last seed.length);
    ∀ (_ : (ett.series.data.tree jSlot.succ.castSucc).vertex terminalInTj = v)
      (_ : (0 : ℕ) < (↑jSlot : ℕ)),
    TreeSequenceVertexSet Tprevious ⊆
      TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot vertexTransfer hterminalJ terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedTj Tprevious hpreviousTj hpreviousStrict hpreviousSeed
      terminalInTj hterminalInTj hjPositive y hy
  obtain ⟨i, rfl⟩ := by
    simpa only [TreeSequenceVertexSet, Finset.mem_image,
      Finset.mem_univ, true_and] using hy
  have hprevSeed := hpreviousSeed hjPositive
  let iSeed : Fin (seed.length + 1) :=
    Fin.castLE (Nat.succ_le_succ hprevSeed.1) i
  let iTj : Fin
      ((ett.series.data.tree jSlot.succ.castSucc).length + 1) :=
    Fin.castLE (Nat.succ_le_succ hseedTj.1) iSeed
  unfold TreeVerticesBefore
  apply Finset.mem_filter.mpr
  refine ⟨?_, iTj, terminalInTj, ?_, hterminalInTj, ?_⟩
  · exact vertexTransfer (hpreviousTj hjPositive)
      (by simp [TreeSequenceVertexSet])
  · exact (hseedTj.2.1 iSeed).trans (hprevSeed.2.1 i)
  · change i.val < seed.length
    exact lt_of_le_of_lt (Nat.lt_succ_iff.mp i.isLt)
      (hpreviousStrict hjPositive)

private theorem helper_hseedBuild_6103.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hjSlot : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal)
      (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : jSlot.castSucc.succ = jSlot.succ.castSucc)
      (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc))
      (_ :
        ∀ {A B C : TreeSequence G e0},
          TreeSequenceInitialSegment A C →
            TreeSequenceInitialSegment B C →
              A.length ≤ B.length → TreeSequenceInitialSegment A B)
      (TjPrime : TreeSequence G e0) (hqLast : indices0 (Fin.last p0) = q),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u)),
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀ (_ : (0 : ℕ) < (↑jSlot : ℕ) → Tprevious.length < seed.length)
      (_ : (0 : ℕ) < (↑jSlot : ℕ) → TreeSequenceInitialSegment Tprevious seed)
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : Fin (TjPrime.length + (1 : ℕ))) (_ : (0 : ℕ) < (↑jSlot : ℕ))
      (lower :
        ExtendedTashkinovTree G k e0 input
          (ett.series.data.tree
            (⟨(↑jSlot : ℕ) + (1 : ℕ), by
                omega⟩ :
              Fin (ett.rounds + (2 : ℕ))))
          (ett.series.data.coloring
            (⟨(↑jSlot : ℕ), by
                omega⟩ :
              Fin (ett.rounds + (1 : ℕ)))))
      (_ : lower.rounds = (↑jSlot : ℕ)),
    ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.PE ∧
        TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) Tprevious
          seed ∨
      (ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.SE ∨
          ett.series.data.kind jSlot.castSucc = some TashkinovExtensionKind.RE) ∧
        ∃ (f : E) (adjoinSeed : TreeSequence G e0),
          ett.series.data.connectingEdges jSlot.castSucc = ({ f } : Finset E) ∧
            TreeSequenceAdjoinEdge Tprevious f adjoinSeed ∧
              TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc)
                adjoinSeed seed := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot hjSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj
      commonPrefix TjPrime hqLast H x componentPath u exitPath Tprevious hpreviousStrict
      hpreviousSeed zPosition u0 exitPath0 zPosition0 uPosition hjPositive lower hround
  exact @helper_hseedBuild_3505 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
      (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@hjSlot) (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj)
      (@commonPrefix) (@TjPrime) (@hqLast) (@x) (@componentPath) (@u) (@exitPath)
      (@hpreviousStrict) (@hpreviousSeed) (@zPosition) (@u0) (@exitPath0) (@zPosition0)
      (@uPosition) (@hjPositive) (@lower) (@hround)

private theorem helper_hLowerI_6128.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
       [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds)
      (_ : LowerRoundInductionHypothesis G k e0 ett.rounds) (v : V),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hjSlot : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (p0 : ℕ)
      (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc))
      (TjPrime : TreeSequence G e0) (hqLast : indices0 (Fin.last p0) = q) (_ _ : V ⊕ E)
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (rho3 : PartialEdgeColoring E k) (_ : Fin (TjPrime.length + (1 : ℕ)))
      (lower :
        ExtendedTashkinovTree G k e0 input
          (ett.series.data.tree
            (⟨(↑jSlot : ℕ) + (1 : ℕ), by
                omega⟩ :
              Fin (ett.rounds + (2 : ℕ))))
          (ett.series.data.coloring
            (⟨(↑jSlot : ℕ), by
                omega⟩ :
              Fin (ett.rounds + (1 : ℕ)))))
      (_ : lower.rounds = (↑jSlot : ℕ)) (Tstar : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 lower rho3 Tstar),
    MaximumProperty corr.replacementETT →
    ColoredVertexSetElementary G rho3 (TreeSequenceVertexSet Tstar) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive hlower v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hjSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedTj TjPrime hqLast a b zPosition0 rho3 uPosition lower hround
      _ corr hcorrMP
  have hcorrRounds : corr.replacementETT.rounds = jSlot.val :=
    corr.rungAgreement.trans hround
  have hpackCorr := hlower corr.replacementETT
    corr.replacementETT.roundsPositive (by omega) hcorrMP
  unfold ColoredVertexSetElementary
  intro a ha b hb hab
  exact hpackCorr.1 ha hb hab

private theorem helper_hLowerVI_6142.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
       [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    let Tprevious : TreeSequence G e0 := ett.series.data.tree jSlot.castSucc.castSucc;
    ∀
      (lower :
        ExtendedTashkinovTree G k e0 input
          (ett.series.data.tree
            (⟨(↑jSlot : ℕ) + (1 : ℕ), by
                omega⟩ :
              Fin (ett.rounds + (2 : ℕ))))
          (ett.series.data.coloring
            (⟨(↑jSlot : ℕ), by
                omega⟩ :
              Fin (ett.rounds + (1 : ℕ))))),
    let nLower : Fin (lower.rounds + (1 : ℕ)) := Fin.last lower.rounds;
    ∀ (_ : lower.series.data.tree nLower.castSucc = Tprevious)
      (_ :
        lower.series.data.coloring nLower = ett.series.data.coloring jSlot.castSucc)
      (_ :
        TashkinovStoredColors lower.series.data nLower =
          TashkinovStoredColors ett.series.data jSlot.castSucc)
      (_ : LowerRoundProperties lower) (sigma : PartialEdgeColoring E k),
    IsProperEdgeColoring G sigma →
    IsOneEdgeUncolored sigma e0 →
    StableColoring Tprevious (TashkinovStoredColors ett.series.data jSlot.castSucc)
        (ett.series.data.coloring jSlot.castSucc) sigma →
    ModColoring lower sigma := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot Tprevious lower nLower hLowerTree hLowerColor hLowerStored hLowerPack
      sigma0 hsigma0Proper hsigma0One hsigma0Stable
  apply hLowerPack.2.2.2.2.2 sigma0 hsigma0Proper hsigma0One
  change StableColoring (lower.series.data.tree nLower.castSucc)
    (TashkinovStoredColors lower.series.data nLower)
    (lower.series.data.coloring nLower) sigma0
  rw [hLowerTree, hLowerStored, hLowerColor]
  exact hsigma0Stable

private theorem helper_branch_6176.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hjSlot : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal) (p0 : ℕ)
      (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (hseedTj : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc))
      (TjPrime : TreeSequence G e0) (hseedPrime : TreeSequenceInitialSegment seed TjPrime)
      (hqLast : indices0 (Fin.last p0) = q) (u0 : V)
      (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (uPosition : Fin (TjPrime.length + (1 : ℕ)))
      (_ : TjPrime.vertex uPosition = u0)
      (_ : seed.length < (↑uPosition : ℕ)),
    let terminalInTj : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)) :=
      Fin.castLE
        (by
          first
          | omega
          | ( have := GoldbergSeymour.TreeSequence.positive T
              have := Fin.isLt terminalPosition
              have := hseedTj.1
              have := hseedPrime.1
              have :=
                GoldbergSeymour.TreeSequence.positive
                  (TreeSequencePrefix
                    (ett.series.data.tree
                      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
                            omega⟩ :
                          Fin ett.rounds).succ.castSucc)
                    (↑terminalPosition : ℕ) hterminalPositionPositive
                    hterminalPositionBound)
              have :=
                GoldbergSeymour.TreeSequence.positive
                  (ett.series.data.tree
                    (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
                          omega⟩ :
                        Fin ett.rounds).succ.castSucc)
              all_goals omega))
        (Fin.last seed.length);
    ∀ (_ : (↑terminalInTj : ℕ) = seed.length)
      (lower :
        ExtendedTashkinovTree G k e0 input
          (ett.series.data.tree
            (⟨(↑jSlot : ℕ) + (1 : ℕ), by
                omega⟩ :
              Fin (ett.rounds + (2 : ℕ))))
          (ett.series.data.coloring
            (⟨(↑jSlot : ℕ), by
                omega⟩ :
              Fin (ett.rounds + (1 : ℕ)))))
      (_ : lower.rounds = (↑jSlot : ℕ))
      (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length)
      (_ : (↑a : ℕ) < (↑zPosition0 : ℕ)),
    (∃ (a_1 : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
        seed.length ≤ (↑a_1 : ℕ) ∧
          (↑a_1 : ℕ) < (↑zPosition0 : ℕ) ∧
            (ett.series.data.tree jSlot.succ.castSucc).edge a_1 =
              (ett.series.data.tree jSlot.succ.castSucc).edge a) ∨
      ∃ (a_1 : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))),
        TjPrime.vertex uPosition = u0 ∧
          (↑a_1 : ℕ) < (↑uPosition : ℕ) ∧
            TjPrime.edge a_1 = (ett.series.data.tree jSlot.succ.castSucc).edge a := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot hjSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed hseedTj TjPrime hseedPrime hqLast u0 zPosition0 uPosition
      huPosition hseedBeforeU terminalInTj hterminalInTjVal lower hround a ha
  by_cases haseed : seed.length ≤ a.val
  · exact Or.inl ⟨a, haseed, ha, rfl⟩
  · apply Or.inr
    let aSeed : Fin seed.length := ⟨a.val, by omega⟩
    let aPrime : Fin TjPrime.length :=
      Fin.castLE hseedPrime.1 aSeed
    refine ⟨aPrime, uPosition, huPosition, ?_, ?_⟩
    · change a.val < uPosition.val
      omega
    · have haCast : Fin.castLE hseedTj.1 aSeed = a := by
        apply Fin.ext
        rfl
      exact (hseedPrime.2.2 aSeed).trans
        ((hseedTj.2.2 aSeed).symm.trans
          (congrArg
            (ett.series.data.tree
              jSlot.succ.castSucc).edge haCast))

theorem helper_branch_13578.{u_1, u_2} :
    helperBranch13578Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma this q
      hqTerminal hvFinal hfirstUpper hfirstPositive jSlot hjSlot vertexTransfer trace hterminalJ
      p0 indices0 gamma0 delta0 rho1 hb2Missing hb2TreeEdges terminalPosition
      hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj hseedTerminal
      hTjQ commonPrefix TjPrime hclosure hprimeElementary hseedPrime hqLast gammaFirst
      hterminalInclusion hdeltaMissing H a b x componentPath u exitPath Tprevious hpreviousTj
      hpreviousStrict hpreviousSeed haugmentation zPosition u0 huPrime0 huOutside0 exitPath0
      beta0 hbeta0 z0 hz0 zPosition0 hzPosition0 hzAfter0 rho3 hrho3Proper hrho3One hd1
      hd2Missing hd2Edges hdeltaZ hd2z hd3 uPosition huPosition hseedBeforeU terminalInTj
      hterminalInTj hterminalInTjVal hterminalBeforeZ hzChoiceForContradiction hjPositive
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
  have hTpreviousBefore : TreeSequenceVertexSet Tprevious ⊆
      TreeVerticesBefore
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ := by
    exact @helper_hTpreviousBefore_6081 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@vertexTransfer) (@hterminalJ) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj) (@hpreviousTj)
        (@hpreviousStrict) (@hpreviousSeed) (@hterminalInTj) (@hjPositive)
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
    exact @helper_hseedBuild_6103 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@trace) (@p0)
        (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@commonPrefix) (@TjPrime) (@hqLast)
        (@x) (@componentPath) (@u) (@exitPath) (@hpreviousStrict) (@hpreviousSeed) (@zPosition)
        (@u0) (@exitPath0) (@zPosition0) (@uPosition) (@hjPositive) (@lower) (@hround)
  have hLowerPack :=
    hlower lower (by omega) (by omega) hLowerMP
  have hLowerI : ∀ (Tstar : TreeSequence G e0)
      (corr : CorrespondingExtendedTashkinovTree G k e0 lower rho3
        Tstar),
      MaximumProperty corr.replacementETT →
        ColoredVertexSetElementary G rho3
          (TreeSequenceVertexSet Tstar) := by
    exact @helper_hLowerI_6128 (@V) (@E) inferInstance inferInstance  inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@hlower) (@v)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@p0) (@indices0)
        (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj)
        (@TjPrime) (@hqLast) (@a) (@b) (@zPosition0) (@rho3) (@uPosition) (@lower) (@hround)
  have hLowerVI : ∀ sigma : PartialEdgeColoring E k,
      IsProperEdgeColoring G sigma →
      IsOneEdgeUncolored sigma e0 →
      StableColoring Tprevious
          (TashkinovStoredColors ett.series.data jSlot.castSucc)
          (ett.series.data.coloring jSlot.castSucc) sigma →
        ModColoring lower sigma := by
    exact @helper_hLowerVI_6142 (@V) (@E) inferInstance inferInstance  inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@lower) (@hLowerTree) (@hLowerColor)
        (@hLowerStored) (@hLowerPack)
  exact ExtensionBaseCaseTwoContradiction ett lower jSlot hjPositive
    Tprevious (ett.series.data.tree jSlot.succ.castSucc) seed TjPrime
    (ett.series.data.coloring jSlot.castSucc) rho1 rho3
    (TashkinovStoredColors ett.series.data jSlot.castSucc)
    v u0 z0 beta0 gammaFirst delta hterminalJ huPrime0 hz0
    zPosition0 uPosition hzPosition0 huPosition hseedTj hseedPrime
    hseedTerminal hzAfter0 hseedBeforeU hterminalBeforeZ
    (by
      intro huTj
      exact huOutside0 (vertexTransfer hTjQ huTj))
    rfl rfl rfl rfl hround hLowerTree hLowerColor hLowerStored
    hLowerKind hLowerConnecting hTpreviousBefore hseedBuild haugmentation
    hclosure hprimeElementary hMP hLowerMP hLowerI
    hLowerVI hb2Missing.1
    (fun a => (hb2TreeEdges a).1.trans (hb2TreeEdges a).2)
    hterminalInclusion hdeltaMissing hbeta0 hrho3Proper hrho3One hd1
    hd2Missing
    (fun f hf => by
      apply hd2Edges f
      rcases hf with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
      · exact @helper_branch_6176 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
          (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
          (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@p0) (@indices0) (@terminalPosition)
          (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj) (@TjPrime)
          (@hseedPrime) (@hqLast) (@u0) (@zPosition0) (@uPosition) (@huPosition) (@hseedBeforeU)
          (@hterminalInTjVal) (@lower) (@hround) (@a) (@ha)
      · exact Or.inr ⟨a, uPosition, huPosition, ha, rfl⟩)
    hdeltaZ hd2z hd3 hzChoiceForContradiction

private theorem helper_hmissingX_6300.{u_1, u_2} :
    helperHmissingX6300Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v this q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      hseedTj TjPrime a u0 z0 hz0 zPosition0 hzPosition0 rho3 uPosition terminalInTj
      hterminalInTjVal huPositionPositive huPositionBound hzPositionPositive hzPositionBound U Z
      hZTj hseedU hterminalInclusionRho3 hbeforeZMissing M huU heveryNewRightEntry hrightOrder
      hseedZSegment n hnU hnM hnM' X j i hvertexMZ hrightOutside hiSeed hiZ ZX hZXZ hZXlen A
      hlenA c hmissingZX hleftX
  unfold TreeMissingColors at hmissingZX ⊢
  obtain ⟨y, hyZX, hcMissing⟩ :=
    Finset.mem_biUnion.mp hmissingZX
  simp only [TreeSequenceVertexSet, Finset.mem_image,
    Finset.mem_univ, true_and] at hyZX
  obtain ⟨a, ha⟩ := hyZX
  have hcMissingY : c ∈ MissingColors G
      (ett.series.data.coloring jSlot.castSucc) y := by
    simpa [ha] using hcMissing
  have hyX : y ∈ TreeSequenceVertexSet X := by
    by_cases hyU : y ∈ TreeSequenceVertexSet U
    · exact hleftX hyU
    · have haPos : 1 ≤ a.val := by
        by_contra hzero
        have haZero : a.val = 0 := by omega
        let pZero : Fin (seed.length + 1) := ⟨0, by omega⟩
        have hZp := hseedZSegment.2.1 pZero
        have hUp := hseedU.2.1 pZero
        apply hyU
        simp only [TreeSequenceVertexSet, Finset.mem_image,
          Finset.mem_univ, true_and]
        refine ⟨Fin.castLE (Nat.succ_le_succ hseedU.1)
          pZero, ?_⟩
        have haZ : Z.vertex (Fin.castLE
            (Nat.succ_le_succ (Nat.le_of_lt hiZ)) a) = y := by
          simpa [ZX, TreeSequencePrefix] using ha
        have ha0 : Fin.castLE
              (Nat.succ_le_succ (Nat.le_of_lt hiZ)) a =
            Fin.castLE
              (Nat.succ_le_succ hseedZSegment.1) pZero := by
          apply Fin.ext
          exact haZero
        rw [ha0, hZp] at haZ
        exact hUp.trans haZ
      let r : Fin Z.length := ⟨a.val - 1, by
        have haLt : a.val < ZX.length + 1 := a.isLt
        simp [ZX] at haLt
        omega⟩
      have hrSucc : r.succ = Fin.castLE
          (Nat.succ_le_succ (Nat.le_of_lt hiZ)) a := by
        apply Fin.ext
        exact Nat.sub_add_cancel haPos
      have hry : Z.vertex r.succ = y := by
        rw [hrSucc]
        simpa [ZX, TreeSequencePrefix] using ha
      have hrOutside :
          Z.vertex r.succ ∉ TreeSequenceVertexSet U := by
        simpa [hry] using hyU
      have hri : r.val < i.val := by
        have haLt : a.val < ZX.length + 1 := a.isLt
        simp [ZX, r] at haLt ⊢
        omega
      obtain ⟨q0, hqU, hedgeq, hvertexq⟩ :=
        heveryNewRightEntry r hrOutside
      have hqn : q0.val < n :=
        hrightOrder r i hrOutside hrightOutside hri q0 j
          hvertexq hvertexMZ
      simp only [TreeSequenceVertexSet, Finset.mem_image,
        Finset.mem_univ, true_and]
      let qX : Fin (X.length + 1) := ⟨q0.val + 1, by
        change q0.val + 1 < n + 1
        omega⟩
      refine ⟨qX, ?_⟩
      rw [← hry, ← hvertexq]
      change M.vertex _ = M.vertex q0.succ
      congr 1
  by_cases hyTerminal : y = v
  · have hcTerminalOld : c ∈ MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v := by
      rw [← hyTerminal]
      exact hcMissingY
    rcases Finset.mem_union.mp
        (hterminalInclusionRho3 hcTerminalOld) with
      hcTerminal | hcU
    · exact Finset.mem_biUnion.mpr
        ⟨v, by simpa [hyTerminal] using hyX, hcTerminal⟩
    · exact Finset.mem_biUnion.mpr ⟨u0, hleftX huU, hcU⟩
  · have hyBefore : y ∈ TreeVerticesBefore
        (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 := by
      unfold TreeVerticesBefore
      apply Finset.mem_filter.mpr
      let aZ : Fin (Z.length + 1) :=
        Fin.castLE (Nat.succ_le_succ hZXZ.1) a
      let aTj : Fin
          ((ett.series.data.tree
            jSlot.succ.castSucc).length + 1) :=
        Fin.castLE (Nat.succ_le_succ hZTj.1) aZ
      have haTj :
          (ett.series.data.tree
            jSlot.succ.castSucc).vertex aTj = y :=
        (hZTj.2.1 aZ).trans ((hZXZ.2.1 a).trans ha)
      refine ⟨?_, aTj, zPosition0, haTj,
        hzPosition0, ?_⟩
      · simp only [TreeSequenceVertexSet,
          Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨aTj, haTj⟩
      change a.val < zPosition0.val
      have haLt := a.isLt
      have hiLt := i.isLt
      simp [ZX, Z, TreeSequencePrefix] at haLt hiLt
      omega
    refine Finset.mem_biUnion.mpr ⟨y, hyX, ?_⟩
    rw [hbeforeZMissing y hyBefore hyTerminal]
    exact hcMissingY

theorem helper_branch_15674.{u_1, u_2} :
    helperBranch15674Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime
      hb2EdgesFromSeed H a b x componentPath u exitPath zPosition u0 exitPath0 z0 hz0 zPosition0
      hzPosition0 rho3 hd2Edges uPosition terminalInTj hterminalInTjVal huPositionPositive
      huPositionBound hzPositionPositive hzPositionBound U Z hZTj hseedU hterminalInclusionRho3
      hbeforeZMissing M huU hroutePhiZ hleftSegment hnewEntryFromRight heveryNewRightEntry
      hrightOrder prefixSegment prefixPrefix hseedZSegment firstStep n hnU ih hnM
  by_cases hnEq : n = M.length
  · omega
  have hnSuccM : n + 1 ≤ M.length := by omega
  have hnM' : n ≤ M.length :=
    Nat.le_trans (Nat.le_succ n) hnSuccM
  have ih' := ih hnM'
  let X := TreeSequencePrefix M n
    (Nat.le_trans U.positive hnU) hnM'
  let Y := TreeSequencePrefix M (n + 1)
    (Nat.le_trans U.positive
      (Nat.le_trans hnU (Nat.le_succ n))) hnSuccM
  let j : Fin M.length := ⟨n, by omega⟩
  obtain ⟨i, hedgeMZ, hvertexMZ⟩ :=
    hnewEntryFromRight j hnU
  have hrightOutside :
      Z.vertex i.succ ∉ TreeSequenceVertexSet U := by
    exact @helper_hrightOutside_7601 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
        (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@a) (@x) (@componentPath) (@u)
        (@exitPath) (@zPosition) (@u0) (@exitPath0) (@zPosition0) (@uPosition)
        (@huPositionPositive) (@huPositionBound) (@hzPositionPositive) (@hzPositionBound) (@M)
        (@hleftSegment) (@n) (@hnU) (@hnM) (@i) (@hvertexMZ)
  have hiSeed : seed.length ≤ i.val := by
    by_contra hnot
    have hi : i.val < seed.length := Nat.lt_of_not_ge hnot
    let a : Fin (seed.length + 1) := ⟨i.val + 1, by omega⟩
    have hZSeedA : Z.vertex
          (Fin.castLE (Nat.succ_le_succ hseedZSegment.1) a) =
        seed.vertex a := hseedZSegment.2.1 a
    apply hrightOutside
    simp only [TreeSequenceVertexSet, Finset.mem_image,
      Finset.mem_univ, true_and]
    refine ⟨Fin.castLE (Nat.succ_le_succ hseedU.1) a, ?_⟩
    have hia : Fin.castLE
        (Nat.succ_le_succ hseedZSegment.1) a = i.succ :=
      Fin.ext (by simp [a])
    rw [hia] at hZSeedA
    exact (hseedU.2.1 a).trans hZSeedA.symm
  have hiZ : i.val < Z.length := i.isLt
  let ZX := TreeSequencePrefix Z i.val
    (Nat.le_trans seed.positive hiSeed) (Nat.le_of_lt hiZ)
  have hseedZX : TreeSequenceInitialSegment seed ZX := by
    refine ⟨hiSeed, ?_, ?_⟩
    · intro a
      change Z.vertex _ = seed.vertex a
      calc
        Z.vertex _ = Z.vertex (Fin.castLE
            (Nat.succ_le_succ hseedZSegment.1) a) := by
          congr 1
        _ = seed.vertex a := hseedZSegment.2.1 a
    · intro a
      change Z.edge _ = seed.edge a
      calc
        Z.edge _ = Z.edge
            (Fin.castLE hseedZSegment.1 a) := by congr 1
        _ = seed.edge a := hseedZSegment.2.2 a
  have hZXZ : TreeSequenceInitialSegment ZX Z :=
    prefixSegment Z i.val
      (Nat.le_trans seed.positive hiSeed) (Nat.le_of_lt hiZ)
  have hsuffix : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) ZX Z :=
    TashkinovAugmentationSequenceSuffix _ seed ZX Z
      hroutePhiZ hseedZX hZXZ
  have hZXlen : ZX.length = i.val := rfl
  obtain ⟨A, hZXA, hAZ⟩ := firstStep hsuffix (by omega)
  rcases hZXA with
    ⟨hlenA, hZXASegment, c, hcolorA, hmissingZX⟩
  have hAZSegment : TreeSequenceInitialSegment A Z :=
    TashkinovAugmentationSequenceInitialSegment _ A Z hAZ
  have hAi : A.length = i.val + 1 := by omega
  let ai : Fin A.length := ⟨i.val, by omega⟩
  have hcolorZ :
      ett.series.data.coloring jSlot.castSucc (Z.edge i) =
        some c := by
    have haiLast : ai =
        Fin.cast hlenA.symm (Fin.last ZX.length) := by
      apply Fin.ext
      simp [ai, hZXlen]
    have hZai : Z.edge (Fin.castLE hAZSegment.1 ai) =
        A.edge ai := hAZSegment.2.2 ai
    have hcast : Fin.castLE hAZSegment.1 ai = i := by
      apply Fin.ext
      simp [ai]
    rw [← hcast, hZai, haiLast]
    exact hcolorA
  have hleftX {y : V} (hyU : y ∈ TreeSequenceVertexSet U) :
      y ∈ TreeSequenceVertexSet X := by
    exact @helper_hleftX_4557 (@V) (@E) (@G) (@e0) (@TjPrime) (@b) (@uPosition)
        (@huPositionPositive) (@huPositionBound) (@M) (@hleftSegment) (@n) (@hnU)
        (@hnM') (@y) (@hyU)
  have hmissingX : c ∈ TreeMissingColors rho3 X := by
    exact @helper_hmissingX_6300 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@a) (@u0) (@z0) (@hz0) (@zPosition0)
        (@hzPosition0) (@rho3) (@uPosition) (@hterminalInTjVal) (@huPositionPositive)
        (@huPositionBound) (@hzPositionPositive) (@hzPositionBound) (@hZTj) (@hseedU)
        (@hterminalInclusionRho3) (@hbeforeZMissing) (@M) (@huU) (@heveryNewRightEntry)
        (@hrightOrder) (@hseedZSegment) (@n) (@hnU) (@hnM) (@hnM') (@i) (@hvertexMZ)
        (@hrightOutside) (@hiSeed) (@hiZ) (@hZXZ) (@hZXlen) (@A) (@hlenA) (@c) (@hmissingZX)
        (@hleftX)
  have hXY : TashkinovAugmentation rho3 X Y := by
    exact @helper_hXY_7786 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0)
        (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@hb2EdgesFromSeed) (@x) (@componentPath)
        (@u) (@exitPath) (@zPosition) (@u0) (@exitPath0) (@zPosition0) (@rho3) (@hd2Edges)
        (@uPosition) (@huPositionPositive) (@huPositionBound) (@hzPositionPositive)
        (@hzPositionBound) (@hZTj) (@M) (@prefixPrefix) (@n) (@hnU) (@hnM) (@hnSuccM) (@hnM')
        (@i) (@hedgeMZ) (@hiSeed) (@c) (@hcolorZ) (@hmissingX)
  change TashkinovAugmentationSequence rho3 U Y
  exact Relation.ReflTransGen.tail ih' hXY

private theorem helper_hrouteUM_6564.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (hseedTj : TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc))
      (TjPrime : TreeSequence G e0)
      (_ :
        ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
          seed.length ≤ (↑a : ℕ) →
            rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
              ett.series.data.coloring jSlot.castSucc
                ((ett.series.data.tree jSlot.succ.castSucc).edge a)),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    let _ : Set (V ⊕ E) := TwoColorComponent G rho1 gamma delta (Sum.inl v);
    ∀ (_ _ : V ⊕ E) (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ :
        TashkinovAugmentationSequence (ett.series.data.coloring jSlot.castSucc) seed
          (ett.series.data.tree jSlot.succ.castSucc))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u0 : V)
      (_ :
        (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
      (z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
      (zPosition0 : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition0 = z0)
      (rho3 : PartialEdgeColoring E k)
      (_ :
        ∀ (f : E),
          ((∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
                seed.length ≤ (↑a : ℕ) ∧
                  (↑a : ℕ) < (↑zPosition0 : ℕ) ∧
                    (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
              ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))),
                TjPrime.vertex uPosition = u0 ∧
                  (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) →
            rho3 f = rho1 f)
      (uPosition : Fin (TjPrime.length + (1 : ℕ))),
    let terminalInTj : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)) :=
      Fin.castLE
        (by
          first
          | omega
          | ( have := GoldbergSeymour.TreeSequence.positive T
              have := Fin.isLt terminalPosition
              have := hseedTj.1
              have :=
                GoldbergSeymour.TreeSequence.positive
                  (TreeSequencePrefix
                    (ett.series.data.tree
                      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
                            omega⟩ :
                          Fin ett.rounds).succ.castSucc)
                    (↑terminalPosition : ℕ) hterminalPositionPositive
                    hterminalPositionBound)
              have :=
                GoldbergSeymour.TreeSequence.positive
                  (ett.series.data.tree
                    (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
                          omega⟩ :
                        Fin ett.rounds).succ.castSucc)
              all_goals omega))
        (Fin.last seed.length);
    ∀ (_ : (↑terminalInTj : ℕ) = seed.length)
      (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length)
      (hzPositionPositive : (1 : ℕ) ≤ (↑zPosition0 : ℕ))
      (hzPositionBound :
        (↑zPosition0 : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
    let Z : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑zPosition0 : ℕ)
        hzPositionPositive hzPositionBound;
    ∀ (_ : TreeSequenceInitialSegment Z (ett.series.data.tree jSlot.succ.castSucc))
      (_ : TreeSequenceInitialSegment seed U)
      (_ : TreeSequenceInitialSegment seed Z)
      (_ :
        MissingColors G (ett.series.data.coloring jSlot.castSucc) v ⊆
          MissingColors G rho3 v ∪ MissingColors G rho3 u0)
      (_ :
        ∀ (y : V)
          (_ : y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z0 hz0)
          (_ : y ≠ v),
          MissingColors G rho3 y =
            MissingColors G (ett.series.data.coloring jSlot.castSucc) y)
      (M : TreeSequence G e0) (_ : OrderedTreeUnion U Z M)
      (_ : u0 ∈ TreeSequenceVertexSet U),
    TashkinovAugmentationSequence rho3 U M := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime
      hb2EdgesFromSeed H C a b x componentPath u exitPath haugmentation zPosition u0 exitPath0 z0
      hz0 zPosition0 hzPosition0 rho3 hd2Edges uPosition terminalInTj hterminalInTjVal
      huPositionPositive huPositionBound hzPositionPositive hzPositionBound U Z hZTj hseedU
      hseedZ hterminalInclusionRho3 hbeforeZMissing M hunion huU
  have hroutePhiZ : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) seed Z :=
    TashkinovAugmentationSequenceRestrict _ seed Z _ haugmentation
      hseedZ hZTj
  have hleftSegment := hunion.leftSegment
  have hnewEntryFromRight := hunion.newEntryFromRight
  have heveryNewRightEntry := hunion.everyNewRightEntry
  have hrightOrder := hunion.rightOrder
  have prefixSegment (A : TreeSequence G e0) (q0 : Nat)
      (hq0 : 1 ≤ q0) (hqA : q0 ≤ A.length) :
      TreeSequenceInitialSegment
        (TreeSequencePrefix A q0 hq0 hqA) A := by
    exact @helper_prefixSegment_4407 (@V) (@E) (@G) (@e0) (@A) (@q0) (@hq0) (@hqA)
  have prefixPrefix (A : TreeSequence G e0) (q0 : Nat)
      (hq0 : 1 ≤ q0) (hqA : q0 + 1 ≤ A.length) :
      TreeSequenceInitialSegment
        (TreeSequencePrefix A q0 hq0
          (Nat.le_trans (Nat.le_succ q0) hqA))
        (TreeSequencePrefix A (q0 + 1) (by omega) hqA) := by
    exact @helper_prefixPrefix_7534 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
        (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@x) (@componentPath) (@u) (@exitPath)
        (@zPosition) (@u0) (@exitPath0) (@zPosition0) (@uPosition) (@A) (@q0) (@hq0) (@hqA)
  have prefixSelf (A : TreeSequence G e0) :
      TreeSequencePrefix A A.length A.positive le_rfl = A := by
    exact @helper_prefixSelf_4429 (@V) (@E) (@G) (@e0) (@A)
  have equalPrefixes {A B D : TreeSequence G e0}
      (hAD : TreeSequenceInitialSegment A D)
      (hBD : TreeSequenceInitialSegment B D)
      (hlen : A.length = B.length) : A = B := by
    exact @helper_equalPrefixes_6220 (@V) (@E) (@G) (@e0) (@A) (@B) (@D) (@hAD) (@hBD)
        (@hlen)
  have prefixAtLeft :
      TreeSequencePrefix M U.length U.positive hleftSegment.1 = U := by
    apply equalPrefixes
      (prefixSegment M U.length U.positive hleftSegment.1)
      hleftSegment
    rfl
  have hseedZSegment : TreeSequenceInitialSegment seed Z :=
    TashkinovAugmentationSequenceInitialSegment _ seed Z hroutePhiZ
  have firstStep {A B : TreeSequence G e0}
      (hAB : TashkinovAugmentationSequence
        (ett.series.data.coloring jSlot.castSucc) A B)
      (hlt : A.length < B.length) :
      ∃ C, TashkinovAugmentation
          (ett.series.data.coloring jSlot.castSucc) A C ∧
        TashkinovAugmentationSequence
          (ett.series.data.coloring jSlot.castSucc) C B := by
    unfold TashkinovAugmentationSequence at hAB ⊢
    induction hAB using Relation.ReflTransGen.head_induction_on with
    | refl => omega
    | @head A C hAC hCB ih => exact ⟨C, hAC, hCB⟩
  have replay : ∀ n (hnU : U.length ≤ n) (hnM : n ≤ M.length),
      TashkinovAugmentationSequence rho3 U
        (TreeSequencePrefix M n
          (Nat.le_trans U.positive hnU) hnM) := by
    intro n hnU hnM
    induction n, hnU using Nat.le_induction with
    | base =>
        simpa [prefixAtLeft] using
          (show TashkinovAugmentationSequence rho3 U U from
            Relation.ReflTransGen.refl)
    | @succ n hnU ih =>
        exact @helper_branch_15674 (@V) (@E) inferInstance inferInstance inferInstance (@G)
            (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
            (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
            (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
            (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@hb2EdgesFromSeed) (@a) (@b) (@x)
            (@componentPath) (@u) (@exitPath) (@zPosition) (@u0) (@exitPath0) (@z0) (@hz0)
            (@zPosition0) (@hzPosition0) (@rho3) (@hd2Edges) (@uPosition) (@hterminalInTjVal)
            (@huPositionPositive) (@huPositionBound) (@hzPositionPositive) (@hzPositionBound)
            (@hZTj) (@hseedU) (@hterminalInclusionRho3) (@hbeforeZMissing) (@M) (@huU)
            (@hroutePhiZ) (@hleftSegment) (@hnewEntryFromRight) (@heveryNewRightEntry)
            (@hrightOrder) (@prefixSegment) (@prefixPrefix) (@hseedZSegment) (@firstStep) (@n)
            (@hnU) (@ih) (@hnM)
  have hfull := replay M.length hleftSegment.1 le_rfl
  simpa [prefixSelf] using hfull

theorem helper_branch_15847.{u_1, u_2} :
    helperBranch15847Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hMP hpositive v gamma delta sigma this q
      hqTerminal hvFinal hfirstUpper hfirstPositive jSlot segmentTrans vertexTransfer trace
      hterminalJ p0 indices0 gamma0 delta0 rho1 hb2Missing terminalPosition
      hterminalPositionPositive hterminalPositionBound seed hseedTj hseedTerminal hTjQ
      hseedVertexBefore segmentVertexBefore transportSeedRoute commonPrefix TjPrime hclosure
      hseedPrime gammaFirst hterminalInclusion hb2EdgesFromSeed hdeltaMissing H C a b x
      componentPath u exitPath haugmentation zPosition u0 huPrime0 huOutside0 exitPath0 beta0 z0
      hz0 zPosition0 hzPosition0 hzAfter0 rho3 hrho3Proper hrho3One hd1 hd2Missing hd2Edges
      hdeltaZ hd2z hd3 hu0Terminal uPosition huPosition hseedBeforeU terminalInTj hterminalInTj
      hterminalInTjVal hzv hterminalBeforeZ hzChoiceForContradiction hjPositive
  have hjZero : jSlot.val = 0 := Nat.eq_zero_of_not_pos hjPositive
  have huPositionPositive : 1 ≤ uPosition.val :=
    seed.positive.trans (Nat.le_of_lt hseedBeforeU)
  have huPositionBound : uPosition.val ≤ TjPrime.length :=
    Nat.lt_succ_iff.mp uPosition.isLt
  have hzPositionPositive : 1 ≤ zPosition0.val :=
    seed.positive.trans hzAfter0
  have hzPositionBound : zPosition0.val ≤
      (ett.series.data.tree jSlot.succ.castSucc).length :=
    Nat.lt_succ_iff.mp zPosition0.isLt
  let U : TreeSequence G e0 :=
    TreeSequencePrefix TjPrime uPosition.val huPositionPositive
      huPositionBound
  let Z : TreeSequence G e0 :=
    TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
      zPosition0.val hzPositionPositive hzPositionBound
  have hUPrime : TreeSequenceInitialSegment U TjPrime := by
    exact @helper_hUPrime_4274 (@V) (@E) (@G) (@e0) (@TjPrime) (@uPosition)
        (@huPositionPositive) (@huPositionBound)
  have hZTj : TreeSequenceInitialSegment Z
      (ett.series.data.tree jSlot.succ.castSucc) := by
    exact @helper_hZTj_4280 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@zPosition0) (@hzPositionPositive)
        (@hzPositionBound)
  have hseedU : TreeSequenceInitialSegment seed U := by
    apply commonPrefix hseedPrime hUPrime
    exact Nat.le_of_lt hseedBeforeU
  have hseedZ : TreeSequenceInitialSegment seed Z := by
    apply commonPrefix hseedTj hZTj
    exact hzAfter0
  have hrouteRhoOneU : TashkinovAugmentationSequence rho1 seed U :=
    TashkinovAugmentationSequenceRestrict rho1 seed U TjPrime
      hclosure.1 hseedU hUPrime
  have hprimeVertexBefore (i : Fin (TjPrime.length + 1))
      (hi : i.val < uPosition.val) :
      TjPrime.vertex i ∈ TreeVerticesBefore TjPrime u0 huPrime0 := by
    unfold TreeVerticesBefore
    apply Finset.mem_filter.mpr
    exact ⟨by simp [TreeSequenceVertexSet], i, uPosition,
      rfl, huPosition, hi⟩
  have hUsegmentVertexBefore {A : TreeSequence G e0}
      (hAU : TreeSequenceInitialSegment A U)
      (hAlen : A.length < U.length) {y : V}
      (hyA : y ∈ TreeSequenceVertexSet A) :
      y ∈ TreeVerticesBefore TjPrime u0 huPrime0 := by
    exact @helper_hUsegmentVertexBefore_7424 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
        (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@x) (@componentPath) (@u) (@exitPath)
        (@zPosition) (@u0) (@huPrime0) (@exitPath0) (@zPosition0) (@uPosition)
        (@huPositionPositive) (@huPositionBound) (@hUPrime) (@hprimeVertexBefore) (@A) (@hAU)
        (@hAlen) (@y) (@hyA)
  have hbeforePrimeNeU {y : V}
      (hy : y ∈ TreeVerticesBefore TjPrime u0 huPrime0) :
      y ≠ u0 := by
    exact @helper_hbeforePrimeNeU_7437 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
        (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@x) (@componentPath) (@u) (@exitPath)
        (@zPosition) (@u0) (@huPrime0) (@exitPath0) (@zPosition0) (@uPosition) (@y) (@hy)
  have hbeforePrimeMissing (y : V)
      (hy : y ∈ TreeVerticesBefore TjPrime u0 huPrime0) :
      MissingColors G rho3 y = MissingColors G rho1 y := by
    exact @helper_hbeforePrimeMissing_7447 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@TjPrime) (@u0)
        (@huPrime0) (@z0) (@hz0) (@rho3) (@hd2Missing) (@hd2z) (@hbeforePrimeNeU) (@y) (@hy)
  have transportUStep {A B : TreeSequence G e0}
      (hstep : TashkinovAugmentation rho1 A B)
      (hBU : TreeSequenceInitialSegment B U) :
      TashkinovAugmentation rho3 A B := by
    exact @helper_transportUStep_7455 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@segmentTrans)
        (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@x)
        (@componentPath) (@u) (@exitPath) (@zPosition) (@u0) (@huPrime0) (@exitPath0)
        (@zPosition0) (@rho3) (@hd2Edges) (@uPosition) (@huPosition) (@huPositionPositive)
        (@huPositionBound) (@hUPrime) (@hUsegmentVertexBefore) (@hbeforePrimeMissing) (@A) (@B)
        (@hstep) (@hBU)
  have transportURoute (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence rho1 S U) :
      TashkinovAugmentationSequence rho3 S U := by
    exact @helper_transportURoute_4333 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@v) (@sigma)
        (@hvFinal) (@trace) (@TjPrime) (@rho3) (@uPosition) (@huPositionPositive)
        (@huPositionBound) (@transportUStep) (@S) (@hroute)
  have hrouteRhoThreeU : TashkinovAugmentationSequence rho3 seed U :=
    transportURoute seed hrouteRhoOneU
  have hterminalNeU : v ≠ u0 := hu0Terminal.symm
  have hterminalMissingEq : MissingColors G rho3 v =
      MissingColors G rho1 v := by
    exact @helper_hterminalMissingEq_7478 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@TjPrime) (@u0)
        (@huPrime0) (@z0) (@hz0) (@rho3) (@hd2Missing) (@hzv) (@hterminalBeforeZ) (@hterminalNeU)
  have hterminalInclusionRho3 :
      MissingColors G (ett.series.data.coloring jSlot.castSucc) v ⊆
        MissingColors G rho3 v ∪ MissingColors G rho3 u0 := by
    exact @helper_hterminalInclusionRho3_4355 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
        (@v) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace)
        (@p0) (@gamma0) (@hterminalInclusion) (@u0) (@rho3) (@hd3) (@hterminalMissingEq)
  have hbeforeZData {y : V}
      (hy : y ∈ TreeVerticesBefore
        (ett.series.data.tree jSlot.succ.castSucc) z0 hz0) :
      y ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) ∧ y ≠ z0 := by
    exact @helper_hbeforeZData_7492 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0)
        (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@x) (@componentPath) (@u) (@exitPath)
        (@zPosition) (@u0) (@exitPath0) (@z0) (@hz0) (@zPosition0) (@uPosition) (@y) (@hy)
  have hbeforeZMissing (y : V)
      (hy : y ∈ TreeVerticesBefore
        (ett.series.data.tree jSlot.succ.castSucc) z0 hz0)
      (hyTerminal : y ≠ v) :
      MissingColors G rho3 y =
        MissingColors G (ett.series.data.coloring jSlot.castSucc) y := by
    exact @helper_hbeforeZMissing_7504 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@vertexTransfer) (@trace) (@hb2Missing)
        (@hTjQ) (@TjPrime) (@u0) (@huPrime0) (@huOutside0) (@z0) (@hz0) (@rho3) (@hd2Missing)
        (@hbeforeZData) (@y) (@hy) (@hyTerminal)
  obtain ⟨M, ⟨hunion⟩⟩ := OrderedTreeUnionExists U Z
  have huU : u0 ∈ TreeSequenceVertexSet U := by
    exact @helper_huU_4386 (@V) (@E) (@G) (@e0) (@TjPrime) (@u0) (@uPosition)
        (@huPosition) (@huPositionPositive) (@huPositionBound)
  have hrouteUM : TashkinovAugmentationSequence rho3 U M := by
    exact @helper_hrouteUM_6564 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0)
        (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (@TjPrime) (@hb2EdgesFromSeed) (@a) (@b) (@x)
        (@componentPath) (@u) (@exitPath) (@haugmentation) (@zPosition) (@u0) (@exitPath0) (@z0)
        (@hz0) (@zPosition0) (@hzPosition0) (@rho3) (@hd2Edges) (@uPosition) (@hterminalInTjVal)
        (@huPositionPositive) (@huPositionBound) (@hzPositionPositive) (@hzPositionBound) (@hZTj)
        (@hseedU) (@hseedZ) (@hterminalInclusionRho3) (@hbeforeZMissing) (@M) (@hunion) (@huU)
  exact @helper_caseContinuation_11664 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@v) (@gamma) (@delta)
      (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@segmentTrans)
      (@vertexTransfer) (@trace) (@hterminalJ) (@p0) (@indices0) (@gamma0) (@delta0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj)
      (@hseedTerminal) (@hTjQ) (@hseedVertexBefore) (@segmentVertexBefore) (@transportSeedRoute)
      (@commonPrefix) (@TjPrime) (@hdeltaMissing) (@a) (@x) (@componentPath) (@u) (@exitPath)
      (@zPosition) (@u0) (@huOutside0) (@exitPath0) (@beta0) (@z0) (@zPosition0) (@hzPosition0)
      (@rho3) (@hrho3Proper) (@hrho3One) (@hd1) (@hdeltaZ) (@uPosition) (@hterminalInTj) (@hzv)
      (@hzChoiceForContradiction) (@hjZero) (@huPositionPositive) (@huPositionBound)
      (@hzPositionPositive) (@hzPositionBound) (@hZTj) (@hseedZ) (@hrouteRhoThreeU)
      (@hterminalMissingEq) (@M) (@hunion) (@huU) (@hrouteUM)

theorem helper_continuation_12157.{u_1, u_2} :
    helperContinuation12157Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma this q
      hqTerminal hvStage hvFinal hfirstUpper hfirstPositive jSlot hjSlot segmentTrans
      vertexTransfer trace hterminalJ p0 indices0 gamma0 delta0 rho1 hb2Missing hb2TreeEdges
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj
      hseedTerminal hTjQ hseedVertexBefore segmentVertexBefore transportSeedRoute commonPrefix
      supportColors TjPrime hclosure hprimeElementary hseedPrime hterminalPrime hqLast gammaFirst
      hterminalInclusion hb2EdgesFromSeed hterminalSeed hseedN fN hdeltaMissing H C a b x
      componentPath u exitPath Tprevious hpreviousTj hpreviousStrict hpreviousSeed haugmentation
      zPosition hclaim45Package
  obtain ⟨u0, huPrime0, huOutside0, exitPath0, hexitPath0,
      hexitLength0, hexitSupport0, hexitIntersection0, hexitBoundary0,
      huNotFN0, beta0, hbeta0, hbetaSupport0, z0, hz0, zPosition0,
      hzPosition0, hzAfter0, hzChoice0, hzBefore0, hzEdges0, rho3,
      hrho3Proper, hrho3One, hd1, hd2Missing, hd2Edges, hdeltaZ,
      hd2z, hd3⟩ := hclaim45Package
  have hu0Terminal : u0 ≠ v := by
    intro huv
    exact huOutside0 (by simpa [huv] using hvStage)
  have hbeta0Terminal : beta0 ∉ MissingColors G rho1 v := by
    intro hbetaV
    have hdisjoint := hprimeElementary huPrime0 hterminalPrime hu0Terminal
    exact (Finset.disjoint_left.mp hdisjoint) hbeta0 hbetaV
  obtain ⟨uPosition, -, huPosition⟩ := Finset.mem_image.mp huPrime0
  have huNotSeed : u0 ∉ TreeSequenceVertexSet seed := by
    intro huSeed0
    exact huOutside0 (vertexTransfer hseedN huSeed0)
  have hseedBeforeU : seed.length < uPosition.val := by
    exact @helper_hseedBeforeU_7025 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0)
        (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@TjPrime) (@hseedPrime) (@x) (@componentPath) (@u) (@exitPath)
        (@zPosition) (@u0) (@exitPath0) (@zPosition0) (@uPosition) (@huPosition) (@huNotSeed)
  let terminalInTj : Fin
      ((ett.series.data.tree jSlot.succ.castSucc).length + 1) :=
    Fin.castLE (Nat.succ_le_succ hseedTj.1) (Fin.last seed.length)
  have hterminalInTj :
      (ett.series.data.tree jSlot.succ.castSucc).vertex terminalInTj = v := by
    exact (hseedTj.2.1 (Fin.last seed.length)).trans hseedTerminal
  have hterminalInTjVal : terminalInTj.val = seed.length := by
    rfl
  have hzTerminalIff : z0 = v ↔ zPosition0 = terminalInTj := by
    constructor
    · intro hzv
      apply (ett.series.data.tree
        jSlot.succ.castSucc).vertex_injective
      exact hzPosition0.trans (hzv.trans hterminalInTj.symm)
    · intro hpos
      exact hzPosition0.symm.trans (hpos ▸ hterminalInTj)
  have hzPositionCases :
      (z0 = v ∧ zPosition0.val = seed.length) ∨
        (z0 ≠ v ∧ seed.length < zPosition0.val) := by
    by_cases hzv : z0 = v
    · left
      refine ⟨hzv, ?_⟩
      rw [(hzTerminalIff.mp hzv), hterminalInTjVal]
    · right
      refine ⟨hzv, lt_of_le_of_ne hzAfter0 ?_⟩
      intro heq
      apply hzv
      apply hzTerminalIff.mpr
      apply Fin.ext
      simpa [hterminalInTjVal] using heq.symm
  by_cases hzv : z0 = v
  · exact @helper_branch_13441 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@v) (@gamma) (@delta)
      (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot)
      (@segmentTrans) (@vertexTransfer) (@trace) (@hterminalJ) (@p0) (@indices0) (@gamma0)
      (@delta0) (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
      (@hjTreeIndex) (@hseedTj) (@hseedTerminal) (@hTjQ) (@hseedVertexBefore)
      (@segmentVertexBefore) (@transportSeedRoute) (@commonPrefix) (@TjPrime) (@hclosure)
      (@hseedPrime) (@hqLast) (@hterminalSeed) (@a) (@x) (@componentPath) (@u) (@exitPath)
      (@hpreviousStrict) (@hpreviousSeed) (@zPosition) (@u0) (@huPrime0) (@huOutside0)
      (@exitPath0) (@beta0) (@z0) (@hz0) (@zPosition0) (@hzChoice0) (@rho3) (@hrho3Proper)
      (@hrho3One) (@hd1) (@hd2Missing) (@hd2Edges) (@hd2z) (@hbeta0Terminal) (@uPosition)
      (@huPosition) (@hseedBeforeU) (@hterminalInTj) (@hterminalInTjVal) (@hzTerminalIff) (@hzv)
  · have hseedBeforeZ : seed.length < zPosition0.val :=
      hzPositionCases.resolve_left (fun h => hzv h.1) |>.2
    have hterminalBeforeZ : v ∈ TreeVerticesBefore
        (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 := by
      unfold TreeVerticesBefore
      apply Finset.mem_filter.mpr
      refine ⟨hterminalJ, terminalInTj, zPosition0,
        hterminalInTj, hzPosition0, ?_⟩
      simpa [hterminalInTjVal] using hseedBeforeZ
    have hzChoiceForContradiction :
        zPosition0 = Fin.last
            (ett.series.data.tree jSlot.succ.castSucc).length ∨
          (zPosition0.val <
              (Fin.last
                (ett.series.data.tree jSlot.succ.castSucc).length).val ∧
            beta0 ∈ MissingColors G rho1 z0) := by
      exact @helper_hzChoiceForContradiction_7230 (@V) (@E) inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
          (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace)
          (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@beta0)
          (@z0) (@zPosition0) (@hzChoice0)
    by_cases hjPositive : 0 < jSlot.val
    · exact @helper_branch_13578 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
        (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper)
        (@hfirstPositive) (@hjSlot) (@vertexTransfer) (@trace) (@hterminalJ) (@p0) (@indices0)
        (@gamma0) (@delta0) (@hb2Missing) (@hb2TreeEdges) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj)
        (@hseedTerminal) (@hTjQ) (@commonPrefix) (@TjPrime) (@hclosure) (@hprimeElementary)
        (@hseedPrime) (@hqLast) (@hterminalInclusion) (@hdeltaMissing) (@a) (@b) (@x)
        (@componentPath) (@u) (@exitPath) (@hpreviousTj) (@hpreviousStrict) (@hpreviousSeed)
        (@haugmentation) (@zPosition) (@u0) (@huPrime0) (@huOutside0) (@exitPath0) (@beta0)
        (@hbeta0) (@z0) (@hz0) (@zPosition0) (@hzPosition0) (@hzAfter0) (@rho3) (@hrho3Proper)
        (@hrho3One) (@hd1) (@hd2Missing) (@hd2Edges) (@hdeltaZ) (@hd2z) (@hd3) (@uPosition)
        (@huPosition) (@hseedBeforeU) (@hterminalInTj) (@hterminalInTjVal) (@hterminalBeforeZ)
        (@hzChoiceForContradiction) (@hjPositive)
    · exact @helper_branch_15847 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@segmentTrans)
        (@vertexTransfer) (@trace) (@hterminalJ) (@p0) (@indices0) (@gamma0) (@delta0)
        (@hb2Missing) (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
        (@hseedTj) (@hseedTerminal) (@hTjQ) (@hseedVertexBefore) (@segmentVertexBefore)
        (@transportSeedRoute) (@commonPrefix) (@TjPrime) (@hclosure) (@hseedPrime)
        (@hterminalInclusion) (@hb2EdgesFromSeed) (@hdeltaMissing) (@a) (@b) (@x)
        (@componentPath) (@u) (@exitPath) (@haugmentation) (@zPosition) (@u0) (@huPrime0)
        (@huOutside0) (@exitPath0) (@beta0) (@z0) (@hz0) (@zPosition0) (@hzPosition0) (@hzAfter0)
        (@rho3) (@hrho3Proper) (@hrho3One) (@hd1) (@hd2Missing) (@hd2Edges) (@hdeltaZ) (@hd2z)
        (@hd3) (@hu0Terminal) (@uPosition) (@huPosition) (@hseedBeforeU) (@hterminalInTj)
        (@hterminalInTjVal) (@hzv) (@hterminalBeforeZ) (@hzChoiceForContradiction) (@hjPositive)
private theorem helper_hcaseTwoObservationPackage_7053.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    let supportColors : Finset (Fin k) :=
      Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0) (fN : E),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (componentPath : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (exitPath : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : exitPath.IsPath) (_ : (2 : ℕ) ≤ exitPath.length)
      (_ : ∀ y ∈ exitPath.support, y ∈ componentPath.support)
      (_ :
        ∀
          w ∈
            TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪
              TreeSequenceVertexSet TjPrime,
          Sum.inl w ∈ exitPath.support ↔ w = u)
      (_ :
        ∃
          g ∈
            BoundaryColorEdges G rho1
              (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪
                TreeSequenceVertexSet TjPrime)
              gamma,
          Incident G u g ∧ Sum.inr g ∈ exitPath.support)
      (_ : ¬Incident G u fN) (_ : u ∈ TreeSequenceVertexSet TjPrime)
      (_ : u ∉ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      (beta : Fin k) (_ : beta ∈ MissingColors G rho1 u)
      (_ : beta ∉ supportColors) (z : V)
      (hz : z ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
      (zPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition = z)
      (_ : seed.length ≤ (↑zPosition : ℕ))
      (_ :
        (seed.length < (↑zPosition : ℕ) ∧
            beta ∈ MissingColors G rho1 z ∧
              ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
                seed.length < (↑r : ℕ) →
                  (↑r : ℕ) < (↑zPosition : ℕ) →
                    beta ∉
                      MissingColors G rho1
                        ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) ∨
          zPosition = Fin.last (ett.series.data.tree jSlot.succ.castSucc).length ∧
            ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
              seed.length < (↑r : ℕ) →
                beta ∉
                  MissingColors G rho1
                    ((ett.series.data.tree jSlot.succ.castSucc).vertex r))
      (_ :
        ∀ w ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z hz,
          beta ∉ MissingColors G rho1 w)
      (_ :
        ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
          seed.length ≤ (↑a : ℕ) →
            (↑a : ℕ) < (↑zPosition : ℕ) →
              rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) ≠ some beta),
    (u ∈ TreeSequenceVertexSet TjPrime ∧
        u ∉ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) ∧
    (exitPath.IsPath ∧
        (2 : ℕ) ≤ exitPath.length ∧
          (∀ y ∈ exitPath.support, y ∈ componentPath.support) ∧
            (∀
                y ∈
                  TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪
                    TreeSequenceVertexSet TjPrime,
                Sum.inl y ∈ exitPath.support ↔ y = u) ∧
              (∃
                  g ∈
                    BoundaryColorEdges G rho1
                      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪
                        TreeSequenceVertexSet TjPrime)
                      gamma,
                  Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
                ¬Incident G u fN) ∧
    (beta ∈ MissingColors G rho1 u ∧ beta ∉ supportColors) ∧
    z ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∧
    (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition = z ∧
    seed.length ≤ (↑zPosition : ℕ) ∧
    ((seed.length < (↑zPosition : ℕ) ∧
          beta ∈ MissingColors G rho1 z ∧
            ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
              seed.length < (↑r : ℕ) →
                (↑r : ℕ) < (↑zPosition : ℕ) →
                  beta ∉
                    MissingColors G rho1
                      ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) ∨
        zPosition = Fin.last (ett.series.data.tree jSlot.succ.castSucc).length ∧
          ∀ (r : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
            seed.length < (↑r : ℕ) →
              beta ∉
                MissingColors G rho1
                  ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) ∧
    (∀ y ∈ TreeVerticesBefore (ett.series.data.tree jSlot.succ.castSucc) z hz,
        beta ∉ MissingColors G rho1 y) ∧
    ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
    seed.length ≤ (↑a : ℕ) →
    (↑a : ℕ) < (↑zPosition : ℕ) →
    rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) ≠ some beta := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 rho1 terminalPosition
      hterminalPositionPositive hterminalPositionBound seed supportColors TjPrime fN H x
      componentPath u exitPath hexitPath hexitLength hexitSupport hexitIntersection hexitBoundary
      huNotFN huPrime huOutside beta hbeta hbetaSupport z hz zPosition hzPosition hzAfter
      hzChoice hzBefore hzEdges
  exact @helper_hcaseTwoObservationPackage_6796 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@trace) (@p0) (@indices0) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@TjPrime) (@fN) (@x) (@componentPath) (@u) (@exitPath)
      (@hexitPath) (@hexitLength) (@hexitSupport) (@hexitIntersection) (@hexitBoundary)
      (@huNotFN) (@huPrime) (@huOutside) (@beta) (@hbeta) (@hbetaSupport) (@z) (@hz)
      (@zPosition) (@hzPosition) (@hzAfter) (@hzChoice) (@hzBefore) (@hzEdges)

private theorem helper_hpreterminalGammaPresent_7105.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds)
      (_ : v ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k)
      (_ : ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc)
      (_ :
        Function.Injective (Fin.cons (gamma0 (0 : Fin (p0 + (1 : ℕ)))) delta0)),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (_ :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let supportColors : Finset (Fin k) :=
      Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0)
      (_ :
        ∀ (a : Fin (p0 + (1 : ℕ))),
          ett.series.data.stored (indices0 a).succ =
            (insert (gamma0 a) ({delta0 a} : Finset (Fin k)) : Finset (Fin k)))
      (_ :
        ∀ x ∈ (TreeSequenceVertexSet TjPrime).erase v,
          (MissingColors G rho1 x ∩ supportColors : Finset (Fin k)) = ∅)
      (_ : gamma0 (Fin.last p0) = gamma),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (_ : V ⊕ E) (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : u ∈ (TreeSequenceVertexSet TjPrime).erase v)
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (u : V) (beta : Fin k),
    u ∈ TreeSequenceVertexSet TjPrime →
    u ∉ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) →
    beta ∈ MissingColors G rho1 u →
    ∀ (a : Fin p0),
    gamma0 a.castSucc ∈
      PresentColors G
        (TwoColorComponentSwap G (OutsideTreeColorSwap TjPrime rho1 beta delta) gamma beta
          (Sum.inl u))
        u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma this q hqTerminal
      hvStage hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 hchain0
      hinjective0 rho1 terminalPosition hterminalPositionPositive hterminalPositionBound
      supportColors TjPrime hstored0 hcaseTwoPointwise hgammaLast H a x componentPath u exitPath
      huErase zPosition
  exact @helper_hpreterminalGammaPresent_6848 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
      (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvStage) (@hvFinal) (@hfirstUpper)
      (@hfirstPositive) (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@hchain0)
      (@hinjective0) (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
      (@TjPrime) (@hstored0) (@hcaseTwoPointwise) (@hgammaLast) (@a) (@x) (@componentPath) (@u)
      (@exitPath) (@huErase) (@zPosition)

private theorem helper_hTjInitialEarlier_7122.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (gamma delta : Fin k)
      (sigma : PartialEdgeColoring E k),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal)
      (_ :
        ∀ (a b : ℕ),
          (1 : ℕ) ≤ a →
            ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds),
              TreeSequenceInitialSegment
                (ett.series.data.tree
                  (⟨a, by
                      omega⟩ :
                    Fin (ett.rounds + (2 : ℕ))))
                (ett.series.data.tree
                  (⟨b, by
                      omega⟩ :
                    Fin (ett.rounds + (2 : ℕ)))))
      (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ _ : Fin (p0 + (1 : ℕ)) → Fin k),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (_ :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length)
      (_ : indices0 (Fin.last p0) = q),
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
    ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V)
      (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u))
      (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))),
    ∀ s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q,
    TreeSequenceInitialSegment (ett.series.data.tree jSlot.succ.castSucc)
      (ett.series.data.tree s.succ.castSucc) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot hjSlot stageToStage trace p0 indices0 gamma0
      delta0 rho1 terminalPosition hterminalPositionPositive hterminalPositionBound hqLast H x
      componentPath u exitPath zPosition
  exact @helper_hTjInitialEarlier_6865 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
      (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot)
      (@stageToStage) (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hqLast) (@x) (@componentPath)
      (@u) (@exitPath) (@zPosition)

private theorem helper_hpositiveClaim45_7133.{u_1, u_2} :
    helperHpositiveClaim457133Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound hgammaLast gammaFirst H x
      componentPath u exitPath zPosition hp0
  exact @helper_hgammaFirstZero_6905 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
      (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
      (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@hgammaLast) (@x) (@componentPath) (@u) (@exitPath)
      (@zPosition) (@hp0)

private theorem helper_hclaim45Package_7169.{u_1, u_2} :
    helperHclaim45Package7169Conditions.{u_1, u_2} := by
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
  exact @helper_hclaim45Package_6912 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
      (@sigma) (@hqTerminal) (@hvStage) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace)
      (@hterminalJ) (@p0) (@indices0) (@gamma0) (@hrho1Proper) (@hrho1One) (@hb2Missing)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj)
      (@hseedTerminal) (@hTjQ) (@TjPrime) (@hclosure) (@hprimeElementary) (@hseedPrime)
      (@hb1Tj) (@hcaseTwoPointwise) (@hgammaSupport) (@hdeltaSupport) (@hgammaDelta)
      (@hb2EdgesFromSeed) (@hdeltaPhiJ) (@hterminalSeed) (@fN) (@hdeltaMissing) (@a) (@x)
      (@componentPath) (@hcomponentPath) (@hcomponentSupport) (@hxOutside) (@u) (@exitPath)
      (@hexitPath) (@hexitLength) (@hexitSupport) (@hexitIntersection) (@hexitBoundary)
      (@huNotFN) (@huPrime) (@huOutside) (@hdegree) (@beta) (@hbeta) (@hbetaSupport)
      (@haugmentation) (@z) (@hz) (@zPosition) (@hzPosition) (@hzAfter) (@hzChoice) (@hzBefore)
      (@hzEdges) (@hpositiveClaim45) (@hgammaFirstZero)

private theorem helper_continuation_8265.{u_1, u_2} :
    helperContinuation8265Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma this q
      hqTerminal hvStage hvFinal hfirstUpper hfirstPositive jSlot hjSlot segmentTrans
      vertexTransfer trace hterminalJ p0 indices0 gamma0 delta0 rho1 hrho1Proper hrho1One
      hb2Missing hb2TreeEdges terminalPosition hterminalPositionPositive hterminalPositionBound
      seed hjTreeIndex hseedTj hseedTerminal hTjQ hseedVertexBefore segmentVertexBefore
      transportSeedRoute commonPrefix supportColors TjPrime hclosure hprimeElementary hseedPrime
      hterminalPrime hqLast hb1Tj hcaseTwoPointwise gammaFirst hgammaSupport hdeltaSupport
      hgammaDelta hterminalInclusion hb2EdgesFromSeed hdeltaPhiJ hterminalSeed hseedN fN
      hdeltaMissing H C a b x componentPath hcomponentPath hcomponentSupport hxOutside u exitPath
      hexitPath hexitLength hexitSupport hexitIntersection hexitBoundary huNotFN huPrime
      huOutside hdegree beta hbeta hbetaSupport Tprevious hpreviousTj hpreviousStrict
      hpreviousSeed haugmentation z hz zPosition hzPosition hzAfter hzChoice hzBefore hzEdges
      hpositiveClaim45 hgammaFirstZero
  have hclaim45Package :
      ∃ (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet TjPrime)
        (huOutside0 : u0 ∉ TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc))
        (exitPath0 : (TwoColorIncidenceGraph G rho1 gamma delta).Walk
          (Sum.inl x) (Sum.inl u0)),
        exitPath0.IsPath ∧ 2 ≤ exitPath0.length ∧
        (∀ y : Sum V E, y ∈ exitPath0.support →
          y ∈ componentPath.support) ∧
        (∀ y : V,
          y ∈ TreeSequenceVertexSet
              (ett.series.data.tree q.succ.castSucc) ∪
                TreeSequenceVertexSet TjPrime →
          (Sum.inl y ∈ exitPath0.support ↔ y = u0)) ∧
        (∃ g ∈ BoundaryColorEdges G rho1
            (TreeSequenceVertexSet
                (ett.series.data.tree q.succ.castSucc) ∪
              TreeSequenceVertexSet TjPrime) gamma,
          Incident G u0 g ∧ Sum.inr g ∈ exitPath0.support) ∧
        ¬ Incident G u0 fN ∧
        ∃ beta0 : Fin k,
          beta0 ∈ MissingColors G rho1 u0 ∧
          beta0 ∉ supportColors ∧
          ∃ (z0 : V) (hz0 : z0 ∈ TreeSequenceVertexSet
              (ett.series.data.tree jSlot.succ.castSucc))
            (zPosition0 : Fin
              ((ett.series.data.tree jSlot.succ.castSucc).length + 1)),
            (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition0 =
                z0 ∧
            seed.length ≤ zPosition0.val ∧
            ((seed.length < zPosition0.val ∧
                beta0 ∈ MissingColors G rho1 z0 ∧
                ∀ r : Fin
                    ((ett.series.data.tree jSlot.succ.castSucc).length + 1),
                  seed.length < r.val → r.val < zPosition0.val →
                  beta0 ∉ MissingColors G rho1
                    ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) ∨
              (zPosition0 = Fin.last
                  (ett.series.data.tree jSlot.succ.castSucc).length ∧
                ∀ r : Fin
                    ((ett.series.data.tree jSlot.succ.castSucc).length + 1),
                  seed.length < r.val →
                  beta0 ∉ MissingColors G rho1
                    ((ett.series.data.tree jSlot.succ.castSucc).vertex r))) ∧
            (∀ y ∈ TreeVerticesBefore
                (ett.series.data.tree jSlot.succ.castSucc) z0 hz0,
              beta0 ∉ MissingColors G rho1 y) ∧
            (∀ a : Fin
                (ett.series.data.tree jSlot.succ.castSucc).length,
              seed.length ≤ a.val → a.val < zPosition0.val →
              rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) ≠
                some beta0) ∧
            ∃ rho3 : PartialEdgeColoring E k,
              IsProperEdgeColoring G rho3 ∧
              IsOneEdgeUncolored rho3 e0 ∧
              StableColoringBeforeVertex
                (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
                (TashkinovStoredColors ett.series.data jSlot.castSucc)
                (ett.series.data.coloring jSlot.castSucc) rho3 ∧
              (∀ y : V,
                y ∈ (((TreeVerticesBefore
                    (ett.series.data.tree jSlot.succ.castSucc) z0 hz0 ∪
                      {z0}) ∪
                    (TreeVerticesBefore TjPrime u0 huPrime0 ∪
                      {u0})).erase u0).erase z0 →
                MissingColors G rho3 y = MissingColors G rho1 y) ∧
              (∀ f : E,
                ((∃ a : Fin
                      (ett.series.data.tree jSlot.succ.castSucc).length,
                    seed.length ≤ a.val ∧ a.val < zPosition0.val ∧
                      (ett.series.data.tree
                        jSlot.succ.castSucc).edge a = f) ∨
                  (∃ (a : Fin TjPrime.length)
                    (uPosition : Fin (TjPrime.length + 1)),
                    TjPrime.vertex uPosition = u0 ∧
                      a.val < uPosition.val ∧ TjPrime.edge a = f)) →
                rho3 f = rho1 f) ∧
              (beta0 ∈ MissingColors G rho1 z0 →
                delta ∈ MissingColors G rho3 z0) ∧
              (z0 ∈ TreeVerticesBefore TjPrime u0 huPrime0 →
                MissingColors G rho3 z0 = MissingColors G rho1 z0) ∧
              gammaFirst ∈ MissingColors G rho3 u0 := by
    exact @helper_hclaim45Package_7169 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvStage) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace)
        (@hterminalJ) (@p0) (@indices0) (@gamma0) (@hrho1Proper) (@hrho1One) (@hb2Missing)
        (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj)
        (@hseedTerminal) (@hTjQ) (@TjPrime) (@hclosure) (@hprimeElementary) (@hseedPrime)
        (@hb1Tj) (@hcaseTwoPointwise) (@hgammaSupport) (@hdeltaSupport) (@hgammaDelta)
        (@hb2EdgesFromSeed) (@hdeltaPhiJ) (@hterminalSeed) (@fN) (@hdeltaMissing) (@a) (@x)
        (@componentPath) (@hcomponentPath) (@hcomponentSupport) (@hxOutside) (@u) (@exitPath)
        (@hexitPath) (@hexitLength) (@hexitSupport) (@hexitIntersection) (@hexitBoundary)
        (@huNotFN) (@huPrime) (@huOutside) (@hdegree) (@beta) (@hbeta) (@hbetaSupport)
        (@haugmentation) (@z) (@hz) (@zPosition) (@hzPosition) (@hzAfter) (@hzChoice) (@hzBefore)
        (@hzEdges) (@hpositiveClaim45) (@hgammaFirstZero)
  exact @helper_continuation_12157 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvStage) (@hvFinal)
      (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@segmentTrans) (@vertexTransfer) (@trace)
      (@hterminalJ) (@p0) (@indices0) (@gamma0) (@delta0) (@hb2Missing) (@hb2TreeEdges)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex)
      (@hseedTj) (@hseedTerminal) (@hTjQ) (@hseedVertexBefore) (@segmentVertexBefore)
      (@transportSeedRoute) (@commonPrefix) (@TjPrime) (@hclosure) (@hprimeElementary)
      (@hseedPrime) (@hterminalPrime) (@hqLast) (@hterminalInclusion) (@hb2EdgesFromSeed)
      (@hterminalSeed) (@hseedN) (@fN) (@hdeltaMissing) (@a) (@b) (@x) (@componentPath) (@u)
      (@exitPath) (@hpreviousTj) (@hpreviousStrict) (@hpreviousSeed) (@haugmentation)
      (@zPosition) (@hclaim45Package)

theorem helper_continuation_11325.{u_1, u_2} :
    helperContinuation11325Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma
      hsigmaProper hsigmaOne this q hqTerminal hqGamma hqDelta hvStage hvFinal hfirstUpper
      hfirstPositive jSlot hjSlot segmentTrans stageToStage vertexTransfer trace hterminalJ p0
      indices0 gamma0 delta0 hincreasing0 hclass0 hgamma0 hdelta0 hchain0 hinjective0 rho1
      hrho1Proper hrho1One hb2Missing hb2TreeEdges hb3EdgeEffects terminalPosition
      hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj hseedTerminal
      hTjQ hseedVertexBefore segmentVertexBefore transportSeedRoute commonPrefix supportColors
      TjPrime hclosure hprimeElementary hseedPrime hterminalPrime hqLast hsupport0 hkind0
      hstored0 hb1Tj hcaseTwoPointwise hsupportSet hterminalClass hgammaLast gammaFirst
      hgammaSupport hdeltaSupport hgammaFirstSupport hgammaDelta restorationColors
      hterminalColorsNotRestored hsupportColors hdeltaEarlier hpreterminalPackage hb4Earlier
      hsupportComponentOrder hterminalInclusion hb2EdgesFromSeed hdeltaPhiJ hterminalSeed hseedN
      fN hfNterminal hphiNProper hphiNOne hgammaBoundary hdeltaLocation hdeltaMissing
      hterminalIntersection' controlled hgammaControlled hdeltaControlled hsigmaControlled H C a
      b x componentPath hcomponentPath hcomponentSupport hxOutside htwoN u exitPath hexitPath
      hexitLength hexitSupport hexitIntersection hexitBoundary huNotFN huPrime huOutside hdegree
      beta hbeta huErase hbetaSupport Tprevious hpreviousTj hpreviousStrict hpreviousSeed
      haugmentation z hz zPosition hzPosition hzAfter hzChoice hzBefore hzEdges
  have hcaseTwoObservationPackage :
      (u ∈ TreeSequenceVertexSet TjPrime ∧
        u ∉ TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc)) ∧
      (exitPath.IsPath ∧ 2 ≤ exitPath.length ∧
        (∀ y : Sum V E, y ∈ exitPath.support →
          y ∈ componentPath.support) ∧
        (∀ y : V,
          y ∈ TreeSequenceVertexSet
              (ett.series.data.tree q.succ.castSucc) ∪
                TreeSequenceVertexSet TjPrime →
          (Sum.inl y ∈ exitPath.support ↔ y = u)) ∧
        (∃ g ∈ BoundaryColorEdges G rho1
            (TreeSequenceVertexSet
                (ett.series.data.tree q.succ.castSucc) ∪
              TreeSequenceVertexSet TjPrime) gamma,
          Incident G u g ∧ Sum.inr g ∈ exitPath.support) ∧
        ¬ Incident G u fN) ∧
      (beta ∈ MissingColors G rho1 u ∧ beta ∉ supportColors) ∧
      (z ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) ∧
        (ett.series.data.tree jSlot.succ.castSucc).vertex zPosition = z ∧
        seed.length ≤ zPosition.val ∧
        ((seed.length < zPosition.val ∧
            beta ∈ MissingColors G rho1 z ∧
            ∀ r : Fin
                ((ett.series.data.tree jSlot.succ.castSucc).length + 1),
              seed.length < r.val → r.val < zPosition.val →
              beta ∉ MissingColors G rho1
                ((ett.series.data.tree jSlot.succ.castSucc).vertex r)) ∨
          (zPosition = Fin.last
              (ett.series.data.tree jSlot.succ.castSucc).length ∧
            ∀ r : Fin
                ((ett.series.data.tree jSlot.succ.castSucc).length + 1),
              seed.length < r.val →
              beta ∉ MissingColors G rho1
                ((ett.series.data.tree jSlot.succ.castSucc).vertex r))) ∧
        (∀ y ∈ TreeVerticesBefore
            (ett.series.data.tree jSlot.succ.castSucc) z hz,
          beta ∉ MissingColors G rho1 y) ∧
        ∀ a : Fin (ett.series.data.tree jSlot.succ.castSucc).length,
          seed.length ≤ a.val → a.val < zPosition.val →
          rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) ≠
            some beta) := by
    exact @helper_hcaseTwoObservationPackage_7053 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
        (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
        (@trace) (@p0) (@indices0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@TjPrime) (@fN) (@x) (@componentPath) (@u) (@exitPath)
        (@hexitPath) (@hexitLength) (@hexitSupport) (@hexitIntersection) (@hexitBoundary)
        (@huNotFN) (@huPrime) (@huOutside) (@beta) (@hbeta) (@hbetaSupport) (@z) (@hz)
        (@zPosition) (@hzPosition) (@hzAfter) (@hzChoice) (@hzBefore) (@hzEdges)
  have hpreterminalGammaPresent : ∀ (u : V) (beta : Fin k),
      u ∈ TreeSequenceVertexSet TjPrime →
      u ∉ TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc) →
      beta ∈ MissingColors G rho1 u →
      ∀ a : Fin p0,
        gamma0 a.castSucc ∈ PresentColors G
          (TwoColorComponentSwap G
            (OutsideTreeColorSwap TjPrime rho1 beta delta)
            gamma beta (Sum.inl u)) u := by
    exact @helper_hpreterminalGammaPresent_7105 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
        (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvStage) (@hvFinal) (@hfirstUpper)
        (@hfirstPositive) (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@hchain0)
        (@hinjective0) (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
        (@TjPrime) (@hstored0) (@hcaseTwoPointwise) (@hgammaLast) (@a) (@x) (@componentPath) (@u)
        (@exitPath) (@huErase) (@zPosition)
  have hTjInitialEarlier : ∀ s : Fin ett.rounds,
      s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q →
      TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree s.succ.castSucc) := by
    exact @helper_hTjInitialEarlier_7122 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot)
        (@stageToStage) (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@hqLast) (@x) (@componentPath)
        (@u) (@exitPath) (@zPosition)
  have hpositiveClaim45 (hp0 : 0 < p0) :=
    let hpreterminal := hpreterminalPackage hp0
    let preterminalSlot := Classical.choose hpreterminal
    ExtensionBaseClaim45 ett q preterminalSlot jSlot hqTerminal
      (Classical.choose_spec hpreterminal).1 v hvFinal
      (ett.series.data.tree jSlot.succ.castSucc)
      (ett.series.data.tree q.succ.castSucc) seed TjPrime
      (ett.series.data.coloring jSlot.castSucc)
      (ett.series.data.coloring q.succ) sigma rho1
      (TashkinovStoredColors ett.series.data jSlot.castSucc)
      controlled restorationColors supportColors gammaFirst gamma delta
      fN x componentPath hphiNProper hphiNOne hsigmaProper hsigmaOne
      hrho1Proper hrho1One hTjQ hseedTj hseedPrime hseedTerminal
      hterminalJ hterminalSeed hclosure hprimeElementary
      hcaseTwoPointwise hterminalIntersection' hgammaSupport
      hdeltaSupport hgammaFirstSupport hgammaDelta hsigmaControlled
      hgammaControlled hdeltaControlled
      (fun f hf => hb3EdgeEffects f hf)
      hterminalColorsNotRestored.1 hterminalColorsNotRestored.2
      hgammaBoundary hdeltaLocation hdeltaMissing hcomponentPath
      (by simpa [C] using hcomponentSupport) hxOutside htwoN hfNterminal
      hb1Tj hb2Missing.1 hterminalInclusion haugmentation
      hb2EdgesFromSeed hdeltaPhiJ hsupportSet hterminalClass
      (Classical.choose_spec hpreterminal).2.1
      (Classical.choose_spec hpreterminal).2.2 hqGamma hqDelta hb4Earlier
      hsupportColors hdeltaEarlier hsupportComponentOrder p0 indices0
      gamma0 delta0 hincreasing0 hclass0 hqLast hsupport0 hkind0
      hgamma0 hdelta0 hstored0 hchain0 hinjective0 rfl
      hTjInitialEarlier rfl hpreterminalGammaPresent
  have hgammaFirstZero (hp0 : p0 = 0) : gammaFirst = gamma := by
    exact @helper_hpositiveClaim45_7133 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
        (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hgammaLast) (@x) (@componentPath) (@u) (@exitPath)
        (@zPosition) (@hp0)
  exact @helper_continuation_8265 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvStage) (@hvFinal)
      (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@segmentTrans) (@vertexTransfer) (@trace)
      (@hterminalJ) (@p0) (@indices0) (@gamma0) (@delta0) (@hrho1Proper) (@hrho1One)
      (@hb2Missing) (@hb2TreeEdges) (@terminalPosition) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@hseedTerminal) (@hTjQ)
      (@hseedVertexBefore) (@segmentVertexBefore) (@transportSeedRoute) (@commonPrefix)
      (@TjPrime) (@hclosure) (@hprimeElementary) (@hseedPrime) (@hterminalPrime) (@hqLast)
      (@hb1Tj) (@hcaseTwoPointwise) (@hgammaSupport) (@hdeltaSupport) (@hgammaDelta)
      (@hterminalInclusion) (@hb2EdgesFromSeed) (@hdeltaPhiJ) (@hterminalSeed) (@hseedN) (@fN)
      (@hdeltaMissing) (@a) (@b) (@x) (@componentPath) (@hcomponentPath) (@hcomponentSupport)
      (@hxOutside) (@u) (@exitPath) (@hexitPath) (@hexitLength) (@hexitSupport)
      (@hexitIntersection) (@hexitBoundary) (@huNotFN) (@huPrime) (@huOutside) (@hdegree) (@beta)
      (@hbeta) (@hbetaSupport) (@hpreviousTj) (@hpreviousStrict) (@hpreviousSeed)
      (@haugmentation) (@z) (@hz) (@zPosition) (@hzPosition) (@hzAfter) (@hzChoice) (@hzBefore)
      (@hzEdges) (@hpositiveClaim45) (@hgammaFirstZero)
private theorem helper_continuation_7187.{u_1, u_2} :
    helperContinuation7187Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma
      hsigmaProper hsigmaOne this q hqTerminal hqGamma hqDelta hvStage hvFinal hfirstUpper
      hfirstPositive jSlot hjSlot segmentTrans stageToStage vertexTransfer trace hterminalJ p0
      indices0 gamma0 delta0 hincreasing0 hclass0 hgamma0 hdelta0 hchain0 hinjective0 rho1
      hrho1Proper hrho1One hb2Missing hb2TreeEdges hb3EdgeEffects terminalPosition
      hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj hseedTerminal
      hTjQ hseedVertexBefore segmentVertexBefore transportSeedRoute commonPrefix supportColors
      TjPrime hclosure hprimeElementary hseedPrime hterminalPrime hqLast hsupport0 hkind0
      hstored0 hb1Tj hcaseTwoPointwise hsupportSet hterminalClass hgammaLast gammaFirst
      hgammaSupport hdeltaSupport hgammaFirstSupport hgammaDelta restorationColors
      hterminalColorsNotRestored hsupportColors hdeltaEarlier hpreterminalPackage hb4Earlier
      hsupportComponentOrder hterminalInclusion hb2EdgesFromSeed hdeltaPhiJ hterminalSeed hseedN
      fN hfNterminal hphiNProper hphiNOne hgammaBoundary hdeltaLocation hdeltaMissing
      hterminalIntersection' controlled hgammaControlled hdeltaControlled hsigmaControlled H C a
      b x componentPath hcomponentPath hcomponentSupport hxOutside htwoN u exitPath hexitPath
      hexitLength hexitSupport hexitIntersection hexitBoundary huNotFN huPrime huOutside hdegree
      beta hbeta huErase hbetaSupport hbetaGammaFirst hbetaTerminal huSeed Tprevious hpreviousTj
      hpreviousStrict
  have hpreviousSeed (hjPositive : 0 < jSlot.val) :
      TreeSequenceInitialSegment Tprevious seed :=
    commonPrefix (hpreviousTj hjPositive) hseedTj
      (Nat.le_of_lt (hpreviousStrict hjPositive))
  have haugmentation : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) seed
      (ett.series.data.tree jSlot.succ.castSucc) := by as_aux_lemma =>
    generalize htarget : jSlot.castSucc = target
    cases ett.series.certified target with
    | initial triple seedLength initialColoring initialStored initialEdges
        initialKind initialVertex initialOutside initialDelta initialGamma
        initialClosure =>
            exact @helper_branch_6740 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
                (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@terminalPosition)
                (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj) (@commonPrefix)
                (@seedLength) (@initialClosure) (@htarget)
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
            exact @helper_branch_6748 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
                (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
                (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
                (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@commonPrefix) (@x)
                (@componentPath) (@u) (@exitPath) (@hpreviousStrict) (@i) (@choice) (@adjoined)
                (@adjoinedExactly) (@closedExtension) (@htarget)
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        chosenGamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
            exact @helper_branch_6761 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
                (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
                (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
                (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@x) (@componentPath) (@u)
                (@exitPath) (@hpreviousSeed) (@i) (@closedExtension) (@htarget)
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
            exact @helper_branch_6775 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
                (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
                (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalPositionPositive)
                (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@commonPrefix) (@x)
                (@componentPath) (@u) (@exitPath) (@hpreviousStrict) (@i) (@available)
                (@adjoined) (@adjoinedExactly) (@closedExtension) (@htarget)
  obtain ⟨z, hz, zPosition, hzPosition, hzAfter,
      hzChoice, hzBefore, hzEdges⟩ :=
    ExtensionBaseCaseTwoObservation23
      (ett.series.data.tree jSlot.succ.castSucc) seed TjPrime
      (ett.series.data.coloring jSlot.castSucc) rho1 v u beta gammaFirst
      hseedTj hseedPrime hseedTerminal huPrime huSeed hprimeElementary
      hbeta hterminalSeed hb2Missing.1 hbetaTerminal hterminalInclusion
      hbetaGammaFirst haugmentation hb2EdgesFromSeed
  exact @helper_continuation_11325 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hsigmaProper) (@hsigmaOne) (@hqTerminal)
      (@hqGamma) (@hqDelta) (@hvStage) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot)
      (@segmentTrans) (@stageToStage) (@vertexTransfer) (@trace) (@hterminalJ) (@p0) (@indices0)
      (@gamma0) (@delta0) (@hincreasing0) (@hclass0) (@hgamma0) (@hdelta0) (@hchain0)
      (@hinjective0) (@hrho1Proper) (@hrho1One) (@hb2Missing) (@hb2TreeEdges) (@hb3EdgeEffects)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex)
      (@hseedTj) (@hseedTerminal) (@hTjQ) (@hseedVertexBefore) (@segmentVertexBefore)
      (@transportSeedRoute) (@commonPrefix) (@TjPrime) (@hclosure) (@hprimeElementary)
      (@hseedPrime) (@hterminalPrime) (@hqLast) (@hsupport0) (@hkind0) (@hstored0) (@hb1Tj)
      (@hcaseTwoPointwise) (@hsupportSet) (@hterminalClass) (@hgammaLast) (@hgammaSupport)
      (@hdeltaSupport) (@hgammaFirstSupport) (@hgammaDelta) (@hterminalColorsNotRestored)
      (@hsupportColors) (@hdeltaEarlier) (@hpreterminalPackage) (@hb4Earlier)
      (@hsupportComponentOrder) (@hterminalInclusion) (@hb2EdgesFromSeed) (@hdeltaPhiJ)
      (@hterminalSeed) (@hseedN) (@fN) (@hfNterminal) (@hphiNProper) (@hphiNOne)
      (@hgammaBoundary) (@hdeltaLocation) (@hdeltaMissing) (@hterminalIntersection')
      (@hgammaControlled) (@hdeltaControlled) (@hsigmaControlled) (@a) (@b) (@x) (@componentPath)
      (@hcomponentPath) (@hcomponentSupport) (@hxOutside) (@htwoN) (@u) (@exitPath) (@hexitPath)
      (@hexitLength) (@hexitSupport) (@hexitIntersection) (@hexitBoundary) (@huNotFN) (@huPrime)
      (@huOutside) (@hdegree) (@beta) (@hbeta) (@huErase) (@hbetaSupport) (@hpreviousTj)
      (@hpreviousStrict) (@hpreviousSeed) (@haugmentation) (@z) (@hz) (@zPosition) (@hzPosition)
      (@hzAfter) (@hzChoice) (@hzBefore) (@hzEdges)

theorem helper_continuation_10517.{u_1, u_2} :
    helperContinuation10517Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma
      hsigmaProper hsigmaOne w hw hwNe this q hqTerminal hqSucc hqKind hqVertex hqGamma hqDelta
      hvStage hvFinal hfirstUpper hfirstPositive jSlot hjSlot hsigmaTerminal segmentTrans
      stepSegment stageToStage vertexTransfer hdeltaExclusion trace hterminalJ hqActive p0
      indices0 gamma0 delta0 hincreasing0 hclass0 hgamma0 hdelta0 hchain0 hinjective0 rho1
      hrho1Proper hrho1One hb2Missing hb2TreeEdges hb3EdgeEffects terminalPosition hterminalAt
      hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj hseedTerminal
      hTjQ hseedVertexBefore segmentVertexBefore transportSeedRoute commonPrefix supportColors
      TjPrime hclosure hprimeElementary hseedPrime hterminalPrime hqLast hsupport0 hkind0
      hstored0 hb1Tj hcaseTwoPointwise hsupportSet hterminalClass hgammaLast gammaFirst
      hgammaSupport hdeltaSupport hgammaFirstSupport hgammaDelta restorationColors
      hterminalColorsNotRestored hsupportColors hdeltaEarlier hpreterminalPackage hb4Earlier
      hsupportComponentOrder hterminalInclusion hb2EdgesFromSeed hdeltaPhiJ hterminalSeed hseedN
      fN hfNterminal hphiNProper hphiNOne hgammaBoundary hdeltaLocation hdeltaMissing
      hterminalIntersection' controlled hgammaControlled hdeltaControlled hsigmaControlled
      hgammaBoundaryRho hdeltaBoundaryRho hterminalGraph hwComponentRho H C a b x componentPath
      hcomponentPath hcomponentSupport hcomponentNonempty hcomponentPositive hendpointC
      hendpointNeighbor
  have hxNe : x ≠ v := by
    exact @helper_hxNe_3545 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@v) (@gamma) (@delta) (@sigma) (@hvFinal)
        (@trace) (@x) (@componentPath) (@hcomponentPath) (@hcomponentSupport)
        (@hcomponentNonempty) (@hcomponentPositive) (@hendpointC) (@hendpointNeighbor)
  have swapBothPresent (phi : PartialEdgeColoring E k)
      (alpha beta : Fin k) (hne : alpha ≠ beta) (root : Sum V E)
      (y : V) (halpha : alpha ∈ PresentColors G phi y)
      (hbeta : beta ∈ PresentColors G phi y) :
      alpha ∈ PresentColors G
          (TwoColorComponentSwap G phi alpha beta root) y ∧
        beta ∈ PresentColors G
          (TwoColorComponentSwap G phi alpha beta root) y := by
    exact @helper_swapBothPresent_4143 (@V) (@E) inferInstance inferInstance (@G) (@k) (@phi)
        (@alpha) (@beta) (@hne) (@root) (@y) (@halpha) (@hbeta)
  have hTnElementary : ColoredVertexSetElementary G
      (ett.series.data.coloring q.castSucc)
      (TreeSequenceVertexSet
        (ett.series.data.tree q.succ.castSucc)) := by
    exact @helper_hTnElementary_6609 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
        (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper)
        (@hfirstPositive) (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition)
        (@hqLast) (@x) (@componentPath)
  have hgammaMissingPre : gamma ∈ MissingColors G
      (ett.series.data.coloring q.castSucc) v := by
    exact @helper_hgammaMissingPre_4237 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma)
        (@hqKind) (@hqVertex) (@hqGamma)
  have hdeltaNotMissingPre : delta ∉ TreeMissingColors
      (ett.series.data.coloring q.castSucc)
      (ett.series.data.tree q.succ.castSucc) :=
    (hdeltaExclusion.1 q q v v hvFinal hvFinal delta gamma hqActive
      hqActive le_rfl hqVertex hqVertex hqDelta hqGamma).1
  have hterminalPresentSigma : ∀ y : V,
      y ∈ TreeSequenceVertexSet
          (ett.series.data.tree q.succ.castSucc) →
      y ≠ v →
      gamma ∈ PresentColors G sigma y ∧
        delta ∈ PresentColors G sigma y := by
    exact @helper_hterminalPresentSigma_6628 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqKind) (@hqVertex) (@hqGamma) (@hqDelta) (@hvStage) (@hsigmaTerminal)
        (@hgammaDelta) (@swapBothPresent) (@hTnElementary) (@hgammaMissingPre)
        (@hdeltaNotMissingPre)
  have hxOutsideN : x ∉ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc) := by
    exact @helper_hxOutsideN_4382 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hvFinal) (@trace) (@hgammaDelta) (@hterminalGraph) (@x) (@componentPath)
        (@hendpointNeighbor) (@hxNe) (@hterminalPresentSigma)
  have hxOutsidePrime : x ∉ TreeSequenceVertexSet TjPrime := by
    exact @helper_hxOutsidePrime_6645 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@v) (@gamma) (@delta) (@sigma) (@hvFinal)
        (@trace) (@p0) (@indices0) (@TjPrime) (@hcaseTwoPointwise) (@hgammaSupport)
        (@hdeltaSupport) (@hgammaDelta) (@x) (@componentPath) (@hendpointNeighbor) (@hxNe)
  have hxOutside : x ∉
      TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) ∪
        TreeSequenceVertexSet TjPrime := by
    intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hxOutsideN hx
    · exact hxOutsidePrime hx
  have hwPath : Sum.inl w ∈ componentPath.support := by
    change Sum.inl w ∈ {z | z ∈ componentPath.support}
    rw [hcomponentSupport]
    exact hwComponentRho
  have hwStage : w ∈ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc) := by
    rw [hqSucc]
    exact hw
  have htwoN : ∃ y ∈ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc),
      y ≠ v ∧ Sum.inl y ∈ componentPath.support :=
    ⟨w, hwStage, hwNe, hwPath⟩
  obtain ⟨u, exitPath, huDiff, hexitPath, hexitLength,
      hexitSupport, hexitIntersection, hexitBoundary, huNotFN⟩ :=
    ExtensionBaseCaseTwoObservation21
      (ett.series.data.tree q.succ.castSucc) TjPrime rho1 gamma delta
      fN v x componentPath hcomponentPath (by simpa [C] using
        hcomponentSupport) hvStage hterminalPrime hxOutside htwoN
      hgammaBoundaryRho hdeltaBoundaryRho hfNterminal
  have huPrime : u ∈ TreeSequenceVertexSet TjPrime :=
    (Finset.mem_sdiff.mp huDiff).1
  have huOutside : u ∉ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc) :=
    (Finset.mem_sdiff.mp huDiff).2
  have hdegree : MaximumDegree G + 1 ≤ k := by
    have step := ett.series.certified 0
    cases step with
    | initial triple => exact triple.2.2.1
  obtain ⟨beta, hbeta⟩ :=
    MissingColorsNonemptyOfMaximumDegree G rho1 hdegree u
  have huTerminal : u ≠ v := by
    intro huv
    apply huOutside
    simpa [huv] using hvStage
  have huErase : u ∈ (TreeSequenceVertexSet TjPrime).erase v :=
    Finset.mem_erase.mpr ⟨huTerminal, huPrime⟩
  have hbetaSupport : beta ∉ supportColors := by
    exact @helper_hbetaSupport_3628 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@v) (@sigma) (@hvFinal) (@trace) (@p0)
        (@indices0) (@TjPrime) (@hcaseTwoPointwise) (@u) (@beta) (@hbeta) (@huErase)
  have hbetaGammaFirst : beta ≠ gammaFirst := by
    intro hEq
    exact hbetaSupport (hEq ▸ hgammaFirstSupport)
  have hbetaTerminal : beta ∉ MissingColors G rho1 v := by
    intro hbetaV
    have hdisjoint := hprimeElementary huPrime hterminalPrime huTerminal
    exact (Finset.disjoint_left.mp hdisjoint) hbeta hbetaV
  have huSeed : u ∉ TreeSequenceVertexSet seed := by
    intro hu
    exact huOutside (vertexTransfer hseedN hu)
  let Tprevious : TreeSequence G e0 :=
    ett.series.data.tree jSlot.castSucc.castSucc
  have hvNotPrevious (hjPositive : 0 < jSlot.val) :
      v ∉ TreeSequenceVertexSet Tprevious := by
    exact @helper_hvNotPrevious_6710 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@trace)
        (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hqLast) (@x) (@componentPath)
        (@u) (@exitPath) (@hjPositive)
  have hpreviousTj (hjPositive : 0 < jSlot.val) :
      TreeSequenceInitialSegment Tprevious
        (ett.series.data.tree jSlot.succ.castSucc) := by
    have hstep := stepSegment jSlot.castSucc (by simpa using hjPositive)
    rw [hjTreeIndex] at hstep
    exact hstep
  have hpreviousStrict (hjPositive : 0 < jSlot.val) :
      Tprevious.length < seed.length := by
    exact @helper_hpreviousStrict_6723 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
        (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hterminalAt)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@x) (@componentPath) (@u)
        (@exitPath) (@hvNotPrevious) (@hpreviousTj) (@hjPositive)
  exact @helper_continuation_7187 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hsigmaProper) (@hsigmaOne) (@hqTerminal)
      (@hqGamma) (@hqDelta) (@hvStage) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot)
      (@segmentTrans) (@stageToStage) (@vertexTransfer) (@trace) (@hterminalJ) (@p0) (@indices0)
      (@gamma0) (@delta0) (@hincreasing0) (@hclass0) (@hgamma0) (@hdelta0) (@hchain0)
      (@hinjective0) (@hrho1Proper) (@hrho1One) (@hb2Missing) (@hb2TreeEdges) (@hb3EdgeEffects)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex)
      (@hseedTj) (@hseedTerminal) (@hTjQ) (@hseedVertexBefore) (@segmentVertexBefore)
      (@transportSeedRoute) (@commonPrefix) (@TjPrime) (@hclosure) (@hprimeElementary)
      (@hseedPrime) (@hterminalPrime) (@hqLast) (@hsupport0) (@hkind0) (@hstored0) (@hb1Tj)
      (@hcaseTwoPointwise) (@hsupportSet) (@hterminalClass) (@hgammaLast) (@hgammaSupport)
      (@hdeltaSupport) (@hgammaFirstSupport) (@hgammaDelta) (@hterminalColorsNotRestored)
      (@hsupportColors) (@hdeltaEarlier) (@hpreterminalPackage) (@hb4Earlier)
      (@hsupportComponentOrder) (@hterminalInclusion) (@hb2EdgesFromSeed) (@hdeltaPhiJ)
      (@hterminalSeed) (@hseedN) (@fN) (@hfNterminal) (@hphiNProper) (@hphiNOne)
      (@hgammaBoundary) (@hdeltaLocation) (@hdeltaMissing) (@hterminalIntersection')
      (@hgammaControlled) (@hdeltaControlled) (@hsigmaControlled) (@a) (@b) (@x) (@componentPath)
      (@hcomponentPath) (@hcomponentSupport) (@hxOutside) (@htwoN) (@u) (@exitPath) (@hexitPath)
      (@hexitLength) (@hexitSupport) (@hexitIntersection) (@hexitBoundary) (@huNotFN) (@huPrime)
      (@huOutside) (@hdegree) (@beta) (@hbeta) (@huErase) (@hbetaSupport) (@hbetaGammaFirst)
      (@hbetaTerminal) (@huSeed) (@hpreviousTj) (@hpreviousStrict)
theorem helper_caseContinuation_10866.{u_1, u_2} :
    helperCaseContinuation10866Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma
      hsigmaProper hsigmaOne w hw hwComponent hwNe this q hqTerminal hqSucc hqKind hqVertex
      hqGamma hqDelta hvStage hvFinal hfirstUpper hfirstPositive jSlot hjSlot hsigmaTerminal
      segmentTrans stepSegment stageToStage vertexTransfer hdeltaExclusion hPEStored trace
      hterminalJ hqActive p0 indices0 gamma0 delta0 hincreasing0 hclass0 hgamma0 hdelta0 hchain0
      hinjective0 rho1 hrho1Proper hrho1One hb2Missing hb2TreeEdges hb3EdgeEffects
      terminalPosition hterminalAt hterminalPositionPositive hterminalPositionBound seed
      hjTreeIndex hseedTj hseedTerminal hTjQ hseedVertexBefore segmentVertexBefore
      transportSeedRoute commonPrefix supportColors TjPrime hclosure hprimeElementary hseedPrime
      hterminalPrime hqLast hsupport0 hkind0 hstored0 hterminalIntersection hb1Tj
      hcaseTwoPointwise hsupportSet hterminalClass hgammaLast hdeltaLast gammaFirst hgammaSupport
      hdeltaSupport hgammaFirstSupport hgammaDelta restorationColors hterminalColorsNotRestored
      hsupportColors hdeltaEarlier hpreterminalPackage hb4Earlier hsupportComponentOrder
      hterminalInclusion hb2EdgesFromSeed hdeltaPhiJ hterminalSeed hseedN fN hfNEdges hfNterminal
      hphiNProper hphiNOne
  have hboundaryStructure := HkuParallelBoundaryStructure G k ett.rounds
    e0 input ett.series q fN delta gamma v hqKind hfNEdges hqDelta
      hqGamma hqVertex
  have hgammaBoundary : BoundaryColorEdges G
      (ett.series.data.coloring q.succ)
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) gamma =
        {fN} := hboundaryStructure.1
  have hdeltaLocation : ∀ f ∈ BoundaryColorEdges G
      (ett.series.data.coloring q.succ)
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc)) delta,
      ∃ y ∈ TreeSequenceVertexSet seed, Incident G y f := by
    exact @helper_hdeltaLocation_6440 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0) (@gamma0)
        (@delta0) (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
        (@hseedTerminal) (@hseedN) (@fN) (@hboundaryStructure)
  have hdeltaMissing : delta ∈ MissingColors G rho1 v := by
    have hmember : delta ∈ MissingColors G rho1 v ∩ supportColors := by
      rw [hterminalIntersection, hdeltaLast]
      simp
    exact (Finset.mem_inter.mp hmember).1
  have hterminalIntersection' :
      MissingColors G rho1 v ∩ supportColors = {delta} := by
    simpa [hdeltaLast] using hterminalIntersection
  obtain ⟨hprimeMissingColors, hprimeAppendedEdges⟩ :=
    ExtensionBaseCaseTwoObservation19 rho1 seed TjPrime v supportColors
      delta hclosure hterminalPrime hcaseTwoPointwise
        hterminalIntersection'
  let controlled : Finset (Fin k) :=
    TreeMissingColors (ett.series.data.coloring q.succ)
        (ett.series.data.tree q.succ.castSucc) ∪
      TashkinovStoredColors ett.series.data q.succ
  have hterminalRawStored : ett.series.data.stored q.succ =
      {gamma, delta} :=
    hPEStored q gamma delta hqKind hqGamma hqDelta
  have hterminalColorControlled : ∀ c : Fin k,
      c ∈ ({gamma, delta} : Finset (Fin k)) → c ∈ controlled := by
    exact @helper_hterminalColorControlled_2850 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive)
        (@gamma) (@delta) (@hterminalRawStored)
  have hgammaControlled : gamma ∈ controlled :=
    hterminalColorControlled gamma (by simp)
  have hdeltaControlled : delta ∈ controlled :=
    hterminalColorControlled delta (by simp)
  have hsigmaControlled : StableColoring
      (ett.series.data.tree q.succ.castSucc) controlled
      (ett.series.data.coloring q.succ) sigma := by
    exact @helper_hsigmaControlled_2871 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@sigma)
        (@hsigmaTerminal)
  obtain ⟨hgammaBoundaryRho, hdeltaBoundaryRho⟩ :=
    ExtensionBaseCaseTwoObservation20
      (ett.series.data.tree q.succ.castSucc) seed TjPrime
      (ett.series.data.coloring q.succ) sigma rho1 controlled
      restorationColors gamma delta fN v hphiNProper hphiNOne hsigmaProper
      hsigmaOne hrho1Proper hrho1One hsigmaControlled hgammaControlled
      hdeltaControlled (fun f hf => (hb3EdgeEffects f hf).2)
      hterminalColorsNotRestored.1 hterminalColorsNotRestored.2
      hgammaBoundary hdeltaLocation hseedN hseedTerminal hclosure
      hterminalSeed hdeltaMissing
  have hterminalEdgeValues : ∀ f : E,
      (sigma f = some gamma ∨ sigma f = some delta) ↔
        (rho1 f = some gamma ∨ rho1 f = some delta) := by
    exact @helper_hterminalEdgeValues_3881 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
        (@gamma) (@delta) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
        (@trace) (@hb3EdgeEffects) (@hterminalColorsNotRestored)
  have hterminalGraph :
      TwoColorIncidenceGraph G sigma gamma delta =
        TwoColorIncidenceGraph G rho1 gamma delta := by
    apply SimpleGraph.ext
    funext a b
    cases a <;> cases b <;>
      simp [TwoColorIncidenceGraph, hterminalEdgeValues]
  have hwComponentRho : Sum.inl w ∈
      TwoColorComponent G rho1 gamma delta (Sum.inl v) := by
    unfold TwoColorComponent
    rw [← hterminalGraph]
    exact hwComponent
  let H := TwoColorIncidenceGraph G rho1 gamma delta
  let C := TwoColorComponent G rho1 gamma delta (Sum.inl v)
  have hfNBoundaryRho : fN ∈ BoundaryColorEdges G rho1
      (TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc))
      gamma := by
    rw [hgammaBoundaryRho]
    simp
  have hfNColorRho : rho1 fN = some gamma :=
    (Finset.mem_filter.mp hfNBoundaryRho).2
  have hfNAdj : H.Adj (Sum.inl v) (Sum.inr fN) := by
    simpa [H, TwoColorIncidenceGraph] using
      (show Incident G v fN ∧
          (rho1 fN = some gamma ∨ rho1 fN = some delta) from
        ⟨hfNterminal, Or.inl hfNColorRho⟩)
  have hvDegree : @SimpleGraph.degree _ H (Sum.inl v)
      (Fintype.ofFinite _) ≤ 1 := by
    exact @helper_hvDegree_3468 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@v) (@gamma) (@delta) (@sigma) (@hvFinal)
        (@trace) (@hrho1Proper) (@hgammaDelta) (@hdeltaMissing)
  have hvSub : Set.Subsingleton (H.neighborSet (Sum.inl v)) := by
    exact @helper_hvSub_3480 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@v) (@gamma) (@delta) (@sigma) (@hvFinal)
        (@trace) (@hvDegree)
  obtain ⟨a, b, spanningPath, hspanningPath, hspanningSupport⟩ :=
    TwoColorComponentSpanningPath G rho1 gamma delta hrho1Proper
      (Sum.inl v)
  have hvC : Sum.inl v ∈ C := by
    change Sum.inl v ∈ H.connectedComponentMk (Sum.inl v)
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have hvSpanning : Sum.inl v ∈ spanningPath.support := by
    change Sum.inl v ∈ {z | z ∈ spanningPath.support}
    rw [hspanningSupport]
    exact hvC
  have hvEndpoint : (Sum.inl v : Sum V E) = a ∨ Sum.inl v = b := by
    by_contra hn
    push Not at hn
    exact (hspanningPath.isTrail.notMem_support_of_subsingleton_neighborSet
      hn.1 hn.2 hvSub) hvSpanning
  obtain ⟨endpoint, componentPath, hcomponentPath, hcomponentSupport⟩ :
      ∃ endpoint,
        ∃ componentPath : H.Walk (Sum.inl v) endpoint,
          componentPath.IsPath ∧
            {z | z ∈ componentPath.support} = C := by
    rcases hvEndpoint with hva | hvb
    · subst a
      exact ⟨b, spanningPath, hspanningPath, hspanningSupport⟩
    · exact @helper_branch_3512 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@v) (@gamma) (@delta) (@sigma) (@hvFinal)
        (@trace) (@a) (@b) (@spanningPath) (@hspanningPath) (@hspanningSupport) (@hvSpanning)
        (@hvb)
  have hfNComponent : Sum.inr fN ∈ C := by
    exact @helper_hfNComponent_3517 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@v) (@gamma) (@delta) (@sigma)
        (@hvFinal) (@trace) (@fN) (@hfNAdj)
  have hcomponentNonempty : ¬ componentPath.Nil := by
    exact @helper_hcomponentNonempty_3523 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@v) (@gamma) (@delta) (@sigma)
        (@hvFinal) (@trace) (@fN) (@endpoint) (@componentPath) (@hcomponentPath)
        (@hcomponentSupport) (@hfNComponent)
  have hcomponentPositive : 0 < componentPath.length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hcomponentNonempty
  have hendpointC : endpoint ∈ C := by
    rw [← hcomponentSupport]
    change endpoint ∈ componentPath.support
    simpa only [componentPath.getVert_length] using
      componentPath.getVert_mem_support componentPath.length
  have hendpointNeighbor : ∀ z, H.Adj endpoint z →
      z = componentPath.getVert (componentPath.length - 1) := by
    exact @helper_hendpointNeighbor_6578 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
        (@indices0) (@gamma0) (@delta0) (@hrho1Proper) (@terminalPosition) (@hvSub) (@endpoint)
        (@componentPath) (@hcomponentPath) (@hcomponentSupport) (@hcomponentNonempty)
        (@hcomponentPositive) (@hendpointC)
  have hendpointVertex : ∃ x : V, endpoint = Sum.inl x := by
    exact @helper_hendpointVertex_6586 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0)
        (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@endpoint) (@componentPath)
        (@hcomponentPositive) (@hendpointNeighbor)
  obtain ⟨x, hendpoint⟩ := hendpointVertex
  subst endpoint
  exact @helper_continuation_10517 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hsigmaProper) (@hsigmaOne) (@w) (@hw) (@hwNe)
      (@hqTerminal) (@hqSucc) (@hqKind) (@hqVertex) (@hqGamma) (@hqDelta) (@hvStage) (@hvFinal)
      (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@hsigmaTerminal) (@segmentTrans) (@stepSegment)
      (@stageToStage) (@vertexTransfer) (@hdeltaExclusion) (@trace) (@hterminalJ) (@hqActive)
      (@p0) (@indices0) (@gamma0) (@delta0) (@hincreasing0) (@hclass0) (@hgamma0) (@hdelta0)
      (@hchain0) (@hinjective0) (@hrho1Proper) (@hrho1One) (@hb2Missing) (@hb2TreeEdges)
      (@hb3EdgeEffects) (@terminalPosition) (@hterminalAt) (@hterminalPositionPositive)
      (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@hseedTerminal) (@hTjQ)
      (@hseedVertexBefore) (@segmentVertexBefore) (@transportSeedRoute) (@commonPrefix)
      (@TjPrime) (@hclosure) (@hprimeElementary) (@hseedPrime) (@hterminalPrime) (@hqLast)
      (@hsupport0) (@hkind0) (@hstored0) (@hb1Tj) (@hcaseTwoPointwise) (@hsupportSet)
      (@hterminalClass) (@hgammaLast) (@hgammaSupport) (@hdeltaSupport) (@hgammaFirstSupport)
      (@hgammaDelta) (@hterminalColorsNotRestored) (@hsupportColors) (@hdeltaEarlier)
      (@hpreterminalPackage) (@hb4Earlier) (@hsupportComponentOrder) (@hterminalInclusion)
      (@hb2EdgesFromSeed) (@hdeltaPhiJ) (@hterminalSeed) (@hseedN) (@fN) (@hfNterminal)
      (@hphiNProper) (@hphiNOne) (@hgammaBoundary) (@hdeltaLocation) (@hdeltaMissing)
      (@hterminalIntersection') (@hgammaControlled) (@hdeltaControlled) (@hsigmaControlled)
      (@hgammaBoundaryRho) (@hdeltaBoundaryRho) (@hterminalGraph) (@hwComponentRho) (@a) (@b)
      (@x) (@componentPath) (@hcomponentPath) (@hcomponentSupport) (@hcomponentNonempty)
      (@hcomponentPositive) (@hendpointC) (@hendpointNeighbor)
private theorem helper_hmissingX_7828.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀
      (_ :
        ∀ {A B : TreeSequence G e0},
          TreeSequenceInitialSegment A B →
            TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B)
      (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀
      (_ :
        (∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
            MissingColors G rho1 x =
              MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
          MissingColors G rho1 v = MissingColors G sigma v)
      (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0) (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
      (b : Fin (p0 + (1 : ℕ)))
      (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
    ∀
      (_ :
        (∀
            x ∈
              TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∪
                TreeVerticesBefore TjPrime u huPrime,
            MissingColors G (traceB.coloring (Fin.last traceB.steps)) x =
              MissingColors G rho1 x) ∧
          ∀ (f : E),
            ((∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
                  (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
                ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + (1 : ℕ))),
                  TjPrime.vertex z = u ∧ (↑a : ℕ) < (↑z : ℕ) ∧ TjPrime.edge a = f) →
              traceB.coloring (Fin.last traceB.steps) f = rho1 f)
      (uPosition : Fin (TjPrime.length + (1 : ℕ)))
      (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed U)
      (_ :
        MissingColors G (ett.series.data.coloring jSlot.castSucc) v ⊆
          MissingColors G rho2 v ∪ MissingColors G rho2 u),
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (M : TreeSequence G e0) (_ : u ∈ TreeSequenceVertexSet U)
      (_ :
        ∀ (i : Fin Tj0.length),
          Tj0.vertex i.succ ∉ TreeSequenceVertexSet U →
            ∃ (j : Fin M.length),
              U.length ≤ (↑j : ℕ) ∧
                M.edge j = Tj0.edge i ∧ M.vertex j.succ = Tj0.vertex i.succ)
      (_ :
        ∀ (i j : Fin Tj0.length),
          Tj0.vertex i.succ ∉ TreeSequenceVertexSet U →
            Tj0.vertex j.succ ∉ TreeSequenceVertexSet U →
              (↑i : ℕ) < (↑j : ℕ) →
                ∀ (p q : Fin M.length),
                  M.vertex p.succ = Tj0.vertex i.succ →
                    M.vertex q.succ = Tj0.vertex j.succ → (↑p : ℕ) < (↑q : ℕ))
      (_ : TreeSequenceInitialSegment seed Tj0) (n : ℕ) (hnU : U.length ≤ n)
      (hnM : n + (1 : ℕ) ≤ M.length) (hnM' : n ≤ M.length),
    let X : TreeSequence G e0 := TreeSequencePrefix M n (Nat.le_trans U.positive hnU) hnM';
    let mIndex : Fin M.length :=
      (⟨n, by
          omega⟩ :
        Fin M.length);
    ∀ (i : Fin Tj0.length) (_ : M.vertex mIndex.succ = Tj0.vertex i.succ)
      (_ : Tj0.vertex i.succ ∉ TreeSequenceVertexSet U)
      (hiSeed : seed.length ≤ (↑i : ℕ)) (hiTj : (↑i : ℕ) < Tj0.length),
    let RX : TreeSequence G e0 :=
      TreeSequencePrefix Tj0 (↑i : ℕ) (Nat.le_trans seed.positive hiSeed)
        (Nat.le_of_lt hiTj);
    ∀ (_ : TreeSequenceInitialSegment RX Tj0) (_ : RX.length = (↑i : ℕ))
      (A : TreeSequence G e0) (_ : A.length = RX.length + (1 : ℕ)) (c : Fin k)
      (_ : c ∈ TreeMissingColors (ett.series.data.coloring jSlot.castSucc) RX)
      (_ : ∀ {x : V} (_ : x ∈ TreeSequenceVertexSet U), x ∈ TreeSequenceVertexSet X),
    c ∈ TreeMissingColors rho2 X := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot vertexTransfer trace p0 indices0 rho1 hb2Missing
      terminalPosition hterminalPositionPositive hterminalPositionBound seed TjPrime u huPrime b
      traceB rho2 c2 uPosition huPositionPositive huPositionBound U hseedU hterminalInclusion Tj0
      M huU heveryNewRightEntry hrightOrder hseedTjSegment n hnU hnM hnM' X mIndex i hvertexMTj
      hrightOutside hiSeed hiTj RX hRXTj hRXlen A hlenA c hmissingRX hleftX
  unfold TreeMissingColors at hmissingRX ⊢
  obtain ⟨x, hxRX, hcx⟩ :=
    Finset.mem_biUnion.mp hmissingRX
  simp only [TreeSequenceVertexSet, Finset.mem_image,
    Finset.mem_univ, true_and] at hxRX
  obtain ⟨a, ha⟩ := hxRX
  have hxTj : x ∈ TreeSequenceVertexSet Tj0 :=
    vertexTransfer hRXTj
      (by
        simp only [TreeSequenceVertexSet, Finset.mem_image,
          Finset.mem_univ, true_and]
        exact ⟨a, ha⟩)
  have hxX : x ∈ TreeSequenceVertexSet X := by
    by_cases hxU : x ∈ TreeSequenceVertexSet U
    · exact hleftX hxU
    · have haPos : 1 ≤ a.val := by
        by_contra hzero
        have haZero : a.val = 0 := by omega
        let p0 : Fin (seed.length + 1) := ⟨0, by omega⟩
        have hTjp0 := hseedTjSegment.2.1 p0
        have hUp0 := hseedU.2.1 p0
        apply hxU
        simp only [TreeSequenceVertexSet, Finset.mem_image,
          Finset.mem_univ, true_and]
        refine ⟨Fin.castLE (Nat.succ_le_succ hseedU.1) p0, ?_⟩
        have haTj : Tj0.vertex
              (Fin.castLE
                (Nat.succ_le_succ (Nat.le_of_lt hiTj)) a) =
            x := by
          simpa [RX, TreeSequencePrefix] using ha
        have ha0 : Fin.castLE
              (Nat.succ_le_succ (Nat.le_of_lt hiTj)) a =
            Fin.castLE
              (Nat.succ_le_succ hseedTjSegment.1) p0 := by
          apply Fin.ext
          exact haZero
        rw [ha0, hTjp0] at haTj
        exact hUp0.trans haTj
      let r : Fin Tj0.length := ⟨a.val - 1, by
        have haLt : a.val < RX.length + 1 := a.isLt
        simp [RX] at haLt
        omega⟩
      have hrSucc : r.succ = Fin.castLE
          (Nat.succ_le_succ (Nat.le_of_lt hiTj)) a := by
        apply Fin.ext
        exact Nat.sub_add_cancel haPos
      have hrv : Tj0.vertex r.succ = x := by
        rw [hrSucc]
        simpa [RX, TreeSequencePrefix] using ha
      have hrOutside :
          Tj0.vertex r.succ ∉ TreeSequenceVertexSet U := by
        simpa [hrv] using hxU
      have hri : r.val < i.val := by
        have haLt : a.val < RX.length + 1 := a.isLt
        simp [RX, r] at haLt ⊢
        omega
      obtain ⟨qM, hqU, hedgeq, hvertexq⟩ :=
        heveryNewRightEntry r hrOutside
      have hqn : qM.val < n :=
        hrightOrder r i hrOutside hrightOutside hri qM mIndex
          hvertexq hvertexMTj
      simp only [TreeSequenceVertexSet, Finset.mem_image,
        Finset.mem_univ, true_and]
      let qX : Fin (X.length + 1) := ⟨qM.val + 1, by
        change qM.val + 1 < n + 1
        omega⟩
      refine ⟨qX, ?_⟩
      rw [← hrv, ← hvertexq]
      change M.vertex _ = M.vertex qM.succ
      congr 1
  by_cases hxTerminal : x = v
  · have hcTerminalOld : c ∈ MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v := by
      rw [← hxTerminal]
      exact hcx
    rcases Finset.mem_union.mp
        (hterminalInclusion hcTerminalOld) with
      hcTerminal | hcU
    · exact Finset.mem_biUnion.mpr ⟨x, hxX, by
        simpa [hxTerminal] using hcTerminal⟩
    · exact Finset.mem_biUnion.mpr ⟨u, hleftX huU, hcU⟩
  · refine Finset.mem_biUnion.mpr ⟨x, hxX, ?_⟩
    have hxTj' : x ∈ TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc) := by
      simpa [Tj0] using hxTj
    rw [c2.1 x (Finset.mem_union_left _ hxTj'),
      hb2Missing.1 x
        (Finset.mem_erase.mpr ⟨hxTerminal, hxTj'⟩)]
    exact hcx

private theorem helper_hrightOutside_8201.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (_ :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length)
      (TjPrime : TreeSequence G e0) (uPosition : Fin (TjPrime.length + (1 : ℕ)))
      (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (M : TreeSequence G e0) (_ : TreeSequenceInitialSegment U M) (n : ℕ)
      (_ : U.length ≤ n) (hnM : n + (1 : ℕ) ≤ M.length),
    let mIndex : Fin M.length :=
      (⟨n, by
          omega⟩ :
        Fin M.length);
    ∀ (i : Fin Tj0.length) (_ : M.vertex mIndex.succ = Tj0.vertex i.succ),
    Tj0.vertex i.succ ∉ TreeSequenceVertexSet U := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound TjPrime uPosition huPositionPositive huPositionBound U Tj0 M
      hleftSegment n hnU hnM mIndex i hvertexMTj
  exact @helper_hrightOutside_6001 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
      (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime) (@uPosition)
      (@huPositionPositive) (@huPositionBound) (@M) (@hleftSegment) (@n) (@hnU) (@hnM) (@i)
      (@hvertexMTj)

private theorem helper_hiSeed_8209.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (p0 : ℕ) (_ : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0) (uPosition : Fin (TjPrime.length + (1 : ℕ)))
      (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
    ∀ (_ : TreeSequenceInitialSegment seed U),
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (_ : TreeSequence G e0) (_ : TreeSequenceInitialSegment seed Tj0) (_ : ℕ)
      (i : Fin Tj0.length) (_ : Tj0.vertex i.succ ∉ TreeSequenceVertexSet U),
    seed.length ≤ (↑i : ℕ) := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot p0 indices0 terminalPosition hterminalPositionPositive
      hterminalPositionBound seed TjPrime uPosition huPositionPositive huPositionBound U hseedU
      Tj0 M hseedTjSegment n i hrightOutside
  exact @helper_hiSeed_6009 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
      (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0) (@terminalPosition)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime) (@uPosition)
      (@huPositionPositive) (@huPositionBound) (@hseedU) (@M) (@hseedTjSegment) (@n) (@i)
      (@hrightOutside)

private theorem helper_hseedRX_8219.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (_ : TreeSequenceInitialSegment seed Tj0) (i : Fin Tj0.length)
      (hiSeed : seed.length ≤ (↑i : ℕ)) (hiTj : (↑i : ℕ) < Tj0.length),
    let RX : TreeSequence G e0 :=
      TreeSequencePrefix Tj0 (↑i : ℕ) (Nat.le_trans seed.positive hiSeed)
        (Nat.le_of_lt hiTj);
    TreeSequenceInitialSegment seed RX := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      Tj0 hseedTjSegment i hiSeed hiTj RX
  refine ⟨hiSeed, ?_, ?_⟩
  · intro a
    change Tj0.vertex _ = seed.vertex a
    calc
      Tj0.vertex _ = Tj0.vertex
          (Fin.castLE (Nat.succ_le_succ hseedTjSegment.1)
            a) := by congr 1
      _ = seed.vertex a := hseedTjSegment.2.1 a
  · intro a
    change Tj0.edge _ = seed.edge a
    calc
      Tj0.edge _ = Tj0.edge
          (Fin.castLE hseedTjSegment.1 a) := by congr 1
      _ = seed.edge a := hseedTjSegment.2.2 a

private theorem helper_hcolorTj_8249.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V),
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    ∀ (TjPrime : TreeSequence G e0) (uPosition : Fin (TjPrime.length + (1 : ℕ)))
      (_ : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (_ : (↑uPosition : ℕ) ≤ TjPrime.length),
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (_ : TreeSequence G e0) (_ : ℕ) (i : Fin Tj0.length) (hiSeed : seed.length ≤ (↑i : ℕ))
      (hiTj : (↑i : ℕ) < Tj0.length),
    let RX : TreeSequence G e0 :=
      TreeSequencePrefix Tj0 (↑i : ℕ) (Nat.le_trans seed.positive hiSeed)
        (Nat.le_of_lt hiTj);
    ∀ (hRXlen : RX.length = (↑i : ℕ)) (A : TreeSequence G e0)
      (hlenA : A.length = RX.length + (1 : ℕ)) (c : Fin k)
      (_ :
        ett.series.data.coloring jSlot.castSucc
            (A.edge
              (Fin.cast
                (by
                  omega)
                (Fin.last RX.length))) =
          some c)
      (_ : TreeSequenceInitialSegment A Tj0),
    let _ : Fin A.length :=
      (⟨(↑i : ℕ), by
          omega⟩ :
        Fin A.length);
    ett.series.data.coloring jSlot.castSucc (Tj0.edge i) = some c := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v q hqTerminal hvFinal hfirstUpper
      hfirstPositive jSlot terminalPosition hterminalPositionPositive hterminalPositionBound seed
      TjPrime uPosition huPositionPositive huPositionBound Tj0 M n i hiSeed hiTj RX hRXlen A
      hlenA c hcolorA hATjSegment ai
  have haiLast : ai =
      Fin.cast hlenA.symm (Fin.last RX.length) := by
    apply Fin.ext
    simp [ai, hRXlen]
  have hTjai : Tj0.edge
        (Fin.castLE hATjSegment.1 ai) = A.edge ai :=
    hATjSegment.2.2 ai
  have hcast : Fin.castLE hATjSegment.1 ai = i := by
    apply Fin.ext
    simp [ai]
  rw [← hcast, hTjai, haiLast]
  exact hcolorA

private theorem helper_hXY_8271.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma) (p0 : ℕ)
      (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (_ :
        (∀ v_1 ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.castSucc.succ)).erase v,
            MissingColors G (trace.coloring (Fin.last trace.steps)) v_1 =
              MissingColors G (ett.series.data.coloring jSlot.castSucc) v_1) ∧
          MissingColors G (trace.coloring (Fin.last trace.steps)) v =
            MissingColors G sigma v),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀
      (_ :
        ∀ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
          rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
              sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
            sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
              ett.series.data.coloring jSlot.castSucc
                ((ett.series.data.tree jSlot.succ.castSucc).edge a))
      (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (_ :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length)
      (TjPrime : TreeSequence G e0) (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
      (b : Fin (p0 + (1 : ℕ)))
      (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
    ∀
      (_ :
        (∀
            x ∈
              TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∪
                TreeVerticesBefore TjPrime u huPrime,
            MissingColors G (traceB.coloring (Fin.last traceB.steps)) x =
              MissingColors G rho1 x) ∧
          ∀ (f : E),
            ((∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
                  (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
                ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + (1 : ℕ))),
                  TjPrime.vertex z = u ∧ (↑a : ℕ) < (↑z : ℕ) ∧ TjPrime.edge a = f) →
              traceB.coloring (Fin.last traceB.steps) f = rho1 f)
      (uPosition : Fin (TjPrime.length + (1 : ℕ)))
      (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
      (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
    let Tj0 : TreeSequence G e0 := ett.series.data.tree jSlot.succ.castSucc;
    ∀ (M : TreeSequence G e0)
      (_ :
        ∀ (A : TreeSequence G e0) (r : ℕ) (hr : (1 : ℕ) ≤ r) (hrA : r + (1 : ℕ) ≤ A.length),
          TreeSequenceInitialSegment
            (TreeSequencePrefix A r hr
              (by
                omega))
            (TreeSequencePrefix A (r + (1 : ℕ))
              (by
                omega)
              hrA))
      (n : ℕ) (hnU : U.length ≤ n) (hnM hnSuccM : n + (1 : ℕ) ≤ M.length)
      (hnM' : n ≤ M.length),
    let X : TreeSequence G e0 := TreeSequencePrefix M n (Nat.le_trans U.positive hnU) hnM';
    let Y : TreeSequence G e0 :=
      TreeSequencePrefix M (n + (1 : ℕ))
        (Nat.le_trans U.positive (Nat.le_trans hnU (Nat.le_succ n))) hnSuccM;
    let mIndex : Fin M.length :=
      (⟨n, by
          omega⟩ :
        Fin M.length);
    ∀ (i : Fin Tj0.length) (_ : M.edge mIndex = Tj0.edge i) (c : Fin k)
      (_ : ett.series.data.coloring jSlot.castSucc (Tj0.edge i) = some c)
      (_ : c ∈ TreeMissingColors rho2 X),
    TashkinovAugmentation rho2 X Y := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace p0 indices0 hb2 rho1 hb2TreeEdges terminalPosition
      hterminalPositionPositive hterminalPositionBound TjPrime u huPrime b traceB rho2 c2
      uPosition huPositionPositive huPositionBound U Tj0 M prefixPrefix n hnU hnM hnSuccM hnM' X
      Y mIndex i hedgeMTj c hcolorTj hmissingX
  exact @helper_hXY_6159 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal) (@hvFinal)
      (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0) (@hb2) (@hb2TreeEdges)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime)
      (@u) (@huPrime) (@b) (@traceB) (@c2) (@uPosition) (@huPositionPositive)
      (@huPositionBound) (@M) (@prefixPrefix) (@n) (@hnU) (@hnM) (@hnSuccM) (@hnM') (@i)
      (@hedgeMTj) (@c) (@hcolorTj) (@hmissingX)

theorem helper_branch_15456.{u_1, u_2} :
    helperBranch15456Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot vertexTransfer trace p0 indices0 hb2 rho1 hb2Missing
      hb2TreeEdges terminalPosition hterminalPositionPositive hterminalPositionBound seed TjPrime
      u huPrime b traceB rho2 c2 uPosition huPositionPositive huPositionBound U hseedU
      hterminalInclusion Tj0 hroutePhiTj0 M huU hleftSegment hnewEntryFromRight
      heveryNewRightEntry hrightOrder prefixSegment prefixPrefix hseedTjSegment firstStep n hnU
      ih hnM
  by_cases hnEq : n = M.length
  · omega
  have hnSuccM : n + 1 ≤ M.length := by omega
  have hnM' : n ≤ M.length :=
    Nat.le_trans (Nat.le_succ n) hnSuccM
  have ih' := ih hnM'
  let X := TreeSequencePrefix M n
    (Nat.le_trans U.positive hnU) hnM'
  let Y := TreeSequencePrefix M (n + 1)
    (Nat.le_trans U.positive
      (Nat.le_trans hnU (Nat.le_succ n))) hnSuccM
  let mIndex : Fin M.length := ⟨n, by omega⟩
  obtain ⟨i, hedgeMTj, hvertexMTj⟩ :=
    hnewEntryFromRight mIndex hnU
  have hrightOutside :
      Tj0.vertex i.succ ∉ TreeSequenceVertexSet U := by
    exact @helper_hrightOutside_8201 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime) (@uPosition)
        (@huPositionPositive) (@huPositionBound) (@M) (@hleftSegment) (@n) (@hnU) (@hnM) (@i)
        (@hvertexMTj)
  have hiSeed : seed.length ≤ i.val := by
    exact @helper_hiSeed_8209 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime) (@uPosition)
        (@huPositionPositive) (@huPositionBound) (@hseedU) (@M) (@hseedTjSegment) (@n) (@i)
        (@hrightOutside)
  have hiTj : i.val < Tj0.length := i.isLt
  let RX := TreeSequencePrefix Tj0 i.val
    (Nat.le_trans seed.positive hiSeed) (Nat.le_of_lt hiTj)
  have hseedRX : TreeSequenceInitialSegment seed RX := by
    exact @helper_hseedRX_8219 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTjSegment) (@i) (@hiSeed) (@hiTj)
  have hRXTj : TreeSequenceInitialSegment RX Tj0 :=
    prefixSegment Tj0 i.val
      (Nat.le_trans seed.positive hiSeed) (Nat.le_of_lt hiTj)
  have hsuffix : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) RX Tj0 :=
    TashkinovAugmentationSequenceSuffix _ seed RX Tj0
      hroutePhiTj0 hseedRX hRXTj
  have hRXlen : RX.length = i.val := rfl
  obtain ⟨A, hRXA, hATj⟩ := firstStep hsuffix (by omega)
  rcases hRXA with
    ⟨hlenA, hRXASegment, c, hcolorA, hmissingRX⟩
  have hATjSegment : TreeSequenceInitialSegment A Tj0 :=
    TashkinovAugmentationSequenceInitialSegment _ _ _ hATj
  have hAi : A.length = i.val + 1 := by omega
  let ai : Fin A.length := ⟨i.val, by omega⟩
  have hcolorTj :
      ett.series.data.coloring jSlot.castSucc (Tj0.edge i) =
        some c := by
    exact @helper_hcolorTj_8249 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@TjPrime) (@uPosition) (@huPositionPositive)
        (@huPositionBound) (@M) (@n) (@i) (@hiSeed) (@hiTj) (@hRXlen) (@A) (@hlenA) (@c)
        (@hcolorA) (@hATjSegment)
  have hleftX {x : V} (hxU : x ∈ TreeSequenceVertexSet U) :
      x ∈ TreeSequenceVertexSet X := by
    exact @helper_hleftX_3005 (@V) (@E) (@G) (@e0) (@TjPrime) (@uPosition)
        (@huPositionPositive) (@huPositionBound) (@M) (@hleftSegment) (@n) (@hnU)
        (@hnM') (@x) (@hxU)
  have hmissingX : c ∈ TreeMissingColors rho2 X := by
    exact @helper_hmissingX_7828 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@vertexTransfer) (@trace) (@p0) (@indices0)
        (@hb2Missing) (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
        (@TjPrime) (@u) (@huPrime) (@b) (@traceB) (@c2) (@uPosition) (@huPositionPositive)
        (@huPositionBound) (@hseedU) (@hterminalInclusion) (@M) (@huU) (@heveryNewRightEntry)
        (@hrightOrder) (@hseedTjSegment) (@n) (@hnU) (@hnM) (@hnM') (@i) (@hvertexMTj)
        (@hrightOutside) (@hiSeed) (@hiTj) (@hRXTj) (@hRXlen) (@A) (@hlenA) (@c) (@hmissingRX)
        (@hleftX)
  have hXY : TashkinovAugmentation rho2 X Y := by
    exact @helper_hXY_8271 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0) (@hb2) (@hb2TreeEdges)
        (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime)
        (@u) (@huPrime) (@b) (@traceB) (@c2) (@uPosition) (@huPositionPositive)
        (@huPositionBound) (@M) (@prefixPrefix) (@n) (@hnU) (@hnM) (@hnSuccM) (@hnM') (@i)
        (@hedgeMTj) (@c) (@hcolorTj) (@hmissingX)
  change TashkinovAugmentationSequence rho2 U Y
  exact Relation.ReflTransGen.tail ih' hXY

private theorem helper_continuation_7819.{u_1, u_2} :
    helperContinuation7819Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma
      hsigmaProper hsigmaOne w hw hwComponent hwNe this q hqTerminal hqSucc hqKind hqVertex
      hqGamma hqDelta hvStage hvFinal hfirstUpper hfirstPositive jSlot hjSlot hsigmaTerminal
      segmentTrans stepSegment stageToStage vertexTransfer hdeltaExclusion hPEStored trace
      hterminalJ hqActive p0 indices0 gamma0 delta0 hincreasing0 hclass0 hgamma0 hdelta0 hchain0
      hinjective0 rho1 hrho1Proper hrho1One hb2Missing hb2TreeEdges hb3EdgeEffects
      terminalPosition hterminalAt hterminalPositionPositive hterminalPositionBound seed
      hjTreeIndex hseedTj hseedTerminal hTjQ hseedVertexBefore segmentVertexBefore
      transportSeedRoute commonPrefix supportColors TjPrime hclosure hprimeElementary hseedPrime
      hterminalPrime hqLast hsupport0 hkind0 hstored0 hterminalIntersection hb1Tj
      hcaseTwoPointwise hsupportSet hterminalClass hgammaLast hdeltaLast gammaFirst hgammaSupport
      hdeltaSupport hgammaFirstSupport hgammaDelta restorationColors hterminalColorsNotRestored
      hsupportColors hdeltaEarlier hpreterminalPackage hb4Earlier hsupportComponentOrder
      hterminalInclusion hb2EdgesFromSeed hdeltaPhiJ hterminalSeed
  have hseedN : TreeSequenceInitialSegment seed
      (ett.series.data.tree q.succ.castSucc) :=
    segmentTrans hseedTj hTjQ
  obtain ⟨fN, hfNEdges, hfNterminal, hphiNProper, hphiNOne⟩ :
      ∃ fN : E,
        ett.series.data.connectingEdges q.succ = {fN} ∧
          Incident G v fN ∧
          IsProperEdgeColoring G (ett.series.data.coloring q.succ) ∧
          IsOneEdgeUncolored (ett.series.data.coloring q.succ) e0 := by
    generalize htarget : q.succ = target
    cases ett.series.certified target with
    | initial => exact (Fin.succ_ne_zero q htarget).elim
    | SE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternative
        currentColoring currentStored currentEdges currentKind currentVertex
        currentOutside currentDelta currentGamma adjoined adjoinedExactly
        closedExtension orderedExtension strictExtension =>
            exact @helper_branch_3361 (@V) (@E) inferInstance inferInstance inferInstance
                (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
                (@hqKind) (@i) (@currentKind) (@htarget)
    | RE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed available currentColoring currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma adjoined adjoinedExactly closedExtension orderedExtension
        strictExtension =>
            exact @helper_branch_3370 (@V) (@E) inferInstance inferInstance inferInstance
                (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
                (@hqKind) (@i) (@currentKind) (@htarget)
    | PE i previousProper previousOneUncolored previousClosed
        previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
        actualGamma gammaRule secondStable secondStableProper
        secondStableOneUncolored secondStableRelation exitWitness
        currentColoring currentProper currentOneUncolored currentStored
        currentEdges currentKind currentVertex currentOutside currentDelta
        currentGamma closedExtension orderedExtension strictExtension =>
            exact @helper_branch_6417 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqVertex) (@i)
                (@previousProper) (@previousOneUncolored) (@previousClosed)
                (@previousNotStronglyClosed) (@noRevisiting) (@choice) (@seriesAlternativeFails)
                (@actualGamma) (@gammaRule) (@secondStable) (@secondStableRelation)
                (@exitWitness) (@currentColoring) (@currentProper) (@currentOneUncolored)
                (@currentStored) (@currentEdges) (@currentKind) (@currentVertex)
                (@currentOutside) (@currentDelta) (@currentGamma) (@closedExtension)
                (@orderedExtension) (@strictExtension) (@htarget)
  exact @helper_caseContinuation_10866 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hsigmaProper) (@hsigmaOne) (@w) (@hw)
      (@hwComponent) (@hwNe) (@hqTerminal) (@hqSucc) (@hqKind) (@hqVertex) (@hqGamma) (@hqDelta)
      (@hvStage) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@hsigmaTerminal)
      (@segmentTrans) (@stepSegment) (@stageToStage) (@vertexTransfer) (@hdeltaExclusion)
      (@hPEStored) (@trace) (@hterminalJ) (@hqActive) (@p0) (@indices0) (@gamma0) (@delta0)
      (@hincreasing0) (@hclass0) (@hgamma0) (@hdelta0) (@hchain0) (@hinjective0) (@hrho1Proper)
      (@hrho1One) (@hb2Missing) (@hb2TreeEdges) (@hb3EdgeEffects) (@terminalPosition)
      (@hterminalAt) (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex)
      (@hseedTj) (@hseedTerminal) (@hTjQ) (@hseedVertexBefore) (@segmentVertexBefore)
      (@transportSeedRoute) (@commonPrefix) (@TjPrime) (@hclosure) (@hprimeElementary)
      (@hseedPrime) (@hterminalPrime) (@hqLast) (@hsupport0) (@hkind0) (@hstored0)
      (@hterminalIntersection) (@hb1Tj) (@hcaseTwoPointwise) (@hsupportSet) (@hterminalClass)
      (@hgammaLast) (@hdeltaLast) (@hgammaSupport) (@hdeltaSupport) (@hgammaFirstSupport)
      (@hgammaDelta) (@hterminalColorsNotRestored) (@hsupportColors) (@hdeltaEarlier)
      (@hpreterminalPackage) (@hb4Earlier) (@hsupportComponentOrder) (@hterminalInclusion)
      (@hb2EdgesFromSeed) (@hdeltaPhiJ) (@hterminalSeed) (@hseedN) (@fN) (@hfNEdges)
      (@hfNterminal) (@hphiNProper) (@hphiNOne)

theorem helper_branch_15626.{u_1, u_2} :
    helperBranch15626Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma
      hsigmaProper hsigmaOne w hw hwComponent hwNe this q hqTerminal hqSucc hqKind hqVertex
      hqGamma hqDelta hvStage hvFinal hfirstUpper hfirstPositive jSlot hjSlot hsigmaTerminal
      segmentTrans stepSegment stageToStage vertexTransfer hdeltaExclusion hPESlotData hPEStored
      hpairOverlapColors trace hterminalJ hqActive hqClass p0 indices0 gamma0 delta0 hincreasing0
      hclass0 hgamma0 hdelta0 hchain0 hinjective0 hmissing0 rho1 hrho1Proper hrho1One hb2Missing
      hb2TreeEdges hb3EdgeEffects hb4Interchange terminalPosition hterminalAt
      hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj hseedTerminal
      hTjQ hseedVertexBefore segmentVertexBefore transportSeedRoute commonPrefix supportColors
      TjPrime hclosure hprimeElementary hseedPrime hterminalPrime hqLast hsupport0 hkind0
      hstored0 hterminalIntersection hdeltaAvoidsTj hb1Tj hcaseTwo
  have hcaseTwoPointwise : ∀ x : V,
      x ∈ (TreeSequenceVertexSet TjPrime).erase v →
        MissingColors G rho1 x ∩ supportColors = ∅ := by
    intro x hx
    apply Finset.eq_empty_of_forall_notMem
    intro c hc
    have hbig : c ∈
        ((TreeSequenceVertexSet TjPrime).erase v).biUnion
            (fun y => MissingColors G rho1 y) ∩ supportColors := by
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨x, hx, (Finset.mem_inter.mp hc).1⟩,
          (Finset.mem_inter.mp hc).2⟩
    rw [hcaseTwo] at hbig
    simp at hbig
  have hsupportSet : supportColors =
      (ExtensionBaseSupportClass ett v hvFinal v).biUnion
        (fun s => ett.series.data.stored s.succ) := by
    exact @helper_hsupportSet_3222 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@v) (@hvFinal) (@p0) (@indices0)
        (@hclass0)
  have hterminalClass : q ∈ ExtensionBaseSupportClass ett v hvFinal v :=
    hqClass
  have hgammaLast : gamma0 (Fin.last p0) = gamma := by
    apply Option.some.inj
    exact (hgamma0 (Fin.last p0)).symm.trans (by
      rw [hqLast]
      exact hqGamma)
  have hdeltaLast : delta0 (Fin.last p0) = delta := by
    apply Option.some.inj
    exact (hdelta0 (Fin.last p0)).symm.trans (by
      rw [hqLast]
      exact hqDelta)
  let gammaFirst : Fin k := gamma0 0
  have hgammaSupport : gamma ∈ supportColors := by
    exact @helper_hgammaSupport_3247 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@gamma) (@p0) (@indices0) (@gamma0)
        (@delta0) (@hstored0) (@hgammaLast)
  have hdeltaSupport : delta ∈ supportColors := by
    exact @helper_hdeltaSupport_3253 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@delta) (@p0) (@indices0) (@gamma0)
        (@delta0) (@hstored0) (@hdeltaLast)
  have hgammaFirstSupport : gammaFirst ∈ supportColors := by
    exact @helper_hgammaFirstSupport_3259 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@p0) (@indices0) (@gamma0)
        (@delta0) (@hstored0)
  have hgammaDelta : gamma ≠ delta :=
    (ParallelStepRootComponentSetup ett.series q v gamma delta hqKind
      hqVertex hqGamma hqDelta).1
  let restorationColors :=
    (ExtensionBaseRestorationIndices ett v hvFinal).biUnion
      (fun s => ett.series.data.stored s.succ)
  have hterminalColorsNotRestored :
      gamma ∉ restorationColors ∧ delta ∉ restorationColors := by
    exact @helper_hterminalColorsNotRestored_6300 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
        (@gamma) (@delta) (@hqTerminal) (@hqVertex) (@hqGamma) (@hqDelta) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@hPESlotData) (@hPEStored) (@hpairOverlapColors)
        (@hqActive) (@hqClass) (@p0) (@indices0) (@gamma0) (@delta0) (@terminalPosition) (@hqLast)
  have hsupportColors : ∀ (s : Fin ett.rounds)
      (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      gammaS ∈ supportColors ∧ deltaS ∈ supportColors := by
    exact @helper_hsupportColors_2684 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hvFinal)
        (@hPEStored) (@p0) (@indices0) (@hsupportSet)
  have hdeltaEarlier : ∀ (s : Fin ett.rounds)
      (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      delta ≠ gammaS ∧ delta ≠ deltaS := by
    exact @helper_hdeltaEarlier_6317 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@delta) (@hqTerminal)
        (@hqVertex) (@hqDelta) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hdeltaExclusion)
        (@hqActive) (@p0) (@indices0) (@gamma0) (@delta0) (@hincreasing0) (@hclass0) (@hdelta0)
        (@hinjective0) (@hqLast) (@hdeltaLast)
  have hpreterminalPackage : 0 < p0 →
      ∃ preterminalSlot : Fin ett.rounds,
        preterminalSlot.val < q.val ∧
          preterminalSlot ∈
            (ExtensionBaseSupportClass ett v hvFinal v).erase q ∧
          ett.series.data.delta preterminalSlot.succ = some gamma := by
    exact @helper_hpreterminalPackage_6328 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0) (@gamma0)
        (@delta0) (@hincreasing0) (@hclass0) (@hdelta0) (@hchain0) (@terminalPosition) (@hqLast)
        (@hgammaLast)
  have hb4Earlier : ∀ (s : Fin ett.rounds)
      (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s v rho1 gammaS deltaS := by
    exact @helper_hb4Earlier_3295 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hvFinal)
        (@trace) (@hb4Interchange)
  have hsupportComponentOrder : ∀ (s : Fin ett.rounds)
      (gammaS deltaS : Fin k),
      s ∈ (ExtensionBaseSupportClass ett v hvFinal v).erase q →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ∀ x : V,
        x ∈ TreeSequenceVertexSet
            (ett.series.data.tree s.succ.castSucc) →
        x ≠ v →
        ∀ y : V, Sum.inl y ∈
          TwoColorComponent G rho1 gammaS deltaS (Sum.inl x) →
          y ∈ TreeSequenceVertexSet
            (ett.series.data.tree q.succ.castSucc) := by
    exact @helper_hsupportComponentOrder_6348 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@gamma) (@delta)
        (@sigma) (@hqTerminal) (@hqKind) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
        (@stageToStage) (@vertexTransfer) (@trace) (@p0) (@indices0) (@gamma0) (@delta0)
        (@terminalPosition) (@hqLast) (@hb4Earlier)
  have hterminalInclusion : MissingColors G
        (ett.series.data.coloring jSlot.castSucc) v ⊆
      MissingColors G rho1 v ∪ {gammaFirst} := by
    exact @helper_hterminalInclusion_3322 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0)
        (@gamma0) (@delta0) (@hmissing0) (@hb2Missing)
  have hb2EdgesFromSeed : ∀ a : Fin
      (ett.series.data.tree jSlot.succ.castSucc).length,
      seed.length ≤ a.val →
      rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
        ett.series.data.coloring jSlot.castSucc
          ((ett.series.data.tree jSlot.succ.castSucc).edge a) := by
    intro a ha
    exact (hb2TreeEdges a).1.trans (hb2TreeEdges a).2
  have hdeltaPhiJ : delta ∉ TreeMissingColors
      (ett.series.data.coloring jSlot.castSucc)
      (ett.series.data.tree jSlot.succ.castSucc) := by
    simpa [hdeltaLast] using hdeltaAvoidsTj (Fin.last p0)
  have hterminalSeed : v ∈ TreeSequenceVertexSet seed := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨Fin.last seed.length, hseedTerminal⟩
  exact @helper_continuation_7819 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hsigmaProper) (@hsigmaOne) (@w) (@hw)
      (@hwComponent) (@hwNe) (@hqTerminal) (@hqSucc) (@hqKind) (@hqVertex) (@hqGamma) (@hqDelta)
      (@hvStage) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@hsigmaTerminal)
      (@segmentTrans) (@stepSegment) (@stageToStage) (@vertexTransfer) (@hdeltaExclusion)
      (@hPEStored) (@trace) (@hterminalJ) (@hqActive) (@p0) (@indices0) (@gamma0) (@delta0)
      (@hincreasing0) (@hclass0) (@hgamma0) (@hdelta0) (@hchain0) (@hinjective0) (@hrho1Proper)
      (@hrho1One) (@hb2Missing) (@hb2TreeEdges) (@hb3EdgeEffects) (@terminalPosition)
      (@hterminalAt) (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex)
      (@hseedTj) (@hseedTerminal) (@hTjQ) (@hseedVertexBefore) (@segmentVertexBefore)
      (@transportSeedRoute) (@commonPrefix) (@TjPrime) (@hclosure) (@hprimeElementary)
      (@hseedPrime) (@hterminalPrime) (@hqLast) (@hsupport0) (@hkind0) (@hstored0)
      (@hterminalIntersection) (@hb1Tj) (@hcaseTwoPointwise) (@hsupportSet) (@hterminalClass)
      (@hgammaLast) (@hdeltaLast) (@hgammaSupport) (@hdeltaSupport) (@hgammaFirstSupport)
      (@hgammaDelta) (@hterminalColorsNotRestored) (@hsupportColors) (@hdeltaEarlier)
      (@hpreterminalPackage) (@hb4Earlier) (@hsupportComponentOrder) (@hterminalInclusion)
      (@hb2EdgesFromSeed) (@hdeltaPhiJ) (@hterminalSeed)
private theorem helper_caseContinuation_8566.{u_1, u_2} :
    helperCaseContinuation8566Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v sigma this q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot hjSlot segmentTrans vertexTransfer trace
      hterminalJ p0 indices0 hb2 rho1 hb2Missing hb2TreeEdges terminalPosition
      hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj hseedTerminal
      commonPrefix TjPrime hqLast u huPrime b traceB huOutside rho2 c1 c2 hrho2Proper hrho2One
      uPosition huPosition huPositionPositive huPositionBound U hseedU hrouteRhoTwoU
      hterminalInclusion Tprevious hpreviousTj hpreviousStrict hpreviousSeed hroutePhiTj
  let Tj0 : TreeSequence G e0 :=
    ett.series.data.tree jSlot.succ.castSucc
  have hroutePhiTj0 : TashkinovAugmentationSequence
      (ett.series.data.coloring jSlot.castSucc) seed Tj0 := by
    simpa [Tj0] using hroutePhiTj
  have hseedTj0 : TreeSequenceInitialSegment seed Tj0 := by
    simpa [Tj0] using hseedTj
  obtain ⟨M, ⟨hunion⟩⟩ := OrderedTreeUnionExists U Tj0
  have huU : u ∈ TreeSequenceVertexSet U := by
    exact @helper_huU_2850 (@V) (@E) (@G) (@e0) (@TjPrime) (@u) (@uPosition) (@huPosition)
        (@huPositionPositive) (@huPositionBound)
  have hrouteUM : TashkinovAugmentationSequence rho2 U M := by
    as_aux_lemma =>
    have hleftSegment := hunion.leftSegment
    have hnewEntryFromRight := hunion.newEntryFromRight
    have heveryNewRightEntry := hunion.everyNewRightEntry
    have hrightOrder := hunion.rightOrder
    have prefixSegment (A : TreeSequence G e0) (r : Nat)
        (hr : 1 ≤ r) (hrA : r ≤ A.length) :
        TreeSequenceInitialSegment
          (TreeSequencePrefix A r hr hrA) A := by
      exact @helper_prefixSegment_2868 (@V) (@E) (@G) (@e0) (@A) (@r) (@hr) (@hrA)
    have prefixPrefix (A : TreeSequence G e0) (r : Nat)
        (hr : 1 ≤ r) (hrA : r + 1 ≤ A.length) :
        TreeSequenceInitialSegment
          (TreeSequencePrefix A r hr
            (Nat.le_trans (Nat.le_succ r) hrA))
          (TreeSequencePrefix A (r + 1) (by omega) hrA) := by
      exact @helper_prefixPrefix_5937 (@V) (@E) inferInstance inferInstance inferInstance (@G)
          (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
          (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0) (@terminalPosition)
          (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime) (@uPosition) (@A)
          (@r) (@hr) (@hrA)
    have prefixSelf (A : TreeSequence G e0) :
        TreeSequencePrefix A A.length A.positive le_rfl = A := by
      exact @helper_prefixSelf_2890 (@V) (@E) (@G) (@e0) (@A)
    have equalPrefixes {A B D : TreeSequence G e0}
        (hAD : TreeSequenceInitialSegment A D)
        (hBD : TreeSequenceInitialSegment B D)
        (hlen : A.length = B.length) : A = B := by
      exact @helper_equalPrefixes_2607 (@V) (@E) (@G) (@e0) (@A) (@B) (@D) (@hAD) (@hBD) (@hlen)
    have prefixAtLeft :
        TreeSequencePrefix M U.length U.positive hleftSegment.1 = U := by
      apply equalPrefixes
        (prefixSegment M U.length U.positive hleftSegment.1)
        hleftSegment
      rfl
    have hseedTjSegment : TreeSequenceInitialSegment seed Tj0 :=
      TashkinovAugmentationSequenceInitialSegment _ _ _ hroutePhiTj0
    have firstStep {A B : TreeSequence G e0}
        (hAB : TashkinovAugmentationSequence
          (ett.series.data.coloring jSlot.castSucc) A B)
        (hlt : A.length < B.length) :
        ∃ C, TashkinovAugmentation
            (ett.series.data.coloring jSlot.castSucc) A C ∧
          TashkinovAugmentationSequence
            (ett.series.data.coloring jSlot.castSucc) C B := by
      unfold TashkinovAugmentationSequence at hAB ⊢
      induction hAB using Relation.ReflTransGen.head_induction_on with
      | refl => omega
      | @head A C hAC hCB ih => exact ⟨C, hAC, hCB⟩
    have replay : ∀ n (hnU : U.length ≤ n) (hnM : n ≤ M.length),
        TashkinovAugmentationSequence rho2 U
          (TreeSequencePrefix M n
            (Nat.le_trans U.positive hnU) hnM) := by
      intro n hnU hnM
      induction n, hnU using Nat.le_induction with
      | base =>
          simpa [prefixAtLeft] using
            (show TashkinovAugmentationSequence rho2 U U from
              Relation.ReflTransGen.refl)
      | @succ n hnU ih =>
          exact @helper_branch_15456 (@V) (@E) inferInstance inferInstance inferInstance (@G)
              (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma)
              (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@vertexTransfer)
              (@trace) (@p0) (@indices0) (@hb2) (@hb2Missing) (@hb2TreeEdges)
              (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
              (@TjPrime) (@u) (@huPrime) (@b) (@traceB) (@c2) (@uPosition)
              (@huPositionPositive) (@huPositionBound) (@hseedU) (@hterminalInclusion)
              (@hroutePhiTj0) (@M) (@huU) (@hleftSegment) (@hnewEntryFromRight)
              (@heveryNewRightEntry) (@hrightOrder) (@prefixSegment) (@prefixPrefix)
              (@hseedTjSegment) (@firstStep) (@n) (@hnU) (@ih) (@hnM)
    have hfull := replay M.length hleftSegment.1 le_rfl
    simpa [prefixSelf] using hfull
  exact @helper_caseContinuation_10294 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
      (@hjSlot) (@segmentTrans) (@vertexTransfer) (@trace) (@hterminalJ) (@p0) (@indices0)
      (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex)
      (@hseedTj) (@hseedTerminal) (@commonPrefix) (@TjPrime) (@hqLast) (@u) (@b) (@traceB)
      (@huOutside) (@c1) (@hrho2Proper) (@hrho2One) (@uPosition) (@huPositionPositive)
      (@huPositionBound) (@hrouteRhoTwoU) (@hpreviousTj) (@hpreviousStrict) (@hpreviousSeed)
      (@hseedTj0) (@M) (@hunion) (@huU) (@hrouteUM)

theorem helper_continuation_14753.{u_1, u_2} :
    helperContinuation14753Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma
      hsigmaProper hsigmaOne w hw hwComponent hwNe this q hqTerminal hqSucc hqKind hqVertex
      hqGamma hqDelta hvStage hvFinal hfirstUpper hfirstPositive jSlot hjSlot hsigmaTerminal
      segmentTrans stepSegment stageToStage vertexTransfer hdeltaExclusion hPESlotData hPEStored
      hpairOverlapColors trace hterminalJ hqActive hqClass p0 indices0 gamma0 delta0 hincreasing0
      hclass0 hgamma0 hdelta0 hchain0 hinjective0 hmissing0 hb2 rho1 hrho1Proper hrho1One
      hb2Missing hb2TreeEdges hb3EdgeEffects hb4Interchange terminalPosition hterminalAt
      hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj hseedTerminal
      hTjQ hseedVertexBefore segmentVertexBefore transportSeedRoute commonPrefix supportColors
      TjPrime hclosure hprimeElementary hcaseSplit hseedPrime hterminalPrime hqLast hsupport0
      hkind0 hstored0 hterminalIntersection hdeltaAvoidsTj hb1Tj hcaseOnePrepared
  rcases hcaseSplit with hcaseOne | hcaseTwo
  · obtain ⟨u, huPrime, b, traceB, huOutside, hinvariantB,
        hclaim44⟩ := hcaseOnePrepared hcaseOne
    let rho2 : PartialEdgeColoring E k :=
      traceB.coloring (Fin.last traceB.steps)
    dsimp only at hclaim44
    obtain ⟨c1, c2, c3⟩ := hclaim44
    have hrho2Proper : IsProperEdgeColoring G rho2 := by
      simpa [rho2] using (hinvariantB.1 (Fin.last traceB.steps)).1
    have hrho2One : IsOneEdgeUncolored rho2 e0 := by
      simpa [rho2] using (hinvariantB.1 (Fin.last traceB.steps)).2
    obtain ⟨uPosition, -, huPosition⟩ := Finset.mem_image.mp huPrime
    have huNotSeed : u ∉ TreeSequenceVertexSet seed := by
      intro huSeed
      exact huOutside (vertexTransfer hseedTj huSeed)
    have hseedBeforeU : seed.length < uPosition.val := by
      exact @helper_hseedBeforeU_5770 (@V) (@E) inferInstance inferInstance inferInstance (@G)
          (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
          (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0) (@terminalPosition)
          (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime) (@hseedPrime) (@u)
          (@uPosition) (@huPosition) (@huNotSeed)
    have huPositionPositive : 1 ≤ uPosition.val := by
      exact seed.positive.trans (Nat.le_of_lt hseedBeforeU)
    have huPositionBound : uPosition.val ≤ TjPrime.length :=
      Nat.lt_succ_iff.mp uPosition.isLt
    let U : TreeSequence G e0 :=
      TreeSequencePrefix TjPrime uPosition.val huPositionPositive
        huPositionBound
    have hUPrime : TreeSequenceInitialSegment U TjPrime := by
      exact @helper_hUPrime_2738 (@V) (@E) (@G) (@e0) (@TjPrime) (@uPosition)
          (@huPositionPositive) (@huPositionBound)
    have hseedU : TreeSequenceInitialSegment seed U := by
      apply commonPrefix hseedPrime hUPrime
      exact Nat.le_of_lt hseedBeforeU
    have hrouteRhoOneU : TashkinovAugmentationSequence rho1 seed U :=
      TashkinovAugmentationSequenceRestrict rho1 seed U TjPrime
        hclosure.1 hseedU hUPrime
    have hprimeVertexBefore (i : Fin (TjPrime.length + 1))
        (hi : i.val < uPosition.val) :
        TjPrime.vertex i ∈ TreeVerticesBefore TjPrime u huPrime := by
      exact @helper_hprimeVertexBefore_2750 (@V) (@E) inferInstance (@G) (@e0) (@TjPrime) (@u)
          (@huPrime) (@uPosition) (@huPosition) (@i) (@hi)
    have hUsegmentVertexBefore {A : TreeSequence G e0}
        (hAU : TreeSequenceInitialSegment A U)
        (hAlen : A.length < U.length) {x : V}
        (hxA : x ∈ TreeSequenceVertexSet A) :
        x ∈ TreeVerticesBefore TjPrime u huPrime := by
      exact @helper_hUsegmentVertexBefore_5797 (@V) (@E) inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
          (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0)
          (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime)
          (@u) (@huPrime) (@uPosition) (@huPositionPositive) (@huPositionBound) (@hUPrime)
          (@hprimeVertexBefore) (@A) (@hAU) (@hAlen) (@x) (@hxA)
    have transportUStep {A B : TreeSequence G e0}
        (hstep : TashkinovAugmentation rho1 A B)
        (hBU : TreeSequenceInitialSegment B U) :
        TashkinovAugmentation rho2 A B := by
      exact @helper_transportUStep_5808 (@V) (@E) inferInstance inferInstance inferInstance (@G)
          (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
          (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@segmentTrans) (@trace) (@p0) (@indices0)
          (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime)
          (@u) (@huPrime) (@b) (@traceB) (@c2) (@uPosition) (@huPosition) (@huPositionPositive)
          (@huPositionBound) (@hUPrime) (@hUsegmentVertexBefore) (@A) (@B) (@hstep) (@hBU)
    have transportURoute (S : TreeSequence G e0)
        (hroute : TashkinovAugmentationSequence rho1 S U) :
        TashkinovAugmentationSequence rho2 S U := by
      exact @helper_transportURoute_2771 (@V) (@E) inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@v) (@sigma) (@hvFinal) (@trace)
          (@p0) (@indices0) (@TjPrime) (@u) (@b) (@traceB) (@uPosition) (@huPositionPositive)
          (@huPositionBound) (@transportUStep) (@S) (@hroute)
    have hrouteRhoTwoU : TashkinovAugmentationSequence rho2 seed U :=
      transportURoute seed hrouteRhoOneU
    have hterminalMissingEq : MissingColors G rho2 v =
        MissingColors G rho1 v := by
      exact c2.1 v (Finset.mem_union_left _ hterminalJ)
    have hterminalInclusion : MissingColors G
          (ett.series.data.coloring jSlot.castSucc) v ⊆
        MissingColors G rho2 v ∪ MissingColors G rho2 u := by
      exact @helper_hterminalInclusion_5831 (@V) (@E) inferInstance inferInstance inferInstance
          (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma)
          (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@p0) (@indices0)
          (@gamma0) (@delta0) (@hmissing0) (@hb2Missing) (@u) (@b) (@traceB) (@c3)
          (@hterminalMissingEq)
    let Tprevious : TreeSequence G e0 :=
      ett.series.data.tree jSlot.castSucc.castSucc
    have hvNotPrevious (hjPositive : 0 < jSlot.val) :
        v ∉ TreeSequenceVertexSet Tprevious := by
      exact @helper_hvNotPrevious_5841 (@V) (@E) inferInstance inferInstance inferInstance (@G)
          (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
          (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@p0) (@indices0)
          (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime)
          (@hqLast) (@uPosition) (@hjPositive)
    have hpreviousTj (hjPositive : 0 < jSlot.val) :
        TreeSequenceInitialSegment Tprevious
          (ett.series.data.tree jSlot.succ.castSucc) := by
      have hstep := stepSegment jSlot.castSucc (by simpa using hjPositive)
      rw [hjTreeIndex] at hstep
      exact hstep
    have hpreviousStrict (hjPositive : 0 < jSlot.val) :
        Tprevious.length < seed.length := by
      exact @helper_hpreviousStrict_5854 (@V) (@E) inferInstance inferInstance inferInstance (@G)
          (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
          (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0) (@terminalPosition)
          (@hterminalAt) (@hterminalPositionPositive) (@hterminalPositionBound) (@TjPrime)
          (@uPosition) (@hvNotPrevious) (@hpreviousTj) (@hjPositive)
    have hpreviousSeed (hjPositive : 0 < jSlot.val) :
        TreeSequenceInitialSegment Tprevious seed :=
      commonPrefix (hpreviousTj hjPositive) hseedTj
        (Nat.le_of_lt (hpreviousStrict hjPositive))
    have hroutePhiTj : TashkinovAugmentationSequence
        (ett.series.data.coloring jSlot.castSucc) seed
        (ett.series.data.tree jSlot.succ.castSucc) := by as_aux_lemma =>
      generalize htarget : jSlot.castSucc = target
      cases ett.series.certified target with
      | initial triple seedLength initialColoring initialStored initialEdges
          initialKind initialVertex initialOutside initialDelta initialGamma
          initialClosure =>
              exact @helper_branch_5870 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                  (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
                  (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@terminalPosition)
                  (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTj)
                  (@commonPrefix) (@seedLength) (@initialClosure) (@htarget)
      | SE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternative
          currentColoring currentStored currentEdges currentKind currentVertex
          currentOutside currentDelta currentGamma adjoined adjoinedExactly
          closedExtension orderedExtension strictExtension =>
              exact @helper_branch_5878 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                  (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
                  (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0)
                  (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
                  (@hjTreeIndex) (@hseedTj) (@commonPrefix) (@TjPrime) (@uPosition)
                  (@hpreviousStrict) (@i) (@choice) (@adjoined) (@adjoinedExactly)
                  (@closedExtension) (@htarget)
      | PE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
          chosenGamma gammaRule secondStable secondStableProper
          secondStableOneUncolored secondStableRelation exitWitness
          currentColoring currentProper currentOneUncolored currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma closedExtension orderedExtension strictExtension =>
              exact @helper_branch_5890 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                  (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
                  (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0)
                  (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
                  (@hjTreeIndex) (@hseedTj) (@TjPrime) (@uPosition) (@hpreviousSeed) (@i)
                  (@closedExtension) (@htarget)
      | RE i previousProper previousOneUncolored previousClosed
          previousNotStronglyClosed available currentColoring currentStored
          currentEdges currentKind currentVertex currentOutside currentDelta
          currentGamma adjoined adjoinedExactly closedExtension orderedExtension
          strictExtension =>
              exact @helper_branch_5903 (@V) (@E) inferInstance inferInstance inferInstance (@G)
                  (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
                  (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@p0) (@indices0)
                  (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
                  (@hjTreeIndex) (@hseedTj) (@commonPrefix) (@TjPrime) (@uPosition)
                  (@hpreviousStrict) (@i) (@available) (@adjoined) (@adjoinedExactly)
                  (@closedExtension) (@htarget)
    exact @helper_caseContinuation_8566 (@V) (@E) inferInstance inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
        (@hlower) (@v) (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
        (@hjSlot) (@segmentTrans) (@vertexTransfer) (@trace) (@hterminalJ) (@p0) (@indices0)
        (@hb2) (@hb2Missing) (@hb2TreeEdges) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj) (@hseedTerminal) (@commonPrefix)
        (@TjPrime) (@hqLast) (@u) (@huPrime) (@b) (@traceB) (@huOutside) (@c1) (@c2)
        (@hrho2Proper) (@hrho2One) (@uPosition) (@huPosition) (@huPositionPositive)
        (@huPositionBound) (@hseedU) (@hrouteRhoTwoU) (@hterminalInclusion) (@hpreviousTj)
        (@hpreviousStrict) (@hpreviousSeed) (@hroutePhiTj)
  · exact @helper_branch_15626 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@hlower) (@v)
      (@gamma) (@delta) (@sigma) (@hsigmaProper) (@hsigmaOne) (@w) (@hw) (@hwComponent) (@hwNe)
      (@hqTerminal) (@hqSucc) (@hqKind) (@hqVertex) (@hqGamma) (@hqDelta) (@hvStage) (@hvFinal)
      (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@hsigmaTerminal) (@segmentTrans) (@stepSegment)
      (@stageToStage) (@vertexTransfer) (@hdeltaExclusion) (@hPESlotData) (@hPEStored)
      (@hpairOverlapColors) (@trace) (@hterminalJ) (@hqActive) (@hqClass) (@p0) (@indices0)
      (@gamma0) (@delta0) (@hincreasing0) (@hclass0) (@hgamma0) (@hdelta0) (@hchain0)
      (@hinjective0) (@hmissing0) (@hrho1Proper) (@hrho1One) (@hb2Missing) (@hb2TreeEdges)
      (@hb3EdgeEffects) (@hb4Interchange) (@terminalPosition) (@hterminalAt)
      (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex) (@hseedTj)
      (@hseedTerminal) (@hTjQ) (@hseedVertexBefore) (@segmentVertexBefore) (@transportSeedRoute)
      (@commonPrefix) (@TjPrime) (@hclosure) (@hprimeElementary) (@hseedPrime) (@hterminalPrime)
      (@hqLast) (@hsupport0) (@hkind0) (@hstored0) (@hterminalIntersection) (@hdeltaAvoidsTj)
      (@hb1Tj) (@hcaseTwo)
private theorem helper_hcaseOnePrepared_8906.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (generating : PartialEdgeColoring E k)
      (ett : ExtendedTashkinovTree G k e0 input T generating)
      (hpositive : (0 : ℕ) < ett.rounds) (v : V) (sigma : PartialEdgeColoring E k),
    let this : DecidableEq V := Classical.decEq V;
    let q : Fin ett.rounds :=
      (⟨ett.rounds - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (hqTerminal : (↑q : ℕ) + (1 : ℕ) = ett.rounds) (hvFinal : v ∈ TreeSequenceVertexSet T)
      (hfirstUpper : ETTFirstAppearanceIndex ett v hvFinal ≤ (↑q : ℕ) + (1 : ℕ))
      (hfirstPositive : (0 : ℕ) < ETTFirstAppearanceIndex ett v hvFinal),
    let jSlot : Fin ett.rounds :=
      (⟨ETTFirstAppearanceIndex ett v hvFinal - (1 : ℕ), by
          omega⟩ :
        Fin ett.rounds);
    ∀ (_ : (↑jSlot : ℕ) + (1 : ℕ) = ETTFirstAppearanceIndex ett v hvFinal)
      (_ : (↑jSlot : ℕ) ≤ (↑q : ℕ))
      (_ :
        ∀ (a b : ℕ),
          (1 : ℕ) ≤ a →
            ∀ (_hab : a ≤ b) (_hb : b ≤ ett.rounds),
              TreeSequenceInitialSegment
                (ett.series.data.tree
                  (⟨a, by
                      omega⟩ :
                    Fin (ett.rounds + (2 : ℕ))))
                (ett.series.data.tree
                  (⟨b, by
                      omega⟩ :
                    Fin (ett.rounds + (2 : ℕ)))))
      (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma)
      (hterminalJ : v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc))
      (p0 : ℕ) (indices0 : Fin (p0 + (1 : ℕ)) → Fin ett.rounds)
      (gamma0 delta0 : Fin (p0 + (1 : ℕ)) → Fin k)
      (_ :
        ∀ (a b : Fin (p0 + (1 : ℕ))),
          (↑a : ℕ) < (↑b : ℕ) → (↑(indices0 a) : ℕ) < (↑(indices0 b) : ℕ))
      (_ :
        ∀ (r : Fin ett.rounds),
          r ∈ ExtensionBaseSupportClass ett v hvFinal v ↔
            ∃ (a : Fin (p0 + (1 : ℕ))), indices0 a = r)
      (_ :
        ∀ (a : Fin (p0 + (1 : ℕ))),
          ett.series.data.gamma (indices0 a).succ = some (gamma0 a))
      (_ :
        ∀ (a : Fin (p0 + (1 : ℕ))),
          ett.series.data.delta (indices0 a).succ = some (delta0 a))
      (_ : ∀ (a : Fin p0), gamma0 a.succ = delta0 a.castSucc)
      (_ :
        Function.Injective (Fin.cons (gamma0 (0 : Fin (p0 + (1 : ℕ)))) delta0)),
    let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
    ∀ (_ : IsProperEdgeColoring G rho1) (_ : IsOneEdgeUncolored rho1 e0)
      (_ :
        (∀ x ∈ (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)).erase v,
            MissingColors G rho1 x =
              MissingColors G (ett.series.data.coloring jSlot.castSucc) x) ∧
          MissingColors G rho1 v = MissingColors G sigma v)
      (_ :
        ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
          s ∈ ExtensionBaseSupportClass ett v hvFinal v →
            s ≠ q →
              ett.series.data.chosenVertex s.succ = some v →
                ett.series.data.gamma s.succ = some gammaS →
                  ett.series.data.delta s.succ = some deltaS →
                    ETTStrongInterchangeable ett s v rho1 gammaS deltaS)
      (terminalPosition : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ)))
      (_ : (ett.series.data.tree jSlot.succ.castSucc).vertex terminalPosition = v)
      (hterminalPositionPositive : (1 : ℕ) ≤ (↑terminalPosition : ℕ))
      (hterminalPositionBound :
        (↑terminalPosition : ℕ) ≤ (ett.series.data.tree jSlot.succ.castSucc).length),
    let seed : TreeSequence G e0 :=
      TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc) (↑terminalPosition : ℕ)
        hterminalPositionPositive hterminalPositionBound;
    let supportColors : Finset (Fin k) :=
      Finset.univ.biUnion fun (a : Fin (p0 + (1 : ℕ))) ↦
        ett.series.data.stored (indices0 a).succ;
    ∀ (TjPrime : TreeSequence G e0) (_ : TashkinovClosure rho1 seed TjPrime)
      (_ : ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime))
      (_ : v ∈ TreeSequenceVertexSet TjPrime)
      (_ : indices0 (Fin.last p0) = q)
      (_ :
        ∀ (a : Fin (p0 + (1 : ℕ))), ett.series.data.chosenVertex (indices0 a).succ = some v)
      (_ :
        ∀ (a : Fin (p0 + (1 : ℕ))),
          ett.series.data.kind (indices0 a).succ = some TashkinovExtensionKind.PE)
      (_ :
        ∀ (a : Fin (p0 + (1 : ℕ))),
          ett.series.data.stored (indices0 a).succ =
            (insert (gamma0 a) ({delta0 a} : Finset (Fin k)) : Finset (Fin k)))
      (_ :
        (MissingColors G rho1 v ∩ supportColors : Finset (Fin k)) =
          ({delta0 (Fin.last p0)} : Finset (Fin k)))
      (_ :
        gamma0 (0 : Fin (p0 + (1 : ℕ))) ∈
          MissingColors G (ett.series.data.coloring jSlot.castSucc) v)
      (_ :
        ∀ (a : Fin (p0 + (1 : ℕ))),
          delta0 a ∉
            TreeMissingColors (ett.series.data.coloring jSlot.castSucc)
              (ett.series.data.tree jSlot.succ.castSucc))
      (_ :
        ColoredVertexSetElementary G (ett.series.data.coloring jSlot.castSucc)
          (TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc)))
      (_ :
        StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
          (TashkinovStoredColors ett.series.data jSlot.castSucc)
          (ett.series.data.coloring jSlot.castSucc) rho1),
    ((((TreeSequenceVertexSet TjPrime).erase v).biUnion fun (x : V) ↦
              MissingColors G rho1 x) ∩
            supportColors :
          Finset (Fin k)).Nonempty →
    ∃ (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (b : Fin (p0 + (1 : ℕ))) (traceB
      : ExtensionBaseAlgorithmBTrace ett v rho1 u p0 indices0 b),
    u ∉ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∧
    ExtensionBaseAlgorithmBInvariant ett v jSlot rho1 u p0 indices0 b traceB ∧
    let rho2 : PartialEdgeColoring E k := traceB.coloring (Fin.last traceB.steps);
    StableColoringBeforeVertex (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
        (TashkinovStoredColors ett.series.data jSlot.castSucc)
        (ett.series.data.coloring jSlot.castSucc) rho2 ∧
    ((∀
          x ∈
            TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) ∪
              TreeVerticesBefore TjPrime u huPrime,
          MissingColors G rho2 x = MissingColors G rho1 x) ∧
        ∀ (f : E),
          ((∃ (a : Fin (ett.series.data.tree jSlot.succ.castSucc).length),
                (ett.series.data.tree jSlot.succ.castSucc).edge a = f) ∨
              ∃ (a : Fin TjPrime.length) (z : Fin (TjPrime.length + (1 : ℕ))),
                TjPrime.vertex z = u ∧ (↑a : ℕ) < (↑z : ℕ) ∧ TjPrime.edge a = f) →
            rho2 f = rho1 f) ∧
    gamma0 (0 : Fin (p0 + (1 : ℕ))) ∈ MissingColors G rho2 u := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot hjSlot hjle stageToStage trace hterminalJ p0 indices0
      gamma0 delta0 hincreasing0 hclass0 hgamma0 hdelta0 hchain0 hinjective0 rho1 hrho1Proper
      hrho1One hb2Missing hb4Interchange terminalPosition hterminalAt hterminalPositionPositive
      hterminalPositionBound seed supportColors TjPrime hclosure hprimeElementary hterminalPrime
      hqLast hsupport0 hkind0 hstored0 hterminalIntersection hfirstGammaMissing hdeltaAvoidsTj
      hTjElementary hb1Tj hcaseOne
  obtain ⟨u, huPrime, b, huNe, hselected, hminimal, hfirstChoice,
      huOutside, hprefixData⟩ :=
    ExtensionBaseCaseOneSelection ett v hvFinal jSlot q hjle hqTerminal
      hjSlot rho1 seed TjPrime terminalPosition hterminalAt
      hterminalPositionPositive rfl hclosure hterminalPrime p0 indices0
      gamma0 delta0 hincreasing0 hclass0 hqLast hgamma0 hdelta0 hstored0
      hchain0 hinjective0 (by simpa [supportColors] using hcaseOne)
      hprimeElementary (by simpa [supportColors] using hterminalIntersection)
      hTjElementary hb2Missing.1 hfirstGammaMissing hdeltaAvoidsTj
  dsimp only at hprefixData
  have hinitialB : ∀ a : Fin (p0 + 1), a.val < b.val →
      ETTStrongInterchangeable ett (indices0 a) v rho1
        (gamma0 a) (delta0 a) := by
    exact @helper_hinitialB_2039 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hvFinal)
        (@trace) (@p0) (@indices0) (@gamma0) (@delta0) (@hincreasing0) (@hclass0) (@hgamma0)
        (@hdelta0) (@hb4Interchange) (@hqLast) (@hsupport0) (@b)
  have hTjInitialB : ∀ a : Fin (p0 + 1), a.val < b.val →
      TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree (indices0 a).succ.castSucc) := by
    exact @helper_hTjInitialB_2054 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@stageToStage) (@p0)
        (@indices0) (@hclass0) (@terminalPosition) (@hqLast) (@b)
  obtain ⟨traceB, hinvariantB⟩ :=
    ExtensionBaseAlgorithmB ett v jSlot rho1 u p0 indices0 gamma0 delta0
      b hrho1Proper hrho1One hincreasing0 hsupport0 hkind0 hgamma0
      hdelta0 hchain0 hinjective0 hselected hminimal hinitialB
      hTjInitialB hprefixData.2.2 hstored0
  have hprefixSubset :
      (ExtensionBaseCaseOneIndices ett p0 indices0 b).biUnion
          (fun t => ett.series.data.stored t.succ) ⊆
        supportColors := by
    exact @helper_hprefixSubset_2691 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@p0) (@indices0) (@b)
  have hprefixAvoids :
      (TreeVerticesBefore TjPrime u huPrime).biUnion
            (fun x => MissingColors G rho1 x) ∩
          ((ExtensionBaseCaseOneIndices ett p0 indices0 b).biUnion
            fun t => ett.series.data.stored t.succ) = ∅ := by
    exact @helper_hprefixAvoids_2180 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@v) (@sigma) (@hvFinal) (@trace) (@p0)
        (@indices0) (@delta0) (@TjPrime) (@u) (@huPrime) (@b) (@hprefixData) (@hprefixSubset)
  have hclaim44 := ExtensionBaseClaim44 ett v hvFinal jSlot hjSlot rho1
    (TashkinovStoredColors ett.series.data jSlot.castSucc) u TjPrime seed
    terminalPosition hterminalAt hterminalPositionPositive rfl huPrime p0
    indices0 gamma0 delta0 b hincreasing0 hclass0 traceB hinvariantB
    hb1Tj huOutside hclosure hprefixAvoids hselected hminimal hgamma0
    hdelta0 hchain0 hinjective0 hstored0
  dsimp only at hclaim44
  exact ⟨u, huPrime, b, traceB, huOutside, hinvariantB, hclaim44⟩

theorem helper_continuation_14264.{u_1, u_2} :
    helperContinuation14264Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma
      hsigmaProper hsigmaOne w hw hwComponent hwNe this q hqTerminal hqSucc hqKind hqVertex
      hqGamma hqDelta hvStage hvFinal hfirstUpper hfirstPositive jSlot hjSlot hjle hsigmaTerminal
      segmentTrans stepSegment stageToStage vertexTransfer hdeltaExclusion hPESlotData hPEStored
      hpairOverlapColors trace hterminalJ hqActive hqClass p0 indices0 gamma0 delta0 hincreasing0
      hclass0 hgamma0 hdelta0 hchain0 hinjective0 hmissing0 hb2 rho1 hrho1Proper hrho1One hb1Rho
      hb2Missing hb2TreeEdges hb3EdgeEffects hb4Interchange terminalPosition hterminalAt
      hterminalPositionPositive hterminalPositionBound seed hjTreeIndex hseedTj hseedTerminal
      hTjQ hqFinal hseedVertexBefore segmentVertexBefore transportStep
  have transportSeedRoute (S : TreeSequence G e0)
      (hroute : TashkinovAugmentationSequence
        (ett.series.data.coloring jSlot.castSucc) S seed) :
      TashkinovAugmentationSequence rho1 S seed := by
    exact @helper_transportSeedRoute_2514 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma)
        (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@transportStep) (@S) (@hroute)
  have commonPrefix {A B C : TreeSequence G e0}
      (hAC : TreeSequenceInitialSegment A C)
      (hBC : TreeSequenceInitialSegment B C)
      (hlen : A.length ≤ B.length) :
      TreeSequenceInitialSegment A B := by
    exact @helper_commonPrefix_1530 (@V) (@E) (@G) (@e0) (@A) (@B) (@C) (@hAC) (@hBC) (@hlen)
  let supportColors := Finset.univ.biUnion fun a : Fin (p0 + 1) =>
    ett.series.data.stored (indices0 a).succ
  obtain ⟨TjPrime, hclosure, hprimeElementary, hcaseSplit⟩ :
      ∃ TjPrime : TreeSequence G e0,
        TashkinovClosure rho1 seed TjPrime ∧
          ColoredVertexSetElementary G rho1
            (TreeSequenceVertexSet TjPrime) ∧
          (let awayMissing :=
            ((TreeSequenceVertexSet TjPrime).erase v).biUnion
              fun x => MissingColors G rho1 x
           (awayMissing ∩ supportColors).Nonempty ∨
             awayMissing ∩ supportColors = ∅) := by
    by_cases hjPositive : 0 < jSlot.val
    · exact @helper_branch_5591 (@V) (@E) inferInstance inferInstance  inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive) (@hlower) (@v)
        (@sigma) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot)
        (@stepSegment) (@trace) (@p0) (@indices0) (@hrho1Proper) (@hrho1One) (@hb1Rho)
        (@terminalPosition) (@hterminalAt) (@hterminalPositionPositive) (@hterminalPositionBound)
        (@hjTreeIndex) (@hseedTj) (@segmentVertexBefore) (@transportSeedRoute) (@commonPrefix)
        (@hjPositive)
    · exact @helper_branch_1907 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@trace) (@p0) (@indices0)
        (@hrho1Proper) (@hrho1One) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hseedTj) (by assumption) (@commonPrefix) (@hjPositive)
  have hseedPrime : TreeSequenceInitialSegment seed TjPrime :=
    TashkinovAugmentationSequenceInitialSegment rho1 seed TjPrime hclosure.1
  have hterminalPrime : v ∈ TreeSequenceVertexSet TjPrime := by
    apply vertexTransfer hseedPrime
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨Fin.last seed.length, hseedTerminal⟩
  have hqLast : indices0 (Fin.last p0) = q := by
    exact @helper_hqLast_2554 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@hqClass) (@p0) (@indices0) (@hincreasing0)
        (@hclass0) (@terminalPosition)
  have hsupport0 : ∀ a : Fin (p0 + 1),
      ett.series.data.chosenVertex (indices0 a).succ = some v := by
    intro a
    have ha := (hclass0 (indices0 a)).2 ⟨a, rfl⟩
    simp only [ExtensionBaseSupportClass, Finset.mem_filter] at ha
    exact ha.2
  have hkind0 : ∀ a : Fin (p0 + 1),
      ett.series.data.kind (indices0 a).succ =
        some TashkinovExtensionKind.PE := by
    exact @helper_hkind0_2572 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@v) (@hvFinal) (@p0) (@indices0) (@hclass0)
  have hstored0 : ∀ a : Fin (p0 + 1),
      ett.series.data.stored (indices0 a).succ =
        {gamma0 a, delta0 a} := by
    intro a
    exact hPEStored (indices0 a) (gamma0 a) (delta0 a) (hkind0 a)
      (hgamma0 a) (hdelta0 a)
  have hterminalIntersection : MissingColors G rho1 v ∩ supportColors =
      {delta0 (Fin.last p0)} := by
    dsimp [supportColors]
    rw [hb2Missing.2]
    exact hmissing0.1
  have hfirstGammaMissing : gamma0 0 ∈ MissingColors G
      (ett.series.data.coloring jSlot.castSucc) v := by
    rw [hmissing0.2]
    simp
  have hdeltaAvoidsTj : ∀ a : Fin (p0 + 1),
      delta0 a ∉ TreeMissingColors
        (ett.series.data.coloring jSlot.castSucc)
        (ett.series.data.tree jSlot.succ.castSucc) := by
    exact @helper_hdeltaAvoidsTj_2598 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hdeltaExclusion) (@p0) (@indices0)
        (@delta0) (@hclass0) (@hdelta0) (@hsupport0)
  have hTjElementary : ColoredVertexSetElementary G
      (ett.series.data.coloring jSlot.castSucc)
      (TreeSequenceVertexSet
        (ett.series.data.tree jSlot.succ.castSucc)) := by
    exact @helper_hTjElementary_2030 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
        (@hlower) (@v) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot)
        (@p0) (@indices0) (@terminalPosition) (@hqLast)
  have hTjFinal : TreeSequenceInitialSegment
      (ett.series.data.tree jSlot.succ.castSucc) T :=
    segmentTrans hTjQ hqFinal
  have hbeforeTjFinal : TreeVerticesBefore
        (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ ⊆
      TreeVerticesBefore T v hvFinal := by
    exact @helper_hbeforeTjFinal_2616 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@vertexTransfer) (@hterminalJ) (@hTjFinal)
  have hb1Tj : StableColoringBeforeVertex
      (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
      (TashkinovStoredColors ett.series.data jSlot.castSucc)
      (ett.series.data.coloring jSlot.castSucc) rho1 := by
    exact @helper_hb1Tj_1978 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@trace) (@hterminalJ) (@hb1Rho)
        (@hbeforeTjFinal)
  have hcaseOnePrepared :
      (((TreeSequenceVertexSet TjPrime).erase v).biUnion
          (fun x => MissingColors G rho1 x) ∩ supportColors).Nonempty →
        ∃ (u : V) (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
          (b : Fin (p0 + 1))
          (traceB : ExtensionBaseAlgorithmBTrace ett v rho1 u
            p0 indices0 b),
          u ∉ TreeSequenceVertexSet
              (ett.series.data.tree jSlot.succ.castSucc) ∧
            ExtensionBaseAlgorithmBInvariant ett v jSlot rho1 u
              p0 indices0 b traceB ∧
            (let rho2 := traceB.coloring (Fin.last traceB.steps)
             StableColoringBeforeVertex
                  (ett.series.data.tree jSlot.succ.castSucc) v hterminalJ
                  (TashkinovStoredColors ett.series.data jSlot.castSucc)
                  (ett.series.data.coloring jSlot.castSucc) rho2 ∧
               ((∀ x : V,
                  x ∈ TreeSequenceVertexSet
                        (ett.series.data.tree jSlot.succ.castSucc) ∪
                      TreeVerticesBefore TjPrime u huPrime →
                  MissingColors G rho2 x = MissingColors G rho1 x) ∧
                ∀ f : E,
                  ((∃ a : Fin (ett.series.data.tree
                        jSlot.succ.castSucc).length,
                      (ett.series.data.tree
                        jSlot.succ.castSucc).edge a = f) ∨
                    ∃ (a : Fin TjPrime.length)
                      (z : Fin (TjPrime.length + 1)),
                      TjPrime.vertex z = u ∧ a.val < z.val ∧
                        TjPrime.edge a = f) →
                  rho2 f = rho1 f) ∧
               gamma0 0 ∈ MissingColors G rho2 u) := by
    exact @helper_hcaseOnePrepared_8906 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@hjle) (@stageToStage) (@trace)
        (@hterminalJ) (@p0) (@indices0) (@gamma0) (@delta0) (@hincreasing0) (@hclass0) (@hgamma0)
        (@hdelta0) (@hchain0) (@hinjective0) (@hrho1Proper) (@hrho1One) (@hb2Missing)
        (@hb4Interchange) (@terminalPosition) (@hterminalAt) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@TjPrime) (@hclosure) (@hprimeElementary) (@hterminalPrime)
        (@hqLast) (@hsupport0) (@hkind0) (@hstored0) (@hterminalIntersection)
        (@hfirstGammaMissing) (@hdeltaAvoidsTj) (@hTjElementary) (@hb1Tj)
  exact @helper_continuation_14753 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hsigmaProper) (@hsigmaOne) (@w) (@hw)
      (@hwComponent) (@hwNe) (@hqTerminal) (@hqSucc) (@hqKind) (@hqVertex) (@hqGamma) (@hqDelta)
      (@hvStage) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@hsigmaTerminal)
      (@segmentTrans) (@stepSegment) (@stageToStage) (@vertexTransfer) (@hdeltaExclusion)
      (@hPESlotData) (@hPEStored) (@hpairOverlapColors) (@trace) (@hterminalJ) (@hqActive)
      (@hqClass) (@p0) (@indices0) (@gamma0) (@delta0) (@hincreasing0) (@hclass0) (@hgamma0)
      (@hdelta0) (@hchain0) (@hinjective0) (@hmissing0) (@hb2) (@hrho1Proper) (@hrho1One)
      (@hb2Missing) (@hb2TreeEdges) (@hb3EdgeEffects) (@hb4Interchange) (@terminalPosition)
      (@hterminalAt) (@hterminalPositionPositive) (@hterminalPositionBound) (@hjTreeIndex)
      (@hseedTj) (@hseedTerminal) (@hTjQ) (@hseedVertexBefore) (@segmentVertexBefore)
      (@transportSeedRoute) (@commonPrefix) (@TjPrime) (@hclosure) (@hprimeElementary)
      (@hcaseSplit) (@hseedPrime) (@hterminalPrime) (@hqLast) (@hsupport0) (@hkind0) (@hstored0)
      (@hterminalIntersection) (@hdeltaAvoidsTj) (@hb1Tj) (@hcaseOnePrepared)
theorem helper_continuation_13931.{u_1, u_2} :
    helperContinuation13931Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma
      hsigmaProper hsigmaOne w hw hwComponent hwNe this q hqTerminal hqSucc hqKind hqVertex
      hqGamma hqDelta hvStage hqTreeIndex hvFinal hfirstUpper hfirstPositive jSlot hjSlot hjle
      hsigmaTerminal hsigmaBefore segmentTrans stepSegment stageToStage vertexTransfer
      hdeltaExclusion hPESlotData hPEStored hclassPackage hterminalBefore hjInitial hslotData
      hinitialSI hclassMissing hpairOverlapColors
  obtain ⟨trace, hinvariant⟩ := ExtensionBaseAlgorithmA ett v hvFinal
    jSlot q sigma hqTerminal hqKind hqVertex hjSlot hsigmaProper hsigmaOne
    hterminalBefore hjInitial hslotData hinitialSI hclassMissing
    hpairOverlapColors
  have hterminalJ : v ∈ TreeSequenceVertexSet
      (ett.series.data.tree jSlot.succ.castSucc) := by
    exact @helper_hterminalJ_1166 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@hjSlot)
  have hqActive : q ∈ ExtensionBaseActiveIndices ett v hvFinal := by
    simp only [ExtensionBaseActiveIndices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨hfirstUpper, hqKind, v, hvFinal, hqVertex, le_rfl⟩
  have hqClass : q ∈ ExtensionBaseSupportClass ett v hvFinal v := by
    simp [ExtensionBaseSupportClass, hqActive, hqVertex]
  obtain ⟨p0, indices0, gamma0, delta0, hincreasing0, hclass0,
      hgamma0, hdelta0, hchain0, hinjective0, hunsupported, hmissing0⟩ :=
    hclassPackage v ⟨q, hqClass⟩
  have hclassPrepared : ∀ x : V,
      x ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) →
      x ≠ v →
      (∃ t : Fin ett.rounds,
        t ∈ ExtensionBaseRestorationIndices ett v hvFinal ∧
          ett.series.data.chosenVertex t.succ = some x) →
      ∃ p : ℕ, ∃ indices : Fin (p + 1) → Fin ett.rounds,
        ∃ gammaClass deltaClass : Fin (p + 1) → Fin k,
          (∀ a b, a.val < b.val →
            (indices a).val < (indices b).val) ∧
          (∀ r : Fin ett.rounds,
            r ∈ ExtensionBaseSupportClass ett v hvFinal x ↔
              ∃ a : Fin (p + 1), indices a = r) ∧
          (∀ a, ett.series.data.gamma (indices a).succ =
            some (gammaClass a)) ∧
          (∀ a, ett.series.data.delta (indices a).succ =
            some (deltaClass a)) ∧
          (∀ a : Fin p, gammaClass a.succ = deltaClass a.castSucc) ∧
          Function.Injective (Fin.cons (gammaClass 0) deltaClass) ∧
          MissingColors G (ett.series.data.coloring jSlot.castSucc) x =
            (MissingColors G sigma x \ {deltaClass (Fin.last p)}) ∪
              {gammaClass 0} := by
    exact @helper_hclassPrepared_1698 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hclassPackage)
  have hclaim43 := ExtensionBaseClaim43 ett v hvFinal jSlot q hjle
    hqTerminal hqKind hqVertex hjSlot sigma
    (TashkinovStoredColors ett.series.data jSlot.castSucc) hterminalJ
    hsigmaProper hsigmaOne hsigmaTerminal hsigmaBefore trace hinvariant
    hunsupported hclassPrepared
  dsimp at hclaim43
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hclaim43
  let rho1 : PartialEdgeColoring E k :=
    trace.coloring (Fin.last trace.steps)
  have hrho1Proper : IsProperEdgeColoring G rho1 := by
    simpa [rho1] using (hinvariant.1 (Fin.last trace.steps)).1
  have hrho1One : IsOneEdgeUncolored rho1 e0 := by
    simpa [rho1] using (hinvariant.1 (Fin.last trace.steps)).2
  have hb1Rho : StableColoringBeforeVertex T v hvFinal
      (TashkinovStoredColors ett.series.data jSlot.castSucc)
      (ett.series.data.coloring jSlot.castSucc) rho1 := by
    simpa [rho1] using hb1
  have hb2Missing :
      (∀ x : V,
        x ∈ (TreeSequenceVertexSet
            (ett.series.data.tree jSlot.succ.castSucc)).erase v →
        MissingColors G rho1 x =
          MissingColors G
            (ett.series.data.coloring jSlot.castSucc) x) ∧
      MissingColors G rho1 v = MissingColors G sigma v := by
    simpa [rho1] using hb2
  have hb2TreeEdges : ∀ a : Fin
      (ett.series.data.tree jSlot.succ.castSucc).length,
      rho1 ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
          sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧
        sigma ((ett.series.data.tree jSlot.succ.castSucc).edge a) =
          ett.series.data.coloring jSlot.castSucc
            ((ett.series.data.tree jSlot.succ.castSucc).edge a) := by
    simpa [rho1] using hb3
  have hb3EdgeEffects : ∀ f : E, rho1 f ≠ sigma f →
      f ∉ InternalEdges G
          (TreeSequenceVertexSet
            (ett.series.data.tree jSlot.succ.castSucc)) ∧
        ∃ c d : Fin k, sigma f = some c ∧ rho1 f = some d ∧
          c ∈ (ExtensionBaseRestorationIndices ett v hvFinal).biUnion
            (fun t => ett.series.data.stored t.succ) ∧
          d ∈ (ExtensionBaseRestorationIndices ett v hvFinal).biUnion
            (fun t => ett.series.data.stored t.succ) := by
    simpa [rho1] using hb4
  have hb4Interchange : ∀ (s : Fin ett.rounds)
      (gammaS deltaS : Fin k),
      s ∈ ExtensionBaseSupportClass ett v hvFinal v →
      s ≠ q →
      ett.series.data.chosenVertex s.succ = some v →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s v rho1 gammaS deltaS := by
    simpa [rho1] using hb5
  classical
  obtain ⟨terminalPosition, -, hterminalAt⟩ :=
    Finset.mem_image.mp hterminalJ
  have hterminalPositionPositive : 1 ≤ terminalPosition.val := by
    exact @helper_hterminalPositionPositive_1612 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v)
        (@hqTerminal) (@hqKind) (@hqVertex) (@hvFinal) (@hfirstUpper) (@hfirstPositive)
        (@hjSlot) (@stageToStage) (@terminalPosition) (@hterminalAt)
  have hterminalPositionBound : terminalPosition.val ≤
      (ett.series.data.tree jSlot.succ.castSucc).length :=
    Nat.le_of_lt_succ terminalPosition.isLt
  let seed : TreeSequence G e0 :=
    TreeSequencePrefix (ett.series.data.tree jSlot.succ.castSucc)
      terminalPosition.val hterminalPositionPositive hterminalPositionBound
  have hjTreeIndex : jSlot.castSucc.succ = jSlot.succ.castSucc := by
    apply Fin.ext
    rfl
  have hseedTj : TreeSequenceInitialSegment seed
      (ett.series.data.tree jSlot.succ.castSucc) := by
    exact @helper_hseedTj_2451 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalPositionPositive)
        (@hterminalPositionBound) (@hjTreeIndex)
  have hseedTerminal : seed.vertex (Fin.last seed.length) = v := by
    exact @helper_hseedTerminal_2462 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@terminalPosition) (@hterminalAt)
        (@hterminalPositionPositive) (@hterminalPositionBound)
  have hTjQ : TreeSequenceInitialSegment
      (ett.series.data.tree jSlot.succ.castSucc)
      (ett.series.data.tree q.succ.castSucc) := by
    have hseg := stageToStage (jSlot.val + 1) (q.val + 1)
      (by omega) (by omega) (by omega)
    convert hseg using 1 <;> congr 1
  have hqFinal : TreeSequenceInitialSegment
      (ett.series.data.tree q.succ.castSucc) T := by
    simpa [hqTreeIndex] using ett.abovePenultimate
  have hseedFinal : TreeSequenceInitialSegment seed T :=
    segmentTrans hseedTj (segmentTrans hTjQ hqFinal)
  have hseedVertexBefore (i : Fin (seed.length + 1))
      (hi : i.val < seed.length) :
      seed.vertex i ∈ TreeVerticesBefore T v hvFinal := by
    exact @helper_hseedVertexBefore_5540 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@vertexTransfer) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedTerminal) (@hseedFinal)
        (@i) (@hi)
  have segmentVertexBefore {A : TreeSequence G e0}
      (hAseed : TreeSequenceInitialSegment A seed)
      (hAlen : A.length < seed.length) {x : V}
      (hxA : x ∈ TreeSequenceVertexSet A) :
      x ∈ TreeVerticesBefore T v hvFinal := by
    exact @helper_segmentVertexBefore_5548 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@terminalPosition)
        (@hterminalPositionPositive) (@hterminalPositionBound) (@hseedVertexBefore) (@A)
        (@hAseed) (@hAlen) (@x) (@hxA)
  have transportStep {A B : TreeSequence G e0}
      (hstep : TashkinovAugmentation
        (ett.series.data.coloring jSlot.castSucc) A B)
      (hBseed : TreeSequenceInitialSegment B seed) :
      TashkinovAugmentation rho1 A B := by
    exact @helper_transportStep_1463 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@segmentTrans) (@trace) (@hb1Rho)
        (@terminalPosition) (@hterminalPositionPositive) (@hterminalPositionBound)
        (by assumption) (@A) (@B) (@hstep) (@hBseed)
  exact @helper_continuation_14264 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hsigmaProper) (@hsigmaOne) (@w) (@hw)
      (@hwComponent) (@hwNe) (@hqTerminal) (@hqSucc) (@hqKind) (@hqVertex) (@hqGamma) (@hqDelta)
      (@hvStage) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@hjle) (@hsigmaTerminal)
      (@segmentTrans) (@stepSegment) (@stageToStage) (@vertexTransfer) (@hdeltaExclusion)
      (@hPESlotData) (@hPEStored) (@hpairOverlapColors) (@trace) (@hterminalJ) (@hqActive)
      (@hqClass) (@p0) (@indices0) (@gamma0) (@delta0) (@hincreasing0) (@hclass0) (@hgamma0)
      (@hdelta0) (@hchain0) (@hinjective0) (@hmissing0) (@hb2) (@hrho1Proper) (@hrho1One)
      (@hb1Rho) (@hb2Missing) (@hb2TreeEdges) (@hb3EdgeEffects) (@hb4Interchange)
      (@terminalPosition) (@hterminalAt) (@hterminalPositionPositive) (@hterminalPositionBound)
      (@hjTreeIndex) (@hseedTj) (@hseedTerminal) (@hTjQ) (@hqFinal) (@hseedVertexBefore)
      (@segmentVertexBefore) (@transportStep)
theorem helper_caseContinuation_13733.{u_1, u_2} :
    helperCaseContinuation13733Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 input T generating ett hMP hpositive hlower v gamma delta sigma
      hsigmaProper hsigmaOne w hw hwComponent hwNe this q hqTerminal hqSucc hqKind hqVertex
      hqGamma hqDelta hvStage hqTreeIndex hvFinal hfirstUpper hfirstPositive jSlot hjSlot hjle
      hsigmaTerminal hsigmaBefore segmentTrans stepSegment stageToStage vertexTransfer
      hsupportOrder hdeltaExclusion hpairOverlap
  have htreeEdges := ExtensionBaseClaimTreeEdgeColors G k e0 input
    ett.rounds ett.series jSlot q hjle hqTerminal sigma hsigmaProper
    hsigmaOne hsigmaTerminal
  have hLowerInterchange : ∀ (t : Fin ett.rounds) (vt : V)
      (gammaT deltaT : Fin k),
      t ∈ ExtensionBaseActiveIndices ett v hvFinal →
      t.val < q.val →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      TreeInterchangeable G (ett.series.data.tree t.succ.succ)
        (ett.series.data.coloring t.succ) gammaT deltaT := by
    exact @helper_hLowerInterchange_328 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
        (@hlower) (@v) (@hqTerminal) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@vertexTransfer)
  have hstrongInterchange := ExtensionBaseClaimStrongInterchangeable ett v
    hvFinal q hqTerminal hqKind hqVertex hLowerInterchange sigma hsigmaProper
    hsigmaOne hsigmaTerminal
  have hPESlotData : ∀ t : Fin ett.rounds,
      ett.series.data.kind t.succ = some TashkinovExtensionKind.PE →
      ∃ vt : V, ∃ gammaT deltaT : Fin k,
        ett.series.data.chosenVertex t.succ = some vt ∧
          ett.series.data.gamma t.succ = some gammaT ∧
          ett.series.data.delta t.succ = some deltaT := by
    exact @helper_hPESlotData_805 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett)
  have hPEStored : ∀ (t : Fin ett.rounds) (gammaT deltaT : Fin k),
      ett.series.data.kind t.succ = some TashkinovExtensionKind.PE →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ett.series.data.stored t.succ = {gammaT, deltaT} := by
    exact @helper_hPEStored_851 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett)
  have qStageToFinal : ∀ x : V,
      x ∈ TreeSequenceVertexSet (ett.series.data.tree q.succ.castSucc) →
      x ∈ TreeSequenceVertexSet T := by
    exact @helper_qStageToFinal_2202 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
        (@hqTreeIndex) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@vertexTransfer)
  have hclassPackage : ∀ u : V,
      (ExtensionBaseSupportClass ett v hvFinal u).Nonempty →
      ∃ p : ℕ, ∃ indices : Fin (p + 1) → Fin ett.rounds,
        ∃ gammaClass deltaClass : Fin (p + 1) → Fin k,
          (∀ a b, a.val < b.val →
            (indices a).val < (indices b).val) ∧
          (∀ r : Fin ett.rounds,
            r ∈ ExtensionBaseSupportClass ett v hvFinal u ↔
              ∃ a : Fin (p + 1), indices a = r) ∧
          (∀ a, ett.series.data.gamma (indices a).succ =
            some (gammaClass a)) ∧
          (∀ a, ett.series.data.delta (indices a).succ =
            some (deltaClass a)) ∧
          (∀ a : Fin p, gammaClass a.succ = deltaClass a.castSucc) ∧
          Function.Injective (Fin.cons (gammaClass 0) deltaClass) ∧
          (∀ x : V,
            x ∈ TreeSequenceVertexSet
                (ett.series.data.tree jSlot.succ.castSucc) →
            (∀ r : Fin ett.rounds,
              r ∈ ExtensionBaseActiveIndices ett v hvFinal →
              ett.series.data.chosenVertex r.succ ≠ some x) →
            MissingColors G sigma x =
              MissingColors G
                (ett.series.data.coloring jSlot.castSucc) x) ∧
          (let storedPairs := Finset.univ.biUnion fun a : Fin (p + 1) =>
              ett.series.data.stored (indices a).succ
           MissingColors G sigma u ∩ storedPairs =
                {deltaClass (Fin.last p)} ∧
             MissingColors G (ett.series.data.coloring jSlot.castSucc) u =
               (MissingColors G sigma u \ {deltaClass (Fin.last p)}) ∪
                 {gammaClass 0}) := by
    intro u hclassNonempty
    obtain ⟨p, indices, huStage, hincreasing, hclass, henumerates⟩ :=
      ExtensionBaseSupportClassEnumeration ett v hvFinal q hqTerminal u
        (fun s x hxFinal hsActive hsChosen =>
          (hsupportOrder.2.1 s x hxFinal hsActive hsChosen).1)
        hclassNonempty
    have hslot : ∀ a : Fin (p + 1), ∃ gammaA deltaA : Fin k,
        ett.series.data.gamma (indices a).succ = some gammaA ∧
          ett.series.data.delta (indices a).succ = some deltaA := by
      exact @helper_hslot_2247 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
          (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@hPESlotData) (@u) (@p)
          (@indices) (@henumerates)
    choose gammaClass deltaClass hgammaClass hdeltaClass using hslot
    have huFinal := qStageToFinal u huStage
    have hdeltaAvoids : ∀ a b, a.val ≤ b.val →
        deltaClass b ≠ gammaClass a := by
      exact @helper_hdeltaAvoids_5315 (@V) (@E) inferInstance inferInstance inferInstance (@G)
          (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal)
          (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hdeltaExclusion) (@u) (@p) (@indices)
          (@hincreasing) (@hclass) (@gammaClass) (@deltaClass) (@hgammaClass) (@hdeltaClass)
          (@huFinal)
    obtain ⟨hchain, hinjective⟩ := ExtensionBaseSupportClassColors ett v
      hvFinal q hqTerminal u huStage p indices hincreasing hclass henumerates
      gammaClass deltaClass hgammaClass hdeltaClass hdeltaAvoids
    have hmissing := ExtensionBaseClaimMissingColors ett v hvFinal jSlot q
      hjle hqTerminal hqKind hqVertex hjSlot u huStage p indices hincreasing
      hclass henumerates (gammaClass 0) (deltaClass (Fin.last p))
      (hgammaClass 0) (hdeltaClass (Fin.last p)) sigma hsigmaProper
      hsigmaOne hsigmaTerminal
    exact ⟨p, indices, gammaClass, deltaClass, hincreasing, hclass,
      hgammaClass, hdeltaClass, hchain, hinjective, hmissing⟩
  have hterminalBefore : ∀ (t : Fin ett.rounds) (vt : V),
      t ∈ ExtensionBaseRestorationIndices ett v hvFinal →
      ett.series.data.chosenVertex t.succ = some vt →
      TreeVertexOrder T v vt := by
    exact @helper_hterminalBefore_988 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@v) (@hvFinal) (@hsupportOrder)
  have hjInitial : ∀ t : Fin ett.rounds,
      t ∈ ExtensionBaseRestorationIndices ett v hvFinal →
      TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree t.succ.castSucc) := by
    exact @helper_hjInitial_1603 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@hqTerminal) (@hvFinal)
        (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@stageToStage)
  have hslotData : ∀ t : Fin ett.rounds,
      t ∈ ExtensionBaseRestorationIndices ett v hvFinal →
      ∃ vt : V, ∃ gammaT deltaT : Fin k,
        ett.series.data.chosenVertex t.succ = some vt ∧
          ett.series.data.gamma t.succ = some gammaT ∧
          ett.series.data.delta t.succ = some deltaT := by
    exact @helper_hslotData_2282 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@v) (@hvFinal) (@hPESlotData)
  have hinitialSI : ∀ (t : Fin ett.rounds) (vt : V)
      (gammaT deltaT : Fin k),
      t ∈ ExtensionBaseActiveIndices ett v hvFinal →
      t ≠ q →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ETTStrongInterchangeable ett t vt sigma gammaT deltaT := by
    exact @helper_hinitialSI_2295 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hstrongInterchange)
  have hclassMissing : ∀ (u : V) (t : Fin ett.rounds)
      (deltaT : Fin k),
      ExtensionBaseSupportClass ett v hvFinal u ⊆
          ExtensionBaseRestorationIndices ett v hvFinal →
      t ∈ ExtensionBaseSupportClass ett v hvFinal u →
      (∀ s : Fin ett.rounds,
        s ∈ ExtensionBaseSupportClass ett v hvFinal u → s.val ≤ t.val) →
      ett.series.data.delta t.succ = some deltaT →
      MissingColors G sigma u ∩
          (ExtensionBaseSupportClass ett v hvFinal u).biUnion
            (fun s => ett.series.data.stored s.succ) = {deltaT} := by
    exact @helper_hclassMissing_1053 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hpositive) (@v) (@sigma) (@hqTerminal)
        (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hclassPackage)
  have hpairOverlapColors : ∀ (s t : Fin ett.rounds) (vs vt : V)
      (gammaS deltaS gammaT deltaT : Fin k),
      s ∈ ExtensionBaseActiveIndices ett v hvFinal →
      t ∈ ExtensionBaseActiveIndices ett v hvFinal →
      s.val < t.val →
      ett.series.data.chosenVertex s.succ = some vs →
      ett.series.data.chosenVertex t.succ = some vt →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ett.series.data.gamma t.succ = some gammaT →
      ett.series.data.delta t.succ = some deltaT →
      ((({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT}).Nonempty ↔
        vs = vt ∧ ¬ ∃ r : Fin ett.rounds,
          r ∈ ExtensionBaseSupportClass ett v hvFinal vs ∧
            s.val < r.val ∧ r.val < t.val ∧
            ett.series.data.chosenVertex r.succ = some vs) ∧
      ((({gammaS, deltaS} : Finset (Fin k)) ∩
          {gammaT, deltaT}).Nonempty →
        ({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT} =
            {gammaT} ∧
          ({gammaS, deltaS} : Finset (Fin k)) ∩ {gammaT, deltaT} =
            {deltaS}) := by
    exact @helper_hpairOverlapColors_581 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@v) (@hvFinal) (@hpairOverlap)
        (@hPEStored)
  exact @helper_continuation_13931 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@input) (@T) (@generating) (@ett) (@hMP) (@hpositive)
      (@hlower) (@v) (@gamma) (@delta) (@sigma) (@hsigmaProper) (@hsigmaOne) (@w) (@hw)
      (@hwComponent) (@hwNe) (@hqTerminal) (@hqSucc) (@hqKind) (@hqVertex) (@hqGamma) (@hqDelta)
      (@hvStage) (@hqTreeIndex) (@hvFinal) (@hfirstUpper) (@hfirstPositive) (@hjSlot) (@hjle)
      (@hsigmaTerminal) (@hsigmaBefore) (@segmentTrans) (@stepSegment) (@stageToStage)
      (@vertexTransfer) (@hdeltaExclusion) (@hPESlotData) (@hPEStored) (@hclassPackage)
      (@hterminalBefore) (@hjInitial) (@hslotData) (@hinitialSI) (@hclassMissing)
      (@hpairOverlapColors)

end GoldbergSeymour.ExtensionBaseProof

end
