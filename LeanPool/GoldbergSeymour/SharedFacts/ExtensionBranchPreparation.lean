/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

import all LeanPool.GoldbergSeymour.ExtensionBaseAuxiliary
public import LeanPool.GoldbergSeymour.ExtensionBaseRestorationTrace
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TreeVerticesBefore

/-!
# Shared facts for ExtensionBaseBranchPreparation

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ExtensionBranchPreparation

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hbeforePrimeNeUStatement.{u_1, u_2} : Prop :=
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
          TreeSequenceInitialSegment seed (ett.series.data.tree jSlot.succ.castSucc) →
      ∀ (TjPrime : TreeSequence G e0),
      let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gamma delta;
      ∀ (x : V) (_ : H.Walk (Sum.inl v) (Sum.inl x)) (u : V) (_ : (TwoColorIncidenceGraph G rho1
          gamma delta).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin ((ett.series.data.tree
          jSlot.succ.castSucc).length + (1 : ℕ))) (u0 : V) (huPrime0 : u0 ∈ TreeSequenceVertexSet
          TjPrime) (_ : (TwoColorIncidenceGraph G rho1 gamma delta).Walk (Sum.inl x) (Sum.inl u0))
          (_ : Fin ((ett.series.data.tree jSlot.succ.castSucc).length + (1 : ℕ))) (_ : Fin
          (TjPrime.length + (1 : ℕ))) {y : V}, y ∈ TreeVerticesBefore TjPrime u0 huPrime0 → y ≠ u0

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hbeforePrimeMissingStatement.{u_1, u_2} : Prop :=
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
          u0).erase z0, MissingColors G rho3 y = MissingColors G rho1 y) → (z0 ∈ TreeVerticesBefore
          TjPrime u0 huPrime0 → MissingColors G rho3 z0 = MissingColors G rho1 z0) → (
      ∀ {y : V}, y ∈ TreeVerticesBefore TjPrime u0 huPrime0 → y ≠ u0) →
      ∀ y ∈ TreeVerticesBefore TjPrime u0 huPrime0, MissingColors G rho3 y = MissingColors G rho1 y

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev transportURouteStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (T :
          TreeSequence G e0) (generating : PartialEdgeColoring E k) (ett : ExtendedTashkinovTree G k
          e0 input T generating) (v : V) (sigma : PartialEdgeColoring E k) (hvFinal : v ∈
          TreeSequenceVertexSet T) (trace : ExtensionBaseRestorationTrace ett v hvFinal sigma),
      let rho1 : PartialEdgeColoring E k := trace.coloring (Fin.last trace.steps);
      ∀ (TjPrime : TreeSequence G e0) (rho3 : PartialEdgeColoring E k) (uPosition : Fin
          (TjPrime.length + (1 : ℕ))) (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
          (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
      let U : TreeSequence G e0 := TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive
          huPositionBound; (
      ∀ {A B : TreeSequence G e0}, TashkinovAugmentation rho1 A B → TreeSequenceInitialSegment B U →
          TashkinovAugmentation rho3 A B) →
      ∀ (S : TreeSequence G e0), TashkinovAugmentationSequence rho1 S U →
          TashkinovAugmentationSequence rho3 S U

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev huUStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
        (TjPrime : TreeSequence G e0) (u0 : V) (uPosition : Fin (TjPrime.length + (1 : ℕ))),
      TjPrime.vertex uPosition = u0 →
      ∀ (huPositionPositive : (1 : ℕ) ≤ (↑uPosition : ℕ))
        (huPositionBound : (↑uPosition : ℕ) ≤ TjPrime.length),
      let U : TreeSequence G e0 :=
        TreeSequencePrefix TjPrime (↑uPosition : ℕ) huPositionPositive huPositionBound;
      u0 ∈ TreeSequenceVertexSet U

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hbeforePrimeNeU.{u_1, u_2} : hbeforePrimeNeUStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v gamma delta sigma q hqTerminal
      hvFinal hfirstUpper hfirstPositive jSlot trace p0 indices0 gamma0 delta0 rho1
      terminalPosition hterminalPositionPositive hterminalPositionBound seed hseedTj TjPrime H x
      componentPath u exitPath zPosition u0 huPrime0 exitPath0 zPosition0 uPosition y hy
  unfold TreeVerticesBefore at hy
  obtain ⟨-, i, j, hiy, hju, hij⟩ := Finset.mem_filter.mp hy
  intro hyu
  have hijEq : i = j := TjPrime.vertex_injective
    (hiy.trans (hyu.trans hju.symm))
  omega

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hbeforePrimeMissing.{u_1, u_2} : hbeforePrimeMissingStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett hpositive v sigma this q hqTerminal hvFinal
      hfirstUpper hfirstPositive jSlot trace rho1 TjPrime u0 huPrime0 z0 hz0 rho3 hd2Missing hd2z
      hbeforePrimeNeU y hy
  by_cases hyz : y = z0
  · subst y
    exact hd2z hy
  · apply hd2Missing y
    apply Finset.mem_erase.mpr
    refine ⟨hyz, Finset.mem_erase.mpr ⟨hbeforePrimeNeU hy, ?_⟩⟩
    exact Finset.mem_union_right _ (Finset.mem_union_left _ hy)

/-- A common proof used by the branches of this transport or construction argument. -/
theorem transportURoute.{u_1, u_2} : transportURouteStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 input T generating ett v sigma hvFinal trace rho1 TjPrime rho3 uPosition
      huPositionPositive huPositionBound U transportUStep S hroute
  unfold TashkinovAugmentationSequence at hroute ⊢
  induction hroute using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head A B hAB hBU ih =>
      have hBsegment : TreeSequenceInitialSegment B U :=
        TashkinovAugmentationSequenceInitialSegment rho1 B U hBU
      exact Relation.ReflTransGen.head
        (transportUStep hAB hBsegment) ih

/-- A common proof used by the branches of this transport or construction argument. -/
theorem huU.{u_1, u_2} : huUStatement.{u_1, u_2} := by
  classical
  intro V E G e0 TjPrime u0 uPosition huPosition huPositionPositive huPositionBound U
  simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  refine ⟨Fin.last U.length, ?_⟩
  change TjPrime.vertex (Fin.castLE (Nat.succ_le_succ huPositionBound)
    (Fin.last uPosition.val)) = u0
  have hindex : Fin.castLE (Nat.succ_le_succ huPositionBound)
      (Fin.last uPosition.val) = uPosition := by
    apply Fin.ext
    rfl
  rw [hindex]
  exact huPosition

end GoldbergSeymour.SharedFacts.ExtensionBranchPreparation

end
