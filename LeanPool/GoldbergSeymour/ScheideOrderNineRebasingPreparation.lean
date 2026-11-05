/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.BalancedGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed
public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.LooplessMultigraph
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.NormalGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.ScheideOrderNineBlockCompletion
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideHeightFiveGammaEdges
public import LeanPool.GoldbergSeymour.ScheideHeightFiveOutsideLinks
public import LeanPool.GoldbergSeymour.ScheideKempePathHeightBound
public import LeanPool.GoldbergSeymour.ScheideTrunkRotationColoring
public import LeanPool.GoldbergSeymour.ScheideTrunkRotationCycle
public import LeanPool.GoldbergSeymour.ScheideTrunkRotationNormal
public import LeanPool.GoldbergSeymour.ScheideTrunkRotationPreserves
public import LeanPool.GoldbergSeymour.ScheideTrunkRotationTree
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TrunkRotation
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import Mathlib.Tactic.FinCases

/-!
# Scheide Order Nine Block Structure

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour.ScheideRebasing

open scoped Sym2

/-- Dependent contract shared by the order-nine tree rebasing proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation995Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T), ScheideGraphHeight G = (5 : ℕ) →
    let this : DecidableEq V := Classical.decEq V;
    let Good : {e : E} → (psi : PartialEdgeColoring E k) → (S : TreeSequence G e) →
        NormalGlobalMaximumTriple G k e psi S → Prop := fun {e : E} (psi : PartialEdgeColoring E
        k) (S : TreeSequence G e) (M : NormalGlobalMaximumTriple G k e psi S) ↦
    ∃ (_ : BalancedGlobalMaximumTriple M) (x : S.length = (8 : ℕ)) (_ : M.height = (5 : ℕ)) (gamma
        : Fin (2 : ℕ) → Fin k), Function.Injective gamma ∧ (
    ∀ (i j : Fin (2 : ℕ)),
    ∃ (q : Fin (5 : ℕ)), G.ends (S.edge (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    by
             have := GoldbergSeymour.TreeSequence.positive S
             omega
    ⟩ : Fin S.length)) = s(S.vertex (⟨(↑q : ℕ),
    by
             have := GoldbergSeymour.TreeSequence.positive S
             omega
    ⟩ : Fin (S.length + (1 : ℕ))), S.vertex (⟨(5 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    by
             have := GoldbergSeymour.TreeSequence.positive S
             omega
    ⟩ : Fin (S.length + (1 : ℕ))))) ∧ (
    ∀ (i j : Fin (2 : ℕ)), psi (S.edge (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    by
             have := GoldbergSeymour.TreeSequence.positive S
             omega
    ⟩ : Fin S.length)) = some (gamma i)) ∧ (
    ∀ (i : Fin (2 : ℕ)),
    ∃ (q : Fin (5 : ℕ)), gamma i ∈ MissingColors G psi (S.vertex (⟨(↑q : ℕ),
    by
               have := GoldbergSeymour.TreeSequence.positive S
               omega
    ⟩ : Fin (S.length + (1 : ℕ))))) ∧
    ∀ (i : Fin (4 : ℕ)), (1 : ℕ) ≤ (↑i : ℕ) →
    ∀ (c : Fin k), psi (S.edge (⟨(↑i : ℕ),
    by
                 have := GoldbergSeymour.TreeSequence.positive S
                 omega
    ⟩ : Fin S.length)) = some c →
    ∀ (r : Fin (2 : ℕ)), c ≠ gamma r;
    ∀ {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence G e) (M :
        NormalGlobalMaximumTriple G k e psi S), BalancedGlobalMaximumTriple M →
    ∀ (hlen : S.length = (8 : ℕ)) (hheight : M.height = (5 : ℕ)) (g0 : Fin k),
        IsProperEdgeColoring G psi → TashkinovOrder G = (TreeSequenceVertexSet S).card ∧ (3 : ℕ) ≤
        (TreeSequenceVertexSet S).card ∧ Odd (TreeSequenceVertexSet S).card ∧
        ColoredVertexSetElementary G psi (TreeSequenceVertexSet S) ∧ ColoredVertexSetClosed G psi
        (TreeSequenceVertexSet S) → ColoredVertexSetElementary G psi (TreeSequenceVertexSet S) →
        ColoredVertexSetClosed G psi (TreeSequenceVertexSet S) →
    let y0 : V := S.vertex (⟨(0 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y1 : V := S.vertex (⟨(1 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y2 : V := S.vertex (⟨(2 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y3 : V := S.vertex (⟨(3 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y4 : V := S.vertex (⟨(4 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y5 : V := S.vertex (⟨(5 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y6 : V := S.vertex (⟨(6 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y7 : V := S.vertex (⟨(7 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y8 : V := S.vertex (⟨(8 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let a1 : E := S.edge (⟨(1 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin S.length);
    let a2 : E := S.edge (⟨(2 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin S.length);
    let a3 : E := S.edge (⟨(3 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin S.length);
    let b0 : E := S.edge (⟨(4 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin S.length);
    let b1 : E := S.edge (⟨(5 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin S.length);
    let c0 : E := S.edge (⟨(6 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin S.length);
    let c1 : E := S.edge (⟨(7 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin S.length); (
    ∀ {i j : Fin (S.length + (1 : ℕ))}, i ≠ j → S.vertex i ≠ S.vertex j) → (
    ∀ {i j : Fin S.length}, i ≠ j → S.edge i ≠ S.edge j) → (
    ∀ (i : Fin (S.length + (1 : ℕ))), S.vertex i ∈ TreeSequenceVertexSet S) → (
    ∀ {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G psi v → Incident G v f → psi f ≠ some c) →
        psi b0 = some g0 → psi b1 = some g0 → g0 ∈ MissingColors G psi y0 →
    ∀ (p0 : Fin ((↑(⟨(4 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive S
          omega
    ⟩ : Fin S.length) : ℕ) + (1 : ℕ))), G.ends b0 = s(y5, S.vertex (p0.castLT (
    by
        have := GoldbergSeymour.TreeSequence.positive S
        omega
    ))) →
    ∀ (p1 : Fin ((↑(⟨(5 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive S
          omega
    ⟩ : Fin S.length) : ℕ) + (1 : ℕ))), G.ends b1 = s(y6, S.vertex (p1.castLT (
    by
        have := GoldbergSeymour.TreeSequence.positive S
        omega
    ))) → (↑p1 : ℕ) ≠ (5 : ℕ) →
    ∀ (f1 f2 f3 : E) (v1 v2 : V), G.ends f1 = s(S.vertex (⟨(1 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive S
        omega
    ⟩ : Fin (S.length + (1 : ℕ))), v1) → G.ends f2 = s(S.vertex (⟨(4 : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive S
        omega
    ⟩ : Fin (S.length + (1 : ℕ))), v2) → psi f1 = some g0 → psi f2 = some g0 → psi f3 = some g0 →
        v1 ∈ TreeSequenceVertexSet S → v2 ∈ TreeSequenceVertexSet S → v1 ≠ S.vertex (⟨(0 : ℕ),
    by
       have := GoldbergSeymour.TreeSequence.positive S
       omega
    ⟩ : Fin (S.length + (1 : ℕ))) → v1 ≠ S.vertex (⟨(1 : ℕ),
    by
       have := GoldbergSeymour.TreeSequence.positive S
       omega
    ⟩ : Fin (S.length + (1 : ℕ))) → v1 ≠ S.vertex (⟨(2 : ℕ),
    by
       have := GoldbergSeymour.TreeSequence.positive S
       omega
    ⟩ : Fin (S.length + (1 : ℕ))) → v1 ≠ S.vertex (⟨(3 : ℕ),
    by
       have := GoldbergSeymour.TreeSequence.positive S
       omega
    ⟩ : Fin (S.length + (1 : ℕ))) → v1 ≠ S.vertex (⟨(4 : ℕ),
    by
       have := GoldbergSeymour.TreeSequence.positive S
       omega
    ⟩ : Fin (S.length + (1 : ℕ))) → v2 ≠ S.vertex (⟨(0 : ℕ),
    by
       have := GoldbergSeymour.TreeSequence.positive S
       omega
    ⟩ : Fin (S.length + (1 : ℕ))) → v2 ≠ S.vertex (⟨(1 : ℕ),
    by
       have := GoldbergSeymour.TreeSequence.positive S
       omega
    ⟩ : Fin (S.length + (1 : ℕ))) → v2 ≠ S.vertex (⟨(2 : ℕ),
    by
       have := GoldbergSeymour.TreeSequence.positive S
       omega
    ⟩ : Fin (S.length + (1 : ℕ))) → v2 ≠ S.vertex (⟨(3 : ℕ),
    by
       have := GoldbergSeymour.TreeSequence.positive S
       omega
    ⟩ : Fin (S.length + (1 : ℕ))) → v2 ≠ S.vertex (⟨(4 : ℕ),
    by
       have := GoldbergSeymour.TreeSequence.positive S
       omega
    ⟩ : Fin (S.length + (1 : ℕ))) → G.ends f1 = s(y1, v1) → G.ends f2 = s(y4, v2) → G.ends f3 =
        s(y2, y3) → (
    ∀ (j : Fin (2 : ℕ)), S.edge (⟨(4 : ℕ) + (↑j : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive S
          omega
    ⟩ : Fin S.length) = f1 ∧ S.vertex (⟨(5 : ℕ) + (↑j : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive S
          omega
    ⟩ : Fin (S.length + (1 : ℕ))) = v1 ∨ S.edge (⟨(4 : ℕ) + (↑j : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive S
          omega
    ⟩ : Fin S.length) = f2 ∧ S.vertex (⟨(5 : ℕ) + (↑j : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive S
          omega
    ⟩ : Fin (S.length + (1 : ℕ))) = v2) →
    ∃ (e' : E) (psi' : PartialEdgeColoring E k) (S' : TreeSequence G e') (M' :
        NormalGlobalMaximumTriple G k e' psi' S'), Good psi' S' M'

/-- Dependent contract shared by the order-nine tree rebasing proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation1474Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T), ScheideGraphHeight G = (5 : ℕ) →
    let Good : {e : E} → (psi : PartialEdgeColoring E k) → (S : TreeSequence G e) →
        NormalGlobalMaximumTriple G k e psi S → Prop := fun {e : E} (psi : PartialEdgeColoring E
        k) (S : TreeSequence G e) (M : NormalGlobalMaximumTriple G k e psi S) ↦
    ∃ (_ : BalancedGlobalMaximumTriple M) (x : S.length = (8 : ℕ)) (_ : M.height = (5 : ℕ)) (gamma
        : Fin (2 : ℕ) → Fin k), Function.Injective gamma ∧ (
    ∀ (i j : Fin (2 : ℕ)),
    ∃ (q : Fin (5 : ℕ)), G.ends (S.edge (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) + (2
        : ℕ) * (↑i : ℕ) + (↑j : ℕ) < S.length) ↦
    by omega
    ⟩ : Fin S.length)) = s(S.vertex (⟨(↑q : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(↑q : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))), S.vertex (⟨(5 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) + (2
        : ℕ) * (↑i : ℕ) + (↑j : ℕ) < S.length + (1 : ℕ)) ↦
    by
              omega
    ⟩ : Fin (S.length + (1 : ℕ))))) ∧ (
    ∀ (i j : Fin (2 : ℕ)), psi (S.edge (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) + (2
        : ℕ) * (↑i : ℕ) + (↑j : ℕ) < S.length) ↦
    by omega
    ⟩ : Fin S.length)) = some (gamma i)) ∧ (
    ∀ (i : Fin (2 : ℕ)),
    ∃ (q : Fin (5 : ℕ)), gamma i ∈ MissingColors G psi (S.vertex (⟨(↑q : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(↑q : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))))) ∧
    ∀ (i : Fin (4 : ℕ)), (1 : ℕ) ≤ (↑i : ℕ) →
    ∀ (c : Fin k), psi (S.edge (⟨(↑i : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(↑i : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length)) = some c →
    ∀ (r : Fin (2 : ℕ)), c ≠ gamma r;
    ∀ {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence G e) (M :
        NormalGlobalMaximumTriple G k e psi S), BalancedGlobalMaximumTriple M →
    ∀ (hlen : S.length = (8 : ℕ)), M.height = (5 : ℕ) →
    ∀ (g0 : Fin k), IsProperEdgeColoring G psi → TashkinovOrder G = (TreeSequenceVertexSet S).card
        ∧ (3 : ℕ) ≤ (TreeSequenceVertexSet S).card ∧ Odd (TreeSequenceVertexSet S).card ∧
        ColoredVertexSetElementary G psi (TreeSequenceVertexSet S) ∧ ColoredVertexSetClosed G psi
        (TreeSequenceVertexSet S) → ColoredVertexSetElementary G psi (TreeSequenceVertexSet S) →
        ColoredVertexSetClosed G psi (TreeSequenceVertexSet S) →
    let y0 : V := S.vertex (⟨(0 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y1 : V := S.vertex (⟨(1 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y2 : V := S.vertex (⟨(2 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(2 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y3 : V := S.vertex (⟨(3 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y4 : V := S.vertex (⟨(4 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y5 : V := S.vertex (⟨(5 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y6 : V := S.vertex (⟨(6 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y7 : V := S.vertex (⟨(7 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(7 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y8 : V := S.vertex (⟨(8 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(8 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let a1 : E := S.edge (⟨(1 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let a2 : E := S.edge (⟨(2 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(2 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let a3 : E := S.edge (⟨(3 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let b0 : E := S.edge (⟨(4 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let b1 : E := S.edge (⟨(5 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let c0 : E := S.edge (⟨(6 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let c1 : E := S.edge (⟨(7 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(7 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length); (
    ∀ {i j : Fin (S.length + (1 : ℕ))}, i ≠ j → S.vertex i ≠ S.vertex j) → (
    ∀ {i j : Fin S.length}, i ≠ j → S.edge i ≠ S.edge j) → (
    ∀ (i : Fin (S.length + (1 : ℕ))), S.vertex i ∈ TreeSequenceVertexSet S) → (
    ∀ {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G psi v → Incident G v f → psi f ≠ some c) →
        psi b0 = some g0 → psi b1 = some g0 → g0 ∈ MissingColors G psi y0 →
    ∀ (p0 : Fin ((↑(⟨(4 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length) : ℕ) + (1 : ℕ))), G.ends b0 = s(y5, S.vertex (p0.castLT (
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(↑p0 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
        omega
    ))) →
    ∀ (p1 : Fin ((↑(⟨(5 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length) : ℕ) + (1 : ℕ))), G.ends b1 = s(y6, S.vertex (p1.castLT (
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(↑p1 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
        omega
    ))) → (↑p1 : ℕ) ≠ (5 : ℕ) →
    ∀ (f1 f2 f3 : E) (v1 v2 : V), psi f1 = some g0 → psi f2 = some g0 → psi f3 = some g0 → v1 ≠
        S.vertex (⟨(0 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))) → v1 ≠ S.vertex (⟨(4 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))) → G.ends f1 = s(y1, v1) → G.ends f2 = s(y4, v2) → G.ends f3 =
        s(y2, y3) → b0 ≠ b1 → b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2 ∨ b0 = f2 ∧ y5 = v2 ∧ b1 = f1
        ∧ y6 = v1 →
    ∀ (alpha56 beta56 : E), psi alpha56 = some M.alpha → G.ends beta56 = s(v1, v2) → psi beta56 =
        some M.beta → G.ends alpha56 = s(y5, y6) → G.ends beta56 = s(y5, y6) → G.ends a1 = s(y1,
        y2) → G.ends a2 = s(y2, y3) → G.ends a3 = s(y3, y4) → G.ends M.closingEdge = s(y4, y0) →
        psi a1 = some M.alpha → psi a2 = some M.beta → psi a3 = some M.alpha → psi M.closingEdge =
        some M.beta → M.alpha ≠ M.beta → g0 ≠ M.alpha → g0 ≠ M.beta →
    let r6' : Fin S.length := (⟨(6 : ℕ),
    by
     have :=
      GoldbergSeymour.TreeSequence.positive S
     have :=
      GoldbergSeymour.TreeSequence.positive S
     omega
    ⟩ : Fin S.length);
    let r7' : Fin S.length := (⟨(7 : ℕ),
    by
     have :=
      GoldbergSeymour.TreeSequence.positive S
     have :=
      GoldbergSeymour.TreeSequence.positive S
     omega
    ⟩ : Fin S.length);
    ∀ (w : Fin ((↑r6' : ℕ) + (1 : ℕ))) (g1 : Fin k), psi c1 = some g1 → psi c0 = some g1 → g1 ∈
        MissingColors G psi (S.vertex (⟨(↑w : ℕ),
    by
        have :=
         GoldbergSeymour.TreeSequence.positive
          S
        have := Fin.isLt r6'
        have := Fin.isLt w
        have :=
         GoldbergSeymour.TreeSequence.positive
          S
        omega
    ⟩ : Fin (S.length + (1 : ℕ)))) →
    ∀ (pc : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let pc' : Fin (7 : ℕ) := (⟨(↑pc : ℕ),
    by
     have := Fin.isLt pc
     omega
    ⟩ : Fin (7 : ℕ)); G.ends c0 = s(y7, S.vertex (⟨(↑pc' : ℕ),
    by
        have :=
         GoldbergSeymour.TreeSequence.positive
          S
        have := Fin.isLt r6'
        have := Fin.isLt pc
        have := Fin.isLt pc'
        have :=
         GoldbergSeymour.TreeSequence.positive
          S
        omega
    ⟩ : Fin (S.length + (1 : ℕ)))) → c0 ≠ f3 → c0 ≠ alpha56 → c0 ≠ beta56 → c0 ≠ M.closingEdge → (
    ∀ {f : E} {u v : V}, G.ends f = s(u, v) → u ≠ y7 → v ≠ y7 → ¬Incident G y7 f) → y0 ≠ y7 → y1 ≠
        y7 → y2 ≠ y7 → y3 ≠ y7 → y4 ≠ y7 → y5 ≠ y7 → y6 ≠ y7 → v1 ≠ y7 → v2 ≠ y7 →
    ∃ (e' : E) (psi' : PartialEdgeColoring E k) (S' : TreeSequence G e') (M' :
        NormalGlobalMaximumTriple G k e' psi' S'), Good psi' S' M'

/-- Dependent contract shared by the order-nine tree rebasing proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperContinuation2887Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ), ScheideGraphHeight G = (5 : ℕ) →
    let Good : {e : E} → (psi : PartialEdgeColoring E k) → (S : TreeSequence G e) →
        NormalGlobalMaximumTriple G k e psi S → Prop := fun {e : E} (psi : PartialEdgeColoring E
        k) (S : TreeSequence G e) (M : NormalGlobalMaximumTriple G k e psi S) ↦
    ∃ (_ : BalancedGlobalMaximumTriple M) (x : S.length = (8 : ℕ)) (_ : M.height = (5 : ℕ)) (gamma
        : Fin (2 : ℕ) → Fin k), Function.Injective gamma ∧ (
    ∀ (i j : Fin (2 : ℕ)),
    ∃ (q : Fin (5 : ℕ)), G.ends (S.edge (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (↑i : ℕ) < (2 : ℕ) := i.isLt;
    have this_1 : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have this_2 : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) +
        (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ) < S.length) ↦
    by omega
    ⟩ : Fin S.length)) = s(S.vertex (⟨(↑q : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (↑q : ℕ) < (5 : ℕ) := q.isLt;
    have this_1 : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(↑q : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))), S.vertex (⟨(5 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (↑i : ℕ) < (2 : ℕ) := i.isLt;
    have this_1 : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have this_2 : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) +
        (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ) < S.length + (1 : ℕ)) ↦
    by
              omega
    ⟩ : Fin (S.length + (1 : ℕ))))) ∧ (
    ∀ (i j : Fin (2 : ℕ)), psi (S.edge (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (↑i : ℕ) < (2 : ℕ) := i.isLt;
    have this_1 : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have this_2 : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) +
        (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ) < S.length) ↦
    by omega
    ⟩ : Fin S.length)) = some (gamma i)) ∧ (
    ∀ (i : Fin (2 : ℕ)),
    ∃ (q : Fin (5 : ℕ)), gamma i ∈ MissingColors G psi (S.vertex (⟨(↑q : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (↑q : ℕ) < (5 : ℕ) := q.isLt;
    have this_1 : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(↑q : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))))) ∧
    ∀ (i : Fin (4 : ℕ)), (1 : ℕ) ≤ (↑i : ℕ) →
    ∀ (c : Fin k), psi (S.edge (⟨(↑i : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (↑i : ℕ) < (4 : ℕ) := i.isLt;
    have this_1 : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(↑i : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length)) = some c →
    ∀ (r : Fin (2 : ℕ)), c ≠ gamma r;
    ∀ {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence G e) (M :
        NormalGlobalMaximumTriple G k e psi S), BalancedGlobalMaximumTriple M →
    ∀ (hlen : S.length = (8 : ℕ)), M.height = (5 : ℕ) →
    ∀ (g0 : Fin k),
    let y0 : V := S.vertex (⟨(0 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y1 : V := S.vertex (⟨(1 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y2 : V := S.vertex (⟨(2 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(2 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y3 : V := S.vertex (⟨(3 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y4 : V := S.vertex (⟨(4 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y5 : V := S.vertex (⟨(5 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y6 : V := S.vertex (⟨(6 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y7 : V := S.vertex (⟨(7 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(7 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y8 : V := S.vertex (⟨(8 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(8 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let a1 : E := S.edge (⟨(1 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let a2 : E := S.edge (⟨(2 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(2 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let a3 : E := S.edge (⟨(3 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let b0 : E := S.edge (⟨(4 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let b1 : E := S.edge (⟨(5 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let c0 : E := S.edge (⟨(6 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let c1 : E := S.edge (⟨(7 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(7 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length); g0 ∈ MissingColors G psi y0 →
    ∀ (f1 f2 : E) (v1 v2 : V), psi f1 = some g0 → psi f2 = some g0 → G.ends f1 = s(y1, v1) →
        G.ends f2 = s(y4, v2) → b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2 ∨ b0 = f2 ∧ y5 = v2 ∧ b1 =
        f1 ∧ y6 = v1 →
    ∀ (beta56 : E), G.ends beta56 = s(v1, v2) → psi beta56 = some M.beta → G.ends a1 = s(y1, y2) →
        G.ends a2 = s(y2, y3) → G.ends a3 = s(y3, y4) → psi a1 = some M.alpha → psi a2 = some
        M.beta → psi a3 = some M.alpha → M.alpha ≠ M.beta → g0 ≠ M.alpha → g0 ≠ M.beta →
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    by
     have := GoldbergSeymour.TreeSequence.positive S
     have := GoldbergSeymour.TreeSequence.positive S
     omega
    ⟩ : Fin S.length);
    ∀ (w : Fin ((↑r6' : ℕ) + (1 : ℕ))) (g1 : Fin k), psi c1 = some g1 → psi c0 = some g1 → g1 ∈
        MissingColors G psi (S.vertex (⟨(↑w : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (↑r6' : ℕ) < S.length := r6'.isLt;
    have this_1 : (↑w : ℕ) < (↑r6' : ℕ) + (1 : ℕ) :=
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (↑r6' : ℕ) < S.length := r6'.isLt;
    have this : (↑w : ℕ) < (↑r6' : ℕ) + (1 : ℕ) :=
    by
          have := GoldbergSeymour.TreeSequence.positive S
          have := Fin.isLt r6'
          have := Fin.isLt w
          have := GoldbergSeymour.TreeSequence.positive S
          omega;
    have this_1 : (1 : ℕ) ≤ S.length := S.positive; this;
    have this_2 : (1 : ℕ) ≤ S.length := S.positive;
    by
        have := GoldbergSeymour.TreeSequence.positive S
        have := Fin.isLt r6'
        have := Fin.isLt w
        have := GoldbergSeymour.TreeSequence.positive S
        omega
    ⟩ : Fin (S.length + (1 : ℕ)))) → g1 ≠ g0 → g1 ≠ M.alpha → g1 ≠ M.beta →
    ∀ (g0last : E), G.ends g0last = s(y7, y8) → psi g0last = some g0 →
    ∀ (alphaLast : E), G.ends alphaLast = s(y7, y8) → psi alphaLast = some M.alpha →
    ∀ (betaLast : E), G.ends betaLast = s(y7, y8) → psi betaLast = some M.beta →
    let a0 : E := S.edge (⟨(0 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length); ((5 : ℕ) ≤ (↑w : ℕ) →
    ∃ (S' : TreeSequence G e) (M' : NormalGlobalMaximumTriple G k e psi S') (x : S'.length = (8 :
        ℕ)) (_ : M'.height = (5 : ℕ)), BalancedGlobalMaximumTriple M' ∧ S'.vertex (⟨(0 : ℕ),
    by
           have :=
            GoldbergSeymour.TreeSequence.positive S'
           have :=
            GoldbergSeymour.TreeSequence.positive S'
           omega
    ⟩ : Fin (S'.length + (1 : ℕ))) = y0 ∧ S'.vertex (⟨(1 : ℕ),
    by
            have :=
             GoldbergSeymour.TreeSequence.positive S'
            have :=
             GoldbergSeymour.TreeSequence.positive S'
            omega
    ⟩ : Fin (S'.length + (1 : ℕ))) = y1 ∧ S'.vertex (⟨(2 : ℕ),
    by
             have :=
              GoldbergSeymour.TreeSequence.positive S'
             have :=
              GoldbergSeymour.TreeSequence.positive S'
             omega
    ⟩ : Fin (S'.length + (1 : ℕ))) = v1 ∧ S'.vertex (⟨(3 : ℕ),
    by
              have :=
               GoldbergSeymour.TreeSequence.positive S'
              have :=
               GoldbergSeymour.TreeSequence.positive S'
              omega
    ⟩ : Fin (S'.length + (1 : ℕ))) = v2 ∧ S'.vertex (⟨(4 : ℕ),
    by
               have :=
                GoldbergSeymour.TreeSequence.positive S'
               have :=
                GoldbergSeymour.TreeSequence.positive S'
               omega
    ⟩ : Fin (S'.length + (1 : ℕ))) = y4 ∧ S'.vertex (⟨(5 : ℕ),
    by
                have :=
                 GoldbergSeymour.TreeSequence.positive S'
                have :=
                 GoldbergSeymour.TreeSequence.positive S'
                omega
    ⟩ : Fin (S'.length + (1 : ℕ))) = y2 ∧ S'.vertex (⟨(6 : ℕ),
    by
                 have :=
                  GoldbergSeymour.TreeSequence.positive S'
                 have :=
                  GoldbergSeymour.TreeSequence.positive S'
                 omega
    ⟩ : Fin (S'.length + (1 : ℕ))) = y3 ∧ S'.vertex (⟨(7 : ℕ),
    by
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    S'
                  have :=
                   GoldbergSeymour.TreeSequence.positive
                    S'
                  omega
    ⟩ : Fin (S'.length + (1 : ℕ))) = y7 ∧ S'.vertex (⟨(8 : ℕ),
    by
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     S'
                   have :=
                    GoldbergSeymour.TreeSequence.positive
                     S'
                   omega
    ⟩ : Fin (S'.length + (1 : ℕ))) = y8 ∧ S'.edge (⟨(0 : ℕ),
    by
                    have :=
                     GoldbergSeymour.TreeSequence.positive
                      S'
                    have :=
                     GoldbergSeymour.TreeSequence.positive
                      S'
                    omega
    ⟩ : Fin S'.length) = a0 ∧ S'.edge (⟨(1 : ℕ),
    by
                     have :=
                      GoldbergSeymour.TreeSequence.positive
                       S'
                     have :=
                      GoldbergSeymour.TreeSequence.positive
                       S'
                     omega
    ⟩ : Fin S'.length) = f1 ∧ S'.edge (⟨(2 : ℕ),
    by
                      have :=
                       GoldbergSeymour.TreeSequence.positive
                        S'
                      have :=
                       GoldbergSeymour.TreeSequence.positive
                        S'
                      omega
    ⟩ : Fin S'.length) = beta56 ∧ S'.edge (⟨(3 : ℕ),
    by
                       have :=
                        GoldbergSeymour.TreeSequence.positive
                         S'
                       have :=
                        GoldbergSeymour.TreeSequence.positive
                         S'
                       omega
    ⟩ : Fin S'.length) = f2 ∧ S'.edge (⟨(4 : ℕ),
    by
                        have :=
                         GoldbergSeymour.TreeSequence.positive
                          S'
                        have :=
                         GoldbergSeymour.TreeSequence.positive
                          S'
                        omega
    ⟩ : Fin S'.length) = a1 ∧ S'.edge (⟨(5 : ℕ),
    by
                         have :=
                          GoldbergSeymour.TreeSequence.positive
                           S'
                         have :=
                          GoldbergSeymour.TreeSequence.positive
                           S'
                         omega
    ⟩ : Fin S'.length) = a3 ∧ S'.edge (⟨(6 : ℕ),
    by
                          have :=
                           GoldbergSeymour.TreeSequence.positive
                            S'
                          have :=
                           GoldbergSeymour.TreeSequence.positive
                            S'
                          omega
    ⟩ : Fin S'.length) = c0 ∧ S'.edge (⟨(7 : ℕ),
    by
                           have :=
                            GoldbergSeymour.TreeSequence.positive
                             S'
                           have :=
                            GoldbergSeymour.TreeSequence.positive
                             S'
                           omega
    ⟩ : Fin S'.length) = c1 ∧ M'.alpha = g0 ∧ M'.beta = M.beta) →
    ∃ (e' : E) (psi' : PartialEdgeColoring E k) (S' : TreeSequence G e') (M' :
        NormalGlobalMaximumTriple G k e' psi' S'), Good psi' S' M'

/-- Dependent contract shared by the order-nine tree rebasing proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperBranch4561Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T), BalancedGlobalMaximumTriple N →
    let this : DecidableEq V := Classical.decEq V; N.height = (5 : ℕ) →
    ∀ (hlength : T.length = (8 : ℕ)),
    let r4 : Fin T.length := (⟨(4 : ℕ),
    by omega
    ⟩ : Fin T.length);
    let r5 : Fin T.length := (⟨(5 : ℕ),
    by omega
    ⟩ : Fin T.length);
    ∀ (w0 : Fin ((↑r4 : ℕ) + (1 : ℕ))) (gamma0 : Fin k), phi (T.edge r4) = some gamma0 → gamma0 ∈
        MissingColors G phi (T.vertex (w0.castLT (
    by omega
    ))) → phi (T.edge r5) = some gamma0 →
    let Good : {e : E} → (psi : PartialEdgeColoring E k) → (S : TreeSequence G e) →
        NormalGlobalMaximumTriple G k e psi S → Prop := fun {e : E} (psi : PartialEdgeColoring E
        k) (S : TreeSequence G e) (M : NormalGlobalMaximumTriple G k e psi S) ↦
    ∃ (_ : BalancedGlobalMaximumTriple M) (x : S.length = (8 : ℕ)) (_ : M.height = (5 : ℕ)) (gamma
        : Fin (2 : ℕ) → Fin k), Function.Injective gamma ∧ (
    ∀ (i j : Fin (2 : ℕ)),
    ∃ (q : Fin (5 : ℕ)), G.ends (S.edge (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    by omega
    ⟩ : Fin S.length)) = s(S.vertex (⟨(↑q : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))), S.vertex (⟨(5 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))))) ∧ (
    ∀ (i j : Fin (2 : ℕ)), psi (S.edge (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    by omega
    ⟩ : Fin S.length)) = some (gamma i)) ∧ (
    ∀ (i : Fin (2 : ℕ)),
    ∃ (q : Fin (5 : ℕ)), gamma i ∈ MissingColors G psi (S.vertex (⟨(↑q : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))))) ∧
    ∀ (i : Fin (4 : ℕ)), (1 : ℕ) ≤ (↑i : ℕ) →
    ∀ (c : Fin k), psi (S.edge (⟨(↑i : ℕ),
    by omega
    ⟩ : Fin S.length)) = some c →
    ∀ (r : Fin (2 : ℕ)), c ≠ gamma r; (
    ∀ {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence G e) (M :
        NormalGlobalMaximumTriple G k e psi S), BalancedGlobalMaximumTriple M →
    ∀ (hlen : S.length = (8 : ℕ)), M.height = (5 : ℕ) →
    ∀ (g0 : Fin k), psi (S.edge (⟨(4 : ℕ),
    by omega
    ⟩ : Fin S.length)) = some g0 → psi (S.edge (⟨(5 : ℕ),
    by omega
    ⟩ : Fin S.length)) = some g0 → g0 ∈ MissingColors G psi (S.vertex (⟨(0 : ℕ), Nat.zero_lt_succ
        S.length⟩ : Fin (S.length + (1 : ℕ)))) →
    ∃ (e' : E) (psi' : PartialEdgeColoring E k) (S' : TreeSequence G e') (M' :
        NormalGlobalMaximumTriple G k e' psi' S'), Good psi' S' M') → ¬(↑w0 : ℕ) = (0 : ℕ) →
    ∃ (e1 : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e1) (M :
        NormalGlobalMaximumTriple G k e1 psi S) (_ : BalancedGlobalMaximumTriple M) (x : S.length
        = (8 : ℕ)) (_ : M.height = (5 : ℕ)) (gamma : Fin (2 : ℕ) → Fin k), Function.Injective
        gamma ∧ (
    ∀ (i j : Fin (2 : ℕ)),
    ∃ (q : Fin (5 : ℕ)), G.ends (S.edge (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    by omega
    ⟩ : Fin S.length)) = s(S.vertex (⟨(↑q : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))), S.vertex (⟨(5 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))))) ∧ (
    ∀ (i j : Fin (2 : ℕ)), psi (S.edge (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
    by omega
    ⟩ : Fin S.length)) = some (gamma i)) ∧ (
    ∀ (i : Fin (2 : ℕ)),
    ∃ (q : Fin (5 : ℕ)), gamma i ∈ MissingColors G psi (S.vertex (⟨(↑q : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))))) ∧
    ∀ (i : Fin (4 : ℕ)), (1 : ℕ) ≤ (↑i : ℕ) →
    ∀ (c : Fin k), psi (S.edge (⟨(↑i : ℕ),
    by omega
    ⟩ : Fin S.length)) = some c →
    ∀ (r : Fin (2 : ℕ)), c ≠ gamma r

/-- Dependent contract shared by the order-nine tree rebasing proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperFirstEight3682Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (M : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y7 : V := S.vertex (⟨(7 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(7 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    ∀ (f1 f2 beta56 : E),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    by omega
    ⟩ : Fin S.length);
    let r7' : Fin S.length := (⟨(7 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    by omega
    ⟩ : Fin S.length);
    ∀ (w : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        Fin (9 : ℕ) → Fin (S.length + (1 : ℕ))) ((permA : Fin (9 : ℕ) → Fin (9 : ℕ)) i)) else
        S.vertex ((cast9 : Fin (9 : ℕ) → Fin (S.length + (1 : ℕ))) ((permB : Fin (9 : ℕ) → Fin (9
        : ℕ)) i)); newVertex (7 : Fin (9 : ℕ)) = y7 → (
    ∀ (q : Fin (7 : ℕ)),
    ∃ (t : Fin (7 : ℕ)), newVertex (Fin.castLE (
    by omega
    ) t) = S.vertex (⟨(↑q : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)))) →
    ∀ (pc1 : Fin ((↑r7' : ℕ) + (1 : ℕ))) (q : Fin (8 : ℕ)),
    ∃ (t : Fin (8 : ℕ)), newVertex (Fin.castLE (
    by omega
    ) t) = S.vertex (⟨(↑q : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)))

/-- Dependent contract shared by the order-nine tree rebasing proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperClassifyFirst2342Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (_ : NormalGlobalMaximumTriple G k e0 phi T) {e : E} (psi : PartialEdgeColoring E k)
        (S : TreeSequence G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 :
        ℕ)) (g0 : Fin k), IsProperEdgeColoring G psi →
    let y0 : V := S.vertex (⟨(0 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y1 : V := S.vertex (⟨(1 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y2 : V := S.vertex (⟨(2 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y3 : V := S.vertex (⟨(3 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y4 : V := S.vertex (⟨(4 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin S.length);
    let b1 : E := S.edge (⟨(5 : ℕ),
    by
      have := GoldbergSeymour.TreeSequence.positive S
      omega
    ⟩ : Fin S.length); (
    ∀ {i j : Fin (S.length + (1 : ℕ))}, i ≠ j → S.vertex i ≠ S.vertex j) → (
    ∀ {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G psi v → Incident G v f → psi f ≠ some c) →
        psi b0 = some g0 → psi b1 = some g0 → g0 ∈ MissingColors G psi y0 → (
    ∀ (j : Fin (2 : ℕ)),
    ∃ (q : Fin (5 : ℕ)), G.ends (S.edge (⟨(4 : ℕ) + (↑j : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive S
          omega
    ⟩ : Fin S.length)) = s(S.vertex (⟨(↑q : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive S
          omega
    ⟩ : Fin (S.length + (1 : ℕ))), S.vertex (⟨(5 : ℕ) + (↑j : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive S
          omega
    ⟩ : Fin (S.length + (1 : ℕ))))) →
    ∀ (f1 f2 f3 : E) (v1 v2 : V), psi f1 = some g0 → psi f2 = some g0 → psi f3 = some g0 → G.ends
        f1 = s(y1, v1) → G.ends f2 = s(y4, v2) → G.ends f3 = s(y2, y3) →
    ∀ (j : Fin (2 : ℕ)), S.edge (⟨(4 : ℕ) + (↑j : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive S
        omega
    ⟩ : Fin S.length) = f1 ∧ S.vertex (⟨(5 : ℕ) + (↑j : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive S
        omega
    ⟩ : Fin (S.length + (1 : ℕ))) = v1 ∨ S.edge (⟨(4 : ℕ) + (↑j : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive S
        omega
    ⟩ : Fin S.length) = f2 ∧ S.vertex (⟨(5 : ℕ) + (↑j : ℕ),
    by
        have := GoldbergSeymour.TreeSequence.positive S
        omega
    ⟩ : Fin (S.length + (1 : ℕ))) = v2

/-- Typed data construction shared by the order-nine tree rebasing proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
noncomputable abbrev helperS3810.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
  {E : Type u_2} →

  [ DecidableEq E] →
  (G : LooplessMultigraph V E) →
  (k : ℕ) →
  {e : E} →

  (S : TreeSequence G e) →
  (hlen : S.length = (8 : ℕ)) →
  let y0 : V :=
    S.vertex
      (⟨(0 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction
            fun (a : ¬(0 : ℕ) < S.length + (1 : ℕ)) ↦ by omega⟩ :
        Fin (S.length + (1 : ℕ)));
  let y1 : V :=
    S.vertex
      (⟨(1 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction
            fun (a : ¬(1 : ℕ) < S.length + (1 : ℕ)) ↦ by omega⟩ :
        Fin (S.length + (1 : ℕ)));
  let y2 : V :=
    S.vertex
      (⟨(2 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction
            fun (a : ¬(2 : ℕ) < S.length + (1 : ℕ)) ↦ by omega⟩ :
        Fin (S.length + (1 : ℕ)));
  let y3 : V :=
    S.vertex
      (⟨(3 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction
            fun (a : ¬(3 : ℕ) < S.length + (1 : ℕ)) ↦ by omega⟩ :
        Fin (S.length + (1 : ℕ)));
  let y4 : V :=
    S.vertex
      (⟨(4 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction
            fun (a : ¬(4 : ℕ) < S.length + (1 : ℕ)) ↦ by omega⟩ :
        Fin (S.length + (1 : ℕ)));
  let y7 : V :=
    S.vertex
      (⟨(7 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction
            fun (a : ¬(7 : ℕ) < S.length + (1 : ℕ)) ↦ by omega⟩ :
        Fin (S.length + (1 : ℕ)));
  let y8 : V :=
    S.vertex
      (⟨(8 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction
            fun (a : ¬(8 : ℕ) < S.length + (1 : ℕ)) ↦ by omega⟩ :
        Fin (S.length + (1 : ℕ)));
  let a1 : E :=
    S.edge
      (⟨(1 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction fun (a : ¬(1 : ℕ) < S.length) ↦ by
            omega⟩ :
        Fin S.length);
  let a3 : E :=
    S.edge
      (⟨(3 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction fun (a : ¬(3 : ℕ) < S.length) ↦ by
            omega⟩ :
        Fin S.length);
  let b0 : E :=
    S.edge
      (⟨(4 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction fun (a : ¬(4 : ℕ) < S.length) ↦ by
            omega⟩ :
        Fin S.length);
  let c0 : E :=
    S.edge
      (⟨(6 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction fun (a : ¬(6 : ℕ) < S.length) ↦ by
            omega⟩ :
        Fin S.length);
  let c1 : E :=
    S.edge
      (⟨(7 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction fun (a : ¬(7 : ℕ) < S.length) ↦ by
            omega⟩ :
        Fin S.length);
  (f1 f2 : E) →
  (v1 v2 : V) →
  G.ends f1 = s(y1, v1) →
  G.ends f2 = s(y4, v2) →
  (beta56 : E) →
  G.ends beta56 = s(v1, v2) →
  G.ends a1 = s(y1, y2) →
  G.ends a3 = s(y3, y4) →
  let r6' : Fin S.length :=
    (⟨(6 : ℕ),
        have _ : (1 : ℕ) ≤ S.length := S.positive;
        have _ : (1 : ℕ) ≤ S.length := S.positive;
        by omega⟩ :
      Fin S.length);
  let r7' : Fin S.length :=
    (⟨(7 : ℕ),
        have _ : (1 : ℕ) ≤ S.length := S.positive;
        have _ : (1 : ℕ) ≤ S.length := S.positive;
        by omega⟩ :
      Fin S.length);
  (w pc : Fin ((↑r6' : ℕ) + (1 : ℕ))) →
  let pc' : Fin (7 : ℕ) :=
    (⟨(↑pc : ℕ),
        have this : (↑pc : ℕ) < (↑r6' : ℕ) + (1 : ℕ) :=
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (↑r6' : ℕ) < S.length := r6'.isLt;
          have this :
            (↑pc : ℕ) < (↑r6' : ℕ) + (1 : ℕ) := pc.isLt;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          this;
        this⟩ :
      Fin (7 : ℕ));
  G.ends c0 =
      s(y7,
        S.vertex
          (⟨(↑pc' : ℕ),
              have _ : (1 : ℕ) ≤ S.length := S.positive;
              have _ : (↑r6' : ℕ) < S.length :=
                r6'.isLt;
              have _ :
                (↑pc : ℕ) < (↑r6' : ℕ) + (1 : ℕ) :=
                have _ : (1 : ℕ) ≤ S.length :=
                  S.positive;
                have _ : (↑r6' : ℕ) < S.length :=
                  r6'.isLt;
                have this :
                  (↑pc : ℕ) < (↑r6' : ℕ) + (1 : ℕ) :=
                  pc.isLt;
                have _ : (1 : ℕ) ≤ S.length :=
                  S.positive;
                this;
              have this : (↑pc' : ℕ) < (7 : ℕ) :=
                pc'.isLt;
              have _ : (1 : ℕ) ≤ S.length := S.positive;
              by omega⟩ :
            Fin (S.length + (1 : ℕ)))) →
  let a0 : E :=
    S.edge
      (⟨(0 : ℕ),
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          have _ : (1 : ℕ) ≤ S.length := S.positive;
          Decidable.byContradiction
            fun (a : ¬(0 : ℕ) < S.length) ↦ by
            omega⟩ :
        Fin S.length);
  a0 = e →
  G.ends a0 = s(y1, y0) →
  let cast9 :
    Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) :=
    finCongr (by omega);
  let permA : Equiv.Perm (Fin (9 : ℕ)) :=
    Equiv.trans
      (Equiv.swap (2 : Fin (9 : ℕ))
        (5 : Fin (9 : ℕ)))
      (Equiv.swap (3 : Fin (9 : ℕ))
        (6 : Fin (9 : ℕ)));
  let permB : Equiv.Perm (Fin (9 : ℕ)) :=
    (Equiv.trans
          (Equiv.swap (2 : Fin (9 : ℕ))
            (6 : Fin (9 : ℕ)))
          (Equiv.swap (2 : Fin (9 : ℕ))
            (3 : Fin (9 : ℕ)))).trans
      (Equiv.swap (2 : Fin (9 : ℕ))
        (5 : Fin (9 : ℕ)));
  let newVertex : Fin (9 : ℕ) → V :=
    fun (i : Fin (9 : ℕ)) ↦
    if b0 = f1 then
      S.vertex
        ((cast9 :
            Fin (9 : ℕ) →
              Fin (S.length + (1 : ℕ)))
          ((permA : Fin (9 : ℕ) → Fin (9 : ℕ)) i))
    else
      S.vertex
        ((cast9 :
            Fin (9 : ℕ) →
              Fin (S.length + (1 : ℕ)))
          ((permB : Fin (9 : ℕ) → Fin (9 : ℕ))
            i));
  let edgeList : List E :=
    [a0, f1, beta56, f2, a1, a3, c0, c1];
  (hedgeListLength : edgeList.length = (8 : ℕ)) →
  let newEdge : Fin (8 : ℕ) → E :=
    fun (i : Fin (8 : ℕ)) ↦
    edgeList.get
      (Fin.cast (Eq.symm hedgeListLength) i);
  newVertex (0 : Fin (9 : ℕ)) = y0 →
  newVertex (1 : Fin (9 : ℕ)) = y1 →
  newVertex (2 : Fin (9 : ℕ)) = v1 →
  newVertex (3 : Fin (9 : ℕ)) = v2 →
  newVertex (4 : Fin (9 : ℕ)) = y4 →
  newVertex (5 : Fin (9 : ℕ)) = y2 →
  newVertex (6 : Fin (9 : ℕ)) = y3 →
  newVertex (7 : Fin (9 : ℕ)) =
      y7 →
  newVertex (8 : Fin (9 : ℕ)) =
      y8 →
  newEdge (0 : Fin (8 : ℕ)) =
      a0 →
  newEdge
        (1 : Fin (8 : ℕ)) =
      f1 →
  newEdge
        (2 :
          Fin (8 : ℕ)) =
      beta56 →
  newEdge
        (3 :
          Fin (8 : ℕ)) =
      f2 →
  newEdge
        (4 :
          Fin
            (8 : ℕ)) =
      a1 →
  newEdge
        (5 :
          Fin
            (8 :
              ℕ)) =
      a3 →
  newEdge
        (6 :
          Fin
            (8 :
              ℕ)) =
      c0 →
  newEdge
        (7 :
          Fin
            (8 :
              ℕ)) =
      c1 →
  Function.Injective
      newVertex →
  Function.Injective
      newEdge →
  (pc1 :
      Fin
        ((↑r7' :
            ℕ) +
          (1 :
            ℕ))) →
  let
    pc1' :
    Fin
      (8 :
        ℕ) :=
    (⟨(↑pc1 :
          ℕ),
        by
        omega⟩ :
      Fin
        (8 :
          ℕ));
  G.ends
        c1 =
      s(y8,
        S.vertex
          (⟨(↑pc1' :
                ℕ),
              by
              omega⟩ :
            Fin
              (S.length +
                (1 :
                  ℕ)))) →
  (tc0 :
      Fin
        (7 :
          ℕ)) →
  newVertex
        (Fin.castLE
          (by
            omega)
          tc0) =
      S.vertex
        (⟨(↑pc' :
              ℕ),
            by
            omega⟩ :
          Fin
            (S.length +
              (1 :
                ℕ))) →
  (tc1 :
      Fin
        (8 :
          ℕ)) →
  newVertex
        (Fin.castLE
          (by
            omega)
          tc1) =
      S.vertex
        (⟨(↑pc1' :
              ℕ),
            by
            omega⟩ :
          Fin
            (S.length +
              (1 :
                ℕ))) →
  TreeSequence
    G
    e := by
  classical
  intro V E _ G k e S hlen y0 y1 y2 y3 y4 y7 y8 a1 a3 b0 c0 c1 f1 f2 v1 v2 hf1ends' hf2ends' beta56
      hbeta56ends ha1ends ha3ends r6' r7' w pc pc' hc0ends a0 ha0eq ha0ends cast9 permA permB
      newVertex edgeList hedgeListLength newEdge nv0 nv1 nv2 nv3 nv4 nv5 nv6 nv7 nv8 ne0 ne1 ne2 ne3
      ne4 ne5 ne6 ne7 newVertex_injective newEdge_injective pc1 pc1' hc1ends tc0 htc0 tc1 htc1
  exact {
    length := 8
    positive := by omega
    vertex := newVertex
    edge := newEdge
    vertex_injective := newVertex_injective
    edge_injective := newEdge_injective
    first_edge := ne0.trans ha0eq
    attaches := by
      intro j
      fin_cases j
      · refine ⟨0, ?_⟩
        change G.ends (newEdge 0) = s(newVertex 1, newVertex 0)
        rw [ne0, nv0, nv1]
        exact ha0ends
      · refine ⟨1, ?_⟩
        change G.ends (newEdge 1) = s(newVertex 2, newVertex 1)
        rw [ne1, nv1, nv2]
        exact hf1ends'.trans Sym2.eq_swap
      · refine ⟨2, ?_⟩
        change G.ends (newEdge 2) = s(newVertex 3, newVertex 2)
        rw [ne2, nv2, nv3]
        exact hbeta56ends.trans Sym2.eq_swap
      · refine ⟨3, ?_⟩
        change G.ends (newEdge 3) = s(newVertex 4, newVertex 3)
        rw [ne3, nv3, nv4]
        exact hf2ends'
      · refine ⟨1, ?_⟩
        change G.ends (newEdge 4) = s(newVertex 5, newVertex 1)
        rw [ne4, nv1, nv5]
        exact ha1ends.trans Sym2.eq_swap
      · refine ⟨4, ?_⟩
        change G.ends (newEdge 5) = s(newVertex 6, newVertex 4)
        rw [ne5, nv4, nv6]
        exact ha3ends
      · refine ⟨tc0, ?_⟩
        change G.ends (newEdge 6) =
          s(newVertex 7, newVertex (Fin.castLE (by omega) tc0))
        rw [ne6, nv7]
        exact hc0ends.trans (congrArg (fun z ↦ s(y7, z)) htc0.symm)
      · refine ⟨tc1, ?_⟩
        change G.ends (newEdge 7) =
          s(newVertex 8, newVertex (Fin.castLE (by omega) tc1))
        rw [ne7, nv8]
        exact hc1ends.trans (congrArg (fun z ↦ s(y8, z)) htc1.symm) }

/-- Dependent contract shared by the order-nine tree rebasing proof modules.

Keeping this interface separate avoids repeating its dependent hypotheses and data.
-/
abbrev helperHS'tash4523Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (M : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)) (g0 : Fin k),
    let y0 : V := S.vertex (⟨(0 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y1 : V := S.vertex (⟨(1 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y2 : V := S.vertex (⟨(2 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(2 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y3 : V := S.vertex (⟨(3 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y4 : V := S.vertex (⟨(4 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y7 : V := S.vertex (⟨(7 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(7 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y8 : V := S.vertex (⟨(8 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(8 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let a1 : E := S.edge (⟨(1 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let a3 : E := S.edge (⟨(3 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let b0 : E := S.edge (⟨(4 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let c0 : E := S.edge (⟨(6 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let c1 : E := S.edge (⟨(7 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(7 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    ∀ (hg0' : g0 ∈ MissingColors G psi y0) (f1 f2 : E) (v1 v2 : V) (hf1color : psi f1 = some g0)
        (hf2color : psi f2 = some g0) (hf1ends' : G.ends f1 = s(y1, v1)) (hf2ends' : G.ends f2 =
        s(y4, v2)) (beta56 : E) (hbeta56ends : G.ends beta56 = s(v1, v2)) (hbeta56color : psi
        beta56 = some M.beta) (ha1ends : G.ends a1 = s(y1, y2)) (ha3ends : G.ends a3 = s(y3, y4))
        (ha1color : psi a1 = some M.alpha) (ha3color : psi a3 = some M.alpha),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have x : (1 : ℕ) ≤ S.length := S.positive;
    by omega
    ⟩ : Fin S.length);
    let r7' : Fin S.length := (⟨(7 : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have x : (1 : ℕ) ≤ S.length := S.positive;
    by omega
    ⟩ : Fin S.length);
    ∀ (w : Fin ((↑r6' : ℕ) + (1 : ℕ))) (g1 : Fin k) (hc1color : psi c1 = some g1) (hc0color' : psi
        c0 = some g1) (pc : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let pc' : Fin (7 : ℕ) := (⟨(↑pc : ℕ),
    have this : (↑pc : ℕ) < (↑r6' : ℕ) + (1 : ℕ) :=
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (↑r6' : ℕ) < S.length := r6'.isLt;
    have this : (↑pc : ℕ) < (↑r6' : ℕ) + (1 : ℕ) := pc.isLt;
    have this_1 : (1 : ℕ) ≤ S.length := S.positive; this; this⟩ : Fin (7 : ℕ));
    ∀ (hc0ends : G.ends c0 = s(y7, S.vertex (⟨(↑pc' : ℕ),
    have x : (1 : ℕ) ≤ S.length := S.positive;
    have x : (↑r6' : ℕ) < S.length := r6'.isLt;
    have x : (↑pc : ℕ) < (↑r6' : ℕ) + (1 : ℕ) :=
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (↑r6' : ℕ) < S.length := r6'.isLt;
    have this : (↑pc : ℕ) < (↑r6' : ℕ) + (1 : ℕ) := pc.isLt;
    have this_1 : (1 : ℕ) ≤ S.length := S.positive; this;
    have this : (↑pc' : ℕ) < (7 : ℕ) := pc'.isLt;
    have x : (1 : ℕ) ≤ S.length := S.positive;
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))))),
    let a0 : E := S.edge (⟨(0 : ℕ),
    have this : (1 : ℕ) ≤ S.length := S.positive;
    have this : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    ∀ (ha0eq : a0 = e) (ha0ends : G.ends a0 = s(y1, y0)),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permA : (a : Fin (9 : ℕ)) → Fin (9 : ℕ))
        i)) else S.vertex ((cast9 : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permB : (a :
        Fin (9 : ℕ)) → Fin (9 : ℕ)) i));
    let edgeList : List E := [a0, f1, beta56, f2, a1, a3, c0, c1];
    ∀ (hedgeListLength : edgeList.length = (8 : ℕ)),
    let newEdge : Fin (8 : ℕ) → E := fun (i : Fin (8 : ℕ)) ↦ edgeList.get (Fin.cast (Eq.symm
        hedgeListLength) i);
    ∀ (nv0 : newVertex (0 : Fin (9 : ℕ)) = y0) (nv1 : newVertex (1 : Fin (9 : ℕ)) = y1) (nv2 :
        newVertex (2 : Fin (9 : ℕ)) = v1) (nv3 : newVertex (3 : Fin (9 : ℕ)) = v2) (nv4 :
        newVertex (4 : Fin (9 : ℕ)) = y4) (nv5 : newVertex (5 : Fin (9 : ℕ)) = y2) (nv6 :
        newVertex (6 : Fin (9 : ℕ)) = y3) (nv7 : newVertex (7 : Fin (9 : ℕ)) = y7) (nv8 :
        newVertex (8 : Fin (9 : ℕ)) = y8) (ne0 : newEdge (0 : Fin (8 : ℕ)) = a0) (ne1 : newEdge (1
        : Fin (8 : ℕ)) = f1) (ne2 : newEdge (2 : Fin (8 : ℕ)) = beta56) (ne3 : newEdge (3 : Fin (8
        : ℕ)) = f2) (ne4 : newEdge (4 : Fin (8 : ℕ)) = a1) (ne5 : newEdge (5 : Fin (8 : ℕ)) = a3)
        (ne6 : newEdge (6 : Fin (8 : ℕ)) = c0) (ne7 : newEdge (7 : Fin (8 : ℕ)) = c1)
        (newVertex_injective : Function.Injective newVertex) (newEdge_injective :
        Function.Injective newEdge) (pc1 : Fin ((↑r7' : ℕ) + (1 : ℕ))),
    let pc1' : Fin (8 : ℕ) := (⟨(↑pc1 : ℕ),
    by omega
    ⟩ : Fin (8 : ℕ));
    ∀ (hc1ends : G.ends c1 = s(y8, S.vertex (⟨(↑pc1' : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))))) (tc0 : Fin (7 : ℕ)) (htc0 : newVertex (Fin.castLE (
    by omega
    ) tc0) = S.vertex (⟨(↑pc' : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)))) (tc1 : Fin (8 : ℕ)) (htc1 : newVertex (Fin.castLE (
    by omega
    ) tc1) = S.vertex (⟨(↑pc1' : ℕ),
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)))) (tw : Fin (7 : ℕ)),
    let S' : TreeSequence G e := helperS3810 G k S hlen f1 f2 v1 v2 hf1ends' hf2ends' beta56
        hbeta56ends ha1ends ha3ends w pc hc0ends ha0eq ha0ends hedgeListLength nv0 nv1 nv2 nv3 nv4
        nv5 nv6 nv7 nv8 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 newVertex_injective newEdge_injective pc1
        hc1ends tc0 htc0 tc1 htc1;
    ∀ (hS'length : S'.length = (8 : ℕ)) (htwMissing : g1 ∈ MissingColors G psi (S'.vertex (⟨(↑tw :
        ℕ),
    by omega
    ⟩ : Fin (S'.length + (1 : ℕ))))), TashkinovTree G e psi S'

theorem mappedCastLE {V : Type*} {m n : ℕ} (f : Fin n → V)
    (h : m ≤ n) (i : Fin m) (j : Fin n) (heq : i.val = j.val) :
    f (Fin.castLE h i) = f j := congrArg f (Fin.ext heq)

theorem alternatingVertexSupport {V E : Type*} (vertex : Fin 5 → V)
    (e1 e2 e3 c : E) (v : V) :
    Sum.inl v ∈ [Sum.inl (vertex 1), Sum.inr e1, Sum.inl (vertex 2), Sum.inr e2,
      Sum.inl (vertex 3), Sum.inr e3, Sum.inl (vertex 4), Sum.inr c, Sum.inl (vertex 0)] ↔
      ∃ i : Fin 5, v = vertex i := by
  simp only [List.mem_cons, List.not_mem_nil, Sum.inl.injEq, reduceCtorEq,
    or_false, false_or, Fin.exists_fin_succ, Fin.exists_fin_zero]
  tauto

theorem alternatingEdgeSupport {V E : Type*} (v0 v1 v2 v3 v4 : V)
    (e1 e2 e3 c : E) (edge : Fin 8 → E) (h1 : edge 1 = e1)
    (h2 : edge 2 = e2) (h3 : edge 3 = e3) (f : E) :
    Sum.inr f ∈ [Sum.inl v1, Sum.inr e1, Sum.inl v2, Sum.inr e2,
      Sum.inl v3, Sum.inr e3, Sum.inl v4, Sum.inr c, Sum.inl v0] ↔
      f = c ∨ ∃ j : Fin 8, 1 ≤ j.val ∧ j.val + 2 ≤ 5 ∧ f = edge j := by
  simp [Fin.exists_fin_succ, h1, h2, h3, or_left_comm, or_comm]

theorem helper_hp1not5_194.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (_ : NormalGlobalMaximumTriple G k e0 phi T) {e : E} (psi : PartialEdgeColoring E k)
    (S : TreeSequence G e) (_ : NormalGlobalMaximumTriple G k e psi S)
    (hlen : S.length = (8 : ℕ)) (g0 : Fin k),
  IsProperEdgeColoring G psi →
  let y5 : V := S.vertex (⟨(5 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y6 : V := S.vertex (⟨(6 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let b0 : E := S.edge (⟨(4 : ℕ), by omega⟩ : Fin S.length);
  let b1 : E := S.edge (⟨(5 : ℕ), by omega⟩ : Fin S.length);
  (∀ {i j : Fin S.length}, i ≠ j → S.edge i ≠ S.edge j) →
  psi b0 = some g0 →
  psi b1 = some g0 →
  ∀ (p0 : Fin ((↑(⟨(4 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ))),
  G.ends b0 = s(y5, S.vertex (p0.castLT (by omega))) →
  ∀ (p1 : Fin ((↑(⟨(5 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ))),
  G.ends b1 = s(y6, S.vertex (p1.castLT (by omega))) →
  (↑p1 : ℕ) ≠ (5 : ℕ) := by
  classical
  intro V E _ _ _ G k e0 phi T N e psi S M hlen g0 hproper y5 y6 b0 b1 hedge_ne h4' h5' p0
      hb0ends p1 hb1ends hp15
  have hinc0 : Incident G y5 b0 := by
    rw [Incident, hb0ends]
    simp
  have hp1vertex : S.vertex (Fin.castLT p1
      (Nat.lt_trans p1.isLt
        (Nat.succ_lt_succ (⟨5, by omega⟩ : Fin S.length).isLt))) = y5 := by
    apply congrArg S.vertex
    apply Fin.ext
    simpa [y5] using hp15
  have hinc1 : Incident G y5 b1 := by
    rw [Incident, hb1ends, hp1vertex]
    simp
  have hbne : b0 ≠ b1 := by
    apply hedge_ne
    norm_num
  exact (hproper hbne ⟨y5, hinc0, hinc1⟩ h4') h5'

theorem helper_hfirstAttach_212.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (_ : NormalGlobalMaximumTriple G k e0 phi T) {e : E} (psi : PartialEdgeColoring E k)
    (S : TreeSequence G e) (_ : NormalGlobalMaximumTriple G k e psi S)
    (hlen : S.length = (8 : ℕ)),
  let y5 : V := S.vertex (⟨(5 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y6 : V := S.vertex (⟨(6 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let b0 : E := S.edge (⟨(4 : ℕ), by omega⟩ : Fin S.length);
  let b1 : E := S.edge (⟨(5 : ℕ), by omega⟩ : Fin S.length);
  ∀ (p0 : Fin ((↑(⟨(4 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ))),
  G.ends b0 = s(y5, S.vertex (p0.castLT (by omega))) →
  ∀ (p1 : Fin ((↑(⟨(5 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ))),
  G.ends b1 = s(y6, S.vertex (p1.castLT (by omega))) →
  (↑p1 : ℕ) ≠ (5 : ℕ) →
  ∀ (j : Fin (2 : ℕ)),
  ∃ (q : Fin (5 : ℕ)),
  G.ends (S.edge (⟨(4 : ℕ) + (↑j : ℕ), by omega⟩ : Fin S.length)) =
    s(S.vertex (⟨(↑q : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))),
      S.vertex (⟨(5 : ℕ) + (↑j : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)))) := by
  classical
  intro V E _ _ _ G k e0 phi T N e psi S M hlen y5 y6 b0 b1 p0 hb0ends p1 hb1ends hp1not5 j
  have hj : j.val = 0 ∨ j.val = 1 := by omega
  rcases hj with hj | hj
  · let q : Fin 5 := ⟨p0.val, by simp⟩
    refine ⟨q, ?_⟩
    have hv : S.vertex (Fin.castLT p0
        (Nat.lt_trans p0.isLt
          (Nat.succ_lt_succ (⟨4, by omega⟩ : Fin S.length).isLt))) =
        S.vertex ⟨q.val, by omega⟩ := by
      apply congrArg S.vertex
      apply Fin.ext
      rfl
    rw [show j = (0 : Fin 2) by apply Fin.ext; exact hj]
    simpa [b0, y5, hv] using hb0ends.trans Sym2.eq_swap
  · let q : Fin 5 := ⟨p1.val, by
        have hp := p1.isLt
        have hp' : p1.val < 6 := by simp
        omega⟩
    refine ⟨q, ?_⟩
    have hv : S.vertex (Fin.castLT p1
        (Nat.lt_trans p1.isLt
          (Nat.succ_lt_succ (⟨5, by omega⟩ : Fin S.length).isLt))) =
        S.vertex ⟨q.val, by omega⟩ := by
      apply congrArg S.vertex
      apply Fin.ext
      rfl
    rw [show j = (1 : Fin 2) by apply Fin.ext; exact hj]
    simpa [b1, y6, hv] using hb1ends.trans Sym2.eq_swap

theorem helper_branch_380.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (_ : NormalGlobalMaximumTriple G k e0 phi T) {e : E} (psi : PartialEdgeColoring E k)
    (S : TreeSequence G e) (_ : NormalGlobalMaximumTriple G k e psi S)
    (hlen : S.length = (8 : ℕ)) (g0 : Fin k),
  IsProperEdgeColoring G psi →
  let y1 : V := S.vertex (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  ∀ (f1 f2 : E) (v1 v2 : V),
  psi f1 = some g0 →
  G.ends f1 = s(y1, v1) →
  ∀ (j : Fin (2 : ℕ)) (q : Fin (5 : ℕ)),
  let bj : E := S.edge (⟨(4 : ℕ) + (↑j : ℕ), by omega⟩ : Fin S.length);
  let z : V := S.vertex (⟨(5 : ℕ) + (↑j : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  G.ends bj = s(S.vertex (⟨(↑q : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))), z) →
  psi bj = some g0 →
  z ≠ y1 →
  (↑q : ℕ) = (1 : ℕ) →
  S.edge (⟨(4 : ℕ) + (↑j : ℕ), by omega⟩ : Fin S.length) = f1 ∧
      S.vertex (⟨(5 : ℕ) + (↑j : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))) = v1 ∨
    S.edge (⟨(4 : ℕ) + (↑j : ℕ), by omega⟩ : Fin S.length) = f2 ∧
      S.vertex (⟨(5 : ℕ) + (↑j : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))) = v2 := by
  classical
  intro V E _ _ _ G k e0 phi T N e psi S M hlen g0 hproper y1 f1 f2 v1 v2 hf1color hf1ends' j q
      bj z hbjends hbjcolor hz1 hq1
  have hincb : Incident G y1 bj := by
    rw [Incident, hbjends]
    have hv : S.vertex ⟨q.val, by omega⟩ = y1 := by
      apply congrArg S.vertex
      apply Fin.ext
      simpa [y1] using hq1
    rw [hv]
    simp
  have hincf : Incident G y1 f1 := by
    rw [Incident, hf1ends']
    simp
  have hbf : bj = f1 := by
    by_contra hne
    exact (hproper hne ⟨y1, hincb, hincf⟩ hbjcolor) hf1color
  left
  refine ⟨by simpa [bj] using hbf, ?_⟩
  have hpairs : s(y1, z) = s(y1, v1) := by
    calc
      s(y1, z) = G.ends bj := by
        rw [hbjends]
        congr 1
        apply congrArg S.vertex
        apply Fin.ext
        simpa [y1] using hq1.symm
      _ = G.ends f1 := congrArg G.ends hbf
      _ = s(y1, v1) := hf1ends'
  rcases Sym2.eq_iff.mp hpairs with hd | hs
  · simpa [z] using hd.2
  · exact False.elim (hz1 hs.2)

theorem helper_branch_409.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (_ : NormalGlobalMaximumTriple G k e0 phi T) {e : E} (psi : PartialEdgeColoring E k)
    (S : TreeSequence G e) (_ : NormalGlobalMaximumTriple G k e psi S)
    (hlen : S.length = (8 : ℕ)) (g0 : Fin k),
  IsProperEdgeColoring G psi →
  let y4 : V := S.vertex (⟨(4 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  ∀ (f1 f2 : E) (v1 v2 : V),
  psi f2 = some g0 →
  G.ends f2 = s(y4, v2) →
  ∀ (j : Fin (2 : ℕ)) (q : Fin (5 : ℕ)),
  let bj : E := S.edge (⟨(4 : ℕ) + (↑j : ℕ), by omega⟩ : Fin S.length);
  let z : V := S.vertex (⟨(5 : ℕ) + (↑j : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  G.ends bj = s(S.vertex (⟨(↑q : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))), z) →
  psi bj = some g0 →
  z ≠ y4 →
  (↑q : ℕ) = (4 : ℕ) →
  S.edge (⟨(4 : ℕ) + (↑j : ℕ), by omega⟩ : Fin S.length) = f1 ∧
      S.vertex (⟨(5 : ℕ) + (↑j : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))) = v1 ∨
    S.edge (⟨(4 : ℕ) + (↑j : ℕ), by omega⟩ : Fin S.length) = f2 ∧
      S.vertex (⟨(5 : ℕ) + (↑j : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))) = v2 := by
  classical
  intro V E _ _ _ G k e0 phi T N e psi S M hlen g0 hproper y4 f1 f2 v1 v2 hf2color hf2ends' j q
      bj z hbjends hbjcolor hz4 hq4
  have hincb : Incident G y4 bj := by
    rw [Incident, hbjends]
    have hv : S.vertex ⟨q.val, by omega⟩ = y4 := by
      apply congrArg S.vertex
      apply Fin.ext
      simpa [y4] using hq4
    rw [hv]
    simp
  have hincf : Incident G y4 f2 := by
    rw [Incident, hf2ends']
    simp
  have hbf : bj = f2 := by
    by_contra hne
    exact (hproper hne ⟨y4, hincb, hincf⟩ hbjcolor) hf2color
  right
  refine ⟨by simpa [bj] using hbf, ?_⟩
  have hpairs : s(y4, z) = s(y4, v2) := by
    calc
      s(y4, z) = G.ends bj := by
        rw [hbjends]
        congr 1
        apply congrArg S.vertex
        apply Fin.ext
        simpa [y4] using hq4.symm
      _ = G.ends f2 := congrArg G.ends hbf
      _ = s(y4, v2) := hf2ends'
  rcases Sym2.eq_iff.mp hpairs with hd | hs
  · simpa [z] using hd.2
  · exact False.elim (hz4 hs.2)

theorem helper_hg0alpha_524.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (_ : NormalGlobalMaximumTriple G k e0 phi T) {e : E} (psi : PartialEdgeColoring E k)
    (S : TreeSequence G e) (M : NormalGlobalMaximumTriple G k e psi S)
    (hlen : S.length = (8 : ℕ)) (g0 : Fin k),
  IsProperEdgeColoring G psi →
  let y1 : V := S.vertex (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y5 : V := S.vertex (⟨(5 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y6 : V := S.vertex (⟨(6 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let b0 : E := S.edge (⟨(4 : ℕ), by omega⟩ : Fin S.length);
  let b1 : E := S.edge (⟨(5 : ℕ), by omega⟩ : Fin S.length);
  (∀ {i j : Fin (S.length + (1 : ℕ))}, i ≠ j → S.vertex i ≠ S.vertex j) →
  ∀ (f1 f2 : E) (v1 v2 : V),
  psi f1 = some g0 →
  G.ends f1 = s(y1, v1) →
  b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2 ∨ b0 = f2 ∧ y5 = v2 ∧ b1 = f1 ∧ y6 = v1 →
  ∀ (alpha56 : E),
  psi alpha56 = some M.alpha →
  G.ends alpha56 = s(y5, y6) →
  g0 ≠ M.alpha := by
  classical
  intro V E _ _ _ G k e0 phi T N e psi S M hlen g0 hproper y1 y5 y6 b0 b1 hvertex_ne f1 f2 v1 v2
      hf1color hf1ends' horient alpha56 halpha56color halpha56ends' hEq
  have hfne : f1 ≠ alpha56 := by
    intro heq
    have hpairs : s(y1, v1) = s(y5, y6) := by
      rw [← hf1ends', heq, halpha56ends']
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact (hvertex_ne (i := (⟨1, by omega⟩ : Fin (S.length + 1)))
        (j := (⟨5, by omega⟩ : Fin (S.length + 1))) (by norm_num))
        (by simpa [y1, y5] using hd.1)
    · exact (hvertex_ne (i := (⟨1, by omega⟩ : Fin (S.length + 1)))
        (j := (⟨6, by omega⟩ : Fin (S.length + 1))) (by norm_num))
        (by simpa [y1, y6] using hs.1)
  have hincf : Incident G v1 f1 := by
    rw [Incident, hf1ends']
    simp
  have hinca : Incident G v1 alpha56 := by
    rw [Incident, halpha56ends']
    rcases horient with h | h
    · simp [h.2.1]
    · simp [h.2.2.2]
  exact (hproper hfne ⟨v1, hincf, hinca⟩ hf1color)
    (by simpa [hEq] using halpha56color)

theorem helper_hg0beta_547.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (_ : NormalGlobalMaximumTriple G k e0 phi T) {e : E} (psi : PartialEdgeColoring E k)
    (S : TreeSequence G e) (M : NormalGlobalMaximumTriple G k e psi S)
    (hlen : S.length = (8 : ℕ)) (g0 : Fin k),
  IsProperEdgeColoring G psi →
  let y1 : V := S.vertex (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y5 : V := S.vertex (⟨(5 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y6 : V := S.vertex (⟨(6 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let b0 : E := S.edge (⟨(4 : ℕ), by omega⟩ : Fin S.length);
  let b1 : E := S.edge (⟨(5 : ℕ), by omega⟩ : Fin S.length);
  (∀ {i j : Fin (S.length + (1 : ℕ))}, i ≠ j → S.vertex i ≠ S.vertex j) →
  ∀ (f1 f2 : E) (v1 v2 : V),
  psi f1 = some g0 →
  G.ends f1 = s(y1, v1) →
  b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2 ∨ b0 = f2 ∧ y5 = v2 ∧ b1 = f1 ∧ y6 = v1 →
  ∀ (beta56 : E),
  psi beta56 = some M.beta →
  G.ends beta56 = s(y5, y6) →
  g0 ≠ M.beta := by
  classical
  intro V E _ _ _ G k e0 phi T N e psi S M hlen g0 hproper y1 y5 y6 b0 b1 hvertex_ne f1 f2 v1 v2
      hf1color hf1ends' horient beta56 hbeta56color hbeta56ends' hEq
  have hfne : f1 ≠ beta56 := by
    intro heq
    have hpairs : s(y1, v1) = s(y5, y6) := by
      rw [← hf1ends', heq, hbeta56ends']
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact (hvertex_ne (i := (⟨1, by omega⟩ : Fin (S.length + 1)))
        (j := (⟨5, by omega⟩ : Fin (S.length + 1))) (by norm_num))
        (by simpa [y1, y5] using hd.1)
    · exact (hvertex_ne (i := (⟨1, by omega⟩ : Fin (S.length + 1)))
        (j := (⟨6, by omega⟩ : Fin (S.length + 1))) (by norm_num))
        (by simpa [y1, y6] using hs.1)
  have hincf : Incident G v1 f1 := by
    rw [Incident, hf1ends']
    simp
  have hincb : Incident G v1 beta56 := by
    rw [Incident, hbeta56ends']
    rcases horient with h | h
    · simp [h.2.1]
    · simp [h.2.2.2]
  exact (hproper hfne ⟨v1, hincf, hincb⟩ hf1color)
    (by simpa [hEq] using hbeta56color)

theorem helper_hcoverG0_732.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (_ : NormalGlobalMaximumTriple G k e0 phi T) {e : E} (psi : PartialEdgeColoring E k)
    (S : TreeSequence G e) (_ : NormalGlobalMaximumTriple G k e psi S)
    (hlen : S.length = (8 : ℕ)) (g0 : Fin k),
  let y1 : V := S.vertex (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y2 : V := S.vertex (⟨(2 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y3 : V := S.vertex (⟨(3 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y4 : V := S.vertex (⟨(4 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y5 : V := S.vertex (⟨(5 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y6 : V := S.vertex (⟨(6 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y7 : V := S.vertex (⟨(7 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let b0 : E := S.edge (⟨(4 : ℕ), by omega⟩ : Fin S.length);
  let b1 : E := S.edge (⟨(5 : ℕ), by omega⟩ : Fin S.length);
  let c0 : E := S.edge (⟨(6 : ℕ), by omega⟩ : Fin S.length);
  (∀ {i j : Fin S.length}, i ≠ j → S.edge i ≠ S.edge j) →
  psi b0 = some g0 →
  psi b1 = some g0 →
  ∀ (p0 : Fin ((↑(⟨(4 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ))),
  G.ends b0 = s(y5, S.vertex (p0.castLT (by omega))) →
  ∀ (p1 : Fin ((↑(⟨(5 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ))),
  G.ends b1 = s(y6, S.vertex (p1.castLT (by omega))) →
  ∀ (f1 f2 f3 : E) (v1 v2 : V),
  psi f1 = some g0 →
  psi f2 = some g0 →
  psi f3 = some g0 →
  G.ends f1 = s(y1, v1) →
  G.ends f2 = s(y4, v2) →
  G.ends f3 = s(y2, y3) →
  b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2 ∨ b0 = f2 ∧ y5 = v2 ∧ b1 = f1 ∧ y6 = v1 →
  c0 ≠ f3 →
  ¬Incident G y7 f1 →
  ¬Incident G y7 f2 →
  ¬Incident G y7 f3 →
  ¬Incident G y7 b0 →
  ¬Incident G y7 b1 →
  ∀ (q : Fin (7 : ℕ)),
  q ≠ (0 : Fin (7 : ℕ)) →
  ∃ (f : E),
  f ≠ c0 ∧
  Incident G (S.vertex (⟨(↑q : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)))) f ∧
  psi f = some g0 ∧
  ¬Incident G y7 f := by
  classical
  intro V E _ _ _ G k e0 phi T N e psi S M hlen g0 y1 y2 y3 y4 y5 y6 y7 b0 b1 c0 hedge_ne h4' h5'
      p0 hb0ends p1 hb1ends f1 f2 f3 v1 v2 hf1color hf2color hf3color hf1ends' hf2ends' hf3ends'
      horient hc0_ne_f3 hno_f1 hno_f2 hno_f3 hno_b0 hno_b1 q hq
  have hcases : q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨
      q.val = 4 ∨ q.val = 5 ∨ q.val = 6 := by
    have hq0 : q.val ≠ 0 := by intro h; apply hq; apply Fin.ext; exact h
    omega
  rcases hcases with h | h | h | h | h | h
  · refine ⟨f1, ?_, ?_, hf1color, hno_f1⟩
    · rcases horient with ho | ho
      · rw [← ho.1]
        apply hedge_ne
        norm_num
      · rw [← ho.2.2.1]
        apply hedge_ne
        norm_num
    · rw [Incident, hf1ends']
      have hv : S.vertex ⟨q.val, by omega⟩ = y1 := by
        apply congrArg S.vertex; apply Fin.ext; simpa [y1] using h
      rw [hv]
      simp
  · refine ⟨f3, hc0_ne_f3.symm, ?_, hf3color, hno_f3⟩
    rw [Incident, hf3ends']
    have hv : S.vertex ⟨q.val, by omega⟩ = y2 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y2] using h
    rw [hv]
    simp
  · refine ⟨f3, hc0_ne_f3.symm, ?_, hf3color, hno_f3⟩
    rw [Incident, hf3ends']
    have hv : S.vertex ⟨q.val, by omega⟩ = y3 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y3] using h
    rw [hv]
    simp
  · refine ⟨f2, ?_, ?_, hf2color, hno_f2⟩
    · rcases horient with ho | ho
      · rw [← ho.2.2.1]
        apply hedge_ne
        norm_num
      · rw [← ho.1]
        apply hedge_ne
        norm_num
    · rw [Incident, hf2ends']
      have hv : S.vertex ⟨q.val, by omega⟩ = y4 := by
        apply congrArg S.vertex; apply Fin.ext; simpa [y4] using h
      rw [hv]
      simp
  · refine ⟨b0, ?_, ?_, h4', hno_b0⟩
    · apply hedge_ne
      norm_num
    · rw [Incident, hb0ends]
      have hv : S.vertex ⟨q.val, by omega⟩ = y5 := by
        apply congrArg S.vertex; apply Fin.ext; simpa [y5] using h
      rw [hv]
      simp
  · refine ⟨b1, ?_, ?_, h5', hno_b1⟩
    · apply hedge_ne
      norm_num
    · rw [Incident, hb1ends]
      have hv : S.vertex ⟨q.val, by omega⟩ = y6 := by
        apply congrArg S.vertex; apply Fin.ext; simpa [y6] using h
      rw [hv]
      simp

theorem helper_hcoverAlpha_795.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (_ : NormalGlobalMaximumTriple G k e0 phi T) {e : E} (psi : PartialEdgeColoring E k)
    (S : TreeSequence G e) (M : NormalGlobalMaximumTriple G k e psi S)
    (hlen : S.length = (8 : ℕ)),
  let y1 : V := S.vertex (⟨(1 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y2 : V := S.vertex (⟨(2 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y3 : V := S.vertex (⟨(3 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y4 : V := S.vertex (⟨(4 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y5 : V := S.vertex (⟨(5 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y6 : V := S.vertex (⟨(6 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y7 : V := S.vertex (⟨(7 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let a1 : E := S.edge (⟨(1 : ℕ), by omega⟩ : Fin S.length);
  let a3 : E := S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length);
  let c0 : E := S.edge (⟨(6 : ℕ), by omega⟩ : Fin S.length);
  (∀ {i j : Fin S.length}, i ≠ j → S.edge i ≠ S.edge j) →
  ∀ (_ : Fin ((↑(⟨(4 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ)))
    (_ : Fin ((↑(⟨(5 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ))) (alpha56 : E),
  psi alpha56 = some M.alpha →
  G.ends alpha56 = s(y5, y6) →
  G.ends a1 = s(y1, y2) →
  G.ends a3 = s(y3, y4) →
  psi a1 = some M.alpha →
  psi a3 = some M.alpha →
  c0 ≠ alpha56 →
  ¬Incident G y7 a1 →
  ¬Incident G y7 a3 →
  ¬Incident G y7 alpha56 →
  ∀ (q : Fin (7 : ℕ)),
  q ≠ (0 : Fin (7 : ℕ)) →
  ∃ (f : E),
  f ≠ c0 ∧
  Incident G (S.vertex (⟨(↑q : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)))) f ∧
  psi f = some M.alpha ∧
  ¬Incident G y7 f := by
  classical
  intro V E _ _ _ G k e0 phi T N e psi S M hlen y1 y2 y3 y4 y5 y6 y7 a1 a3 c0 hedge_ne p0 p1
      alpha56 halpha56color halpha56ends' ha1ends ha3ends ha1color ha3color hc0_ne_alpha56 hno_a1
      hno_a3 hno_alpha56 q hq
  have hcases : q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨
      q.val = 4 ∨ q.val = 5 ∨ q.val = 6 := by
    have hq0 : q.val ≠ 0 := by intro h; apply hq; apply Fin.ext; exact h
    omega
  rcases hcases with h | h | h | h | h | h
  · refine ⟨a1, by apply hedge_ne; norm_num, ?_, ha1color, hno_a1⟩
    rw [Incident, ha1ends]
    have hv : S.vertex ⟨q.val, by omega⟩ = y1 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y1] using h
    rw [hv]; simp
  · refine ⟨a1, by apply hedge_ne; norm_num, ?_, ha1color, hno_a1⟩
    rw [Incident, ha1ends]
    have hv : S.vertex ⟨q.val, by omega⟩ = y2 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y2] using h
    rw [hv]; simp
  · refine ⟨a3, by apply hedge_ne; norm_num, ?_, ha3color, hno_a3⟩
    rw [Incident, ha3ends]
    have hv : S.vertex ⟨q.val, by omega⟩ = y3 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y3] using h
    rw [hv]; simp
  · refine ⟨a3, by apply hedge_ne; norm_num, ?_, ha3color, hno_a3⟩
    rw [Incident, ha3ends]
    have hv : S.vertex ⟨q.val, by omega⟩ = y4 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y4] using h
    rw [hv]; simp
  · refine ⟨alpha56, hc0_ne_alpha56.symm, ?_, halpha56color, hno_alpha56⟩
    rw [Incident, halpha56ends']
    have hv : S.vertex ⟨q.val, by omega⟩ = y5 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y5] using h
    rw [hv]; simp
  · refine ⟨alpha56, hc0_ne_alpha56.symm, ?_, halpha56color, hno_alpha56⟩
    rw [Incident, halpha56ends']
    have hv : S.vertex ⟨q.val, by omega⟩ = y6 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y6] using h
    rw [hv]; simp

theorem helper_hcoverBeta_834.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (_ : NormalGlobalMaximumTriple G k e0 phi T) {e : E} (psi : PartialEdgeColoring E k)
    (S : TreeSequence G e) (M : NormalGlobalMaximumTriple G k e psi S)
    (hlen : S.length = (8 : ℕ)),
  let y0 : V := S.vertex (⟨(0 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y2 : V := S.vertex (⟨(2 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y3 : V := S.vertex (⟨(3 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y4 : V := S.vertex (⟨(4 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y5 : V := S.vertex (⟨(5 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y6 : V := S.vertex (⟨(6 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y7 : V := S.vertex (⟨(7 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let a2 : E := S.edge (⟨(2 : ℕ), by omega⟩ : Fin S.length);
  let c0 : E := S.edge (⟨(6 : ℕ), by omega⟩ : Fin S.length);
  (∀ {i j : Fin S.length}, i ≠ j → S.edge i ≠ S.edge j) →
  ∀ (_ : Fin ((↑(⟨(4 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ)))
    (_ : Fin ((↑(⟨(5 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ))) (beta56 : E),
  psi beta56 = some M.beta →
  G.ends beta56 = s(y5, y6) →
  G.ends a2 = s(y2, y3) →
  G.ends M.closingEdge = s(y4, y0) →
  psi a2 = some M.beta →
  psi M.closingEdge = some M.beta →
  c0 ≠ beta56 →
  c0 ≠ M.closingEdge →
  ¬Incident G y7 a2 →
  ¬Incident G y7 M.closingEdge →
  ¬Incident G y7 beta56 →
  ∀ (q : Fin (7 : ℕ)),
  q ≠ (1 : Fin (7 : ℕ)) →
  ∃ (f : E),
  f ≠ c0 ∧
  Incident G (S.vertex (⟨(↑q : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)))) f ∧
  psi f = some M.beta ∧
  ¬Incident G y7 f := by
  classical
  intro V E _ _ _ G k e0 phi T N e psi S M hlen y0 y2 y3 y4 y5 y6 y7 a2 c0 hedge_ne p0 p1 beta56
      hbeta56color hbeta56ends' ha2ends hclosingEnds ha2color hclosingColor hc0_ne_beta56
      hc0_ne_closing hno_a2 hno_close hno_beta56 q hq
  have hcases : q.val = 0 ∨ q.val = 2 ∨ q.val = 3 ∨
      q.val = 4 ∨ q.val = 5 ∨ q.val = 6 := by
    have hq1 : q.val ≠ 1 := by intro h; apply hq; apply Fin.ext; exact h
    omega
  rcases hcases with h | h | h | h | h | h
  · refine ⟨M.closingEdge, hc0_ne_closing.symm, ?_, hclosingColor, hno_close⟩
    rw [Incident, hclosingEnds]
    have hv : S.vertex ⟨q.val, by omega⟩ = y0 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y0] using h
    rw [hv]; simp
  · refine ⟨a2, by apply hedge_ne; norm_num, ?_, ha2color, hno_a2⟩
    rw [Incident, ha2ends]
    have hv : S.vertex ⟨q.val, by omega⟩ = y2 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y2] using h
    rw [hv]; simp
  · refine ⟨a2, by apply hedge_ne; norm_num, ?_, ha2color, hno_a2⟩
    rw [Incident, ha2ends]
    have hv : S.vertex ⟨q.val, by omega⟩ = y3 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y3] using h
    rw [hv]; simp
  · refine ⟨M.closingEdge, hc0_ne_closing.symm, ?_, hclosingColor, hno_close⟩
    rw [Incident, hclosingEnds]
    have hv : S.vertex ⟨q.val, by omega⟩ = y4 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y4] using h
    rw [hv]; simp
  · refine ⟨beta56, hc0_ne_beta56.symm, ?_, hbeta56color, hno_beta56⟩
    rw [Incident, hbeta56ends']
    have hv : S.vertex ⟨q.val, by omega⟩ = y5 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y5] using h
    rw [hv]; simp
  · refine ⟨beta56, hc0_ne_beta56.symm, ?_, hbeta56color, hno_beta56⟩
    rw [Incident, hbeta56ends']
    have hv : S.vertex ⟨q.val, by omega⟩ = y6 := by
      apply congrArg S.vertex; apply Fin.ext; simpa [y6] using h
    rw [hv]; simp

theorem helper_last_pair_edge_881.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (_ : NormalGlobalMaximumTriple G k e0 phi T),
  let _ : DecidableEq V := Classical.decEq V;
  ∀ {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence G e)
    (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
  IsProperEdgeColoring G psi →
  ColoredVertexSetElementary G psi (TreeSequenceVertexSet S) →
  ColoredVertexSetClosed G psi (TreeSequenceVertexSet S) →
  let y7 : V := S.vertex (⟨(7 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y8 : V := S.vertex (⟨(8 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let c0 : E := S.edge (⟨(6 : ℕ), by omega⟩ : Fin S.length);
  (∀ {i j : Fin (S.length + (1 : ℕ))}, i ≠ j → S.vertex i ≠ S.vertex j) →
  (∀ (i : Fin (S.length + (1 : ℕ))), S.vertex i ∈ TreeSequenceVertexSet S) →
  (∀ {c : Fin k} {v : V} {f : E},
      c ∈ MissingColors G psi v → Incident G v f → psi f ≠ some c) →
  ∀ (_ : Fin ((↑(⟨(4 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ)))
    (_ : Fin ((↑(⟨(5 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ))) (c : Fin k)
    (m : Fin (7 : ℕ)),
  c ∈ MissingColors G psi (S.vertex (⟨(↑m : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)))) →
  (∀ (q : Fin (7 : ℕ)),
      q ≠ m →
        ∃ (f : E),
          f ≠ c0 ∧
            Incident G (S.vertex (⟨(↑q : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)))) f ∧
              psi f = some c ∧ ¬Incident G y7 f) →
  ∃ (f : E),
  G.ends f = s(y7, y8) ∧
  psi f = some c := by
  classical
  intro V E _ _ _ G k e0 phi T N this e psi S M hlen hproper helem hclosed y7 y8 c0 hvertex_ne
      hmem missing_excludes p0 p1 c m hcmiss hcover
  have hmMem : S.vertex ⟨m.val, by omega⟩ ∈ TreeSequenceVertexSet S :=
    hmem (⟨m.val, by omega⟩ : Fin (S.length + 1))
  have hy7Mem : y7 ∈ TreeSequenceVertexSet S := by
    simpa [y7] using hmem (⟨7, by omega⟩ : Fin (S.length + 1))
  have hym7 : S.vertex ⟨m.val, by omega⟩ ≠ y7 := by
    apply hvertex_ne
    apply Fin.ne_of_val_ne
    change m.val ≠ 7
    omega
  have hcnotmissing : c ∉ MissingColors G psi y7 := by
    intro hc7
    have hd := helem hmMem hy7Mem hym7
    exact (Finset.disjoint_left.mp hd) hcmiss hc7
  have hcpresent : c ∈ PresentColors G psi y7 := by
    simpa [MissingColors] using hcnotmissing
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hcpresent
  obtain ⟨f, hfinc, hfcolor⟩ := hcpresent
  obtain ⟨z, hfends⟩ := Sym2.mem_iff_exists.mp hfinc
  have hzT : z ∈ TreeSequenceVertexSet S := by
    by_contra hz
    have hfBoundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet S) := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨y7, hy7Mem, z, hz, hfends⟩
    exact (hclosed hfBoundary hmMem hfcolor) hcmiss
  obtain ⟨q, -, hqz⟩ := Finset.mem_image.mp
    (show z ∈ Finset.image S.vertex Finset.univ from by
      simpa [TreeSequenceVertexSet] using hzT)
  have hq8 : q.val = 8 := by
    have hqbound : q.val < 9 := by
      calc
        q.val < S.length + 1 := q.isLt
        _ = 9 := by omega
    by_contra hne
    by_cases hq7 : q.val = 7
    · have hz7 : z = y7 := by
        rw [← hqz]
        apply congrArg S.vertex
        apply Fin.ext
        simpa [y7] using hq7
      exact G.loopless f y7 (by simpa [hz7] using hfends)
    · have hqlt : q.val < 7 := by omega
      let q7 : Fin 7 := ⟨q.val, hqlt⟩
      have hzq : z = S.vertex ⟨q7.val, by omega⟩ := by
        calc
          z = S.vertex q := hqz.symm
          _ = S.vertex ⟨q7.val, by omega⟩ := by
            apply congrArg S.vertex
            apply Fin.ext
            rfl
      by_cases hqm : q7 = m
      · have hincm : Incident G (S.vertex ⟨m.val, by omega⟩) f := by
          rw [Incident, hfends, hzq]
          have hv : S.vertex ⟨q7.val, by omega⟩ =
              S.vertex ⟨m.val, by omega⟩ := by
            apply congrArg S.vertex
            apply Fin.ext
            simpa using congrArg Fin.val hqm
          rw [hv]
          simp
        exact (missing_excludes hcmiss hincm) hfcolor
      · obtain ⟨g, _, hginc, hgcolor, hgno7⟩ := hcover q7 hqm
        have hfne : f ≠ g := by
          intro heq
          exact hgno7 (heq ▸ hfinc)
        have hfincq : Incident G (S.vertex ⟨q7.val, by omega⟩) f := by
          rw [Incident, hfends, hzq]
          simp
        exact (hproper hfne ⟨S.vertex ⟨q7.val, by omega⟩,
          hfincq, hginc⟩ hfcolor) hgcolor
  have hzy8 : z = y8 := by
    rw [← hqz]
    apply congrArg S.vertex
    apply Fin.ext
    simpa [y8] using hq8
  exact ⟨f, by simpa [hzy8] using hfends, hfcolor⟩

theorem helper_newEdge_injective_1199.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
    [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (_ : NormalGlobalMaximumTriple G k e0 phi T) {e : E} (psi : PartialEdgeColoring E k)
    (S : TreeSequence G e) (_ : NormalGlobalMaximumTriple G k e psi S)
    (hlen : S.length = (8 : ℕ)),
  let y5 : V := S.vertex (⟨(5 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let y6 : V := S.vertex (⟨(6 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)));
  let a1 : E := S.edge (⟨(1 : ℕ), by omega⟩ : Fin S.length);
  let a3 : E := S.edge (⟨(3 : ℕ), by omega⟩ : Fin S.length);
  let b0 : E := S.edge (⟨(4 : ℕ), by omega⟩ : Fin S.length);
  let b1 : E := S.edge (⟨(5 : ℕ), by omega⟩ : Fin S.length);
  let c0 : E := S.edge (⟨(6 : ℕ), by omega⟩ : Fin S.length);
  let c1 : E := S.edge (⟨(7 : ℕ), by omega⟩ : Fin S.length);
  ∀ (_ : Fin ((↑(⟨(4 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ)))
    (_ : Fin ((↑(⟨(5 : ℕ), by omega⟩ : Fin S.length) : ℕ) + (1 : ℕ))) (f1 f2 : E)
    (v1 v2 : V),
  b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2 ∨ b0 = f2 ∧ y5 = v2 ∧ b1 = f1 ∧ y6 = v1 →
  ∀ (beta56 : E),
  let a0 : E := S.edge (⟨(0 : ℕ), by omega⟩ : Fin S.length);
  a0 = e →
  beta56 ≠ a0 →
  beta56 ≠ f1 →
  beta56 ≠ f2 →
  beta56 ≠ a1 →
  beta56 ≠ a3 →
  beta56 ≠ c0 →
  beta56 ≠ c1 →
  let edgeList : List E := [a0, f1, beta56, f2, a1, a3, c0, c1];
  ∀ (hedgeListLength : edgeList.length = (8 : ℕ)),
  let newEdge : Fin (8 : ℕ) → E := fun (i : Fin (8 : ℕ)) ↦
    edgeList.get (Fin.cast (by omega) i);
  (∀ (i j : Fin S.length), S.edge i = S.edge j ↔ i = j) →
  Function.Injective newEdge := by
  classical
  intro V E _ _ _ G k e0 phi T N e psi S M hlen y5 y6 a1 a3 b0 b1 c0 c1 p0 p1 f1 f2 v1 v2 horient
      beta56 a0 ha0eq hbeta_a0 hbeta_f1 hbeta_f2 hbeta_a1 hbeta_a3 hbeta_c0 hbeta_c1 edgeList
      hedgeListLength newEdge hedge_iff
  have hnodup : edgeList.Nodup := by
    rcases horient with ho | ho
    · have hb0beta : b0 ≠ beta56 := by
        intro hh
        exact hbeta_f1 (hh.symm.trans ho.1)
      have hbeta_b1 : beta56 ≠ b1 := by
        intro hh
        exact hbeta_f2 (hh.trans ho.2.2.1)
      simp [edgeList, ← ho.1, ← ho.2.2.1, a0, a1,
        a3, b0, b1, c0, c1, hedge_iff, hbeta_a1, hbeta_a3, hbeta_c0, hbeta_c1,
        Ne.symm hbeta_a0, hb0beta, hbeta_b1]
    · have hb1beta : b1 ≠ beta56 := by
        intro hh
        exact hbeta_f1 (hh.symm.trans ho.2.2.1)
      have hbeta_b0 : beta56 ≠ b0 := by
        intro hh
        exact hbeta_f2 (hh.trans ho.1)
      simp [edgeList, ← ho.2.2.1, ← ho.1, a0, a1,
        a3, b0, b1, c0, c1, hedge_iff, hbeta_a1, hbeta_a3, hbeta_c0, hbeta_c1,
        Ne.symm hbeta_a0, hb1beta, hbeta_b0]
  intro i j hij
  have hcast := hnodup.injective_get hij
  apply Fin.ext
  simpa using congrArg Fin.val hcast

theorem helper_horient_1122.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y5 : V := S.vertex (⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y6 : V := S.vertex (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    let b1 : E := S.edge (⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length);
    ∀ (f1 f2 : E) (v1 v2 : V), (
    ∀ (j : Fin (2 : ℕ)), S.edge (⟨(4 : ℕ) + (↑j : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) + (↑j :
        ℕ) < S.length) ↦
    by
                    omega
    ⟩ : Fin S.length) = f1 ∧ S.vertex (⟨(5 : ℕ) + (↑j : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) + (↑j :
        ℕ) < S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))) = v1 ∨ S.edge (⟨(4 : ℕ) + (↑j : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) + (↑j :
        ℕ) < S.length) ↦
    by
                    omega
    ⟩ : Fin S.length) = f2 ∧ S.vertex (⟨(5 : ℕ) + (↑j : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) + (↑j :
        ℕ) < S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ))) = v2) → b0 ≠ b1 → b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2 ∨ b0 =
        f2 ∧ y5 = v2 ∧ b1 = f1 ∧ y6 = v1 := by
  classical
  intro V E _ _ _ G k e psi S M hlen y5 y6 b0 b1 f1 f2 v1 v2 classifyFirst hb01ne
  have h0 := classifyFirst (0 : Fin 2)
  have h1 := classifyFirst (1 : Fin 2)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact False.elim (hb01ne (by simpa [b0, b1] using h0.1.trans h1.1.symm))
  · left
    simpa [b0, b1, y5, y6] using ⟨h0.1, h0.2, h1.1, h1.2⟩
  · right
    simpa [b0, b1, y5, y6] using ⟨h0.1, h0.2, h1.1, h1.2⟩
  · exact False.elim (hb01ne (by simpa [b0, b1] using h0.1.trans h1.1.symm))

theorem helper_ha1ends_1148.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (M : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)), M.height =
        (5 : ℕ) →
    let y1 : V := S.vertex (⟨(1 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y2 : V := S.vertex (⟨(2 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(2 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let a1 : E := S.edge (⟨(1 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length); G.ends a1 = s(y1, y2) := by
  classical
  intro V E _ _ _ G k e psi S M hlen hheight y1 y2 a1
  let r : Fin S.length := ⟨1, by omega⟩
  have ht := M.trunk_edge_ends r (by simp [r]) (by simp [hheight, r])
  have hs : r.succ = (⟨2, by omega⟩ : Fin (S.length + 1)) := Fin.ext rfl
  rw [hs] at ht
  simpa [a1, y1, y2, r] using ht

theorem helper_ha2ends_1154.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (M : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)), M.height =
        (5 : ℕ) →
    let y2 : V := S.vertex (⟨(2 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(2 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y3 : V := S.vertex (⟨(3 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let a2 : E := S.edge (⟨(2 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(2 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length); G.ends a2 = s(y2, y3) := by
  classical
  intro V E _ _ _ G k e psi S M hlen hheight y2 y3 a2
  let r : Fin S.length := ⟨2, by omega⟩
  have ht := M.trunk_edge_ends r (by simp [r]) (by simp [hheight, r])
  have hs : r.succ = (⟨3, by omega⟩ : Fin (S.length + 1)) := Fin.ext rfl
  rw [hs] at ht
  simpa [a2, y2, y3, r] using ht

theorem helper_ha3ends_1160.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (M : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)), M.height =
        (5 : ℕ) →
    let y3 : V := S.vertex (⟨(3 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y4 : V := S.vertex (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let a3 : E := S.edge (⟨(3 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length) ↦
    by omega
    ⟩ : Fin S.length); G.ends a3 = s(y3, y4) := by
  classical
  intro V E _ _ _ G k e psi S M hlen hheight y3 y4 a3
  let r : Fin S.length := ⟨3, by omega⟩
  have ht := M.trunk_edge_ends r (by simp [r]) (by simp [hheight, r])
  have hs : r.succ = (⟨4, by omega⟩ : Fin (S.length + 1)) := Fin.ext rfl
  rw [hs] at ht
  simpa [a3, y3, y4, r] using ht

theorem helper_hab_1198.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (M : NormalGlobalMaximumTriple G k e psi S), S.length = (8 : ℕ) →
        ColoredVertexSetElementary G psi (TreeSequenceVertexSet S) → (
    ∀ {i j : Fin (S.length + (1 : ℕ))}, i ≠ j → S.vertex i ≠ S.vertex j) → (
    ∀ (i : Fin (S.length + (1 : ℕ))), S.vertex i ∈ TreeSequenceVertexSet S) → M.alpha ≠ M.beta := by
  classical
  intro V E _ _ _ G k e psi S M hlen helem hvertex_ne hmem hEq
  have hd := helem (hmem (⟨0, by omega⟩ : Fin (S.length + 1)))
    (hmem (⟨1, by omega⟩ : Fin (S.length + 1)))
    (by apply hvertex_ne; norm_num)
  exact (Finset.disjoint_left.mp hd) M.alpha_missing
    (by simpa [hEq] using M.beta_missing)

theorem helper_no_y7_of_ends_1435.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y7 : V := S.vertex (⟨(7 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(7 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    ∀ {f : E} {u v : V}, G.ends f = s(u, v) → u ≠ y7 → v ≠ y7 → ¬Incident G y7 f := by
  classical
  intro V E _ _ _ G k e psi S M hlen y7 f u v hf hu hv hinc
  rw [Incident, hf] at hinc
  rcases Sym2.mem_iff.mp hinc with h | h
  · exact hu h.symm
  · exact hv h.symm

theorem helper_continuation_2887.{u_1, u_2} :
    helperContinuation2887Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k hgraphHeight Good e psi S M hbal hlen hheight g0 y0 y1 y2 y3 y4 y5 y6 y7 y8
      a1 a2 a3 b0 b1 c0 c1 hg0' f1 f2 v1 v2 hf1color hf2color hf1ends' hf2ends' horient beta56
      hbeta56ends hbeta56color ha1ends ha2ends ha3ends ha1color ha2color ha3color hab hg0alpha
      hg0beta r6' w g1 hc1color hc0color' hwmissing' hg10 hg1alpha hg1beta g0last hg0lastEnds
      hg0lastColor alphaLast halphaLastEnds halphaLastColor betaLast hbetaLastEnds hbetaLastColor
      a0 rebase
  by_cases hwbase : 5 ≤ w.val
  · obtain ⟨S', M', hlen', hheight', hbal', hv0', hv1', hv2', hv3',
        hv4', hv5', hv6', hv7', hv8', he0', he1', he2', he3', he4',
        he5', he6', he7', hMalpha, hMbeta⟩ := rebase hwbase
    have hwcases : w.val = 5 ∨ w.val = 6 := by
      have hwlt : w.val < 7 := by simp [r6']
      omega
    obtain ⟨m', hmvertex⟩ : ∃ m' : Fin 5,
        S'.vertex ⟨m'.val, by omega⟩ = S.vertex ⟨w.val, by omega⟩ := by
      rcases hwcases with hw5 | hw6
      · rcases horient with ho | ho
        · refine ⟨2, ?_⟩
          calc
            S'.vertex ⟨(2 : Fin 5).val, by omega⟩ =
                S'.vertex ⟨2, by omega⟩ := by congr 1
            _ = v1 := hv2'
            _ = y5 := ho.2.1.symm
            _ = S.vertex ⟨w.val, by omega⟩ := by
              apply congrArg S.vertex
              apply Fin.ext
              simpa [y5] using hw5.symm
        · refine ⟨3, ?_⟩
          calc
            S'.vertex ⟨(3 : Fin 5).val, by omega⟩ =
                S'.vertex ⟨3, by omega⟩ := by congr 1
            _ = v2 := hv3'
            _ = y5 := ho.2.1.symm
            _ = S.vertex ⟨w.val, by omega⟩ := by
              apply congrArg S.vertex
              apply Fin.ext
              simpa [y5] using hw5.symm
      · rcases horient with ho | ho
        · refine ⟨3, ?_⟩
          calc
            S'.vertex ⟨(3 : Fin 5).val, by omega⟩ =
                S'.vertex ⟨3, by omega⟩ := by congr 1
            _ = v2 := hv3'
            _ = y6 := ho.2.2.2.symm
            _ = S.vertex ⟨w.val, by omega⟩ := by
              apply congrArg S.vertex
              apply Fin.ext
              simpa [y6] using hw6.symm
        · refine ⟨2, ?_⟩
          calc
            S'.vertex ⟨(2 : Fin 5).val, by omega⟩ =
                S'.vertex ⟨2, by omega⟩ := by congr 1
            _ = v1 := hv2'
            _ = y6 := ho.2.2.2.symm
            _ = S.vertex ⟨w.val, by omega⟩ := by
              apply congrArg S.vertex
              apply Fin.ext
              simpa [y6] using hw6.symm
    refine ⟨e, psi, S', M', ?_⟩
    refine P2968_T2_ScheideOrderNineBlockCompletion G k psi S' M' hbal' hgraphHeight hlen'
        hheight' M.alpha g1
      (by rw [hv0']; simpa [y0] using M.alpha_missing) m'
      (by rw [hmvertex]; exact hwmissing')
      (by rw [hMalpha]; exact hg0alpha.symm)
      (by rw [hMbeta]; exact hab)
      (by rw [hMalpha]; exact hg10)
      (by rw [hMbeta]; exact hg1beta)
      hg1alpha a1 a3 a2 alphaLast g0last betaLast y2 y3
      (by simpa only [hv1'] using ha1ends)
      (by simpa only [hv4', Sym2.eq_swap] using ha3ends)
      ha1color ha3color ha2ends
      (by rw [hMbeta]; exact ha2color)
      (by simpa only [hv7', hv8'] using halphaLastEnds)
      halphaLastColor
      (by simpa only [hv7', hv8'] using hg0lastEnds)
      (by rw [hMalpha]; exact hg0lastColor)
      (by simpa only [hv7', hv8'] using hbetaLastEnds)
      (by rw [hMbeta]; exact hbetaLastColor)
      (Or.inl ⟨he4', hv5', he5', hv6'⟩) ?_
    intro j
    fin_cases j
    · simpa only using (he6' ▸ hc0color')
    · simpa only using (he7' ▸ hc1color)
  · have hwlt : w.val < 5 := by omega
    let m' : Fin 5 := ⟨w.val, hwlt⟩
    refine ⟨e, psi, S, M, ?_⟩
    refine P2968_T2_ScheideOrderNineBlockCompletion G k psi S M hbal hgraphHeight hlen hheight g0
        g1 hg0' m'
      (by simpa [m'] using hwmissing') hg0alpha hg0beta hg1alpha hg1beta
      hg10 f1 f2 beta56 g0last alphaLast betaLast v1 v2 hf1ends' hf2ends'
      hf1color hf2color hbeta56ends hbeta56color hg0lastEnds hg0lastColor
      halphaLastEnds halphaLastColor
      hbetaLastEnds hbetaLastColor
      (by simpa [b0, b1, y5, y6] using horient) ?_
    intro j
    fin_cases j
    · simpa [c0] using hc0color'
    · simpa [c1] using hc1color

theorem helper_nv2_3221.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y5 : V := S.vertex (⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y6 : V := S.vertex (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let b1 : E := S.edge (⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 f2 : E) (v1 v2 : V),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    by
        omega
    ⟩ : Fin S.length);
    ∀ (_ : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by
        omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        Fin (9 : ℕ) → Fin (S.length + (1 : ℕ))) ((permA : Fin (9 : ℕ) → Fin (9 : ℕ)) i)) else
        S.vertex ((cast9 : Fin (9 : ℕ) → Fin (S.length + (1 : ℕ))) ((permB : Fin (9 : ℕ) → Fin (9
        : ℕ)) i)); (b0 = f1 → y5 = v1 ∧ b1 = f2 ∧ y6 = v2) → (b0 ≠ f1 → y5 = v2 ∧ b1 = f1 ∧ y6 =
        v1) → (
    ∀ (i : Fin (9 : ℕ)) (q : Fin (S.length + (1 : ℕ))), (↑i : ℕ) = (↑q : ℕ) → S.vertex ((cast9 :
        Fin (9 : ℕ) → Fin (S.length + (1 : ℕ))) i) = S.vertex q) → newVertex (2 : Fin (9 : ℕ)) =
        v1 := by
  classical
  intro V E _ _ _ G k e psi S M hlen y5 y6 b0 b1 f1 f2 v1 v2 r6' w cast9 permA permB newVertex
      hselectA hselectB vertex_cast9
  by_cases hb : b0 = f1
  · calc
      newVertex 2 = y5 := by
        simp only [newVertex, ite_eq_left hb, y5]
        apply vertex_cast9
        simp [permA, Equiv.swap_apply_def]
      _ = v1 := (hselectA hb).1
  · calc
      newVertex 2 = y6 := by
        simp only [newVertex, ite_eq_right hb, y6]
        apply vertex_cast9
        simp [permB, Equiv.swap_apply_def]
      _ = v1 := (hselectB hb).2.2

theorem helper_nv3_3235.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y5 : V := S.vertex (⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y6 : V := S.vertex (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let b1 : E := S.edge (⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 f2 : E) (v1 v2 : V),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    by
        omega
    ⟩ : Fin S.length);
    ∀ (_ : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by
        omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        Fin (9 : ℕ) → Fin (S.length + (1 : ℕ))) ((permA : Fin (9 : ℕ) → Fin (9 : ℕ)) i)) else
        S.vertex ((cast9 : Fin (9 : ℕ) → Fin (S.length + (1 : ℕ))) ((permB : Fin (9 : ℕ) → Fin (9
        : ℕ)) i)); (b0 = f1 → y5 = v1 ∧ b1 = f2 ∧ y6 = v2) → (b0 ≠ f1 → y5 = v2 ∧ b1 = f1 ∧ y6 =
        v1) → (
    ∀ (i : Fin (9 : ℕ)) (q : Fin (S.length + (1 : ℕ))), (↑i : ℕ) = (↑q : ℕ) → S.vertex ((cast9 :
        Fin (9 : ℕ) → Fin (S.length + (1 : ℕ))) i) = S.vertex q) → newVertex (3 : Fin (9 : ℕ)) =
        v2 := by
  classical
  intro V E _ _ _ G k e psi S M hlen y5 y6 b0 b1 f1 f2 v1 v2 r6' w cast9 permA permB newVertex
      hselectA hselectB vertex_cast9
  by_cases hb : b0 = f1
  · calc
      newVertex 3 = y6 := by
        simp only [newVertex, ite_eq_left hb, y6]
        apply vertex_cast9
        simp [permA, Equiv.swap_apply_def]
      _ = v2 := (hselectA hb).2.2
  · calc
      newVertex 3 = y5 := by
        simp only [newVertex, ite_eq_right hb, y5]
        apply vertex_cast9
        simp [permB, Equiv.swap_apply_def]
      _ = v2 := (hselectB hb).1

theorem helper_firstSeven_3311.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y0 : V := S.vertex (⟨(0 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y1 : V := S.vertex (⟨(1 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y2 : V := S.vertex (⟨(2 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(2 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y3 : V := S.vertex (⟨(3 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y4 : V := S.vertex (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y5 : V := S.vertex (⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y6 : V := S.vertex (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let b1 : E := S.edge (⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 f2 : E) (v1 v2 : V), b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2 ∨ b0 = f2 ∧ y5 = v2 ∧ b1 = f1
        ∧ y6 = v1 →
    ∀ (_ : E),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    by
        omega
    ⟩ : Fin S.length);
    ∀ (_ : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by
        omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        Fin (9 : ℕ) → Fin (S.length + (1 : ℕ))) ((permA : Fin (9 : ℕ) → Fin (9 : ℕ)) i)) else
        S.vertex ((cast9 : Fin (9 : ℕ) → Fin (S.length + (1 : ℕ))) ((permB : Fin (9 : ℕ) → Fin (9
        : ℕ)) i)); newVertex (0 : Fin (9 : ℕ)) = y0 → newVertex (1 : Fin (9 : ℕ)) = y1 → newVertex
        (2 : Fin (9 : ℕ)) = v1 → newVertex (3 : Fin (9 : ℕ)) = v2 → newVertex (4 : Fin (9 : ℕ)) =
        y4 → newVertex (5 : Fin (9 : ℕ)) = y2 → newVertex (6 : Fin (9 : ℕ)) = y3 →
    ∀ (q : Fin (7 : ℕ)),
    ∃ (t : Fin (7 : ℕ)), newVertex (Fin.castLE (
    by
          omega
    ) t) = S.vertex (⟨(↑q : ℕ),
    by
          omega
    ⟩ : Fin (S.length + (1 : ℕ))) := by
  classical
  intro V E _ _ _ G k e psi S M hlen y0 y1 y2 y3 y4 y5 y6 b0 b1 f1 f2 v1 v2 horient beta56 r6' w
      cast9 permA permB newVertex nv0 nv1 nv2 nv3 nv4 nv5 nv6 q
  fin_cases q
  · exact ⟨0, by change newVertex 0 = y0; exact nv0⟩
  · exact ⟨1, by change newVertex 1 = y1; exact nv1⟩
  · exact ⟨5, by change newVertex 5 = y2; exact nv5⟩
  · exact ⟨6, by change newVertex 6 = y3; exact nv6⟩
  · exact ⟨4, by change newVertex 4 = y4; exact nv4⟩
  · rcases horient with ho | ho
    · exact ⟨2, by change newVertex 2 = y5; rw [nv2]; exact ho.2.1.symm⟩
    · exact ⟨3, by change newVertex 3 = y5; rw [nv3]; exact ho.2.1.symm⟩
  · rcases horient with ho | ho
    · exact ⟨3, by change newVertex 3 = y6; rw [nv3]; exact ho.2.2.2.symm⟩
    · exact ⟨2, by change newVertex 2 = y6; rw [nv2]; exact ho.2.2.2.symm⟩

theorem helper_firstEight_3682.{u_1, u_2} :
    helperFirstEight3682Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e psi S M hlen y7 b0 f1 f2 beta56 r6' r7' w cast9 permA permB newVertex nv7
      firstSeven pc1 q
  by_cases hq : q.val = 7
  · have hqeq : q = (7 : Fin 8) := Fin.ext hq
    subst q
    refine ⟨7, ?_⟩
    change newVertex 7 = y7
    exact nv7
  · let q' : Fin 7 := ⟨q.val, by omega⟩
    obtain ⟨t, ht⟩ := firstSeven q'
    refine ⟨Fin.castLE (by norm_num : 7 ≤ 8) t, ?_⟩
    simpa [q'] using ht

theorem helper_hselectA_3623.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {e : E} (S : TreeSequence G e)
        (hlen : S.length = (8 : ℕ)),
    let y5 : V := S.vertex (⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y6 : V := S.vertex (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let b1 : E := S.edge (⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 f2 : E) (v1 v2 : V) (_ : b0 ≠ b1) (_ : b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2 ∨ b0 = f2 ∧
        y5 = v2 ∧ b1 = f1 ∧ y6 = v1) (_ : b0 = f1), y5 = v1 ∧ b1 = f2 ∧ y6 = v2 := by
  classical
  intro V E G e S hlen y5 y6 b0 b1 f1 f2 v1 v2 hb01ne horient hb
  rcases horient with ho | ho
  · exact ⟨ho.2.1, ho.2.2.1, ho.2.2.2⟩
  · exfalso
    apply hb01ne
    calc
      b0 = f1 := hb
      _ = b1 := ho.2.2.1.symm

theorem helper_nv0_3642.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y0 : V := S.vertex (⟨(0 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 : E),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    by
        omega
    ⟩ : Fin S.length);
    ∀ (_ : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by
        omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permA : (a : Fin (9 : ℕ)) → Fin (9 : ℕ))
        i)) else S.vertex ((cast9 : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permB : (a :
        Fin (9 : ℕ)) → Fin (9 : ℕ)) i));
    ∀ (_ :
    ∀ (i : Fin (9 : ℕ)) (q : Fin (S.length + (1 : ℕ))) (_ : (↑i : ℕ) = (↑q : ℕ)), S.vertex ((cast9
        : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) i) = S.vertex q), newVertex (0 : Fin (9 :
        ℕ)) = y0 := by
  classical
  intro V E _ _ _ G k e psi S M hlen y0 b0 f1 r6' w cast9 permA permB newVertex vertex_cast9
  by_cases hb : b0 = f1
  · simp only [newVertex, ite_eq_left hb, y0]
    apply vertex_cast9
    simp [permA, Equiv.swap_apply_def]
  · simp only [newVertex, ite_eq_right hb, y0]
    apply vertex_cast9
    simp [permB, Equiv.swap_apply_def]

theorem helper_nv1_3650.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y1 : V := S.vertex (⟨(1 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 : E),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    by
        omega
    ⟩ : Fin S.length);
    ∀ (_ : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by
        omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permA : (a : Fin (9 : ℕ)) → Fin (9 : ℕ))
        i)) else S.vertex ((cast9 : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permB : (a :
        Fin (9 : ℕ)) → Fin (9 : ℕ)) i));
    ∀ (_ :
    ∀ (i : Fin (9 : ℕ)) (q : Fin (S.length + (1 : ℕ))) (_ : (↑i : ℕ) = (↑q : ℕ)), S.vertex ((cast9
        : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) i) = S.vertex q), newVertex (1 : Fin (9 :
        ℕ)) = y1 := by
  classical
  intro V E _ _ _ G k e psi S M hlen y1 b0 f1 r6' w cast9 permA permB newVertex vertex_cast9
  by_cases hb : b0 = f1
  · simp only [newVertex, ite_eq_left hb, y1]
    apply vertex_cast9
    simp [permA, Equiv.swap_apply_def]
  · simp only [newVertex, ite_eq_right hb, y1]
    apply vertex_cast9
    simp [permB, Equiv.swap_apply_def]

theorem helper_nv4_3666.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y4 : V := S.vertex (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 : E),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    by
        omega
    ⟩ : Fin S.length);
    ∀ (_ : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by
        omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permA : (a : Fin (9 : ℕ)) → Fin (9 : ℕ))
        i)) else S.vertex ((cast9 : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permB : (a :
        Fin (9 : ℕ)) → Fin (9 : ℕ)) i));
    ∀ (_ :
    ∀ (i : Fin (9 : ℕ)) (q : Fin (S.length + (1 : ℕ))) (_ : (↑i : ℕ) = (↑q : ℕ)), S.vertex ((cast9
        : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) i) = S.vertex q), newVertex (4 : Fin (9 :
        ℕ)) = y4 := by
  classical
  intro V E _ _ _ G k e psi S M hlen y4 b0 f1 r6' w cast9 permA permB newVertex vertex_cast9
  by_cases hb : b0 = f1
  · simp only [newVertex, ite_eq_left hb, y4]
    apply vertex_cast9
    simp [permA, Equiv.swap_apply_def]
  · simp only [newVertex, ite_eq_right hb, y4]
    apply vertex_cast9
    simp [permB, Equiv.swap_apply_def]

theorem helper_nv5_3674.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y2 : V := S.vertex (⟨(2 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(2 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 : E),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    by
        omega
    ⟩ : Fin S.length);
    ∀ (_ : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by
        omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permA : (a : Fin (9 : ℕ)) → Fin (9 : ℕ))
        i)) else S.vertex ((cast9 : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permB : (a :
        Fin (9 : ℕ)) → Fin (9 : ℕ)) i));
    ∀ (_ :
    ∀ (i : Fin (9 : ℕ)) (q : Fin (S.length + (1 : ℕ))) (_ : (↑i : ℕ) = (↑q : ℕ)), S.vertex ((cast9
        : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) i) = S.vertex q), newVertex (5 : Fin (9 :
        ℕ)) = y2 := by
  classical
  intro V E _ _ _ G k e psi S M hlen y2 b0 f1 r6' w cast9 permA permB newVertex vertex_cast9
  by_cases hb : b0 = f1
  · simp only [newVertex, ite_eq_left hb, y2]
    apply vertex_cast9
    simp [permA, Equiv.swap_apply_def]
  · simp only [newVertex, ite_eq_right hb, y2]
    apply vertex_cast9
    simp [permB, Equiv.swap_apply_def]

theorem helper_nv6_3682.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y3 : V := S.vertex (⟨(3 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 : E),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    by
        omega
    ⟩ : Fin S.length);
    ∀ (_ : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by
        omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permA : (a : Fin (9 : ℕ)) → Fin (9 : ℕ))
        i)) else S.vertex ((cast9 : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permB : (a :
        Fin (9 : ℕ)) → Fin (9 : ℕ)) i));
    ∀ (_ :
    ∀ (i : Fin (9 : ℕ)) (q : Fin (S.length + (1 : ℕ))) (_ : (↑i : ℕ) = (↑q : ℕ)), S.vertex ((cast9
        : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) i) = S.vertex q), newVertex (6 : Fin (9 :
        ℕ)) = y3 := by
  classical
  intro V E _ _ _ G k e psi S M hlen y3 b0 f1 r6' w cast9 permA permB newVertex vertex_cast9
  by_cases hb : b0 = f1
  · simp only [newVertex, ite_eq_left hb, y3]
    apply vertex_cast9
    simp [permA, Equiv.swap_apply_def]
  · simp only [newVertex, ite_eq_right hb, y3]
    apply vertex_cast9
    simp [permB, Equiv.swap_apply_def]

theorem helper_nv7_3690.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y7 : V := S.vertex (⟨(7 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(7 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 : E),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    by
        omega
    ⟩ : Fin S.length);
    ∀ (_ : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by
        omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permA : (a : Fin (9 : ℕ)) → Fin (9 : ℕ))
        i)) else S.vertex ((cast9 : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permB : (a :
        Fin (9 : ℕ)) → Fin (9 : ℕ)) i));
    ∀ (_ :
    ∀ (i : Fin (9 : ℕ)) (q : Fin (S.length + (1 : ℕ))) (_ : (↑i : ℕ) = (↑q : ℕ)), S.vertex ((cast9
        : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) i) = S.vertex q), newVertex (7 : Fin (9 :
        ℕ)) = y7 := by
  classical
  intro V E _ _ _ G k e psi S M hlen y7 b0 f1 r6' w cast9 permA permB newVertex vertex_cast9
  by_cases hb : b0 = f1
  · simp only [newVertex, ite_eq_left hb, y7]
    apply vertex_cast9
    simp [permA, Equiv.swap_apply_def]
  · simp only [newVertex, ite_eq_right hb, y7]
    apply vertex_cast9
    simp [permB, Equiv.swap_apply_def]

theorem helper_nv8_3698.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y8 : V := S.vertex (⟨(8 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(8 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 : E),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    by
        omega
    ⟩ : Fin S.length);
    ∀ (_ : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by
        omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permA : (a : Fin (9 : ℕ)) → Fin (9 : ℕ))
        i)) else S.vertex ((cast9 : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permB : (a :
        Fin (9 : ℕ)) → Fin (9 : ℕ)) i));
    ∀ (_ :
    ∀ (i : Fin (9 : ℕ)) (q : Fin (S.length + (1 : ℕ))) (_ : (↑i : ℕ) = (↑q : ℕ)), S.vertex ((cast9
        : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) i) = S.vertex q), newVertex (8 : Fin (9 :
        ℕ)) = y8 := by
  classical
  intro V E _ _ _ G k e psi S M hlen y8 b0 f1 r6' w cast9 permA permB newVertex vertex_cast9
  by_cases hb : b0 = f1
  · simp only [newVertex, ite_eq_left hb, y8]
    apply vertex_cast9
    simp [permA, Equiv.swap_apply_def]
  · simp only [newVertex, ite_eq_right hb, y8]
    apply vertex_cast9
    simp [permB, Equiv.swap_apply_def]

theorem helper_hedge_iff_3716.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 : E),
    let r6' : Fin S.length := (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    by
        omega
    ⟩ : Fin S.length);
    ∀ (_ : Fin ((↑r6' : ℕ) + (1 : ℕ))),
    let cast9 : Fin (9 : ℕ) ≃ Fin (S.length + (1 : ℕ)) := finCongr (
    by
        omega
    );
    let permA : Equiv.Perm (Fin (9 : ℕ)) := Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (5 : Fin (9
        : ℕ))) (Equiv.swap (3 : Fin (9 : ℕ)) (6 : Fin (9 : ℕ)));
    let permB : Equiv.Perm (Fin (9 : ℕ)) := (Equiv.trans (Equiv.swap (2 : Fin (9 : ℕ)) (6 : Fin (9
        : ℕ))) (Equiv.swap (2 : Fin (9 : ℕ)) (3 : Fin (9 : ℕ)))).trans (Equiv.swap (2 : Fin (9 :
        ℕ)) (5 : Fin (9 : ℕ)));
    let newVertex : Fin (9 : ℕ) → V := fun (i : Fin (9 : ℕ)) ↦ if b0 = f1 then S.vertex ((cast9 :
        (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permA : (a : Fin (9 : ℕ)) → Fin (9 : ℕ))
        i)) else S.vertex ((cast9 : (a : Fin (9 : ℕ)) → Fin (S.length + (1 : ℕ))) ((permB : (a :
        Fin (9 : ℕ)) → Fin (9 : ℕ)) i)); Function.Injective newVertex := by
  classical
  intro V E _ _ _ G k e psi S M hlen b0 f1 r6' w cast9 permA permB newVertex
  by_cases hb : b0 = f1
  · intro i j hij
    simp only [newVertex, ite_eq_left hb] at hij
    exact permA.injective (cast9.injective (S.vertex_injective hij))
  · intro i j hij
    simp only [newVertex, ite_eq_right hb] at hij
    exact permB.injective (cast9.injective (S.vertex_injective hij))

theorem helper_newEdge_injective_3726.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (_ : NormalGlobalMaximumTriple G k e0 phi T) {e : E} (psi : PartialEdgeColoring E k)
        (S : TreeSequence G e) (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 :
        ℕ)),
    let y5 : V := S.vertex (⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y6 : V := S.vertex (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let a1 : E := S.edge (⟨(1 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let a3 : E := S.edge (⟨(3 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let b0 : E := S.edge (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let b1 : E := S.edge (⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let c0 : E := S.edge (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let c1 : E := S.edge (⟨(7 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(7 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (_ : Fin ((↑(⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length) ↦
    by
                    omega
    ⟩ : Fin S.length) : ℕ) + (1 : ℕ))) (_ : Fin ((↑(⟨(5 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(5 : ℕ) <
        S.length) ↦
    by
                    omega
    ⟩ : Fin S.length) : ℕ) + (1 : ℕ))) (f1 f2 : E) (v1 v2 : V) (_ : b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧
        y6 = v2 ∨ b0 = f2 ∧ y5 = v2 ∧ b1 = f1 ∧ y6 = v1) (beta56 : E),
    let a0 : E := S.edge (⟨(0 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (_ : a0 = e) (_ : beta56 ≠ a0) (_ : beta56 ≠ f1) (_ : beta56 ≠ f2) (_ : beta56 ≠ a1) (_ :
        beta56 ≠ a3) (_ : beta56 ≠ c0) (_ : beta56 ≠ c1),
    let edgeList : List E := [a0, f1, beta56, f2, a1, a3, c0, c1];
    ∀ (hedgeListLength : edgeList.length = (8 : ℕ)),
    let newEdge : Fin (8 : ℕ) → E := fun (i : Fin (8 : ℕ)) ↦ edgeList.get (Fin.cast (Eq.symm
        hedgeListLength) i);
    ∀ (_ :
    ∀ (i j : Fin S.length), S.edge i = S.edge j ↔ i = j), Function.Injective newEdge := by
  classical
  intro V E _ _ _ G k e0 phi T N e psi S M hlen y5 y6 a1 a3 b0 b1 c0 c1 p0 p1 f1 f2 v1 v2 horient
      beta56 a0 ha0eq hbeta_a0 hbeta_f1 hbeta_f2 hbeta_a1 hbeta_a3 hbeta_c0 hbeta_c1 edgeList
      hedgeListLength newEdge hedge_iff
  apply helper_newEdge_injective_1199 <;> assumption
theorem helper_hS'tash_4523.{u_1, u_2} :
    helperHS'tash4523Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e psi S M hlen g0 y0 y1 y2 y3 y4 y7 y8 a1 a3 b0 c0 c1 hg0' f1 f2 v1 v2
      hf1color hf2color hf1ends' hf2ends' beta56 hbeta56ends hbeta56color ha1ends ha3ends ha1color
      ha3color r6' r7' w g1 hc1color hc0color' pc pc' hc0ends a0 ha0eq ha0ends cast9 permA permB
      newVertex edgeList hedgeListLength newEdge nv0 nv1 nv2 nv3 nv4 nv5 nv6 nv7 nv8 ne0 ne1 ne2 ne3
      ne4 ne5 ne6 ne7 newVertex_injective newEdge_injective pc1 pc1' hc1ends tc0 htc0 tc1 htc1 tw S'
      hS'length htwMissing j hj
  fin_cases j
  · simp at hj
  · refine ⟨0, g0, ?_, ?_⟩
    · change psi (newEdge 1) = some g0
      rw [ne1]
      exact hf1color
    · change g0 ∈ MissingColors G psi (newVertex 0)
      rw [nv0]
      exact hg0'
  · refine ⟨1, M.beta, ?_, ?_⟩
    · change psi (newEdge 2) = some M.beta
      rw [ne2]
      exact hbeta56color
    · change M.beta ∈ MissingColors G psi (newVertex 1)
      rw [nv1]
      simpa [y1] using M.beta_missing
  · refine ⟨0, g0, ?_, ?_⟩
    · change psi (newEdge 3) = some g0
      rw [ne3]
      exact hf2color
    · change g0 ∈ MissingColors G psi (newVertex 0)
      rw [nv0]
      exact hg0'
  · refine ⟨0, M.alpha, ?_, ?_⟩
    · change psi (newEdge 4) = some M.alpha
      rw [ne4]
      exact ha1color
    · change M.alpha ∈ MissingColors G psi (newVertex 0)
      rw [nv0]
      simpa [y0] using M.alpha_missing
  · refine ⟨0, M.alpha, ?_, ?_⟩
    · change psi (newEdge 5) = some M.alpha
      rw [ne5]
      exact ha3color
    · change M.alpha ∈ MissingColors G psi (newVertex 0)
      rw [nv0]
      simpa [y0] using M.alpha_missing
  · refine ⟨tw, g1, ?_, ?_⟩
    · change psi (newEdge 6) = some g1
      rw [ne6]
      exact hc0color'
    · have hv : S'.vertex (Fin.castLT tw (by omega)) =
          S'.vertex ⟨tw.val, by omega⟩ := by
          apply congrArg S'.vertex
          apply Fin.ext
          rfl
      rw [hv]
      exact htwMissing
  · refine ⟨Fin.castLE (by norm_num : 7 ≤ 8) tw, g1, ?_, ?_⟩
    · change psi (newEdge 7) = some g1
      rw [ne7]
      exact hc1color
    · have hv : S'.vertex
          (Fin.castLT (Fin.castLE (by norm_num : 7 ≤ 8) tw)
            (lt_trans tw.isLt (by norm_num : 7 < 9))) =
          S'.vertex ⟨tw.val, by omega⟩ := by
          apply congrArg S'.vertex
          apply Fin.ext
          rfl
      rw [hv]
      exact htwMissing

theorem helper_hbetaClose_5054.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
        G e) (M : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
    let y0 : V := S.vertex (⟨(0 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    let y4 : V := S.vertex (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (S.length + (1 : ℕ)));
    ∀ (v1 v2 : V) (_ : v1 ≠ S.vertex (⟨(0 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
                omega
    ⟩ : Fin (S.length + (1 : ℕ)))) (_ : v1 ≠ S.vertex (⟨(4 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        S.length + (1 : ℕ)) ↦
    by
                omega
    ⟩ : Fin (S.length + (1 : ℕ)))) (beta56 : E) (_ : G.ends beta56 = s(v1, v2)) (_ : G.ends
        M.closingEdge = s(y4, y0)), beta56 ≠ M.closingEdge := by
  classical
  intro V E _ _ _ G k e psi S M hlen y0 y4 v1 v2 hv10 hv14 beta56 hbeta56ends hclosingEnds hh
  have he : s(v1, v2) = s(y4, y0) := by
    rw [← hbeta56ends, hh]
    exact hclosingEnds
  rcases Sym2.eq_iff.mp he with hp | hp
  · exact hv14 hp.1
  · exact hv10 hp.1

theorem helper_hf1f2_5119.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) {e : E} (S : TreeSequence G e)
        (hlen : S.length = (8 : ℕ)),
    let a1 : E := S.edge (⟨(1 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let a3 : E := S.edge (⟨(3 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(3 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let c0 : E := S.edge (⟨(6 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(6 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let c1 : E := S.edge (⟨(7 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(7 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    ∀ (f1 f2 beta56 : E),
    let a0 : E := S.edge (⟨(0 : ℕ),
    have _ : (1 : ℕ) ≤ S.length := S.positive;
    have _ : (1 : ℕ) ≤ S.length := S.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        S.length) ↦
    by
            omega
    ⟩ : Fin S.length);
    let edgeList : List E := [a0, f1, beta56, f2, a1, a3, c0, c1];
    ∀ (hedgeListLength : edgeList.length = (8 : ℕ)),
    let newEdge : Fin (8 : ℕ) → E := fun (i : Fin (8 : ℕ)) ↦ edgeList.get (Fin.cast (Eq.symm
        hedgeListLength) i);
    ∀ (_ : newEdge (1 : Fin (8 : ℕ)) = f1) (_ : newEdge (3 : Fin (8 : ℕ)) = f2) (_ :
        Function.Injective newEdge), f1 ≠ f2 := by
  classical
  intro V E G e S hlen a1 a3 c0 c1 f1 f2 beta56 a0 edgeList hedgeListLength newEdge ne1 ne3
      newEdge_injective hh
  have he : newEdge 1 = newEdge 3 := by rw [ne1, ne3, hh]
  have hi := newEdge_injective he
  have hiv := congrArg Fin.val hi
  norm_num at hiv

end GoldbergSeymour.ScheideRebasing

end
