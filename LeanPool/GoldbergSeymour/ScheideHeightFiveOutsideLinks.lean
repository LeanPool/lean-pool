/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.ScheideHeightFiveGammaEdges

public import LeanPool.GoldbergSeymour.ScheideGraphHeight
public import LeanPool.GoldbergSeymour.ScheideKempePathHeightBound
public import LeanPool.GoldbergSeymour.TashkinovOrderBound

/-!
# Scheide Height Five Outside Links

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private abbrev helperContinuation1992Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5
        : ℕ)), ScheideGraphHeight G = (5 : ℕ) →
    ∀ gamma ∈ MissingColors G phi (T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length
        + (1 : ℕ)))),
    ∀ (f1 f2 : E) (v1 v2 : V), phi f1 = some gamma → phi f2 = some gamma → v2 ∈
        TreeSequenceVertexSet T →
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1;
    let a2 : E := T.edge r2;
    let a3 : E := T.edge r3;
    let q : E := N.closingEdge; y0 ≠ y1 → y0 ≠ y2 → y0 ≠ y3 → y0 ≠ y4 → y1 ≠ y2 → y1 ≠ y3 → y1 ≠
        y4 → y2 ≠ y3 → y2 ≠ y4 → y3 ≠ y4 → G.ends a1 = s(y1, y2) → G.ends a2 = s(y2, y3) → G.ends
        a3 = s(y3, y4) → G.ends q = s(y4, y0) → IsProperEdgeColoring G phi → (
    ∀ {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G phi v → Incident G v f → phi f ≠ some c) →
        phi a1 = some N.alpha → a1 ≠ a2 → phi a2 = some N.beta → a2 ≠ a3 → phi a3 = some N.alpha →
        phi q = some N.beta → gamma ≠ N.beta → G.ends f1 = s(y1, v1) → G.ends f2 = s(y4, v2) → v1
        ≠ y0 → v1 ≠ y1 → v1 ≠ y2 → v1 ≠ y3 → v1 ≠ y4 → v2 ≠ y0 → v2 ≠ y1 → v2 ≠ y2 → v2 ≠ y3 → v2
        ≠ y4 → f1 ≠ f2 → v1 ≠ v2 → q ≠ f1 → q ≠ f2 →
    ∀ (p1 : (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), p1.IsPath → (4 : ℕ) ∣
        p1.length → p1.length / (2 : ℕ) + (1 : ℕ) ≤ ScheideGraphHeight G →
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi gamma N.beta;
    let C1 : Set (V ⊕ E) := TwoColorComponent G phi gamma N.beta (Sum.inl y0);
        {z : V ⊕ E | z ∈ p1.support} = C1 → Sum.inl y0 ∈ C1 →
    ∃ (alphaEdge : E) (betaEdge : E), G.ends alphaEdge = s(v1, v2) ∧ phi alphaEdge = some N.alpha
        ∧ G.ends betaEdge = s(v1, v2) ∧ phi betaEdge = some N.beta ∧ alphaEdge ≠ betaEdge

private abbrev helperContinuation2397Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5
        : ℕ)), ScheideGraphHeight G = (5 : ℕ) →
    ∀ (gamma : Fin k) (f1 f2 : E) (v1 v2 : V), v2 ∈ TreeSequenceVertexSet T →
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(1 : ℕ) <
        T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper;
    have this_1 : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(4 : ℕ) <
        T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let q : E := N.closingEdge; G.ends q = s(y4, y0) → G.ends f1 = s(y1, v1) → v2 ≠ y0 → v2 ≠ y1 →
        v2 ≠ y4 →
    ∀ (p1 : (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
    let K8 : Finset (V ⊕ E) := (insert (Sum.inl y0) (insert (Sum.inl y1) (insert (Sum.inl y4)
        (insert (Sum.inl v1) (insert (Sum.inl v2) (insert (Sum.inr q) (insert (Sum.inr f1)
        ({Sum.inr f2} : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) :
        Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)); K8.card = (8 : ℕ) →
    ∀ (iv2 : ℕ) (b : E), Incident G v2 f2 → phi b = some N.beta →
    ∀ (w : V), G.ends b = s(v1, v2) →
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    have this : (1 : ℕ) ≤ T.length := T.positive; Decidable.byContradiction fun (a : ¬(0 : ℕ) <
        T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper;
    by
                     have := GoldbergSeymour.TreeSequence.positive T
                     omega
    ⟩ : Fin (T.length + (1 : ℕ))); N.alpha ≠ N.beta →
    ∀ (pmax : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))),
    let C0 : Set (V ⊕ E) := TwoColorComponent G phi N.alpha N.beta (Sum.inl y0);
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi N.alpha N.beta; (
    ∀ {x z : V ⊕ E}, x ∈ C0 → H0.Adj x z → z ∈ C0) →
    ∀ (p0 : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), Sum.inl v1 ∉ C0 → gamma ≠
        N.alpha →
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
        IsProperEdgeColoring G phi' → phi' f1 = some gamma → phi' f2 = some gamma → phi' q = some
        N.alpha → N.alpha ∈ MissingColors G phi' y1 → (
    ∀ {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G phi' v → Incident G v f → phi' f ≠ some c)
        →
    ∀ (p2 : (TwoColorIncidenceGraph G phi' gamma N.alpha).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), p2.IsPath → (4 : ℕ) ∣
        p2.length → p2.length / (2 : ℕ) + (1 : ℕ) ≤ ScheideGraphHeight G →
    let H2 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi' gamma N.alpha;
    let C2 : Set (V ⊕ E) := TwoColorComponent G phi' gamma N.alpha (Sum.inl y0);
        {z : V ⊕ E | z ∈ p2.support} = C2 → (
    ∀ {x z : V ⊕ E}, x ∈ C2 → H2.Adj x z → z ∈ C2) → (
    ∀ {z : V ⊕ E}, z ∈ C2 → z ∈ p2.support) → Sum.inl y0 ∈ p2.support → Sum.inr q ∈ p2.support →
        Sum.inl y4 ∈ p2.support → Sum.inr f2 ∈ p2.support → Sum.inl v2 ∈ p2.support →
    ∃ (alphaEdge : E) (betaEdge : E), G.ends alphaEdge = s(v1, v2) ∧ phi alphaEdge = some N.alpha
        ∧ G.ends betaEdge = s(v1, v2) ∧ phi betaEdge = some N.beta ∧ alphaEdge ≠ betaEdge

private abbrev helperContinuation2127Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5
        : ℕ)), ScheideGraphHeight G = (5 : ℕ) →
    ∀ gamma ∈ MissingColors G phi (T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length
        + (1 : ℕ)))),
    ∀ (f1 f2 : E) (v1 v2 : V), phi f1 = some gamma → phi f2 = some gamma → v2 ∈
        TreeSequenceVertexSet T →
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper;
    by
             have := GoldbergSeymour.TreeSequence.positive T
             omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper;
    by
             have := GoldbergSeymour.TreeSequence.positive T
             omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper;
    by
             have := GoldbergSeymour.TreeSequence.positive T
             omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper;
    by
             have := GoldbergSeymour.TreeSequence.positive T
             omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper;
    by
             have := GoldbergSeymour.TreeSequence.positive T
             omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper;
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin T.length);
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper;
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper;
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1;
    let a2 : E := T.edge r2;
    let a3 : E := T.edge r3;
    let q : E := N.closingEdge; y0 ≠ y1 → y0 ≠ y2 → y0 ≠ y3 → y0 ≠ y4 → y1 ≠ y2 → y1 ≠ y3 → y1 ≠
        y4 → y2 ≠ y3 → y2 ≠ y4 → y3 ≠ y4 → G.ends a1 = s(y1, y2) → G.ends a2 = s(y2, y3) → G.ends
        a3 = s(y3, y4) → G.ends q = s(y4, y0) → (
    ∀ {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G phi v → Incident G v f → phi f ≠ some c) →
        phi a1 = some N.alpha → a1 ≠ a2 → phi a2 = some N.beta → a2 ≠ a3 → phi a3 = some N.alpha →
        phi q = some N.beta → gamma ≠ N.beta → G.ends f1 = s(y1, v1) → G.ends f2 = s(y4, v2) → v1
        ≠ y0 → v1 ≠ y1 → v1 ≠ y2 → v1 ≠ y3 → v1 ≠ y4 → v2 ≠ y0 → v2 ≠ y1 → v2 ≠ y2 → v2 ≠ y3 → v2
        ≠ y4 →
    ∀ (p1 : (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
    let K8 : Finset (V ⊕ E) := (insert (Sum.inl y0) (insert (Sum.inl y1) (insert (Sum.inl y4)
        (insert (Sum.inl v1) (insert (Sum.inl v2) (insert (Sum.inr q) (insert (Sum.inr f1)
        ({Sum.inr f2} : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) :
        Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)); K8.card = (8 : ℕ) →
    ∀ (iv2 : ℕ) (b : E), Incident G v2 f2 → phi b = some N.beta →
    ∀ (w : V), G.ends b = s(v1, v2) →
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by
                                                     have := GoldbergSeymour.TreeSequence.positive T
                                                     omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by
                                                      omega
    ⟩ : Fin (T.length + (1 : ℕ))); N.alpha ≠ N.beta →
    ∀ (pmax : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))), {z : V ⊕ E | z ∈ pmax.support} = TwoColorComponent G phi N.alpha N.beta
        (Sum.inl (T.vertex i0)) → IsProperEdgeColoring G (TwoColorComponentSwap G phi N.alpha
        N.beta (Sum.inl (T.vertex i0))) ∧ IsOneEdgeUncolored (TwoColorComponentSwap G phi N.alpha
        N.beta (Sum.inl (T.vertex i0))) e0 ∧ TashkinovTree G e0 (TwoColorComponentSwap G phi
        N.alpha N.beta (Sum.inl (T.vertex i0))) T →
    ∃ (alphaEdge : E) (betaEdge : E), G.ends alphaEdge = s(v1, v2) ∧ phi alphaEdge = some N.alpha
        ∧ G.ends betaEdge = s(v1, v2) ∧ phi betaEdge = some N.beta ∧ alphaEdge ≠ betaEdge

private theorem helper_missing_excludes_146.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (phi : PartialEdgeColoring E k) {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G phi v →
        Incident G v f → phi f ≠ some c := by
  classical
  intro V E _ _ G k phi c v f hc hinc hfc
  let _ := Fintype.ofFinite V
  have hp : c ∈ PresentColors G phi v := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨f, hinc, hfc⟩
  have hn : c ∉ PresentColors G phi v := by
    simpa [MissingColors] using hc
  exact hn hp

private theorem helper_edge_color_of_closing_support_156.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (f : E),
    Sum.inr f ∈ N.closingPath.support →
    phi f = some N.alpha ∨ phi f = some N.beta := by
  classical
  intro V E _ _ _ G k e0 phi T N f hf
  obtain ⟨i, hi, hile⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
  have hilt : i < N.closingPath.length := by
    by_contra hn
    have hil : N.closingPath.length ≤ i := by omega
    have hend := N.closingPath.getVert_of_length_le (i := i) hil
    rw [hi] at hend
    simp at hend
  have hadj := N.closingPath.adj_getVert_succ hilt
  rw [hi] at hadj
  cases hz : N.closingPath.getVert (i + 1) with
  | inl v =>
      rw [hz] at hadj
      have hdata : Incident G v f ∧
          (phi f = some N.alpha ∨ phi f = some N.beta) := by
        simpa [TwoColorIncidenceGraph] using hadj
      exact hdata.2
  | inr e =>
      rw [hz] at hadj
      simp [TwoColorIncidenceGraph] at hadj

private theorem helper_ha1color_190.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1; G.ends a1 = s(y1, y2) → (
    ∀ {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G phi v → Incident G v f → phi f ≠ some c) →
        (
    ∀ (f : E), Sum.inr f ∈ N.closingPath.support → phi f = some N.alpha ∨ phi f = some N.beta) →
        Sum.inr a1 ∈ N.closingPath.support → phi a1 = some N.alpha := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y1 y2 r1 a1 ha1ends missing_excludes
      edge_color_of_closing_support ha1support
  rcases edge_color_of_closing_support a1 ha1support with h | h
  · exact h
  · have hbmiss : N.beta ∈ MissingColors G phi y1 := by
      simpa [y1] using N.beta_missing
    have hinc : Incident G y1 a1 := by
      unfold Incident
      rw [ha1ends]
      simp [Sym2.mem_iff]
    exact False.elim ((missing_excludes hbmiss hinc) h)

private theorem helper_ha1a2_200.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1;
    let a2 : E := T.edge r2; G.ends a1 = s(y1, y2) → G.ends a2 = s(y2, y3) → AdjacentEdges G a1 a2
  := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y1 y2 y3 r1 r2 a1 a2 ha1ends ha2ends
  refine ⟨y2, ?_, ?_⟩ <;> unfold Incident
  · rw [ha1ends]
    simp [Sym2.mem_iff]
  · rw [ha2ends]
    simp [Sym2.mem_iff]

private theorem helper_ha2a3_213.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a2 : E := T.edge r2;
    let a3 : E := T.edge r3; G.ends a2 = s(y2, y3) → G.ends a3 = s(y3, y4) → AdjacentEdges G a2 a3
  := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y2 y3 y4 r2 r3 a2 a3 ha2ends ha3ends
  refine ⟨y3, ?_, ?_⟩ <;> unfold Incident
  · rw [ha2ends]
    simp [Sym2.mem_iff]
  · rw [ha3ends]
    simp [Sym2.mem_iff]

private theorem helper_ha3q_226.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a3 : E := T.edge r3;
    let q : E := N.closingEdge; G.ends a3 = s(y3, y4) → G.ends q = s(y4, y0) → AdjacentEdges G a3
        q := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y0 y3 y4 r3 a3 q ha3ends hqends
  refine ⟨y4, ?_, ?_⟩ <;> unfold Incident
  · rw [ha3ends]
    simp [Sym2.mem_iff]
  · rw [hqends]
    simp [Sym2.mem_iff]

private theorem helper_hgamma_beta_243.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (f1 : E) (v1 : V), G.ends f1 = s(T.vertex (⟨(1 : ℕ),
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    ⟩ : Fin (T.length + (1 : ℕ))), v1) → phi f1 = some gamma →
    let _ : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); (
    ∀ {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G phi v → Incident G v f → phi f ≠ some c) →
        gamma ≠ N.beta := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma f1 v1 hf1ends hf1color y1 missing_excludes h
  have hinc : Incident G y1 f1 := by
    unfold Incident
    rw [hf1ends]
    simp [y1, Sym2.mem_iff]
  exact (missing_excludes (by simpa [y1] using N.beta_missing) hinc)
    (by simpa [h] using hf1color)

private theorem helper_hf12ne_263.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (f1 f2
        : E) (v1 v2 : V),
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); y1 ≠ y4 → G.ends f1 = s(y1, v1) → G.ends f2 = s(y4, v2) → v2 ≠
        y1 → f1 ≠ f2 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight f1 f2 v1 v2 y1 y4 hy14 hf1ends' hf2ends' hv21' h
  have hpairs : s(y1, v1) = s(y4, v2) := by
    rw [← hf1ends', h, hf2ends']
  rcases Sym2.eq_iff.mp hpairs with hd | hs
  · exact hy14 hd.1
  · exact hv21' hs.1.symm

private theorem helper_hv12ne_270.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (f1 f2 : E) (v1 v2 : V), phi f1 = some gamma → phi f2 = some gamma →
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); IsProperEdgeColoring G phi → G.ends f1 = s(y1, v1) → G.ends f2
        = s(y4, v2) → f1 ≠ f2 → v1 ≠ v2 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma f1 f2 v1 v2 hf1color hf2color y1 y4 hproper
      hf1ends' hf2ends' hf12ne h
  have hadj : AdjacentEdges G f1 f2 := by
    refine ⟨v1, ?_, ?_⟩ <;> unfold Incident
    · rw [hf1ends']
      simp [Sym2.mem_iff]
    · rw [hf2ends', ← h]
      simp [Sym2.mem_iff]
  exact (hproper hf12ne hadj hf1color) hf2color

private theorem helper_hK8sub_343.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5
        : ℕ)) (gamma : Fin k) (f1 f2 : E) (v1 v2 : V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let q : E := N.closingEdge;
    ∀ (p1 : (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), Sum.inl y0 ∈ p1.support →
        Sum.inr q ∈ p1.support → Sum.inl y4 ∈ p1.support → Sum.inr f2 ∈ p1.support → Sum.inl v2 ∈
        p1.support → Sum.inl y1 ∈ p1.support → Sum.inr f1 ∈ p1.support → Sum.inl v1 ∈ p1.support →
    let K8 : Finset (V ⊕ E) := (insert (Sum.inl y0) (insert (Sum.inl y1) (insert (Sum.inl y4)
        (insert (Sum.inl v1) (insert (Sum.inl v2) (insert (Sum.inr q) (insert (Sum.inr f1)
        ({Sum.inr f2} : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) :
        Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)); K8 ⊆
        p1.support.toFinset := by
  classical
  intro V E _ _ _ _ G k e0 phi T N hNheight gamma f1 f2 v1 v2 y0 y1 y4 q p1 hy0p1 hqp1 hy4p1
      hf2p1 hv2p1 hy1p1 hf1p1 hv1p1 K8 z hz
  simp only [K8, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using hy0p1
  · simpa using hy1p1
  · simpa using hy4p1
  · simpa using hv1p1
  · simpa using hv2p1
  · simpa using hqp1
  · simpa using hf1p1
  · simpa using hf2p1

private theorem helper_hiv2lt_370.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (_ _ : E) (_ v2 : V),
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); v2 ≠ y1 →
    ∀ (p1 : (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), (4 : ℕ) ∣ p1.length →
        p1.length = (8 : ℕ) →
    ∀ (iv2 : ℕ), p1.getVert iv2 = Sum.inl v2 → iv2 ≤ p1.length → iv2 < p1.length := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma f1 f2 v1 v2 y1 hv21' p1 hp1div hp1length iv2 hiv2
      hiv2le
  by_contra h
  have hil : p1.length ≤ iv2 := by omega
  have hvend := p1.getVert_of_length_le hil
  have hv : (Sum.inl v2 : Sum V E) = Sum.inl y1 := by
    rw [hiv2] at hvend
    simpa [y1] using hvend
  exact hv21' (Sum.inl_injective hv)

private theorem helper_hprevnext_387.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T), N.height = (5 : ℕ) →
    ∀ (gamma : Fin k) (_ _ : E) (_ _ : V) (p1 : (TwoColorIncidenceGraph G phi gamma N.beta).Walk
        (Sum.inl (T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ)))))
        (Sum.inl (T.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
        p1.IsPath → (4 : ℕ) ∣ p1.length → p1.length = (8 : ℕ) →
    ∀ iv2 ≤ p1.length, iv2 < p1.length → p1.getVert (iv2 - (1 : ℕ)) ≠ p1.getVert (iv2 + (1 : ℕ))
  := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma f1 f2 v1 v2 p1 hp1 hp1div hp1length iv2 hiv2le
      hiv2lt h
  have hi := hp1.getVert_injOn
    (show iv2 - 1 ≤ p1.length by omega)
    (show iv2 + 1 ≤ p1.length by omega) h
  omega

private theorem helper_branch_396.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (gamma : Fin k) (f2 : E) (v2 : V) (p1 :
        (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi gamma N.beta;
    ∀ (iv2 : ℕ), H1.Adj (Sum.inl v2) (p1.getVert (iv2 + (1 : ℕ))) → p1.getVert (iv2 - (1 : ℕ)) ≠
        p1.getVert (iv2 + (1 : ℕ)) → p1.getVert (iv2 - (1 : ℕ)) = Sum.inr f2 →
    ∃ (b : E), H1.Adj (Sum.inl v2) (Sum.inr b) ∧ Sum.inr b ∈ p1.support ∧ b ≠ f2 := by
  classical
  intro V E _ _ _ G k e0 phi T N gamma f2 v2 p1 H1 iv2 hnextAdj hprevnext hp
  cases hn : p1.getVert (iv2 + 1) with
  | inl w =>
      rw [hn] at hnextAdj
      simp [H1, TwoColorIncidenceGraph] at hnextAdj
  | inr b =>
      rw [hn] at hnextAdj
      refine ⟨b, hnextAdj, ?_, ?_⟩
      · rw [← hn]
        exact p1.getVert_mem_support (iv2 + 1)
      · intro h
        apply hprevnext
        rw [hp, hn, h]

private theorem helper_branch_408.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (gamma : Fin k) (f2 : E) (v2 : V) (p1 :
        (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi gamma N.beta;
    ∀ (iv2 : ℕ), H1.Adj (Sum.inl v2) (p1.getVert (iv2 - (1 : ℕ))) → ¬p1.getVert (iv2 - (1 : ℕ)) =
        Sum.inr f2 →
    ∃ (b : E), H1.Adj (Sum.inl v2) (Sum.inr b) ∧ Sum.inr b ∈ p1.support ∧ b ≠ f2 := by
  classical
  intro V E _ _ _ G k e0 phi T N gamma f2 v2 p1 H1 iv2 hprevAdj hp
  cases hn : p1.getVert (iv2 - 1) with
  | inl w =>
      rw [hn] at hprevAdj
      simp [H1, TwoColorIncidenceGraph] at hprevAdj
  | inr b =>
      rw [hn] at hprevAdj
      refine ⟨b, hprevAdj, ?_, ?_⟩
      · rw [← hn]
        exact p1.getVert_mem_support (iv2 - 1)
      · intro h
        exact hp (by rw [hn, h])

private theorem helper_hbq_431.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (v2 :
        V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let q : E := N.closingEdge; G.ends q = s(y4, y0) → v2 ≠ y0 → v2 ≠ y4 →
    ∀ (b : E) (w : V), G.ends b = s(v2, w) → b ≠ q := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight v2 y0 y4 q hqends hv20' hv24' b w hbends h
  have hpairs : s(v2, w) = s(y4, y0) := by
    rw [← hbends, h, hqends]
  rcases Sym2.eq_iff.mp hpairs with hd | hs
  · exact hv24' hd.1
  · exact hv20' hs.1

private theorem helper_hK9sub_447.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5
        : ℕ)) (gamma : Fin k) (f1 f2 : E) (v1 v2 : V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let q : E := N.closingEdge;
    ∀ (p1 : (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
    let K8 : Finset (V ⊕ E) := (insert (Sum.inl y0) (insert (Sum.inl y1) (insert (Sum.inl y4)
        (insert (Sum.inl v1) (insert (Sum.inl v2) (insert (Sum.inr q) (insert (Sum.inr f1)
        ({Sum.inr f2} : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) :
        Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)); K8 ⊆
        p1.support.toFinset →
    ∀ (b : E), Sum.inr b ∈ p1.support →
    let K9 : Finset (V ⊕ E) := (insert (Sum.inr b) K8 : Finset (V ⊕ E)); K9 ⊆ p1.support.toFinset
  := by
  classical
  intro V E _ _ _ _ G k e0 phi T N hNheight gamma f1 f2 v1 v2 y0 y1 y4 q p1 K8 hK8sub b hbp1 K9 z hz
  simp only [K9, Finset.mem_insert] at hz
  rcases hz with rfl | hz
  · simpa using hbp1
  · exact hK8sub hz

private theorem helper_hwy0_470.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (v2 :
        V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let q : E := N.closingEdge; G.ends q = s(y4, y0) → IsProperEdgeColoring G phi → phi q = some
        N.beta →
    ∀ (b : E), phi b = some N.beta →
    ∀ (w : V), G.ends b = s(v2, w) → b ≠ q → w ≠ y0 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight v2 y0 y4 q hqends hproper hqcolor b hbcolor w hbends hbq h
  have hadj : AdjacentEdges G b q := ⟨y0, by
    unfold Incident
    rw [hbends, h]
    simp [Sym2.mem_iff], by
    unfold Incident
    rw [hqends]
    simp [Sym2.mem_iff]⟩
  exact (hproper hbq hadj hbcolor) hqcolor

private theorem helper_hwy1_480.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (v2 :
        V),
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); (
    ∀ {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G phi v → Incident G v f → phi f ≠ some c) →
    ∀ (b : E), phi b = some N.beta →
    ∀ (w : V), G.ends b = s(v2, w) → w ≠ y1 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight v2 y1 missing_excludes b hbcolor w hbends h
  have hinc : Incident G y1 b := by
    unfold Incident
    rw [hbends, h]
    simp [Sym2.mem_iff]
  exact (missing_excludes (by simpa [y1] using N.beta_missing) hinc) hbcolor

private theorem helper_hwy4_487.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (v2 :
        V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let q : E := N.closingEdge; G.ends q = s(y4, y0) → IsProperEdgeColoring G phi → phi q = some
        N.beta →
    ∀ (b : E), phi b = some N.beta →
    ∀ (w : V), G.ends b = s(v2, w) → b ≠ q → w ≠ y4 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight v2 y0 y4 q hqends hproper hqcolor b hbcolor w hbends hbq h
  have hadj : AdjacentEdges G b q := ⟨y4, by
    unfold Incident
    rw [hbends, h]
    simp [Sym2.mem_iff], by
    unfold Incident
    rw [hqends]
    simp [Sym2.mem_iff]⟩
  exact (hproper hbq hadj hbcolor) hqcolor

private theorem helper_hfixed_509.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
      (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
      (T : TreeSequence G e0) (_ : NormalGlobalMaximumTriple G k e0 phi T),
    FixedPairMaximalTashkinovTree G e0 phi T := by
  classical
  intro V E _ _ _ G k e0 phi T N
  refine ⟨N.global.2.1, ?_⟩
  intro S hS hsub
  have hScard := treeCard_le_tashkinovOrder G k e0 phi S N.global.1 hS
  have hcard : (TreeSequenceVertexSet S).card ≤
      (TreeSequenceVertexSet T).card := by
    rw [N.global.2.2]
    exact hScard
  have heq : TreeSequenceVertexSet T = TreeSequenceVertexSet S :=
    Finset.eq_of_subset_of_card_le hsub hcard
  exact heq.symm.subset

private theorem helper_hK0sub_601.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5
        : ℕ)),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1;
    let a2 : E := T.edge r2;
    let a3 : E := T.edge r3;
    let q : E := N.closingEdge;
    let C0 : Set (V ⊕ E) := TwoColorComponent G phi N.alpha N.beta (Sum.inl y0); Sum.inl y0 ∈ C0 →
    ∀ (p0 : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), (
    ∀ {z : V ⊕ E}, z ∈ C0 → z ∈ p0.support) → Sum.inr q ∈ C0 → Sum.inl y4 ∈ C0 → Sum.inr a3 ∈ C0 →
        Sum.inl y3 ∈ C0 → Sum.inr a2 ∈ C0 → Sum.inl y2 ∈ C0 → Sum.inr a1 ∈ C0 → Sum.inl y1 ∈ C0 →
    let K0 : Finset (V ⊕ E) := (insert (Sum.inl y0) (insert (Sum.inl y1) (insert (Sum.inl y2)
        (insert (Sum.inl y3) (insert (Sum.inl y4) (insert (Sum.inr q) (insert (Sum.inr a1) (insert
        (Sum.inr a2) ({Sum.inr a3} : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset
        (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset
        (V ⊕ E)); K0 ⊆ p0.support.toFinset := by
  classical
  intro V E _ _ _ _ G k e0 phi T N hNheight y0 y1 y2 y3 y4 r1 r2 r3 a1 a2 a3 q C0 hC0root p0
      support_of_C0 hqC0 hy4C0 ha3C0 hy3C0 ha2C0 hy2C0 ha1C0 hy1C0 K0 z hz
  simp only [K0, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using support_of_C0 hC0root
  · simpa using support_of_C0 hy1C0
  · simpa using support_of_C0 hy2C0
  · simpa using support_of_C0 hy3C0
  · simpa using support_of_C0 hy4C0
  · simpa using support_of_C0 hqC0
  · simpa using support_of_C0 ha1C0
  · simpa using support_of_C0 ha2C0
  · simpa using support_of_C0 ha3C0

private theorem helper_hv1notC0_629.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5
        : ℕ)) (v1 : V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1;
    let a2 : E := T.edge r2;
    let a3 : E := T.edge r3;
    let q : E := N.closingEdge; v1 ≠ y0 → v1 ≠ y1 → v1 ≠ y2 → v1 ≠ y3 → v1 ≠ y4 →
    let C0 : Set (V ⊕ E) := TwoColorComponent G phi N.alpha N.beta (Sum.inl y0);
    ∀ (p0 : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), (
    ∀ {z : V ⊕ E}, z ∈ C0 → z ∈ p0.support) →
    let K0 : Finset (V ⊕ E) := (insert (Sum.inl y0) (insert (Sum.inl y1) (insert (Sum.inl y2)
        (insert (Sum.inl y3) (insert (Sum.inl y4) (insert (Sum.inr q) (insert (Sum.inr a1) (insert
        (Sum.inr a2) ({Sum.inr a3} : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset
        (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset
        (V ⊕ E)); K0 = p0.support.toFinset → Sum.inl v1 ∉ C0 := by
  classical
  intro V E _ _ _ _ G k e0 phi T N hNheight v1 y0 y1 y2 y3 y4 r1 r2 r3 a1 a2 a3 q hv10' hv11'
      hv12' hv13' hv14' C0 p0 support_of_C0 K0 hK0eq hv
  have hvp := support_of_C0 hv
  have hvK : Sum.inl v1 ∈ K0 := by
    rw [hK0eq]
    simpa using hvp
  simp [K0, hv10', hv11', hv12', hv13', hv14'] at hvK

private theorem helper_hgamma_alpha_643.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (f1 : E) (v1 : V), phi f1 = some gamma →
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); G.ends f1 = s(y1, v1) →
    let C0 : Set (V ⊕ E) := TwoColorComponent G phi N.alpha N.beta (Sum.inl y0);
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi N.alpha N.beta; (
    ∀ {x z : V ⊕ E}, x ∈ C0 → H0.Adj x z → z ∈ C0) → Sum.inl y1 ∈ C0 → Sum.inl v1 ∉ C0 → gamma ≠
        N.alpha := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma f1 v1 hf1color y0 y1 hf1ends' C0 H0 C0_of_adj
      hy1C0 hv1notC0 h
  have hf1adj : H0.Adj (Sum.inl y1) (Sum.inr f1) := by
    simp [H0, TwoColorIncidenceGraph, Incident, hf1ends', hf1color, h,
      Sym2.mem_iff]
  have hf1C : Sum.inr f1 ∈ C0 := C0_of_adj hy1C0 hf1adj
  have hv1adj : H0.Adj (Sum.inr f1) (Sum.inl v1) := by
    simp [H0, TwoColorIncidenceGraph, Incident, hf1ends', hf1color, h,
      Sym2.mem_iff]
  exact hv1notC0 (C0_of_adj hf1C hv1adj)

private theorem helper_hgamma_677.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    ∀ gamma ∈ MissingColors G phi (T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length
        + (1 : ℕ)))),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
        (
    ∀ (e : E), phi' e = some gamma ↔ phi e = some gamma) → gamma ∈ MissingColors G phi' y0 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma hgamma y0 phi' hgamma_fixed
  have hn : gamma ∉ PresentColors G phi' y0 := by
    intro hp
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨e, heinc, hecolor⟩ := hp
    have hpold : gamma ∈ PresentColors G phi y0 := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, heinc, (hgamma_fixed e).1 hecolor⟩
    have hnold : gamma ∉ PresentColors G phi y0 := by
      simpa [y0, MissingColors] using hgamma
    exact hnold hpold
  simpa [MissingColors] using hn

private theorem helper_halpha_689.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); (
    ∀ {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G phi v → Incident G v f → phi f ≠ some c) →
        N.alpha ≠ N.beta →
    let C0 : Set (V ⊕ E) := TwoColorComponent G phi N.alpha N.beta (Sum.inl y0);
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi N.alpha N.beta; (
    ∀ {x z : V ⊕ E}, x ∈ C0 → H0.Adj x z → z ∈ C0) → Sum.inl y1 ∈ C0 →
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
        N.alpha ∈ MissingColors G phi' y1 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y0 y1 missing_excludes hab C0 H0 C0_of_adj hy1C0 phi'
  have hn : N.alpha ∉ PresentColors G phi' y1 := by
    intro hp
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨e, heinc, hecolor⟩ := hp
    by_cases heC : Sum.inr e ∈ C0
    · by_cases hea : phi e = some N.alpha
      · have : phi' e = some N.beta := by
          simp [phi', TwoColorComponentSwap, C0, heC, hea]
        exact hab (Option.some.inj (this.symm.trans hecolor)).symm
      · by_cases heb : phi e = some N.beta
        · have hbmiss : N.beta ∈ MissingColors G phi y1 := by
            simpa [y1] using N.beta_missing
          exact (missing_excludes hbmiss heinc) heb
        · have hfix : phi' e = phi e := by
            simp [phi', TwoColorComponentSwap, C0, heC, hea, heb]
          exact hea (hfix.symm.trans hecolor)
    · have heold : phi e = some N.alpha := by
        simpa [phi', TwoColorComponentSwap, C0, heC] using hecolor
      have hadj : H0.Adj (Sum.inl y1) (Sum.inr e) := by
        simp [H0, TwoColorIncidenceGraph, heinc, heold]
      exact heC (C0_of_adj hy1C0 hadj)
  rw [MissingColors, Finset.mem_sdiff]
  exact ⟨Finset.mem_univ _, hn⟩

private theorem helper_missing_excludes_713.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
    ∀ {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G phi' v → Incident G v f → phi' f ≠ some c
  := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y0 phi' c v f hc hinc hfc
  have hp : c ∈ PresentColors G phi' v := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨f, hinc, hfc⟩
  have hn : c ∉ PresentColors G phi' v := by
    simpa [MissingColors] using hc
  exact hn hp

private theorem helper_hK8sub2_773.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5
        : ℕ)) (gamma : Fin k) (f1 f2 : E) (v1 v2 : V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let q : E := N.closingEdge;
    let K8 : Finset (V ⊕ E) := (insert (Sum.inl y0) (insert (Sum.inl y1) (insert (Sum.inl y4)
        (insert (Sum.inl v1) (insert (Sum.inl v2) (insert (Sum.inr q) (insert (Sum.inr f1)
        ({Sum.inr f2} : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) :
        Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E));
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
    ∀ (p2 : (TwoColorIncidenceGraph G phi' gamma N.alpha).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), Sum.inl y0 ∈ p2.support →
        Sum.inr q ∈ p2.support → Sum.inl y4 ∈ p2.support → Sum.inr f2 ∈ p2.support → Sum.inl v2 ∈
        p2.support → Sum.inl y1 ∈ p2.support → Sum.inr f1 ∈ p2.support → Sum.inl v1 ∈ p2.support →
        K8 ⊆ p2.support.toFinset := by
  classical
  intro V E _ _ _ _ G k e0 phi T N hNheight gamma f1 f2 v1 v2 y0 y1 y4 q K8 phi' p2 hy0p2 hqp2
      hy4p2 hf2p2 hv2p2 hy1p2 hf1p2 hv1p2 z hz
  simp only [K8, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using hy0p2
  · simpa using hy1p2
  · simpa using hy4p2
  · simpa using hv1p2
  · simpa using hv2p2
  · simpa using hqp2
  · simpa using hf1p2
  · simpa using hf2p2

private theorem helper_hiv2lt_800.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (_ _ : E) (_ v2 : V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); v2 ≠ y1 →
    ∀ (_ : (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (_ : ℕ) (_ : E),
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))) (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex
        (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex
        (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
    ∀ (p2 : (TwoColorIncidenceGraph G phi' gamma N.alpha).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), (4 : ℕ) ∣ p2.length →
        p2.length = (8 : ℕ) →
    ∀ (iv2' : ℕ), p2.getVert iv2' = Sum.inl v2 → iv2' ≤ p2.length → iv2' < p2.length := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma f1 f2 v1 v2 y0 y1 hv21' p1 iv2 b i0 i1 pmax p0
      phi' p2 hp2div hp2length iv2' hiv2' hiv2le'
  by_contra h
  have hil : p2.length ≤ iv2' := by omega
  have hvend := p2.getVert_of_length_le hil
  have hv : (Sum.inl v2 : Sum V E) = Sum.inl y1 := by
    rw [hiv2'] at hvend
    simpa [y1] using hvend
  exact hv21' (Sum.inl_injective hv)

private theorem helper_hprevnext2_817.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (_ _ : E) (_ _ : V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (_ : ℕ) (_ : E),
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by
          have := GoldbergSeymour.TreeSequence.positive T
          omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))) (_ : (TwoColorIncidenceGraph G phi N.alpha N.beta).Walk (Sum.inl (T.vertex
        (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex
        (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
    ∀ (p2 : (TwoColorIncidenceGraph G phi' gamma N.alpha).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), p2.IsPath → (4 : ℕ) ∣
        p2.length → p2.length = (8 : ℕ) →
    ∀ iv2' ≤ p2.length, iv2' < p2.length → p2.getVert (iv2' - (1 : ℕ)) ≠ p2.getVert (iv2' + (1 :
        ℕ)) := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma f1 f2 v1 v2 y0 p1 iv2 b i0 i1 pmax p0 phi' p2 hp2
      hp2div hp2length iv2' hiv2le' hiv2lt' h
  have hi := hp2.getVert_injOn
    (show iv2' - 1 ≤ p2.length by omega)
    (show iv2' + 1 ≤ p2.length by omega) h
  omega

private theorem helper_branch_826.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (f2 : E) (v2 : V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : V),
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
    ∀ (p2 : (TwoColorIncidenceGraph G phi' gamma N.alpha).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
    let H2 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi' gamma N.alpha;
    ∀ (iv2' : ℕ), H2.Adj (Sum.inl v2) (p2.getVert (iv2' + (1 : ℕ))) → p2.getVert (iv2' - (1 : ℕ))
        ≠ p2.getVert (iv2' + (1 : ℕ)) → p2.getVert (iv2' - (1 : ℕ)) = Sum.inr f2 →
    ∃ (a : E), H2.Adj (Sum.inl v2) (Sum.inr a) ∧ Sum.inr a ∈ p2.support ∧ a ≠ f2 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma f2 v2 y0 w phi' p2 H2 iv2' hnextAdj2 hprevnext2 hp
  cases hn : p2.getVert (iv2' + 1) with
  | inl w =>
      rw [hn] at hnextAdj2
      simp [H2, TwoColorIncidenceGraph] at hnextAdj2
  | inr a =>
      rw [hn] at hnextAdj2
      refine ⟨a, hnextAdj2, ?_, ?_⟩
      · rw [← hn]
        exact p2.getVert_mem_support (iv2' + 1)
      · intro h
        apply hprevnext2
        rw [hp, hn, h]

private theorem helper_branch_838.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (f2 : E) (v2 : V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (_ : V),
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
    ∀ (p2 : (TwoColorIncidenceGraph G phi' gamma N.alpha).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
    let H2 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi' gamma N.alpha;
    ∀ (iv2' : ℕ), H2.Adj (Sum.inl v2) (p2.getVert (iv2' - (1 : ℕ))) → ¬p2.getVert (iv2' - (1 : ℕ))
        = Sum.inr f2 →
    ∃ (a : E), H2.Adj (Sum.inl v2) (Sum.inr a) ∧ Sum.inr a ∈ p2.support ∧ a ≠ f2 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma f2 v2 y0 w phi' p2 H2 iv2' hprevAdj2 hp
  cases hn : p2.getVert (iv2' - 1) with
  | inl w =>
      rw [hn] at hprevAdj2
      simp [H2, TwoColorIncidenceGraph] at hprevAdj2
  | inr a =>
      rw [hn] at hprevAdj2
      refine ⟨a, hprevAdj2, ?_, ?_⟩
      · rw [← hn]
        exact p2.getVert_mem_support (iv2' - 1)
      · intro h
        exact hp (by rw [hn, h])

private theorem helper_haq_857.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (v2 :
        V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let q : E := N.closingEdge; G.ends q = s(y4, y0) → v2 ≠ y0 → v2 ≠ y4 →
    ∀ (a : E) (x : V), G.ends a = s(v2, x) → a ≠ q := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight v2 y0 y4 q hqends hv20' hv24' a x haends h
  have hpairs : s(v2, x) = s(y4, y0) := by
    rw [← haends, h, hqends]
  rcases Sym2.eq_iff.mp hpairs with hd | hs
  · exact hv24' hd.1
  · exact hv20' hs.1

private theorem helper_hK9asub_873.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5
        : ℕ)) (gamma : Fin k) (f1 f2 : E) (v1 v2 : V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let q : E := N.closingEdge;
    let K8 : Finset (V ⊕ E) := (insert (Sum.inl y0) (insert (Sum.inl y1) (insert (Sum.inl y4)
        (insert (Sum.inl v1) (insert (Sum.inl v2) (insert (Sum.inr q) (insert (Sum.inr f1)
        ({Sum.inr f2} : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) :
        Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E));
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
    ∀ (p2 : (TwoColorIncidenceGraph G phi' gamma N.alpha).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), K8 ⊆ p2.support.toFinset →
    ∀ (a : E), Sum.inr a ∈ p2.support →
    let K9a : Finset (V ⊕ E) := (insert (Sum.inr a) K8 : Finset (V ⊕ E)); K9a ⊆
        p2.support.toFinset := by
  classical
  intro V E _ _ _ _ G k e0 phi T N hNheight gamma f1 f2 v1 v2 y0 y1 y4 q K8 phi' p2 hK8sub2 a
      hap2 K9a z hz
  simp only [K9a, Finset.mem_insert] at hz
  rcases hz with rfl | hz
  · simpa using hap2
  · exact hK8sub2 hz

private theorem helper_hxy0_896.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (v2 :
        V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let q : E := N.closingEdge; G.ends q = s(y4, y0) →
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
        IsProperEdgeColoring G phi' → phi' q = some N.alpha →
    ∀ (a : E), phi' a = some N.alpha →
    ∀ (x : V), G.ends a = s(v2, x) → a ≠ q → x ≠ y0 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight v2 y0 y4 q hqends phi' hproper' hqcolor' a hacolor' x
      haends haq h
  have hadj : AdjacentEdges G a q := ⟨y0, by
    unfold Incident
    rw [haends, h]
    simp [Sym2.mem_iff], by
    unfold Incident
    rw [hqends]
    simp [Sym2.mem_iff]⟩
  exact (hproper' haq hadj hacolor') hqcolor'

private theorem helper_hxy1_906.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (v2 :
        V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
        N.alpha ∈ MissingColors G phi' y1 → (
    ∀ {c : Fin k} {v : V} {f : E}, c ∈ MissingColors G phi' v → Incident G v f → phi' f ≠ some c)
        →
    ∀ (a : E), phi' a = some N.alpha →
    ∀ (x : V), G.ends a = s(v2, x) → x ≠ y1 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight v2 y0 y1 phi' halpha' missing_excludes' a hacolor' x
      haends h
  have hinc : Incident G y1 a := by
    unfold Incident
    rw [haends, h]
    simp [Sym2.mem_iff]
  exact (missing_excludes' halpha' hinc) hacolor'

private theorem helper_hxy4_913.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (v2 :
        V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let q : E := N.closingEdge; G.ends q = s(y4, y0) →
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
        IsProperEdgeColoring G phi' → phi' q = some N.alpha →
    ∀ (a : E), phi' a = some N.alpha →
    ∀ (x : V), G.ends a = s(v2, x) → a ≠ q → x ≠ y4 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight v2 y0 y4 q hqends phi' hproper' hqcolor' a hacolor' x
      haends haq h
  have hadj : AdjacentEdges G a q := ⟨y4, by
    unfold Incident
    rw [haends, h]
    simp [Sym2.mem_iff], by
    unfold Incident
    rw [hqends]
    simp [Sym2.mem_iff]⟩
  exact (hproper' haq hadj hacolor') hqcolor'

private theorem helper_haNotC0_935.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (v1 v2
        : V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); N.alpha ≠ N.beta →
    let C0 : Set (V ⊕ E) := TwoColorComponent G phi N.alpha N.beta (Sum.inl y0);
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi N.alpha N.beta; (
    ∀ {x z : V ⊕ E}, x ∈ C0 → H0.Adj x z → z ∈ C0) → Sum.inl v1 ∉ C0 →
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0);
    ∀ (a : E), phi' a = some N.alpha → G.ends a = s(v1, v2) → Sum.inr a ∉ C0 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight v1 v2 y0 hab C0 H0 C0_of_adj hv1notC0 phi' a hacolor'
      haends' haC
  have habeta : phi a = some N.beta := by
    by_cases haa : phi a = some N.alpha
    · have hs : phi' a = some N.beta := by
        simp [phi', TwoColorComponentSwap, C0, haC, haa]
      exact False.elim (hab (Option.some.inj (hacolor'.symm.trans hs)))
    · by_cases habeta : phi a = some N.beta
      · exact habeta
      · have hfix : phi' a = phi a := by
          simp [phi', TwoColorComponentSwap, C0, haC, haa, habeta]
        exact False.elim (haa (hfix.symm.trans hacolor'))
  have hadj : H0.Adj (Sum.inr a) (Sum.inl v1) := by
    simp [H0, TwoColorIncidenceGraph, Incident, haends', habeta, Sym2.mem_iff]
  exact hv1notC0 (C0_of_adj haC hadj)

private theorem helper_continuation_2397.{u_1, u_2} :
    helperContinuation2397Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T N hNheight hGheight gamma f1 f2 v1 v2 _ y0 y1 y4 q hqends
      hf1ends' hv20' hv21' hv24' p1 K8 hK8card iv2 b hf2inc hbcolor w hbends' i0 i1 hab pmax C0
      H0 C0_of_adj p0 hv1notC0 hgamma_alpha phi' hproper' hf1color' hf2color' hqcolor' halpha'
      missing_excludes' p2 hp2 hp2div hp2bound H2 C2 hp2support' C2_of_adj support_of_C2 hy0p2
      hqp2 hy4p2 hf2p2 hv2p2
  have hy1p2 : Sum.inl y1 ∈ p2.support := by
    simpa [y1] using p2.end_mem_support
  have hy1C2 : Sum.inl y1 ∈ C2 := by
    rw [← hp2support']
    exact hy1p2
  have hf1adj12 : H2.Adj (Sum.inl y1) (Sum.inr f1) := by
    simp [H2, TwoColorIncidenceGraph, Incident, hf1ends', hf1color', Sym2.mem_iff]
  have hf1C2 : Sum.inr f1 ∈ C2 := C2_of_adj hy1C2 hf1adj12
  have hf1p2 : Sum.inr f1 ∈ p2.support := support_of_C2 hf1C2
  have hf1adjv12 : H2.Adj (Sum.inr f1) (Sum.inl v1) := by
    simp [H2, TwoColorIncidenceGraph, Incident, hf1ends', hf1color', Sym2.mem_iff]
  have hv1C2 : Sum.inl v1 ∈ C2 := C2_of_adj hf1C2 hf1adjv12
  have hv1p2 : Sum.inl v1 ∈ p2.support := support_of_C2 hv1C2
  have hK8sub2 : K8 ⊆ p2.support.toFinset := by
    exact @helper_hK8sub2_773 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@f1) (@f2) (@v1) (@v2) (@p2)
        (@hy0p2) (@hqp2) (@hy4p2) (@hf2p2) (@hv2p2) (@hy1p2) (@hf1p2) (@hv1p2)
  have hp2lower : 7 ≤ p2.length := by
    have hc := Finset.card_le_card hK8sub2
    rw [hK8card, List.toFinset_card_of_nodup hp2.support_nodup,
      SimpleGraph.Walk.length_support] at hc
    omega
  have hp2length : p2.length = 8 := by
    rcases hp2div with ⟨d, hd⟩
    omega
  obtain ⟨iv2', hiv2', hiv2le'⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv2p2
  have hiv20' : iv2' ≠ 0 := by
    intro h
    have hv : (Sum.inl v2 : Sum V E) = Sum.inl y0 := by
      rw [← hiv2', h, p2.getVert_zero]
    exact hv20' (Sum.inl_injective hv)
  have hiv2lt' : iv2' < p2.length := by
    exact @helper_hiv2lt_800 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@gamma) (@f1) (@f2) (@v1) (@v2) (@hv21') (@p1) (@iv2) (@b)
        (@pmax) (@p0) (@p2) (@hp2div) (@hp2length) (@iv2') (@hiv2') (@hiv2le')
  have hprevAdj2 : H2.Adj (Sum.inl v2) (p2.getVert (iv2' - 1)) := by
    have h := (p2.adj_getVert_succ (i := iv2' - 1) (by omega)).symm
    have heq : iv2' - 1 + 1 = iv2' := by omega
    rw [heq, hiv2'] at h
    exact h
  have hnextAdj2 : H2.Adj (Sum.inl v2) (p2.getVert (iv2' + 1)) := by
    have h := p2.adj_getVert_succ hiv2lt'
    rw [hiv2'] at h
    exact h
  have hprevnext2 : p2.getVert (iv2' - 1) ≠ p2.getVert (iv2' + 1) := by
    exact @helper_hprevnext2_817 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@f1) (@f2) (@v1) (@v2) (@p1) (@iv2) (@b)
        (@pmax) (@p0) (@p2) (@hp2) (@hp2div) (@hp2length) (@iv2') (@hiv2le') (@hiv2lt')
  obtain ⟨a, haAdj, hap2, haf2⟩ : ∃ a : E,
      H2.Adj (Sum.inl v2) (Sum.inr a) ∧ Sum.inr a ∈ p2.support ∧ a ≠ f2 := by
    by_cases hp : p2.getVert (iv2' - 1) = Sum.inr f2
    · exact @helper_branch_826 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@f2) (@v2) (@w) (@p2) (@iv2') (@hnextAdj2)
        (@hprevnext2) (@hp)
    · exact @helper_branch_838 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@f2) (@v2) (@w) (@p2) (@iv2') (@hprevAdj2)
        (@hp)
  have hainc : Incident G v2 a := by
    simpa [H2, TwoColorIncidenceGraph] using haAdj |>.1
  have hfaadj : AdjacentEdges G f2 a := ⟨v2, hf2inc, hainc⟩
  have hacolor' : phi' a = some N.alpha := by
    have hc : phi' a = some gamma ∨ phi' a = some N.alpha := by
      simpa [H2, TwoColorIncidenceGraph] using haAdj |>.2
    exact hc.resolve_left (hproper' haf2.symm hfaadj hf2color')
  obtain ⟨x, haends⟩ := Sym2.mem_iff_exists.mp hainc
  have haq : a ≠ q := by
    exact @helper_haq_857 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@v2) (@hqends) (@hv20') (@hv24') (@a) (@x) (@haends)
  have haf1 : a ≠ f1 := by
    intro h
    have hc : some N.alpha = some gamma := by rw [← hacolor', h, hf1color']
    exact hgamma_alpha (Option.some.inj hc).symm
  let K9a : Finset (Sum V E) := insert (Sum.inr a) K8
  have hK9acard : K9a.card = 9 := by
    rw [Finset.card_insert_of_notMem]
    · rw [hK8card]
    · simp [K8, haf2, haf1, haq]
  have hK9asub : K9a ⊆ p2.support.toFinset := by
    exact @helper_hK9asub_873 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@f1) (@f2) (@v1) (@v2) (@p2)
        (@hK8sub2) (@a) (@hap2)
  have hp2card : p2.support.toFinset.card = 9 := by
    rw [List.toFinset_card_of_nodup hp2.support_nodup,
      SimpleGraph.Walk.length_support, hp2length]
  have hK9aeq : K9a = p2.support.toFinset :=
    Finset.eq_of_subset_of_card_le hK9asub (by rw [hK9acard, hp2card])
  have haAdjx : H2.Adj (Sum.inr a) (Sum.inl x) := by
    simp [H2, TwoColorIncidenceGraph, Incident, haends, hacolor', Sym2.mem_iff]
  have haC2 : Sum.inr a ∈ C2 := by
    rw [← hp2support']
    exact hap2
  have hxC2 : Sum.inl x ∈ C2 := C2_of_adj haC2 haAdjx
  have hxp2 : Sum.inl x ∈ p2.support := support_of_C2 hxC2
  have hxcases : x = y0 ∨ x = y1 ∨ x = y4 ∨ x = v1 ∨ x = v2 := by
    have hxfin : Sum.inl x ∈ K9a := by
      rw [hK9aeq]
      simpa using hxp2
    simpa [K9a, K8] using hxfin
  have hxy0 : x ≠ y0 := by
    exact @helper_hxy0_896 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@v2) (@hqends) (@hproper') (@hqcolor') (@a) (@hacolor')
        (@x) (@haends) (@haq)
  have hxy1 : x ≠ y1 := by
    exact @helper_hxy1_906 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@v2) (@halpha') (@missing_excludes') (@a) (@hacolor') (@x)
        (@haends)
  have hxy4 : x ≠ y4 := by
    exact @helper_hxy4_913 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@v2) (@hqends) (@hproper') (@hqcolor') (@a) (@hacolor')
        (@x) (@haends) (@haq)
  have hxv2 : x ≠ v2 := by
    intro h
    exact G.loopless a v2 (by simpa [h] using haends)
  have hxv1 : x = v1 := by
    simpa only [hxy0, hxy1, hxy4, hxv2, false_or, or_false] using hxcases
  have haends' : G.ends a = s(v1, v2) := by
    rw [haends, hxv1, Sym2.eq_swap]
  have haNotC0 : Sum.inr a ∉ C0 := by
    exact @helper_haNotC0_935 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@v1) (@v2) (@hab) (@C0_of_adj) (@hv1notC0) (@a) (@hacolor')
        (@haends')
  have hacolor : phi a = some N.alpha := by
    simpa [phi', TwoColorComponentSwap, C0, haNotC0] using hacolor'
  have habedge : a ≠ b := by
    intro h
    have hc : some N.alpha = some N.beta := by rw [← hacolor, h, hbcolor]
    exact hab (Option.some.inj hc)
  exact ⟨a, b, haends', hacolor, hbends', hbcolor, habedge⟩

private theorem helper_continuation_2127.{u_1, u_2} :
    helperContinuation2127Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T N hNheight hGheight gamma hgamma f1 f2 v1 v2 hf1color hf2color _
      y0 y1 y2 y3 y4 r1 r2 r3 a1 a2 a3 q hy01 hy02 hy03 hy04 hy12 hy13 hy14 hy23 hy24 hy34
      ha1ends ha2ends ha3ends hqends missing_excludes ha1color ha12ne ha2color ha23ne ha3color
      hqcolor hgamma_beta hf1ends' hf2ends' hv10' hv11' hv12' hv13' hv14' hv20' hv21' hv22' hv23'
      hv24' p1 K8 hK8card iv2 b hf2inc hbcolor w hbends' i0 i1 hab pmax hpmaxsupport hchangedata
  let C0 := TwoColorComponent G phi N.alpha N.beta (Sum.inl y0)
  let H0 := TwoColorIncidenceGraph G phi N.alpha N.beta
  have hpmaxsupport' : {z | z ∈ pmax.support} = C0 := by
    simpa [C0, i0, y0] using hpmaxsupport
  have hC0root : Sum.inl y0 ∈ C0 := by
    change Sum.inl y0 ∈ H0.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have C0_of_adj {x z : Sum V E} (hx : x ∈ C0) (hxz : H0.Adj x z) : z ∈ C0 := by
    change H0.connectedComponentMk x = H0.connectedComponentMk (Sum.inl y0) at hx
    change H0.connectedComponentMk z = H0.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans hx
  obtain ⟨p0, hp0, hp0support, hp0div, hp0vertices, hp0bound⟩ :=
    ScheideKempePathHeightBound G k e0 phi T N.global N.alpha N.beta
      N.alpha_missing N.beta_missing
  have hp0support' : {z | z ∈ p0.support} = C0 := by
    simpa [C0, y0] using hp0support
  have support_of_C0 {z : Sum V E} (hz : z ∈ C0) : z ∈ p0.support := by
    change z ∈ {w | w ∈ p0.support}
    rw [hp0support']
    exact hz
  have hq0adj : H0.Adj (Sum.inl y0) (Sum.inr q) := by
    simp [H0, TwoColorIncidenceGraph, Incident, hqends, hqcolor, Sym2.mem_iff]
  have hqC0 : Sum.inr q ∈ C0 := C0_of_adj hC0root hq0adj
  have hq4adj : H0.Adj (Sum.inr q) (Sum.inl y4) := by
    simp [H0, TwoColorIncidenceGraph, Incident, hqends, hqcolor, Sym2.mem_iff]
  have hy4C0 : Sum.inl y4 ∈ C0 := C0_of_adj hqC0 hq4adj
  have ha34adj : H0.Adj (Sum.inl y4) (Sum.inr a3) := by
    simp [H0, TwoColorIncidenceGraph, Incident, ha3ends, ha3color, Sym2.mem_iff]
  have ha3C0 : Sum.inr a3 ∈ C0 := C0_of_adj hy4C0 ha34adj
  have ha33adj : H0.Adj (Sum.inr a3) (Sum.inl y3) := by
    simp [H0, TwoColorIncidenceGraph, Incident, ha3ends, ha3color, Sym2.mem_iff]
  have hy3C0 : Sum.inl y3 ∈ C0 := C0_of_adj ha3C0 ha33adj
  have ha23adj : H0.Adj (Sum.inl y3) (Sum.inr a2) := by
    simp [H0, TwoColorIncidenceGraph, Incident, ha2ends, ha2color, Sym2.mem_iff]
  have ha2C0 : Sum.inr a2 ∈ C0 := C0_of_adj hy3C0 ha23adj
  have ha22adj : H0.Adj (Sum.inr a2) (Sum.inl y2) := by
    simp [H0, TwoColorIncidenceGraph, Incident, ha2ends, ha2color, Sym2.mem_iff]
  have hy2C0 : Sum.inl y2 ∈ C0 := C0_of_adj ha2C0 ha22adj
  have ha12adj : H0.Adj (Sum.inl y2) (Sum.inr a1) := by
    simp [H0, TwoColorIncidenceGraph, Incident, ha1ends, ha1color, Sym2.mem_iff]
  have ha1C0 : Sum.inr a1 ∈ C0 := C0_of_adj hy2C0 ha12adj
  have ha11adj : H0.Adj (Sum.inr a1) (Sum.inl y1) := by
    simp [H0, TwoColorIncidenceGraph, Incident, ha1ends, ha1color, Sym2.mem_iff]
  have hy1C0 : Sum.inl y1 ∈ C0 := C0_of_adj ha1C0 ha11adj
  have ha13ne : a1 ≠ a3 := by
    intro h
    exact (show r1 ≠ r3 by simp [r1, r3])
      (T.edge_injective (by simpa [a1, a3] using h))
  have hqa1 : q ≠ a1 := by
    intro h
    have hc : some N.beta = some N.alpha := by rw [← hqcolor, h, ha1color]
    exact hab (Option.some.inj hc).symm
  have hqa3 : q ≠ a3 := by
    intro h
    have hc : some N.beta = some N.alpha := by rw [← hqcolor, h, ha3color]
    exact hab (Option.some.inj hc).symm
  have hqa2 : q ≠ a2 := by
    exact @SharedFacts.ScheideHeightFiveGammaEdges.hqa2 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@hy24) (@hy34) (@ha2ends) (@hqends)
  let K0 : Finset (Sum V E) :=
    {Sum.inl y0, Sum.inl y1, Sum.inl y2, Sum.inl y3, Sum.inl y4,
      Sum.inr q, Sum.inr a1, Sum.inr a2, Sum.inr a3}
  have hK0card : K0.card = 9 := by
    simp [K0, hy01, hy02, hy03, hy04, hy12, hy13, hy14, hy23, hy24, hy34,
      ha12ne, ha13ne, ha23ne, hqa1, hqa2, hqa3]
  have hK0sub : K0 ⊆ p0.support.toFinset := by
    exact @helper_hK0sub_601 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@hC0root) (@p0) (@support_of_C0) (@hqC0)
        (@hy4C0) (@ha3C0) (@hy3C0) (@ha2C0) (@hy2C0) (@ha1C0) (@hy1C0)
  have hp0lower : 8 ≤ p0.length := by
    have hc := Finset.card_le_card hK0sub
    rw [hK0card, List.toFinset_card_of_nodup hp0.support_nodup,
      SimpleGraph.Walk.length_support] at hc
    omega
  have hp0bound' : p0.length / 2 + 1 ≤ 5 := by
    simpa [hGheight] using hp0bound
  have hp0length : p0.length = 8 := by
    rcases hp0div with ⟨d, hd⟩
    omega
  have hp0card : p0.support.toFinset.card = 9 := by
    rw [List.toFinset_card_of_nodup hp0.support_nodup,
      SimpleGraph.Walk.length_support, hp0length]
  have hK0eq : K0 = p0.support.toFinset :=
    Finset.eq_of_subset_of_card_le hK0sub (by rw [hK0card, hp0card])
  have hv1notC0 : Sum.inl v1 ∉ C0 := by
    exact @helper_hv1notC0_629 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@v1) (@hv10') (@hv11') (@hv12') (@hv13')
        (@hv14') (@p0) (@support_of_C0) (@hK0eq)
  have hgamma_alpha : gamma ≠ N.alpha := by
    exact @helper_hgamma_alpha_643 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@f1) (@v1) (@hf1color) (@hf1ends')
        (@C0_of_adj) (@hy1C0) (@hv1notC0)
  let phi' := TwoColorComponentSwap G phi N.alpha N.beta (Sum.inl y0)
  have hproper' : IsProperEdgeColoring G phi' := by
    simpa [phi', y0, i0] using hchangedata.1
  have hone' : IsOneEdgeUncolored phi' e0 := by
    simpa [phi', y0, i0] using hchangedata.2.1
  have hTash' : TashkinovTree G e0 phi' T := by
    simpa [phi', y0, i0] using hchangedata.2.2
  have hglobal' : GlobalMaximumTriple G k e0 phi' T := by
    refine ⟨⟨N.global.1.1, N.global.1.2.1, N.global.1.2.2.1,
      hproper', hone'⟩, hTash', N.global.2.2⟩
  have hgamma_fixed (e : E) : phi' e = some gamma ↔ phi e = some gamma := by
    exact TwoColorComponentSwap.otherColor_iff (G := G) (phi := phi)
      (z := Sum.inl y0) hgamma_alpha hgamma_beta e
  have hf1color' : phi' f1 = some gamma := (hgamma_fixed f1).2 hf1color
  have hf2color' : phi' f2 = some gamma := (hgamma_fixed f2).2 hf2color
  have hqcolor' : phi' q = some N.alpha := by
    simp [phi', TwoColorComponentSwap, C0, hqC0, hqcolor]
  have hgamma' : gamma ∈ MissingColors G phi' y0 := by
    exact @helper_hgamma_677 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@gamma) (@hgamma) (@hgamma_fixed)
  have halpha' : N.alpha ∈ MissingColors G phi' y1 := by
    exact @helper_halpha_689 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@missing_excludes) (@hab) (@C0_of_adj) (@hy1C0)
  have missing_excludes' {c : Fin k} {v : V} {f : E}
      (hc : c ∈ MissingColors G phi' v) (hinc : Incident G v f) :
      phi' f ≠ some c := by
    exact @helper_missing_excludes_713 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@c) (@v) (@f) (@hc) (@hinc)
  obtain ⟨p2, hp2, hp2support, hp2div, hp2vertices, hp2bound⟩ :=
    ScheideKempePathHeightBound G k e0 phi' T hglobal' gamma N.alpha
      (by simpa [y0] using hgamma') (by simpa [y1] using halpha')
  have hp2bound' : p2.length / 2 + 1 ≤ 5 := by
    simpa [hGheight] using hp2bound
  let H2 := TwoColorIncidenceGraph G phi' gamma N.alpha
  let C2 := TwoColorComponent G phi' gamma N.alpha (Sum.inl y0)
  have hp2support' : {z | z ∈ p2.support} = C2 := by
    simpa [C2, y0] using hp2support
  have hC2root : Sum.inl y0 ∈ C2 := by
    change Sum.inl y0 ∈ H2.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  have C2_of_adj {x z : Sum V E} (hx : x ∈ C2) (hxz : H2.Adj x z) : z ∈ C2 := by
    change H2.connectedComponentMk x = H2.connectedComponentMk (Sum.inl y0) at hx
    change H2.connectedComponentMk z = H2.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans hx
  have support_of_C2 {z : Sum V E} (hz : z ∈ C2) : z ∈ p2.support := by
    change z ∈ {w | w ∈ p2.support}
    rw [hp2support']
    exact hz
  have hy0p2 : Sum.inl y0 ∈ p2.support := support_of_C2 hC2root
  have hqadj02 : H2.Adj (Sum.inl y0) (Sum.inr q) := by
    simp [H2, TwoColorIncidenceGraph, Incident, hqends, hqcolor', Sym2.mem_iff]
  have hqC2 : Sum.inr q ∈ C2 := C2_of_adj hC2root hqadj02
  have hqp2 : Sum.inr q ∈ p2.support := support_of_C2 hqC2
  have hqadj42 : H2.Adj (Sum.inr q) (Sum.inl y4) := by
    simp [H2, TwoColorIncidenceGraph, Incident, hqends, hqcolor', Sym2.mem_iff]
  have hy4C2 : Sum.inl y4 ∈ C2 := C2_of_adj hqC2 hqadj42
  have hy4p2 : Sum.inl y4 ∈ p2.support := support_of_C2 hy4C2
  have hf2adj42 : H2.Adj (Sum.inl y4) (Sum.inr f2) := by
    simp [H2, TwoColorIncidenceGraph, Incident, hf2ends', hf2color', Sym2.mem_iff]
  have hf2C2 : Sum.inr f2 ∈ C2 := C2_of_adj hy4C2 hf2adj42
  have hf2p2 : Sum.inr f2 ∈ p2.support := support_of_C2 hf2C2
  have hf2adjv22 : H2.Adj (Sum.inr f2) (Sum.inl v2) := by
    simp [H2, TwoColorIncidenceGraph, Incident, hf2ends', hf2color', Sym2.mem_iff]
  have hv2C2 : Sum.inl v2 ∈ C2 := C2_of_adj hf2C2 hf2adjv22
  have hv2p2 : Sum.inl v2 ∈ p2.support := support_of_C2 hv2C2
  exact @helper_continuation_2397 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@hGheight) (@gamma) (@f1) (@f2)
      (@v1) (@v2) (by assumption) (@hqends) (@hf1ends') (@hv20') (@hv21') (@hv24') (@p1)
      (@hK8card) (@iv2) (@b) (@hf2inc) (@hbcolor) (@w) (@hbends') (@hab) (@pmax) (@C0_of_adj)
      (@p0) (@hv1notC0) (@hgamma_alpha) (@hproper') (@hf1color') (@hf2color') (@hqcolor')
      (@halpha') (@missing_excludes') (@p2) (@hp2) (@hp2div) (@hp2bound) (@hp2support')
      (@C2_of_adj) (@support_of_C2) (@hy0p2) (@hqp2) (@hy4p2) (@hf2p2) (@hv2p2)
private theorem helper_continuation_1992.{u_1, u_2} :
    helperContinuation1992Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T N hNheight hGheight gamma hgamma f1 f2 v1 v2 hf1color hf2color _
      y0 y1 y2 y3 y4 r1 r2 r3 a1 a2 a3 q hy01 hy02 hy03 hy04 hy12 hy13 hy14 hy23 hy24 hy34
      ha1ends ha2ends ha3ends hqends hproper missing_excludes ha1color ha12ne ha2color ha23ne
      ha3color hqcolor hgamma_beta hf1ends' hf2ends' hv10' hv11' hv12' hv13' hv14' hv20' hv21'
      hv22' hv23' hv24' hf12ne hv12ne hqf1 hqf2 p1 hp1 hp1div hp1bound H1 C1 hp1support' hC1root
  have C1_of_adj {x z : Sum V E} (hx : x ∈ C1) (hxz : H1.Adj x z) : z ∈ C1 := by
    change H1.connectedComponentMk x = H1.connectedComponentMk (Sum.inl y0) at hx
    change H1.connectedComponentMk z = H1.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans hx
  have support_of_C1 {z : Sum V E} (hz : z ∈ C1) : z ∈ p1.support := by
    change z ∈ {w | w ∈ p1.support}
    rw [hp1support']
    exact hz
  have hy0p1 : Sum.inl y0 ∈ p1.support := support_of_C1 hC1root
  have hqadj0 : H1.Adj (Sum.inl y0) (Sum.inr q) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hqends, hqcolor, Sym2.mem_iff]
  have hqC1 : Sum.inr q ∈ C1 := C1_of_adj hC1root hqadj0
  have hqp1 : Sum.inr q ∈ p1.support := support_of_C1 hqC1
  have hqadj4 : H1.Adj (Sum.inr q) (Sum.inl y4) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hqends, hqcolor, Sym2.mem_iff]
  have hy4C1 : Sum.inl y4 ∈ C1 := C1_of_adj hqC1 hqadj4
  have hy4p1 : Sum.inl y4 ∈ p1.support := support_of_C1 hy4C1
  have hf2adj4 : H1.Adj (Sum.inl y4) (Sum.inr f2) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hf2ends', hf2color, Sym2.mem_iff]
  have hf2C1 : Sum.inr f2 ∈ C1 := C1_of_adj hy4C1 hf2adj4
  have hf2p1 : Sum.inr f2 ∈ p1.support := support_of_C1 hf2C1
  have hf2adjv2 : H1.Adj (Sum.inr f2) (Sum.inl v2) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hf2ends', hf2color, Sym2.mem_iff]
  have hv2C1 : Sum.inl v2 ∈ C1 := C1_of_adj hf2C1 hf2adjv2
  have hv2p1 : Sum.inl v2 ∈ p1.support := support_of_C1 hv2C1
  have hy1p1 : Sum.inl y1 ∈ p1.support := by
    simpa [y1] using p1.end_mem_support
  have hy1C1 : Sum.inl y1 ∈ C1 := by
    rw [← hp1support']
    exact hy1p1
  have hf1adj1 : H1.Adj (Sum.inl y1) (Sum.inr f1) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hf1ends', hf1color, Sym2.mem_iff]
  have hf1C1 : Sum.inr f1 ∈ C1 := C1_of_adj hy1C1 hf1adj1
  have hf1p1 : Sum.inr f1 ∈ p1.support := support_of_C1 hf1C1
  have hf1adjv1 : H1.Adj (Sum.inr f1) (Sum.inl v1) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hf1ends', hf1color, Sym2.mem_iff]
  have hv1C1 : Sum.inl v1 ∈ C1 := C1_of_adj hf1C1 hf1adjv1
  have hv1p1 : Sum.inl v1 ∈ p1.support := support_of_C1 hv1C1
  let K8 : Finset (Sum V E) :=
    {Sum.inl y0, Sum.inl y1, Sum.inl y4, Sum.inl v1, Sum.inl v2,
      Sum.inr q, Sum.inr f1, Sum.inr f2}
  have hK8card : K8.card = 8 := by
    simp [K8, hy01, hy04, hy14, hv12ne, hqf1, hqf2, hf12ne, Ne.symm hv10', Ne.symm hv11', Ne.symm
        hv14', Ne.symm hv20',
      Ne.symm hv21', Ne.symm hv24']
  have hK8sub : K8 ⊆ p1.support.toFinset := by
    exact @helper_hK8sub_343 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@f1) (@f2) (@v1) (@v2) (@p1)
        (@hy0p1) (@hqp1) (@hy4p1) (@hf2p1) (@hv2p1) (@hy1p1) (@hf1p1) (@hv1p1)
  have hp1lower : 7 ≤ p1.length := by
    have hc := Finset.card_le_card hK8sub
    rw [hK8card, List.toFinset_card_of_nodup hp1.support_nodup,
      SimpleGraph.Walk.length_support] at hc
    omega
  have hp1length : p1.length = 8 := by
    rcases hp1div with ⟨d, hd⟩
    omega
  obtain ⟨iv2, hiv2, hiv2le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv2p1
  have hiv20 : iv2 ≠ 0 := by
    intro h
    have hv : (Sum.inl v2 : Sum V E) = Sum.inl y0 := by
      rw [← hiv2, h, p1.getVert_zero]
    exact hv20' (Sum.inl_injective hv)
  have hiv2lt : iv2 < p1.length := by
    exact @helper_hiv2lt_370 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@gamma) (@f1) (@f2) (@v1) (@v2) (@hv21') (@p1) (@hp1div)
        (@hp1length) (@iv2) (@hiv2) (@hiv2le)
  have hprevAdj : H1.Adj (Sum.inl v2) (p1.getVert (iv2 - 1)) := by
    have h := (p1.adj_getVert_succ (i := iv2 - 1) (by omega)).symm
    have heq : iv2 - 1 + 1 = iv2 := by omega
    rw [heq, hiv2] at h
    exact h
  have hnextAdj : H1.Adj (Sum.inl v2) (p1.getVert (iv2 + 1)) := by
    have h := p1.adj_getVert_succ hiv2lt
    rw [hiv2] at h
    exact h
  have hprevnext : p1.getVert (iv2 - 1) ≠ p1.getVert (iv2 + 1) := by
    exact @helper_hprevnext_387 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@f1) (@f2) (@v1) (@v2) (@p1) (@hp1)
        (@hp1div) (@hp1length) (@iv2) (@hiv2le) (@hiv2lt)
  obtain ⟨b, hbAdj, hbp1, hbf2⟩ : ∃ b : E,
      H1.Adj (Sum.inl v2) (Sum.inr b) ∧ Sum.inr b ∈ p1.support ∧ b ≠ f2 := by
    by_cases hp : p1.getVert (iv2 - 1) = Sum.inr f2
    · exact @helper_branch_396 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@gamma) (@f2) (@v2) (@p1) (@iv2) (@hnextAdj) (@hprevnext) (@hp)
    · exact @helper_branch_408 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@gamma) (@f2) (@v2) (@p1) (@iv2) (@hprevAdj) (@hp)
  have hbinc : Incident G v2 b := by
    simpa [H1, TwoColorIncidenceGraph] using hbAdj |>.1
  have hf2inc : Incident G v2 f2 := by
    unfold Incident
    rw [hf2ends']
    simp [Sym2.mem_iff]
  have hfbadj : AdjacentEdges G f2 b := ⟨v2, hf2inc, hbinc⟩
  have hbcolor : phi b = some N.beta := by
    have hc : phi b = some gamma ∨ phi b = some N.beta := by
      simpa [H1, TwoColorIncidenceGraph] using hbAdj |>.2
    exact hc.resolve_left (hproper hbf2.symm hfbadj hf2color)
  obtain ⟨w, hbends⟩ := Sym2.mem_iff_exists.mp hbinc
  have hbq : b ≠ q := by
    exact @helper_hbq_431 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@v2) (@hqends) (@hv20') (@hv24') (@b) (@w) (@hbends)
  have hbf1 : b ≠ f1 := by
    intro h
    have hc : some N.beta = some gamma := by rw [← hbcolor, h, hf1color]
    exact hgamma_beta (Option.some.inj hc).symm
  let K9 : Finset (Sum V E) := insert (Sum.inr b) K8
  have hK9card : K9.card = 9 := by
    rw [Finset.card_insert_of_notMem]
    · rw [hK8card]
    · simp [K8, hbf2, hbf1, hbq]
  have hK9sub : K9 ⊆ p1.support.toFinset := by
    exact @helper_hK9sub_447 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@f1) (@f2) (@v1) (@v2) (@p1)
        (@hK8sub) (@b) (@hbp1)
  have hp1card : p1.support.toFinset.card = 9 := by
    rw [List.toFinset_card_of_nodup hp1.support_nodup,
      SimpleGraph.Walk.length_support, hp1length]
  have hK9eq : K9 = p1.support.toFinset := by
    exact Finset.eq_of_subset_of_card_le hK9sub (by rw [hK9card, hp1card])
  have hbAdjw : H1.Adj (Sum.inr b) (Sum.inl w) := by
    simp [H1, TwoColorIncidenceGraph, Incident, hbends, hbcolor, Sym2.mem_iff]
  have hbC1 : Sum.inr b ∈ C1 := by
    rw [← hp1support']
    exact hbp1
  have hwC1 : Sum.inl w ∈ C1 := C1_of_adj hbC1 hbAdjw
  have hwp1 : Sum.inl w ∈ p1.support := support_of_C1 hwC1
  have hwcases : w = y0 ∨ w = y1 ∨ w = y4 ∨ w = v1 ∨ w = v2 := by
    have hwfin : Sum.inl w ∈ K9 := by
      rw [hK9eq]
      simpa using hwp1
    simpa [K9, K8] using hwfin
  have hwy0 : w ≠ y0 := by
    exact @helper_hwy0_470 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@v2) (@hqends) (@hproper) (@hqcolor) (@b) (@hbcolor) (@w)
        (@hbends) (@hbq)
  have hwy1 : w ≠ y1 := by
    exact @helper_hwy1_480 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@v2) (@missing_excludes) (@b) (@hbcolor) (@w) (@hbends)
  have hwy4 : w ≠ y4 := by
    exact @helper_hwy4_487 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@v2) (@hqends) (@hproper) (@hqcolor) (@b) (@hbcolor) (@w)
        (@hbends) (@hbq)
  have hwv2 : w ≠ v2 := by
    intro h
    exact G.loopless b v2 (by simpa [h] using hbends)
  have hwv1 : w = v1 := by
    simpa only [hwy0, hwy1, hwy4, hwv2, false_or, or_false] using hwcases
  have hbends' : G.ends b = s(v1, v2) := by
    rw [hbends, hwv1, Sym2.eq_swap]
  have hfixed : FixedPairMaximalTashkinovTree G e0 phi T := by
    exact @helper_hfixed_509 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N)
  let i0 : Fin (T.length + 1) := ⟨0, by omega⟩
  let i1 : Fin (T.length + 1) := ⟨1, by have := N.height_upper; omega⟩
  obtain ⟨hab, pmax, hpmax, hpmaxsupport, hpmaxdiv, hpmaxvertices, hchange⟩ :=
    ScheideMaximalKempePath G k e0 phi T T N.global.1 hfixed N.global.2.1
      i0 i1 (by simp [i0, i1]) N.alpha N.beta
      (by simpa [i0] using N.alpha_missing)
      (by simpa [i1] using N.beta_missing)
  have hunused : TreeColorUnusedThrough phi T N.alpha i1 := by
    intro r hr hrj
    simp [i1] at hrj
    omega
  have hchangedata := hchange hunused
  exact @helper_continuation_2127 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@hGheight) (@gamma) (@hgamma)
      (@f1) (@f2) (@v1) (@v2) (@hf1color) (@hf2color) (by assumption) (@hy01) (@hy02) (@hy03)
      (@hy04) (@hy12) (@hy13) (@hy14) (@hy23) (@hy24) (@hy34) (@ha1ends) (@ha2ends) (@ha3ends)
      (@hqends) (@missing_excludes) (@ha1color) (@ha12ne) (@ha2color) (@ha23ne) (@ha3color)
      (@hqcolor) (@hgamma_beta) (@hf1ends') (@hf2ends') (@hv10') (@hv11') (@hv12') (@hv13')
      (@hv14') (@hv20') (@hv21') (@hv22') (@hv23') (@hv24') (@p1) (@hK8card) (@iv2) (@b)
      (@hf2inc) (@hbcolor) (@w) (@hbends') (@hab) (@pmax) (@hpmaxsupport) (@hchangedata)
theorem ScheideHeightFiveOutsideLinks {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hNheight : N.height = 5) (hGheight : ScheideGraphHeight G = 5)
    (gamma : Fin k)
    (hgamma : gamma ∈ MissingColors G phi
      (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
    (f1 f2 : E) (v1 v2 : V)
    (hf1ends : G.ends f1 =
      s(T.vertex ⟨1, by have := N.height_upper; omega⟩, v1))
    (hf2ends : G.ends f2 =
      s(T.vertex ⟨4, by have := N.height_upper; omega⟩, v2))
    (hf1color : phi f1 = some gamma) (hf2color : phi f2 = some gamma)
    (_ : v1 ∈ TreeSequenceVertexSet T)
    (_ : v2 ∈ TreeSequenceVertexSet T)
    (hv10 : v1 ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩)
    (hv11 : v1 ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩)
    (hv12 : v1 ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩)
    (hv13 : v1 ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩)
    (hv14 : v1 ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩)
    (hv20 : v2 ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩)
    (hv21 : v2 ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩)
    (hv22 : v2 ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩)
    (hv23 : v2 ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩)
    (hv24 : v2 ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩) :
    ∃ alphaEdge betaEdge : E,
    G.ends alphaEdge = s(v1, v2) ∧
      phi alphaEdge = some N.alpha ∧
        G.ends betaEdge = s(v1, v2) ∧ phi betaEdge = some N.beta ∧ alphaEdge ≠ betaEdge := by
  classical
  let y0 : V := T.vertex ⟨0, by have := N.height_upper; omega⟩
  let y1 : V := T.vertex ⟨1, by have := N.height_upper; omega⟩
  let y2 : V := T.vertex ⟨2, by have := N.height_upper; omega⟩
  let y3 : V := T.vertex ⟨3, by have := N.height_upper; omega⟩
  let y4 : V := T.vertex ⟨4, by have := N.height_upper; omega⟩
  let r1 : Fin T.length := ⟨1, by have := N.height_upper; omega⟩
  let r2 : Fin T.length := ⟨2, by have := N.height_upper; omega⟩
  let r3 : Fin T.length := ⟨3, by have := N.height_upper; omega⟩
  let a1 : E := T.edge r1
  let a2 : E := T.edge r2
  let a3 : E := T.edge r3
  let q : E := N.closingEdge
  have hy01 : y0 ≠ y1 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy02 : y0 ≠ y2 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy03 : y0 ≠ y3 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy04 : y0 ≠ y4 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy12 : y1 ≠ y2 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy13 : y1 ≠ y3 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy14 : y1 ≠ y4 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy23 : y2 ≠ y3 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy24 : y2 ≠ y4 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy34 : y3 ≠ y4 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have ha1ends : G.ends a1 = s(y1, y2) := by
    simpa [a1, r1, y1, y2, hNheight] using N.trunk_edge_ends r1 (by simp [r1])
      (by simp [r1, hNheight])
  have ha2ends : G.ends a2 = s(y2, y3) := by
    simpa [a2, r2, y2, y3, hNheight] using N.trunk_edge_ends r2 (by simp [r2])
      (by simp [r2, hNheight])
  have ha3ends : G.ends a3 = s(y3, y4) := by
    simpa [a3, r3, y3, y4, hNheight] using N.trunk_edge_ends r3 (by simp [r3])
      (by simp [r3, hNheight])
  have hqends : G.ends q = s(y4, y0) := by
    exact @SharedFacts.ScheideHeightFiveGammaEdges.hqends (@V) (@E) inferInstance
        inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight)
  have hproper : IsProperEdgeColoring G phi := N.global.1.2.2.2.1
  have missing_excludes {c : Fin k} {v : V} {f : E}
      (hc : c ∈ MissingColors G phi v) (hinc : Incident G v f) :
      phi f ≠ some c := by
    exact @helper_missing_excludes_146 (@V) (@E) inferInstance inferInstance (@G) (@k) (@phi)
        (@c) (@v) (@f) (@hc) (@hinc)
  have edge_color_of_closing_support (f : E)
      (hf : Sum.inr f ∈ N.closingPath.support) :
      phi f = some N.alpha ∨ phi f = some N.beta := by
    exact @helper_edge_color_of_closing_support_156 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@e0) (@phi) (@T) (@N) (@f) (@hf)
  have ha1support : Sum.inr a1 ∈ N.closingPath.support := by
    apply (N.closingPath_edges a1).2
    exact Or.inr ⟨r1, by simp [r1], by simp [r1, hNheight], rfl⟩
  have ha2support : Sum.inr a2 ∈ N.closingPath.support := by
    apply (N.closingPath_edges a2).2
    exact Or.inr ⟨r2, by simp [r2], by simp [r2, hNheight], rfl⟩
  have ha3support : Sum.inr a3 ∈ N.closingPath.support := by
    apply (N.closingPath_edges a3).2
    exact Or.inr ⟨r3, by simp [r3], by simp [r3, hNheight], rfl⟩
  have hqsupport : Sum.inr q ∈ N.closingPath.support := by
    exact (N.closingPath_edges q).2 (Or.inl rfl)
  have ha1color : phi a1 = some N.alpha := by
    exact @helper_ha1color_190 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@hNheight) (@ha1ends) (@missing_excludes)
        (@edge_color_of_closing_support) (@ha1support)
  have ha1a2 : AdjacentEdges G a1 a2 := by
    exact @helper_ha1a2_200 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@ha1ends) (@ha2ends)
  have ha12ne : a1 ≠ a2 := by
    intro h
    exact (show r1 ≠ r2 by simp [r1, r2]) (T.edge_injective (by simpa [a1, a2] using h))
  have ha2color : phi a2 = some N.beta := by
    rcases edge_color_of_closing_support a2 ha2support with h | h
    · exact False.elim ((hproper ha12ne ha1a2 ha1color) h)
    · exact h
  have ha2a3 : AdjacentEdges G a2 a3 := by
    exact @helper_ha2a3_213 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@ha2ends) (@ha3ends)
  have ha23ne : a2 ≠ a3 := by
    intro h
    exact (show r2 ≠ r3 by simp [r2, r3]) (T.edge_injective (by simpa [a2, a3] using h))
  have ha3color : phi a3 = some N.alpha := by
    rcases edge_color_of_closing_support a3 ha3support with h | h
    · exact h
    · exact False.elim ((hproper ha23ne ha2a3 ha2color) h)
  have ha3q : AdjacentEdges G a3 q := by
    exact @helper_ha3q_226 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@ha3ends) (@hqends)
  have ha3qne : a3 ≠ q := by
    exact @SharedFacts.ScheideHeightFiveGammaEdges.ha3qne (@V) (@E) inferInstance
        inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@hy03) (@hy34) (@ha3ends) (@hqends)
  have hqcolor : phi q = some N.beta := by
    rcases edge_color_of_closing_support q hqsupport with h | h
    · exact False.elim ((hproper ha3qne ha3q ha3color) h)
    · exact h
  have hgamma_beta : gamma ≠ N.beta := by
    exact @helper_hgamma_beta_243 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@f1) (@v1) (@hf1ends) (@hf1color)
        (@missing_excludes)
  have hf1ends' : G.ends f1 = s(y1, v1) := by simpa [y1] using hf1ends
  have hf2ends' : G.ends f2 = s(y4, v2) := by simpa [y4] using hf2ends
  have hv10' : v1 ≠ y0 := by simpa [y0] using hv10
  have hv11' : v1 ≠ y1 := by simpa [y1] using hv11
  have hv12' : v1 ≠ y2 := by simpa [y2] using hv12
  have hv13' : v1 ≠ y3 := by simpa [y3] using hv13
  have hv14' : v1 ≠ y4 := by simpa [y4] using hv14
  have hv20' : v2 ≠ y0 := by simpa [y0] using hv20
  have hv21' : v2 ≠ y1 := by simpa [y1] using hv21
  have hv22' : v2 ≠ y2 := by simpa [y2] using hv22
  have hv23' : v2 ≠ y3 := by simpa [y3] using hv23
  have hv24' : v2 ≠ y4 := by simpa [y4] using hv24
  have hf12ne : f1 ≠ f2 := by
    exact @helper_hf12ne_263 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@f1) (@f2) (@v1) (@v2) (@hy14) (@hf1ends') (@hf2ends')
        (@hv21')
  have hv12ne : v1 ≠ v2 := by
    exact @helper_hv12ne_270 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@hNheight) (@gamma) (@f1) (@f2) (@v1) (@v2) (@hf1color) (@hf2color)
        (@hproper) (@hf1ends') (@hf2ends') (@hf12ne)
  have hqf1 : q ≠ f1 := by
    intro h
    have hc : some N.beta = some gamma := by rw [← hqcolor, h, hf1color]
    exact hgamma_beta (Option.some.inj hc).symm
  have hqf2 : q ≠ f2 := by
    intro h
    have hc : some N.beta = some gamma := by rw [← hqcolor, h, hf2color]
    exact hgamma_beta (Option.some.inj hc).symm
  obtain ⟨p1, hp1, hp1support, hp1div, hp1vertices, hp1bound⟩ :=
    ScheideKempePathHeightBound G k e0 phi T N.global gamma N.beta
      hgamma N.beta_missing
  have hp1bound' : p1.length / 2 + 1 ≤ 5 := by
    simpa [hGheight] using hp1bound
  let H1 := TwoColorIncidenceGraph G phi gamma N.beta
  let C1 := TwoColorComponent G phi gamma N.beta (Sum.inl y0)
  have hp1support' : {z | z ∈ p1.support} = C1 := by
    simpa [C1, y0] using hp1support
  have hC1root : Sum.inl y0 ∈ C1 := by
    change Sum.inl y0 ∈ H1.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl
  exact @helper_continuation_1992 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@hGheight) (@gamma) (@hgamma)
      (@f1) (@f2) (@v1) (@v2) (@hf1color) (@hf2color) (by assumption) (@hy01) (@hy02) (@hy03)
      (@hy04) (@hy12) (@hy13) (@hy14) (@hy23) (@hy24) (@hy34) (@ha1ends) (@ha2ends) (@ha3ends)
      (@hqends) (@hproper) (@missing_excludes) (@ha1color) (@ha12ne) (@ha2color) (@ha23ne)
      (@ha3color) (@hqcolor) (@hgamma_beta) (@hf1ends') (@hf2ends') (@hv10') (@hv11') (@hv12')
      (@hv13') (@hv14') (@hv20') (@hv21') (@hv22') (@hv23') (@hv24') (@hf12ne) (@hv12ne) (@hqf1)
      (@hqf2) (@p1) (@hp1) (@hp1div) (@hp1bound) (@hp1support') (@hC1root)
end GoldbergSeymour

end
