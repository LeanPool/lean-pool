/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideReplacementData
public import LeanPool.GoldbergSeymour.ScheideSymmetricReplacementBoundaryConfiguration
public import LeanPool.GoldbergSeymour.TreeFreeColors

/-!
# Scheide Symmetric Replacement Path Order

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation264Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) (beta : Fin k) (v z : V) (p : (TwoColorIncidenceGraph G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)), v ∈ TreeSequenceVertexSet
        T \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V) → beta ∈
        MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d))) v → beta ≠ C.gamma (D.gammaIndex d) → ScheideDefectiveChainPath
        R.replacementTree (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta v z p →
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let Xd : Finset V := TreeSequenceVertexSet R.replacementTree;
    let Z : Finset V := X \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phiD gamma beta; Z ⊆ Xd → v ∈ Xd →
        IsProperEdgeColoring G phiD → GlobalMaximumTriple G k e0 phiD R.replacementTree →
        ColoredVertexSetElementary G phiD Xd → ColoredVertexSetClosed G phiD Xd → C.gamma
        (D.gammaIndex d) ∈ DefectiveColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d))) (TreeSequenceVertexSet R.replacementTree) →
        TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))
        (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) = some (C.gamma (D.gammaIndex d)) →
        TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))
        (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) = some (C.gamma (D.gammaIndex d)) → (
    ∀ (f : E), (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)) f = some (C.gamma (D.gammaIndex d)) ∧
    ∃ v ∈ TreeSequenceVertexSet T \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V),
    ∃ w ∉ TreeSequenceVertexSet R.replacementTree, G.ends f = s(v, w)) ↔ f = D.f0 d ∨ f =
        C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) ∨ f = C.blockEdge (D.gammaIndex d) (1 : Fin
        (2 : ℕ))) → TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)) (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) = some (C.gamma (D.gammaIndex
        d)) → Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∈ p.support → Sum.inr
        (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∈ p.support →
    ∀ (h : E), G.ends h = s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)), C.blockVertex
        (D.gammaIndex d) (1 : Fin (2 : ℕ))) → (IsProperEdgeColoring G (TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) ∧ IsOneEdgeUncolored
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        e0 ∧ TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)) (D.f0 d) = some (C.gamma (D.gammaIndex d)) ∧ MissingColors G (TwoColorComponentSwap G
        phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) (D.v0 d) = (insert (↑d :
        Fin k) ((MissingColors G phi (D.v0 d)).erase (C.gamma (D.gammaIndex d))) : Finset (Fin k))
        ∧ (
    ∀ (f : E), (
    ∃ v ∈ TreeSequenceVertexSet T, Incident G v f) → ¬f = D.f0 d → TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f = phi f) ∧ (
    ∀ v ∈ TreeSequenceVertexSet T, ¬v = D.v0 d → MissingColors G (TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v = MissingColors G phi v) ∧
    ∀ (v : V), Sum.inl v ∉ TwoColorComponent G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)) → MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v = MissingColors G phi v) → phiD h = some beta →
    ∀ (a0 : Fin C.p), G.ends (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) = s(C.y a0,
        C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) →
    ∀ (a1 : Fin C.p), G.ends (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) = s(C.y a1,
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) → H.Adj (Sum.inr (C.blockEdge
        (D.gammaIndex d) (0 : Fin (2 : ℕ)))) (Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2
        : ℕ)))) → H.Adj (Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))) (Sum.inr h) →
        H.Adj (Sum.inr h) (Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ)))) → H.Adj
        (Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ)))) (Sum.inr (C.blockEdge
        (D.gammaIndex d) (1 : Fin (2 : ℕ)))) → Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2
        : ℕ))) ∈ p.support → Sum.inr h ∈ p.support → Sum.inl (C.blockVertex (D.gammaIndex d) (1 :
        Fin (2 : ℕ))) ∈ p.support → p.IsPath → (0 : ℕ) < p.length → (
    ∀ (x : V ⊕ E), H.Adj (Sum.inl v) x → x = p.getVert (1 : ℕ)) →
    ∃ (h : E) (i0 : Fin (p.length + (1 : ℕ))) (i1 : Fin (p.length + (1 : ℕ))) (i2 : Fin (p.length
        + (1 : ℕ))) (i3 : Fin (p.length + (1 : ℕ))) (i4 : Fin (p.length + (1 : ℕ))) (qv : Fin
        (p.length + (1 : ℕ))) (qf : Fin (p.length + (1 : ℕ))), TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) h = some beta ∧ G.ends h =
        s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) (1 :
        Fin (2 : ℕ))) ∧ (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) ∧ (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) ∧ (↑i3 :
        ℕ) = (↑i2 : ℕ) + (1 : ℕ) ∧ (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) ∧ (p.getVert (↑i0 : ℕ) =
        Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ) = Sum.inl
        (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) = Sum.inr h ∧
        p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧
        p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∨ p.getVert
        (↑i0 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ)
        = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) =
        Sum.inr h ∧ p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ))) ∧ p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)))) ∧
        (↑i4 : ℕ) < (↑qv : ℕ) ∧ (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) ∧ p.getVert (↑qv : ℕ) = Sum.inl
        (D.v0 d) ∧ p.getVert (↑qf : ℕ) = Sum.inr (D.f0 d) ∧ (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑qv : ℕ) < (↑r : ℕ) →
    ∀ (w : V), p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet R.replacementTree) ∧
        R.u1 ∉ ScheideExitVertices R.replacementTree (TwoColorComponentSwap G phi (C.gamma
        (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) ∧ R.u2 ∉ ScheideExitVertices
        R.replacementTree (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)))

private abbrev helperContinuation462Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) (beta : Fin k) (v z : V) (p : (TwoColorIncidenceGraph G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)), v ∈ TreeSequenceVertexSet
        T \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V) → beta ∈
        MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d))) v → ScheideDefectiveChainPath R.replacementTree (TwoColorComponentSwap
        G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex
        d)) beta v z p →
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let Xd : Finset V := TreeSequenceVertexSet R.replacementTree;
    let Z : Finset V := X \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phiD gamma beta; Z ⊆ Xd → v ∈ Xd →
        GlobalMaximumTriple G k e0 phiD R.replacementTree → ColoredVertexSetElementary G phiD Xd →
        ColoredVertexSetClosed G phiD Xd → C.gamma (D.gammaIndex d) ∈ DefectiveColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        (TreeSequenceVertexSet R.replacementTree) → (
    ∀ (f : E), (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)) f = some (C.gamma (D.gammaIndex d)) ∧
    ∃ v ∈ TreeSequenceVertexSet T \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V),
    ∃ w ∉ TreeSequenceVertexSet R.replacementTree, G.ends f = s(v, w)) ↔ f = D.f0 d ∨ f =
        C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) ∨ f = C.blockEdge (D.gammaIndex d) (1 : Fin
        (2 : ℕ))) → TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)) (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) = some (C.gamma (D.gammaIndex
        d)) →
    ∀ (h : E), G.ends h = s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)), C.blockVertex
        (D.gammaIndex d) (1 : Fin (2 : ℕ))) → (IsProperEdgeColoring G (TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) ∧ IsOneEdgeUncolored
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        e0 ∧ TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)) (D.f0 d) = some (C.gamma (D.gammaIndex d)) ∧ MissingColors G (TwoColorComponentSwap G
        phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) (D.v0 d) = (insert (↑d :
        Fin k) ((MissingColors G phi (D.v0 d)).erase (C.gamma (D.gammaIndex d))) : Finset (Fin k))
        ∧ (
    ∀ (f : E), (
    ∃ v ∈ TreeSequenceVertexSet T, Incident G v f) → ¬f = D.f0 d → TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) f = phi f) ∧ (
    ∀ v ∈ TreeSequenceVertexSet T, ¬v = D.v0 d → MissingColors G (TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v = MissingColors G phi v) ∧
    ∀ (v : V), Sum.inl v ∉ TwoColorComponent G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)) → MissingColors G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex
        d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v = MissingColors G phi v) → phiD h = some beta →
    ∀ (a0 : Fin C.p), G.ends (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) = s(C.y a0,
        C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) →
    ∀ (a1 : Fin C.p), G.ends (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) = s(C.y a1,
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) → p.IsPath → (0 : ℕ) < p.length →
    ∀ (j0 : ℕ), p.getVert j0 = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) → j0 ≤
        p.length →
    ∀ (j1 : ℕ), p.getVert j1 = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) →
    ∀ (j2 : ℕ), p.getVert j2 = Sum.inr h →
    ∀ (j3 : ℕ), p.getVert j3 = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) →
    ∀ (j4 : ℕ), p.getVert j4 = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) → j4 ≤
        p.length → j1 = j0 + (1 : ℕ) ∧ j2 = j1 + (1 : ℕ) ∧ j3 = j2 + (1 : ℕ) ∧ j4 = j3 + (1 : ℕ) ∨
        j3 = j4 + (1 : ℕ) ∧ j2 = j3 + (1 : ℕ) ∧ j1 = j2 + (1 : ℕ) ∧ j0 = j1 + (1 : ℕ) → (
    ∀ (q : Fin C.p), C.y q ∈ TreeSequenceVertexSet T) → (2 : ℕ) ≤ C.p → T.length + (1 : ℕ) = C.p +
        (2 : ℕ) * C.s → R.replacementTree.length = T.length → (↑(D.gammaIndex d) : ℕ) < C.s → (
    ∀ (q : Fin C.p), C.y q ∈ Z) →
    ∃ (h : E) (i0 : Fin (p.length + (1 : ℕ))) (i1 : Fin (p.length + (1 : ℕ))) (i2 : Fin (p.length
        + (1 : ℕ))) (i3 : Fin (p.length + (1 : ℕ))) (i4 : Fin (p.length + (1 : ℕ))) (qv : Fin
        (p.length + (1 : ℕ))) (qf : Fin (p.length + (1 : ℕ))), TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) h = some beta ∧ G.ends h =
        s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) (1 :
        Fin (2 : ℕ))) ∧ (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) ∧ (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) ∧ (↑i3 :
        ℕ) = (↑i2 : ℕ) + (1 : ℕ) ∧ (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) ∧ (p.getVert (↑i0 : ℕ) =
        Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ) = Sum.inl
        (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) = Sum.inr h ∧
        p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧
        p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∨ p.getVert
        (↑i0 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ)
        = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) =
        Sum.inr h ∧ p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ))) ∧ p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)))) ∧
        (↑i4 : ℕ) < (↑qv : ℕ) ∧ (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) ∧ p.getVert (↑qv : ℕ) = Sum.inl
        (D.v0 d) ∧ p.getVert (↑qf : ℕ) = Sum.inr (D.f0 d) ∧ (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑qv : ℕ) < (↑r : ℕ) →
    ∀ (w : V), p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet R.replacementTree) ∧
        R.u1 ∉ ScheideExitVertices R.replacementTree (TwoColorComponentSwap G phi (C.gamma
        (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) ∧ R.u2 ∉ ScheideExitVertices
        R.replacementTree (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)))

private abbrev helperContinuation790Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (R : ScheideReplacementData
        G k e0 phi T C D d) (beta : Fin k) (v z : V) (p : (TwoColorIncidenceGraph G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)), beta ∈ MissingColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) v
        → ScheideDefectiveChainPath R.replacementTree (TwoColorComponentSwap G phi (C.gamma
        (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta v z p →
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let Xd : Finset V := TreeSequenceVertexSet R.replacementTree;
    let Z : Finset V := X \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phiD gamma beta; Z ⊆ Xd → v ∈ Xd →
        GlobalMaximumTriple G k e0 phiD R.replacementTree → ColoredVertexSetElementary G phiD Xd →
        ColoredVertexSetClosed G phiD Xd → C.gamma (D.gammaIndex d) ∈ DefectiveColors G
        (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)))
        (TreeSequenceVertexSet R.replacementTree) → (
    ∀ (f : E), (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)) f = some (C.gamma (D.gammaIndex d)) ∧
    ∃ v ∈ TreeSequenceVertexSet T \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V),
    ∃ w ∉ TreeSequenceVertexSet R.replacementTree, G.ends f = s(v, w)) ↔ f = D.f0 d ∨ f =
        C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) ∨ f = C.blockEdge (D.gammaIndex d) (1 : Fin
        (2 : ℕ))) → TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)) (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) = some (C.gamma (D.gammaIndex
        d)) →
    ∀ (h : E), G.ends h = s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)), C.blockVertex
        (D.gammaIndex d) (1 : Fin (2 : ℕ))) → phiD h = some beta →
    ∀ (a0 : Fin C.p), G.ends (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) = s(C.y a0,
        C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) →
    ∀ (a1 : Fin C.p), G.ends (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) = s(C.y a1,
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) → p.IsPath → (0 : ℕ) < p.length →
    ∀ (j0 : ℕ), p.getVert j0 = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) → j0 ≤
        p.length →
    ∀ (j1 : ℕ), p.getVert j1 = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) →
    ∀ (j2 : ℕ), p.getVert j2 = Sum.inr h →
    ∀ (j3 : ℕ), p.getVert j3 = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) →
    ∀ (j4 : ℕ), p.getVert j4 = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) → j4 ≤
        p.length → j1 = j0 + (1 : ℕ) ∧ j2 = j1 + (1 : ℕ) ∧ j3 = j2 + (1 : ℕ) ∧ j4 = j3 + (1 : ℕ) ∨
        j3 = j4 + (1 : ℕ) ∧ j2 = j3 + (1 : ℕ) ∧ j1 = j2 + (1 : ℕ) ∧ j0 = j1 + (1 : ℕ) → (
    ∀ (q : Fin C.p), C.y q ∈ Z) → (
    ∀ c ∈ TreeUsedColors phiD R.replacementTree,
    ∃ y ∈ Z, c ∈ MissingColors G phiD y) →
    ∃ (h : E) (i0 : Fin (p.length + (1 : ℕ))) (i1 : Fin (p.length + (1 : ℕ))) (i2 : Fin (p.length
        + (1 : ℕ))) (i3 : Fin (p.length + (1 : ℕ))) (i4 : Fin (p.length + (1 : ℕ))) (qv : Fin
        (p.length + (1 : ℕ))) (qf : Fin (p.length + (1 : ℕ))), TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) h = some beta ∧ G.ends h =
        s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) (1 :
        Fin (2 : ℕ))) ∧ (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) ∧ (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) ∧ (↑i3 :
        ℕ) = (↑i2 : ℕ) + (1 : ℕ) ∧ (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) ∧ (p.getVert (↑i0 : ℕ) =
        Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ) = Sum.inl
        (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) = Sum.inr h ∧
        p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧
        p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∨ p.getVert
        (↑i0 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ)
        = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) =
        Sum.inr h ∧ p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ))) ∧ p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)))) ∧
        (↑i4 : ℕ) < (↑qv : ℕ) ∧ (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) ∧ p.getVert (↑qv : ℕ) = Sum.inl
        (D.v0 d) ∧ p.getVert (↑qf : ℕ) = Sum.inr (D.f0 d) ∧ (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑qv : ℕ) < (↑r : ℕ) →
    ∀ (w : V), p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet R.replacementTree) ∧
        R.u1 ∉ ScheideExitVertices R.replacementTree (TwoColorComponentSwap G phi (C.gamma
        (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) ∧ R.u2 ∉ ScheideExitVertices
        R.replacementTree (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)))

private abbrev helperBranch1139Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V) (p :
        (TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let Xd : Finset V := TreeSequenceVertexSet R.replacementTree;
    let Z : Finset V := X \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phiD gamma beta; Z ⊆ Xd →
    ∀ (h : E), G.ends h = s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)), C.blockVertex
        (D.gammaIndex d) (1 : Fin (2 : ℕ))) → phiD h = some beta →
    ∀ (a1 : Fin C.p), G.ends (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) = s(C.y a1,
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) → p.IsPath →
    ∀ (j0 : ℕ), p.getVert j0 = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) → j0 ≤
        p.length →
    ∀ (j1 : ℕ), p.getVert j1 = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) →
    ∀ (j2 : ℕ), p.getVert j2 = Sum.inr h →
    ∀ (j3 : ℕ), p.getVert j3 = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) →
    ∀ (j4 : ℕ), p.getVert j4 = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) → j4 ≤
        p.length → (
    ∀ (q : Fin C.p), C.y q ∈ Z) → R.u1 ∉ ScheideExitVertices R.replacementTree phiD → R.u2 ∉
        ScheideExitVertices R.replacementTree phiD →
    let insideIndices : Finset (Fin (p.length + (1 : ℕ))) := ({q : Fin (p.length + (1 : ℕ)) |
    ∃ w ∈ Xd, p.getVert (↑q : ℕ) = Sum.inl w} : Finset (Fin (p.length + (1 : ℕ))));
    ∀ (insideNonempty : insideIndices.Nonempty),
    let qv : Fin (p.length + (1 : ℕ)) := insideIndices.max' insideNonempty;
    ∀ w ∈ Xd, p.getVert (↑qv : ℕ) = Sum.inl w → (
    ∀ (q : Fin (p.length + (1 : ℕ))), (↑qv : ℕ) < (↑q : ℕ) →
    ∀ (a : V), p.getVert (↑q : ℕ) = Sum.inl a → a ∉ Xd) →
    ∀ (hqvlt : (↑qv : ℕ) < p.length),
    let qf : Fin (p.length + (1 : ℕ)) := (⟨(↑qv : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (p.length + (1 : ℕ))); (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) →
    ∀ (f : E), p.getVert (↑qf : ℕ) = Sum.inr f → Incident G w f → (↑qf : ℕ) < p.length → f = D.f0
        d ∨ f = C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) ∨ f = C.blockEdge (D.gammaIndex d)
        (1 : Fin (2 : ℕ)) → TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)) (D.f0 d) = some (C.gamma (D.gammaIndex d)) → D.u0 d ∉ Xd → j1 = j0 + (1
        : ℕ) ∧ j2 = j1 + (1 : ℕ) ∧ j3 = j2 + (1 : ℕ) ∧ j4 = j3 + (1 : ℕ) →
    ∃ (h : E) (i0 : Fin (p.length + (1 : ℕ))) (i1 : Fin (p.length + (1 : ℕ))) (i2 : Fin (p.length
        + (1 : ℕ))) (i3 : Fin (p.length + (1 : ℕ))) (i4 : Fin (p.length + (1 : ℕ))) (qv : Fin
        (p.length + (1 : ℕ))) (qf : Fin (p.length + (1 : ℕ))), TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) h = some beta ∧ G.ends h =
        s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) (1 :
        Fin (2 : ℕ))) ∧ (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) ∧ (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) ∧ (↑i3 :
        ℕ) = (↑i2 : ℕ) + (1 : ℕ) ∧ (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) ∧ (p.getVert (↑i0 : ℕ) =
        Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ) = Sum.inl
        (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) = Sum.inr h ∧
        p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧
        p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∨ p.getVert
        (↑i0 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ)
        = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) =
        Sum.inr h ∧ p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ))) ∧ p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)))) ∧
        (↑i4 : ℕ) < (↑qv : ℕ) ∧ (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) ∧ p.getVert (↑qv : ℕ) = Sum.inl
        (D.v0 d) ∧ p.getVert (↑qf : ℕ) = Sum.inr (D.f0 d) ∧ (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑qv : ℕ) < (↑r : ℕ) →
    ∀ (w : V), p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet R.replacementTree) ∧
        R.u1 ∉ ScheideExitVertices R.replacementTree (TwoColorComponentSwap G phi (C.gamma
        (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) ∧ R.u2 ∉ ScheideExitVertices
        R.replacementTree (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)))

private abbrev helperBranch1227Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V) (p :
        (TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let Xd : Finset V := TreeSequenceVertexSet R.replacementTree;
    let Z : Finset V := X \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phiD gamma beta; Z ⊆ Xd →
    ∀ (h : E), G.ends h = s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)), C.blockVertex
        (D.gammaIndex d) (1 : Fin (2 : ℕ))) → phiD h = some beta →
    ∀ (a0 : Fin C.p), G.ends (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) = s(C.y a0,
        C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) → p.IsPath →
    ∀ (j0 : ℕ), p.getVert j0 = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) → j0 ≤
        p.length →
    ∀ (j1 : ℕ), p.getVert j1 = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) →
    ∀ (j2 : ℕ), p.getVert j2 = Sum.inr h →
    ∀ (j3 : ℕ), p.getVert j3 = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) →
    ∀ (j4 : ℕ), p.getVert j4 = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) → j4 ≤
        p.length → (
    ∀ (q : Fin C.p), C.y q ∈ Z) → R.u1 ∉ ScheideExitVertices R.replacementTree phiD → R.u2 ∉
        ScheideExitVertices R.replacementTree phiD →
    let insideIndices : Finset (Fin (p.length + (1 : ℕ))) := ({q : Fin (p.length + (1 : ℕ)) |
    ∃ w ∈ Xd, p.getVert (↑q : ℕ) = Sum.inl w} : Finset (Fin (p.length + (1 : ℕ))));
    ∀ (insideNonempty : insideIndices.Nonempty),
    let qv : Fin (p.length + (1 : ℕ)) := insideIndices.max' insideNonempty;
    ∀ w ∈ Xd, p.getVert (↑qv : ℕ) = Sum.inl w → (
    ∀ (q : Fin (p.length + (1 : ℕ))), (↑qv : ℕ) < (↑q : ℕ) →
    ∀ (a : V), p.getVert (↑q : ℕ) = Sum.inl a → a ∉ Xd) →
    ∀ (hqvlt : (↑qv : ℕ) < p.length),
    let qf : Fin (p.length + (1 : ℕ)) := (⟨(↑qv : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (p.length + (1 : ℕ))); (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) →
    ∀ (f : E), p.getVert (↑qf : ℕ) = Sum.inr f → Incident G w f → (↑qf : ℕ) < p.length → f = D.f0
        d ∨ f = C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) ∨ f = C.blockEdge (D.gammaIndex d)
        (1 : Fin (2 : ℕ)) → D.u0 d ∉ Xd → j3 = j4 + (1 : ℕ) ∧ j2 = j3 + (1 : ℕ) ∧ j1 = j2 + (1 :
        ℕ) ∧ j0 = j1 + (1 : ℕ) →
    ∃ (h : E) (i0 : Fin (p.length + (1 : ℕ))) (i1 : Fin (p.length + (1 : ℕ))) (i2 : Fin (p.length
        + (1 : ℕ))) (i3 : Fin (p.length + (1 : ℕ))) (i4 : Fin (p.length + (1 : ℕ))) (qv : Fin
        (p.length + (1 : ℕ))) (qf : Fin (p.length + (1 : ℕ))), TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) h = some beta ∧ G.ends h =
        s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) (1 :
        Fin (2 : ℕ))) ∧ (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) ∧ (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) ∧ (↑i3 :
        ℕ) = (↑i2 : ℕ) + (1 : ℕ) ∧ (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) ∧ (p.getVert (↑i0 : ℕ) =
        Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ) = Sum.inl
        (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) = Sum.inr h ∧
        p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧
        p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∨ p.getVert
        (↑i0 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ)
        = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) =
        Sum.inr h ∧ p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ))) ∧ p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)))) ∧
        (↑i4 : ℕ) < (↑qv : ℕ) ∧ (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) ∧ p.getVert (↑qv : ℕ) = Sum.inl
        (D.v0 d) ∧ p.getVert (↑qf : ℕ) = Sum.inr (D.f0 d) ∧ (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑qv : ℕ) < (↑r : ℕ) →
    ∀ (w : V), p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet R.replacementTree) ∧
        R.u1 ∉ ScheideExitVertices R.replacementTree (TwoColorComponentSwap G phi (C.gamma
        (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) ∧ R.u2 ∉ ScheideExitVertices
        R.replacementTree (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)))

private abbrev helperContinuation981Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D :
        ScheideDefectiveSetup G k e0 phi T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet
        T))) (R : ScheideReplacementData G k e0 phi T C D d) (beta : Fin k) (v z : V) (p :
        (TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let X : Finset V := TreeSequenceVertexSet T;
    let Xd : Finset V := TreeSequenceVertexSet R.replacementTree;
    let Z : Finset V := X \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V);
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phiD gamma beta; Z ⊆ Xd → (
    ∀ (f : E), (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0
        d)) f = some (C.gamma (D.gammaIndex d)) ∧
    ∃ v ∈ TreeSequenceVertexSet T \ (insert (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)))
        ({C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))} : Finset V) : Finset V),
    ∃ w ∉ TreeSequenceVertexSet R.replacementTree, G.ends f = s(v, w)) ↔ f = D.f0 d ∨ f =
        C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)) ∨ f = C.blockEdge (D.gammaIndex d) (1 : Fin
        (2 : ℕ))) →
    ∀ (h : E), G.ends h = s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)), C.blockVertex
        (D.gammaIndex d) (1 : Fin (2 : ℕ))) → phiD h = some beta →
    ∀ (a0 : Fin C.p), G.ends (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) = s(C.y a0,
        C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) →
    ∀ (a1 : Fin C.p), G.ends (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) = s(C.y a1,
        C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) → p.IsPath →
    ∀ (j0 : ℕ), p.getVert j0 = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) → j0 ≤
        p.length →
    ∀ (j1 : ℕ), p.getVert j1 = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) →
    ∀ (j2 : ℕ), p.getVert j2 = Sum.inr h →
    ∀ (j3 : ℕ), p.getVert j3 = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) →
    ∀ (j4 : ℕ), p.getVert j4 = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) → j4 ≤
        p.length → j1 = j0 + (1 : ℕ) ∧ j2 = j1 + (1 : ℕ) ∧ j3 = j2 + (1 : ℕ) ∧ j4 = j3 + (1 : ℕ) ∨
        j3 = j4 + (1 : ℕ) ∧ j2 = j3 + (1 : ℕ) ∧ j1 = j2 + (1 : ℕ) ∧ j0 = j1 + (1 : ℕ) → (
    ∀ (q : Fin C.p), C.y q ∈ Z) → R.u1 ∉ ScheideExitVertices R.replacementTree phiD → R.u2 ∉
        ScheideExitVertices R.replacementTree phiD →
    let insideIndices : Finset (Fin (p.length + (1 : ℕ))) := ({q : Fin (p.length + (1 : ℕ)) |
    ∃ w ∈ Xd, p.getVert (↑q : ℕ) = Sum.inl w} : Finset (Fin (p.length + (1 : ℕ))));
    ∀ (insideNonempty : insideIndices.Nonempty),
    let qv : Fin (p.length + (1 : ℕ)) := insideIndices.max' insideNonempty;
    ∀ w ∈ Xd, p.getVert (↑qv : ℕ) = Sum.inl w → (
    ∀ (q : Fin (p.length + (1 : ℕ))), (↑qv : ℕ) < (↑q : ℕ) →
    ∀ (a : V), p.getVert (↑q : ℕ) = Sum.inl a → a ∉ Xd) →
    ∀ (hqvlt : (↑qv : ℕ) < p.length),
    let qf : Fin (p.length + (1 : ℕ)) := (⟨(↑qv : ℕ) + (1 : ℕ),
    by omega
    ⟩ : Fin (p.length + (1 : ℕ))); (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) →
    ∀ (f : E), p.getVert (↑qf : ℕ) = Sum.inr f → Incident G w f → (↑qf : ℕ) < p.length →
    ∀ x ∉ Xd, G.ends f = s(w, x) → phiD f = some gamma → w ∈ Z →
    ∃ (h : E) (i0 : Fin (p.length + (1 : ℕ))) (i1 : Fin (p.length + (1 : ℕ))) (i2 : Fin (p.length
        + (1 : ℕ))) (i3 : Fin (p.length + (1 : ℕ))) (i4 : Fin (p.length + (1 : ℕ))) (qv : Fin
        (p.length + (1 : ℕ))) (qf : Fin (p.length + (1 : ℕ))), TwoColorComponentSwap G phi
        (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) h = some beta ∧ G.ends h =
        s(C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ)), C.blockVertex (D.gammaIndex d) (1 :
        Fin (2 : ℕ))) ∧ (↑i1 : ℕ) = (↑i0 : ℕ) + (1 : ℕ) ∧ (↑i2 : ℕ) = (↑i1 : ℕ) + (1 : ℕ) ∧ (↑i3 :
        ℕ) = (↑i2 : ℕ) + (1 : ℕ) ∧ (↑i4 : ℕ) = (↑i3 : ℕ) + (1 : ℕ) ∧ (p.getVert (↑i0 : ℕ) =
        Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ) = Sum.inl
        (C.blockVertex (D.gammaIndex d) (0 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) = Sum.inr h ∧
        p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧
        p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∨ p.getVert
        (↑i0 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i1 : ℕ)
        = Sum.inl (C.blockVertex (D.gammaIndex d) (1 : Fin (2 : ℕ))) ∧ p.getVert (↑i2 : ℕ) =
        Sum.inr h ∧ p.getVert (↑i3 : ℕ) = Sum.inl (C.blockVertex (D.gammaIndex d) (0 : Fin (2 :
        ℕ))) ∧ p.getVert (↑i4 : ℕ) = Sum.inr (C.blockEdge (D.gammaIndex d) (0 : Fin (2 : ℕ)))) ∧
        (↑i4 : ℕ) < (↑qv : ℕ) ∧ (↑qf : ℕ) = (↑qv : ℕ) + (1 : ℕ) ∧ p.getVert (↑qv : ℕ) = Sum.inl
        (D.v0 d) ∧ p.getVert (↑qf : ℕ) = Sum.inr (D.f0 d) ∧ (
    ∀ (r : Fin (p.length + (1 : ℕ))), (↑qv : ℕ) < (↑r : ℕ) →
    ∀ (w : V), p.getVert (↑r : ℕ) = Sum.inl w → w ∉ TreeSequenceVertexSet R.replacementTree) ∧
        R.u1 ∉ ScheideExitVertices R.replacementTree (TwoColorComponentSwap G phi (C.gamma
        (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d))) ∧ R.u2 ∉ ScheideExitVertices
        R.replacementTree (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d : Fin k)
        (Sum.inl (D.v0 d)))

private theorem helper_branch_1139.{u_1, u_2} :
    helperBranch1139Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p gamma phiD X Xd Z H hZsubXd h hhends hhColor
      a1 ha1ends hpath j0 hj0 hj0le j1 hj1 j2 hj2 j3 hj3 j4 hj4 hj4le hbaseZ hu1NotExit
      hu2NotExit insideIndices insideNonempty qv w hwXd hqvw hafter hqvlt qf hqfval f hqff hwf
      hqflt hfThree _ hu0out horient
  rcases horient with ⟨hj01, hj12, hj23, hj34⟩
  let i0 : Fin (p.length + 1) := ⟨j0, by omega⟩
  let i1 : Fin (p.length + 1) := ⟨j1, by omega⟩
  let i2 : Fin (p.length + 1) := ⟨j2, by omega⟩
  let i3 : Fin (p.length + 1) := ⟨j3, by omega⟩
  let i4 : Fin (p.length + 1) := ⟨j4, by omega⟩
  have hi4lt : i4.val < p.length := by
    by_contra hn
    have heq : i4.val = p.length := by omega
    have hh := hj4
    rw [← show i4.val = j4 by rfl, heq, p.getVert_length] at hh
    simp at hh
  let ir : Fin (p.length + 1) := ⟨i4.val + 1, by omega⟩
  have hretAdj := p.adj_getVert_succ (i := i4.val) hi4lt
  have hret : p.getVert ir.val = Sum.inl (C.y a1) := by
    have hprev : p.getVert (i4.val - 1) =
        Sum.inl (C.blockVertex (D.gammaIndex d) 1) := by
      have heq : i4.val - 1 = j3 := by simp [i4]; omega
      simpa [heq] using hj3
    cases hcase : p.getVert ir.val with
    | inr e =>
        rw [show p.getVert i4.val = Sum.inr (C.blockEdge (D.gammaIndex d) 1) by
          simpa [i4] using hj4, hcase] at hretAdj
        simp [TwoColorIncidenceGraph] at hretAdj
    | inl y =>
        have hinc : Incident G y (C.blockEdge (D.gammaIndex d) 1) := by
          rw [show p.getVert i4.val = Sum.inr (C.blockEdge (D.gammaIndex d) 1) by
            simpa [i4] using hj4, hcase] at hretAdj
          have hadjData : Incident G y (C.blockEdge (D.gammaIndex d) 1) ∧
              (phiD (C.blockEdge (D.gammaIndex d) 1) = some gamma ∨
                phiD (C.blockEdge (D.gammaIndex d) 1) = some beta) := by
            simpa [H, ir, TwoColorIncidenceGraph] using hretAdj
          exact hadjData.1
        have hy : y = C.y a1 ∨ y = C.blockVertex (D.gammaIndex d) 1 := by
          simpa [Incident, ha1ends] using hinc
        rcases hy with rfl | rfl
        · simp
        · exfalso
          have hinj := hpath.getVert_injOn (by omega : i4.val - 1 ≤ p.length)
            (by omega : ir.val ≤ p.length) (hprev.trans hcase.symm)
          have hne : i4.val - 1 ≠ ir.val := by simp [ir]
          exact hne hinj
  have hirMem : ir ∈ insideIndices := by
    simp only [insideIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨C.y a1, hZsubXd (hbaseZ a1), hret⟩
  have hirle := Finset.le_max' insideIndices ir hirMem
  have hi4qv : i4.val < qv.val := by
    change ir.val ≤ qv.val at hirle
    simp [ir] at hirle
    omega
  have hfn0 : f ≠ C.blockEdge (D.gammaIndex d) 0 := by
    intro heq
    have hverts : p.getVert qf.val = p.getVert i0.val := by
      rw [hqff, heq]
      simpa [i0] using hj0.symm
    have hind := hpath.getVert_injOn (by omega : qf.val ≤ p.length)
      (by omega : i0.val ≤ p.length) hverts
    simp [qf, i0, i4] at hind hi4qv
    omega
  have hfn1 : f ≠ C.blockEdge (D.gammaIndex d) 1 := by
    intro heq
    have hverts : p.getVert qf.val = p.getVert i4.val := by
      rw [hqff, heq]
      simpa [i4] using hj4.symm
    have hind := hpath.getVert_injOn (by omega : qf.val ≤ p.length)
      (by omega : i4.val ≤ p.length) hverts
    simp [qf] at hind
    omega
  have hf0 : f = D.f0 d := hfThree.resolve_right (by
    rintro (heq | heq)
    · exact hfn0 heq
    · exact hfn1 heq)
  have hwv0 : w = D.v0 d := by
    have hwinc : Incident G w (D.f0 d) := hf0 ▸ hwf
    have hwcase : w = D.v0 d ∨ w = D.u0 d := by
      simpa [Incident, D.f0_ends] using hwinc
    exact hwcase.resolve_right (fun heq => hu0out (heq ▸ hwXd))
  refine ⟨h, i0, i1, i2, i3, i4, qv, qf, hhColor, hhends,
    by simpa [i0, i1] using hj01, by simpa [i1, i2] using hj12,
    by simpa [i2, i3] using hj23, by simpa [i3, i4] using hj34,
    ?_, hi4qv, hqfval, ?_, ?_, ?_, hu1NotExit, hu2NotExit⟩
  · left
    exact ⟨by simpa [i0] using hj0, by simpa [i1] using hj1,
      by simpa [i2] using hj2, by simpa [i3] using hj3,
      by simpa [i4] using hj4⟩
  · simpa [hwv0] using hqvw
  · simpa [hf0] using hqff
  · simpa [Xd] using hafter

private theorem helper_branch_1227.{u_1, u_2} :
    helperBranch1227Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p gamma phiD X Xd Z H hZsubXd h hhends hhColor
      a0 ha0ends hpath j0 hj0 hj0le j1 hj1 j2 hj2 j3 hj3 j4 hj4 hj4le hbaseZ hu1NotExit
      hu2NotExit insideIndices insideNonempty qv w hwXd hqvw hafter hqvlt qf hqfval f hqff hwf
      hqflt hfThree hu0out horient
  rcases horient with ⟨hj43, hj32, hj21, hj10⟩
  let i0 : Fin (p.length + 1) := ⟨j4, by omega⟩
  let i1 : Fin (p.length + 1) := ⟨j3, by omega⟩
  let i2 : Fin (p.length + 1) := ⟨j2, by omega⟩
  let i3 : Fin (p.length + 1) := ⟨j1, by omega⟩
  let i4 : Fin (p.length + 1) := ⟨j0, by omega⟩
  have hi4lt : i4.val < p.length := by
    by_contra hn
    have heq : i4.val = p.length := by omega
    have hh := hj0
    rw [← show i4.val = j0 by rfl, heq, p.getVert_length] at hh
    simp at hh
  let ir : Fin (p.length + 1) := ⟨i4.val + 1, by omega⟩
  have hretAdj := p.adj_getVert_succ (i := i4.val) hi4lt
  have hret : p.getVert ir.val = Sum.inl (C.y a0) := by
    have hprev : p.getVert (i4.val - 1) =
        Sum.inl (C.blockVertex (D.gammaIndex d) 0) := by
      have heq : i4.val - 1 = j1 := by simp [i4]; omega
      simpa [heq] using hj1
    cases hcase : p.getVert ir.val with
    | inr e =>
        rw [show p.getVert i4.val = Sum.inr (C.blockEdge (D.gammaIndex d) 0) by
          simpa [i4] using hj0, hcase] at hretAdj
        simp [TwoColorIncidenceGraph] at hretAdj
    | inl y =>
        have hinc : Incident G y (C.blockEdge (D.gammaIndex d) 0) := by
          rw [show p.getVert i4.val = Sum.inr (C.blockEdge (D.gammaIndex d) 0) by
            simpa [i4] using hj0, hcase] at hretAdj
          have hadjData : Incident G y (C.blockEdge (D.gammaIndex d) 0) ∧
              (phiD (C.blockEdge (D.gammaIndex d) 0) = some gamma ∨
                phiD (C.blockEdge (D.gammaIndex d) 0) = some beta) := by
            simpa [H, ir, TwoColorIncidenceGraph] using hretAdj
          exact hadjData.1
        have hy : y = C.y a0 ∨ y = C.blockVertex (D.gammaIndex d) 0 := by
          simpa [Incident, ha0ends] using hinc
        rcases hy with rfl | rfl
        · simp
        · exfalso
          have hinj := hpath.getVert_injOn (by omega : i4.val - 1 ≤ p.length)
            (by omega : ir.val ≤ p.length) (hprev.trans hcase.symm)
          have hne : i4.val - 1 ≠ ir.val := by simp [ir]
          exact hne hinj
  have hirMem : ir ∈ insideIndices := by
    simp only [insideIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨C.y a0, hZsubXd (hbaseZ a0), hret⟩
  have hirle := Finset.le_max' insideIndices ir hirMem
  have hi4qv : i4.val < qv.val := by
    change ir.val ≤ qv.val at hirle
    simp [ir] at hirle
    omega
  have hfn0 : f ≠ C.blockEdge (D.gammaIndex d) 0 := by
    intro heq
    have hverts : p.getVert qf.val = p.getVert i4.val := by
      rw [hqff, heq]
      simpa [i4] using hj0.symm
    have hind := hpath.getVert_injOn (by omega : qf.val ≤ p.length)
      (by omega : i4.val ≤ p.length) hverts
    simp [qf] at hind
    omega
  have hfn1 : f ≠ C.blockEdge (D.gammaIndex d) 1 := by
    intro heq
    have hverts : p.getVert qf.val = p.getVert i0.val := by
      rw [hqff, heq]
      simpa [i0] using hj4.symm
    have hind := hpath.getVert_injOn (by omega : qf.val ≤ p.length)
      (by omega : i0.val ≤ p.length) hverts
    simp [qf, i0, i4] at hind hi4qv
    omega
  have hf0 : f = D.f0 d := hfThree.resolve_right (by
    rintro (heq | heq)
    · exact hfn0 heq
    · exact hfn1 heq)
  have hwv0 : w = D.v0 d := by
    have hwinc : Incident G w (D.f0 d) := hf0 ▸ hwf
    have hwcase : w = D.v0 d ∨ w = D.u0 d := by
      simpa [Incident, D.f0_ends] using hwinc
    exact hwcase.resolve_right (fun heq => hu0out (heq ▸ hwXd))
  refine ⟨h, i0, i1, i2, i3, i4, qv, qf, hhColor, hhends,
    by simpa [i0, i1] using hj43, by simpa [i1, i2] using hj32,
    by simpa [i2, i3] using hj21, by simpa [i3, i4] using hj10,
    ?_, hi4qv, hqfval, ?_, ?_, ?_, hu1NotExit, hu2NotExit⟩
  · right
    exact ⟨by simpa [i0] using hj4, by simpa [i1] using hj3,
      by simpa [i2] using hj2, by simpa [i3] using hj1,
      by simpa [i4] using hj0⟩
  · simpa [hwv0] using hqvw
  · simpa [hf0] using hqff
  · simpa [Xd] using hafter

private theorem helper_continuation_981.{u_1, u_2} :
    helperContinuation981Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p gamma phiD X Xd Z H hZsubXd hexact h hhends
      hhColor a0 ha0ends a1 ha1ends hpath j0 hj0 hj0le j1 hj1 j2 hj2 j3 hj3 j4 hj4 hj4le
      horientation hbaseZ hu1NotExit hu2NotExit insideIndices insideNonempty qv w hwXd hqvw
      hafter hqvlt qf hqfval f hqff hwf hqflt x hxXd hfends hfGamma hwZ
  have hfThree : f = D.f0 d ∨ f = C.blockEdge (D.gammaIndex d) 0 ∨
      f = C.blockEdge (D.gammaIndex d) 1 := by
    apply (hexact f).mp
    exact ⟨by simpa [phiD, gamma] using hfGamma, w, by simpa [Z, X] using hwZ,
      x, by simpa [Xd] using hxXd, hfends⟩
  have hf0Data := (hexact (D.f0 d)).2 (Or.inl rfl)
  obtain ⟨_, av, havZ, bv, hbvo, habends⟩ := hf0Data
  have havX : av ∈ X := by
    exact (Finset.mem_sdiff.mp havZ).1
  have havInc : Incident G av (D.f0 d) := by
    change av ∈ G.ends (D.f0 d)
    rw [habends]
    simp
  have hav0 : av = D.v0 d := by
    have hc : av = D.v0 d ∨ av = D.u0 d := by
      simpa [Incident, D.f0_ends] using havInc
    exact hc.resolve_right (fun heq => D.u0_outside d (heq ▸ by simpa [X] using havX))
  have hbvInc : Incident G bv (D.f0 d) := by
    change bv ∈ G.ends (D.f0 d)
    rw [habends]
    simp
  have hv0Xd : D.v0 d ∈ Xd := hZsubXd (by simpa [hav0, Z, X] using havZ)
  have hbvu0 : bv = D.u0 d := by
    have hc : bv = D.v0 d ∨ bv = D.u0 d := by
      simpa [Incident, D.f0_ends] using hbvInc
    exact hc.resolve_left (fun heq => hbvo (by simpa [heq, Xd] using hv0Xd))
  have hu0out : D.u0 d ∉ Xd := by simpa [hbvu0, Xd] using hbvo
  rcases horientation with horient | horient
  · exact @helper_branch_1139 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@R) (@beta) (@v) (@z) (@p) (@hZsubXd) (@h)
      (@hhends) (@hhColor) (@a1) (@ha1ends) (@hpath) (@j0) (@hj0) (@hj0le) (@j1) (@hj1) (@j2)
      (@hj2) (@j3) (@hj3) (@j4) (@hj4) (@hj4le) (@hbaseZ) (@hu1NotExit) (@hu2NotExit)
      (@insideNonempty) (@w) (@hwXd) (@hqvw) (@hafter) (@hqvlt) (@hqfval) (@f) (@hqff) (@hwf)
      (@hqflt) (@hfThree) (by assumption) (@hu0out) (@horient)
  · exact @helper_branch_1227 (@V) (@E) inferInstance inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@R) (@beta) (@v) (@z) (@p) (@hZsubXd) (@h)
      (@hhends) (@hhColor) (@a0) (@ha0ends) (@hpath) (@j0) (@hj0) (@hj0le) (@j1) (@hj1) (@j2)
      (@hj2) (@j3) (@hj3) (@j4) (@hj4) (@hj4le) (@hbaseZ) (@hu1NotExit) (@hu2NotExit)
      (@insideNonempty) (@w) (@hwXd) (@hqvw) (@hafter) (@hqvlt) (@hqfval) (@f) (@hqff) (@hwf)
      (@hqflt) (@hfThree) (@hu0out) (@horient)
private theorem helper_continuation_790.{u_1, u_2} :
    helperContinuation790Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p hbetaD hp gamma phiD X Xd Z H hZsubXd hvXd
      hglobalD helemD hclosedD hgammaDef hexact _ h hhends hhColor a0 ha0ends a1 ha1ends hpath
      hlength j0 hj0 hj0le j1 hj1 j2 hj2 j3 hj3 j4 hj4 hj4le horientation hbaseZ husedWitnessZ
  have hu1Xd : R.u1 ∈ Xd := by
    change R.u1 ∈ TreeSequenceVertexSet R.replacementTree
    rw [R.replacement_vertices]
    simp
  have hu2Xd : R.u2 ∈ Xd := by
    change R.u2 ∈ TreeSequenceVertexSet R.replacementTree
    rw [R.replacement_vertices]
    simp
  have pairHasFree : ∀ u : V, u ∈ Xd → u ∉ Z →
      ∃ c, c ∈ MissingColors G phiD u ∧
        c ∈ TreeFreeColors phiD R.replacementTree := by
    intro u huXd huZ
    have hcount := ScheideGlobalMaximumMissingCounts G k e0 phiD
      R.replacementTree hglobalD u huXd
    have hnonempty : (MissingColors G phiD u).Nonempty := by
      apply Finset.card_pos.mp
      by_cases hi : Incident G u e0
      · have hc := (hcount.1 hi).2
        omega
      · have hc := (hcount.2 hi).2
        omega
    obtain ⟨c, hcMissing⟩ := hnonempty
    have hcUnused : c ∉ TreeUsedColors phiD R.replacementTree := by
      intro hcUsed
      obtain ⟨y, hyZ, hyMissing⟩ := husedWitnessZ c hcUsed
      have hyu : y ≠ u := by
        intro heq
        exact huZ (heq ▸ hyZ)
      exact (Finset.disjoint_left.mp (helemD (hZsubXd hyZ) huXd hyu))
        hyMissing hcMissing
    refine ⟨c, hcMissing, ?_⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hcUnused⟩
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨u, huXd, hcMissing⟩
  have hu1NotZ : R.u1 ∉ Z := by
    intro hu
    have hu' : R.u1 ∈ X \ {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1} := by simpa only [Z] using hu
    exact R.u1_outside (by simpa [X] using (Finset.mem_sdiff.mp hu').1)
  have hu2NotZ : R.u2 ∉ Z := by
    intro hu
    have hu' : R.u2 ∈ X \ {C.blockVertex (D.gammaIndex d) 0,
        C.blockVertex (D.gammaIndex d) 1} := by simpa only [Z] using hu
    exact R.u2_outside (by simpa [X] using (Finset.mem_sdiff.mp hu').1)
  obtain ⟨c1, hc1Missing, hc1Free⟩ := pairHasFree R.u1 hu1Xd hu1NotZ
  obtain ⟨c2, hc2Missing, hc2Free⟩ := pairHasFree R.u2 hu2Xd hu2NotZ
  have hu1NotExit : R.u1 ∉ ScheideExitVertices R.replacementTree phiD := by
    intro hu
    have hd := ScheideExitNoFree G k e0 phiD R.replacementTree hglobalD R.u1 hu
    exact (Finset.disjoint_left.mp hd) hc1Missing hc1Free
  have hu2NotExit : R.u2 ∉ ScheideExitVertices R.replacementTree phiD := by
    intro hu
    have hd := ScheideExitNoFree G k e0 phiD R.replacementTree hglobalD R.u2 hu
    exact (Finset.disjoint_left.mp hd) hc2Missing hc2Free
  let insideIndices : Finset (Fin (p.length + 1)) :=
    Finset.univ.filter fun q => ∃ w ∈ Xd, p.getVert q.val = Sum.inl w
  have insideNonempty : insideIndices.Nonempty := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp only [insideIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hvXd, p.getVert_zero⟩
  let qv : Fin (p.length + 1) := insideIndices.max' insideNonempty
  have hqvMem : qv ∈ insideIndices := Finset.max'_mem insideIndices insideNonempty
  obtain ⟨w, hwXd, hqvw⟩ := by
    simpa only [insideIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      using hqvMem
  have hafter : ∀ q : Fin (p.length + 1), qv.val < q.val →
      ∀ a : V, p.getVert q.val = Sum.inl a → a ∉ Xd := by
    intro q hq a hqa haXd
    have hqmem : q ∈ insideIndices := by
      simp only [insideIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, haXd, hqa⟩
    exact (not_le_of_gt hq) (Finset.le_max' insideIndices q hqmem)
  have hqvlt : qv.val < p.length := by
    by_contra hn
    have heq : qv.val = p.length := by omega
    have hwz : w = z := by
      apply Sum.inl.inj
      rw [← hqvw, heq, p.getVert_length]
    exact hp.2.2.1 (hwz ▸ hwXd)
  let qf : Fin (p.length + 1) := ⟨qv.val + 1, by omega⟩
  have hqfval : qf.val = qv.val + 1 := rfl
  have hqadj := p.adj_getVert_succ (i := qv.val) hqvlt
  rw [hqvw] at hqadj
  have hqadj' : H.Adj (Sum.inl w) (p.getVert qf.val) := by
    simpa [H, qf] using hqadj
  obtain ⟨f, hqff, hwf, hfcolor⟩ : ∃ f : E,
      p.getVert qf.val = Sum.inr f ∧ Incident G w f ∧
        (phiD f = some gamma ∨ phiD f = some beta) := by
    cases hnext : p.getVert qf.val with
    | inl a =>
        exfalso
        rw [hnext] at hqadj'
        simp [H, TwoColorIncidenceGraph] at hqadj'
    | inr f =>
        refine ⟨f, rfl, ?_⟩
        rw [hnext] at hqadj'
        simpa [H, TwoColorIncidenceGraph] using hqadj'
  have hqflt : qf.val < p.length := by
    by_contra hn
    have heq : qf.val = p.length := by omega
    have hh := hqff
    rw [heq, p.getVert_length] at hh
    simp at hh
  let qx : Fin (p.length + 1) := ⟨qf.val + 1, by omega⟩
  have hfxadj := p.adj_getVert_succ (i := qf.val) hqflt
  rw [hqff] at hfxadj
  have hfxadj' : H.Adj (Sum.inr f) (p.getVert qx.val) := by
    simpa [H, qx] using hfxadj
  obtain ⟨x, hqxx, hxf⟩ : ∃ x : V,
      p.getVert qx.val = Sum.inl x ∧ Incident G x f := by
    cases hnext : p.getVert qx.val with
    | inl a =>
        refine ⟨a, rfl, ?_⟩
        rw [hnext] at hfxadj'
        have hadjData : Incident G a f ∧
            (phiD f = some gamma ∨ phiD f = some beta) := by
          simpa [H, TwoColorIncidenceGraph] using hfxadj'
        exact hadjData.1
    | inr e =>
        exfalso
        rw [hnext] at hfxadj'
        simp [H, TwoColorIncidenceGraph] at hfxadj'
  have hxXd : x ∉ Xd := hafter qx (by dsimp [qx, qf]; omega) x hqxx
  have hwne : w ≠ x := fun heq => hxXd (heq ▸ hwXd)
  have hfends : G.ends f = s(w, x) :=
    (Sym2.mem_and_mem_iff hwne).mp ⟨hwf, hxf⟩
  have hfBoundary : f ∈ BoundaryEdges G Xd := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hwXd, x, hxXd, hfends⟩
  have hfGamma : phiD f = some gamma := by
    rcases hfcolor with hfg | hfb
    · exact hfg
    · exact False.elim ((hclosedD hfBoundary hvXd hfb) hbetaD)
  have hwExit : ScheideExitVertex R.replacementTree phiD w := by
    exact ⟨v, beta, gamma, hvXd, hbetaD,
      by simpa [gamma, phiD, Xd] using hgammaDef, z, p,
      by simpa [gamma, phiD] using hp, qv, hqvw, hwXd, hafter⟩
  have hwExits : w ∈ ScheideExitVertices R.replacementTree phiD := by
    simp only [ScheideExitVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hwExit
  have hwZ : w ∈ Z := by
    have hu := hwXd
    change w ∈ TreeSequenceVertexSet R.replacementTree at hu
    rw [R.replacement_vertices] at hu
    rcases Finset.mem_union.mp hu with hz | hu
    · simpa [Z, X] using hz
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact False.elim (hu1NotExit hwExits)
      · exact False.elim (hu2NotExit hwExits)
  exact @helper_continuation_981 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@R) (@beta) (@v) (@z) (@p)
      (@hZsubXd) (@hexact) (@h) (@hhends) (@hhColor) (@a0) (@ha0ends) (@a1) (@ha1ends) (@hpath)
      (@j0) (@hj0) (@hj0le) (@j1) (@hj1) (@j2) (@hj2) (@j3) (@hj3) (@j4) (@hj4) (@hj4le)
      (@horientation) (@hbaseZ) (@hu1NotExit) (@hu2NotExit) (@insideNonempty) (@w) (@hwXd)
      (@hqvw) (@hafter) (@hqvlt) (@hqfval) (@f) (@hqff) (@hwf) (@hqflt) (@x) (@hxXd) (@hfends)
      (@hfGamma) (@hwZ)
private theorem helper_continuation_462.{u_1, u_2} :
    helperContinuation462Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p hv hbetaD hp gamma phiD X Xd Z H hZsubXd hvXd
      hglobalD helemD hclosedD hgammaDef hexact _ h hhends heffect hhColor a0 ha0ends a1 ha1ends
      hpath hlength j0 hj0 hj0le j1 hj1 j2 hj2 j3 hj3 j4 hj4 hj4le horientation htreeY hpTwo
      hlengthT hlengthD hrLt hbaseZ
  have hdeltaUnusedOriginal : d.1 ∉ TreeUsedColors phi T := by
    have hu := (ScheideGlobalMaximumUnused G k e0 phi T C.globally_maximum).1
    exact fun hd => (Finset.disjoint_left.mp hu) d.2 hd
  have originalEdgeFixed : ∀ (q : ℕ) (hq : q < T.length), 1 ≤ q →
      phiD (T.edge ⟨q, hq⟩) = phi (T.edge ⟨q, hq⟩) := by
    intro q hq hqpos
    apply heffect.2.2.2.2.1
    · obtain ⟨i, hi⟩ := T.attaches ⟨q, hq⟩
      refine ⟨T.vertex ⟨q + 1, by omega⟩, ?_, ?_⟩
      · simp [TreeSequenceVertexSet]
      · change T.vertex ⟨q + 1, by omega⟩ ∈ G.ends (T.edge ⟨q, hq⟩)
        rw [hi]
        simp
    · intro heq
      apply hdeltaUnusedOriginal
      simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨q, hq⟩, hqpos, by simpa [heq] using D.f0_color d⟩
  have hf1D : phiD R.f1 = some d.1 := by
    have hf := ScheideReplacementPairFixed G k e0 phi T C D d R R.f1
      (Or.inl (by
        change R.u1 ∈ G.ends R.f1
        rw [R.f1_ends]
        simp []))
    simpa [phiD, gamma] using hf.trans R.f1_color
  have hf2D : phiD R.f2 = some d.1 := by
    have hf := ScheideReplacementPairFixed G k e0 phi T C D d R R.f2
      (Or.inr (by
        change R.u2 ∈ G.ends R.f2
        rw [R.f2_ends]
        simp []))
    simpa [phiD, gamma] using hf.trans R.f2_color
  have husedWitnessZ : ∀ c : Fin k,
      c ∈ TreeUsedColors phiD R.replacementTree →
        ∃ y ∈ Z, c ∈ MissingColors G phiD y := by
    intro c hc
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc with ⟨j, hj, hc⟩
    by_cases hjBase : j.val < C.p - 1
    · obtain ⟨i, c0, hcolor0, hmiss0⟩ := hglobalD.2.1 j hj
      have hc0 : c0 = c := Option.some.inj (hcolor0.symm.trans hc)
      let q : Fin C.p := ⟨i.val, by omega⟩
      have hvrep := R.retained_vertices_before i.val (by omega)
        (by rw [C.length_eq]; omega)
      have hidx : Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ j.isLt)) =
          (⟨i.val, by omega⟩ : Fin (R.replacementTree.length + 1)) := Fin.ext rfl
      have holdidx : (⟨i.val, by omega⟩ : Fin (T.length + 1)) =
          (⟨q.val, by rw [C.length_eq]; omega⟩ : Fin (T.length + 1)) := Fin.ext rfl
      refine ⟨C.y q, hbaseZ q, ?_⟩
      rw [hidx, hvrep, holdidx, C.base_vertex_position q] at hmiss0
      simpa [hc0] using hmiss0
    · by_cases hbefore : j.val < C.p - 1 + 2 * (D.gammaIndex d).val
      · let n := j.val - (C.p - 1)
        let q : Fin C.s := ⟨n / 2, by omega⟩
        let t : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by omega)⟩
        have hjpos : j.val = C.p - 1 + 2 * q.val + t.val := by
          dsimp [q, t, n]
          have hdiv := Nat.mod_add_div (j.val - (C.p - 1)) 2
          omega
        have hqr : q ≠ D.gammaIndex d := by
          intro hqeq
          have hv := congrArg Fin.val hqeq
          dsimp [q, n] at hv
          omega
        have hedgeOld : T.edge ⟨j.val, by omega⟩ = C.blockEdge q t := by
          calc
            T.edge ⟨j.val, by omega⟩ =
                T.edge ⟨C.p - 1 + 2 * q.val + t.val, by omega⟩ := by
              congr 1
              exact Fin.ext hjpos
            _ = C.blockEdge q t := C.block_edge_position q t
        have hedgeRep : R.replacementTree.edge j = T.edge ⟨j.val, by omega⟩ :=
          R.retained_edges_before j.val hbefore (by omega)
        have hcolorD : phiD (R.replacementTree.edge j) = some (C.gamma q) := by
          rw [hedgeRep, originalEdgeFixed j.val (by omega) (by omega), hedgeOld]
          exact C.block_color q t
        have hcol : C.gamma q = c := Option.some.inj (hcolorD.symm.trans hc)
        obtain ⟨a, haMissing⟩ := C.block_color_missing_on_base q
        have hneGamma : C.gamma q ≠ gamma := by
          intro heq
          apply hqr
          apply C.gamma_injective
          simpa [gamma] using heq
        have haMissingD : C.gamma q ∈ MissingColors G phiD (C.y a) := by
          by_cases ha0 : C.y a = D.v0 d
          · rw [ha0, heffect.2.2.2.1]
            exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hneGamma, by
              simpa [ha0] using haMissing⟩)
          · rw [heffect.2.2.2.2.2.1 (C.y a) (htreeY a) ha0]
            exact haMissing
        exact ⟨C.y a, hbaseZ a, by simpa [hcol] using haMissingD⟩
      · by_cases hafter : j.val + 2 < T.length
        · let n := j.val + 2 - (C.p - 1)
          let q : Fin C.s := ⟨n / 2, by omega⟩
          let t : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by omega)⟩
          have hjpos : j.val + 2 = C.p - 1 + 2 * q.val + t.val := by
            dsimp [q, t, n]
            have hdiv := Nat.mod_add_div (j.val + 2 - (C.p - 1)) 2
            omega
          have hqr : q ≠ D.gammaIndex d := by
            intro hqeq
            have hv := congrArg Fin.val hqeq
            dsimp [q, n] at hv
            omega
          have hedgeOld : T.edge ⟨j.val + 2, hafter⟩ = C.blockEdge q t := by
            calc
              T.edge ⟨j.val + 2, hafter⟩ =
                  T.edge ⟨C.p - 1 + 2 * q.val + t.val, by omega⟩ := by
                congr 1
                exact Fin.ext hjpos
              _ = C.blockEdge q t := C.block_edge_position q t
          have hedgeRep : R.replacementTree.edge j = T.edge ⟨j.val + 2, hafter⟩ :=
            R.retained_edges_after j.val (by omega) hafter
          have hcolorD : phiD (R.replacementTree.edge j) = some (C.gamma q) := by
            rw [hedgeRep, originalEdgeFixed (j.val + 2) hafter (by omega), hedgeOld]
            exact C.block_color q t
          have hcol : C.gamma q = c := Option.some.inj (hcolorD.symm.trans hc)
          obtain ⟨a, haMissing⟩ := C.block_color_missing_on_base q
          have hneGamma : C.gamma q ≠ gamma := by
            intro heq
            apply hqr
            apply C.gamma_injective
            simpa [gamma] using heq
          have haMissingD : C.gamma q ∈ MissingColors G phiD (C.y a) := by
            by_cases ha0 : C.y a = D.v0 d
            · rw [ha0, heffect.2.2.2.1]
              exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hneGamma, by
                simpa [ha0] using haMissing⟩)
            · rw [heffect.2.2.2.2.2.1 (C.y a) (htreeY a) ha0]
              exact haMissing
          exact ⟨C.y a, hbaseZ a, by simpa [hcol] using haMissingD⟩
        · have hjlast : j.val = T.length - 2 ∨ j.val = T.length - 1 := by
            have hl := R.replacement_length
            omega
          have hdc : d.1 = c := by
            rcases hjlast with hjlast | hjlast
            · have hedge : R.replacementTree.edge j = R.f1 := by
                calc
                  R.replacementTree.edge j =
                      R.replacementTree.edge ⟨T.length - 2, by
                        rw [R.replacement_length]; omega⟩ := by
                    congr 1
                    exact Fin.ext hjlast
                  _ = R.f1 := R.replacement_last_edges.1
              exact Option.some.inj ((hedge ▸ hf1D).symm.trans hc)
            · have hedge : R.replacementTree.edge j = R.f2 := by
                calc
                  R.replacementTree.edge j =
                      R.replacementTree.edge ⟨T.length - 1, by
                        rw [R.replacement_length]; omega⟩ := by
                    congr 1
                    exact Fin.ext hjlast
                  _ = R.f2 := R.replacement_last_edges.2
              exact Option.some.inj ((hedge ▸ hf2D).symm.trans hc)
          obtain ⟨a, ha, hv0a⟩ := Finset.mem_image.mp
            (ScheideStructuralExitsInBase G k e0 phi T C (D.v0_is_exit d))
          have hv0Z : D.v0 d ∈ Z := hv0a ▸ hbaseZ a
          refine ⟨D.v0 d, hv0Z, ?_⟩
          rw [← hdc, heffect.2.2.2.1]
          simp
  exact @helper_continuation_790 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@R) (@beta) (@v) (@z) (@p)
      (@hbetaD) (@hp) (@hZsubXd) (@hvXd) (@hglobalD) (@helemD) (@hclosedD) (@hgammaDef) (@hexact)
      (by assumption) (@h) (@hhends) (@hhColor) (@a0) (@ha0ends) (@a1) (@ha1ends) (@hpath)
      (@hlength) (@j0) (@hj0) (@hj0le) (@j1) (@hj1) (@j2) (@hj2) (@j3) (@hj3) (@j4) (@hj4)
      (@hj4le) (@horientation) (@hbaseZ) (@husedWitnessZ)
private theorem helper_continuation_264.{u_1, u_2} :
    helperContinuation264Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D d R beta v z p hv hbetaD hbetaGamma hp gamma phiD X Xd Z H
      hZsubXd hvXd hproper hglobalD helemD hclosedD hgammaDef hb0Color hb1Color hexact _
      hb0Support hb1Support h hhends heffect hhColor a0 ha0ends a1 ha1ends hb0u0 hu0h hhu1 hu1b1
      hu0Support hhSupport hu1Support hpath hlength startNeighborUnique
  have forwardAdjacent : ∀ i j : ℕ, i ≤ p.length → j ≤ p.length →
      i < j → H.Adj (p.getVert i) (p.getVert j) → i + 1 = j := by
    intro i j hi hj hijlt hij
    by_contra hnot
    have hgap : i + 1 < j := by omega
    by_cases hi0 : i = 0
    · subst i
      have heq := startNeighborUnique (p.getVert j) (by simpa using hij)
      have hinj := hpath.getVert_injOn (by omega : 1 ≤ p.length) hj heq.symm
      omega
    · have hprev := p.adj_getVert_succ (i := i - 1) (by omega)
      have hnext := p.adj_getVert_succ (i := i) (by omega)
      have hprev' : H.Adj (p.getVert i) (p.getVert (i - 1)) := by
        have hieq : i - 1 + 1 = i := by omega
        simpa [H, hieq] using hprev.symm
      have hnext' : H.Adj (p.getVert i) (p.getVert (i + 1)) := by
        simpa [H] using hnext
      have hprevNext : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
        intro heq
        have hindex := hpath.getVert_injOn
          (by omega : i - 1 ≤ p.length) (by omega : i + 1 ≤ p.length) heq
        omega
      have hprevJ : p.getVert (i - 1) ≠ p.getVert j := by
        intro heq
        have hindex := hpath.getVert_injOn (by omega : i - 1 ≤ p.length) hj heq
        omega
      have hnextJ : p.getVert (i + 1) ≠ p.getVert j := by
        intro heq
        have hindex := hpath.getVert_injOn (by omega : i + 1 ≤ p.length) hj heq
        omega
      let S : Finset (Sum V E) :=
        {p.getVert (i - 1), p.getVert (i + 1), p.getVert j}
      have hScard : S.card = 3 := by
        simp [S, hprevNext, hprevJ, hnextJ]
      have hSsub : ∀ x ∈ S, x ∈ H.neighborSet (p.getVert i) := by
        intro x hx
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · simpa only [SimpleGraph.mem_neighborSet] using hprev'
        · simpa only [SimpleGraph.mem_neighborSet] using hnext'
        · simpa only [SimpleGraph.mem_neighborSet] using hij
      let inclusion : {x // x ∈ S} → H.neighborSet (p.getVert i) :=
        fun x => ⟨x.1, hSsub x.1 x.2⟩
      have hinclusion : Function.Injective inclusion := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun q : H.neighborSet (p.getVert i) => q.1) hxy
      let : Fintype (H.neighborSet (p.getVert i)) := Fintype.ofFinite _
      have hcard := Fintype.card_le_of_injective inclusion hinclusion
      rw [Fintype.card_coe, hScard, SimpleGraph.card_neighborSet_eq_degree] at hcard
      have hdegree := TwoColorIncidenceDegreeAtMostTwo G phiD gamma beta hproper
        (p.getVert i)
      have hdegree' : H.degree (p.getVert i) ≤ 2 := by
        simpa only [H] using hdegree
      omega
  have adjacentIndices : ∀ i j : ℕ, i ≤ p.length → j ≤ p.length →
      H.Adj (p.getVert i) (p.getVert j) →
        i + 1 = j ∨ j + 1 = i := by
    intro i j hi hj hij
    have hijne : i ≠ j := by
      intro heq
      subst j
      exact H.irrefl hij
    rcases lt_or_gt_of_ne hijne with hijlt | hjilt
    · exact Or.inl (forwardAdjacent i j hi hj hijlt hij)
    · exact Or.inr (forwardAdjacent j i hj hi hjilt hij.symm)
  obtain ⟨j0, hj0, hj0le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hb0Support
  obtain ⟨j1, hj1, hj1le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hu0Support
  obtain ⟨j2, hj2, hj2le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hhSupport
  obtain ⟨j3, hj3, hj3le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hu1Support
  obtain ⟨j4, hj4, hj4le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hb1Support
  have ha01 := adjacentIndices j0 j1 hj0le hj1le
    (by simpa [H, hj0, hj1] using hb0u0)
  have ha12 := adjacentIndices j1 j2 hj1le hj2le
    (by simpa [H, hj1, hj2] using hu0h)
  have ha23 := adjacentIndices j2 j3 hj2le hj3le
    (by simpa [H, hj2, hj3] using hhu1)
  have ha34 := adjacentIndices j3 j4 hj3le hj4le
    (by simpa [H, hj3, hj4] using hu1b1)
  have hb0ColorD : phiD (C.blockEdge (D.gammaIndex d) 0) = some gamma := by
    simpa [gamma, phiD] using hb0Color
  have hb1ColorD : phiD (C.blockEdge (D.gammaIndex d) 1) = some gamma := by
    simpa [gamma, phiD] using hb1Color
  have hb0h : C.blockEdge (D.gammaIndex d) 0 ≠ h := by
    intro heq
    have hc : gamma = beta := Option.some.inj
      (hb0ColorD.symm.trans (heq ▸ hhColor))
    exact hbetaGamma hc.symm
  have hhb1 : h ≠ C.blockEdge (D.gammaIndex d) 1 := by
    intro heq
    have hc : beta = gamma := Option.some.inj
      (hhColor.symm.trans (heq ▸ hb1ColorD))
    exact hbetaGamma hc
  have hu0u1 : C.blockVertex (D.gammaIndex d) 0 ≠
      C.blockVertex (D.gammaIndex d) 1 := by
    intro heq
    apply G.loopless h (C.blockVertex (D.gammaIndex d) 0)
    simpa [heq] using hhends
  have hj02 : j0 ≠ j2 := by
    intro heq
    apply hb0h
    apply Sum.inr.inj
    exact hj0.symm.trans (by simpa [heq] using hj2)
  have hj13 : j1 ≠ j3 := by
    intro heq
    apply hu0u1
    apply Sum.inl.inj
    exact hj1.symm.trans (by simpa [heq] using hj3)
  have hj24 : j2 ≠ j4 := by
    intro heq
    apply hhb1
    apply Sum.inr.inj
    exact hj2.symm.trans (by simpa [heq] using hj4)
  have horientation :
      (j1 = j0 + 1 ∧ j2 = j1 + 1 ∧ j3 = j2 + 1 ∧ j4 = j3 + 1) ∨
      (j3 = j4 + 1 ∧ j2 = j3 + 1 ∧ j1 = j2 + 1 ∧ j0 = j1 + 1) := by
    rcases ha01 with h01 | h10 <;>
      rcases ha12 with h12 | h21 <;>
      rcases ha23 with h23 | h32 <;>
      rcases ha34 with h34 | h43 <;> omega
  have htreeY : ∀ q : Fin C.p, C.y q ∈ TreeSequenceVertexSet T := by
    intro q
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨q.val, by rw [C.length_eq]; omega⟩, C.base_vertex_position q⟩
  have hpTwo : 2 ≤ C.p := C.p_ge_two
  have hlengthT : T.length + 1 = C.p + 2 * C.s := C.length_eq
  have hlengthD : R.replacementTree.length = T.length := R.replacement_length
  have hrLt : (D.gammaIndex d).val < C.s := (D.gammaIndex d).isLt
  have hbaseZ : ∀ q : Fin C.p, C.y q ∈ Z := by
    intro q
    apply Finset.mem_sdiff.mpr
    refine ⟨by simpa [X] using htreeY q, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (he | he)
    · have hi := T.vertex_injective
        ((C.base_vertex_position q).trans
          (he.trans (C.block_vertex_position (D.gammaIndex d) 0).symm))
      have hv := congrArg Fin.val hi
      have hq := q.isLt
      change q.val = C.p + 2 * (D.gammaIndex d).val at hv
      omega
    · have hi := T.vertex_injective
        ((C.base_vertex_position q).trans
          (he.trans (C.block_vertex_position (D.gammaIndex d) 1).symm))
      have hv := congrArg Fin.val hi
      have hq := q.isLt
      change q.val = C.p + 2 * (D.gammaIndex d).val + 1 at hv
      omega
  exact @helper_continuation_462 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@R) (@beta) (@v) (@z) (@p) (@hv)
      (@hbetaD) (@hp) (@hZsubXd) (@hvXd) (@hglobalD) (@helemD) (@hclosedD) (@hgammaDef) (@hexact)
      (by assumption) (@h) (@hhends) (@heffect) (@hhColor) (@a0) (@ha0ends) (@a1) (@ha1ends)
      (@hpath) (@hlength) (@j0) (@hj0) (@hj0le) (@j1) (@hj1) (@j2) (@hj2) (@j3) (@hj3) (@j4)
      (@hj4) (@hj4le) (@horientation) (@htreeY) (@hpTwo) (@hlengthT) (@hlengthD) (@hrLt) (@hbaseZ)
private theorem helper_startNeighborUnique_2406.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))) (beta : Fin k) (v z : V) (p
        : (TwoColorIncidenceGraph G (TwoColorComponentSwap G phi (C.gamma (D.gammaIndex d)) (↑d :
        Fin k) (Sum.inl (D.v0 d))) (C.gamma (D.gammaIndex d)) beta).Walk (Sum.inl v) (Sum.inl z)),
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
        (D.v0 d));
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phiD gamma beta;
    ∀ (_ : IsProperEdgeColoring G phiD) (_ : (0 : ℕ) < p.length) (_ :
    ∀ (e : E), Incident G v e → phiD e ≠ some beta) (x : V ⊕ E), H.Adj (Sum.inl v) x → x =
        p.getVert (1 : ℕ) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d beta v z p gamma phiD H hproper hlength hbetaAbsent x hx
  have hfirst := p.adj_getVert_succ (i := 0) hlength
  rw [p.getVert_zero] at hfirst
  cases hxcase : x with
  | inl w =>
      rw [hxcase] at hx
      simp [H, TwoColorIncidenceGraph] at hx
  | inr e =>
      rw [hxcase] at hx
      rcases (by simpa [H, TwoColorIncidenceGraph] using hx) with ⟨hve, hec⟩
      have hegamma : phiD e = some gamma :=
        hec.resolve_right (hbetaAbsent e hve)
      cases hnext : p.getVert 1 with
      | inl w =>
          rw [hnext] at hfirst
          simp [TwoColorIncidenceGraph] at hfirst
      | inr f =>
          rw [hnext] at hfirst
          rcases (by simpa [H, TwoColorIncidenceGraph] using hfirst) with
            ⟨hvf, hfc⟩
          have hfgamma : phiD f = some gamma :=
            hfc.resolve_right (hbetaAbsent f hvf)
          have hef : e = f := by
            by_contra hne
            exact (hproper hne ⟨v, hve, hvf⟩ hegamma) hfgamma
          simp [hef]

theorem ScheideSymmetricReplacementPathOrder {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)})
    (R : ScheideReplacementData G k e0 phi T C D d) :
    let gamma := C.gamma (D.gammaIndex d)
    let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
    ∀ (beta : Fin k) (v z : V)
      (p : (TwoColorIncidenceGraph G phiD gamma beta).Walk
        (Sum.inl v) (Sum.inl z)),
      v ∈ TreeSequenceVertexSet T \
          {C.blockVertex (D.gammaIndex d) 0,
            C.blockVertex (D.gammaIndex d) 1} →
      beta ∈ MissingColors G phiD v → beta ∈ MissingColors G phi v →
      beta ∈ TreeFreeColors phiD R.replacementTree →
      beta ≠ d.1 → beta ≠ gamma →
      ScheideDefectiveChainPath R.replacementTree phiD gamma beta v z p →
      ∃ (h : E) (i0 i1 i2 i3 i4 qv qf : Fin (p.length + 1)),
        phiD h = some beta ∧
        G.ends h = s(C.blockVertex (D.gammaIndex d) 0,
          C.blockVertex (D.gammaIndex d) 1) ∧
        i1.val = i0.val + 1 ∧ i2.val = i1.val + 1 ∧
        i3.val = i2.val + 1 ∧ i4.val = i3.val + 1 ∧
        ((p.getVert i0.val = Sum.inr (C.blockEdge (D.gammaIndex d) 0) ∧
            p.getVert i1.val = Sum.inl (C.blockVertex (D.gammaIndex d) 0) ∧
            p.getVert i2.val = Sum.inr h ∧
            p.getVert i3.val = Sum.inl (C.blockVertex (D.gammaIndex d) 1) ∧
            p.getVert i4.val = Sum.inr (C.blockEdge (D.gammaIndex d) 1)) ∨
          (p.getVert i0.val = Sum.inr (C.blockEdge (D.gammaIndex d) 1) ∧
            p.getVert i1.val = Sum.inl (C.blockVertex (D.gammaIndex d) 1) ∧
            p.getVert i2.val = Sum.inr h ∧
            p.getVert i3.val = Sum.inl (C.blockVertex (D.gammaIndex d) 0) ∧
            p.getVert i4.val = Sum.inr (C.blockEdge (D.gammaIndex d) 0))) ∧
        i4.val < qv.val ∧ qf.val = qv.val + 1 ∧
        p.getVert qv.val = Sum.inl (D.v0 d) ∧
        p.getVert qf.val = Sum.inr (D.f0 d) ∧
        (∀ r : Fin (p.length + 1), qv.val < r.val →
          ∀ w : V, p.getVert r.val = Sum.inl w →
            w ∉ TreeSequenceVertexSet R.replacementTree) ∧
        R.u1 ∉ ScheideExitVertices R.replacementTree phiD ∧
        R.u2 ∉ ScheideExitVertices R.replacementTree phiD := by
  classical
  dsimp only
  intro beta v z p hv hbetaD hbetaOld hbetaFree hbetaDelta hbetaGamma hp
  let gamma := C.gamma (D.gammaIndex d)
  let phiD := TwoColorComponentSwap G phi gamma d.1 (Sum.inl (D.v0 d))
  let X := TreeSequenceVertexSet T
  let Xd := TreeSequenceVertexSet R.replacementTree
  let Z := X \ {C.blockVertex (D.gammaIndex d) 0,
    C.blockVertex (D.gammaIndex d) 1}
  let H := TwoColorIncidenceGraph G phiD gamma beta
  have hvZ : v ∈ Z := by simpa [Z, X] using hv
  have hZsubXd : Z ⊆ Xd := by
    intro a ha
    change a ∈ TreeSequenceVertexSet R.replacementTree
    rw [R.replacement_vertices]
    exact Finset.mem_union_left _ (by simpa [Z, X] using ha)
  have hvXd : v ∈ Xd := hZsubXd hvZ
  have hmaximum := ScheideReplacementMaximum G k e0 phi T C D d R
  dsimp [gamma, phiD] at hmaximum
  have hproper : IsProperEdgeColoring G phiD := hmaximum.1
  have hglobalD : GlobalMaximumTriple G k e0 phiD R.replacementTree :=
    hmaximum.2.2
  have horderD := ScheideGlobalMaximumOrder G k e0 phiD R.replacementTree hglobalD
  have helemD : ColoredVertexSetElementary G phiD Xd := horderD.2.2.2.1
  have hclosedD : ColoredVertexSetClosed G phiD Xd := horderD.2.2.2.2
  have hconfig :=
    ScheideSymmetricReplacementBoundaryConfiguration G k e0 phi T C D d R
  dsimp [gamma, phiD, Xd, Z, X] at hconfig
  rcases hconfig with
    ⟨hgammaDef, hf0Color, hb0Color, hb1Color, hf0ne0, hf0ne1,
      hb01ne, hexact⟩
  have hb0Data := (hexact (C.blockEdge (D.gammaIndex d) 0)).2
    (Or.inr (Or.inl rfl))
  obtain ⟨_, b0in, hb0inZ, b0out, hb0out, hb0ends⟩ := hb0Data
  have hb1Data := (hexact (C.blockEdge (D.gammaIndex d) 1)).2
    (Or.inr (Or.inr rfl))
  obtain ⟨_, b1in, hb1inZ, b1out, hb1out, hb1ends⟩ := hb1Data
  have hb0Boundary : C.blockEdge (D.gammaIndex d) 0 ∈ BoundaryEdges G Xd := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨b0in, hZsubXd (by simpa [Z, X] using hb0inZ), b0out,
      by simpa [Xd] using hb0out, hb0ends⟩
  have hb1Boundary : C.blockEdge (D.gammaIndex d) 1 ∈ BoundaryEdges G Xd := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨b1in, hZsubXd (by simpa [Z, X] using hb1inZ), b1out,
      by simpa [Xd] using hb1out, hb1ends⟩
  have hb0ColorBoundary : C.blockEdge (D.gammaIndex d) 0 ∈
      BoundaryColorEdges G phiD Xd gamma :=
    Finset.mem_filter.mpr ⟨hb0Boundary, by simpa [phiD, gamma] using hb0Color⟩
  have hb1ColorBoundary : C.blockEdge (D.gammaIndex d) 1 ∈
      BoundaryColorEdges G phiD Xd gamma :=
    Finset.mem_filter.mpr ⟨hb1Boundary, by simpa [phiD, gamma] using hb1Color⟩
  have hchain := ScheideDefectiveChainBoundaryEdges G k e0 phiD
    R.replacementTree hglobalD gamma beta
    (by simpa [gamma, phiD, Xd] using hgammaDef) hbetaFree v hvXd
    (by simpa [phiD] using hbetaD) z p (by simpa [gamma, phiD] using hp)
  have hb0Support : Sum.inr (C.blockEdge (D.gammaIndex d) 0) ∈ p.support :=
    (hchain (C.blockEdge (D.gammaIndex d) 0)).mp hb0ColorBoundary |>.2
  have hb1Support : Sum.inr (C.blockEdge (D.gammaIndex d) 1) ∈ p.support :=
    (hchain (C.blockEdge (D.gammaIndex d) 1)).mp hb1ColorBoundary |>.2
  obtain ⟨h, hhOldColor, hhends⟩ := ScheideStructuralInternalPair
    G k e0 phi T C (D.gammaIndex d) beta
      (by simpa [gamma] using hbetaGamma) ⟨v, hv, hbetaOld⟩
  have hhne0 : h ≠ D.f0 d := by
    intro heq
    have hc : beta = d.1 := Option.some.inj
      (hhOldColor.symm.trans (heq ▸ D.f0_color d))
    exact hbetaDelta hc
  have hblock0X : C.blockVertex (D.gammaIndex d) 0 ∈ X := by
    simp only [X, TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨⟨C.p + 2 * (D.gammaIndex d).val, by rw [C.length_eq]; omega⟩,
      C.block_vertex_position (D.gammaIndex d) 0⟩
  have hhIncident : ∃ a ∈ TreeSequenceVertexSet T, Incident G a h := by
    refine ⟨C.blockVertex (D.gammaIndex d) 0, by simpa [X] using hblock0X, ?_⟩
    change C.blockVertex (D.gammaIndex d) 0 ∈ G.ends h
    rw [hhends]
    simp
  have heffect := ScheideDefectiveSwitchEffect G k e0 phi T C D d
  dsimp [gamma, phiD] at heffect
  have hhColor : phiD h = some beta := by
    exact (heffect.2.2.2.2.1 h hhIncident hhne0).trans hhOldColor
  obtain ⟨a0, ha0ends⟩ := C.block_attaches_to_base (D.gammaIndex d) 0
  obtain ⟨a1, ha1ends⟩ := C.block_attaches_to_base (D.gammaIndex d) 1
  have hb0u0 : H.Adj (Sum.inr (C.blockEdge (D.gammaIndex d) 0))
      (Sum.inl (C.blockVertex (D.gammaIndex d) 0)) := by
    simp [H, TwoColorIncidenceGraph, Incident, ha0ends, hb0Color, phiD, gamma]
  have hu0h : H.Adj (Sum.inl (C.blockVertex (D.gammaIndex d) 0))
      (Sum.inr h) := by
    simp [H, TwoColorIncidenceGraph, Incident, hhends, hhColor]
  have hhu1 : H.Adj (Sum.inr h)
      (Sum.inl (C.blockVertex (D.gammaIndex d) 1)) := by
    simp [H, TwoColorIncidenceGraph, Incident, hhends, hhColor]
  have hu1b1 : H.Adj (Sum.inl (C.blockVertex (D.gammaIndex d) 1))
      (Sum.inr (C.blockEdge (D.gammaIndex d) 1)) := by
    simp [H, TwoColorIncidenceGraph, Incident, ha1ends, hb1Color, phiD, gamma]
  have hb0Component : H.connectedComponentMk
      (Sum.inr (C.blockEdge (D.gammaIndex d) 0)) =
      H.connectedComponentMk (Sum.inl v) := by
    change Sum.inr (C.blockEdge (D.gammaIndex d) 0) ∈
      TwoColorComponent G phiD gamma beta (Sum.inl v)
    rw [← hp.2.2.2]
    exact hb0Support
  have hu0Component : H.connectedComponentMk
      (Sum.inl (C.blockVertex (D.gammaIndex d) 0)) =
      H.connectedComponentMk (Sum.inl v) :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hb0u0).symm.trans
      hb0Component
  have hhComponent : H.connectedComponentMk (Sum.inr h) =
      H.connectedComponentMk (Sum.inl v) :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hu0h).symm.trans
      hu0Component
  have hu1Component : H.connectedComponentMk
      (Sum.inl (C.blockVertex (D.gammaIndex d) 1)) =
      H.connectedComponentMk (Sum.inl v) :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hhu1).symm.trans
      hhComponent
  have componentSupport :
    ∀ x : Sum V E, H.connectedComponentMk x = H.connectedComponentMk (Sum.inl v) → x ∈ p.support
  := by
    intro x hx
    have hx' : x ∈ TwoColorComponent G phiD gamma beta (Sum.inl v) := hx
    rw [← hp.2.2.2] at hx'
    exact hx'
  have hu0Support := componentSupport _ hu0Component
  have hhSupport := componentSupport _ hhComponent
  have hu1Support := componentSupport _ hu1Component
  have hpath : p.IsPath := hp.2.1
  have hlength : 0 < p.length := by
    by_contra hn
    have hzero : p.length = 0 := by omega
    have hvz : (Sum.inl v : Sum V E) = Sum.inl z :=
      SimpleGraph.Walk.eq_of_length_eq_zero hzero
    exact hp.2.2.1 (Sum.inl.inj hvz ▸ hvXd)
  have hbetaAbsent : ∀ e : E, Incident G v e → phiD e ≠ some beta := by
    intro e hve heb
    have hnot : beta ∉ PresentColors G phiD v :=
      (Finset.mem_sdiff.mp hbetaD).2
    apply hnot
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, hve, heb⟩
  have startNeighborUnique := @helper_startNeighborUnique_2406 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@beta) (@v) (@z) (@p) (@hproper)
      (@hlength) (@hbetaAbsent)
  exact @helper_continuation_264 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@R) (@beta) (@v) (@z) (@p) (@hv)
      (@hbetaD) (@hbetaGamma) (@hp) (@hZsubXd) (@hvXd) (@hproper) (@hglobalD) (@helemD)
      (@hclosedD) (@hgammaDef) (@hb0Color) (@hb1Color) (@hexact) (by assumption) (@hb0Support)
      (@hb1Support) (@h) (@hhends) (@heffect) (@hhColor) (@a0) (@ha0ends) (@a1) (@ha1ends)
      (@hb0u0) (@hu0h) (@hhu1) (@hu1b1) (@hu0Support) (@hhSupport) (@hu1Support) (@hpath)
      (@hlength) (@startNeighborUnique)
end GoldbergSeymour

end
