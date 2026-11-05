/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.OutsideTreeColorSwap
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwapStable
public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.StableColoring

/-!
# Scheide Defective Terminal Component

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperContinuation357Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let p : (TwoColorIncidenceGraph G phi D.alpha0 (↑d : Fin k)).Walk (Sum.inl (C.y (⟨(0 : ℕ),
        lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p))) (Sum.inl (D.initialZ d)) :=
        D.initialPath d;
    let i : Fin ((D.initialPath d).length + (1 : ℕ)) := D.v0Index d;
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi D.alpha0 (↑d : Fin k);
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi1 gamma (↑d : Fin k);
    let R : Set (V ⊕ E) := {q : V ⊕ E |
    ∃ (r : Fin (p.length + (1 : ℕ))), (↑i : ℕ) ≤ (↑r : ℕ) ∧ p.getVert (↑r : ℕ) = q};
    let _ : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    ∀ (_ : IsProperEdgeColoring G phi) (_ : D.v0 d ∈ X) (_ : p.IsPath) (_ :
        {q : V ⊕ E | q ∈ p.support} = TwoColorComponent G phi D.alpha0 (↑d : Fin k) (Sum.inl y0))
        (_ : IsProperEdgeColoring G phi1) (_ : IsOneEdgeUncolored phi1 e0) (_ : StableColoring T ∅
        phi phi1) (_ :
    ∀ (f : E), TreeIncidentEdge T f → phi1 f = phi f) (_ : (↑(D.f0Index d) : ℕ) = (↑(D.v0Index d)
        : ℕ) + (1 : ℕ) ∧ (↑(D.u0Index d) : ℕ) = (↑(D.v0Index d) : ℕ) + (2 : ℕ)) (_ : (↑i : ℕ) + (1
        : ℕ) < p.length) (_ : p.getVert (↑i : ℕ) = Sum.inl (D.v0 d)) (_ : p.getVert ((↑i : ℕ) + (1
        : ℕ)) = Sum.inr (D.f0 d)) (_ :
    ∀ {c : Fin k} {v : V} {e : E}, c ∈ MissingColors G phi v → Incident G v e → phi e ≠ some c) (_
        :
    ∀ {r : Fin (p.length + (1 : ℕ))} {w : V}, (↑i : ℕ) ≤ (↑r : ℕ) → p.getVert (↑r : ℕ) = Sum.inl w
        → (↑r : ℕ) = (↑i : ℕ) ∧ w = D.v0 d ∨ (↑i : ℕ) < (↑r : ℕ) ∧ w ∉ X) (_ :
    ∀ (n m : ℕ), n ≤ p.length → m ≤ p.length → H0.Adj (p.getVert n) (p.getVert m) → n + (1 : ℕ) =
        m ∨ m + (1 : ℕ) = n) (_ :
    ∀ (n : ℕ), (↑i : ℕ) ≤ n → n < p.length → H1.Adj (p.getVert n) (p.getVert (n + (1 : ℕ)))) (_ :
    ∀ {q r : V ⊕ E}, q ∈ R → H1.Adj q r → H0.Adj q r), IsProperEdgeColoring G
        (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) ∧ IsOneEdgeUncolored
        (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) e0 ∧ StableColoring T ∅
        phi (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) ∧ (
    ∀ (f : E), TreeIncidentEdge T f → OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex
        d)) f = phi f) ∧ {q : V ⊕ E |
    ∃ (r : Fin ((D.initialPath d).length + (1 : ℕ))), (↑(D.v0Index d) : ℕ) ≤ (↑r : ℕ) ∧
        (D.initialPath d).getVert (↑r : ℕ) = q} = TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)) ∧ Sum.inr (D.f0 d) ∈ TwoColorComponent G (OutsideTreeColorSwap T phi D.alpha0
        (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) ∧ (
    ∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)) ↔ v = D.v0 d) ∧ (
    ∀ (q : Fin T.length), Sum.inr (T.edge q) ∉ TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d))) ∧
    ∀ (f : E), Sum.inr f ∈ TwoColorComponent G (OutsideTreeColorSwap T phi D.alpha0 (C.gamma
        (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) →
        OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d)) f = some (C.gamma
        (D.gammaIndex d)) ∨ OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d)) f =
        some (↑d : Fin k)

private abbrev helperContinuation351Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let y0 : V := C.y (⟨(0 : ℕ), lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p);
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let p : (TwoColorIncidenceGraph G phi D.alpha0 (↑d : Fin k)).Walk (Sum.inl (C.y (⟨(0 : ℕ),
        lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩ : Fin C.p))) (Sum.inl (D.initialZ d)) :=
        D.initialPath d;
    let i : Fin ((D.initialPath d).length + (1 : ℕ)) := D.v0Index d;
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi D.alpha0 (↑d : Fin k);
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi1 gamma (↑d : Fin k);
    let _ : Set (V ⊕ E) := {q : V ⊕ E |
    ∃ (r : Fin (p.length + (1 : ℕ))), (↑i : ℕ) ≤ (↑r : ℕ) ∧ p.getVert (↑r : ℕ) = q};
    let _ : Set (V ⊕ E) := TwoColorComponent G phi1 gamma (↑d : Fin k) (Sum.inl (D.v0 d));
    ∀ (_ : IsProperEdgeColoring G phi) (_ : ColoredVertexSetClosed G phi X) (_ : y0 ∈ X) (_ : D.v0
        d ∈ X) (_ : p.IsPath) (_ : {q : V ⊕ E | q ∈ p.support} = TwoColorComponent G phi D.alpha0
        (↑d : Fin k) (Sum.inl y0)) (_ : D.alpha0 ≠ (↑d : Fin k)) (_ : gamma ≠ (↑d : Fin k)) (_ :
        D.alpha0 ≠ gamma) (_ : IsProperEdgeColoring G phi1) (_ : IsOneEdgeUncolored phi1 e0) (_ :
        StableColoring T ∅ phi phi1) (_ :
    ∀ (f : E), TreeIncidentEdge T f → phi1 f = phi f) (_ : (↑(D.f0Index d) : ℕ) = (↑(D.v0Index d)
        : ℕ) + (1 : ℕ) ∧ (↑(D.u0Index d) : ℕ) = (↑(D.v0Index d) : ℕ) + (2 : ℕ)) (_ : (↑i : ℕ) + (1
        : ℕ) < p.length) (_ : p.getVert (↑i : ℕ) = Sum.inl (D.v0 d)) (_ : p.getVert ((↑i : ℕ) + (1
        : ℕ)) = Sum.inr (D.f0 d)) (_ :
    ∀ {e : E} {w : V}, TreeIncidentEdge T e → w ∉ X → Incident G w e → e ∈ BoundaryEdges G X) (_ :
    ∀ {c : Fin k} {v : V} {e : E}, c ∈ MissingColors G phi v → Incident G v e → phi e ≠ some c) (_
        :
    ∀ {r : Fin (p.length + (1 : ℕ))} {w : V}, (↑i : ℕ) ≤ (↑r : ℕ) → p.getVert (↑r : ℕ) = Sum.inl w
        → (↑r : ℕ) = (↑i : ℕ) ∧ w = D.v0 d ∨ (↑i : ℕ) < (↑r : ℕ) ∧ w ∉ X) (_ :
    ∀ (n m : ℕ), n ≤ p.length → m ≤ p.length → n < m → H0.Adj (p.getVert n) (p.getVert m) → m = n
        + (1 : ℕ)), IsProperEdgeColoring G (OutsideTreeColorSwap T phi D.alpha0 (C.gamma
        (D.gammaIndex d))) ∧ IsOneEdgeUncolored (OutsideTreeColorSwap T phi D.alpha0 (C.gamma
        (D.gammaIndex d))) e0 ∧ StableColoring T ∅ phi (OutsideTreeColorSwap T phi D.alpha0
        (C.gamma (D.gammaIndex d))) ∧ (
    ∀ (f : E), TreeIncidentEdge T f → OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex
        d)) f = phi f) ∧ {q : V ⊕ E |
    ∃ (r : Fin ((D.initialPath d).length + (1 : ℕ))), (↑(D.v0Index d) : ℕ) ≤ (↑r : ℕ) ∧
        (D.initialPath d).getVert (↑r : ℕ) = q} = TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)) ∧ Sum.inr (D.f0 d) ∈ TwoColorComponent G (OutsideTreeColorSwap T phi D.alpha0
        (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) ∧ (
    ∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)) ↔ v = D.v0 d) ∧ (
    ∀ (q : Fin T.length), Sum.inr (T.edge q) ∉ TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d))) ∧
    ∀ (f : E), Sum.inr f ∈ TwoColorComponent G (OutsideTreeColorSwap T phi D.alpha0 (C.gamma
        (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) →
        OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d)) f = some (C.gamma
        (D.gammaIndex d)) ∨ OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d)) f =
        some (↑d : Fin k)

private theorem helper_hv0X_82.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T; D.v0 d ∈ X := by
  classical
  intro V E _ _ _ G k e0 phi T C D d X
  have hexit : ScheideExitVertex T phi (D.v0 d) :=
    (Finset.mem_filter.mp (D.v0_is_exit d)).2
  rcases hexit with
    ⟨u, a, b, hu, ha, hb, z, q, hq, j, hj, hv, hlast⟩
  simpa [X] using hv

private theorem helper_hdeltaPresent_99.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (d : ↥(DefectiveColors G
        phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T; ColoredVertexSetClosed G phi X → DefectiveColor G
        phi X (↑d : Fin k) →
    ∀ v ∈ X, (↑d : Fin k) ∈ PresentColors G phi v := by
  classical
  intro V E _ _ G k e0 phi T d X hclosed hdefective v hv
  have hcard : 0 < (BoundaryColorEdges G phi X d.1).card := by
    change 2 ≤ (BoundaryColorEdges G phi X d.1).card at hdefective
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hcard
  have hnot : d.1 ∉ MissingColors G phi v := by
    intro hm
    exact hclosed (Finset.mem_filter.mp hb).1 hv
      (Finset.mem_filter.mp hb).2 hm
  simpa [MissingColors] using hnot

private theorem helper_hgammaDelta_118.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let gamma : Fin k := C.gamma (D.gammaIndex d); D.v0 d ∈ X → (
    ∀ v ∈ X, (↑d : Fin k) ∈ PresentColors G phi v) → gamma ≠ (↑d : Fin k) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d X gamma hv0X hdeltaPresent h
  have hpresent := hdeltaPresent (D.v0 d) hv0X
  have hm : d.1 ∈ MissingColors G phi (D.v0 d) := by
    exact h ▸ (by simpa [gamma] using D.gamma_missing_at_v0 d)
  have hnot : d.1 ∉ PresentColors G phi (D.v0 d) := by
    simpa [MissingColors] using hm
  exact hnot hpresent

private theorem helper_ends_eq_of_mem_157.{u_1} :
    open scoped Classical in
    ∀ {V : Type u_1} {q : Sym2 V} {x y : V}, x ∈ q → y ∈ q → x ≠ y → q = s(x, y) := by
  classical
  intro V q x y hx hy hxy
  induction q using Sym2.inductionOn with
  | _ a b =>
    simp only [Sym2.mem_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp_all []

private theorem helper_boundary_of_tree_incident_outside_165.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (e0 : E)
        (T : TreeSequence G e0),
    let X : Finset V := TreeSequenceVertexSet T; (
    ∀ {q : Sym2 V} {x y : V}, x ∈ q → y ∈ q → x ≠ y → q = s(x, y)) →
    ∀ {e : E} {w : V}, TreeIncidentEdge T e → w ∉ X → Incident G w e → e ∈ BoundaryEdges G X := by
  classical
  intro V E _ _ G e0 T X ends_eq_of_mem e w he hwout hwe
  obtain ⟨x, hx, hxe⟩ := he
  have hxX : x ∈ X := by simpa [X] using hx
  have hxw : x ≠ w := by
    intro h
    exact hwout (h ▸ hxX)
  simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨x, hxX, w, hwout, ends_eq_of_mem hxe hwe hxw⟩

private theorem helper_missing_no_incident_175.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (phi : PartialEdgeColoring E k) {c : Fin k} {v : V} {e : E}, c ∈ MissingColors G phi v →
        Incident G v e → phi e ≠ some c := by
  classical
  intro V E _ _ G k phi c v e hm hinc hc
  let _ := Fintype.ofFinite V
  have hp : c ∈ PresentColors G phi v := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, hinc, hc⟩
  have hnot : c ∉ PresentColors G phi v := by
    simpa [MissingColors] using hm
  exact hnot hp

private theorem helper_continuation_357.{u_1, u_2} :
    helperContinuation357Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T C D d X y0 gamma phi1 p i H0 H1 R K hproper hv0X hpathIs hsupport
      hproper1 hone1 hstable1 hfixed hsucc hiOneLt hv0At hf0At missing_no_incident tail_vertex
      old_adjacent_indices tail_step_new new_adj_old
  have R_closed : ∀ {q r : Sum V E}, q ∈ R → H1.Adj q r → r ∈ R := by
    intro q r hq hadj
    have holdAdj := new_adj_old hq hadj
    obtain ⟨n, hn, hget⟩ := hq
    have hqOld : q ∈ TwoColorComponent G phi D.alpha0 d.1 (Sum.inl y0) := by
      rw [← hsupport]
      rw [← hget]
      exact p.getVert_mem_support n.val
    have hrOld : r ∈ TwoColorComponent G phi D.alpha0 d.1 (Sum.inl y0) := by
      change H0.connectedComponentMk r = H0.connectedComponentMk (Sum.inl y0)
      change H0.connectedComponentMk q = H0.connectedComponentMk (Sum.inl y0) at hqOld
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        holdAdj.symm).trans hqOld
    have hrSupport : r ∈ p.support := by
      have : r ∈ {x | x ∈ p.support} := by
        rw [hsupport]
        exact hrOld
      exact this
    obtain ⟨m, hmget, hml⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hrSupport
    have hindices := old_adjacent_indices n.val m (Nat.le_of_lt_succ n.isLt) hml
      (by simpa [H0, hget, hmget] using holdAdj)
    rcases hindices with hforward | hback
    · refine ⟨⟨m, Nat.lt_succ_of_le hml⟩, ?_, hmget⟩
      have him : i.val ≤ m := hn.trans (by omega)
      exact him
    · by_cases hm : i.val ≤ m
      · exact ⟨⟨m, Nat.lt_succ_of_le hml⟩, hm, hmget⟩
      · have hnbase : n.val = i.val := by omega
        have hmbase : m + 1 = i.val := by omega
        have hqv : q = Sum.inl (D.v0 d) := by
          rw [← hget, hnbase, hv0At]
        cases hr : r with
        | inl w =>
          have hbad : H1.Adj (Sum.inl (D.v0 d)) (Sum.inl w) := by
            simpa [hqv, hr] using hadj
          simp [H1, TwoColorIncidenceGraph] at hbad
        | inr e =>
          have hbad : H1.Adj (Sum.inl (D.v0 d)) (Sum.inr e) := by
            simpa [hqv, hr] using hadj
          have hnew : Incident G (D.v0 d) e ∧
              (phi1 e = some gamma ∨ phi1 e = some d.1) := by
            simpa [H1, TwoColorIncidenceGraph] using hbad
          have heTree : TreeIncidentEdge T e :=
            ⟨D.v0 d, by simpa [X] using hv0X, hnew.1⟩
          have heOld : phi e = some d.1 := by
            rcases hnew.2 with hg | hd
            · have hgold : phi e = some gamma := (hfixed e heTree).symm.trans hg
              exact False.elim ((missing_no_incident
                (by simpa [gamma] using D.gamma_missing_at_v0 d) hnew.1) hgold)
            · exact (hfixed e heTree).symm.trans hd
          have hef : e ≠ D.f0 d := by
            intro hef
            have hnodes : p.getVert m = p.getVert (i.val + 1) := by
              rw [hmget, hr, hef, hf0At]
            have hidx := hpathIs.getVert_injOn hml (Nat.le_of_lt hiOneLt) hnodes
            omega
          exact False.elim ((hproper hef
            ⟨D.v0 d, hnew.1, by simp [Incident, D.f0_ends d]⟩ heOld)
              (D.f0_color d))
  have hcomponentTail : K ⊆ R := by
    intro q hq
    change H1.connectedComponentMk q =
      H1.connectedComponentMk (Sum.inl (D.v0 d)) at hq
    have hreach := SimpleGraph.ConnectedComponent.exact hq
    obtain ⟨walk⟩ := hreach
    have propagate : ∀ {a b : Sum V E}, H1.Walk a b → a ∈ R → b ∈ R := by
      intro a b walk ha
      induction walk with
      | nil => exact ha
      | @cons a c b hac rest ih => exact ih (R_closed ha hac)
    have hv0R : Sum.inl (D.v0 d) ∈ R := by
      exact ⟨i, le_rfl, hv0At⟩
    exact propagate walk.reverse hv0R
  have htailComponent : R ⊆ K := by
    intro q hq
    obtain ⟨r, hir, hget⟩ := hq
    have go : ∀ t : ℕ, i.val + t ≤ p.length →
        H1.connectedComponentMk (p.getVert (i.val + t)) =
          H1.connectedComponentMk (Sum.inl (D.v0 d)) := by
      intro t ht
      induction t with
      | zero => simpa using congrArg H1.connectedComponentMk hv0At
      | succ t ih =>
        have hprev : i.val + t ≤ p.length := by omega
        have hadj := tail_step_new (i.val + t) (by omega) (by omega)
        have hcc := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
        exact hcc.symm.trans (ih hprev)
    change H1.connectedComponentMk q = H1.connectedComponentMk (Sum.inl (D.v0 d))
    rw [← hget]
    have heq : i.val + (r.val - i.val) = r.val := by omega
    rw [← heq]
    have hrle : r.val ≤ p.length := Nat.le_of_lt_succ r.isLt
    exact go (r.val - i.val) (by omega)
  have hRK : R = K := Set.Subset.antisymm htailComponent hcomponentTail
  have hf0K : Sum.inr (D.f0 d) ∈ K := by
    rw [← hRK]
    exact ⟨D.f0Index d, by simp [i, hsucc.1], by simpa [p] using D.f0_at_index d⟩
  have hKtree : ∀ v : V, v ∈ X →
      (Sum.inl v ∈ K ↔ v = D.v0 d) := by
    intro v hv
    constructor
    · intro hvK
      have hvR : Sum.inl v ∈ R := by rw [hRK]; exact hvK
      obtain ⟨r, hir, hget⟩ := hvR
      rcases tail_vertex hir hget with hbase | hout
      · exact hbase.2
      · exact False.elim (hout.2 hv)
    · rintro rfl
      rw [← hRK]
      exact ⟨i, le_rfl, hv0At⟩
  have htreeEdges : ∀ q : Fin T.length, Sum.inr (T.edge q) ∉ K := by
    intro q hqK
    have hqR : Sum.inr (T.edge q) ∈ R := by rw [hRK]; exact hqK
    obtain ⟨r, hir, hget⟩ := hqR
    have hrlt : r.val < p.length := by
      by_contra hn
      have hre : r.val = p.length := by omega
      have hend : p.getVert r.val = Sum.inl (D.initialZ d) := by
        simp [hre]
      rw [hget] at hend
      simp at hend
    have hadj := p.adj_getVert_succ hrlt
    rw [hget] at hadj
    cases hnext : p.getVert (r.val + 1) with
    | inr e =>
      rw [hnext] at hadj
      simp [TwoColorIncidenceGraph] at hadj
    | inl w =>
      rw [hnext] at hadj
      have hwout : w ∉ X := by
        have hir0 : (D.v0Index d).val ≤ r.val := by simpa [i] using hir
        have hout := D.v0_is_last_tree_vertex d
          ⟨r.val + 1, by
            dsimp [p] at hrlt ⊢
            omega⟩ (by
              change (D.v0Index d).val < r.val + 1
              omega) w (by simpa [p] using hnext)
        simpa [X] using hout
      have hwinc : Incident G w (T.edge q) := by
        simpa [H0, TwoColorIncidenceGraph] using hadj.1
      obtain ⟨a, ha⟩ := T.attaches q
      have hwend : w = T.vertex q.succ ∨
          w = T.vertex (Fin.castLT a
            (Nat.lt_trans a.isLt (Nat.succ_lt_succ q.isLt))) := by
        unfold Incident at hwinc
        rw [ha] at hwinc
        simpa using hwinc
      rcases hwend with rfl | rfl <;> exact hwout (by simp [X, TreeSequenceVertexSet])
  have hKcolors : ∀ f : E, Sum.inr f ∈ K →
      phi1 f = some gamma ∨ phi1 f = some d.1 := by
    intro f hfK
    have hfR : Sum.inr f ∈ R := by rw [hRK]; exact hfK
    obtain ⟨r, hir, hget⟩ := hfR
    have hstrict : i.val < r.val := by
      by_contra hn
      have hre : r.val = i.val := by omega
      have : Sum.inr f = Sum.inl (D.v0 d) := by
        rw [← hget, hre, hv0At]
      simp at this
    have hadj := tail_step_new (r.val - 1) (by omega) (by omega)
    have hidx : r.val - 1 + 1 = r.val := by omega
    rw [hidx, hget] at hadj
    cases hprev : p.getVert (r.val - 1) with
    | inr e =>
      rw [hprev] at hadj
      simp [H1, TwoColorIncidenceGraph] at hadj
    | inl w =>
      rw [hprev] at hadj
      simpa [H1, TwoColorIncidenceGraph] using hadj.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [phi1, gamma] using hproper1
  · simpa [phi1, gamma] using hone1
  · simpa [phi1, gamma] using hstable1
  · intro f hf
    simpa [phi1, gamma] using hfixed f hf
  · simpa [R, K, p, i, phi1, gamma] using hRK
  · simpa [K, phi1, gamma] using hf0K
  · intro v hv
    simpa [K, X, phi1, gamma] using hKtree v (by simpa [X] using hv)
  · intro q
    simpa [K, phi1, gamma] using htreeEdges q
  · intro f hf
    simpa [K, phi1, gamma] using hKcolors f (by simpa [K, phi1, gamma] using hf)

private theorem helper_continuation_351.{u_1, u_2} :
    helperContinuation351Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T C D d X y0 gamma phi1 p i H0 H1 R K hproper hclosed hy0X hv0X
      hpathIs hsupport halphaDelta hgammaDelta halphaGamma hproper1 hone1 hstable1 hfixed hsucc
      hiOneLt hv0At hf0At boundary_of_tree_incident_outside missing_no_incident tail_vertex
      adjacent_indices_forward
  have old_adjacent_indices : ∀ (n m : ℕ), n ≤ p.length → m ≤ p.length →
      H0.Adj (p.getVert n) (p.getVert m) → n + 1 = m ∨ m + 1 = n := by
    intro n m hn hm hadj
    have hne : n ≠ m := by
      intro h
      subst m
      exact H0.loopless.irrefl _ hadj
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact Or.inl (adjacent_indices_forward n m hn hm hnm hadj).symm
    · exact Or.inr (adjacent_indices_forward m n hm hn hmn hadj.symm).symm
  have outside_edge_effect : ∀ {w : V} {e : E}, w ∉ X → Incident G w e →
      (phi e = some D.alpha0 ∨ phi e = some d.1) →
      phi1 e = some gamma ∨ phi1 e = some d.1 := by
    intro w e hwout hinc hold
    by_cases hti : TreeIncidentEdge T e
    · have hb := boundary_of_tree_incident_outside hti hwout hinc
      have hnotAlpha : phi e ≠ some D.alpha0 := by
        intro ha
        exact (hclosed hb hy0X ha) (by simpa [y0] using D.alpha0_missing_at_y0)
      have hd : phi e = some d.1 := hold.resolve_left hnotAlpha
      exact Or.inr ((hfixed e hti).trans hd)
    · rcases hold with ha | hd
      · left
        simp [phi1, OutsideTreeColorSwap, hti, ha]
      · right
        simp [phi1, OutsideTreeColorSwap, hti, hd, halphaDelta.symm, hgammaDelta.symm]
  have tail_step_new : ∀ n : ℕ, i.val ≤ n → n < p.length →
      H1.Adj (p.getVert n) (p.getVert (n + 1)) := by
    intro n hin hnlt
    have hold := p.adj_getVert_succ hnlt
    cases hleft : p.getVert n with
    | inl w =>
      cases hright : p.getVert (n + 1) with
      | inl x =>
        rw [hleft, hright] at hold
        simp [TwoColorIncidenceGraph] at hold
      | inr e =>
        rw [hleft, hright] at hold
        have hdata : Incident G w e ∧
            (phi e = some D.alpha0 ∨ phi e = some d.1) := by
          simpa [H0, TwoColorIncidenceGraph] using hold
        let rn : Fin (p.length + 1) := ⟨n, by omega⟩
        have htv := tail_vertex (r := rn) (w := w) (by simpa [rn] using hin)
          (by simpa [rn] using hleft)
        have hnew : phi1 e = some gamma ∨ phi1 e = some d.1 := by
          rcases htv with hbase | hout
          · have hnbase : n = i.val := hbase.1
            have heq : e = D.f0 d := by
              apply Sum.inr.inj
              rw [← hright, hnbase, hf0At]
            subst e
            right
            apply (hfixed (D.f0 d) ?_).trans (D.f0_color d)
            exact ⟨D.v0 d, by simpa [X] using hv0X, by simpa [hbase.2] using hdata.1⟩
          · exact outside_edge_effect hout.2 hdata.1 hdata.2
        simpa [H1, TwoColorIncidenceGraph] using And.intro hdata.1 hnew
    | inr e =>
      cases hright : p.getVert (n + 1) with
      | inr f =>
        rw [hleft, hright] at hold
        simp [TwoColorIncidenceGraph] at hold
      | inl w =>
        rw [hleft, hright] at hold
        have hdata : Incident G w e ∧
            (phi e = some D.alpha0 ∨ phi e = some d.1) := by
          simpa [H0, TwoColorIncidenceGraph] using hold
        let rn : Fin (p.length + 1) := ⟨n + 1, by omega⟩
        have htv := tail_vertex (r := rn) (w := w) (by simp [rn]; omega)
          (by simpa [rn] using hright)
        have hwout : w ∉ X := by
          rcases htv with hbase | hout
          · simp [rn] at hbase
            omega
          · exact hout.2
        have hnew := outside_edge_effect hwout hdata.1 hdata.2
        simpa [H1, TwoColorIncidenceGraph] using And.intro hdata.1 hnew
  have new_edge_old : ∀ {r : Fin (p.length + 1)} {w : V} {e : E},
      i.val ≤ r.val → p.getVert r.val = Sum.inl w → Incident G w e →
      (phi1 e = some gamma ∨ phi1 e = some d.1) →
      phi e = some D.alpha0 ∨ phi e = some d.1 := by
    intro r w e hir hget hinc hnew
    have htv := tail_vertex hir hget
    by_cases hti : TreeIncidentEdge T e
    · have hfix := hfixed e hti
      rcases hnew with hg | hd
      · have hgold : phi e = some gamma := hfix.symm.trans hg
        rcases htv with hbase | hout
        · exact False.elim ((missing_no_incident
            (by simpa [gamma] using D.gamma_missing_at_v0 d)
            (by simpa [hbase.2] using hinc)) hgold)
        · have hb := boundary_of_tree_incident_outside hti hout.2 hinc
          exact False.elim ((hclosed hb hv0X hgold)
            (by simpa [gamma] using D.gamma_missing_at_v0 d))
      · exact Or.inr (hfix.symm.trans hd)
    · rcases hnew with hg | hd
      · by_cases ha : phi e = some D.alpha0
        · exact Or.inl ha
        · by_cases hgc : phi e = some gamma
          · have heq : some D.alpha0 = some gamma := by
              simp [phi1, OutsideTreeColorSwap, hti, hgc, halphaGamma, halphaGamma.symm] at hg
            exact False.elim (halphaGamma (Option.some.inj heq))
          · have : phi e = some gamma := by
              simp [phi1, OutsideTreeColorSwap, hti, ha, hgc] at hg
            exact False.elim (hgc this)
      · by_cases ha : phi e = some D.alpha0
        · have heq : some gamma = some d.1 := by
            simpa [phi1, OutsideTreeColorSwap, hti, ha] using hd
          exact False.elim (hgammaDelta (Option.some.inj heq))
        · by_cases hgc : phi e = some gamma
          · have heq : some D.alpha0 = some d.1 := by
              simpa [phi1, OutsideTreeColorSwap, hti, ha, hgc, halphaGamma,
                halphaGamma.symm] using hd
            exact False.elim (halphaDelta (Option.some.inj heq))
          · exact Or.inr (by
              simpa [phi1, OutsideTreeColorSwap, hti, ha, hgc] using hd)
  have new_adj_old : ∀ {q r : Sum V E}, q ∈ R → H1.Adj q r → H0.Adj q r := by
    intro q r hq hadj
    obtain ⟨n, hn, hget⟩ := hq
    cases q with
    | inl w =>
      cases r with
      | inl x => simp [H1, TwoColorIncidenceGraph] at hadj
      | inr e =>
        have hnew : Incident G w e ∧
            (phi1 e = some gamma ∨ phi1 e = some d.1) := by
          simpa [H1, TwoColorIncidenceGraph] using hadj
        have hold := new_edge_old hn hget hnew.1 hnew.2
        simpa [H0, TwoColorIncidenceGraph] using And.intro hnew.1 hold
    | inr e =>
      cases r with
      | inr f => simp [H1, TwoColorIncidenceGraph] at hadj
      | inl w =>
        have hn0 : 0 < n.val := by
          by_contra hz
          have hz0 : n.val = 0 := by omega
          rw [hz0] at hget
          have : Sum.inr e = Sum.inl y0 := by simpa [p, y0] using hget.symm
          simp at this
        have hprev := p.adj_getVert_succ (i := n.val - 1) (by omega)
        have hidx : n.val - 1 + 1 = n.val := by omega
        rw [hidx, hget] at hprev
        cases hprevNode : p.getVert (n.val - 1) with
        | inr f =>
          rw [hprevNode] at hprev
          simp [TwoColorIncidenceGraph] at hprev
        | inl x =>
          rw [hprevNode] at hprev
          have hold : phi e = some D.alpha0 ∨ phi e = some d.1 := by
            simpa [H0, TwoColorIncidenceGraph] using hprev.2
          have hinc : Incident G w e := by
            simpa [H1, TwoColorIncidenceGraph] using hadj.1
          simpa [H0, TwoColorIncidenceGraph] using And.intro hinc hold
  exact @helper_continuation_357 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@C) (@D) (@d) (@hproper) (@hv0X) (@hpathIs) (@hsupport) (@hproper1)
      (@hone1) (@hstable1) (@hfixed) (@hsucc) (@hiOneLt) (@hv0At) (@hf0At) (@missing_no_incident)
      (@tail_vertex) (@old_adjacent_indices) (@tail_step_new) (@new_adj_old)
private theorem helper_continuation_826.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
        T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
    let X : Finset V := TreeSequenceVertexSet T;
    let y0 : V := C.y (⟨(0 : ℕ),
    by
            first
            | omega
            | ( have := GoldbergSeymour.TreeSequence.positive T
                have := C.p_ge_two
                all_goals omega)
    ⟩ : Fin C.p);
    let gamma : Fin k := C.gamma (D.gammaIndex d);
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi D.alpha0 gamma;
    let p : (TwoColorIncidenceGraph G phi D.alpha0 (↑d : Fin k)).Walk (Sum.inl (C.y (⟨(0 : ℕ),
    by
                first
                | omega
                | ( have := GoldbergSeymour.TreeSequence.positive T
                    have := C.p_ge_two
                    all_goals omega)
    ⟩ : Fin C.p))) (Sum.inl (D.initialZ d)) := D.initialPath d;
    let i : Fin ((D.initialPath d).length + (1 : ℕ)) := D.v0Index d;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi D.alpha0 (↑d : Fin k);
    ∀ (_ : IsProperEdgeColoring G phi) (_ : ColoredVertexSetClosed G phi X) (_ : y0 ∈ X) (_ : D.v0
        d ∈ X) (_ : p.IsPath) (_ : {q : V ⊕ E | q ∈ p.support} = TwoColorComponent G phi D.alpha0
        (↑d : Fin k) (Sum.inl y0)) (_ : D.alpha0 ≠ (↑d : Fin k)) (_ : gamma ≠ (↑d : Fin k)) (_ :
        D.alpha0 ≠ gamma) (_ : IsProperEdgeColoring G phi1) (_ : IsOneEdgeUncolored phi1 e0) (_ :
        StableColoring T ∅ phi phi1) (_ :
    ∀ (f : E), TreeIncidentEdge T f → phi1 f = phi f) (_ : (↑(D.f0Index d) : ℕ) = (↑(D.v0Index d)
        : ℕ) + (1 : ℕ) ∧ (↑(D.u0Index d) : ℕ) = (↑(D.v0Index d) : ℕ) + (2 : ℕ)) (_ : (↑i : ℕ) + (1
        : ℕ) < p.length) (_ : p.getVert (↑i : ℕ) = Sum.inl (D.v0 d)) (_ : p.getVert ((↑i : ℕ) + (1
        : ℕ)) = Sum.inr (D.f0 d)) (_ :
    ∀ {e : E} {w : V}, TreeIncidentEdge T e → w ∉ X → Incident G w e → e ∈ BoundaryEdges G X) (_ :
    ∀ {c : Fin k} {v : V} {e : E}, c ∈ MissingColors G phi v → Incident G v e → phi e ≠ some c) (_
        :
    ∀ {r : Fin (p.length + (1 : ℕ))} {w : V}, (↑i : ℕ) ≤ (↑r : ℕ) → p.getVert (↑r : ℕ) = Sum.inl w
        → (↑r : ℕ) = (↑i : ℕ) ∧ w = D.v0 d ∨ (↑i : ℕ) < (↑r : ℕ) ∧ w ∉ X), IsProperEdgeColoring G
        (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) ∧ IsOneEdgeUncolored
        (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) e0 ∧ StableColoring T ∅
        phi (OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d))) ∧ (
    ∀ (f : E), TreeIncidentEdge T f → OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex
        d)) f = phi f) ∧ {q : V ⊕ E |
    ∃ (r : Fin ((D.initialPath d).length + (1 : ℕ))), (↑(D.v0Index d) : ℕ) ≤ (↑r : ℕ) ∧
        (D.initialPath d).getVert (↑r : ℕ) = q} = TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)) ∧ Sum.inr (D.f0 d) ∈ TwoColorComponent G (OutsideTreeColorSwap T phi D.alpha0
        (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) ∧ (
    ∀ v ∈ TreeSequenceVertexSet T, Sum.inl v ∈ TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d)) ↔ v = D.v0 d) ∧ (
    ∀ (q : Fin T.length), Sum.inr (T.edge q) ∉ TwoColorComponent G (OutsideTreeColorSwap T phi
        D.alpha0 (C.gamma (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl
        (D.v0 d))) ∧
    ∀ (f : E), Sum.inr f ∈ TwoColorComponent G (OutsideTreeColorSwap T phi D.alpha0 (C.gamma
        (D.gammaIndex d))) (C.gamma (D.gammaIndex d)) (↑d : Fin k) (Sum.inl (D.v0 d)) →
        OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d)) f = some (C.gamma
        (D.gammaIndex d)) ∨ OutsideTreeColorSwap T phi D.alpha0 (C.gamma (D.gammaIndex d)) f =
        some (↑d : Fin k) := by
  classical
  intro V E _ _ _ G k e0 phi T C D d X y0 gamma phi1 p i H0 hproper hclosed hy0X hv0X hpathIs
      hsupport halphaDelta hgammaDelta halphaGamma hproper1 hone1 hstable1 hfixed hsucc hiOneLt
      hv0At hf0At boundary_of_tree_incident_outside missing_no_incident tail_vertex
  have hy0Degree : @SimpleGraph.degree _ H0 (Sum.inl y0)
      (Fintype.ofFinite _) ≤ 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [SimpleGraph.mem_neighborFinset] at ha hb
    cases a with
    | inl a => simp [H0, TwoColorIncidenceGraph] at ha
    | inr e =>
      cases b with
      | inl b => simp [H0, TwoColorIncidenceGraph] at hb
      | inr f =>
        simp only [H0, TwoColorIncidenceGraph] at ha hb
        have hea : phi e = some d.1 := ha.2.resolve_left
          (missing_no_incident D.alpha0_missing_at_y0 ha.1)
        have hfa : phi f = some d.1 := hb.2.resolve_left
          (missing_no_incident D.alpha0_missing_at_y0 hb.1)
        by_cases hef : e = f
        · exact congrArg Sum.inr hef
        · exact False.elim ((hproper hef ⟨y0, ha.1, hb.1⟩ hea) hfa)
  have adjacent_indices_forward : ∀ (n m : ℕ), n ≤ p.length → m ≤ p.length →
      n < m → H0.Adj (p.getVert n) (p.getVert m) → m = n + 1 := by
    intro n m hn hm hnm hadj
    by_contra hne
    have hgap : n + 1 < m := by omega
    by_cases hn0 : n = 0
    · subst n
      have hfirstAdj := p.adj_getVert_succ (by omega : 0 < p.length)
      have hstart : p.getVert 0 = Sum.inl y0 := by simp [p, y0]
      have hneigh : p.getVert 1 ≠ p.getVert m := by
        intro heq
        have := hpathIs.getVert_injOn (show 1 ≤ p.length by omega) hm heq
        omega
      have htwo : 2 ≤ (@SimpleGraph.neighborFinset (Sum V E) H0 (Sum.inl y0)
          (Fintype.ofFinite _)).card := by
        have hs : ({p.getVert 1, p.getVert m} : Finset (Sum V E)) ⊆
            @SimpleGraph.neighborFinset (Sum V E) H0 (Sum.inl y0)
              (Fintype.ofFinite _) := by
          intro q hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · simpa [SimpleGraph.mem_neighborFinset, H0, hstart] using hfirstAdj
          · simpa [SimpleGraph.mem_neighborFinset, H0, hstart] using hadj
        have hc : ({p.getVert 1, p.getVert m} : Finset (Sum V E)).card = 2 := by
          simp [hneigh]
        rw [← hc]
        exact Finset.card_le_card hs
      rw [← SimpleGraph.card_neighborFinset_eq_degree] at hy0Degree
      omega
    · have hnlt : n < p.length := by omega
      have hleft : H0.Adj (p.getVert n) (p.getVert (n - 1)) := by
        have h := p.adj_getVert_succ (i := n - 1) (by omega)
        have heq : n - 1 + 1 = n := by omega
        simpa [H0, heq] using h.symm
      have hright : H0.Adj (p.getVert n) (p.getVert (n + 1)) := by
        simpa [H0] using p.adj_getVert_succ hnlt
      have hnm1 : p.getVert (n - 1) ≠ p.getVert (n + 1) := by
        intro heq
        have := hpathIs.getVert_injOn (Nat.sub_le n 1 |>.trans hn)
          (Nat.succ_le_of_lt hnlt) heq
        omega
      have hnm2 : p.getVert (n - 1) ≠ p.getVert m := by
        intro heq
        have := hpathIs.getVert_injOn (Nat.sub_le n 1 |>.trans hn) hm heq
        omega
      have hnm3 : p.getVert (n + 1) ≠ p.getVert m := by
        intro heq
        have := hpathIs.getVert_injOn (Nat.succ_le_of_lt hnlt) hm heq
        omega
      have hthree : 3 ≤ (@SimpleGraph.neighborFinset (Sum V E) H0 (p.getVert n)
          (Fintype.ofFinite _)).card := by
        let S : Finset (Sum V E) :=
          {p.getVert (n - 1), p.getVert (n + 1), p.getVert m}
        have hs : S ⊆ @SimpleGraph.neighborFinset (Sum V E) H0 (p.getVert n)
            (Fintype.ofFinite _) := by
          intro q hq
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl
          · simpa [SimpleGraph.mem_neighborFinset] using hleft
          · simpa [SimpleGraph.mem_neighborFinset] using hright
          · simpa [SimpleGraph.mem_neighborFinset] using hadj
        have hc : S.card = 3 := by
          simp [S, hnm1, hnm2, hnm3]
        rw [← hc]
        exact Finset.card_le_card hs
      have hdeg := TwoColorIncidenceDegreeAtMostTwo G phi D.alpha0 d.1 hproper
        (p.getVert n)
      change @SimpleGraph.degree _ H0 (p.getVert n) (Fintype.ofFinite _) ≤ 2 at hdeg
      rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
      omega
  exact @helper_continuation_351 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@C) (@D) (@d) (@hproper) (@hclosed) (@hy0X) (@hv0X) (@hpathIs)
      (@hsupport) (@halphaDelta) (@hgammaDelta) (@halphaGamma) (@hproper1) (@hone1) (@hstable1)
      (@hfixed) (@hsucc) (@hiOneLt) (@hv0At) (@hf0At) (@boundary_of_tree_incident_outside)
      (@missing_no_incident) (@tail_vertex) (@adjacent_indices_forward)

theorem ScheideDefectiveTerminalComponent {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideReducedConfiguration G k e0 phi T)
    (D : ScheideDefectiveSetup G k e0 phi T C)
    (d : {delta // delta ∈ DefectiveColors G phi (TreeSequenceVertexSet T)}) :
    let gamma := C.gamma (D.gammaIndex d)
    let phi1 := OutsideTreeColorSwap T phi D.alpha0 gamma
    let K := TwoColorComponent G phi1 gamma d.1 (Sum.inl (D.v0 d))
    IsProperEdgeColoring G phi1 ∧ IsOneEdgeUncolored phi1 e0 ∧
      StableColoring T ∅ phi phi1 ∧
      (∀ f : E, TreeIncidentEdge T f → phi1 f = phi f) ∧
      {q | ∃ r : Fin ((D.initialPath d).length + 1),
        (D.v0Index d).val ≤ r.val ∧ (D.initialPath d).getVert r.val = q} = K ∧
      Sum.inr (D.f0 d) ∈ K ∧
      (∀ v : V, v ∈ TreeSequenceVertexSet T →
        (Sum.inl v ∈ K ↔ v = D.v0 d)) ∧
      (∀ q : Fin T.length, Sum.inr (T.edge q) ∉ K) ∧
      ∀ f : E, Sum.inr f ∈ K →
        phi1 f = some gamma ∨ phi1 f = some d.1 := by
  classical
  dsimp only
  let X := TreeSequenceVertexSet T
  let y0 := C.y ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩
  let gamma := C.gamma (D.gammaIndex d)
  let phi1 := OutsideTreeColorSwap T phi D.alpha0 gamma
  let p := D.initialPath d
  let i := D.v0Index d
  let H0 := TwoColorIncidenceGraph G phi D.alpha0 d.1
  let H1 := TwoColorIncidenceGraph G phi1 gamma d.1
  let R : Set (Sum V E) := {q | ∃ r : Fin (p.length + 1),
    i.val ≤ r.val ∧ p.getVert r.val = q}
  let K := TwoColorComponent G phi1 gamma d.1 (Sum.inl (D.v0 d))
  have hproper : IsProperEdgeColoring G phi := C.globally_maximum.1.2.2.2.1
  have hone : IsOneEdgeUncolored phi e0 := C.globally_maximum.1.2.2.2.2
  have horder := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have hclosed0 : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.2
  have hclosed : ColoredVertexSetClosed G phi X := by
    exact hclosed0
  have hy0X : y0 ∈ X := by
    dsimp [y0, X]
    rw [← C.base_vertex_position
      ⟨0, lt_of_lt_of_le Nat.zero_lt_two C.p_ge_two⟩]
    simp [TreeSequenceVertexSet]
  have hv0X := @helper_hv0X_82 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@C) (@D) (@d)
  have hpath : ScheideDefectiveChainPath T phi D.alpha0 d.1
      y0 (D.initialZ d) p := by
    simpa [y0, p] using D.initial_path_full d
  have hpathIs : p.IsPath := hpath.2.1
  have hsupport : {q | q ∈ p.support} =
      TwoColorComponent G phi D.alpha0 d.1 (Sum.inl y0) := hpath.2.2.2
  have hdefective : DefectiveColor G phi X d.1 := by
    have hd := d.2
    change d.1 ∈ (Finset.univ.filter fun delta =>
      DefectiveColor G phi X delta) at hd
    exact (Finset.mem_filter.mp hd).2
  have hdeltaPresent := @helper_hdeltaPresent_99 (@V) (@E) inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@d) (@hclosed) (@hdefective)
  have halphaDelta : D.alpha0 ≠ d.1 := by
    intro h
    have hpresent := hdeltaPresent y0 hy0X
    have hm : d.1 ∈ MissingColors G phi y0 := by
      simpa [y0] using (h ▸ D.alpha0_missing_at_y0)
    have hnot : d.1 ∉ PresentColors G phi y0 := by
      simpa [MissingColors] using hm
    exact hnot hpresent
  have hgammaDelta := @helper_hgammaDelta_118 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@d) (@hv0X) (@hdeltaPresent)
  have halphaGamma : D.alpha0 ≠ gamma := by
    simpa [gamma] using D.alpha0_not_block (D.gammaIndex d)
  have halphaTree : D.alpha0 ∈ TreeMissingColors phi T := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨y0, by simpa [X] using hy0X, by simpa [y0] using D.alpha0_missing_at_y0⟩
  have hgammaTree : gamma ∈ TreeMissingColors phi T := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨D.v0 d, by simpa [X] using hv0X,
      by simpa [gamma] using D.gamma_missing_at_v0 d⟩
  have hswap := OutsideTreeColorSwapStable T ∅ phi D.alpha0 gamma
    hproper hone hclosed0 halphaTree hgammaTree halphaGamma
  have hproper1 : IsProperEdgeColoring G phi1 := by
    simpa [phi1] using hswap.1
  have hone1 : IsOneEdgeUncolored phi1 e0 := by
    simpa [phi1] using hswap.2.1
  have hstable1 : StableColoring T ∅ phi phi1 := by
    simpa [phi1] using hswap.2.2.1
  have hfixed : ∀ f, TreeIncidentEdge T f → phi1 f = phi f := by
    intro f hf
    simpa [phi1] using hswap.2.2.2 f hf
  have hsucc := D.successive_indices d
  have hiTwo : i.val + 2 < p.length + 1 := by
    dsimp [i, p]
    rw [← hsucc.2]
    exact (D.u0Index d).isLt
  have hiOneLt : i.val + 1 < p.length := by omega
  have hv0At : p.getVert i.val = Sum.inl (D.v0 d) := by
    simpa [p, i] using D.v0_at_index d
  have hf0At : p.getVert (i.val + 1) = Sum.inr (D.f0 d) := by
    rw [← hsucc.1]
    simpa [p] using D.f0_at_index d
  have ends_eq_of_mem := @helper_ends_eq_of_mem_157 (@V)
  have boundary_of_tree_incident_outside := @helper_boundary_of_tree_incident_outside_165 (@V) (@E)
      inferInstance inferInstance (@G) (@e0) (@T) (@ends_eq_of_mem)
  have missing_no_incident := @helper_missing_no_incident_175 (@V) (@E) inferInstance inferInstance
      (@G) (@k) (@phi)
  have tail_vertex : ∀ {r : Fin (p.length + 1)} {w : V}, i.val ≤ r.val →
      p.getVert r.val = Sum.inl w →
      (r.val = i.val ∧ w = D.v0 d) ∨ (i.val < r.val ∧ w ∉ X) := by
    intro r w hir hget
    by_cases hri : r.val = i.val
    · left
      refine ⟨hri, ?_⟩
      apply Sum.inl.inj
      rw [← hget, hri, hv0At]
    · right
      have hlt : i.val < r.val := by omega
      refine ⟨hlt, ?_⟩
      simpa [X, p, i] using D.v0_is_last_tree_vertex d r hlt w (by simpa [p] using hget)
  exact @helper_continuation_826 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@C) (@D) (@d) (@hproper) (@hclosed) (@hy0X) (@hv0X) (@hpathIs)
      (@hsupport) (@halphaDelta) (@hgammaDelta) (@halphaGamma) (@hproper1) (@hone1) (@hstable1)
      (@hfixed) (@hsucc) (@hiOneLt) (@hv0At) (@hf0At) (@boundary_of_tree_incident_outside)
      (@missing_no_incident) (@tail_vertex)
end GoldbergSeymour

end
