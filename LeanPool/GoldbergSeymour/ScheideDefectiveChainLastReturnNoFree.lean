/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DegreeTwoPaths

public import LeanPool.GoldbergSeymour.OutsideTreeColorSwapStable
public import LeanPool.GoldbergSeymour.TreeSequenceBoundaryEdgeAppendExists
public import LeanPool.GoldbergSeymour.ScheideDepartureReturn
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumUnused
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumBoundaryFacts
public import LeanPool.GoldbergSeymour.MissingColorIncidenceEndpoint

/-!
# Scheide Defective Chain Last Return No Free

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_new_adj_old_344.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha gamma : Fin k),
        gamma ∈ TreeFreeColors phi T →
    ∀ (u z : V) (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk (Sum.inl u) (Sum.inl z)) (i2
        : Fin (p.length + (1 : ℕ))) (v2 : V) ⦃beta : Fin k⦄, beta ∈ MissingColors G phi v2 →
    let X : Finset V := TreeSequenceVertexSet T; beta ≠ gamma → alpha ≠ gamma → alpha ≠ beta →
        BoundaryColorEdges G phi X beta = ∅ →
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi beta gamma; (
    ∀ (f : E), TreeIncidentEdge T f → phi1 f = phi f) →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha gamma;
    let R : Set (V ⊕ E) := {q : V ⊕ E |
    ∃ (n : ℕ), (↑i2 : ℕ) ≤ n ∧ n ≤ p.length ∧ p.getVert n = q}; (
    ∀ {n : ℕ} {w : V}, (↑i2 : ℕ) ≤ n → n ≤ p.length → p.getVert n = Sum.inl w → n = (↑i2 : ℕ) ∧ w
        = v2 ∨ (↑i2 : ℕ) < n ∧ w ∉ X) → (
    ∀ {e : E} {w : V}, TreeIncidentEdge T e → w ∉ X → Incident G w e → e ∈ BoundaryEdges G X) →
    ∀ {q r : V ⊕ E}, q ∈ R → (TwoColorIncidenceGraph G phi1 alpha beta).Adj q r → H.Adj q r := by
  classical
  intro V E _ _ G k e0 phi T alpha gamma _ u z p i2 v2 beta hbeta X hbg hag hab hbetaBoundary
      phi1 htreeFixed1 H R tail_vertex boundary_of_tree_incident_outside q r hq hadj
  obtain ⟨n, hn, hnl, hget⟩ := hq
  cases q with
  | inl w =>
    cases r with
    | inl x => simp [TwoColorIncidenceGraph] at hadj
    | inr e =>
      have hnew : Incident G w e ∧
          (phi1 e = some alpha ∨ phi1 e = some beta) := by
        simpa [TwoColorIncidenceGraph] using hadj
      have hold : phi e = some alpha ∨ phi e = some gamma := by
        by_cases hti : TreeIncidentEdge T e
        · have hfix := htreeFixed1 e hti
          rcases hnew.2 with ha | hb
          · exact Or.inl (hfix.symm.trans ha)
          · have hbetaOld : phi e = some beta := hfix.symm.trans hb
            rcases tail_vertex hn hnl hget with hbase | hout
            · have hwbeta : beta ∈ PresentColors G phi w := by
                simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨e, hnew.1, hbetaOld⟩
              have hwmissing : beta ∈ MissingColors G phi w := by
                simpa [hbase.2] using hbeta
              have hnotPresent : beta ∉ PresentColors G phi w := by
                simpa [MissingColors] using hwmissing
              exact False.elim (hnotPresent hwbeta)
            · have heb := boundary_of_tree_incident_outside hti hout.2 hnew.1
              have hec : e ∈ BoundaryColorEdges G phi X beta :=
                Finset.mem_filter.mpr ⟨heb, hbetaOld⟩
              rw [hbetaBoundary] at hec
              simp at hec
        · rcases hnew.2 with ha | hb
          · by_cases heB : phi e = some beta
            · have heq : some gamma = some alpha := by
                simpa [phi1, OutsideTreeColorSwap, hti, heB, hbg] using ha
              exact False.elim (hag (Option.some.inj heq).symm)
            · by_cases heG : phi e = some gamma
              · have heq : some beta = some alpha := by
                  simpa [phi1, OutsideTreeColorSwap, hti, heB, heG, hbg,
                    hbg.symm] using ha
                exact False.elim (hab (Option.some.inj heq).symm)
              · exact Or.inl (by
                  simpa [phi1, OutsideTreeColorSwap, hti, heB, heG] using ha)
          · by_cases heB : phi e = some beta
            · have heq : some gamma = some beta := by
                simpa [phi1, OutsideTreeColorSwap, hti, heB, hbg] using hb
              exact False.elim (hbg (Option.some.inj heq).symm)
            · by_cases heG : phi e = some gamma
              · exact Or.inr heG
              · have : phi e = some beta := by
                  simp [phi1, OutsideTreeColorSwap, hti, heB, heG] at hb
                exact False.elim (heB this)
      simpa [H, TwoColorIncidenceGraph] using And.intro hnew.1 hold
  | inr e =>
    cases r with
    | inr f => simp [TwoColorIncidenceGraph] at hadj
    | inl w =>
      have hn0 : 0 < n := by
        by_contra hz
        have hz0 : n = 0 := by omega
        rw [hz0] at hget
        simp at hget
      have hprev := p.adj_getVert_succ (i := n - 1) (by omega)
      have hidx : n - 1 + 1 = n := by omega
      rw [hidx, hget] at hprev
      cases hprevNode : p.getVert (n - 1) with
      | inr f =>
        rw [hprevNode] at hprev
        exfalso
        simp [TwoColorIncidenceGraph] at hprev
      | inl x =>
        have hold : phi e = some alpha ∨ phi e = some gamma := by
          rw [hprevNode] at hprev
          simpa [H, TwoColorIncidenceGraph] using hprev.2
        have hinc : Incident G w e := by
          simpa [TwoColorIncidenceGraph] using hadj.1
        simpa [H, TwoColorIncidenceGraph] using And.intro hinc hold

private theorem helper_R_closed_422.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha gamma : Fin k),
        gamma ∈ TreeFreeColors phi T →
    ∀ (u z : V) (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk (Sum.inl u) (Sum.inl z)),
        ScheideDefectiveChainPath T phi alpha gamma u z p →
    ∀ (i1 i2 : Fin (p.length + (1 : ℕ))) (v1 v2 : V), ScheideDepartureReturn T i1 i2 v1 v2 →
    ∀ ⦃beta : Fin k⦄,
    let X : Finset V := TreeSequenceVertexSet T; IsProperEdgeColoring G phi → v2 ∈ X →
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi beta gamma; (
    ∀ (f : E), TreeIncidentEdge T f → phi1 f = phi f) → beta ∈ MissingColors G phi1 v2 →
    ∀ (fR : E), p.getVert ((↑i2 : ℕ) + (1 : ℕ)) = Sum.inr fR → Incident G v2 fR ∧ (phi fR = some
        alpha ∨ phi fR = some gamma) → (↑i2 : ℕ) + (1 : ℕ) < p.length → phi fR = some alpha →
    let H : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G phi alpha gamma; (
    ∀ (n m : ℕ), n ≤ p.length → m ≤ p.length → H.Adj (p.getVert n) (p.getVert m) → n + (1 : ℕ) = m
        ∨ m + (1 : ℕ) = n) →
    let R : Set (V ⊕ E) := {q : V ⊕ E |
    ∃ (n : ℕ), (↑i2 : ℕ) ≤ n ∧ n ≤ p.length ∧ p.getVert n = q}; (
    ∀ {q r : V ⊕ E}, q ∈ R → (TwoColorIncidenceGraph G phi1 alpha beta).Adj q r → H.Adj q r) →
    ∀ {q r : V ⊕ E}, q ∈ R → (TwoColorIncidenceGraph G phi1 alpha beta).Adj q r → r ∈ R := by
  classical
  intro V E _ _ G k e0 phi T alpha gamma _ u z p hp i1 i2 v1 v2 hdepart beta X hproper hv2X phi1
      htreeFixed1 hbeta1 fR hfRnode hfRdata hfirstlt hfRalpha H old_adjacent_indices R new_adj_old q
      r hq hadj
  let _ := Fintype.ofFinite V
  have holdAdj := new_adj_old hq hadj
  obtain ⟨n, hn, hnl, hget⟩ := hq
  have hqOld : q ∈ TwoColorComponent G phi alpha gamma (Sum.inl u) := by
    rw [← hp.2.2.2]
    rw [← hget]
    exact p.getVert_mem_support n
  have hrOld : r ∈ TwoColorComponent G phi alpha gamma (Sum.inl u) := by
    change H.connectedComponentMk r = H.connectedComponentMk (Sum.inl u)
    change H.connectedComponentMk q = H.connectedComponentMk (Sum.inl u) at hqOld
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      holdAdj.symm).trans hqOld
  have hrSupport : r ∈ p.support := by
    have : r ∈ {x | x ∈ p.support} := by
      rw [hp.2.2.2]
      exact hrOld
    exact this
  obtain ⟨m, hmget, hml⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hrSupport
  have hindices := old_adjacent_indices n m hnl hml (by simpa [H, hget, hmget] using holdAdj)
  rcases hindices with hforward | hback
  · exact ⟨m, by omega, hml, hmget⟩
  · by_cases hm : i2.val ≤ m
    · exact ⟨m, hm, hml, hmget⟩
    · have hnbase : n = i2.val := by omega
      have hmbase : m + 1 = i2.val := by omega
      have hqv : q = Sum.inl v2 := by
        rw [← hget, hnbase, hdepart.2.2.2.2.2.1]
      cases hr : r with
      | inl w =>
        have hbad : (TwoColorIncidenceGraph G phi1 alpha beta).Adj
            (Sum.inl v2) (Sum.inl w) := by
          simpa [hqv, hr] using hadj
        exfalso
        simp [TwoColorIncidenceGraph] at hbad
      | inr e =>
        have hadj' : (TwoColorIncidenceGraph G phi1 alpha beta).Adj
            (Sum.inl v2) (Sum.inr e) := by
          simpa [hqv, hr] using hadj
        have hnew : Incident G v2 e ∧
            (phi1 e = some alpha ∨ phi1 e = some beta) := by
          simpa [TwoColorIncidenceGraph] using hadj'
        have hnotBeta : phi1 e ≠ some beta := by
          intro he
          have hpresent : beta ∈ PresentColors G phi1 v2 := by
            simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨e, hnew.1, he⟩
          have hnotPresent : beta ∉ PresentColors G phi1 v2 := by
            simpa [MissingColors] using hbeta1
          exact hnotPresent hpresent
        have heAlpha : phi1 e = some alpha := hnew.2.resolve_right hnotBeta
        have heTree : TreeIncidentEdge T e := by
          exact ⟨v2, by simpa [X] using hv2X, hnew.1⟩
        have heOld : phi e = some alpha := (htreeFixed1 e heTree).symm.trans heAlpha
        have hef : e ≠ fR := by
          intro hef
          have hnodes : p.getVert m = p.getVert (i2.val + 1) := by
            rw [hmget, hr, hef, hfRnode]
          have hidx := hp.2.1.getVert_injOn hml
            (Nat.le_of_lt hfirstlt) hnodes
          omega
        exact False.elim ((hproper hef ⟨v2, hnew.1, hfRdata.1⟩ heOld) hfRalpha)

private theorem helper_boundary_tail_unique_500.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha gamma : Fin k),
        gamma ∈ TreeFreeColors phi T →
    ∀ (u z : V) (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk (Sum.inl u) (Sum.inl z)),
        ScheideDefectiveChainPath T phi alpha gamma u z p →
    ∀ (i1 i2 : Fin (p.length + (1 : ℕ))) (v1 v2 : V), ScheideDepartureReturn T i1 i2 v1 v2 →
    let X : Finset V := TreeSequenceVertexSet T; (
    ∀ {q : Sym2 V} {x y : V}, x ∈ q → y ∈ q → x ≠ y → q = s(x, y)) →
    ∀ (fR : E), p.getVert ((↑i2 : ℕ) + (1 : ℕ)) = Sum.inr fR →
    let R : Set (V ⊕ E) := {q : V ⊕ E |
    ∃ (n : ℕ), (↑i2 : ℕ) ≤ n ∧ n ≤ p.length ∧ p.getVert n = q};
    ∀ f ∈ BoundaryEdges G X, Sum.inr f ∈ R → f = fR := by
  classical
  intro V E _ _ G k e0 phi T alpha gamma _ u z p hp i1 i2 v1 v2 hdepart X ends_eq_of_mem fR
      hfRnode R f hf hfr
  obtain ⟨n, hn, hnl, hget⟩ := hfr
  have hnstrict : i2.val < n := by
    have hne : n ≠ i2.val := by
      intro heq
      have : Sum.inr f = Sum.inl v2 := by
        rw [← hget, heq, hdepart.2.2.2.2.2.1]
      simp at this
    omega
  by_cases heq : n = i2.val + 1
  · apply Sum.inr.inj
    rw [← hget, heq, hfRnode]
  · have hfar : i2.val + 1 < n := by omega
    have hn0 : 0 < n := by omega
    have hnlt : n < p.length := by
      by_contra hnot
      have hnend : n = p.length := by omega
      have hz : p.getVert n = Sum.inl z := by simp [hnend]
      rw [hget] at hz
      simp at hz
    have hleftAdj := p.adj_getVert_succ (i := n - 1) (by omega)
    have hleftIdx : n - 1 + 1 = n := by omega
    rw [hleftIdx, hget] at hleftAdj
    have hrightAdj := p.adj_getVert_succ (i := n) hnlt
    rw [hget] at hrightAdj
    cases hl : p.getVert (n - 1) with
    | inr e =>
      rw [hl] at hleftAdj
      exfalso
      simp [TwoColorIncidenceGraph] at hleftAdj
    | inl a =>
      rw [hl] at hleftAdj
      cases hr : p.getVert (n + 1) with
      | inr e =>
        rw [hr] at hrightAdj
        exfalso
        simp [TwoColorIncidenceGraph] at hrightAdj
      | inl b =>
        rw [hr] at hrightAdj
        have haout : a ∉ X := by
          have hi : i2.val < n - 1 := by omega
          exact hdepart.2.2.2.2.2.2.2
            ⟨n - 1, Nat.lt_succ_of_le ((Nat.sub_le n 1).trans hnl)⟩ hi a hl
        have hbout : b ∉ X := by
          have hi : i2.val < n + 1 := by omega
          exact hdepart.2.2.2.2.2.2.2
            ⟨n + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hnlt)⟩ hi b hr
        obtain ⟨x, hx, y, hy, hends⟩ := by
          simpa [BoundaryEdges] using hf
        have habv : a ≠ b := by
          intro habv
          have hnodes : p.getVert (n - 1) = p.getVert (n + 1) := by
            rw [hl, hr, habv]
          have hidx := hp.2.1.getVert_injOn
            (Nat.sub_le _ _ |>.trans hnl) (Nat.succ_le_of_lt hnlt) hnodes
          omega
        have habEnds : G.ends f = s(a, b) :=
          ends_eq_of_mem hleftAdj.1 hrightAdj.1 habv
        have hxab : x = a ∨ x = b := by
          have hxmem : x ∈ s(a, b) := by rw [← habEnds]; exact hends ▸ Sym2.mem_iff.mpr (Or.inl rfl)
          simpa using hxmem
        rcases hxab with rfl | rfl
        · exact False.elim (haout hx)
        · exact False.elim (hbout hx)

private theorem helper_htreeU_643.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha gamma : Fin k) (u
        z : V) (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk (Sum.inl u) (Sum.inl z)) (_ :
        Fin (p.length + (1 : ℕ))) (v2 : V) ⦃beta : Fin k⦄,
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi beta gamma;
    ∀ (f : E),
    let phi2 : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 alpha beta (Sum.inl v2);
        alpha ∈ MissingColors G phi2 v2 → phi2 f = some alpha → TashkinovTree G e0 phi2 T →
    ∀ (U : TreeSequence G e0) (hUlen : U.length = T.length + (1 : ℕ)), TreeSequenceInitialSegment
        T U → U.edge (Fin.cast ((
    by omega
    )) (Fin.last T.length)) = f →
    ∀ (v2index : Fin (T.length + (1 : ℕ))), T.vertex v2index = v2 → TashkinovTree G e0 phi2 U := by
  classical
  intro V E _ _ G k e0 phi T alpha gamma u z p i2 v2 beta phi1 f phi2 halpha2 hfPhi2 htree2 U hUlen
      hinit hlast v2index hv2index j hj
  let _ := Fintype.ofFinite V
  by_cases hjlast : j.val = T.length
  · have hjeq : j = Fin.cast hUlen.symm (Fin.last T.length) := by
      apply Fin.ext
      simp [hjlast]
    let a : Fin (j.val + 1) := ⟨v2index.val, by simpa [hjlast] using v2index.isLt⟩
    refine ⟨a, alpha, ?_, ?_⟩
    · rw [hjeq, hlast]
      exact hfPhi2
    · have hacast : Fin.castLT a
          (Nat.lt_trans a.isLt (Nat.succ_lt_succ j.isLt)) =
        Fin.castLE (Nat.succ_le_succ hinit.1) v2index := by
        apply Fin.ext
        rfl
      rw [hacast, hinit.2.1, hv2index]
      exact halpha2
  · have hjold : j.val < T.length := by
      rw [hUlen] at j
      omega
    let jT : Fin T.length := ⟨j.val, hjold⟩
    obtain ⟨a, c, hcolor, hmiss⟩ := htree2 jT (by simpa [jT] using hj)
    let aa : Fin (j.val + 1) := ⟨a.val, by simpa [jT] using a.isLt⟩
    refine ⟨aa, c, ?_, ?_⟩
    · have hjeq : j = Fin.castLE hinit.1 jT := by
        apply Fin.ext
        rfl
      rw [hjeq, hinit.2.2]
      exact hcolor
    · have hacast : Fin.castLT aa
          (Nat.lt_trans aa.isLt (Nat.succ_lt_succ j.isLt)) =
        Fin.castLE (Nat.succ_le_succ hinit.1)
          (Fin.castLT a
            (Nat.lt_trans a.isLt (Nat.succ_lt_succ jT.isLt))) := by
        apply Fin.ext
        rfl
      rw [hacast, hinit.2.1]
      exact hmiss

private theorem helper_htree2_771.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha gamma : Fin k),
        alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T) →
    ∀ (v2 : V) ⦃beta : Fin k⦄, beta ∈ TreeFreeColors phi T →
    let X : Finset V := TreeSequenceVertexSet T; Disjoint (DefectiveColors G phi
        (TreeSequenceVertexSet T)) (TreeUsedColors phi T) ∧ Disjoint (TreeFreeColors phi T)
        (TreeUsedColors phi T) → TashkinovTree G e0 phi T →
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi beta gamma; (
    ∀ w ∈ X, MissingColors G phi1 w = MissingColors G phi w) → (
    ∀ (f : E), TreeIncidentEdge T f → phi1 f = phi f) →
    let _ : Set (V ⊕ E) := TwoColorComponent G phi1 alpha beta (Sum.inl v2);
    let phi2 : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 alpha beta (Sum.inl v2); (
    have C : Set (V ⊕ E) := TwoColorComponent G phi1 alpha beta (Sum.inl v2);
    have phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi1 alpha beta (Sum.inl v2); (
    ∀ (v : V), Sum.inl v ∉ C → MissingColors G phi' v = MissingColors G phi1 v) ∧ (
    ∀ (v : V), Sum.inl v ∈ C → alpha ∈ MissingColors G phi1 v → beta ∈ MissingColors G phi' v) ∧ (
    ∀ (v : V), Sum.inl v ∈ C → beta ∈ MissingColors G phi1 v → alpha ∈ MissingColors G phi' v) ∧
    ∀ (v : V) (c : Fin k), c ≠ alpha → c ≠ beta → (c ∈ MissingColors G phi' v ↔ c ∈ MissingColors
        G phi1 v)) → (
    ∀ (j : Fin T.length), TreeIncidentEdge T (T.edge j)) → TashkinovTree G e0 phi2 T := by
  classical
  intro V E _ _ G k e0 phi T alpha gamma halpha v2 beta hbetaFree X hunused htree phi1 hmissing1
      htreeFixed1 C phi2 hbehavior tree_edge_incident j hj
  obtain ⟨a, c, hcolor, hmiss⟩ := htree j hj
  have hcUsed : c ∈ TreeUsedColors phi T := by
    simp only [TreeUsedColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j, hj, hcolor⟩
  have hca : c ≠ alpha := by
    intro h
    exact (Finset.disjoint_left.mp hunused.1) halpha (h ▸ hcUsed)
  have hcb : c ≠ beta := by
    intro h
    exact (Finset.disjoint_left.mp hunused.2) hbetaFree (h ▸ hcUsed)
  have hcolor1 : phi1 (T.edge j) = some c :=
    (htreeFixed1 (T.edge j) (tree_edge_incident j)).trans hcolor
  have hcolor2 : phi2 (T.edge j) = some c := by
    by_cases heC : Sum.inr (T.edge j) ∈ C
    · simp [phi2, TwoColorComponentSwap, C, heC, hcolor1, hca, hcb]
    · simp [phi2, TwoColorComponentSwap, C, heC, hcolor1]
  refine ⟨a, c, hcolor2, ?_⟩
  let w := T.vertex (Fin.castLT a
    (Nat.lt_trans a.isLt (Nat.succ_lt_succ j.isLt)))
  have hwX : w ∈ X := by simp [w, X, TreeSequenceVertexSet]
  have hmiss1 : c ∈ MissingColors G phi1 w := by
    rw [hmissing1 w hwX]
    exact hmiss
  have hcBehavior := hbehavior.2.2.2 w c hca hcb
  simpa [phi2, w] using hcBehavior.mpr hmiss1

private theorem helper_hcomponentTail_765.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) (k : ℕ) (e0
        : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha gamma : Fin k) (u z :
        V) (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk (Sum.inl u) (Sum.inl z)) (i2 : Fin
        (p.length + (1 : ℕ))) (v2 : V) ⦃beta : Fin k⦄,
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi beta gamma;
    let R : Set (V ⊕ E) := {q : V ⊕ E |
    ∃ (n : ℕ), (↑i2 : ℕ) ≤ n ∧ n ≤ p.length ∧ p.getVert n = q}; Sum.inl v2 ∈ R → (
    ∀ {q r : V ⊕ E}, q ∈ R → (TwoColorIncidenceGraph G phi1 alpha beta).Adj q r → r ∈ R) →
    let C : Set (V ⊕ E) := TwoColorComponent G phi1 alpha beta (Sum.inl v2); C ⊆ R := by
  classical
  intro V E _ _ G k e0 phi T alpha gamma u z p i2 v2 beta phi1 R hv2R R_closed C q hq
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  change (TwoColorIncidenceGraph G phi1 alpha beta).connectedComponentMk q =
    (TwoColorIncidenceGraph G phi1 alpha beta).connectedComponentMk (Sum.inl v2) at hq
  have hreach := SimpleGraph.ConnectedComponent.exact hq
  obtain ⟨walk⟩ := hreach
  have propagate : ∀ {a b : Sum V E},
      (TwoColorIncidenceGraph G phi1 alpha beta).Walk a b → a ∈ R → b ∈ R := by
    intro a b walk ha
    induction walk with
    | nil => exact ha
    | @cons a c b hac rest ih => exact ih (R_closed ha hac)
  exact propagate walk.reverse hv2R

private theorem helper_continuation_778.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0), GlobalMaximumTriple G k e0 phi T →
    ∀ (alpha gamma : Fin k), alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T) → gamma ∈
        TreeFreeColors phi T →
    ∀ (u z : V) (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk (Sum.inl u) (Sum.inl z)),
        ScheideDefectiveChainPath T phi alpha gamma u z p →
    ∀ (i1 i2 : Fin (p.length + (1 : ℕ))) (v1 v2 : V), ScheideDepartureReturn T i1 i2 v1 v2 →
    ∀ ⦃beta : Fin k⦄, beta ∈ TreeFreeColors phi T →
    let X : Finset V := TreeSequenceVertexSet T; TashkinovOrder G = (TreeSequenceVertexSet T).card
        ∧ (3 : ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T) → ((DefectiveColors G phi (TreeSequenceVertexSet T) = ∅ →
        ColoredVertexSetStronglyClosed G phi (TreeSequenceVertexSet T)) ∧ (
    ∀ alpha ∈ TreeMissingColors phi T, BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha =
        ∅) ∧
    ∀ alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T), Odd (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card ∧ (3 : ℕ) ≤ (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card) → Disjoint (DefectiveColors G phi
        (TreeSequenceVertexSet T)) (TreeUsedColors phi T) ∧ Disjoint (TreeFreeColors phi T)
        (TreeUsedColors phi T) → TashkinovTree G e0 phi T → v2 ∈ X → alpha ≠ beta → (
    ∀ {q : Sym2 V} {x y : V}, x ∈ q → y ∈ q → x ≠ y → q = s(x, y)) →
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi beta gamma;
        IsProperEdgeColoring G phi1 → IsOneEdgeUncolored phi1 e0 → (
    ∀ w ∈ X, MissingColors G phi1 w = MissingColors G phi w) → (
    ∀ (f : E), TreeIncidentEdge T f → phi1 f = phi f) → beta ∈ MissingColors G phi1 v2 →
    ∀ (fR : E), p.getVert ((↑i2 : ℕ) + (1 : ℕ)) = Sum.inr fR →
    let R : Set (V ⊕ E) := {q : V ⊕ E |
    ∃ (n : ℕ), (↑i2 : ℕ) ≤ n ∧ n ≤ p.length ∧ p.getVert n = q}; Sum.inl v2 ∈ R → (
    ∀ {q r : V ⊕ E}, q ∈ R → (TwoColorIncidenceGraph G phi1 alpha beta).Adj q r → r ∈ R) → False
  := by
  classical
  intro V E _ _ _ G k e0 phi T hglobal alpha gamma halpha _ u z p hp i1 i2 v1 v2 hdepart beta
      hbetaFree X horder hfacts hunused htree hv2X hab ends_eq_of_mem phi1 hproper1 hone1
      hmissing1 htreeFixed1 hbeta1 fR hfRnode R hv2R R_closed
  let C := TwoColorComponent G phi1 alpha beta (Sum.inl v2)
  have hcomponentTail := @helper_hcomponentTail_765 V E inferInstance inferInstance G k e0 phi T
      alpha gamma u z p i2 v2 beta hv2R R_closed
  have boundary_tail_unique : ∀ f : E, f ∈ BoundaryEdges G X →
      Sum.inr f ∈ R → f = fR := by
    exact @helper_boundary_tail_unique_500 V E inferInstance inferInstance G k e0
        phi T alpha gamma (by assumption) u z p hp i1 i2 v1 v2 hdepart ends_eq_of_mem fR hfRnode
  have hBcard : 3 ≤ (BoundaryColorEdges G phi X alpha).card := by
    simpa [X] using (hfacts.2.2 alpha halpha).2
  obtain ⟨f, hfB, hffR⟩ :=
    (BoundaryColorEdges G phi X alpha).exists_mem_ne (by omega) fR
  have hfBoundary : f ∈ BoundaryEdges G X := (Finset.mem_filter.mp hfB).1
  have hfAlpha : phi f = some alpha := (Finset.mem_filter.mp hfB).2
  have hfNotC : Sum.inr f ∉ C := by
    intro hfC
    exact hffR (boundary_tail_unique f hfBoundary (hcomponentTail hfC))
  have hfTree : TreeIncidentEdge T f := by
    obtain ⟨x, hx, y, hy, hxy⟩ := by simpa [BoundaryEdges] using hfBoundary
    exact ⟨x, by simpa [X] using hx, by simp [Incident, hxy]⟩
  have hfPhi1 : phi1 f = some alpha := (htreeFixed1 f hfTree).trans hfAlpha
  let phi2 := TwoColorComponentSwap G phi1 alpha beta (Sum.inl v2)
  have hproper2 : IsProperEdgeColoring G phi2 := by
    simpa [phi2] using TwoColorComponentSwapProper G phi1 alpha beta hab
      hproper1 (Sum.inl v2)
  have hone2 : IsOneEdgeUncolored phi2 e0 := by
    constructor
    · simp [phi2, TwoColorComponentSwap, hone1.1]
    · intro g hge
      obtain ⟨c, hc⟩ := hone1.2 g hge
      by_cases hgC : Sum.inr g ∈ C
      · by_cases hca : phi1 g = some alpha
        · exact ⟨beta, by simp [phi2, TwoColorComponentSwap, C, hgC, hca]⟩
        · by_cases hcb : phi1 g = some beta
          · exact ⟨alpha, by simp [phi2, TwoColorComponentSwap, C, hgC, hcb]⟩
          · exact ⟨c, by simpa [phi2, TwoColorComponentSwap, C, hgC, hca, hcb] using hc⟩
      · exact ⟨c, by simpa [phi2, TwoColorComponentSwap, C, hgC] using hc⟩
  have hbehavior := TwoColorComponentSwapMissingBehavior G phi1 alpha beta hab
    hproper1 (Sum.inl v2)
  have hv2C : Sum.inl v2 ∈ C := by rfl
  have halpha2 : alpha ∈ MissingColors G phi2 v2 := by
    simpa [phi2, C] using hbehavior.2.2.1 v2 hv2C hbeta1
  have hfPhi2 : phi2 f = some alpha := by
    simp [phi2, TwoColorComponentSwap, C, hfNotC, hfPhi1]
  have tree_edge_incident : ∀ j : Fin T.length, TreeIncidentEdge T (T.edge j) := by
    intro j
    obtain ⟨a, ha⟩ := T.attaches j
    refine ⟨T.vertex j.succ, ?_, ?_⟩
    · simp [TreeSequenceVertexSet]
    · simp [Incident, ha]
  have htree2 := @helper_htree2_771 V E inferInstance inferInstance G k e0 phi T alpha gamma halpha
      v2 beta hbetaFree hunused htree hmissing1 htreeFixed1 hbehavior tree_edge_incident
  obtain ⟨U, hTU⟩ := TreeSequenceBoundaryEdgeAppendExists T f hfBoundary
  rcases hTU with ⟨hUlen, hinit, hlast⟩
  obtain ⟨v2index, hv2index⟩ := by
    simpa [X, TreeSequenceVertexSet] using hv2X
  have htreeU := @helper_htreeU_643 V E inferInstance inferInstance G k e0 phi T alpha gamma u z p
      i2 v2 beta f halpha2 hfPhi2 htree2 U hUlen hinit hlast v2index hv2index
  have hK2 : KTriple G k e0 phi2 :=
    ⟨hglobal.1.1, hglobal.1.2.1, hglobal.1.2.2.1, hproper2, hone2⟩
  have hUcard : (TreeSequenceVertexSet U).card = U.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      U.vertex_injective]
  have hTcard : X.card = T.length + 1 := by
    simp [X, TreeSequenceVertexSet, Finset.card_image_of_injective,
      T.vertex_injective]
  have hle := treeCard_le_tashkinovOrder G k e0 phi2 U hK2 htreeU
  rw [horder.1, hUcard, hUlen, hTcard] at hle
  omega

private theorem helper_continuation_700.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0), GlobalMaximumTriple G k e0 phi T →
    ∀ (alpha gamma : Fin k), alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T) → gamma ∈
        TreeFreeColors phi T →
    ∀ (u : V), gamma ∈ MissingColors G phi u →
    ∀ (z : V) (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk (Sum.inl u) (Sum.inl z)),
        ScheideDefectiveChainPath T phi alpha gamma u z p →
    ∀ (i1 i2 : Fin (p.length + (1 : ℕ))) (v1 v2 : V), ScheideDepartureReturn T i1 i2 v1 v2 →
    ∀ ⦃beta : Fin k⦄, beta ∈ MissingColors G phi v2 → beta ∈ TreeFreeColors phi T →
    let X : Finset V := TreeSequenceVertexSet T; TashkinovOrder G = (TreeSequenceVertexSet T).card
        ∧ (3 : ℕ) ≤ (TreeSequenceVertexSet T).card ∧ Odd (TreeSequenceVertexSet T).card ∧
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) ∧ ColoredVertexSetClosed G phi
        (TreeSequenceVertexSet T) → ((DefectiveColors G phi (TreeSequenceVertexSet T) = ∅ →
        ColoredVertexSetStronglyClosed G phi (TreeSequenceVertexSet T)) ∧ (
    ∀ alpha ∈ TreeMissingColors phi T, BoundaryColorEdges G phi (TreeSequenceVertexSet T) alpha =
        ∅) ∧
    ∀ alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T), Odd (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card ∧ (3 : ℕ) ≤ (BoundaryColorEdges G phi
        (TreeSequenceVertexSet T) alpha).card) → Disjoint (DefectiveColors G phi
        (TreeSequenceVertexSet T)) (TreeUsedColors phi T) ∧ Disjoint (TreeFreeColors phi T)
        (TreeUsedColors phi T) → IsProperEdgeColoring G phi → TashkinovTree G e0 phi T → v2 ∈ X →
        beta ≠ gamma → alpha ≠ gamma → alpha ≠ beta → BoundaryColorEdges G phi X beta = ∅ →
        BoundaryColorEdges G phi X gamma = ∅ → (
    ∀ {q : Sym2 V} {x y : V}, x ∈ q → y ∈ q → x ≠ y → q = s(x, y)) →
    let phi1 : PartialEdgeColoring E k := OutsideTreeColorSwap T phi beta gamma;
        IsProperEdgeColoring G phi1 → IsOneEdgeUncolored phi1 e0 → (
    ∀ w ∈ X, MissingColors G phi1 w = MissingColors G phi w) → (
    ∀ (f : E), TreeIncidentEdge T f → phi1 f = phi f) → beta ∈ MissingColors G phi1 v2 → (↑i2 : ℕ)
        < p.length → (
    ∃ (fR : E), p.getVert ((↑i2 : ℕ) + (1 : ℕ)) = Sum.inr fR) → False := by
  classical
  intro V E _ _ _ G k e0 phi T hglobal alpha gamma halpha _ u hgamma z p hp i1 i2 v1 v2 hdepart
      beta hbeta hbetaFree X horder hfacts hunused hproper htree hv2X hbg hag hab hbetaBoundary
      hgammaBoundary ends_eq_of_mem phi1 hproper1 hone1 hmissing1 htreeFixed1 hbeta1 hi2lt
      hfirstNode
  obtain ⟨fR, hfRnode⟩ := hfirstNode
  have hfRdata : Incident G v2 fR ∧
      (phi fR = some alpha ∨ phi fR = some gamma) := by
    have hadj := p.adj_getVert_succ hi2lt
    rw [hdepart.2.2.2.2.2.1, hfRnode] at hadj
    simpa [TwoColorIncidenceGraph] using hadj
  have hfirstlt : i2.val + 1 < p.length := by
    by_contra hn
    have heq : i2.val + 1 = p.length := by omega
    have hz : p.getVert (i2.val + 1) = Sum.inl z := by simp [heq]
    rw [hfRnode] at hz
    simp at hz
  have hnextNode : ∃ wR : V, p.getVert (i2.val + 2) = Sum.inl wR := by
    have hadj := p.adj_getVert_succ hfirstlt
    rw [hfRnode] at hadj
    cases hq : p.getVert (i2.val + 2) with
    | inl w => exact ⟨w, rfl⟩
    | inr f =>
      rw [hq] at hadj
      exfalso
      simp [TwoColorIncidenceGraph] at hadj
  obtain ⟨wR, hwRnode⟩ := hnextNode
  have hwRout : wR ∉ X := by
    apply hdepart.2.2.2.2.2.2.2 ⟨i2.val + 2, by omega⟩ (by simp)
    simpa [X] using hwRnode
  have hwRinc : Incident G wR fR := by
    have hadj := p.adj_getVert_succ hfirstlt
    rw [hfRnode, hwRnode] at hadj
    simpa [TwoColorIncidenceGraph] using hadj.1
  have hv2wR : v2 ≠ wR := by
    intro h
    exact hwRout (h ▸ hv2X)
  have hfRBoundary : fR ∈ BoundaryEdges G X := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v2, hv2X, wR, hwRout,
      ends_eq_of_mem hfRdata.1 hwRinc hv2wR⟩
  have hfRalpha : phi fR = some alpha := by
    rcases hfRdata.2 with ha | hg
    · exact ha
    · have : fR ∈ BoundaryColorEdges G phi X gamma :=
        Finset.mem_filter.mpr ⟨hfRBoundary, hg⟩
      rw [hgammaBoundary] at this
      simp at this
  let H := TwoColorIncidenceGraph G phi alpha gamma
  have startDegree : @SimpleGraph.degree _ H (Sum.inl u) (Fintype.ofFinite _) ≤ 1 := by
    have bound := MissingColorIncidenceEndpoint G phi gamma alpha hag.symm hproper u hgamma
    have equal : TwoColorIncidenceGraph G phi gamma alpha = H := by
      ext x y
      cases x <;> cases y <;> simp [H, TwoColorIncidenceGraph, or_comm]
    rw [← equal]
    exact bound
  have adjacent_indices_forward := degreeTwoPathAdjacentIndices p hp.2.1
    (TwoColorIncidenceDegreeAtMostTwo G phi alpha gamma hproper) startDegree
  have old_adjacent_indices : ∀ (n m : ℕ), n ≤ p.length → m ≤ p.length →
      H.Adj (p.getVert n) (p.getVert m) → n + 1 = m ∨ m + 1 = n := by
    intro n m hn hm hadj
    have hne : n ≠ m := by
      intro h
      subst m
      exact H.loopless.irrefl _ hadj
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact Or.inl (adjacent_indices_forward n m hn hm hnm hadj).symm
    · exact Or.inr (adjacent_indices_forward m n hm hn hmn hadj.symm).symm
  let R : Set (Sum V E) := {q | ∃ n : ℕ, i2.val ≤ n ∧ n ≤ p.length ∧
    p.getVert n = q}
  have hv2R : Sum.inl v2 ∈ R := by
    exact ⟨i2.val, le_rfl, by omega, hdepart.2.2.2.2.2.1⟩
  have tail_vertex : ∀ {n : ℕ} {w : V}, i2.val ≤ n → n ≤ p.length →
      p.getVert n = Sum.inl w →
      (n = i2.val ∧ w = v2) ∨ (i2.val < n ∧ w ∉ X) := by
    intro n w hn hnl hget
    by_cases heq : n = i2.val
    · left
      refine ⟨heq, ?_⟩
      apply Sum.inl.inj
      rw [← hget, heq, hdepart.2.2.2.2.2.1]
    · right
      have hlt : i2.val < n := by omega
      refine ⟨hlt, ?_⟩
      exact hdepart.2.2.2.2.2.2.2 ⟨n, by omega⟩ hlt w hget
  have boundary_of_tree_incident_outside : ∀ {e : E} {w : V},
      TreeIncidentEdge T e → w ∉ X → Incident G w e → e ∈ BoundaryEdges G X := by
    intro e w he hwout hwe
    obtain ⟨x, hx, hxe⟩ := he
    have hxX : x ∈ X := by simpa [X] using hx
    have hxw : x ≠ w := by
      intro h
      exact hwout (h ▸ hxX)
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hxX, w, hwout, ends_eq_of_mem hxe hwe hxw⟩
  have new_adj_old : ∀ {q r : Sum V E}, q ∈ R →
      (TwoColorIncidenceGraph G phi1 alpha beta).Adj q r → H.Adj q r := by
    exact @helper_new_adj_old_344 V E inferInstance inferInstance G k e0 phi T
        alpha gamma (by assumption) u z p i2 v2 beta hbeta hbg hag hab hbetaBoundary htreeFixed1
        tail_vertex boundary_of_tree_incident_outside
  have R_closed : ∀ {q r : Sum V E}, q ∈ R →
      (TwoColorIncidenceGraph G phi1 alpha beta).Adj q r → r ∈ R := by
    exact @helper_R_closed_422 V E inferInstance inferInstance G k e0 phi T alpha
        gamma (by assumption) u z p hp i1 i2 v1 v2 hdepart beta hproper hv2X htreeFixed1 hbeta1
        fR hfRnode hfRdata hfirstlt hfRalpha old_adjacent_indices new_adj_old
  exact @helper_continuation_778 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@hglobal) (@alpha) (@gamma) (@halpha) (by assumption) (@u) (@z) (@p)
      (@hp) (@i1) (@i2) (@v1) (@v2) (@hdepart) (@beta) (@hbetaFree) (@horder) (@hfacts)
      (@hunused) (@htree) (@hv2X) (@hab) (@ends_eq_of_mem) (@hproper1) (@hone1) (@hmissing1)
      (@htreeFixed1) (@hbeta1) (@fR) (@hfRnode) (@hv2R) (@R_closed)
theorem ScheideDefectiveChainLastReturnNoFree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (alpha gamma : Fin k)
    (halpha : alpha ∈ DefectiveColors G phi (TreeSequenceVertexSet T))
    (_ : gamma ∈ TreeFreeColors phi T)
    (u : V) (hu : u ∈ TreeSequenceVertexSet T)
    (hgamma : gamma ∈ MissingColors G phi u)
    (z : V)
    (p : (TwoColorIncidenceGraph G phi alpha gamma).Walk
      (Sum.inl u) (Sum.inl z))
    (hp : ScheideDefectiveChainPath T phi alpha gamma u z p)
    (i1 i2 : Fin (p.length + 1)) (v1 v2 : V)
    (hdepart : ScheideDepartureReturn T i1 i2 v1 v2) :
    Disjoint (MissingColors G phi v2) (TreeFreeColors phi T) := by
  classical
  rw [Finset.disjoint_left]
  intro beta hbeta hbetaFree
  let X := TreeSequenceVertexSet T
  have horder := ScheideGlobalMaximumOrder G k e0 phi T hglobal
  have hfacts := ScheideGlobalMaximumBoundaryFacts G k e0 phi T hglobal
  have hunused := ScheideGlobalMaximumUnused G k e0 phi T hglobal
  have hproper : IsProperEdgeColoring G phi := hglobal.1.2.2.2.1
  have hone : IsOneEdgeUncolored phi e0 := hglobal.1.2.2.2.2
  have htree : TashkinovTree G e0 phi T := hglobal.2.1
  have helem : ColoredVertexSetElementary G phi X := by
    exact horder.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phi X := by
    exact horder.2.2.2.2
  have hv2X : v2 ∈ X := by simpa [X] using hdepart.2.2.2.2.2.2.1
  have hbMissing : beta ∈ TreeMissingColors phi T := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨v2, by simpa [X] using hv2X, hbeta⟩
  have hgMissing : gamma ∈ TreeMissingColors phi T := by
    simp only [TreeMissingColors, Finset.mem_biUnion]
    exact ⟨u, hu, hgamma⟩
  have hv2_ne_u : v2 ≠ u := by
    intro hvu
    have heq : p.getVert i2.val = p.getVert 0 := by
      rw [hdepart.2.2.2.2.2.1, hvu]
      simp
    have hi20 : i2.val = 0 := hp.2.1.getVert_injOn
      (Nat.le_of_lt_succ i2.isLt) (Nat.zero_le _) heq
    have hi12 := hdepart.2.2.2.2.1
    omega
  have hbg : beta ≠ gamma := by
    intro h
    have hd := Finset.disjoint_left.mp (helem hu (by simpa [X] using hv2X) hv2_ne_u.symm)
    exact hd hgamma (h ▸ hbeta)
  have halpha_present : ∀ w, w ∈ X → alpha ∈ PresentColors G phi w := by
    intro w hw
    have hcard : 0 < (BoundaryColorEdges G phi X alpha).card := by
      have hc : 3 ≤ (BoundaryColorEdges G phi X alpha).card := by
        simpa [X] using (hfacts.2.2 alpha halpha).2
      omega
    obtain ⟨f, hf⟩ := Finset.card_pos.mp hcard
    have hnot : alpha ∉ MissingColors G phi w := by
      intro hm
      exact hclosed (Finset.mem_filter.mp hf).1 hw (Finset.mem_filter.mp hf).2 hm
    simpa [MissingColors] using hnot
  have hag : alpha ≠ gamma := by
    intro h
    have hpresent := halpha_present u (by simpa [X] using hu)
    have hnot : gamma ∉ PresentColors G phi u := by
      simpa [MissingColors] using hgamma
    exact hnot (h ▸ hpresent)
  have hab : alpha ≠ beta := by
    intro h
    have hpresent := halpha_present v2 hv2X
    have hnot : beta ∉ PresentColors G phi v2 := by
      simpa [MissingColors] using hbeta
    exact hnot (h ▸ hpresent)
  have hbetaBoundary : BoundaryColorEdges G phi X beta = ∅ := by
    simpa [X] using hfacts.2.1 beta hbMissing
  have hgammaBoundary : BoundaryColorEdges G phi X gamma = ∅ := by
    simpa [X] using hfacts.2.1 gamma hgMissing
  have ends_eq_of_mem : ∀ {q : Sym2 V} {x y : V}, x ∈ q → y ∈ q → x ≠ y →
      q = s(x, y) := by
    intro q x y hx hy hxy
    induction q using Sym2.inductionOn with
    | _ a b =>
      simp only [Sym2.mem_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        simp_all []
  let phi1 := OutsideTreeColorSwap T phi beta gamma
  have hswap1 := OutsideTreeColorSwapStable T ∅ phi beta gamma hproper hone
    hclosed hbMissing hgMissing hbg
  have hproper1 : IsProperEdgeColoring G phi1 := by
    simpa [phi1] using hswap1.1
  have hone1 : IsOneEdgeUncolored phi1 e0 := by
    simpa [phi1] using hswap1.2.1
  have hmissing1 : ∀ w, w ∈ X →
      MissingColors G phi1 w = MissingColors G phi w := by
    intro w hw
    simpa [phi1, X] using hswap1.2.2.1.2 w (by simpa [X] using hw)
  have htreeFixed1 : ∀ f, TreeIncidentEdge T f → phi1 f = phi f := by
    intro f hf
    simpa [phi1] using hswap1.2.2.2 f hf
  have hbeta1 : beta ∈ MissingColors G phi1 v2 := by
    rw [hmissing1 v2 hv2X]
    exact hbeta
  have hi2lt : i2.val < p.length := by
    by_contra hn
    have hi2eq : i2.val = p.length := by omega
    have hz : p.getVert i2.val = Sum.inl z := by simp [hi2eq]
    have : v2 = z := Sum.inl.inj (hdepart.2.2.2.2.2.1.symm.trans hz)
    exact hp.2.2.1 (this ▸ (by simpa [X] using hv2X))
  have hfirstNode : ∃ fR : E, p.getVert (i2.val + 1) = Sum.inr fR := by
    have hadj := p.adj_getVert_succ hi2lt
    rw [hdepart.2.2.2.2.2.1] at hadj
    cases hq : p.getVert (i2.val + 1) with
    | inl w =>
      rw [hq] at hadj
      exfalso
      simp [TwoColorIncidenceGraph] at hadj
    | inr f => exact ⟨f, rfl⟩
  exact @helper_continuation_700 V E inferInstance inferInstance inferInstance G k
      e0 phi T hglobal alpha gamma halpha (by assumption) u hgamma z p hp i1 i2 v1 v2 hdepart
      beta hbeta hbetaFree horder hfacts hunused hproper htree hv2X hbg hag hab hbetaBoundary
      hgammaBoundary ends_eq_of_mem hproper1 hone1 hmissing1 htreeFixed1 hbeta1 hi2lt hfirstNode
end GoldbergSeymour

end
