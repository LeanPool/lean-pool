/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryColorEdges
public import LeanPool.GoldbergSeymour.OutsideTreeColorSwapStable
public import LeanPool.GoldbergSeymour.OutsideSwapPrefixEffects
public import LeanPool.GoldbergSeymour.StableColoringBeforeVertex
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorIncidenceDegreeAtMostTwo

/-!
# Extension Base Claim45Singleton

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hgammaRho3_224.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN
        beta : Fin k) (u : V) (_ : beta ≠ gammaN),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let rho3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
    ∀ (_ : gammaN ≠ beta) (_ : beta ∈ MissingColors G rho0 u), gammaN ∈ MissingColors G rho3 u := by
  classical
  intro V E _ _ G k e0 TjPrime rho1 gammaN deltaN beta u hbetaGamma rho0 rho3 hgammaBeta hbetaRho0
  let _ := Fintype.ofFinite V
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hgPresent
  simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
    true_and] at hgPresent
  obtain ⟨f, huf, hfRho3⟩ := hgPresent
  by_cases hfComponent : Sum.inr f ∈
      TwoColorComponent G rho0 gammaN beta (Sum.inl u)
  · by_cases hfGamma : rho0 f = some gammaN
    · have : (some beta : Option (Fin k)) = some gammaN := by
        simp [rho3, TwoColorComponentSwap, hfComponent, hfGamma, hbetaGamma] at hfRho3
      exact hbetaGamma (Option.some.inj this)
    · by_cases hfBeta : rho0 f = some beta
      · have hnotPresent : beta ∉ PresentColors G rho0 u := by
          simpa [MissingColors] using hbetaRho0
        exact hnotPresent (by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨f, huf, hfBeta⟩)
      · have : rho0 f = some gammaN := by
          simp [rho3, TwoColorComponentSwap, hfComponent, hfGamma, hfBeta] at hfRho3
        exact hfGamma this
  · have hfRho0 : rho0 f = some gammaN := by
      simpa [rho3, TwoColorComponentSwap, hfComponent] using hfRho3
    have hadj : (TwoColorIncidenceGraph G rho0 gammaN beta).Adj
        (Sum.inl u) (Sum.inr f) := ⟨huf, Or.inl hfRho0⟩
    apply hfComponent
    change (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
        (Sum.inr f) =
      (TwoColorIncidenceGraph G rho0 gammaN beta).connectedComponentMk
        (Sum.inl u)
    exact
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm

private theorem helper_path_edge_data_132.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {k : ℕ} (rho1 :
        PartialEdgeColoring E k) (gammaN deltaN : Fin k) (u x : V) (_ : (TwoColorIncidenceGraph G
        rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)),
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN;
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)) (_ : q.IsPath) {e : E} (_ : Sum.inr e ∈
        q.support),
    ∃ (j : ℕ), (0 : ℕ) < j ∧ j < q.length ∧ q.getVert j = Sum.inr e ∧
    ∃ (v : V) (w : V), q.getVert (j - (1 : ℕ)) = Sum.inl v ∧ q.getVert (j + (1 : ℕ)) = Sum.inl w ∧
        v ≠ w ∧ G.ends e = s(v, w) := by
  classical
  intro V E G k rho1 gammaN deltaN u x exitPath H1 a b q hq e he
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

private theorem helper_exit_edge_color_230.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] [DecidableEq V]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn TjPrime : TreeSequence G e0) (rho1 :
        PartialEdgeColoring E k) (gammaN deltaN beta : Fin k) (u x : V) (exitPath :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)) (_ : gammaN ≠
        deltaN) (_ : beta ≠ deltaN) (_ : exitPath.IsPath) (_ : (
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, Sum.inl w ∈ exitPath.support ↔
        w = u)),
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
  intro V E _ _ _ G k e0 Tn TjPrime rho1 gammaN deltaN beta u x exitPath hgammaDelta hbetaDelta
      hexitPath hexitIntersection rho0 hrho0Fixed hgammaBeta g hgRho1 H1 path_incident_vertex_mem
      path_incident_end_last hgLast e he hcolor
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

private theorem helper_exit_adj_rho0_268.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN
        beta : Fin k) (u x : V) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl x) (Sum.inl u)),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let _ : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN;
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho0 gammaN beta;
    ∀ (_ : (
    ∀ (e : E) (_ : Sum.inr e ∈ exitPath.support) (_ : rho1 e = some gammaN ∨ rho1 e = some
        deltaN), rho0 e = some gammaN ∨ rho0 e = some beta)),
    ∀ i < exitPath.length, H0.Adj (exitPath.getVert i) (exitPath.getVert (i + (1 : ℕ))) := by
  classical
  intro V E _ _ G k e0 TjPrime rho1 gammaN deltaN beta u x exitPath rho0 H1 H0 exit_edge_color i hi
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

private theorem helper_new_x_adj_old_317.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] {G : LooplessMultigraph V E}
        {k : ℕ} {e0 : E} (seed TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k)
        (gammaN deltaN beta : Fin k) (u x : V) (_ : TashkinovClosure rho1 seed TjPrime)
        (_ : gammaN ≠ deltaN) (_ : beta ≠ deltaN) (_ : beta ∈ MissingColors G rho1 u)
        (_ : u ∈ TreeSequenceVertexSet TjPrime),
        let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
        ∀ (_ : (∀ (f : E) (_ : TreeIncidentEdge TjPrime f), rho0 f = rho1 f))
          (_ : x ∉ TreeSequenceVertexSet TjPrime) (e : E) (_ : Incident G x e)
          (_ : rho0 e = some gammaN ∨ rho0 e = some beta),
          rho1 e = some gammaN ∨ rho1 e = some deltaN := by
  classical
  intro V E _ _ G k e0 seed TjPrime rho1 gammaN deltaN beta u x hclosure hgammaDelta hbetaDelta
      hbeta huPrime rho0 hrho0Fixed hxPrime e hxe hcolor
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

private theorem helper_first_p_last_359.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {k : ℕ} (rho1 :
        PartialEdgeColoring E k) (gammaN deltaN : Fin k) (terminalSupport u x : V) (p :
        (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport) (Sum.inl x))
        (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)) (_
        : p.IsPath) (_ : (
    ∀ y ∈ exitPath.support, y ∈ p.support)),
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN;
    ∀ (_ : (
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)) (_ : q.IsPath) {e : E} (_ : Sum.inr e ∈
        q.support) (_ : Incident G b e), q.getVert (q.length - (1 : ℕ)) = Sum.inr e)) (_ : H1.Adj
        (Sum.inl x) (exitPath.getVert (1 : ℕ))), p.getVert (p.length - (1 : ℕ)) = exitPath.getVert
        (1 : ℕ) := by
  classical
  intro V E G k rho1 gammaN deltaN terminalSupport u x p exitPath hpath hexitSupport H1
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

private theorem helper_old_x_neighbor_unique_376.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tj :
        TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN : Fin k)
        (terminalSupport u x z : V) (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl terminalSupport) (Sum.inl x)) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN
        deltaN).Walk (Sum.inl x) (Sum.inl u)) (_ : p.IsPath) (_ : {y : V ⊕ E | y ∈ p.support} =
        TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport)) (_ : z ∈
        TreeSequenceVertexSet Tj),
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN;
    ∀ (_ : (
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)) (_ : q.IsPath) {e : E} (_ : Sum.inr e ∈
        q.support) (_ : Incident G b e), q.getVert (q.length - (1 : ℕ)) = Sum.inr e)) (_ :
        p.getVert (p.length - (1 : ℕ)) = exitPath.getVert (1 : ℕ)) (z : V ⊕ E) (_ : H1.Adj
        (Sum.inl x) z), z = exitPath.getVert (1 : ℕ) := by
  classical
  intro V E G k e0 Tj rho1 gammaN deltaN terminalSupport u x z p exitPath hpath hcomponent hz H1
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

private theorem helper_x_neighbor_unique_407.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (Tj TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN
        beta : Fin k) (u x z : V) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl x) (Sum.inl u)) (_ : z ∈ TreeSequenceVertexSet Tj),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN;
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho0 gammaN beta;
    ∀ (_ : (
    ∀ (e : E) (_ : Incident G x e) (_ : rho0 e = some gammaN ∨ rho0 e = some beta), rho1 e = some
        gammaN ∨ rho1 e = some deltaN)) (_ : (
    ∀ (z : V ⊕ E) (_ : H1.Adj (Sum.inl x) z), z = exitPath.getVert (1 : ℕ))) (z : V ⊕ E) (_ :
        H0.Adj (Sum.inl x) z), z = exitPath.getVert (1 : ℕ) := by
  classical
  intro V E _ _ G k e0 Tj TjPrime rho1 gammaN deltaN beta u x z exitPath hz rho0 H1 H0 new_x_adj_old
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

private theorem helper_u_neighbor_unique_423.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (Tj TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN
        beta : Fin k) (u x z : V) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl x) (Sum.inl u)) (_ : z ∈ TreeSequenceVertexSet Tj),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    ∀ (_ : IsProperEdgeColoring G rho0) (_ : beta ∈ MissingColors G rho0 u) (g : E) (_ : Incident
        G u g) (_ : rho0 g = some gammaN),
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho0 gammaN beta;
    ∀ (_ : exitPath.getVert (exitPath.length - (1 : ℕ)) = Sum.inr g) (z : V ⊕ E) (_ : H0.Adj
        (Sum.inl u) z), z = exitPath.getVert (exitPath.length - (1 : ℕ)) := by
  classical
  intro V E _ _ G k e0 Tj TjPrime rho1 gammaN deltaN beta u x z exitPath hz rho0 hrho0Proper
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

private theorem helper_support_closed_448.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (Tj TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (gammaN deltaN
        beta : Fin k) (u x z : V) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl x) (Sum.inl u)) (_ : exitPath.IsPath) (_ : (2 : ℕ) ≤ exitPath.length) (_ : z ∈
        TreeSequenceVertexSet Tj),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    ∀ (_ : IsProperEdgeColoring G rho0),
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho0 gammaN beta;
    ∀ (_ : (
    ∀ i < exitPath.length, H0.Adj (exitPath.getVert i) (exitPath.getVert (i + (1 : ℕ))))) (_ : (
    ∀ (z : V ⊕ E) (_ : H0.Adj (Sum.inl x) z), z = exitPath.getVert (1 : ℕ))) (_ : (
    ∀ (z : V ⊕ E) (_ : H0.Adj (Sum.inl u) z), z = exitPath.getVert (exitPath.length - (1 : ℕ)))),
    ∀ w ∈ exitPath.support,
    ∀ (z : V ⊕ E), H0.Adj w z → z ∈ exitPath.support := by
  classical
  intro V E _ _ G k e0 Tj TjPrime rho1 gammaN deltaN beta u x z exitPath hexitPath hexitLength hz
      rho0 hrho0Proper H0 exit_adj_rho0 x_neighbor_unique u_neighbor_unique w hw z hwz
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  obtain ⟨n, hn, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
  by_cases hn0 : n = 0
  · subst n
    have hwstart : w = Sum.inl x := by simpa using hn.symm
    have hz := x_neighbor_unique z (by simpa [hwstart] using hwz)
    simp [hz]
  by_cases hnend : n = exitPath.length
  · have hwend : w = Sum.inl u := by
      rw [← hn, hexitPath.getVert_eq_end_iff hnle]
      exact hnend
    have hz := u_neighbor_unique z (by simpa [hwend] using hwz)
    simp [hz]
  have hleft : H0.Adj (exitPath.getVert n)
      (exitPath.getVert (n - 1)) := by
    rw [← show n - 1 + 1 = n by omega]
    exact (exit_adj_rho0 (n - 1) (by omega)).symm
  have hright : H0.Adj (exitPath.getVert n)
      (exitPath.getVert (n + 1)) :=
    exit_adj_rho0 n (by omega)
  by_contra hznot
  have hwz' := hwz
  rw [← hn] at hwz'
  have hneleft : exitPath.getVert (n - 1) ≠ z := by
    intro he
    apply hznot
    rw [← he]
    exact exitPath.getVert_mem_support _
  have hneright : exitPath.getVert (n + 1) ≠ z := by
    intro he
    apply hznot
    rw [← he]
    exact exitPath.getVert_mem_support _
  have hnelr : exitPath.getVert (n - 1) ≠
      exitPath.getVert (n + 1) := by
    intro he
    have hindex := hexitPath.getVert_injOn
      (show n - 1 ≤ exitPath.length by omega)
      (show n + 1 ≤ exitPath.length by omega) he
    omega
  let : Fintype (H0.neighborSet (exitPath.getVert n)) :=
    Fintype.ofFinite _
  have hthree : 3 ≤ H0.degree (exitPath.getVert n) := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    let s : Finset (Sum V E) :=
      {z, exitPath.getVert (n - 1), exitPath.getVert (n + 1)}
    have hs : s ⊆ H0.neighborFinset (exitPath.getVert n) := by
      intro t ht
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · simpa [SimpleGraph.mem_neighborFinset] using hwz'
      · simpa [SimpleGraph.mem_neighborFinset] using hleft
      · simpa [SimpleGraph.mem_neighborFinset] using hright
    have hcard : 3 ≤ s.card := by
      simp [s, hnelr, hneleft.symm,
        hneright.symm]
    exact hcard.trans (Finset.card_le_card hs)
  have hupper : H0.degree (exitPath.getVert n) ≤ 2 := by
    simpa [H0] using TwoColorIncidenceDegreeAtMostTwo
      G rho0 gammaN beta hrho0Proper (exitPath.getVert n)
  omega

private theorem helper_branch_316.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn Tj seed TjPrime : TreeSequence G e0)
        (rho1 : PartialEdgeColoring E k) (gammaN deltaN beta : Fin k) (terminalSupport u x z : V)
        (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport) (Sum.inl
        x)) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl
        u)) (_ : TashkinovClosure rho1 seed TjPrime) (_ : gammaN ≠ deltaN) (_ : beta ≠ deltaN) (_
        : beta ∈ MissingColors G rho1 u) (_ : p.IsPath) (_ : {y : V ⊕ E | y ∈ p.support} =
        TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport)) (_ : x ∉
        TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) (_ : u ∈ TreeSequenceVertexSet
        TjPrime) (_ : exitPath.IsPath) (_ : (2 : ℕ) ≤ exitPath.length) (_ : (
    ∀ y ∈ exitPath.support, y ∈ p.support)) (_ : z ∈ TreeSequenceVertexSet Tj),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    ∀ (_ : IsProperEdgeColoring G rho0) (_ : (
    ∀ (f : E) (_ : TreeIncidentEdge TjPrime f), rho0 f = rho1 f)) (_ : beta ∈ MissingColors G rho0
        u) (g : E) (_ : Incident G u g) (_ : rho0 g = some gammaN),
    let H1 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho1 gammaN deltaN;
    let H0 : SimpleGraph (V ⊕ E) := TwoColorIncidenceGraph G rho0 gammaN beta;
    ∀ (_ : (
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)) (_ : q.IsPath) {e : E} (_ : Sum.inr e ∈
        q.support) (_ : Incident G b e), q.getVert (q.length - (1 : ℕ)) = Sum.inr e)) (_ :
        exitPath.getVert (exitPath.length - (1 : ℕ)) = Sum.inr g) (_ : (
    ∀ i < exitPath.length, H0.Adj (exitPath.getVert i) (exitPath.getVert (i + (1 : ℕ))))),
        TwoColorComponent G rho0 gammaN beta (Sum.inl u) ⊆ {y : V ⊕ E | y ∈ exitPath.support} := by
  classical
  intro V E _ _ _ G k e0 Tn Tj seed TjPrime rho1 gammaN deltaN beta terminalSupport u x z p
      exitPath hclosure hgammaDelta hbetaDelta hbeta hpath hcomponent hxOutside huPrime hexitPath
      hexitLength hexitSupport hz rho0 hrho0Proper hrho0Fixed hbetaRho0 g hug hgRho0 H1 H0
      path_incident_end_last hgLast exit_adj_rho0 y hy
  have hxPrime : x ∉ TreeSequenceVertexSet TjPrime := by
    intro hx
    exact hxOutside (Finset.mem_union.mpr (Or.inr hx))
  have new_x_adj_old : ∀ e : E, Incident G x e →
      (rho0 e = some gammaN ∨ rho0 e = some beta) →
        rho1 e = some gammaN ∨ rho1 e = some deltaN := by
    exact @helper_new_x_adj_old_317 V E inferInstance inferInstance G k e0 seed TjPrime rho1
        gammaN deltaN beta u x hclosure hgammaDelta hbetaDelta hbeta huPrime hrho0Fixed hxPrime
  have first_old_adj : H1.Adj (Sum.inl x) (exitPath.getVert 1) := by
    simpa [H1] using exitPath.adj_getVert_succ
      (show 0 < exitPath.length by omega)
  have first_p_last :
      p.getVert (p.length - 1) = exitPath.getVert 1 := by
    exact @helper_first_p_last_359 V E G k rho1 gammaN deltaN terminalSupport u x p exitPath
        hpath hexitSupport path_incident_end_last first_old_adj
  have old_x_neighbor_unique : ∀ z : Sum V E,
      H1.Adj (Sum.inl x) z → z = exitPath.getVert 1 := by
    exact @helper_old_x_neighbor_unique_376 V E G k e0 Tj rho1 gammaN deltaN terminalSupport u x
        z p exitPath hpath hcomponent hz path_incident_end_last first_p_last
  have x_neighbor_unique : ∀ z : Sum V E,
      H0.Adj (Sum.inl x) z → z = exitPath.getVert 1 := by
    exact @helper_x_neighbor_unique_407 V E inferInstance inferInstance G k e0 Tj TjPrime rho1
        gammaN deltaN beta u x z exitPath hz new_x_adj_old old_x_neighbor_unique
  have u_neighbor_unique :
    ∀ z : Sum V E, H0.Adj (Sum.inl u) z → z = exitPath.getVert (exitPath.length - 1) := by
    exact @helper_u_neighbor_unique_423 V E inferInstance inferInstance G k e0 Tj
        TjPrime rho1 gammaN deltaN beta u x z exitPath hz hrho0Proper hbetaRho0 g hug hgRho0 hgLast
  have support_closed : ∀ w : Sum V E, w ∈ exitPath.support →
      ∀ z : Sum V E, H0.Adj w z → z ∈ exitPath.support := by
    exact @helper_support_closed_448 V E inferInstance inferInstance
        G k e0 Tj TjPrime rho1 gammaN deltaN beta u x z exitPath hexitPath hexitLength hz
        hrho0Proper exit_adj_rho0 x_neighbor_unique u_neighbor_unique
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

private theorem helper_hcomponentExit_260.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn Tj seed TjPrime : TreeSequence G e0)
        (rho1 : PartialEdgeColoring E k) (_ gammaN deltaN beta : Fin k) (terminalSupport u x z :
        V) (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl terminalSupport)
        (Sum.inl x)) (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x)
        (Sum.inl u)) (_ : Fin (Tj.length + (1 : ℕ))) (_ : TashkinovClosure rho1 seed TjPrime) (_ :
        gammaN ≠ deltaN) (_ : beta ≠ deltaN) (_ : beta ∈ MissingColors G rho1 u) (_ : p.IsPath) (_
        : {y : V ⊕ E | y ∈ p.support} = TwoColorComponent G rho1 gammaN deltaN (Sum.inl
        terminalSupport)) (_ : x ∉ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) (_ :
        u ∈ TreeSequenceVertexSet TjPrime) (_ : exitPath.IsPath) (_ : (2 : ℕ) ≤ exitPath.length)
        (_ : (
    ∀ y ∈ exitPath.support, y ∈ p.support)) (_ : (
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, Sum.inl w ∈ exitPath.support ↔
        w = u)) (_ : z ∈ TreeSequenceVertexSet Tj),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    ∀ (_ : IsProperEdgeColoring G rho0) (_ : (
    ∀ (f : E) (_ : TreeIncidentEdge TjPrime f), rho0 f = rho1 f)) (_ : gammaN ≠ beta) (_ : beta ∈
        MissingColors G rho0 u) (g : E) (_ : Incident G u g) (_ : Sum.inr g ∈ exitPath.support) (_
        : rho1 g = some gammaN) (_ : rho0 g = some gammaN), {y : V ⊕ E | y ∈ exitPath.support} =
        TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
  classical
  intro V E _ _ _ G k e0 Tn Tj seed TjPrime rho1 gammaFirst gammaN deltaN beta terminalSupport u
      x z p exitPath zPosition hclosure hgammaDelta hbetaDelta hbeta hpath hcomponent hxOutside
      huPrime hexitPath hexitLength hexitSupport hexitIntersection hz rho0 hrho0Proper hrho0Fixed
      hgammaBeta hbetaRho0 g hug hgExit hgRho1 hgRho0
  let H1 := TwoColorIncidenceGraph G rho1 gammaN deltaN
  let H0 := TwoColorIncidenceGraph G rho0 gammaN beta
  have path_edge_data :
    ∀ {a b : V} (q : H1.Walk (Sum.inl a) (Sum.inl b)) (hq : q.IsPath) {e : E}, Sum.inr e ∈
        q.support →
    ∃ j : ℕ, 0 < j ∧ j < q.length ∧ q.getVert j = Sum.inr e ∧
    ∃ v w : V, q.getVert (j - 1) = Sum.inl v ∧ q.getVert (j + 1) = Sum.inl w ∧ v ≠ w ∧ G.ends e =
        s(v, w) := by
    exact @helper_path_edge_data_132 V E G k rho1 gammaN deltaN u x exitPath
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
    exact @helper_exit_edge_color_230 V E inferInstance inferInstance inferInstance G k e0 Tn
        TjPrime rho1 gammaN deltaN beta u x exitPath hgammaDelta hbetaDelta hexitPath
        hexitIntersection hrho0Fixed hgammaBeta g hgRho1 path_incident_vertex_mem
        path_incident_end_last hgLast
  have exit_adj_rho0 : ∀ i : ℕ, i < exitPath.length →
      H0.Adj (exitPath.getVert i) (exitPath.getVert (i + 1)) := by
    exact @helper_exit_adj_rho0_268 V E inferInstance inferInstance G k e0 TjPrime rho1 gammaN
        deltaN beta u x exitPath exit_edge_color
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
  · exact @helper_branch_316 V E inferInstance inferInstance inferInstance G k e0
      Tn Tj seed TjPrime rho1 gammaN deltaN beta terminalSupport u x z p exitPath hclosure
      hgammaDelta hbetaDelta hbeta hpath hcomponent hxOutside huPrime hexitPath hexitLength
      hexitSupport hz hrho0Proper hrho0Fixed hbetaRho0 g hug hgRho0 path_incident_end_last hgLast
      exit_adj_rho0
private theorem helper_htreeEdgeFixed_771.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] {G : LooplessMultigraph V E} {k : ℕ}
        {e0 : E} (Tj _ TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k) (_ gammaN
        deltaN beta : Fin k) (u x : V) (_ : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
        (Sum.inl x) (Sum.inl u)) (_ : Fin (Tj.length + (1 : ℕ))),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let rho3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
    ∀ (_ : (
    ∀ w ∈ TreeSequenceVertexSet TjPrime, w ≠ u →
    ∀ (f : E), Incident G w f → rho3 f = rho1 f)) (a : Fin TjPrime.length), rho3 (TjPrime.edge a)
        = rho1 (TjPrime.edge a) := by
  classical
  intro V E _ _ G k e0 Tj seed TjPrime rho1 gammaFirst gammaN deltaN beta u x exitPath zPosition
      rho0 rho3 hmuRho1PrimeFixed a
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
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

private theorem helper_component_edge_avoids_763.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] [DecidableEq V]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn TjPrime : TreeSequence G e0) (rho1 :
        PartialEdgeColoring E k) (gammaN deltaN beta : Fin k) (u : V),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    ∀ (_ : (
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, Sum.inl w ∈ TwoColorComponent
        G rho0 gammaN beta (Sum.inl u) ↔ w = u)),
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, w ≠ u →
    ∀ (f : E), Incident G w f → Sum.inr f ∉ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
  classical
  intro V E _ _ _ G k e0 Tn TjPrime rho1 gammaN deltaN beta u rho0 hcomponentIntersection w hw hwu f
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

private theorem helper_before_seed_817.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Finite V] {G :
    LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tj seed : TreeSequence G e0) (rho1 :
    PartialEdgeColoring E k) (_ gammaN deltaN : Fin k) (terminalSupport u x : V) (_ :
    (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk (Sum.inl x) (Sum.inl u)) (_ : Fin
    (Tj.length + (1 : ℕ))), TreeSequenceInitialSegment seed Tj → seed.vertex (Fin.last
    seed.length) = terminalSupport → ∀ (hterminalTj : terminalSupport ∈ TreeSequenceVertexSet
    Tj), ∀ w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj, w ∈ TreeSequenceVertexSet
    seed := by
  classical
  intro V E _ G k e0 Tj seed rho1 gammaFirst gammaN deltaN terminalSupport u x exitPath zPosition
      hseedJ hseedTerminal hterminalTj w hw
  let _ := Fintype.ofFinite V
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

private theorem helper_rho0_unaffected_871.{u_1, u_2} :
    open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] {G : LooplessMultigraph V E}
        {k : ℕ} {e0 : E} (TjPrime : TreeSequence G e0) (rho1 : PartialEdgeColoring E k)
        (deltaN beta : Fin k),
        let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
        ∀ (c : Fin k) (_ : c ≠ beta) (_ : c ≠ deltaN) (f : E),
          rho0 f = some c ↔ rho1 f = some c := by
  classical
  intro V E _ _ G k e0 TjPrime rho1 deltaN beta rho0 c hcb hcd f
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite E
  unfold rho0 OutsideTreeColorSwap
  by_cases ht : TreeIncidentEdge TjPrime f
  · simp [ht]
  · simp only [ite_eq_right ht]
    by_cases hfb : rho1 f = some beta
    · rw [ite_eq_left hfb]
      constructor
      · intro h
        exact False.elim (hcd (Option.some.inj h).symm)
      · intro h
        exact False.elim (hcb (Option.some.inj (h.symm.trans hfb)))
    · rw [ite_eq_right hfb]
      by_cases hfd : rho1 f = some deltaN
      · rw [ite_eq_left hfd]
        constructor
        · intro h
          exact False.elim (hcb (Option.some.inj h).symm)
        · intro h
          exact False.elim (hcd (Option.some.inj (h.symm.trans hfd)))
      · rw [ite_eq_right hfd]

private theorem helper_continuation_1155.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} (Tn Tj seed TjPrime : TreeSequence G e0)
        (phiJ rho1 : PartialEdgeColoring E k) (Dprev : Finset (Fin k)) (gammaFirst gammaN deltaN
        beta : Fin k) (terminalSupport u x z : V) (_ : (TwoColorIncidenceGraph G rho1 gammaN
        deltaN).Walk (Sum.inl x) (Sum.inl u)) (zPosition : Fin (Tj.length + (1 : ℕ))) (_ :
        gammaFirst = gammaN) (_ : TreeSequenceInitialSegment Tj Tn) (_ :
        TreeSequenceInitialSegment seed Tj) (_ : TreeSequenceInitialSegment seed TjPrime) (_ :
        seed.vertex (Fin.last seed.length) = terminalSupport) (hterminalTj : terminalSupport ∈
        TreeSequenceVertexSet Tj) (_ : TashkinovClosure rho1 seed TjPrime) (_ :
        ColoredVertexSetElementary G rho1 (TreeSequenceVertexSet TjPrime)) (_ : beta ≠ deltaN) (_
        : beta ∈ MissingColors G rho1 u) (_ : deltaN ∈ MissingColors G rho1 terminalSupport)
        (huPrime : u ∈ TreeSequenceVertexSet TjPrime) (_ : u ∉ TreeSequenceVertexSet Tn) (_ :
        StableColoringBeforeVertex Tj terminalSupport hterminalTj Dprev phiJ rho1) (_ : (
    ∀ v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport, MissingColors G rho1 v = MissingColors
        G phiJ v)) (_ : TashkinovAugmentationSequence phiJ seed Tj) (_ : (
    ∀ (a : Fin Tj.length) (_ : seed.length ≤ (↑a : ℕ)), rho1 (Tj.edge a) = phiJ (Tj.edge a))) (_ :
        deltaN ∉ TreeMissingColors phiJ Tj) (hz : z ∈ TreeSequenceVertexSet Tj) (_ : Tj.vertex
        zPosition = z) (_ : seed.length ≤ (↑zPosition : ℕ)) (_ : (
    ∀ w ∈ TreeVerticesBefore Tj z hz, beta ∉ MissingColors G rho1 w)) (_ : (
    ∀ (a : Fin Tj.length) (_ : seed.length ≤ (↑a : ℕ)) (_ : (↑a : ℕ) < (↑zPosition : ℕ)), rho1
        (Tj.edge a) ≠ some beta)) (_ : (
    ∀ {A B : TreeSequence G e0} (_ : TreeSequenceInitialSegment A B), TreeSequenceVertexSet A ⊆
        TreeSequenceVertexSet B)) (_ : terminalSupport ∈ TreeSequenceVertexSet TjPrime) (_ : u ∉
        TreeSequenceVertexSet seed),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let rho3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
    ∀ (_ : (
    ∀ (f : E) (_ : TreeIncidentEdge TjPrime f), rho0 f = rho1 f)) (_ : IsProperEdgeColoring G
        rho3) (_ : IsOneEdgeUncolored rho3 e0) (_ : gammaN ∈ MissingColors G rho3 u) (_ : (
    ∀ w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime, Sum.inl w ∈ TwoColorComponent
        G rho0 gammaN beta (Sum.inl u) ↔ w = u)),
    let rho0 : PartialEdgeColoring E k := OutsideTreeColorSwap TjPrime rho1 beta deltaN;
    let rho3 : PartialEdgeColoring E k := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u);
        IsProperEdgeColoring G rho3 ∧ IsOneEdgeUncolored rho3 e0 ∧ StableColoringBeforeVertex Tj
        terminalSupport hterminalTj Dprev phiJ rho3 ∧ ((
    ∀ v ∈ ((TreeVerticesBefore Tj z hz ∪ ({ z } : Finset V) ∪ (TreeVerticesBefore TjPrime u
        huPrime ∪ ({ u } : Finset V))).erase u).erase z, MissingColors G rho3 v = MissingColors G
        rho1 v) ∧ (
    ∀ (f : E), ((
    ∃ (a : Fin Tj.length), seed.length ≤ (↑a : ℕ) ∧ (↑a : ℕ) < (↑zPosition : ℕ) ∧ Tj.edge a = f) ∨
    ∃ (a : Fin TjPrime.length) (uPosition : Fin (TjPrime.length + (1 : ℕ))), TjPrime.vertex
        uPosition = u ∧ (↑a : ℕ) < (↑uPosition : ℕ) ∧ TjPrime.edge a = f) → rho3 f = rho1 f) ∧
        (beta ∈ MissingColors G rho1 z → deltaN ∈ MissingColors G rho3 z) ∧ (z ∈
        TreeVerticesBefore TjPrime u huPrime → MissingColors G rho3 z = MissingColors G rho1 z)) ∧
        gammaFirst ∈ MissingColors G rho3 u := by
  classical
  intro V E _ _ _ G k e0 Tn Tj seed TjPrime phiJ rho1 Dprev gammaFirst gammaN deltaN beta
      terminalSupport u x z exitPath zPosition hgammaFirst hTjN hseedJ hseedPrime hseedTerminal
      hterminalTj hclosure hprimeElementary hbetaDelta hbeta hdeltaMissing huPrime huOutside hb1
      hb2Missing haugmentation hb2Edges hdeltaPhiJ hz hzPosition hzAfter hzBefore hzEdges
      initial_subset hterminalPrime huSeed rho0 rho3 hrho0Fixed hrho3Proper hrho3One hgammaRho3
      hcomponentIntersection
  have component_edge_avoids :
    ∀ (w : V), w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime → w ≠ u →
    ∀ f : E, Incident G w f → Sum.inr f ∉ TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    exact @helper_component_edge_avoids_763 V E inferInstance inferInstance inferInstance G k e0
        Tn TjPrime rho1 gammaN deltaN beta u hcomponentIntersection
  have hmuRho0Fixed : ∀ (w : V),
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      w ≠ u → ∀ f : E, Incident G w f → rho3 f = rho0 f := by
    intro w hw hwu f hwf
    have hf := component_edge_avoids w hw hwu f hwf
    simp [rho3, TwoColorComponentSwap, hf]
  have hmuRho1PrimeFixed : ∀ (w : V),
      w ∈ TreeSequenceVertexSet TjPrime → w ≠ u →
      ∀ f : E, Incident G w f → rho3 f = rho1 f := by
    intro w hw hwu f hwf
    rw [hmuRho0Fixed w (Finset.mem_union.mpr (Or.inr hw)) hwu f hwf]
    exact hrho0Fixed f ⟨w, hw, hwf⟩
  have missing_eq_of_incident_eq : ∀ (w : V),
      (∀ f : E, Incident G w f → rho3 f = rho1 f) →
      MissingColors G rho3 w = MissingColors G rho1 w := by
    intro w hfixed
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
  have before_seed : ∀ w : V,
      w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj →
      w ∈ TreeSequenceVertexSet seed := by
    exact @helper_before_seed_817 V E inferInstance G k e0 Tj seed rho1 gammaFirst gammaN deltaN
        terminalSupport u x exitPath zPosition hseedJ hseedTerminal hterminalTj
  have before_prime : ∀ w : V,
      w ∈ TreeVerticesBefore Tj terminalSupport hterminalTj →
      w ∈ TreeSequenceVertexSet TjPrime := by
    intro w hw
    exact initial_subset hseedPrime (before_seed w hw)
  have hE1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ rho3 := by
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
  have hmissingPrime : ∀ w : V,
      w ∈ TreeSequenceVertexSet TjPrime → w ≠ u →
      MissingColors G rho3 w = MissingColors G rho1 w := by
    intro w hw hwu
    exact missing_eq_of_incident_eq w (hmuRho1PrimeFixed w hw hwu)
  have htreeEdgeFixed : ∀ a : Fin TjPrime.length,
      rho3 (TjPrime.edge a) = rho1 (TjPrime.edge a) := by
    exact @helper_htreeEdgeFixed_771 V E inferInstance inferInstance G k e0 Tj seed
        TjPrime rho1 gammaFirst gammaN deltaN beta u x exitPath zPosition hmuRho1PrimeFixed
  have rho0_unaffected : ∀ (c : Fin k), c ≠ beta → c ≠ deltaN →
      ∀ f : E, (rho0 f = some c ↔ rho1 f = some c) := by
    exact @helper_rho0_unaffected_871 V E inferInstance inferInstance G k e0 TjPrime rho1 deltaN
        beta
  have hE2 := P2966_T1_OutsideSwapPrefixEffects Tn Tj seed TjPrime
    phiJ rho1 rho0 rho3 deltaN beta terminalSupport u z zPosition
    hTjN hterminalPrime hclosure.2 hprimeElementary hbetaDelta hbeta
    hdeltaMissing hb2Missing haugmentation hb2Edges hdeltaPhiJ hz
    hzPosition hzAfter huPrime huOutside hzBefore hzEdges rfl hrho0Fixed hmuRho0Fixed
    hmissingPrime htreeEdgeFixed rho0_unaffected
  have hgammaFirstRho3 : gammaFirst ∈ MissingColors G rho3 u := by
    rw [hgammaFirst]
    exact hgammaRho3
  exact ⟨hrho3Proper, hrho3One, hE1, hE2, hgammaFirstRho3⟩

theorem ExtensionBaseClaim45Singleton {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (Tn Tj seed TjPrime : TreeSequence G e0)
    (phiJ rho1 : PartialEdgeColoring E k)
    (Dprev supportColors : Finset (Fin k))
    (gammaFirst gammaN deltaN beta : Fin k)
    (terminalSupport u x z : V)
    (p : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
      (Sum.inl terminalSupport) (Sum.inl x))
    (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk
      (Sum.inl x) (Sum.inl u))
    (zPosition : Fin (Tj.length + 1))
    (hgammaFirst : gammaFirst = gammaN)
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
    (hgammaDelta : gammaN ≠ deltaN)
    (hbetaGamma : beta ≠ gammaN)
    (hbetaDelta : beta ≠ deltaN)
    (hbeta : beta ∈ MissingColors G rho1 u)
    (hdeltaMissing : deltaN ∈ MissingColors G rho1 terminalSupport)
    (hpath : p.IsPath)
    (hcomponent : {y : Sum V E | y ∈ p.support} =
      TwoColorComponent G rho1 gammaN deltaN (Sum.inl terminalSupport))
    (hxOutside : x ∉
      TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime)
    (huPrime : u ∈ TreeSequenceVertexSet TjPrime)
    (huOutside : u ∉ TreeSequenceVertexSet Tn)
    (hexitPath : exitPath.IsPath)
    (hexitLength : 2 ≤ exitPath.length)
    (hexitSupport : ∀ y : Sum V E, y ∈ exitPath.support → y ∈ p.support)
    (hexitIntersection : ∀ w : V,
      w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime →
      (Sum.inl w ∈ exitPath.support ↔ w = u))
    (hexitBoundary : ∃ g ∈ BoundaryColorEdges G rho1
        (TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime) gammaN,
      Incident G u g ∧ Sum.inr g ∈ exitPath.support)
    (hb1 : StableColoringBeforeVertex Tj terminalSupport hterminalTj
      Dprev phiJ rho1)
    (hb2Missing : ∀ v : V,
      v ∈ (TreeSequenceVertexSet Tj).erase terminalSupport →
      MissingColors G rho1 v = MissingColors G phiJ v)
    (haugmentation : TashkinovAugmentationSequence phiJ seed Tj)
    (hb2Edges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      rho1 (Tj.edge a) = phiJ (Tj.edge a))
    (hdeltaPhiJ : deltaN ∉ TreeMissingColors phiJ Tj)
    (hz : z ∈ TreeSequenceVertexSet Tj)
    (hzPosition : Tj.vertex zPosition = z)
    (hzAfter : seed.length ≤ zPosition.val)
    (_ :
      (seed.length < zPosition.val ∧
          beta ∈ MissingColors G rho1 z ∧
          ∀ r : Fin (Tj.length + 1),
            seed.length < r.val → r.val < zPosition.val →
            beta ∉ MissingColors G rho1 (Tj.vertex r)) ∨
        (zPosition = Fin.last Tj.length ∧
          ∀ r : Fin (Tj.length + 1), seed.length < r.val →
            beta ∉ MissingColors G rho1 (Tj.vertex r)))
    (hzBefore : ∀ w ∈ TreeVerticesBefore Tj z hz,
      beta ∉ MissingColors G rho1 w)
    (hzEdges : ∀ a : Fin Tj.length, seed.length ≤ a.val →
      a.val < zPosition.val → rho1 (Tj.edge a) ≠ some beta) :
    let rho0 := OutsideTreeColorSwap TjPrime rho1 beta deltaN
    let rho3 := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
    IsProperEdgeColoring G rho3 ∧ IsOneEdgeUncolored rho3 e0 ∧
      StableColoringBeforeVertex Tj terminalSupport hterminalTj
        Dprev phiJ rho3 ∧
      ((∀ v : V,
        v ∈ (((TreeVerticesBefore Tj z hz ∪ {z}) ∪
            (TreeVerticesBefore TjPrime u huPrime ∪ {u})).erase u).erase z →
        MissingColors G rho3 v = MissingColors G rho1 v) ∧
        (∀ f : E,
          ((∃ a : Fin Tj.length,
              seed.length ≤ a.val ∧ a.val < zPosition.val ∧
                Tj.edge a = f) ∨
            (∃ (a : Fin TjPrime.length)
              (uPosition : Fin (TjPrime.length + 1)),
              TjPrime.vertex uPosition = u ∧ a.val < uPosition.val ∧
                TjPrime.edge a = f)) →
          rho3 f = rho1 f) ∧
        (beta ∈ MissingColors G rho1 z →
          deltaN ∈ MissingColors G rho3 z) ∧
        (z ∈ TreeVerticesBefore TjPrime u huPrime →
          MissingColors G rho3 z = MissingColors G rho1 z)) ∧
      gammaFirst ∈ MissingColors G rho3 u := by
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
  have hterminalPrime : terminalSupport ∈ TreeSequenceVertexSet TjPrime :=
    initial_subset hseedPrime hterminalSeed
  have huSeed : u ∉ TreeSequenceVertexSet seed := by
    intro hu
    exact huOutside (initial_subset hTjN (initial_subset hseedJ hu))
  let rho0 := OutsideTreeColorSwap TjPrime rho1 beta deltaN
  let rho3 := TwoColorComponentSwap G rho0 gammaN beta (Sum.inl u)
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
  have hrho3Proper : IsProperEdgeColoring G rho3 :=
    TwoColorComponentSwapProper G rho0 gammaN beta hgammaBeta
      hrho0Proper (Sum.inl u)
  have hrho3One : IsOneEdgeUncolored rho3 e0 := by
    unfold IsOneEdgeUncolored at hrho0One ⊢
    constructor
    · simp [rho3, TwoColorComponentSwap, hrho0One.1]
    · intro f hfe
      obtain ⟨c, hc⟩ := hrho0One.2 f hfe
      have hne : rho3 f ≠ none := by
        by_cases hK : Sum.inr f ∈
            TwoColorComponent G rho0 gammaN beta (Sum.inl u)
        · by_cases hcg : c = gammaN
          · simp [rho3, TwoColorComponentSwap, hK, hc, hcg]
          · by_cases hcb : c = beta
            · simp [rho3, TwoColorComponentSwap, hK, hc, hcb,
                hbetaGamma]
            · simp [rho3, TwoColorComponentSwap, hK, hc, hcg, hcb]
        · simp [rho3, TwoColorComponentSwap, hK, hc]
      obtain ⟨d, hd⟩ := Option.ne_none_iff_exists.mp hne
      exact ⟨d, hd.symm⟩
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
  have hgRho3 : rho3 g = some beta := by
    simp [rho3, TwoColorComponentSwap, hgComponent, hgRho0]
  have hbetaRho3 : beta ∉ MissingColors G rho3 u := by
    intro hb
    have hbPresent : beta ∉ PresentColors G rho3 u := by
      simpa [MissingColors] using hb
    apply hbPresent
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨g, hug, hgRho3⟩
  have hgammaRho3 : gammaN ∈ MissingColors G rho3 u := by
    exact @helper_hgammaRho3_224 V E inferInstance inferInstance G k e0 TjPrime rho1 gammaN
        deltaN beta u hbetaGamma hgammaBeta hbetaRho0
  have hcomponentExit :
      {y : Sum V E | y ∈ exitPath.support} =
        TwoColorComponent G rho0 gammaN beta (Sum.inl u) := by
    exact @helper_hcomponentExit_260 V E inferInstance inferInstance inferInstance
        G k e0 Tn Tj seed TjPrime rho1 gammaFirst gammaN deltaN beta terminalSupport u x z p
        exitPath zPosition hclosure hgammaDelta hbetaDelta hbeta hpath hcomponent hxOutside
        huPrime hexitPath hexitLength hexitSupport hexitIntersection hz hrho0Proper hrho0Fixed
        hgammaBeta hbetaRho0 g hug hgExit hgRho1 hgRho0
  have hcomponentIntersection :
    ∀ w : V, w ∈ TreeSequenceVertexSet Tn ∪ TreeSequenceVertexSet TjPrime → (Sum.inl w ∈
        TwoColorComponent G rho0 gammaN beta (Sum.inl u) ↔ w = u) := by
    intro w hw
    rw [← hcomponentExit]
    exact hexitIntersection w hw
  exact @helper_continuation_1155 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@Tn) (@Tj) (@seed) (@TjPrime) (@phiJ) (@rho1) (@Dprev) (@gammaFirst) (@gammaN)
      (@deltaN) (@beta) (@terminalSupport) (@u) (@x) (@z) (@exitPath) (@zPosition) (@hgammaFirst)
      (@hTjN) (@hseedJ) (@hseedPrime) (@hseedTerminal) (@hterminalTj) (@hclosure)
      (@hprimeElementary) (@hbetaDelta) (@hbeta) (@hdeltaMissing) (@huPrime) (@huOutside) (@hb1)
      (@hb2Missing) (@haugmentation) (@hb2Edges) (@hdeltaPhiJ) (@hz) (@hzPosition) (@hzAfter)
      (@hzBefore) (@hzEdges) (@initial_subset) (@hterminalPrime) (@huSeed) (@hrho0Fixed)
      (@hrho3Proper) (@hrho3One) (@hgammaRho3) (@hcomponentIntersection)
end GoldbergSeymour

end
