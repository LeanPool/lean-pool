/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.DegreeTwoPaths
public import LeanPool.GoldbergSeymour.TwoColorComponent

/-!
# Incidence paths and component endpoints

General facts extracted from the credited Trellis proof families at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12.
-/

@[expose] public section

namespace GoldbergSeymour

/-- An edge on an incidence path lies between its two distinct endpoints. -/
theorem incidencePathEdgeEndpoints {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ}
    {rho : PartialEdgeColoring E k} {alpha beta : Fin k} {a b : V}
    (q : (TwoColorIncidenceGraph G rho alpha beta).Walk (Sum.inl a) (Sum.inl b))
    (hq : q.IsPath) {e : E} (he : Sum.inr e ∈ q.support) :
    ∃ j : ℕ, 0 < j ∧ j < q.length ∧ q.getVert j = Sum.inr e ∧
      ∃ v w : V, q.getVert (j - 1) = Sum.inl v ∧ q.getVert (j + 1) = Sum.inl w ∧
        v ≠ w ∧ G.ends e = s(v, w) := by
  classical
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
        exact False.elim (by simp [TwoColorIncidenceGraph] at hprev)
  obtain ⟨w, hw⟩ : ∃ w : V, q.getVert (j + 1) = Sum.inl w := by
    cases hc : q.getVert (j + 1) with
    | inl w => exact ⟨w, rfl⟩
    | inr f =>
        rw [hc] at hnext
        exact False.elim (by simp [TwoColorIncidenceGraph] at hnext)
  have hve : Incident G v e := by
    rw [hv] at hprev
    change Incident G v e ∧
      (rho e = some alpha ∨ rho e = some beta) at hprev
    exact hprev.1
  have hwe : Incident G w e := by
    rw [hw] at hnext
    change Incident G w e ∧
      (rho e = some alpha ∨ rho e = some beta) at hnext
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

/-- Both endpoints of an edge on an incidence path belong to the path. -/
theorem incidencePathIncidentVertexMem {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ}
    {rho : PartialEdgeColoring E k} {alpha beta : Fin k} {a b : V}
    (q : (TwoColorIncidenceGraph G rho alpha beta).Walk (Sum.inl a) (Sum.inl b))
    (hq : q.IsPath) {e : E} (he : Sum.inr e ∈ q.support) {w : V} (hwe : Incident G w e) :
    Sum.inl w ∈ q.support := by
  obtain ⟨j, hjpos, hjlt, hj, v, t, hv, ht, hvt, hends⟩ :=
    incidencePathEdgeEndpoints q hq he
  have hwends : w ∈ s(v, t) := by
    rw [← hends]
    exact hwe
  simp only [Sym2.mem_iff] at hwends
  apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
  rcases hwends with hwv | hwt
  · exact ⟨j - 1, by simpa [hwv] using hv, by omega⟩
  · exact ⟨j + 1, by simpa [hwt] using ht, by omega⟩

/-- An edge incident to the final vertex of an incidence path is its last edge. -/
theorem incidencePathIncidentEndLast {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ}
    {rho : PartialEdgeColoring E k} {alpha beta : Fin k} {a b : V}
    (q : (TwoColorIncidenceGraph G rho alpha beta).Walk (Sum.inl a) (Sum.inl b))
    (hq : q.IsPath) {e : E} (he : Sum.inr e ∈ q.support) (hbe : Incident G b e) :
    q.getVert (q.length - 1) = Sum.inr e := by
  obtain ⟨j, hjpos, hjlt, hj, v, w, hv, hw, hvw, hends⟩ :=
    incidencePathEdgeEndpoints q hq he
  have hbends : b ∈ s(v, w) := by
    rw [← hends]
    exact hbe
  simp only [Sym2.mem_iff] at hbends
  rcases hbends with hbv | hbw
  · have hindex := hq.getVert_injOn
        (show j - 1 ≤ q.length by omega) (show q.length ≤ q.length by rfl)
        (by rw [hv, q.getVert_length, hbv])
    omega
  · have hindex := hq.getVert_injOn
        (show j + 1 ≤ q.length by omega) (show q.length ≤ q.length by rfl)
        (by rw [hw, q.getVert_length, hbw])
    have hjlast : j = q.length - 1 := by omega
    simpa [hjlast] using hj

/-- A walk contained in a path and starting at its end begins with the path's last edge. -/
theorem incidenceSubpathFirstEqLast {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ}
    {rho : PartialEdgeColoring E k} {alpha beta : Fin k} {a x u : V}
    (p : (TwoColorIncidenceGraph G rho alpha beta).Walk (Sum.inl a) (Sum.inl x))
    (q : (TwoColorIncidenceGraph G rho alpha beta).Walk (Sum.inl x) (Sum.inl u))
    (hpath : p.IsPath) (contained : ∀ y ∈ q.support, y ∈ p.support)
    (positive : 0 < q.length) : p.getVert (p.length - 1) = q.getVert 1 := by
  have adjacent : (TwoColorIncidenceGraph G rho alpha beta).Adj (Sum.inl x) (q.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero, zero_add] using q.adj_getVert_succ positive
  cases first : q.getVert 1 with
  | inl v =>
    rw [first] at adjacent
    exact False.elim adjacent
  | inr e =>
    have onPath : Sum.inr e ∈ p.support :=
      contained _ (by simpa [first] using q.getVert_mem_support 1)
    have incident : Incident G x e := by
      rw [first] at adjacent
      exact adjacent.1
    exact incidencePathIncidentEndLast p hpath onPath incident

/-- Recoloring all path edges into a second color pair preserves successive adjacency. -/
theorem incidenceWalkAdjacentOfEdgeColors {V E : Type*} {G : LooplessMultigraph V E} {k : ℕ}
    {rho1 rho0 : PartialEdgeColoring E k} {gammaN deltaN beta : Fin k} {a b : Sum V E}
    (exitPath : (TwoColorIncidenceGraph G rho1 gammaN deltaN).Walk a b)
    (exit_edge_color : ∀ e : E, Sum.inr e ∈ exitPath.support →
      (rho1 e = some gammaN ∨ rho1 e = some deltaN) →
        rho0 e = some gammaN ∨ rho0 e = some beta) (i : ℕ) (hi : i < exitPath.length) :
    (TwoColorIncidenceGraph G rho0 gammaN beta).Adj
      (exitPath.getVert i) (exitPath.getVert (i + 1)) := by
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

/-- Every neighbor of the end of a full component path is its last edge. -/
theorem incidenceComponentPathEndNeighbor {V E : Type*} {G : LooplessMultigraph V E}
    {k : ℕ} {rho : PartialEdgeColoring E k} {alpha beta : Fin k} {a b : V}
    (p : (TwoColorIncidenceGraph G rho alpha beta).Walk (Sum.inl a) (Sum.inl b))
    (hpath : p.IsPath)
    (hcomponent : {y | y ∈ p.support} = TwoColorComponent G rho alpha beta (Sum.inl a))
    {z : Sum V E} (hadj : (TwoColorIncidenceGraph G rho alpha beta).Adj (Sum.inl b) z) :
    z = p.getVert (p.length - 1) := by
  cases z with
  | inl v => exact False.elim hadj
  | inr e =>
    have heComponent : Sum.inr e ∈ TwoColorComponent G rho alpha beta (Sum.inl a) := by
      have hxComponent : Sum.inl b ∈ TwoColorComponent G rho alpha beta (Sum.inl a) := by
        rw [← hcomponent]
        exact p.end_mem_support
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans
        hxComponent
    have heP : Sum.inr e ∈ p.support := by
      change Sum.inr e ∈ {y | y ∈ p.support}
      rw [hcomponent]
      exact heComponent
    exact (incidencePathIncidentEndLast p hpath heP hadj.1).symm

/-- A path with unique endpoint neighbors fills its component in a degree-two graph. -/
theorem degreeTwoPathSupportEqComponent {W : Type*} [Finite W]
    {source target : SimpleGraph W} {a b : W} (p : source.Walk a b) (hpath : p.IsPath)
    (degreeBound : ∀ v, @SimpleGraph.degree W target v (Fintype.ofFinite _) ≤ 2)
    (adjacent : ∀ i < p.length, target.Adj (p.getVert i) (p.getVert (i + 1)))
    (startUnique : ∀ z, target.Adj a z → z = p.getVert 1)
    (endUnique : ∀ z, target.Adj b z → z = p.getVert (p.length - 1)) :
    {y | y ∈ p.support} = {y | target.connectedComponentMk y = target.connectedComponentMk b} := by
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨i, hi, hile⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hy
    have htoStart : ∀ j : ℕ, j ≤ p.length →
        target.connectedComponentMk (p.getVert j) = target.connectedComponentMk (p.getVert 0) := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ih =>
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (adjacent j (by omega))).symm.trans (ih (by omega))
    change target.connectedComponentMk y = target.connectedComponentMk b
    simpa only [hi, p.getVert_length] using
      (htoStart i hile).trans (htoStart p.length le_rfl).symm
  · intro y hy
    have reach : target.Reachable b y :=
      (SimpleGraph.ConnectedComponent.eq.mp hy).symm
    apply reach.mem_subgraphVerts
      (H := (⊤ : target.Subgraph).induce {w | w ∈ p.support})
      (fun w hw z hadj => ⟨by simpa using hw,
        degreeTwoPathSupportClosed p hpath degreeBound adjacent startUnique endUnique
          w (by simpa using hw) z hadj, hadj⟩)
      (by simp)

end GoldbergSeymour

end
