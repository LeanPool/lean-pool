/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetClosed

public import LeanPool.GoldbergSeymour.TwoColorComponent

/-!
# Closed Set Two Color Component Avoidance

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ClosedSetTwoColorComponentAvoidance {V E : Type*}
    [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : ℕ} (phi : PartialEdgeColoring E k)
    (alpha beta : Fin k) (X : Finset V) (u a b : V)
    (hclosed : ColoredVertexSetClosed G phi X)
    (hu : u ∉ X) (haX : a ∈ X) (hbX : b ∈ X)
    (ha : alpha ∈ MissingColors G phi a)
    (hb : beta ∈ MissingColors G phi b) :
    (∀ v ∈ X, Sum.inl v ∉
        TwoColorComponent G phi alpha beta (Sum.inl u)) ∧
      (∀ e : E, (∃ v ∈ X, Incident G v e) → Sum.inr e ∉
        TwoColorComponent G phi alpha beta (Sum.inl u)) := by
  classical
  let H := TwoColorIncidenceGraph G phi alpha beta
  let K := TwoColorComponent G phi alpha beta (Sum.inl u)
  let Outside : Sum V E → Prop
    | Sum.inl v => v ∉ X
    | Sum.inr e => ∀ v ∈ X, ¬ Incident G v e
  have boundary_of_crossing {e : E} {v w : V}
      (hv : v ∈ X) (hw : w ∉ X)
      (hve : Incident G v e) (hwe : Incident G w e) :
      e ∈ BoundaryEdges G X := by
    have hvw : v ≠ w := by
      intro h
      exact hw (h ▸ hv)
    have hends : G.ends e = s(v, w) := by
      exact (Sym2.mem_and_mem_iff hvw).mp ⟨hve, hwe⟩
    unfold BoundaryEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hv, w, hw, hends⟩
  have step {z z' : Sum V E} (hzz' : H.Adj z z')
      (hz : Outside z) : Outside z' := by
    cases z with
    | inl v =>
        cases z' with
        | inl w => simp [H, TwoColorIncidenceGraph] at hzz'
        | inr e =>
            simp only [H, TwoColorIncidenceGraph] at hzz'
            intro w hwX hwe
            have hboundary : e ∈ BoundaryEdges G X :=
              boundary_of_crossing hwX hz hwe hzz'.1
            rcases hzz'.2 with healpha | hebeta
            · exact (hclosed hboundary haX healpha) ha
            · exact (hclosed hboundary hbX hebeta) hb
    | inr e =>
        cases z' with
        | inl v =>
            simp only [H, TwoColorIncidenceGraph] at hzz'
            intro hvX
            exact hz v hvX hzz'.1
        | inr f => simp [H, TwoColorIncidenceGraph] at hzz'
  have component_outside : ∀ z, z ∈ K → Outside z := by
    intro z hz
    have hreach : H.Reachable (Sum.inl u) z := by
      apply SimpleGraph.ConnectedComponent.exact
      change H.connectedComponentMk z = H.connectedComponentMk (Sum.inl u) at hz
      exact hz.symm
    clear hz
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    induction hreach with
    | refl => exact hu
    | tail hreach hlast ih => exact step hlast ih
  constructor
  · intro v hvX hvK
    exact (component_outside (Sum.inl v) hvK) hvX
  · intro e heX heK
    obtain ⟨v, hvX, hve⟩ := heX
    exact (component_outside (Sum.inr e) heK) v hvX hve

end GoldbergSeymour

end
