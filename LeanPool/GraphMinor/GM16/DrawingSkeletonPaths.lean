/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section3
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.Section6

/-!
# Paths of a drawing and its hypergraph skeleton

Menger's theorem is stated for the skeleton of a hypergraph. A drawing
has the same finite hypergraph whether it is first viewed as a graph
or directly as a hypergraph. A skeleton path therefore traces a path
subdrawing with exactly the same vertices.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM11
universe w
variable {S : Type w} [TopologicalSpace S]

/-- The graph and hypergraph associated to a drawing have the same
incidence relation. -/
theorem drawing_ofGraph_toGraph (H : Drawing S) :
    Hypergraph.ofGraph H.toGraph H.finite_V H.finite_edges = H.toHypergraph := by
  refine Hypergraph.ext (x := Hypergraph.ofGraph H.toGraph H.finite_V H.finite_edges)
    (y := H.toHypergraph) rfl rfl ?_
  funext e x
  apply propext
  change (∃ y, e ∈ H.E ∧ x ∈ H.V ∧ y ∈ H.V ∧ closure e ∩ H.V = {x, y}) ↔
    e ∈ H.E ∧ x ∈ H.V ∧ x ∈ closure e
  constructor
  · rintro ⟨y, he, hx, _, hcap⟩
    exact ⟨he, hx, (hcap.symm ▸ (show x ∈ ({x, y} : Set S) from Or.inl rfl)).1⟩
  · rintro ⟨he, hx, hxc⟩
    obtain ⟨u, v, hl⟩ := H.toGraph.exists_isLink_of_mem_edgeSet he
    have hxEnds : x ∈ ({u, v} : Set S) := hl.2.2.2 ▸ ⟨hxc, hx⟩
    rcases hxEnds with rfl | hxv
    · exact ⟨v, hl⟩
    · rw [mem_singleton_iff] at hxv
      subst x
      exact ⟨u, hl.symm⟩

/-- A skeleton path of a drawing lifts to a path subdrawing with
exactly the same vertices. This is used for Menger in XVI (8.1). -/
theorem drawing_path_of_skeleton_path [T1Space S] {H : Drawing S} {a b : S}
    (ha : a ∈ H.V) (w : H.toHypergraph.skeleton.Walk a b) (hw : w.IsPath) :
    ∃ P : Drawing S, P.IsPathBetween a b ∧ P.IsSubdrawing H ∧ P.V = {x | x ∈ w.support} := by
  have hEq := drawing_ofGraph_toGraph H
  have hLift : ∀ (J : Hypergraph S (Set S)),
      J = Hypergraph.ofGraph H.toGraph H.finite_V H.finite_edges →
      ∀ w : J.skeleton.Walk a b, ∃ W : GraphWalk H.toGraph a b, W.support = w.support := by
    intro J hJ w
    subst J
    exact exists_graphWalk_of_skeleton_walk H.finite_V H.finite_edges ha w
  obtain ⟨W, hSupport⟩ := hLift H.toHypergraph hEq.symm w
  have hSupport' : W.support = w.support := hSupport
  have hSimple : W.IsSimple := by
    change W.support.Nodup
    rw [hSupport']
    exact hw.support_nodup
  refine ⟨walkDrawing H W, walkDrawing_isPathBetween H hSimple, walkDrawing_isSubdrawing H W, ?_⟩
  rw [walkDrawing_V, hSupport']

end GraphMinor.GM16
