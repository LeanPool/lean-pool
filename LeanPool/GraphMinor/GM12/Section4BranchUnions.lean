/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# Joining path pieces to a connected branch

XII (4.4), page 252, adds shortened external paths to a connected
subdrawing. Each added path meets that subdrawing at its assigned
endpoint. Carry a walk from each point of a path to that endpoint,
and then through the original branch. This proves connectivity of
the whole finite union. The graph-path lemmas below supply the
same connectivity for each shortened path.
-/

public section

namespace GraphMinor.GM12

open Set Surface Hypergraph GM10 GM09

/-- A graph walk gives reachability in the associated hypergraph's
skeleton, including when a walk step is a loop. -/
theorem graphWalk_skeleton_reachable
    {α β : Type*} {G : Graph α β} (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    {x y : α} (W : GraphWalk G x y) :
    (Hypergraph.ofGraph G hV hE).skeleton.Reachable x y := by
  induction W with
  | nil => exact .refl _
  | @cons x z y e hl W ih =>
    by_cases hxz : x = z
    · subst z
      exact ih
    · have hadj : (Hypergraph.ofGraph G hV hE).skeleton.Adj x z :=
        ⟨hxz, e, hl.inc_left, hl.inc_right⟩
      exact hadj.reachable.trans ih

/-- A finite graph traced by a path is connected as a hypergraph. -/
theorem isConnectedSub_of_graph_path
    {α β : Type*} {G P : Graph α β} (hV : P.vertexSet.Finite) (hE : P.edgeSet.Finite)
    {a b : α} (hP : IsGraphPathWithEnds G P a b) :
    IsConnectedSub (Hypergraph.ofGraph P hV hE) := by
  obtain ⟨_, W, _, hWV, _⟩ := hP
  intro x hx y hy
  have hxW : x ∈ W.support := by change x ∈ P.vertexSet at hx; rw [hWV] at hx; exact hx
  have hyW : y ∈ W.support := by change y ∈ P.vertexSet at hy; rw [hWV] at hy; exact hy
  obtain ⟨Px, _, _⟩ := W.exists_append_of_mem hxW
  obtain ⟨Py, _, _⟩ := W.exists_append_of_mem hyW
  exact graphWalk_skeleton_reachable hV hE (Px.reverse.append Py)

/-- Adding finitely many connected pieces, each meeting a fixed
nonempty connected branch, preserves connectivity. -/
theorem isConnectedSub_union_biUnion
    {α β ι : Type*} (A : Hypergraph α β) (B : ι → Hypergraph α β) (F : Finset ι)
    (hne : A.vertexSet.Nonempty) (hA : IsConnectedSub A)
    (hB : ∀ i ∈ F, IsConnectedSub (B i))
    (hmeet : ∀ i ∈ F, (A.vertexSet ∩ (B i).vertexSet).Nonempty) :
    IsConnectedSub (A ∪ Hypergraph.biUnion F B) := by
  let U := A ∪ Hypergraph.biUnion F B
  have hmonoA : A.skeleton ≤ U.skeleton := by
    intro x y hxy
    obtain ⟨hne, e, hex, hey⟩ := hxy
    exact ⟨hne, e, Or.inl hex, Or.inl hey⟩
  have hmonoB : ∀ i ∈ F, (B i).skeleton ≤ U.skeleton := by
    intro i hi x y hxy
    obtain ⟨hne, e, hex, hey⟩ := hxy
    exact ⟨hne, e, Or.inr ⟨i, hi, hex⟩, Or.inr ⟨i, hi, hey⟩⟩
  obtain ⟨c, hc⟩ := hne
  have hreach : ∀ x ∈ U.vertexSet, U.skeleton.Reachable x c := by
    intro x hx
    rcases hx with hxA | hxB
    · exact SimpleGraph.Reachable.mono hmonoA (hA x hxA c hc)
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxB
      obtain ⟨z, hzA, hzB⟩ := hmeet i hi
      exact (SimpleGraph.Reachable.mono (hmonoB i hi) (hB i hi x hxi z hzB)).trans
        (SimpleGraph.Reachable.mono hmonoA (hA z hzA c hc))
  intro x hx y hy
  exact (hreach x hx).trans (hreach y hy).symm

end GraphMinor.GM12
