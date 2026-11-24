/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section5Packing
import LeanPool.GraphMinor.GM16.Section5Minimal
import LeanPool.GraphMinor.GM09.Section3c
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# Graph Minors XVI (5.3)

Choose a minimal forest that keeps the connections between marked
vertices. Apply the subtree packing argument to it. The paths in this
forest lift to paths in the original graph with the same vertices, so
both the packing and the fan give the alternatives in (5.3).
-/

public section
namespace GraphMinor.GM16

open Set Graph SimpleGraph GraphMinor.Surface GraphMinor.GM09
universe u v

/-- Lift a path in a forest on the vertices of a graph back to that
graph. The set of vertices is exactly the image of the path support. -/
theorem exists_graph_path_of_vertex_forest_path
    {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite)
    {F : SimpleGraph V(G)}
    (hF : F ≤ (Hypergraph.ofGraph G hV hE).skeleton.induce V(G))
    {a b : V(G)} (p : F.Path a b) :
    ∃ R : Graph α β, IsGraphPathWithEnds G R a.val b.val ∧
      V(R) = Subtype.val '' {z | z ∈ p.val.support} := by
  let f : F →g (Hypergraph.ofGraph G hV hE).skeleton :=
    ⟨Subtype.val, fun h => hF h⟩
  have hp : (p.val.map f).IsPath := p.isPath.map Subtype.val_injective
  obtain ⟨R, hR, hverts⟩ := exists_isGraphPathWithEnds_of_skeleton_isPath
    hV hE a.property (p.val.map f) hp
  have hsupp : (p.val.map f).support = p.val.support.map Subtype.val :=
    SimpleGraph.Walk.support_map f p.val
  refine ⟨R, hR, ?_⟩
  rw [hverts, hsupp]
  ext z
  exact List.mem_map

/-- **Graph Minors XVI, (5.3)** (page 56). A minimal forest preserving
the connections between marked vertices gives the subtree packing and
covering alternative. If the packing is too small, first-hit paths to
the cover and the paper's pigeonhole count give the required fan. -/
theorem theorem_5_3_proof : GM16Theorem53Statement.{u, v} := by
  classical
  intro α β G Y μ τ hV hE hYG hcomp hcount
  let U := V(G)
  let : Finite U := hV.to_subtype
  let K := (Hypergraph.ofGraph G hV hE).skeleton.induce V(G)
  let Y₀ : Set U := {y | y.val ∈ Y}
  have hYcard : Y₀.ncard = Y.ncard := by
    apply Set.ncard_congr (fun y _ => y.val)
    · intro y hy
      exact hy
    · intro a b _ _ hab
      exact Subtype.ext hab
    · intro y hy
      exact ⟨⟨y, hYG hy⟩, hy, rfl⟩
  have hKcomp : ∀ y ∈ Y₀, ∃ z ∈ Y₀, z ≠ y ∧ K.Reachable y z := by
    intro y hy
    obtain ⟨z, hz, hzy, hreach⟩ := hcomp y.val hy
    obtain ⟨w⟩ := skeleton_reachable_of_reflTransGen_adj hV hE hreach
    obtain ⟨W, hW⟩ := exists_graphWalk_of_skeleton_walk hV hE y.property w
    have hsupp : ∀ x ∈ w.support, x ∈ V(G) := by
      intro x hx
      apply W.mem_vertexSet_of_mem_support
      rwa [hW]
    refine ⟨⟨z, hYG hz⟩, hz, ?_, ⟨w.induce V(G) hsupp⟩⟩
    exact fun h => hzy (congrArg Subtype.val h)
  obtain ⟨F, hFK, hF, hconn⟩ := exists_minimal_marked_forest K Y₀
  have hFcomp : ∀ y ∈ Y₀, ∃ z ∈ Y₀, z ≠ y ∧ F.Reachable y z := by
    intro y hy
    obtain ⟨z, hz, hzy, hr⟩ := hKcomp y hy
    exact ⟨z, hz, hzy, hconn y hy z hz hr⟩
  have hnum : τ * (μ - 1) < Y₀.ncard := hYcard.symm ▸ hcount
  rcases forest_marked_paths_or_fan F Y₀ μ τ hF hFcomp hnum with
    ⟨Q, hQdisj⟩ | ⟨x, s, P, hs, hPinter, hPmarked⟩
  · have hlift := fun i => exists_graph_path_of_vertex_forest_path G hV hE hFK (Q i).path
    choose R hR hverts using hlift
    refine Or.inl ⟨R, fun i => (Q i).start.val, fun i => (Q i).finish.val, ?_, ?_⟩
    · intro i j hij
      apply Set.disjoint_left.mpr
      intro z hzi hzj
      rw [hverts i] at hzi
      rw [hverts j] at hzj
      obtain ⟨a, ha, rfl⟩ := hzi
      obtain ⟨b, hb, hba⟩ := hzj
      have hba' : b = a := Subtype.ext hba
      exact (Set.disjoint_left.mp (hQdisj hij)) ha (hba' ▸ hb)
    · intro i
      refine ⟨(Q i).start_mem, (Q i).finish_mem,
        fun h => (Q i).ne (Subtype.ext h), hR i, Set.Subset.antisymm ?_ ?_⟩
      · rintro z ⟨hzR, hzY⟩
        rw [hverts i] at hzR
        obtain ⟨a, ha, rfl⟩ := hzR
        rcases (Q i).marked a ha hzY with h | h
        · exact Or.inl (congrArg Subtype.val h)
        · exact Or.inr (mem_singleton_iff.mpr (congrArg Subtype.val h))
      · rintro z (rfl | hz)
        · exact ⟨IsGraphPathWithEnds.left_mem (hR i), (Q i).start_mem⟩
        · have hz' := mem_singleton_iff.mp hz
          subst z
          exact ⟨IsGraphPathWithEnds.right_mem (hR i), (Q i).finish_mem⟩
  · have hlift := fun i => exists_graph_path_of_vertex_forest_path G hV hE hFK (P i)
    choose R hR hverts using hlift
    have hinter : ∀ i j, i ≠ j → V(R i) ∩ V(R j) = {x.val} := by
      intro i j hij
      apply Set.Subset.antisymm
      · rintro z ⟨hzi, hzj⟩
        rw [hverts i] at hzi
        rw [hverts j] at hzj
        obtain ⟨a, ha, rfl⟩ := hzi
        obtain ⟨b, hb, hba⟩ := hzj
        have hba' : b = a := Subtype.ext hba
        have hai : a ∈ ({x} : Set U) := hPinter i j hij ▸ ⟨ha, hba' ▸ hb⟩
        exact mem_singleton_iff.mpr (congrArg Subtype.val (mem_singleton_iff.mp hai))
      · rintro z rfl
        exact ⟨IsGraphPathWithEnds.right_mem (hR i), IsGraphPathWithEnds.right_mem (hR j)⟩
    refine Or.inr ⟨x.val, R, fun i => (s i).val, x.property, ?_, ?_⟩
    · intro i j hij
      refine ⟨hinter i j hij, ?_⟩
      apply disjoint_edgeSet_of_inter_singleton (hR i) (IsGraphPathWithEnds.le (hR j))
      exact (hinter i j hij).subset
    · intro i
      refine ⟨(hPmarked i).1, fun h => (hPmarked i).2.1 (Subtype.ext h),
        IsGraphPathWithEnds.symm (hR i), ?_⟩
      rintro z ⟨hzR, hzY⟩
      rw [hverts i] at hzR
      obtain ⟨a, ha, rfl⟩ := hzR
      rcases (hPmarked i).2.2 a ha hzY with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (mem_singleton_iff.mpr (congrArg Subtype.val h))

end GraphMinor.GM16
