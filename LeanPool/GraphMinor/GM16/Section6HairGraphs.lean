/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section6
import LeanPool.GraphMinor.GM16.Section5Degree
import LeanPool.GraphMinor.GM16.Section5Connections
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# The truncated hair paths in XVI (6.3)

Deleting the far end of a path leaves a connected graph containing its
near end. The resulting hair graph meets the embedded drawing at just
its marked near end. These are the graphs `Q_y` on page 59.
-/

public section
namespace GraphMinor.GM16
open Set Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM14
universe u v

/-- Deleting one end of a path with distinct ends leaves a nonempty
connected graph, as used for `Q_y` in XVI (6.3), page 59. -/
theorem path_delete_endpoint_connected
    {α : Type u} {β : Type v} {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hab : a ≠ b) :
    IsGraphConnected (deleteVertices P {b}) := by
  classical
  have hPV := hP.vertexSet_finite
  have hPE := hP.edgeSet_finite
  let K := (Hypergraph.ofGraph P hPV hPE).skeleton
  have hleafP := path_start_neighbors_subsingleton hP.symm
  have hleaf : (K.neighborSet b).Subsingleton := by
    intro y hy z hz
    obtain ⟨hby, e, hbe, hye⟩ := hy
    obtain ⟨hbz, f, hbf, hzf⟩ := hz
    exact hleafP ⟨e, isLink_of_inc_of_inc_of_ne hbe hye hby⟩
      ⟨f, isLink_of_inc_of_inc_of_ne hbf hzf hbz⟩
  refine ⟨⟨a, hP.left_mem, by simpa using hab⟩, ?_⟩
  intro y hy z hz
  have hyP : y ∈ V(P) := hy.1
  have hzP : z ∈ V(P) := hz.1
  have hyb : y ≠ b := by simpa using hy.2
  have hzb : z ≠ b := by simpa using hz.2
  obtain ⟨L, _, hL, _⟩ := hP.exists_subpath hyP hzP
  obtain ⟨W⟩ := graphPath_exists_walk hL
  obtain ⟨q⟩ := skeleton_reachable_of_reflTransGen_adj hPV hPE (graphWalk_adj_reachable W)
  have havoid : b ∉ q.toPath.val.support :=
    q.toPath.isPath.isTrail.notMem_support_of_subsingleton_neighborSet hyb.symm hzb.symm hleaf
  obtain ⟨R, hR, hverts⟩ := exists_isGraphPathWithEnds_of_skeleton_isPath
    hPV hPE hyP q.toPath.val q.toPath.isPath
  have hbR : b ∉ V(R) := by
    rw [hverts]
    exact havoid
  have hRD := hR.in_deleteVertices (Set.disjoint_singleton_left.mpr hbR)
  exact graphPath_exists_walk hRD

/-- A hair path with its far end removed meets the old graph only at
its near end, as in XVI (6.3), page 59. -/
theorem truncated_hair_inter
    {α : Type u} {β : Type v} {G H P : Graph α β} {a b : α}
    (hP : IsHPathWithEnds G H P a b) :
    V(deleteVertices P {b}) ∩ V(H) = {a} := by
  apply Set.Subset.antisymm
  · rintro z ⟨⟨hzP, hzb⟩, hzH⟩
    have hz : z ∈ ({a, b} : Set α) := hP.2.2.2.2.2.1 ▸ ⟨hzP, hzH⟩
    exact hz.resolve_right hzb
  · rintro z rfl
    exact ⟨⟨hP.2.1.left_mem, by simpa using hP.2.2.1⟩, hP.2.2.2.1⟩

end GraphMinor.GM16
