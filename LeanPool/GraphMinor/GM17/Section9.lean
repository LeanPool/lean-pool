/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section8
public import LeanPool.GraphMinor.Menger.Basic
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.GM17.PasteCuff
import LeanPool.GraphMinor.GM17.ArcDisc
import LeanPool.GraphMinor.GM17.MarkCross
import LeanPool.GraphMinor.GM17.ReplaceDisc
import LeanPool.GraphMinor.GM17.RegionDisc
import LeanPool.GraphMinor.GM17.CutArcPaint
import LeanPool.GraphMinor.GM17.PushNode

/-!
# Graph Minors XVII, Section 9: Cell Connectivity in a True Portrayal

This file formalizes Section 9 (pages 183–188) of Robertson and Seymour, *Graph Minors. XVII.
Taming a Vortex*, J. Combin. Theory Ser. B 77 (1999), 162–210.
The portrayal deductions that use painting results are proved in `Section9Proved`.
-/

public section

namespace GraphMinor.GM17

open Set Function Topology Metric
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

local notation "𝕀" => unitInterval

/-! ## 1. Internal Cell Connectivity: (9.1) (Page 183) -/

/-- A walk in `H.skeleton` from `G₁.vertexSet` to `G₂.vertexSet` for a separation `(G₁, G₂)` of `H`
meets `(G₁ ∩ G₂).vertexSet`. -/
theorem walk_meets_separation {α : Type u} {β : Type v} {H G₁ G₂ : Hypergraph α β}
    (hsep : H.IsSeparation G₁ G₂) {u₀ v₀ : α} (w : H.skeleton.Walk u₀ v₀)
    (hu : u₀ ∈ G₁.vertexSet) (hv : v₀ ∈ G₂.vertexSet) :
    ∃ z ∈ w.support, z ∈ (G₁ ∩ G₂).vertexSet := by
  induction w with
  | nil =>
    exact ⟨_, SimpleGraph.Walk.start_mem_support _, hu, hv⟩
  | @cons u u' v hadj w' ih =>
    by_cases hu' : u' ∈ G₁.vertexSet
    · obtain ⟨z, hz_sup, hz_inter⟩ := ih hu' hv
      exact ⟨z, SimpleGraph.Walk.support_cons hadj w' ▸ List.mem_cons_of_mem u hz_sup, hz_inter⟩
    · rcases hadj with ⟨_, e, heu, heu'⟩
      have heH : e ∈ H.edgeSet := H.edge_mem_of_inc heu
      have he_union : e ∈ G₁.edgeSet ∪ G₂.edgeSet := by
        have := congrArg (e ∈ ·.edgeSet) hsep.union_eq
        exact this.mpr heH
      rcases he_union with he₁ | he₂
      · exfalso
        have hends := hsep.left_le.ends_eq e he₁
        have hu'_G₁ : G₁.Inc e u' := by
          change u' ∈ G₁.ends e
          rw [← hends]
          exact heu'
        exact hu' (G₁.vertex_mem_of_inc hu'_G₁)
      · have hends := hsep.right_le.ends_eq e he₂
        have hu_G₂ : G₂.Inc e u := by
          change u ∈ G₂.ends e
          rw [← hends]
          exact heu
        exact ⟨u, SimpleGraph.Walk.start_mem_support _, hu, G₂.vertex_mem_of_inc hu_G₂⟩

end GraphMinor.GM17
