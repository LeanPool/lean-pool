/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section2MinVal
import LeanPool.GraphMinor.GM07.CuffIncidences
import LeanPool.GraphMinor.GM11.DrawingOps
import LeanPool.GraphMinor.Surface.Circle
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.Classification

/-!
# The two cuff incidences at a seam vertex

The local count in VII (4.6), page 225, includes two incidences from the cuff.
The cuff through a seam vertex either has no other seam vertex, giving a loop,
or has two distinct neighbouring edges. We construct these edges from the
cyclic order on the cuff.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The two cuff incidences used in VII (4.6), page 225: either one
boundary loop or two distinct incident boundary edges. -/
theorem Net.exists_cuff_incident_edges (hS : IsSurface S) (N : Net S)
    {J : Drawing S} (hJ : N.IsSeamGraphFor J) {v : S}
    (hvV : v ∈ J.V) (hv_bd : v ∈ bd S) :
    (∃ e ∈ J.E, e ⊆ bd S ∧ J.VertexIncident v e ∧ (tilde e).ncard = 1) ∨
    (∃ e₁ ∈ J.E, ∃ e₂ ∈ J.E, e₁ ≠ e₂ ∧
      e₁ ⊆ bd S ∧ e₂ ⊆ bd S ∧ J.VertexIncident v e₁ ∧ J.VertexIncident v e₂) := by
  apply exists_cuff_incident_edges_of_edge_cover hS ?_ hvV hv_bd
  rw [(N.seamGraph_edges_eq hS hJ).1]
  exact subset_union_right

end GraphMinor.GM07
