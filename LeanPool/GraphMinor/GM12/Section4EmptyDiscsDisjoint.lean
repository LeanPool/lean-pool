/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM12.Section4IncidentEdges
import LeanPool.GraphMinor.GM12.Section4EdgeRegionDistance
import LeanPool.GraphMinor.GM12.Section3DiscRegion
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.Regions

/-!
# Empty discs at distant edges are disjoint

XII (4.3), page 250, uses disjoint empty discs at its chosen
edges. A common drawing point would be a common end of the two
edges, bounding their distance by four. A common point off the
drawing would put both discs in the same incident region. The
region-distance estimate rules this out too.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14

/-- The disjointness assertion following XII (4.3), claim (4),
page 250, with the threshold five made explicit. -/
theorem empty_discs_disjoint_of_edges_distant
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    {e f : Set S} {u v x y : S}
    (he : Γ.toGraph.IsLink e u v) (hf : Γ.toGraph.IsLink f x y)
    {D E r s : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hDU : Γ.U ∩ D = {u, v}) (hEU : Γ.U ∩ E = {x, y})
    (hDa : Γ.U ∩ D = Γ.V ∩ discBd D) (hEa : Γ.U ∩ E = Γ.V ∩ discBd E)
    (hr : r ∈ Γ.R) (hs : s ∈ Γ.R) (her : e ⊆ closure r) (hfs : f ⊆ closure s)
    (hrD : (r ∩ D).Nonempty) (hsE : (s ∩ E).Nonempty)
    (hfar : 5 ≤ d e f) : Disjoint D E := by
  have hreg : 1 ≤ d r s := incident_regions_distance_ge hS hm he.edge_mem hf.edge_mem
    hr hs her hfs hfar
  have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
  have hrs : r ≠ s := by
    intro heq
    subst s
    rw [h91.2.1 r (Or.inr hr)] at hreg
    exact Nat.not_succ_le_zero 0 hreg
  obtain ⟨r', _, _, _, huniqD⟩ := exists_unique_region_meeting_disc hS hD hDa
  obtain ⟨s', _, _, _, huniqE⟩ := exists_unique_region_meeting_disc hS hE hEa
  have hrr' := huniqD r hr hrD
  have hss' := huniqE s hs hsE
  apply Set.disjoint_left.mpr
  intro z hzD hzE
  by_cases hzU : z ∈ Γ.U
  · have hzends := hDU.subset ⟨hzU, hzD⟩
    have hzends' := hEU.subset ⟨hzU, hzE⟩
    have hzV : z ∈ Γ.V := by
      rcases hzends with rfl | hzends
      · exact he.left_mem
      · exact (Set.mem_singleton_iff.mp hzends) ▸ he.right_mem
    have hze : z ∈ closure e := by
      have h : z ∈ closure e ∩ Γ.V := by rw [he.2.2.2]; exact hzends
      exact h.1
    have hzf : z ∈ closure f := by
      have h : z ∈ closure f ∩ Γ.V := by rw [hf.2.2.2]; exact hzends'
      exact h.1
    have hclose := incident_edges_distance_le_four hS hm he.edge_mem hf.edge_mem hzV hze hzf
    omega
  · obtain ⟨q, hq, hzq⟩ := exists_region_of_notMem hzU
    have hqr' := huniqD q hq ⟨z, hzq, hzD⟩
    have hqs' := huniqE q hq ⟨z, hzq, hzE⟩
    exact hrs (hrr'.trans (hqr'.symm.trans (hqs'.trans hss'.symm)))

end GraphMinor.GM12
