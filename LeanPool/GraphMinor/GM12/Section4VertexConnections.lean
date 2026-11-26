/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4EndPartition
public import LeanPool.GraphMinor.GM12.Cited
import LeanPool.GraphMinor.GM12.Section3Theorem
import LeanPool.GraphMinor.GM12.Section3DiscRegion
import LeanPool.GraphMinor.GM12.Section4SingletonFeasibility
import LeanPool.GraphMinor.GM12.Section4SingletonDiscs
import LeanPool.GraphMinor.GM12.Section4FreeSingleton
import LeanPool.GraphMinor.GM12.Section4VertexRegionDistance
import LeanPool.GraphMinor.GM12.Section2NonemptyEdges

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Disjoint connections between distant prescribed vertices

This is the application of (3.2) in XII (4.4), pages 251--252.
Put disjoint singleton discs at the selected vertices. Singleton
feasibility and freeness supply two hypotheses of (3.2). Passing
from vertices to their incident regions loses at most two units
of distance. The connection theorem then gives disjoint connected
subdrawings with precisely the assigned prescribed vertices.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM10 GM14

universe u

/-- The connection step of XII (4.4), pages 251--252, for any
partition of finitely many distant prescribed vertices. -/
theorem exists_threshold_for_vertex_connections
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (p t : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ 2 * p + 2 ≤ N ∧
      ∀ (Γ : Drawing S) (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ) (z : Fin t → S) (κ : Fin t → Fin p),
      HasTangleMetric Γ θ T d → N ≤ θ →
      (∀ i, z i ∈ Γ.V) → Function.Injective z →
      (∀ i j, i ≠ j → N ≤ d {z i} {z j}) →
      HasConnectingSubdrawings Γ (range z) (edgeEndClass z κ) := by
  obtain ⟨η, hη, hmain⟩ := theorem_3_2_proof hS t t
  let N := max η (2 * p) + 2
  have hηN : η + 2 ≤ N := Nat.add_le_add_right (le_max_left _ _) 2
  have hpN : 2 * p + 2 ≤ N := Nat.add_le_add_right (le_max_right _ _) 2
  refine ⟨N, (by omega), hpN, ?_⟩
  intro Γ θ T d z κ hm hN hz hinj hfar
  obtain ⟨Δ, hΔ, hdisj⟩ := exists_disjoint_single_vertex_discs hS Γ z hz hinj
  have havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i) :=
    fun i => (hΔ i).2.1.trans (hΔ i).2.2.2.symm
  have hZ : discBoundaryVertices Γ Δ = range z := by
    ext x
    simp only [discBoundaryVertices, (fun i => (hΔ i).2.2.2), mem_iUnion, mem_singleton_iff,
      mem_range]
    exact exists_congr (fun i => eq_comm)
  have hcount : (discBoundaryVertices Γ Δ).ncard ≤ t := by
    rw [hZ, Set.ncard_range_of_injective hinj]
    simp
  have hfeas : IsTopologicallyFeasible Δ (edgeEndClass z κ) :=
    topologicallyFeasible_singleton_prescriptions hS Δ (fun i => (hΔ i).1) hdisj
      z (fun i => (hΔ i).2.2.1) κ
  have hE : Γ.E.Nonempty := edges_nonempty_of_tangle_order_two hm.1.2.1 (by omega)
  have hreg : ∀ i j, i ≠ j → ∀ ri ∈ Γ.R, (ri ∩ Δ i).Nonempty →
      ∀ rj ∈ Γ.R, (rj ∩ Δ j).Nonempty → η ≤ d ri rj := by
    intro i j hij ri hri hriD rj hrj hrjD
    obtain ⟨r, hr, _, hDr, huniq⟩ := exists_unique_region_meeting_disc hS (hΔ i).1 (havoid i)
    obtain ⟨s, hs, _, hDs, huniq'⟩ := exists_unique_region_meeting_disc hS (hΔ j).1 (havoid j)
    have hzi : z i ∈ closure ri := by
      rw [huniq ri hri hriD]
      exact hDr (discBd_subset _ (hΔ i).2.2.1)
    have hzj : z j ∈ closure rj := by
      rw [huniq' rj hrj hrjD]
      exact hDs (discBd_subset _ (hΔ j).2.2.1)
    exact regions_distant_of_incident_vertices_distant hS hm hE (hz i) (hz j)
      hri hrj hzi hzj (hηN.trans (hfar i j hij))
  have hfree : ∀ i, IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (Δ i)) := by
    intro i
    rw [(hΔ i).2.2.2]
    exact isFreeSet_singleton_of_respectful_drawing hS hm.1 (hz i)
  have hconn := hmain Δ Γ θ T d p (edgeEndClass z κ)
    (fun i => ⟨(hΔ i).1, havoid i⟩) hdisj hcount
    ((iUnion_edgeEndClass z κ).trans hZ.symm)
    (fun i j hij => disjoint_edgeEndClass z κ hinj hij) hfeas
    (by omega) hm hreg hfree
  rwa [hZ] at hconn

end GraphMinor.GM12
