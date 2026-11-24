/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TraceVisits
import LeanPool.GraphMinor.GM12.Section2CirclePeriod
import LeanPool.GraphMinor.GM11.Regions

/-!
# The trace records atoms met by the curve image

The restriction step of XII (2.1), pages 243--244, uses points of the
curve image rather than a fixed real parameter. Represent each such
point in the trace's one-period interval. The trace-step visit lemmas
then record its vertex or region. A zero-length trace records the
unique region directly.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A drawing vertex in the image of a traced curve is a vertex of
the trace walk. -/
theorem trace_vertex_in_image
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {φ : C(Circle, S)}
    {u : S} (W : GraphWalk K.toGraph u u) (hW : IsTrace Γ K φ W)
    {x : S} (hxφ : x ∈ range φ) (hxV : x ∈ Γ.V) : x ∈ W.support := by
  obtain ⟨z, rfl⟩ := hxφ
  rcases hW.2 with ⟨_, _, _, r, hr, hφr, _⟩ | ⟨_, _, a, hsteps⟩
  · exact (region_subset hr (hφr (mem_range_self z)) (Γ.V_subset_U hxV)).elim
  · obtain ⟨s, hs, hsz⟩ := (circle_parameter_bijOn a).surjOn (mem_univ z)
    have heq : periodicCurve φ s = φ z := congrArg φ hsz
    exact heq ▸ traceSteps_vertex_visit W hsteps ⟨hs.1, hs.2.le⟩ (heq.symm ▸ hxV)

/-- A region met by the image of a traced curve contains a walk
vertex, its recorded radial hub. -/
theorem trace_region_in_image
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {φ : C(Circle, S)}
    {u : S} (W : GraphWalk K.toGraph u u) (hW : IsTrace Γ K φ W)
    {r : Set S} (hr : r ∈ Γ.R) (hmeet : (range φ ∩ r).Nonempty) :
    ∃ w ∈ W.support, w ∈ r := by
  obtain ⟨x, ⟨z, rfl⟩, hzr⟩ := hmeet
  rcases hW.2 with ⟨_, _, _, r', hr', hφr', hur'⟩ | ⟨_, _, a, hsteps⟩
  · have hrr : r' = r := region_eq_of_mem hr' hr (hφr' (mem_range_self z)) hzr
    exact ⟨u, W.start_mem_support, hrr ▸ hur'⟩
  · obtain ⟨s, hs, hsz⟩ := (circle_parameter_bijOn a).surjOn (mem_univ z)
    have heq : periodicCurve φ s = φ z := congrArg φ hsz
    exact traceSteps_region_visit W hsteps ⟨hs.1, hs.2.le⟩ hr (heq.symm ▸ hzr)

end GraphMinor.GM12
