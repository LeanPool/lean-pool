/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.CircuitRegions
import LeanPool.GraphMinor.GM11.Section4c

/-!
# The outside of a disc as a union of regions

For the one-cuff candidate-existence argument used by XII (3.1),
page 245, add the disc boundary to the drawing. Each region meeting
the outside of the disc stays outside, since a connected region
cannot cross the boundary. Drawing carriers have empty interior, so
the outside regions are dense in the outside of the disc. Their
union therefore has the required disc complement as its closure.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- When a closed set's frontier belongs to a drawing, the closure
of its complement is the closure of the union of outside regions. -/
theorem closure_compl_eq_closure_outside_regions
    {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) (G : Drawing S) {D : Set S} (hD : IsClosed D)
    (hbd : frontier D ⊆ G.U) :
    closure Dᶜ = closure (⋃₀ {r ∈ G.R | Disjoint r D}) := by
  let : T2Space S := hS.2.1
  apply Subset.antisymm
  · apply closure_minimal
    · intro x hx
      apply mem_closure_iff.mpr
      intro O hO hxO
      obtain ⟨y, hy, hyU⟩ := exists_notMem_U (Γ := G) hS
        (hO.inter hD.isOpen_compl) ⟨x, hxO, hx⟩
      obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyU
      have hdis : Disjoint r D := by
        have hrf : Disjoint r (frontier D) := disjoint_left.mpr
          (fun z hz hzfr => region_subset hr hz (hbd hzfr))
        rcases subset_or_disjoint_of_frontier hD (region_isPreconnected hr) hrf with hin | hout
        · exact (hy.2 (hin hyr)).elim
        · exact hout
      exact ⟨y, hy.1, r, ⟨hr, hdis⟩, hyr⟩
    · exact isClosed_closure
  · apply closure_mono
    rintro x ⟨r, ⟨_, hdis⟩, hxr⟩
    exact disjoint_left.mp hdis hxr

end GraphMinor.GM12
