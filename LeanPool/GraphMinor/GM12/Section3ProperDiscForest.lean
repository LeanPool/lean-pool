/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3DiscStarForest
public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM12.Section3FeasibilityDiscs
import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# Proper forests in boundary-contact discs

For XII (3.1), page 245, each feasibility disc lies in Sigma-star and
meets its surface boundary only at prescribed contacts. The constructed
star is therefore proper, and its boundary vertex set is exactly the
prescribed set. Its interior centre is not a surface boundary point.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A disc whose contacts with the surface boundary form a finite set
carries a connected proper forest with exactly those boundary vertices.
This is the local forest required for XII (3.1), page 245. -/
theorem exists_proper_connected_forest_in_disc
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsSurface S)
    {D Z : Set S} (hD : IsClosedDisc D) (hZ : Z.Finite)
    (hZD : Z ⊆ D) (hZB : Z ⊆ bd S) (hDB : D ∩ bd S ⊆ Z) :
    ∃ H : Drawing S, H.U ⊆ D ∧ GM07.IsSurfaceForest H ∧
      IsConnectedDrawing H ∧ H.V ∩ bd S = Z := by
  have hZdisc : Z ⊆ discBd D := fun x hx =>
    disc_inter_surface_boundary_subset_discBd hS hD ⟨hZD hx, hZB hx⟩
  obtain ⟨H, c, hc, hUD, hV, hboundary, hforest, hconn⟩ :=
    exists_connected_forest_in_disc hD hZ hZdisc
  have hcB : c ∉ bd S := by
    intro hcb
    exact hcb (isInteriorPoint_of_mem_discInt hS.2.2 hD hc)
  have hproper : H.IsProper := by
    rintro x ⟨hxB, hxU⟩
    have hxZ := hDB ⟨hUD hxU, hxB⟩
    rw [hV]
    exact Or.inr hxZ
  have hvertices : H.V ∩ bd S = Z := by
    rw [hV]
    apply Subset.antisymm
    · rintro x ⟨hxV, hxB⟩
      rcases hxV with hxc | hxZ
      · exact False.elim (hcB (hxc ▸ hxB))
      · exact hxZ
    · intro x hxZ
      exact ⟨Or.inr hxZ, hZB hxZ⟩
  exact ⟨H, hUD, ⟨hproper, hforest⟩, hconn, hvertices⟩

end GraphMinor.GM12
