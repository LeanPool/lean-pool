/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section46SeamComplement
import LeanPool.GraphMinor.GM07.Section46DiscSides
import LeanPool.GraphMinor.GM07.Section11a
import LeanPool.GraphMinor.Surface.HoleDisc
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# A seam circle cannot bound a disc in the original surface

In the circle argument of VII (4.6), page 226, a disc bounded by a
circle in the seam has the unique dense region entirely on one side.
It must contain the whole surface. A surface with at least two cuffs
is not a closed disc, so such a circle cannot be null-homotopic there.
This leaves the capped-cuff alternative of hypothesis (ii).
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- A surface with at least two cuffs is not itself a closed disc. -/
theorem not_isClosedDisc_univ_of_two_cuffs {S : Type*} [TopologicalSpace S]
    (hcuffs : 2 ≤ (cuffs S).ncard) : ¬IsClosedDisc (univ : Set S) := by
  intro hD
  have hb : discBd (univ : Set S) = bd S := image_bd_homeomorph (Homeomorph.Set.univ S)
  have hO : IsOArc (bd S) := hb ▸ hD.isOArc_discBd
  have hc := cuffs_eq_of_isConnected hO.isConnected'
  rw [hc, ncard_singleton] at hcuffs
  omega

/-- A circle in the seam cannot be null-homotopic in a surface with
at least two cuffs, in VII (4.6), page 226. -/
theorem Net.not_nullHomotopic_circle_in_seam {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) (hcuffs : 2 ≤ (cuffs S).ncard)
    {F : Set S} (hF : IsOArc F) (hFU : F ⊆ N.seamU) : ¬IsNullHomotopicOArc F := by
  have : T2Space S := hS.2.1
  intro hnull
  obtain ⟨D, hD, hbd⟩ := nullHomotopicOArc_bounds_disc hS hF hnull
  have hside : (univ : Set S) ⊆ D ∨ D ∩ univ ⊆ discBd D := by
    apply disc_side_of_dense_connected_set hS.2.2 hD N.isPreconnected_compl_seamU
      (fun _ _ => N.dense_compl_seamU _)
    rw [hbd]
    exact disjoint_compl_left.mono_right hFU
  rcases hside with hcover | hboundary
  · have heq : D = univ := Subset.antisymm (subset_univ _) hcover
    exact not_isClosedDisc_univ_of_two_cuffs hcuffs (heq ▸ hD)
  · obtain ⟨x, hxD, hxbd⟩ := hD.nonempty_discInt
    exact hxbd (hboundary ⟨hxD, mem_univ _⟩)

end GraphMinor.GM07
