/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.Disc

/-!
# The dense connected complement of a seam

For the disc-side argument on page 226 of VII (4.6), the unique seam
region is connected and dense in the surface. Connectedness comes from
the open disc before pasting. Density follows by mapping the dense
interior of that closed disc under the associated surjection.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- The complement of a net seam is dense, as used in the disc-side
argument of VII (4.6), page 226. -/
theorem Net.dense_compl_seamU {S : Type*} [TopologicalSpace S] (N : Net S) :
    Dense N.seamUᶜ := by
  have : T2Space N.D := N.isSurface_D.2.1
  have hb : discBd (univ : Set N.D) = bd N.D := image_bd_homeomorph (Homeomorph.Set.univ N.D)
  have hd : Dense (discInt (univ : Set N.D)) :=
    fun x => N.isClosedDisc_D.subset_closure_discInt (mem_univ x)
  have hInt : discInt (univ : Set N.D) = (bd N.D)ᶜ := by
    unfold discInt
    rw [hb]
    ext x
    simp
  rw [hInt] at hd
  have him := N.quotientMap_φ.surjective.denseRange.dense_image N.quotientMap_φ.continuous hd
  rw [N.image_compl_bd] at him
  simpa only [compl_eq_univ_sdiff] using him

/-- The complement of the seam is connected, the single-region property
used in VII (4.6), page 226. -/
theorem Net.isPreconnected_compl_seamU {S : Type*} [TopologicalSpace S] [T2Space S]
    (N : Net S) : IsPreconnected N.seamUᶜ := by
  simpa only [compl_eq_univ_sdiff] using
    N.isOpenDisc_compl_seamU.isPathConnected.isConnected.isPreconnected

end GraphMinor.GM07
