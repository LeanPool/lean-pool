/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section46NullCircle
import LeanPool.GraphMinor.GM07.Section46CappedCircle

/-!
# Small seam circles are cuffs

The circle claim on page 226 of VII (4.6) uses hypothesis (ii).
A null circle in the original surface is excluded by the unique dense
seam region. In the capped-cuff alternative, the bounded disc meets
the original surface only along its boundary, forcing the circle to
be that cuff. No part of this disc argument is an extra hypothesis.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- The topological circle claim of VII (4.6), page 226, applied to
any small `G`-normal circle contained in the seam. -/
theorem Net.small_normal_circle_in_seam_is_cuff {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) (hcuffs : 2 ≤ (cuffs S).ncard)
    {G : Drawing S} {v : ℕ}
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ v →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    {F : Set S} (hF : IsOArc F) (hnorm : G.IsNormal F)
    (hsmall : (G.V ∩ F).ncard ≤ v) (hFU : F ⊆ N.seamU) : F ∈ cuffs S := by
  rcases hii F hnorm hF hsmall with hnull | ⟨C, hC, hcap, hVCF⟩
  · exact (N.not_nullHomotopic_circle_in_seam hS hcuffs hF hFU hnull).elim
  · have hVC : (G.V ∩ C).Nonempty := Set.nonempty_of_ncard_ne_zero (by have h := hiii C hC; omega)
    have heq := N.capped_circle_eq_cuff hS hcuffs hF hFU hC hcap hVC hVCF
    exact heq.symm ▸ hC

end GraphMinor.GM07
