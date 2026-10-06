/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityLocalFinite

/-!
# Stability Local Box Enclosure

Supporting estimates for the Navier–Stokes development.
-/

public section

open Set
open CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- Every local box lies in a compact product set still contained in the
space-time carrier. -/
theorem stability_localBox_compact_enclosure
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (hbox : CKN.localBox Ω I Ω' J) :
    ∃ K : Set ParabolicPoint,
      IsCompact K ∧ CKN.spaceTimeSet Ω' J ⊆ K ∧
      K ⊆ CKN.spaceTimeSet Ω I := by
  obtain ⟨_hΩopen, hΩcompact, hΩsub, _hJconn, hJcompact, hJsub⟩ := hbox
  refine ⟨closure Ω' ×ˢ closure J, ?_, ?_, ?_⟩
  · apply parabolicHomeomorph.isCompact_preimage.mpr
    change IsCompact (closure Ω' ×ˢ closure J)
    exact hΩcompact.prod hJcompact
  · exact Set.prod_mono subset_closure subset_closure
  · exact Set.prod_mono hΩsub hJsub

end CKN
