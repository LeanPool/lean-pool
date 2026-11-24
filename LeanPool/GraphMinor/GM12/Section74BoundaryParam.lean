/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.ArcDrawings
import LeanPool.GraphMinor.GM11.EdgeSides
import LeanPool.GraphMinor.GM11.PaintingFacts
import LeanPool.GraphMinor.GM11.Section6

/-!
# Parameterizing a disc boundary punctured at one point

The leaf gluing in XII (7.4), pages 262--263, uses a disc whose
boundary misses the old region at just one point. Regard its
boundary circle as a loop drawing with that point as its sole
vertex. The edge parameter then runs through every other boundary
point injectively in the open parameter interval, and starts and
ends at the missing point.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 unitInterval

/-- A circle punctured at a marked point has a loop parameter
that is injective on the open interval and takes both ends to
the marked point. -/
theorem exists_punctured_oArc_parameter
    {S : Type*} [TopologicalSpace S] [T2Space S] {F : Set S} {w : S}
    (hF : IsOArc F) (hw : w ∈ F) :
    ∃ ℓ : I → S, Continuous ℓ ∧ ℓ 0 = w ∧ ℓ 1 = w ∧
      InjOn ℓ (Ioo 0 1) ∧ ℓ '' Ioo 0 1 = F \ {w} := by
  obtain ⟨K, hKU, hKV⟩ := exists_loop_drawing hF hw
  have hne : (F \ {w}).Nonempty := ((infinite_of_isOArc hF).sdiff (finite_singleton w)).nonempty
  have hpath : IsPathConnected (F \ {w}) := isPathConnected_oArc_diff hF hw
  have he : F \ {w} ∈ K.E := by
    change F \ {w} ∈ arcComponentsIn (K.U \ K.V)
    rw [hKU, hKV]
    refine ⟨hne, Subset.rfl, hpath, ?_⟩
    intro A hA _ hsub
    exact Subset.antisymm hA hsub
  obtain ⟨ℓ, hℓ, h0, h1, hi, hrange⟩ := exists_edge_param K he
  rw [hKV] at h0 h1
  exact ⟨ℓ, hℓ, h0, h1, hi, hrange⟩

end GraphMinor.GM12
